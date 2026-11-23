module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHeckeLFunctionLeZetaThreeHalvesPow
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1715
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1683
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2820
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2606
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2831
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2823
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0544
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
public import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0143
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2832
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharRestrictsEtaPowOfSign
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeSignEta

theorem idF_ratF (D : D7) (a : D.host.Fˣ) :
    idF D (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom a) =
      Units.map (incA D).toMonoidHom (Units.map (algebraMap D.host.F D.host.E).toMonoidHom a) := by
  refine Units.ext ?_
  show algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (a : D.host.F)) =
    incA D (algebraMap D.host.F D.host.E (a : D.host.F))
  show _ = Algebra.TensorProduct.includeRight (algebraMap D.host.F D.host.E (a : D.host.F))
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply D.host.F (AF D.host.F) (AE D)]

theorem resEta_of_sign : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (N : ℕ), IsHeckeChar D χ →
    (∀ x y : (AE D)ˣ, (y : AE D) = x * cA D x → χ y = 1) →
    ∀ θ : InfFam D, IsInfFam θ →
    (∀ (τ : D.what₂.Tau) (x : (AE D)ˣ), finPart D (x : AE D) = 1 → θ τ (infPart D (x : AE D)) = -1 →
      (∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1) → ((χ x : Circle) : ℂ) = (-1) ^ N) →
    ResEta D χ N := by
  intro D χ N hχ hnorm θ hθ hsign
  refine ⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun ε hε => ?_⟩

  set ψ : (AF D.host.F)ˣ →* Circle := χ.comp (idF D) * (ε ^ N)⁻¹ with hψ
  have hψa : ∀ a, ψ a = χ (idF D a) * (ε a ^ N)⁻¹ := fun a => rfl
  have hker : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryVolumePairs.normGroup D ≤ ψ.ker := by
    rw [GlobalTheory.VolHeckeCompare.normGroup_eq]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, rfl⟩
      show ψ (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom a) = 1
      rw [hψa, idF_ratF, hχ.2, hε.2.1 a, one_pow, inv_one, mul_one]
    · rintro _ ⟨x, rfl⟩
      obtain ⟨-, -, hN, -⟩ := GlobalTheory.VolHeckeCompare.exists_form D
      have e : (idF D (GlobalTheory.VolHeckeCompare.normU D x) : AE D) = (x : AE D) * cA D (x : AE D) := by
        have e0 : idF D (GlobalTheory.VolHeckeCompare.normU D x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryVolumePairs.normId D x := hN x
        rw [e0]; rfl
      show ψ (GlobalTheory.VolHeckeCompare.normU D x) = 1
      rw [hψa, hnorm x _ e, hε.2.2.1 x, one_pow, inv_one, mul_one]

  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  obtain ⟨η, -, -, hη1, hη2⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  obtain ⟨N1, hN1, -, hηx⟩ := hη2 τ
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, -, e1, e2⟩ := GlobalTheory.SplitCharExp.exists_real_hom h
  set w : D.what₂.Tau → ℂ := Pi.mulSingle τ (-1) with hw
  have wτ : w τ = -1 := by simp [w]
  have wo : ∀ τ', τ' ≠ τ → w τ' = 1 := fun τ' ht => by simp [w, Pi.mulSingle_eq_of_ne ht]
  have ww : w * w = 1 := by
    funext τ'
    by_cases ht : τ' = τ
    · subst ht; simp [wτ]
    · simp [wo τ' ht]
  let x : (AE D)ˣ := ⟨e w, e w, by rw [← map_mul, ww, map_one], by rw [← map_mul, ww, map_one]⟩
  have x1 : finPart D (x : AE D) = 1 := e1 w
  have x2 : ∀ τ', θ τ' (infPart D (x : AE D)) = w τ' := e2 w
  have xτ : θ τ (infPart D (x : AE D)) = -1 := by rw [x2, wτ]
  have xo : ∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1 := fun τ' ht => by rw [x2, wo τ' ht]
  have hcx : ((χ x : Circle) : ℂ) = (-1 : ℂ) ^ N := hsign τ x x1 xτ xo
  have hN1' : N1 = 1 := by
    have : (N1 : ℚ) = 1 := by rw [hN1]; norm_num
    exact_mod_cast this
  have hηc : ((η x : Circle) : ℂ) = -1 := by rw [hηx θ hθ x x1 xo, xτ, hN1']; simp
  have hfix : cA D (x : AE D) = x := by
    refine GlobalTheory.SplitCharExp.ext_of_chart h ?_ fun τ' => ?_
    · have e3 : finPart D (cA D (x : AE D)) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) :=
        GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig (x : AE D)
      rw [e3, x1, RingHom.map_one]
    · rw [GlobalTheory.FockCompare.comp_cA hθ, x2]
      by_cases ht : τ' = τ
      · rw [ht, wτ]; simp
      · rw [wo τ' ht]; simp
  obtain ⟨y, hy⟩ := GlobalTheory.SplitParity.exists_idF_of_fixed D x hfix

  have hneg : ∀ ε', IsEta D ε' → ((ε' y : Circle) : ℂ) = -1 := fun ε' hε' => by
    have c2 := hη1.2 ε' hε' y
    rw [hy, pow_one] at c2
    rw [← c2, hηc]
  have hψy : ψ y = 1 := by
    refine Circle.ext ?_
    rw [hψa, hy, Circle.coe_mul, Circle.coe_inv, Circle.coe_pow, hcx, hneg ε hε, Circle.coe_one]
    exact mul_inv_cancel₀ (pow_ne_zero _ (by norm_num))
  have hψ1 : ψ = 1 := by
    by_contra hne
    have hψE : IsEta D ψ := (GlobalTheory.VolHeckeCompare.isEta_iff_normGroup D ψ).2 ⟨hker, hne⟩
    have := hneg ψ hψE
    rw [hψy, Circle.coe_one] at this
    norm_num at this
  intro a
  have ha : ψ a = 1 := by rw [hψ1]; rfl
  rw [hψa, mul_inv_eq_one] at ha
  exact ha

end GlobalTheory.HeckeSignEta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLValueUpperBoundPermutedWeightsOfFE
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.SqTop GlobalTheory.FunObj GlobalTheory.FunObj.SqNum Formalism.BasicNotions GlobalTheory.ChiGrid Formalism.IndefR.Links

namespace GlobalTheory.SqTop

theorem lBound_of : GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips → FieldDat → LBound := by
  intro hFE hS hFD
  set c : ℝ := max 0 (Real.log ‖riemannZeta (3 / 2)‖) with hc
  obtain ⟨CF1, hB⟩ := GlobalTheory.T.gridSizes_log_bound c
  obtain ⟨CF2, hF⟩ := hFD
  refine ⟨max CF1 CF2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, hB⟩ := hB ε CF (le_of_max_le_left hCF)
  obtain ⟨C2, x2, hF⟩ := hF ε CF (le_of_max_le_right hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ hL G => ?_⟩
  have hb := hB C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ hL G
  obtain ⟨hCM, hAb, hFd, hBase, -⟩ := hF C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ hL G
  intro i j s hs1 hs2 π χ Λ hχ hΛ
  set κ := kap D (⟨1, CF, large₂.sc.b⟩ : Consts).cGap i j s with hκ
  set n : ℕ := Module.finrank ℚ D.host.E with hn
  have key : c * (n : ℝ) + Real.log |((discr D.host.E : ℤ) : ℝ)| + 2 * Real.log (levQ G.pl) +
      ∑ τ, Real.log (1 + ((κ τ : ℝ) + s)) ≤ bTH D C large₂.sc.x large₂.sc.b := hb i j s hs1 hs2
  have hc0 : 0 ≤ c := le_max_left _ _
  have hcz : Real.log ‖riemannZeta (3 / 2)‖ ≤ c := le_max_right _ _
  have hd0 : 0 ≤ Real.log |((discr D.host.E : ℤ) : ℝ)| := Real.log_nonneg (by
    have := Int.one_le_abs (NumberField.discr_ne_zero D.host.E); exact_mod_cast this)
  have hq0 : 0 ≤ Real.log (levQ G.pl : ℝ) := Real.log_natCast_nonneg _
  have hk0 : 0 ≤ ∑ τ, Real.log (1 + ((κ τ : ℝ) + s)) :=
    Finset.sum_nonneg fun τ _ => Real.log_nonneg (by have : (0:ℝ) ≤ κ τ := Nat.cast_nonneg _; have : (0:ℝ) ≤ s := Nat.cast_nonneg _; linarith)
  have hn0 : (0 : ℝ) ≤ c * n := mul_nonneg hc0 (Nat.cast_nonneg _)
  by_cases h0 : Λ s = 0
  · rw [h0, norm_zero, Real.log_zero]
    linarith
  have hpos : 0 < ‖Λ s‖ := norm_pos_iff.2 h0
  have hz : 0 < ‖riemannZeta (3 / 2)‖ := norm_pos_iff.2 (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  rcases (by omega : s = 1 ∨ 2 ≤ s) with rfl | h2
  · obtain ⟨a, ha, haN⟩ := _root_.GlobalTheory.FunObj.SqNum.CondExps.exists_condExps D G 1 _ χ hχ
    have hA := _root_.GlobalTheory.HeckeLOneBound.norm_heckeL_one_le D.host.E D.what₂.Tau (cmPhi D) hFE hS hFd.2.2.2.2.2.2.1 χ (fun τ => ((κ (π τ) : ℕ) : ℤ) + ((1 : ℕ) : ℤ)) a Λ
      hχ.1 hχ.2.1 hχ.2.2.1 (fun τ => by positivity) ha hΛ
    simp only [Nat.cast_one] at hpos h0 ⊢
    set N : ℕ := (discr D.host.E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k with hN
    set P : ℝ := ∏ τ, (1 + ((((κ (π τ) : ℕ) : ℤ) + ((1 : ℕ) : ℤ) : ℤ) : ℝ)) with hP
    have hP0 : 0 < P := Finset.prod_pos fun τ _ => by push_cast; positivity
    have hN0 : (0 : ℝ) < N := by
      by_contra hc'
      have : (N : ℝ) = 0 := le_antisymm (not_lt.1 hc') (Nat.cast_nonneg _)
      rw [this, mul_zero, zero_mul] at hA
      linarith
    have hNle : (N : ℝ) ≤ |((discr D.host.E : ℤ) : ℝ)| * (levQ G.pl : ℝ) ^ 2 := by
      rw [hN, Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact_mod_cast haN
    have hQ0 : (0 : ℝ) < levQ G.pl := by
      by_contra hc'
      have : (levQ G.pl : ℝ) = 0 := le_antisymm (not_lt.1 hc') (Nat.cast_nonneg _)
      rw [this, zero_pow two_ne_zero, mul_zero] at hNle; linarith
    have hD0 : (0 : ℝ) < |((discr D.host.E : ℤ) : ℝ)| := by
      have := Int.one_le_abs (NumberField.discr_ne_zero D.host.E)
      have : (1 : ℝ) ≤ |((discr D.host.E : ℤ) : ℝ)| := by exact_mod_cast this
      linarith
    have h1 : Real.log ‖Λ 1‖ ≤ Real.log (‖riemannZeta (3 / 2)‖ ^ n) + Real.log N + Real.log P := by
      rw [← Real.log_mul (by positivity) hN0.ne', ← Real.log_mul (by positivity) hP0.ne']
      exact Real.log_le_log hpos hA
    have h2 : Real.log N ≤ Real.log |((discr D.host.E : ℤ) : ℝ)| + 2 * Real.log (levQ G.pl) := by
      calc Real.log N ≤ Real.log (|((discr D.host.E : ℤ) : ℝ)| * (levQ G.pl : ℝ) ^ 2) := Real.log_le_log hN0 hNle
        _ = _ := by rw [Real.log_mul hD0.ne' (by positivity), Real.log_pow]; push_cast; ring
    have h3 : Real.log P = ∑ τ, Real.log (1 + ((κ τ : ℝ) + ((1 : ℕ) : ℝ))) := by
      rw [hP, Real.log_prod (fun τ _ => by push_cast; positivity)]
      rw [← Equiv.sum_comp π (fun τ => Real.log (1 + ((κ τ : ℝ) + ((1 : ℕ) : ℝ))))]
      refine Finset.sum_congr rfl fun τ _ => ?_
      push_cast; ring_nf
    have h4 : Real.log (‖riemannZeta (3 / 2)‖ ^ n) ≤ c * n := by
      rw [Real.log_pow]; nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    linarith
  · have h := _root_.GlobalTheory.HeckeLBound.norm_heckeL_le D.host.E χ Λ s hχ.1 hΛ (by
      simp only [Complex.natCast_re]; have : (2 : ℝ) ≤ s := by exact_mod_cast h2
      linarith)
    have h4 : Real.log ‖Λ s‖ ≤ c * n := by
      calc Real.log ‖Λ s‖ ≤ Real.log (‖riemannZeta (3 / 2)‖ ^ n) := Real.log_le_log hpos h
        _ = n * Real.log ‖riemannZeta (3 / 2)‖ := Real.log_pow _ _
        _ ≤ c * n := by nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    linarith

end GlobalTheory.SqTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffTateModuleMapInjectiveAndIsogenyIff
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar.IsogTate

variable {K : Type} [Field K] (l : ℕ) [Fact l.Prime]

theorem vmap_comp' {A B C : AbVar K} (f : A ⟶ B) (g : B ⟶ C) :
    vmap l (f ≫ g) = vmap l g ∘ₗ vmap l f := by
  simp only [vmap, tmap_comp, LinearMap.baseChange_comp]

theorem vmap_nsmul_id (A : AbVar K) (n : ℕ) (x : Vl l A) :
    vmap l (n • 𝟙 A) x = (n : ℚ_[l]) • x := by
  have h1 : tmap l A A (n • 𝟙 A) = (n : ℤ_[l]) • LinearMap.id := by
    rw [map_nsmul, tmap_id, Nat.cast_smul_eq_nsmul]
  rw [vmap, h1, LinearMap.baseChange_smul, LinearMap.baseChange_id]
  rw [LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

theorem tmap_injective_of_finite_ker {A B : AbVar K} (f : A ⟶ B) (hG : Finite (ptMap f).ker) :
    Function.Injective (tmap l A B f) := by
  have hp : l.Prime := Fact.out
  set N := Nat.card (ptMap f).ker with hN
  have hN0 : 0 < N := Nat.card_pos
  have hx : ∀ x ∈ (ptMap f).ker, x ^ N = 1 := fun x hx => by
    have := pow_card_eq_one' (G := (ptMap f).ker) (x := ⟨x, hx⟩)
    exact congrArg Subtype.val this
  refine (injective_iff_map_eq_zero _).2 fun t ht => Tate.ext fun n => ?_
  have hmem : ∀ m, t.lev m ∈ (ptMap f).ker := fun m => by
    rw [MonoidHom.mem_ker, ptMap_apply, ← lev_tmap l f t m, ht]
    rfl
  have h1 : t.lev (n + N) ^ l ^ (n + N) = 1 := t.lev_pow _
  have h2 : t.lev (n + N) ^ N = 1 := hx _ (hmem _)
  have h3 : t.lev (n + N) ^ Nat.gcd (l ^ (n + N)) N = 1 := pow_gcd_eq_one.2 ⟨h1, h2⟩
  obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow hp).1 (Nat.gcd_dvd_left (l ^ (n + N)) N)
  have h4 : l ^ j ≤ N := hj' ▸ Nat.le_of_dvd hN0 (Nat.gcd_dvd_right _ _)
  have h5 : j < N := lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt) h4
  have h6 : t.lev (n + N) ^ l ^ N = 1 := by
    obtain ⟨c, hc⟩ := pow_dvd_pow l h5.le
    rw [hc, pow_mul, ← hj', h3, one_pow]
  show t.lev n = 1
  rw [← t.lev_add_pow n N]
  exact h6

theorem isFinite_of_tmap_injective (hl : (l : K) ≠ 0) {A B : AbVar K} (f : A ⟶ B)
    (hf : Function.Injective (tmap l A B f)) : IsFinite f.hom.left := by
  obtain ⟨C, p, i, hp, hi, rfl⟩ := _root_.GlobalTheory.AV.AbVar.exists_factor_abelianSubvariety K A B f
  have hpi : Function.Injective (tmap l A C p) := by
    rw [tmap_comp, LinearMap.coe_comp] at hf
    exact hf.of_comp
  obtain ⟨hA1, hA2, hA3, -, -⟩ := _root_.GlobalTheory.AV.AbVar.tl_free_finrank K l hl A
  obtain ⟨hC1, hC2, hC3, -, -⟩ := _root_.GlobalTheory.AV.AbVar.tl_free_finrank K l hl C
  have h1 : 2 * A.dim ≤ 2 * C.dim := by
    rw [← hA3, ← hC3]
    exact LinearMap.finrank_le_finrank_of_injective hpi
  have h2 : C.dim ≤ A.dim := (_root_.GlobalTheory.AV.DimLe.dim_le K A C p).2 hp
  have h3 : A.dim = C.dim := le_antisymm (by omega) h2
  have hpf : IsFinite p.hom.left := _root_.GlobalTheory.AV.AbVar.isFinite_of_surjective_of_dim_eq K A C p h3 hp
  haveI := hi
  rw [comp_hom, Over.comp_left]
  infer_instance

theorem tmap_injective_of_vmap_injective (hl : (l : K) ≠ 0) {A B : AbVar K} (f : A ⟶ B)
    (hv : Function.Injective (vmap l f)) : Function.Injective (tmap l A B f) := by
  obtain ⟨hA1, -, -, -, -⟩ := _root_.GlobalTheory.AV.AbVar.tl_free_finrank K l hl A
  obtain ⟨hB1, -, -, -, -⟩ := _root_.GlobalTheory.AV.AbVar.tl_free_finrank K l hl B
  have hinj : ∀ (X : AbVar K) [Module.Free ℤ_[l] (Tl l X)],
      Function.Injective (fun t : Tl l X => (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] t) := by
    intro X _
    have h := Module.Flat.rTensor_preserves_injective_linearMap (M := Tl l X)
      (Algebra.linearMap ℤ_[l] ℚ_[l]) (IsFractionRing.injective ℤ_[l] ℚ_[l])
    intro s t hst
    apply (TensorProduct.lid ℤ_[l] (Tl l X)).symm.injective
    apply h
    simpa using hst
  intro s t hst
  apply hinj A
  apply hv
  simp only [vmap, LinearMap.baseChange_tmul, hst]

theorem vmap_bijective_of_isIsogeny {A B : AbVar K} (f : A ⟶ B) (hf : IsIsogeny f) :
    Function.Bijective (vmap l f) := by
  obtain ⟨n, g, hn, -, hfg, hgf⟩ := _root_.GlobalTheory.AV.AbVar.exists_quasiInverse_isogeny K A B f hf
  have hn' : (n : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hb : ∀ (X : AbVar K), Function.Bijective (vmap l (n • 𝟙 X)) := fun X => by
    constructor
    · intro x y h
      rw [vmap_nsmul_id, vmap_nsmul_id] at h
      exact smul_right_injective _ hn' h
    · intro y
      exact ⟨(n : ℚ_[l])⁻¹ • y, by rw [vmap_nsmul_id, smul_smul, mul_inv_cancel₀ hn', one_smul]⟩
  refine ⟨?_, ?_⟩
  · have h := (hb A).1
    rw [← hfg, vmap_comp', LinearMap.coe_comp] at h
    exact h.of_comp
  · have h := (hb B).2
    rw [← hgf, vmap_comp', LinearMap.coe_comp] at h
    exact h.of_comp

end GlobalTheory.AV.AbVar.IsogTate

namespace GlobalTheory.AV.AbVar


open IsogTate in
theorem isFinite_iff_tmap_injective_and_isIsogeny_iff_vmap_bijective : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime],
    (l : K) ≠ 0 → ∀ (A B : AbVar K) (f : A ⟶ B),
    (IsFinite f.hom.left ↔ Function.Injective (tmap l A B f)) ∧ (IsIsogeny f ↔ Function.Bijective (vmap l f)) := by
  intro K _ l _ hl A B f
  have h1 : IsFinite f.hom.left ↔ Function.Injective (tmap l A B f) :=
    ⟨fun h => tmap_injective_of_finite_ker l f ((_root_.GlobalTheory.AV.AbVar.isFinite_iff_finite_ker K A B f).1 h), isFinite_of_tmap_injective l hl f⟩
  refine ⟨h1, fun h => vmap_bijective_of_isIsogeny l f h, fun h => ?_⟩
  have hfin := h1.2 (tmap_injective_of_vmap_injective l hl f h.1)
  obtain ⟨-, -, -, hA4, hA5⟩ := _root_.GlobalTheory.AV.AbVar.tl_free_finrank K l hl A
  obtain ⟨-, -, -, hB4, hB5⟩ := _root_.GlobalTheory.AV.AbVar.tl_free_finrank K l hl B
  have hd : 2 * A.dim = 2 * B.dim := by
    rw [← hA5, ← hB5]
    exact (LinearEquiv.ofBijective _ h).finrank_eq
  exact ⟨hfin, _root_.GlobalTheory.AV.AbVar.surjective_of_isFinite_of_dim_eq K A B f (by omega) hfin⟩

end GlobalTheory.AV.AbVar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperRestrictOfSubsetAbLocus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.AbLocusProperNormal

theorem isProper_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V))
    [GrpObj G] (hG : IsSemiAbelian G) (hab : abLocus G = Set.univ) : IsProper G.hom := by
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have := GlobalTheory.grpObj_geometricallyIntegral_of_smooth (Sp V) G
  have p : Sp (ResidueField V) := IsLocalRing.closedPoint (ResidueField V)
  refine _root_.GlobalTheory.FibreProperDvr.isProper_of_specialFibre V G.left G.hom inferInstance inferInstance inferInstance inferInstance inferInstance ?_
  exact GlobalTheory.AbelianTrait.isProper_snd_of_mem_abLocus G (K := ResidueField V)
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V))) p (by rw [hab]; trivial)

theorem isProper_of_abLocus_eq_univ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R))
    [GrpObj G] (hG : IsSemiAbelian G) (hab : abLocus G = Set.univ) : IsProper G.hom := by
  haveI : IsSemiAbelian G := hG
  haveI := hG.separated
  haveI := hG.quasiCompact
  haveI := hG.smooth
  haveI : IsIntegral G.left := GlobalTheory.isIntegral_left_of_isSemiAbelian G
  refine _root_.GlobalTheory.TraitProper.isProper_of_lift_genericPoint R G.left G.hom ?_
  intro V K _ _ _ _ _ _ _ x y _ hxy
  have hGV : IsSemiAbelian ((Over.pullback y).obj G) := IsSemiAbelian.pullback y G hG
  have habV : abLocus ((Over.pullback y).obj G) = Set.univ := Set.eq_univ_of_forall fun z =>
    (abLocus_pullback abLocusOne hG (IsPullback.of_hasPullback G.hom y) z).1 (hab ▸ Set.mem_univ _)
  have hpV : IsProper (pullback.snd G.hom y) := isProper_dvr V _ hGV habV
  let xV : Sp K ⟶ pullback G.hom y := pullback.lift x (spMap (algebraMap V K)) hxy
  have hE : ValuativeCriterion.Existence (pullback.snd G.hom y) := by
    have h : UniversallyClosed (pullback.snd G.hom y) := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let S : ValuativeCommSq (pullback.snd G.hom y) :=
    { R := V, K := K, i₁ := xV, i₂ := 𝟙 _, commSq := ⟨by rw [Category.comp_id]; exact pullback.lift_snd _ _ _⟩ }
  obtain ⟨l⟩ := (hE S).exists_lift
  refine ⟨l.l ≫ pullback.fst G.hom y, ?_⟩
  rw [← Category.assoc]
  have := l.fac_left
  change spMap (algebraMap V K) ≫ l.l = xV at this
  rw [this]
  exact pullback.lift_fst _ _ _

theorem isProper_restrict_of_subset_abLocus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ W : (Sp R).Opens, (W : Set (Sp R)) ⊆ abLocus G → IsProper (G.hom ∣_ W) := by
  intro R _ _ _ _ G _ hG W hW
  let I := {r : R // r ≠ 0 ∧ ((PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) : Set (Sp R)) ⊆ (W : Set (Sp R))}
  let t : ∀ i : I, Sp (Localization.Away i.1) ⟶ Sp R := fun i => spMap (algebraMap R (Localization.Away i.1))
  have hrange : ∀ i : I, Set.range (t i) = (PrimeSpectrum.basicOpen i.1 : Set (PrimeSpectrum R)) := fun i =>
    PrimeSpectrum.localization_away_comap_range (Localization.Away i.1) i.1
  have hprop : ∀ i : I, IsProper (pullback.snd G.hom (t i) ∣_ ⊤) := by
    intro i
    haveI : IsDomain (Localization.Away i.1) :=
      IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors i.2.1)
    haveI : IsNoetherianRing (Localization.Away i.1) :=
      IsLocalization.isNoetherianRing (Submonoid.powers i.1) _ inferInstance
    have hGi : IsSemiAbelian ((Over.pullback (t i)).obj G) := IsSemiAbelian.pullback (t i) G hG
    have hab : abLocus ((Over.pullback (t i)).obj G) = Set.univ := Set.eq_univ_of_forall fun z =>
      (abLocus_pullback abLocusOne hG (IsPullback.of_hasPullback G.hom (t i)) z).1
        (hW (i.2.2 (by rw [← hrange i]; exact ⟨z, rfl⟩)))
    have : IsProper (pullback.snd G.hom (t i)) := isProper_of_abLocus_eq_univ _ _ hGi hab
    infer_instance
  refine GlobalTheory.AbLocusLocal.isProper_restrict_of_cover G.hom t (fun i => pullback.snd G.hom (t i))
    (fun i => pullback.fst G.hom (t i)) (fun i => IsPullback.of_hasPullback G.hom (t i)) (fun _ => ⊤) hprop W
    (fun i => ?_) (fun z hz => ?_)
  · rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine i.2.2 ?_
    rw [← hrange i]
    exact ⟨_, rfl⟩
  · obtain ⟨_, ⟨r, rfl⟩, hzr, hrW⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hz W.isOpen
    have hr : r ≠ 0 := fun h0 => hzr (by rw [h0]; exact zero_mem _)
    let i : I := ⟨r, hr, hrW⟩
    obtain ⟨y, hy⟩ : z ∈ Set.range (t i) := by rw [hrange i]; exact hzr
    exact ⟨i, ⟨y, trivial⟩, by first | exact hy | (erw [Scheme.Hom.comp_apply]; exact hy) | simpa using hy⟩

end GlobalTheory.AbLocusProperNormal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateIntegralThetaExpansionByTwoTorsionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_integral_thetaExpansion_by_twoTorsion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U₂.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D₂.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U₂.gt e).t x) r z J') → (∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ (σ : H0 U.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α), (∀ e : ℕ, U.ExpandsAt e 1 σ f) → ∃ (σ₂ : H0 U₂.LG.L 1) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB 1 α) (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1])), ν.IsGen ∧ (∀ e : ℕ, U₂.ExpandsAt e 1 σ₂ f₂) ∧ ((∀ j, σ₂.f j = 0) → ∀ j, σ.f j = 0) ∧ ∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.toPre.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.toPre.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.toPre.famφB χ κ) z (fun i => J ((r ≫ D₂.toPre.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ D₂.toPre.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J' := by
  first | exact @GlobalTheory.MumCmp.translate_expansion_twist | exact GlobalTheory.MumCmp.translate_expansion_twist | (intros; apply GlobalTheory.MumCmp.translate_expansion_twist <;> assumption)
end

