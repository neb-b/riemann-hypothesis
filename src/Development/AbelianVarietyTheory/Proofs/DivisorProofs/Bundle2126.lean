module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2050
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0264
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemEqnSetOmegaCoeff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0898
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1096
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0275
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0271
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1045
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCohomologyIsoPresentedCrystal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0448

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeOfCrystallineComparison
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Proof.AbelianDeRhamFreeOfHodge

def extSqEquiv {R : Type} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (E : M ≃ₗ[R] N) : ⋀[R]^2 M ≃ₗ[R] ⋀[R]^2 N :=
  LinearEquiv.ofLinear (exteriorPower.map 2 (E : M →ₗ[R] N)) (exteriorPower.map 2 (E.symm : N →ₗ[R] M))
    (by rw [← exteriorPower.map_comp]; simp [exteriorPower.map_id])
    (by rw [← exteriorPower.map_comp]; simp [exteriorPower.map_id])

theorem extSqEquiv_ιMulti {R : Type} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (E : M ≃ₗ[R] N) (a b : M) :
    extSqEquiv E (exteriorPower.ιMulti R 2 ![a, b]) = exteriorPower.ιMulti R 2 ![E a, E b] := by
  change exteriorPower.map 2 (E : M →ₗ[R] N) _ = _
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem free_of (hC : GlobalTheory.Published.CrystallineSmoothLift) (hA : GlobalTheory.Published.AbelianHodgeDeRham)
    (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (s : A.left ⟶ Sp R) (hs : s = A.hom) :
    Module.Finite R (FirstDeRham s) ∧ Module.Projective R (FirstDeRham s) ∧
    (∀ p : PrimeSpectrum R, Module.rankAtStalk (FirstDeRham s) p = 2 * g) ∧
    ∃ e : ⋀[R]^2 (FirstDeRham s) ≃ₗ[R] SecondDeRham s,
      ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cup _ a b := by
  subst hs
  haveI : Smooth A.hom := hab.smooth
  haveI : IsProper A.hom := hab.proper
  obtain ⟨⟨hfin, hproj, hrank⟩, ⟨eH, heH⟩, -⟩ := hA R A g hab hg
  obtain ⟨hbij, e2, he2⟩ := GlobalTheory.CechDR.cechDeRham_comparison_bijective_cup_smooth hC R A.left A.hom inferInstance inferInstance inferInstance
  let E1 : FirstDeRham A.hom ≃ₗ[R] HH1 A.hom := LinearEquiv.ofBijective (cmp1 A.hom) hbij
  refine ⟨Module.Finite.equiv E1.symm, Module.Projective.of_equiv E1.symm, ?_, ?_⟩
  · intro p
    rw [Module.rankAtStalk_eq_of_equiv E1]
    exact hrank p
  · refine ⟨(extSqEquiv E1).trans (eH.trans e2.symm), fun a b => ?_⟩
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, extSqEquiv_ιMulti, heH, LinearEquiv.symm_apply_eq]
    exact (he2 a b).symm

end GlobalTheory.Proof.AbelianDeRhamFreeOfHodge


open GlobalTheory.Proof.AbelianDeRhamFreeOfHodge in
theorem GlobalTheory.Proof.abelianDeRhamFree_of_hodge :
    GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.AbelianDeRhamFree := by
  intro hC hA R _ A _ g hab hg
  exact free_of hC hA R A g hab hg _ (Category.comp_id _)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamPoincareDualityOfCubeDual
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CubeDual

theorem lam_mul_left (hC : GlobalTheory.Published.CubeTheorem) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) {T : Over S} (a a' t : T ⟶ A) :
    lam (cls L hL) (a * a') t = lam (cls L hL) a t + lam (cls L hL) a' t := by
  have h := hC S A hA L hL T a a' t
  have hl := LB.isLB_linComb hL (fun k : Fin 8 ↦ (![a * a' * t, a * a', a * t, a' * t, a, a', t, 1] k).left)
    ![1, -1, -1, -1, 1, 1, 1, -1]
  have e := (cls_eq_zero_iff hl).2 h
  rw [cls_linComb hL _ _ hl, Fin.sum_univ_eight] at e
  simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul] at e
  unfold lam
  rw [← sub_eq_zero, ← e]
  abel

theorem evc_lam {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hP : (abelian₂ A L).IsLB)
    {Y : Over S} (a b : Y ⟶ A) : evc hP a b = lam (cls L hL) a b := by
  rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
    lift_snd]

theorem isAdditive_lam (hC : GlobalTheory.Published.CubeTheorem) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) (hP : (abelian₂ A L).IsLB) : IsAdditive (abelian₂ A L) ∧ IsAdditive (swap (abelian₂ A L)) := by
  haveI := hA.comm
  have hs : (swap (abelian₂ A L)).IsLB := pull_isLB hP _
  refine ⟨(isAdditive_iff hP).2 fun Y a a' t ↦ ?_, (isAdditive_iff hs).2 fun Y a a' t ↦ ?_⟩
  · rw [evc_lam hL, evc_lam hL, evc_lam hL]
    exact lam_mul_left hC hA hL a a' t
  · rw [evc_swap hP hs, evc_swap hP hs, evc_swap hP hs, evc_lam hL, evc_lam hL, evc_lam hL, lam_comm, lam_comm _ t a,
      lam_comm _ t a']
    exact lam_mul_left hC hA hL a a' t

theorem mono_of_isPerfect' {S : Scheme.{0}} {A B B' : Over S} [GrpObj A] [GrpObj B] [GrpObj B']
    {P : LB (A ⊗ B).left} {P' : LB (A ⊗ B').left} (h : IsDual A B' P') (hP : IsPerfect A B P) (x : B ⟶ B')
    (hx : LBIso P (ev P' (fst A B) (snd A B ≫ x))) [IsMonHom x] : Mono x := by
  have h' : (ev P' (fst A B) (snd A B ≫ x)).IsLB := pull_isLB h.isLB _
  have hc : cls P hP.isLB = cls _ h' := (cls_eq_iff hP.isLB h').2 hx
  have key : ∀ {Y : Over S} (a : Y ⟶ A) (t : Y ⟶ B), evc hP.isLB a t = evc h.isLB a (t ≫ x) := by
    intro Y a t
    show CechPic.pull (lift a t).left (cls P hP.isLB) = _
    rw [hc, cls_ev h.isLB, pull_evc, lift_fst, lift_snd_assoc]
  refine ⟨fun {T} u v huv ↦ ?_⟩
  have hw : (u * v⁻¹) ≫ x = 1 := by rw [MonObj.mul_comp, GrpObj.inv_comp, huv, mul_inv_cancel]
  have t := hP.ker_right T (u * v⁻¹) ((triv_ev_iff hP.isLB _ _).2 (by
    rw [key, Category.assoc, hw, MonObj.comp_one, evc_one_right h.isLB h.zero]))
  rwa [mul_inv_eq_one] at t

theorem abelianDeRham_duality : GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme →
    GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham.Free → GlobalTheory.Published.AbelianDeRham.Duality := by
  intro hC hD hPD hF R _ A _ g hA hg L hL ψ hψ
  haveI := hA.comm
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨haddL, haddS⟩ := isAdditive_lam hC hA hL hP
  obtain ⟨B, _, P, hB, hdim, h1, h2⟩ := hD (Sp R) A hA
  have hgB := hdim g hg
  obtain ⟨x, hx, -⟩ := h1.univ A (abelian₂ A L) hP haddL
  haveI hmx : IsMonHom x := GlobalTheory.AbDual.isMonHom_of_classifying (Sp R) A A B (abelian₂ A L) P h1 h2.additive hP haddS x hx
  have perf := h1.isPerfect h2
  obtain ⟨φ, hφ⟩ := exists_isCorrForm (cupSquare_of_free hF (AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB) (smooth_prod hg hgB))
    perf.isLB perf.zero_left perf.zero_right
  have e : LBIso (P.pull (lift (fst A A) (snd A A ≫ x)).left) (abelian₂ A L) :=
    (cls_eq_iff (pull_isLB h1.isLB _) hP).1 ((cls_eq_iff hP (pull_isLB h1.isLB _)).2 hx).symm
  obtain ⟨φ', hφ', k⟩ := hφ.pull h1.isLB (homMor (dp0 R) (𝟙 _) (𝟙 A)) (homMor (dp0 R) (𝟙 _) x)
    (h := (lift (fst A A) (snd A A ≫ x)).left)
    (by simp only [← Over.comp_left, lift_fst, Category.comp_id])
    (by simp only [← Over.comp_left, lift_snd])
    hP e
  have hψ' := isCorrForm_lam hψ
  obtain rfl := hφ'.unique (cupSquare_of_free hF (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) (smooth_prod hg hg)) hP hψ'
  have hform : ∀ a b, φ' a b = φ a (push (dp0 R) (𝟙 _) x b) := fun a b ↦ by
    have := k (push (dp0 R) (𝟙 _) (𝟙 A) a) a (push (dp0 R) (𝟙 _) x b) b (fun _ ↦ rfl) fun _ ↦ rfl
    rw [this, push_id]
    rfl
  obtain ⟨-, orth⟩ := hPD R A B g hA hB hg hgB P h1 φ hφ
  refine ⟨fun a ha b hb ↦ ?_, fun hK ↦ ?_⟩
  · rw [hform]
    exact orth a ha _ (push_mem_Fil x hb)
  · have mx : Mono x := mono_of_isPerfect' h1 (isPerfect_lam hL hK) x hx
    have ix : IsIso x := _root_.GlobalTheory.AbMonoIsoAny.isIso_of_mono (Sp R) A B hA hB g hg hgB x hmx mx
    have hd : IsDual A A (abelian₂ A L) := GlobalTheory.AbDual.transport (Sp R) A A B (abelian₂ A L) P h1 hP x ix hmx hx
    exact (hPD R A A g hA hA hg hg (abelian₂ A L) hd φ' hψ').1

end GlobalTheory.CubeDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDualCrystalOfHyp
section
namespace GlobalTheory

theorem abelianDualCrystal_of_dual_of_smoothLift :
    GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianDualCrystal :=
  fun h₁ h₂ => ⟨h₁, _root_.GlobalTheory.CrysLift.crystallineDeRham_of_smoothLift h₂⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianHeightBoundedBelow
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt

namespace GlobalTheory.AmpleHtLow

theorem nsq_shift_pow {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (t : (k →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (m : ℕ) (σ : k →+* ℂ) (f : (L.pow m).B.ι → CxPts p σ → ℂ)
    (y : CxPts p σ) :
    (((L.shift t ht).pow m).φ σ).nsq f y = ((L.pow m).φ σ).nsq f y * Real.exp (-(2 * m * t σ)) := by
  simp only [Weight.nsq, HermLB.pow, HermLB.shift, Weight.pow]
  erw [Weight.zpow_φ, Weight.zpow_φ]
  rw [mul_assoc, ← Real.exp_add]
  simp only [Weight.addFn]
  congr 2
  push_cast
  ring

theorem small_of_shift : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (L : HermLB p) (m : ℕ), 1 ≤ m → ∀ (s : (L.pow m).B.Sec), ∃ c : ℝ,
      s ∈ ((L.shift (fun _ => -c) fun _ => rfl).pow m).smallSec := by
  intro k _ X p D hX L m hm s
  have := hX.finite_emb
  have hb : ∀ σ : k →+* ℂ, ∃ K : ℝ, ∀ y, ((L.pow m).φ σ).nsq (CxPts.secVal p σ s) y ≤ K := fun σ => by
    have := hX.compactSpace σ
    obtain ⟨K, hK⟩ := (isCompact_range (((L.pow m).cInf σ).continuous_nsq s)).bddAbove
    exact ⟨K, fun y => hK ⟨y, rfl⟩⟩
  choose K hK using hb
  have := Fintype.ofFinite (k →+* ℂ)
  have hK' : ∀ σ, K σ ≤ ∑ τ, |K τ| + 1 := fun σ => by
    have := Finset.single_le_sum (fun τ (_ : τ ∈ Finset.univ) => abs_nonneg (K τ)) (Finset.mem_univ σ)
    linarith [le_abs_self (K σ)]
  have h1 : (1 : ℝ) ≤ ∑ τ, |K τ| + 1 := by
    linarith [Finset.sum_nonneg fun τ (_ : τ ∈ Finset.univ) => abs_nonneg (K τ)]
  set K' : ℝ := ∑ τ, |K τ| + 1
  have hl : 0 ≤ Real.log K' := Real.log_nonneg h1
  have hpos : 0 < K' := by linarith
  refine ⟨-(Real.log K' / 2), fun σ y => ?_⟩
  refine (le_of_eq (nsq_shift_pow L (fun _ => -(-(Real.log K' / 2))) (fun _ => rfl) m σ (CxPts.secVal p σ s) y)).trans ?_
  have h0 : 0 ≤ ((L.pow m).φ σ).nsq (CxPts.secVal p σ s) y := by unfold Weight.nsq; positivity
  have h2 : Real.exp (-(2 * (m : ℝ) * -(-(Real.log K' / 2)))) ≤ K'⁻¹ := by
    rw [show -(2 * (m : ℝ) * -(-(Real.log K' / 2))) = -((m : ℝ) * Real.log K') by ring,
      ← Real.exp_log hpos, ← Real.exp_neg, Real.exp_log hpos]
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  calc ((L.pow m).φ σ).nsq (CxPts.secVal p σ s) y * Real.exp (-(2 * (m : ℝ) * -(-(Real.log K' / 2))))
      ≤ K' * K'⁻¹ := mul_le_mul ((hK σ y).trans (hK' σ)) h2 (Real.exp_pos _).le hpos.le
    _ = 1 := mul_inv_cancel₀ hpos.ne'

end GlobalTheory.AmpleHtLow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLiftDeRhamUnique
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OActLift


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
set_option autoImplicit false in
theorem _root_.GlobalTheory.OActLift.isMonHom_mul_of_comm {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (f g : G ⟶ G) [IsMonHom f] [IsMonHom g] : IsMonHom (f * g) := by
  rw [Hom.mul_def]
  infer_instance

end GlobalTheory.OActLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalFormsPrimitiveOfFramesStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianSchemeGlobalFormsPrimitive_of_frames : (∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.HasFrame (OAff A.hom) ∧ GlobalTheory.AbCoh.UConst A.hom ∧ GlobalTheory.AbCoh.PrimF A) → FormSt := by
  first | exact @GlobalTheory.FormsOnAb.formSt_of | exact GlobalTheory.FormsOnAb.formSt_of | (intros; apply GlobalTheory.FormsOnAb.formSt_of <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeLiftAlongNilpotent
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem abelianScheme_constLift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀) (s : R₀ →+* R), π.comp s = RingHom.id R₀ →
    ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom →
      ∃ (A : Over (Sp R)) (_ : GrpObj A) (i : A₀.left ⟶ A.left) (_ : IsGrpPullback A₀ A (spMap π) i),
        IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom := by
  intro R R₀ _ _ π s hs A₀ _ g hA hg
  have hAs := isGrpPullback_pullback A₀ (spMap s)
  have hid : spMap π ≫ spMap s = 𝟙 (Sp R₀) := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hs]
    exact Spec.map_id _
  have hBA := isGrpPullback_pullback ((Over.pullback (spMap s)).obj A₀) (spMap π)
  have hB0 := (hBA.comp hAs).congr hid rfl
  obtain ⟨e, he, -⟩ := grpPullback_iso hB0 (GlobalTheory.CrysConn.isGrpPullback_refl A₀)
  haveI : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have h0B := isGrpPullback_of_iso e.symm
  refine ⟨(Over.pullback (spMap s)).obj A₀, inferInstance, _, (h0B.comp hBA).congr (Category.id_comp _) rfl,
    isAbelianScheme_pullback_obj (spMap s) A₀ hA, ?_⟩
  exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hg

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemePresentedBySystem
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem exists_isCompl_ker_of_projective {R : Type} {M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Projective R N] (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    ∃ C : Submodule R M, IsCompl (LinearMap.ker f) C := by
  obtain ⟨g, hg⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hfg : ∀ y, f (g y) = y := fun y ↦ LinearMap.congr_fun hg y
  refine ⟨LinearMap.range g, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x hx ⟨y, rfl⟩
    have : y = 0 := (hfg y).symm.trans hx
    rw [this, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have e : x = (x - g (f x)) + g (f x) := by abel
    rw [e]
    refine Submodule.add_mem_sup ?_ (LinearMap.mem_range_self g _)
    rw [LinearMap.mem_ker, map_sub, hfg, sub_self]

theorem mem_smul_top_of_tmul_eq_zero {R R₀ M : Type} [CommRing R] [CommRing R₀] [AddCommGroup M] [Module R M]
    (π : R →+* R₀) (hπ : Function.Surjective π) {I : Ideal R} (hk : RingHom.ker π = I) (x : M)
    (h : letI := π.toAlgebra; (1 : R₀) ⊗ₜ[R] x = 0) : x ∈ I • (⊤ : Submodule R M) := by
  letI := π.toAlgebra
  subst hk
  let f : (R ⧸ RingHom.ker π) ≃ₐ[R] R₀ :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R R₀) hπ
  let E : R₀ ⊗[R] M ≃ₗ[R] M ⧸ (RingHom.ker π) • (⊤ : Submodule R M) :=
    (TensorProduct.congr f.toLinearEquiv.symm (LinearEquiv.refl R M)).trans
      (TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker π))
  have h1 : E ((1 : R₀) ⊗ₜ[R] x) = Submodule.Quotient.mk x := by
    have : f.symm (1 : R₀) = Ideal.Quotient.mk _ 1 := by rw [map_one, map_one]
    change TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker π) (f.symm 1 ⊗ₜ[R] x) = _
    rw [this, TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul]
  rw [h, map_zero, eq_comm, Submodule.Quotient.mk_eq_zero] at h1
  exact h1

theorem full_and_isCompl : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → ∀ S : Sys I π A₀.hom, S.Presents A'.hom i' → S.Full hI ∧ ∃ N, IsCompl (S.K hI) N := by
  intro H HD R R₀ _ _ I hI π hπ hk g A₀ _ A' _ i' h' hA hg S hS
  have hpb : IsPullback i' A₀.hom A'.hom (spMap π) := h'.1
  obtain ⟨e, he1, he2⟩ := _root_.GlobalTheory.LiftSys.cohomology_presents R R₀ I hI π hπ hk A₀.left A₀.hom S A'.left A'.hom i' hpb hS
  have hsm : Smooth A'.hom := hA.smooth
  haveI : IsProper A'.hom := hA.proper
  have hsep : IsSeparated A'.hom := inferInstance
  have hqc : QuasiCompact A'.hom := inferInstance
  have hw : i' ≫ A'.hom = (A₀.hom ≫ spMap π) ≫ spMap (RingHom.id R) := by
    rw [Cris.spMap_id, Category.comp_id]; exact hpb.w
  let m : IsMor (dp0 R) A'.hom (divided₂ hI) (A₀.hom ≫ spMap π) (RingHom.id R) i' := IsMor.of_dividedPowersZeroIdeal _ hw
  have hm := (H.toCrystallineDeRham R I (divided₂ hI) (isDPNilpotent_squareZero hI) R₀ π hπ hk A'.left A₀.left A'.hom A₀.hom i'
    hsm hsep hqc hpb m).1
  have hc := H.bijective_cechDeRhamComparison_degreeOne A'.hom hsm hsep hqc
  obtain ⟨-, -, -, ⟨-, hproj, -⟩, ⟨-, -, hto⟩, hbc⟩ := HD R A' g hA hg
  have key : ∀ c, S.r hI (m.pull1 c) = e (toHO1 A'.hom (cmp1 A'.hom c)) := fun c ↦ (he1 m c).symm
  have hr : Function.Surjective (S.r hI) := by
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨w, rfl⟩ := hto x
    obtain ⟨c, rfl⟩ := hc.2 w
    exact ⟨m.pull1 c, key c⟩
  haveI : Module.Projective R (GlobalTheory.CatCoh.H1 S.F) := Module.Projective.of_equiv e
  refine ⟨?_, exists_isCompl_ker_of_projective (S.r hI) hr⟩
  intro z hz
  have hz0 : S.redO.pullbackOneCocycle z = 0 := by
    refine Subtype.ext (funext fun U ↦ funext fun V ↦ funext fun a ↦ ?_)
    exact (S.ker V _).2 (hz U V a)
  have h0 : S.redO.pull1 (H1.mk _ z) = 0 := by
    rw [CoefMap.pullCohomologyOne_class, hz0, map_zero]
  set x := e.symm (H1.mk _ z) with hxdef
  have hx0 : IsPullO hpb.w x 0 := by
    have := he2 x
    rwa [hxdef, LinearEquiv.apply_symm_apply, h0] at this
  letI := π.toAlgebra
  obtain ⟨-, -, e', he'⟩ := hbc R₀ A₀.left A₀.hom i' hpb
  have h1 : e' ((1 : R₀) ⊗ₜ[R] x) = 0 := by
    have a := he' x
    unfold IsPullO at a hx0
    exact (pairRes_injective i' A₀.hom).1 (a.symm.trans (hx0.trans (map_zero _).symm))
  have hxI : x ∈ I • (⊤ : Submodule R (HO1 A'.hom)) :=
    mem_smul_top_of_tmul_eq_zero π hπ hk x ((LinearEquiv.map_eq_zero_iff e').1 h1)
  have hzI : H1.mk _ z ∈ I • (⊤ : Submodule R (GlobalTheory.CatCoh.H1 S.F)) := by
    have : H1.mk _ z = e x := by rw [hxdef, LinearEquiv.apply_symm_apply]
    rw [this]
    have hm' : e.toLinearMap x ∈ Submodule.map e.toLinearMap (I • ⊤) := Submodule.mem_map_of_mem hxI
    rw [Submodule.map_smul''] at hm'
    exact Submodule.smul_mono le_rfl le_top hm'
  have hsurjI : Submodule.map (S.r hI) (I • ⊤) = I • (⊤ : Submodule R (GlobalTheory.CatCoh.H1 S.F)) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hr]
  rw [← hsurjI] at hzI
  obtain ⟨c, hc, hcz⟩ := hzI
  exact ⟨c, hc, hcz⟩

end GlobalTheory.LiftSys
end
end

