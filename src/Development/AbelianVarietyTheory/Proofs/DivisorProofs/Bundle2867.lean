module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2619
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2106
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfCharZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0727
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2844
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2757
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2840
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FrameSqEqOfSymmetricThetaElement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepsXSt
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0525

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NondegOfFieldExtension
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart.AbPol

theorem relAmple_lam_diag {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) :
    haveI := P.isAb.comm
    RelAmple P.A ((abelian₂ P.A P.L).pull (lift (𝟙 P.A) (𝟙 P.A)).left) := by
  haveI := P.isAb.comm
  have hL : Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hA := P.isAb
  have hLB := P.isLB
  have hΔ := GlobalTheory.FullSiegel.cls_diag hL.mulPull P
  have hΔ' := pull_isLB (GlobalTheory.FullSiegel.isLB_lam hLB) (lift (𝟙 P.A) (𝟙 P.A)).left
  have R := GlobalTheory.relAmple_finite_pow_iso S P.A P.A (𝟙 _) P.L 2 two_pos hA hA hLB (inferInstanceAs (IsFinite (𝟙 _)))
  have R' := GlobalTheory.relAmple_finite_pow_iso S P.A P.A (𝟙 _) (lbPow P.L 2) 2 two_pos hA hA (isLB_lbPow hLB 2)
    (inferInstanceAs (IsFinite (𝟙 _)))
  exact R'.2.2.2 _ hΔ' ((CechPic.cls_eq_iff (isLB_lbPow hLB 2) hΔ').1 ((CechPic.cls_lbPow hLB 2 _).trans hΔ.symm))
    (R.2.1.2 P.ample)

theorem isBiRig_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] {P : LB (G2 A).left}
    (h : IsBiRig A P) : IsBiRig ((Over.pullback f).obj A) (P.pull (Pdiv.PullbackComparison.pφ₂ f A)) := by
  obtain ⟨hP, ⟨t₁, ht₁⟩, ⟨t₂, ht₂⟩, hs⟩ := h
  exact ⟨pull_isLB hP _,
    gen_chartPull (chartPullLinComb P _ _ _ _ (Pdiv.PullbackComparison.pφ f A) (fun _ => Pdiv.PullbackComparison.lift_one_id f A)) t₁ ht₁,
    gen_chartPull (chartPullLinComb P _ _ _ _ (Pdiv.PullbackComparison.pφ f A) (fun _ => Pdiv.PullbackComparison.lift_id_one f A)) t₂ ht₂,
    LBIso.chartPull (Geo.Tor.chartPullPull P _ _ rfl)
      (chartPullLinComb P _ _ _ _ (Pdiv.PullbackComparison.pφ₂ f A) (fun _ => Pdiv.PullbackComparison.lift_swap f A)) hs⟩

theorem nondeg_of_fieldExtension {K K' : Type} [Field K] [Field K'] (i : K →+* K') (A : Over (Sp K)) [GrpObj A]
    (A' : Over (Sp K')) [GrpObj A'] {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}
    (h : IsGrpPullback A' A (spMap i) φ) (sq : IsSquare φ φ₂) {P : LB (A ⊗ A).left} {P' : LB (A' ⊗ A').left}
    (hP : P.IsLB) (hP' : P'.IsLB) (e : LBIso P' (P.pull φ₂))
    (hn : ∀ (T : Over (Sp K')) (x : T ⟶ A'),
      (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x = 1)
    (T : Over (Sp K)) (x : T ⟶ A) (hx : ∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) : x = 1 := by
  letI := i.toAlgebra
  have : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (Spec (CommRingCat.of K')) := inferInstanceAs (Nonempty (PrimeSpectrum K'))
  have : Flat (spMap i) := inferInstanceAs (Flat (specOf i))
  have : Surjective (spMap i) := inferInstanceAs (Surjective (specOf i))
  let T' : Over (Sp K) := Over.mk (pullback.fst T.hom (spMap i) ≫ T.hom)
  let q : T' ⟶ T := Over.homMk (pullback.fst T.hom (spMap i)) rfl
  have hq : Epi q.left := Flat.epi_of_flat_of_surjective (pullback.fst T.hom (spMap i))
  have key : q ≫ x = 1 := by
    refine GlobalTheory.NondegSpread.eq_one_of_generic_nondeg K K' A A' φ φ₂ h sq P P' hP hP' e hn T'
      (pullback.snd T.hom (spMap i)) pullback.condition (q ≫ x) ?_
    have z := (CechPic.cls_eq_zero_iff (pull_isLB hP _)).2 hx
    refine (CechPic.cls_eq_zero_iff (pull_isLB hP _)).1 ?_
    rw [CechPic.cls_pull hP] at z ⊢
    have e' : lift (snd A T' ≫ q ≫ x) (fst A T') = (A ◁ q) ≫ lift (snd A T ≫ x) (fst A T) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [e', Over.comp_left, CechPic.pull_comp, z, map_zero]
  have e₂ : q ≫ x = q ≫ (1 : T ⟶ A) := by rw [key, MonObj.comp_one]
  exact Over.OverMorphism.ext ((cancel_epi q.left).1 (congrArg (fun r => r.left) e₂))

theorem relAmple_of_generic (O K : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Field K]
    [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A] (hA : IsAbelianScheme A) {M : LB A.left} (hM : M.IsLB)
    (hamp : RelAmple ((Over.pullback (spMap (algebraMap O K))).obj A) (M.pull (pullback.fst A.hom _))) :
    RelAmple A M := by
  haveI := hA.proper
  haveI := hA.smooth
  refine GlobalTheory.ProperFinite.relAmple_of_geometricFibres A hM fun K' _ _ y => ?_
  obtain ⟨g, rfl⟩ : ∃ g : O →+* K', spMap g = y := ⟨(Spec.preimage y).hom, by simp [spMap]⟩
  haveI : (RingHom.ker g).IsPrime := RingHom.ker_isPrime g
  let Op := Localization.AtPrime (RingHom.ker g)
  haveI : IsDomain Op := IsLocalization.isDomain_localization (RingHom.ker g).primeCompl_le_nonZeroDivisors
  haveI : IsNoetherianRing Op := IsLocalization.isNoetherianRing (RingHom.ker g).primeCompl _ inferInstance
  haveI : IsIntegrallyClosed Op := isIntegrallyClosed_of_isLocalization Op (RingHom.ker g).primeCompl
    (RingHom.ker g).primeCompl_le_nonZeroDivisors
  letI : Algebra Op K := IsLocalization.localizationAlgebraOfSubmonoidLe Op K (RingHom.ker g).primeCompl
    (nonZeroDivisors O) (RingHom.ker g).primeCompl_le_nonZeroDivisors
  haveI : IsScalarTower O Op K := IsLocalization.localization_isScalarTower_of_submonoid_le Op K
    (RingHom.ker g).primeCompl (nonZeroDivisors O) (RingHom.ker g).primeCompl_le_nonZeroDivisors
  haveI : IsFractionRing Op K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (RingHom.ker g).primeCompl Op K
  have e₁ : spMap (algebraMap Op K) ≫ spMap (algebraMap O Op) = spMap (algebraMap O K) := by
    rw [← spMap_comp, ← IsScalarTower.algebraMap_eq]
  have hu : ∀ x : (RingHom.ker g).primeCompl, IsUnit (g x) := fun x => isUnit_iff_ne_zero.2 x.2
  let g' : Op →+* K' := IsLocalization.lift hu
  have e₂ : spMap g' ≫ spMap (algebraMap O Op) = spMap g := by
    rw [← spMap_comp]
    exact congrArg spMap (IsLocalization.lift_comp hu)
  let Ap := (Over.pullback (spMap (algebraMap O Op))).obj A
  have pp := isGrpPullback_pullback A (spMap (algebraMap O Op))
  have pK := isGrpPullback_pullback A (spMap (algebraMap O K))
  let φ := pp.1.lift (pullback.fst A.hom (spMap (algebraMap O K)))
    (((Over.pullback (spMap (algebraMap O K))).obj A).hom ≫ spMap (algebraMap Op K))
    (by rw [Category.assoc, e₁]; exact pK.1.w)
  have hφ : φ ≫ pullback.fst A.hom (spMap (algebraMap O Op)) = pullback.fst A.hom (spMap (algebraMap O K)) :=
    pp.1.lift_fst _ _ _
  have hpb : IsGrpPullback _ Ap (spMap (algebraMap Op K)) φ :=
    pp.cancel (pK.congr e₁.symm hφ.symm) (pp.1.lift_snd _ _ _)
  have hp : RelAmple Ap (M.pull (pullback.fst A.hom _)) :=
    GlobalTheory.AmpleGenericLocal.relAmple_of_generic Op K Ap _ φ (Out.TLinPf.isAb_pullback _ A hA) hpb _ _ (pull_isLB hM _)
      (pull_isLB hM _) (GlobalTheory.FibreAmple.lbIso_pull_comp hφ.symm (GlobalTheory.lbIso_refl (pull_isLB hM _))) hamp
  exact GlobalTheory.isAmpleLB_of_relAmple_of_isAffine (Over.mk (pullback.snd A.hom (spMap g))) (pull_isLB hM _)
    (GlobalTheory.FibreAmple.relAmple_of_factor hM pp.1 (IsPullback.of_hasPullback A.hom (spMap g)) (spMap g') e₂
      (pull_isLB hM _) (GlobalTheory.lbIso_refl (pull_isLB hM _)) hp)

theorem isSquare_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {ψ : G''.left ⟶ G'.left} {ψ₂ : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : IsSquare ψ ψ₂) (h : IsSquare φ φ₂) : IsSquare (ψ ≫ φ) (ψ₂ ≫ φ₂) :=
  ⟨by rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc],
    by rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]⟩

theorem isPPol_of_field (O K' : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Field K']
    (j : O →+* K') (hj : Function.Injective j) (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (A' : Over (Sp K')) [GrpObj A'] {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}
    (h : IsGrpPullback A' A (spMap j) φ) (sq : IsSquare φ φ₂) {P : LB (A ⊗ A).left} {P' : LB (A' ⊗ A').left}
    (hP : IsBiRig A P) (hP' : P'.IsLB) (e : LBIso P' (P.pull φ₂))
    (ha : RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left))
    (hn : ∀ (T : Over (Sp K')) (x : T ⟶ A'),
      (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x = 1) : IsPPol A P := by
  haveI := hA.proper
  let K := FractionRing O
  let i : K →+* K' := IsFractionRing.lift hj
  have e₁ : spMap i ≫ spMap (algebraMap O K) = spMap j := by
    rw [← spMap_comp]
    exact congrArg spMap (RingHom.ext fun x => IsFractionRing.lift_algebraMap hj x)
  let f := spMap (algebraMap O K)
  let AK := (Over.pullback f).obj A
  have pK := Pdiv.PullbackComparison.isGrpPullback f A
  have sK := Pdiv.PullbackComparison.isSquare f A
  let ψ := pK.1.lift φ (A'.hom ≫ spMap i) (by rw [Category.assoc, e₁]; exact h.1.w)
  have hψ : ψ ≫ Pdiv.PullbackComparison.pφ f A = φ := pK.1.lift_fst _ _ _
  have hpb : IsGrpPullback A' AK (spMap i) ψ := pK.cancel (h.congr e₁.symm hψ.symm) (pK.1.lift_snd _ _ _)
  have sψ := GlobalTheory.LamPull.exists_isSquare hpb.1.w
  have e₂ := GlobalTheory.LamPull.isSquare_unique sq (hψ ▸ isSquare_comp sψ sK)
  have hM := pull_isLB hP.1 (lift (𝟙 A) (𝟙 A)).left
  haveI : IsProper A'.hom := MorphismProperty.of_isPullback h.1 hA.proper
  have ha' : RelAmple A' ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull φ) :=
    (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A' (pull_isLB hM φ)).2
      ((GlobalTheory.isAmpleLB_congr (pull_isLB hP' _) (pull_isLB hM φ) (GlobalTheory.SiegelPull.diag_iso sq e)).1
        ((GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A' (pull_isLB hP' _)).1 ha))
  have hamp : RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) :=
    relAmple_of_generic O K A hA hM (GlobalTheory.FibreAmple.relAmple_of_fieldExtension hM i (IsPullback.of_hasPullback A.hom f)
      (e₁ ▸ h.1) (pull_isLB hM _) (GlobalTheory.lbIso_refl (pull_isLB hM _)) ha')
  have hPK := pull_isLB hP.1 (Pdiv.PullbackComparison.pφ₂ f A)
  refine ⟨hP, hamp, GlobalTheory.NondegSpread.nondeg_of_generic O K A AK _ _ hA pK sK P _ hP.1 hPK (GlobalTheory.lbIso_refl hPK)
    hP.2.1 hP.2.2.1 hP.2.2.2 hamp (nondeg_of_fieldExtension i AK A' hpb sψ hPK hP' ?_ hn)⟩
  exact LBIso.trans hP' (pull_isLB hP.1 _) (pull_isLB hPK _) e
    (GlobalTheory.FibreAmple.lbIso_pull_comp e₂ (GlobalTheory.lbIso_refl hPK))

theorem exists_isPPol_away : ∀ (g n : ℕ) (φ : InvFun ℤ), 3 ≤ n → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) → ∃ (A : Over (Sp (Localization.Away (∏ k, C.t k)))) (_ : GrpObj A) (_ : IsCommMonObj A) (π₀ : A.left ⟶ G₁.left) (π₂ : (G2 A).left ⟶ (G2 G₁).left), IsGrpPullback A G₁ (spMap (algebraMap C.R (Localization.Away (∏ k, C.t k)))) π₀ ∧ IsSquare π₀ π₂ ∧ IsAbelianScheme A ∧ IsPPol A (P.pull π₂) := by
  intro g n φ hn C G₁ _ _ P ⟨hCN, _, hG, hP, hU⟩ hab
  obtain ⟨hmono, -, hcone, hdef, ht⟩ := GlobalTheory.TChart.Taut.monomial_chart g n φ (by omega) C
  have hn' : (0 : ℤ) < n := by omega
  obtain ⟨R', _, _, _, ρ, -, D, ε, hCN', hρ, hfin, -, -, href, -⟩ :=
    GlobalTheory.PolDeg.refine_monomial_of_polarised C.R C.Q C.m C.t (fun k => (n : ℤ) • C.δ k) hCN hmono C.bd ht
      (fun k y z => by simp only [LinearMap.smul_apply, (hcone.mem k).1 y z])
      (fun k y => by simpa only [LinearMap.smul_apply, smul_eq_mul] using mul_nonneg hn'.le (hcone.nonneg k y))
      (fun y hy => by
        obtain ⟨k, hk⟩ := hdef y hy
        exact ⟨k, by simpa only [LinearMap.smul_apply, smul_eq_mul] using mul_pos hn' hk⟩)
  obtain ⟨G', _, _, π, π₂, B, U, hπ, sπ, eπ⟩ := hU R' ρ hCN' hρ hfin D ε href
  set t := ∏ k, C.t k with htd
  have ht0 : t ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => ht k
  let O := Localization.Away t
  haveI := hCN.1
  haveI := hCN.2.1
  have hle : Submonoid.powers t ≤ nonZeroDivisors C.R := powers_le_nonZeroDivisors_of_noZeroDivisors ht0
  haveI : IsDomain O := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing O := IsLocalization.isNoetherianRing (Submonoid.powers t) _ inferInstance
  haveI : IsIntegrallyClosed O := isIntegrallyClosed_of_isLocalization O (Submonoid.powers t) hle
  let f := spMap (algebraMap C.R O)
  let A := (Over.pullback f).obj G₁
  have hG' : IsSemiAbelian A := IsSemiAbelian.pullback f G₁ hG
  have habA : abLocus A = Set.univ := Set.eq_univ_of_forall fun z =>
    (abLocus_pullback abLocusOne hG (IsPullback.of_hasPullback G₁.hom f) z).1 ((hab _).2 fun hz =>
      z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hz (IsLocalization.Away.algebraMap_isUnit t)))
  have hA : IsAbelianScheme A :=
    { comm := hG'.comm
      smooth := hG'.smooth
      proper := GlobalTheory.AbLocusProperNormal.isProper_of_abLocus_eq_univ _ _ hG' habA
      geomConnected := hG'.geomConnected }
  have pA := Pdiv.PullbackComparison.isGrpPullback f G₁
  have sA := Pdiv.PullbackComparison.isSquare f G₁
  refine ⟨A, inferInstance, inferInstance, _, _, pA, sA, hA, ?_⟩

  let κ : C.R →+* FractionRing R' := (algebraMap R' (FractionRing R')).comp ρ
  have hκ : Function.Injective κ := (IsFractionRing.injective R' (FractionRing R')).comp hρ
  have hu : IsUnit (κ t) := isUnit_iff_ne_zero.2 ((map_ne_zero_iff κ hκ).2 ht0)
  let j : O →+* FractionRing R' := IsLocalization.Away.lift t hu
  have hjκ : j.comp (algebraMap C.R O) = κ := IsLocalization.Away.lift_comp t hu
  have hj : Function.Injective j := by
    refine (IsLocalization.lift_injective_iff _).2 fun x x' => ?_
    rw [(IsLocalization.injective O hle).eq_iff, hκ.eq_iff]
  have e₁ : spMap j ≫ f = (𝟙 _ ≫ jK R') ≫ spMap ρ := by
    rw [Category.id_comp, ← spMap_comp, hjκ, spMap_comp]
  haveI := U.gen_hom
  haveI := B.isAb.comm
  haveI : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have ha : IsGrpPullback B.A G' (𝟙 _ ≫ jK R') (U.gen.inv.left ≫ pullback.fst G'.hom (jK R')) :=
    (isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G' (jK R'))
  have sa := GlobalTheory.LamPull.exists_isSquare ha.1.w
  have hb := ha.comp hπ
  let ψ := pA.1.lift _ (B.A.hom ≫ spMap j) (by rw [Category.assoc _ _ f, e₁]; exact hb.1.w)
  have hψ : ψ ≫ Pdiv.PullbackComparison.pφ f G₁ = _ := pA.1.lift_fst _ _ _
  have hpb : IsGrpPullback B.A A (spMap j) ψ := pA.cancel (hb.congr e₁.symm hψ.symm) (pA.1.lift_snd _ _ _)
  have sψ := GlobalTheory.LamPull.exists_isSquare hpb.1.w
  have e₂ := GlobalTheory.LamPull.isSquare_unique (isSquare_comp sa sπ) (hψ ▸ isSquare_comp sψ sA)
  have hLG : U.LG.L.IsLB := U.LG.isLB
  have eL : LBIso B.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G'.hom (jK R'))) := by
    have e := (CechPic.cls_eq_iff (pull_isLB B.isLB _) (pull_isLB hLG _)).2 U.ext
    rw [CechPic.cls_pull B.isLB, CechPic.cls_pull hLG] at e
    rw [← CechPic.cls_eq_iff B.isLB (pull_isLB hLG _), CechPic.cls_pull hLG, CechPic.pull_comp, ← e,
      ← CechPic.pull_comp, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, CechPic.pull_id]
  have hΛ := GlobalTheory.FullSiegel.isLB_lam (G := B.A) B.isLB
  have hΛ' := GlobalTheory.FullSiegel.isLB_lam (G := G') hLG
  refine isPPol_of_field O _ j hj A hA B.A hpb sψ (isBiRig_pullback f G₁ hP) hΛ ?_ (relAmple_lam_diag B)
    (GlobalTheory.FullSiegel.eq_one_of_lam_triv B.isLB B.rigid B.ktriv)
  have c₁ := (CechPic.cls_eq_iff hΛ (pull_isLB hΛ' _)).2 (GlobalTheory.LamPull.lbIso_lam_pull ha hLG B.isLB eL sa)
  have c₂ := (CechPic.cls_eq_iff hΛ' (pull_isLB hP.1 _)).2 eπ
  rw [← CechPic.cls_eq_iff hΛ (pull_isLB (pull_isLB hP.1 _) _), c₁, CechPic.cls_pull hΛ', c₂,
    CechPic.cls_pull hP.1, CechPic.cls_pull (pull_isLB hP.1 _), CechPic.cls_pull hP.1, ← CechPic.pull_comp,
    ← CechPic.pull_comp, e₂]

end GlobalTheory.TChart.AbPol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PTaylor0
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AnPer.TaylorClause

theorem isSep {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (h : IsAbelianScheme A) : A.left.IsSeparated := by
  have : IsProper A.hom := h.proper
  rw [Scheme.isSeparated_iff, ← Limits.terminal.comp_from A.hom]
  infer_instance

theorem of_core0 (core : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} {B : Type} [CommRing B] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp ℂ} {σ : B →+* Hol F.V} (e : Unif F s σ) (e₀ : Unif F₀ s₀ (algebraMap ℂ (Hol F₀.V))), X.IsSeparated → X₀.IsSeparated → (0 : I → ℂ) ∈ F.V → (∃ z, z ∈ F₀.V) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (φ₀ : X₀ ⟶ X), (∀ p : Tot Empty g, p.1 ∈ F₀.V → e₀.E p ≫ φ₀ = e.E (0, p.2)) → ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : ℂ, π (algebraMap ℂ D a) = a) → ∀ (N : ℕ) (t : I → D), (∀ i, π (t i) = 0) → (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (j : B →+* D), (∀ b, j b = GlobalTheory.PeriodFamily.taylor N t (σ b).fn) → ∀ (s' : X₀ ⟶ Sp D), s' = s₀ ≫ spMap π → ∀ (n : IsMor (dp0 B) s κ s' j φ₀) (φ : X₀ ⟶ X₀), φ = 𝟙 X₀ → ∀ (k : IsMor (dp0 ℂ) s₀ κ s' (algebraMap ℂ D) φ) (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod e c per → ∀ (m : ℕ) (d : Fin m → D) (cs : Fin m → FirstDeRham s₀) (p : Fin m → Λ → ℂ) (ps : Fin m → Λ →+ Hol F₀.V), (∀ i l, ps i l = algebraMap ℂ _ (p i l)) → (∀ i, IsPeriod e₀ (cs i) (ps i)) → n.pull1 c = ∑ i, d i • k.pull1 (cs i) → ∀ l, ∑ i, d i * algebraMap ℂ D (p i l) = GlobalTheory.PeriodFamily.taylor N t (per l).fn) :
    PTaylor := by
  intro I _ _ g B _ _ 𝒜 _ hA hg y₀ A₀ _ φ₀ h₀ L₀ u₀ F σ e h0 hy hE hτ P₀ hP D _ _ π κ hκ hπ N t ht hN j hj
    A' _ φ' h' m' i h hi k x d hd c per hper
  obtain ⟨hA₀, hg₀⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback _ 𝒜 A₀ φ₀ g h₀ hA hg
  have hsp := (_root_.GlobalTheory.primCris_isBC_of_nilThick A₀ g hA₀ hg₀ D π κ hκ hπ k).2
  have hm : (liftMor κ h).pull (m'.pull c) ∈ Submodule.span D (Set.range k.pull) := by rw [hsp]; trivial
  obtain ⟨m, dd, v, hv⟩ := Submodule.mem_span_set'.1 hm
  choose cs hcs using fun a ↦ (v a).2
  have n : IsMor (dp0 B) (𝒜.hom ≫ 𝟙 _) κ (A₀.hom ≫ spMap π) (j : B →+* D) φ₀ := by
    have := m'.isMor.comp (liftMor κ h).isMor
    rwa [RingHom.id_comp, hi] at this
  have hn : n.pull1 c.1 = ∑ a, dd a • k.isMor.pull1 (cs a).1 := by
    rw [← IsMor.pullback1_comp m'.isMor (liftMor κ h).isMor n (fun _ ↦ rfl) hi c.1]
    have := congrArg Subtype.val hv
    rw [Submodule.coe_sum] at this
    refine this.symm.trans (Finset.sum_congr rfl fun a _ ↦ ?_)
    rw [← hcs a]
    rfl
  have key := core (F₀ := fibFam u₀) e (fibUnif u₀) (isSep 𝒜 hA) (isSep A₀ hA₀) h0 ⟨fun a ↦ a.elim, trivial⟩
    (fun l _ ↦ (hτ l).symm) φ₀ (fun p _ ↦ (hE p.2).symm) D π κ hκ hπ N t ht hN (j : B →+* D) hj
    (A₀.hom ≫ spMap π) (by rw [Category.comp_id]) n (Over.Hom.left (𝟙 A₀)) rfl k.isMor c.1 per hper m dd
    (fun a ↦ (cs a).1) (fun a l ↦ P₀ l (cs a)) _ (fun _ _ ↦ rfl) (fun a ↦ hP (cs a)) hn x
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← key, crysToDR_apply, ← hv, map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [map_smul, ← hcs a, hd, smul_eq_mul]

theorem pTaylor0 : PTaylor := of_core0 GlobalTheory.AnPer.TaylorCore.main

end GlobalTheory.AnPer.TaylorClause
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapSpanTopAndFinrankFromCechPeriods
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem span_periods_eq_top_and_finrank : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ P : u.Λ →+ HdR A, (∀ c : primDR A, IsPer u.ex u.Λ (cmp1 (str A) c.1) fun l => P l c) → Submodule.span ℂ (Set.range P) = ⊤ ∧ Module.finrank ℂ (HdR A) = 2 * g := by
  intro A _ g L u hA P hP
  obtain ⟨b, -, -⟩ := GlobalTheory.exists_basis_of_discrete_of_span_eq_top_complex_pi g u.Λ u.discrete u.full
  refine _root_.GlobalTheory.CechPer.span_eval_eq_top_and_finrank_dual (primDR A) u.Λ (2 * g) b P (fun w hw ↦ ?_) (fun p ↦ ?_)
  · have h0 : (fun l ↦ P l w) = 0 := funext hw
    have h1 := hP w
    rw [h0] at h1
    have h2 := _root_.GlobalTheory.CechPer.eq_zero_of_isPer_zero A g L u hA _ h1
    have h3 : w.1 = 0 := (_root_.GlobalTheory.CechPer.crystallineCechDeRhamComparison_bijective_complexAbelian A hA).1 (h2.trans (map_zero _).symm)
    exact Subtype.ext h3
  · obtain ⟨x, hx⟩ := _root_.GlobalTheory.PerSurj.main A g L u hA p
    obtain ⟨c, rfl⟩ := (_root_.GlobalTheory.CechPer.crystallineCechDeRhamComparison_bijective_complexAbelian A hA).2 x
    have hc := _root_.GlobalTheory.CechPer.mem_primDR_of_isPer A g L u hA c p hx
    exact ⟨⟨c, hc⟩, fun l ↦ congrFun (_root_.GlobalTheory.CechPer.isPer_unique A g L u _ _ _ (hP ⟨c, hc⟩) hx) l⟩

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationBundleSymmetricPullbackOfUniformisat
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.PrimDescent

theorem isPrim_of_unif : AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, LBIso U.LG.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → GlobalTheory.PolDeg.IsPrim D.toPre.P (o.onB.act w) := by
  intro R _ _ _ I hI D A G _ _ hS U O _ _ _ o oA oG hlin w hprim
  have := hI.2.2.2
  haveI := oG.hom w
  haveI := oG.hom (1 + w)
  haveI := o.onB.hom w
  haveI := o.onB.hom (1 + w)
  obtain ⟨⟨ρ, hρ, -⟩, -⟩ := GlobalTheory.JetSer.exists_unique_normPrim _ G U.LG (oG.act w) hprim
  have hRig := GlobalTheory.PullGenG.hasGen_one U.LG
  have h0 := (HasGen.of_gen ρ hρ).neg.add hRig
  obtain ⟨uΨ, huΨ⟩ := h0.gen U.LG.isLB (K' := Fin 4)
    ![(padd G (𝟙 _) (oG.act w)).left, 𝟙 G.left, (oG.act w).left, (toUnit G ≫ η[G]).left] ![1, -2, -1, 2] (by
      have h1' : (toUnit G ≫ η[G] : G ⟶ G) = 1 := rfl
      simp [fsum, Fin.sum_univ_four, Fin.sum_univ_five, GlobalTheory.JetSer.primφ, GlobalTheory.JetSer.primε, lf_single, padd_eq_mul, h1',
        Finsupp.single_neg, single_two, single_neg_two, Matrix.vecHead, Matrix.vecTail]
      abel)
  obtain ⟨u, hu, hn⟩ := GlobalTheory.PsiRescale.exists_normalised U.LG.isLB (oG.act w) uΨ huΨ
  have iG : ∀ i, IsMonHom ((![oG.act (1 + w), 𝟙 G, oG.act w, 1] : Fin 4 → (G ⟶ G)) i) := fun i => by
    fin_cases i
    exacts [oG.hom (1 + w), inferInstanceAs (IsMonHom (𝟙 G)), oG.hom w, inferInstanceAs (IsMonHom (toUnit G ≫ η[G]))]
  have iB : ∀ i, IsMonHom ((![o.onB.act (1 + w), 𝟙 _, o.onB.act w, 1] : Fin 4 → (D.toPre.P.A ⟶ D.toPre.P.A)) i) :=
    fun i => by
    fin_cases i
    exacts [o.onB.hom (1 + w), inferInstanceAs (IsMonHom (𝟙 _)), o.onB.hom w,
      inferInstanceAs (IsMonHom (toUnit _ ≫ η[D.toPre.P.A]))]
  obtain ⟨κ, hκ, -⟩ := GlobalTheory.UT.PullDescent.exists_descent U.toUnifPre GlobalTheory.allSixLaws.1.globalFns hS (fun V _ c => by
      rw [Fin.prod_univ_four]
      show c ^ (1 : ℤ) * c ^ (-2 : ℤ) * c ^ (-1 : ℤ) * c ^ (2 : ℤ) = 1
      group)
    ![oG.act (1 + w), 𝟙 G, oG.act w, 1] ![o.onB.act (1 + w), 𝟙 _, o.onB.act w, 1] (fun e i => by
      have := (U.gt e).q_hom
      fin_cases i
      · exact hlin.q_lin e (1 + w)
      · show (Over.pullback (thick R I e)).map (𝟙 G) ≫ _ = _ ≫ (Over.pullback (thick R I e)).map (𝟙 _)
        rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
      · exact hlin.q_lin e w
      · show (Over.pullback (thick R I e)).map (1 : G ⟶ G) ≫ _ =
          _ ≫ (Over.pullback (thick R I e)).map (1 : D.toPre.P.A ⟶ D.toPre.P.A)
        rw [CategoryTheory.Functor.map_one, CategoryTheory.Functor.map_one, MonObj.one_comp, MonObj.comp_one])
    (fun i => by
      fin_cases i
      · show (oG.act (1 + w)).left = (padd G (𝟙 _) (oG.act w)).left
        rw [oG.map_add, oG.map_one]
      all_goals rfl)
    (ψ := ![(padd D.toPre.P.A (𝟙 _) (o.onB.act w)).left, 𝟙 D.toPre.P.A.left, (o.onB.act w).left,
      (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left])
    (fun i => by
      fin_cases i
      · show (o.onB.act (1 + w)).left = (padd D.toPre.P.A (𝟙 _) (o.onB.act w)).left
        rw [o.onB.map_add, o.onB.map_one]
      all_goals rfl) u hu hn
  exact ⟨κ, hκ.1⟩

end GlobalTheory.PrimDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveH1StructureAbelian
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem axesO1_of_isAbelianScheme (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) : AxesVanishingStructureSheafDegOne A := by
  obtain ⟨-, -, hAA, hgg⟩ := _root_.GlobalTheory.AbCoh.basic_of_isAbelianScheme R A g hA hg
  have h1 := (_root_.GlobalTheory.AbCoh.oStr R A g hA hg).1
  have h2 := (_root_.GlobalTheory.AbCoh.oStr R (A ⊗ A) (g + g) hAA hgg).1
  have hax := (_root_.GlobalTheory.AbCoh.AxesPull.main R A).1
  let f : HO1 A.hom × HO1 A.hom →ₗ[R] HO1 (A ⊗ A).hom :=
    pO1 (fst A A) ∘ₗ LinearMap.fst R _ _ + pO1 (snd A A) ∘ₗ LinearMap.snd R _ _
  let r : HO1 (A ⊗ A).hom →ₗ[R] HO1 A.hom × HO1 A.hom :=
    LinearMap.prod (pO1 (lift (𝟙 A) (toUnit A ≫ η[A]))) (pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)))
  have hrf : ∀ x, r (f x) = x := by
    rintro ⟨a, b⟩
    have e : f (a, b) = pO1 (fst A A) a + pO1 (snd A A) b := rfl
    have e2 : ∀ z, r z = (pO1 (lift (𝟙 A) (toUnit A ≫ η[A])) z, pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)) z) :=
      fun _ ↦ rfl
    rw [e2, e, map_add (f := _), map_add (f := _), (hax a).1, (hax b).2.1, (hax a).2.2.2.1, (hax b).2.2.2.2.1, add_zero, zero_add]
  have hP := (_root_.GlobalTheory.AbCoh.fp_ext_prod).2 R _ _ g g h1 h1
  have hbij := _root_.GlobalTheory.AbCoh.bijective_of_split_of_FP R _ _ (g + g) hP h2 f r hrf
  intro y hy1 hy2
  obtain ⟨x, rfl⟩ := hbij.2 y
  have h0 : r (f x) = 0 := Prod.ext hy1 hy2
  rw [hrf] at h0
  rw [h0, map_zero]

theorem primO1_of_isAbelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → StructureSheafH1Primitive A := by
  intro R _ A _ g hA hg x
  have hax := (_root_.GlobalTheory.AbCoh.AxesPull.main R A).1 x
  have h := axesO1_of_isAbelianScheme R A g hA hg (pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x)
    (by rw [map_sub, map_sub, hax.1, hax.2.1, hax.2.2.1, sub_self, sub_zero])
    (by rw [map_sub, map_sub, hax.2.2.2.1, hax.2.2.2.2.1, hax.2.2.2.2.2, sub_zero, sub_self])
  rw [sub_sub, sub_eq_zero] at h
  exact h

end GlobalTheory.AbCoh
end
end

