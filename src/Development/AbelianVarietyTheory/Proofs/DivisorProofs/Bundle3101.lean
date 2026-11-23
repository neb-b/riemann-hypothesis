module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeLiftWithPrincipalLineBundle
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2021
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2822
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Rosati
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0791
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3087
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveCharZeroTensorRingOfIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRhoPartLieDeRhamQuotient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0098

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrystalReductionSquareZeroArtinian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open GlobalTheory.ZM GlobalTheory.SiegelTor
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open IsLocalRing
open GlobalTheory.AbDual GlobalTheory.AbLaw GlobalTheory.CechPic

namespace GlobalTheory.CrysRed


open GlobalTheory.Published.GrothendieckMessing in
theorem exists_crysRed : ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ (O : Type) [Ring O] (a : GlobalTheory.UPel.HT.OActN O A₀), ∃ red : Crys (divided₂ hsq) (spMap π) A₀ →ₛₗ[π] HdR A₀, Module.Finite C (Crys (divided₂ hsq) (spMap π) A₀) ∧ Module.Projective C (Crys (divided₂ hsq) (spMap π) A₀) ∧ Function.Surjective red ∧ (∀ x, red x = 0 → x ∈ RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) A₀))) ∧ (∀ d y, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl A₀).Corr d y ↔ red d = y) ∧ (∀ (c : O) d, red (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) a c d) = GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) a c (red d)) ∧ ∃ E' M : Submodule C (Crys (divided₂ hsq) (spMap π) A₀), IsCompl E' M ∧ ∀ y, y ∈ Fil A₀ ↔ ∃ d ∈ E', red d = y := by
  intro C C₀ _ _ _ _ π hπ hsq A₀ _ _ hA₀ O _ a
  have hI2 : RingHom.ker π ^ 2 = ⊥ := hsq
  haveI : Nontrivial C₀ := by
    refine ⟨⟨0, 1, fun h ↦ ?_⟩⟩
    have h1 : (1 : C) ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_one]; exact h.symm
    have h2 : (1 : C) ∈ RingHom.ker π ^ 2 := by
      rw [pow_two]; simpa using Ideal.mul_mem_mul h1 h1
    rw [hI2] at h2
    exact one_ne_zero ((Submodule.mem_bot C).1 h2)
  haveI : IsLocalRing C₀ := IsLocalRing.of_surjective' π hπ
  let κ := divided₂ hsq
  have hκ : IsNilDP κ := isDPNilpotent_squareZero hsq
  have ADR : GlobalTheory.Published.AbelianDeRham := GlobalTheory.abelianDeRham
  have GD : GlobalTheory.Published.GrothendieckDeformation :=
    GlobalTheory.Published.grothendieckDeformation_of_lifting GlobalTheory.abelianDeRham GlobalTheory.abelianScheme_hom_lifting_nilpotent_dividedPowers
  obtain ⟨A', _, i', h', hA'⟩ := GlobalTheory.UnobTop.abelianUnobstructed C (RingHom.ker π) hsq C₀ π hπ rfl A₀ hA₀
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C A' hA'
  have HC := (GD C (RingHom.ker π) κ hκ C₀ π hπ rfl).1
  obtain ⟨bij, ⟨N0, hN0⟩, hAdm⟩ := HC g A₀ A' i' h' hA' hg
  let e := LinearEquiv.ofBijective (crysToDR κ h') (HC.crysToDR_bijective h' hA' hg)
  have ee : ∀ xA, crysToDR κ h' (e.symm xA) = xA := e.apply_symm_apply
  letI : Algebra C C₀ := π.toAlgebra
  have hBC := (ADR.2.2.1 C A' g hA' hg C₀ A₀ i' h').1
  obtain ⟨hfinA, hprojA, -⟩ := ADR.1.prim hA' hg
  haveI := hfinA
  haveI := hprojA
  have hfin : Module.Finite C (Crys κ (spMap π) A₀) := Module.Finite.equiv e.symm
  have hproj : Module.Projective C (Crys κ (spMap π) A₀) := Module.Projective.of_equiv e.symm
  let red : Crys κ (spMap π) A₀ →ₛₗ[π] HdR A₀ := hBC.bcMap.comp (crysToDR κ h')
  have hm : ∀ x, (crysRedMor κ rfl A₀).Corr x (red x) := fun x ↦
    (corr_crysToDR_iff rfl h' bij.2 x (red x)).1 (by exact hBC.corr_iff.2 rfl)
  have hcorr : ∀ d y, (crysRedMor κ rfl A₀).Corr d y ↔ red d = y := fun d y ↦
    ⟨fun H ↦ by exact hBC.corr_iff.1 ((corr_crysToDR_iff rfl h' bij.2 d y).2 H), fun H ↦ H ▸ hm d⟩
  have hred : Function.Surjective red := by
    intro y
    let l : primDR A' →ₗ[C] C₀ :=
      { toFun c := y ((redMor h').pull c)
        map_add' := by simp
        map_smul' r c := by rw [LinearMap.map_smulₛₗ, map_smul]; rfl }
    obtain ⟨xA, hx⟩ := Module.projective_lifting_property (Algebra.linearMap C C₀) l hπ
    refine ⟨e.symm xA, ?_⟩
    show hBC.bcMap (crysToDR κ h' (e.symm xA)) = y
    rw [ee]
    exact hBC.corr_iff.1 fun c ↦ (LinearMap.congr_fun hx c).symm
  have hker : ∀ x, red x = 0 → x ∈ (RingHom.ker π) • (⊤ : Submodule C (Crys κ (spMap π) A₀)) := by
    intro x hx
    have hc := hBC.corr_iff.2 hx
    have hmem := GlobalTheory.BirigLift.mem_smul_top_of_forall_mem (RingHom.ker π) (crysToDR κ h' x) fun c ↦
      RingHom.mem_ker.2 ((hc c).symm.trans (LinearMap.zero_apply _))
    have := Submodule.mem_map_of_mem (f := e.symm.toLinearMap) hmem
    rw [Submodule.map_smul''] at this
    have ex : e.symm.toLinearMap (crysToDR κ h' x) = x := e.symm_apply_apply x
    rw [ex] at this
    exact Submodule.smul_mono le_rfl le_top this
  have hact : ∀ (c : O) d, red (GlobalTheory.HTSummand.crysAct κ (spMap π) a c d) =
      GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) a c (red d) := by
    intro c d
    haveI := a.hom c
    refine (hcorr _ _).1 ?_
    rw [GlobalTheory.HTSummand.crysAct_apply, GlobalTheory.HTSummand.crysAct_apply]
    exact GrpMor.Corr.push (m := crysRedMor κ rfl A₀) (crysRedMor κ rfl A₀) (a.act c) (a.act c) (by simp) (hm d)
  have hFN : IsCompl (liftFil κ h') (N0.comap (crysToDR κ h')) :=
    (Submodule.orderIsoMapComap e).symm.isCompl hN0
  refine ⟨red, hfin, hproj, hred, hker, hcorr, hact, liftFil κ h', N0.comap (crysToDR κ h'), hFN, fun y ↦ ⟨?_, ?_⟩⟩
  · intro hy
    obtain ⟨xA, hxA, hc⟩ := (hAdm y).1 hy
    refine ⟨e.symm xA, ?_, ?_⟩
    · show crysToDR κ h' (e.symm xA) ∈ Fil A'
      rw [ee]; exact hxA
    · show hBC.bcMap (crysToDR κ h' (e.symm xA)) = y
      rw [ee]; exact hBC.corr_iff.1 hc
  · rintro ⟨d, hd, rfl⟩
    exact (hAdm (red d)).2 ⟨crysToDR κ h' d, hd, by exact hBC.corr_iff.2 rfl⟩

end GlobalTheory.CrysRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFanOrderIdealThetaCompactification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem idealSt_holds : IdealSt := by
  intro g hg n hn hodd F Z z i hθ φ hφ
  obtain ⟨ι, _, W, hclo, hirr, hpart⟩ := _root_.GlobalTheory.irreducibleComponents_clopen_partition n Z z hθ.1 hθ.2.1
  have key : ∀ c, ∃ (d : ℕ) (J : Z.IdealSheafData), 1 ≤ d ∧ (∀ x ∈ J.support, x ∈ W c ∧ x ∉ Set.range i) ∧
      ∀ (T : Trait F) (ξ : Sp T.V ⟶ Z), jK T.V ≫ ξ = T.y ≫ i → ξ (closedPoint T.V) ∈ W c →
        ∃ a : ℕ, (a : ℝ) = d * φ.evalZ T.β ∧ idlAlong J ξ = Ideal.span {T.ϖ ^ a} := by
    intro c
    obtain ⟨W8, X₁, ι₁, J₁, h1, h2, h4, h5⟩ :=
      _root_.GlobalTheory.Poinc.exists_setup_ideal_over_component g n hg hn hodd F Z z i hθ φ hφ (W c) (hclo c) (hirr c)
    exact _root_.GlobalTheory.PoincDown.idealDescent g n hg hn hodd F Z z i hθ φ hφ (W c) (hclo c) (hirr c) W8 X₁ ι₁ J₁ h1 h2 h4 h5
  choose d J hd hJ hv using key
  exact _root_.GlobalTheory.Poinc.exists_valOn_of_pieces F i φ W J d hclo hpart hd hJ hv

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinExtCubicalSymmetricEvenFactorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finExt_cubicalSymmetric_even_factor : (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsDomain R₀) (_ : IsLocalRing R₀) (ρ₀ : R →+* R₀) (G₀ : Over (Sp R₀)) (_ : GrpObj G₀) (_ : IsCommMonObj G₀) (β₀ : G₀.left ⟶ G.left) (β₀₂ : (G2 G₀).left ⟶ (G2 G).left) (P : GlobalTheory.UU.CP G₀) (A₀ : PolAV (Sp (FractionRing R₀))) (gen₀ : (Over.pullback (jK R₀)).obj G₀ ≅ A₀.A), FinExt ρ₀ ∧ IsGrpPullback G₀ G (spMap ρ₀) β₀ ∧ Geo.Tor.IsSquare β₀ β₀₂ ∧ IsSemiAbelian G₀ ∧ LBIso (abelian₂ G₀ P.L.L) ((abelian₂ G' U'.LG.L).pull (β₀₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) ∧ EvenOn P ∧ IsMonHom gen₀.hom ∧ LBIso (A₀.L.pull gen₀.hom.left) (P.L.L.pull (pullback.fst G₀.hom (jK R₀)))) := by
  first | exact @GlobalTheory.Mum.exists_finExt_cp_factor_even | exact GlobalTheory.Mum.exists_finExt_cp_factor_even | (intros; apply GlobalTheory.Mum.exists_finExt_cp_factor_even <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsIsoCompEqOfSiegRelBy
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

namespace GlobalTheory.UPel.HT.SiegFactor

theorem comp_id_pow {S : Scheme.{0}} {T A : Over S} [GrpObj A] (x : T ⟶ A) (k : ℕ) :
    x ≫ (𝟙 A) ^ k = x ^ k := by
  rw [MonObj.comp_pow, Category.comp_id]

theorem id_pow_comp {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (χ : A ⟶ B) [IsMonHom χ]
    (k : ℕ) : ((𝟙 A) ^ k) ≫ χ = χ ≫ (𝟙 B) ^ k := by
  rw [MonObj.pow_comp, Category.id_comp, comp_id_pow]

theorem isMonHom_epi_id_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) {k : ℕ}
    (hk : 0 < k) : IsMonHom ((𝟙 A) ^ k) ∧ Epi ((𝟙 A) ^ k) := by
  have := hA.comm
  have hm : IsMonHom ((𝟙 A) ^ k) := GlobalTheory.AbLaw.MulN.isMonHom_mulA A k
  obtain ⟨hfl, hsu, hqc⟩ := SiegUniqBase.flat_surjective_qc_pow S A hA k hk
  exact ⟨hm, (GlobalTheory.exists_monHom_factor_of_flat_surjective S A A A _ _ hm hm hfl hsu hqc
    fun _ _ h => h).2⟩

end GlobalTheory.UPel.HT.SiegFactor

namespace GlobalTheory.UPel.HT

end GlobalTheory.UPel.HT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogCanonicalCutAngehrnSiuInduction
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

namespace GlobalTheory.PairStep

theorem exists_lcCut_induction : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → 1 ≤ n →
    letI := algebraΓOfHom p;
    ∀ (Δ : X → ℚ) (r : ℕ) (N₀ : LB X) (x : X) (c : ℕ → ℝ),
      IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < r → N₀.IsLB → IsNef ℂ N₀ → IsBig ℂ N₀ →
      IsClosed ({x} : Set X) → (∀ e ∈ Finset.Icc 1 n, 0 < c e) →
      (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e →
        topologicalKrullDim (Z : Set X) = e →
        c e ^ e < (interNumRed ℂ Z fun _ : Fin e => N₀ : ℝ) / (r : ℝ) ^ e) →
      ∃ A : CartierDiv X, IsAmpleLB (toLB A) ∧ ∀ j, j < n → ∃ (j' : ℕ) (lam μ : ℚ) (m' : ℕ) (D₀ : CartierDiv X),
        j' ≤ j ∧ 0 < m' ∧ D₀.Eff ∧ 0 < μ ∧ (lam : ℝ) < ∑ e ∈ Finset.Icc (j' + 1) n, (e : ℝ) / c e ∧
        (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' =
          lam * interNumRed ℂ C ![N₀] / r - μ * interNumRed ℂ C ![toLB A]) ∧
        LcCut p n (Δ + qWeil D₀ m') x j' := by
  intro hPr X _ _ _ p n hP hn hn1
  letI := algebraΓOfHom p
  intro Δ r N₀ x c hΔ hklt hr hN₀ hnef hbig hx hc hZ
  obtain ⟨m, G, hm, hG⟩ := _root_.GlobalTheory.Discrepancy.exists_isLogCanonicalMultiple_of_kltAt X p n hP hn Δ hΔ hklt
  have hcpos : ∀ e, 1 ≤ e → e ≤ n → 0 < c e := fun e h1 h2 => hc e (Finset.mem_Icc.2 ⟨h1, h2⟩)
  have hgen : closure ({genericPoint X} : Set X) = Set.univ := (genericPoint_spec X).def
  have hdimX : topologicalKrullDim (closure ({genericPoint X} : Set X)) = n := by
    rw [hgen, ← hn]
    exact ((Homeomorph.Set.univ X).isHomeomorph).topologicalKrullDim_eq
  have hcn := hZ (Closeds.closure ({genericPoint X} : Set X)) n isIrreducible_singleton.closure
    (by simpa using specializes_iff_mem_closure.1 (genericPoint_specializes x)) hn1 hdimX
  obtain ⟨c', hc'v, hc'gt⟩ : ∃ c' : ℝ, c' ^ n < (interNumRed ℂ (Closeds.closure ({genericPoint X} : Set X))
      (fun _ : Fin n => N₀) : ℝ) / (r : ℝ) ^ n ∧ c n < c' := by
    have hev := ((continuous_pow n).tendsto (c n)).eventually_lt_const hcn
    exact ((hev.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Set.Ioi (c n) ∈ nhdsWithin (c n) (Set.Ioi (c n)))).exists
  have hcn0 := hcpos n hn1 le_rfl
  have hc'0 : 0 < c' := hcn0.trans hc'gt
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlt : (n : ℝ) / c' < n / c n := div_lt_div_of_pos_left hnpos hcn0 hc'gt
  obtain ⟨β, hβ0, hβ⟩ := exists_rat_btwn (sub_pos.2 hlt)
  have hβ0' : (0 : ℚ) < β := by exact_mod_cast hβ0
  obtain ⟨A, F, a, hA, ha, hF, lam₀, μ₀, m₀, D₀, hm₀, hD₀, hμ₀, hlam₀, hnum₀, hklt₀⟩ :=
    GlobalTheory.T.exists_ample_effective_klt_inductionStart hPr X p n hP hn Δ r N₀ hN₀ β hΔ hklt hr hnef hbig hβ0'
  refine ⟨A, hA, ?_⟩
  have key : ∀ a : WithBot ℕ∞, ∀ j : ℕ, (j : WithBot ℕ∞) < a → a ≤ ((j + 1 : ℕ) : WithBot ℕ∞) →
      a = ((j + 1 : ℕ) : WithBot ℕ∞) := by
    intro a j h1 h2
    induction a using WithBot.recBotCoe with
    | bot => simp at h1
    | coe a =>
      induction a using ENat.recTopCoe with
      | top =>
        exfalso
        have h3 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ (((j + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := h2
        exact absurd (WithBot.coe_le_coe.1 h3) (by simp)
      | coe k =>
        have h1' : j < k := by exact_mod_cast h1
        have h2' : k ≤ j + 1 := by exact_mod_cast h2
        have : k = j + 1 := by omega
        subst this; rfl
  have hsplit : ∀ j, j + 1 ≤ n → ∑ e ∈ Finset.Icc (j + 1) n, (e : ℝ) / c e =
      (j + 1 : ℕ) / c (j + 1) + ∑ e ∈ Finset.Icc (j + 2) n, (e : ℝ) / c e := by
    intro j hj
    rw [← Finset.insert_Icc_add_one_left_eq_Icc hj, Finset.sum_insert (by simp)]
    first | rfl | (push_cast; ring_nf) | simp [add_assoc]
  let S : ℕ → Prop := fun j => ∃ (j' : ℕ) (lam μ : ℚ) (m' : ℕ) (D₀ : CartierDiv X),
        j' ≤ j ∧ 0 < m' ∧ D₀.Eff ∧ 0 < μ ∧ (lam : ℝ) < ∑ e ∈ Finset.Icc (j' + 1) n, (e : ℝ) / c e ∧
        (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' =
          lam * interNumRed ℂ C ![N₀] / r - μ * interNumRed ℂ C ![toLB A]) ∧
        LcCut p n (Δ + qWeil D₀ m') x j'
  have first : S (n - 1) := by
    obtain ⟨lam₁, μ₁, m₁, D₁, hm₁, hD₁, hμ₁, hlam₁, hnum₁, hcut₁⟩ :=
      GlobalTheory.T.angehrnSiu_cut_lower_centre_dimension hPr X p n hP hn Δ m G r N₀ hN₀ A F a x (genericPoint X) n c' lam₀ μ₀ m₀ D₀ hΔ hklt hm hG hr
        hnef hA ha hF hx (genericPoint_specializes x) hn1 hdimX (Or.inl rfl) hc'0 hc'v hm₀ hD₀ hμ₀
        hnum₀ (hklt₀ x).lcAt
    refine ⟨n - 1, lam₁, μ₁, m₁, D₁, le_rfl, hm₁, hD₁, hμ₁, ?_, hnum₁, hcut₁⟩
    rw [Nat.sub_add_cancel hn1, Finset.Icc_self, Finset.sum_singleton]
    have : (lam₀ : ℝ) < β := by exact_mod_cast hlam₀
    linarith
  have step : ∀ j, j + 1 < n → S (j + 1) → S j := by
    intro j hj ⟨j', lam, μ, m', D₁, hj', hm', hD₁, hμ, hlam, hnum, hcut⟩
    by_cases hle : j' ≤ j
    · exact ⟨j', lam, μ, m', D₁, hle, hm', hD₁, hμ, hlam, hnum, hcut⟩
    obtain rfl : j' = j + 1 := by omega
    have hsj := hsplit j (by omega)
    have hcj := hcpos (j + 1) (by omega) (by omega)
    have hpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) / c (j + 1) := div_pos (by positivity) hcj
    obtain ⟨hlc, hnk, hdim⟩ := hcut
    by_cases hall : ∀ z, z ⤳ x → ¬ KltAt p n (Δ + qWeil D₁ m') z →
        topologicalKrullDim (closure ({z} : Set X)) ≤ j
    · refine ⟨j, lam, μ, m', D₁, le_rfl, hm', hD₁, hμ, ?_, hnum, hlc, hnk, hall⟩
      rw [hsj]; linarith
    push_neg at hall
    obtain ⟨z, hzx, hzk, hzd⟩ := hall
    have hq : IsQCart (qWeil D₁ m') := ⟨m', D₁, hm', hD₁, rfl⟩
    obtain ⟨w, hwz, hw⟩ := _root_.GlobalTheory.PairStep.Centre.exists_isNkltCentre X p n hP hn Δ (qWeil D₁ m') z hq (hklt z) hzk
    have hwx : w ⤳ x := hwz.trans hzx
    have hwk : ¬ KltAt p n (Δ + qWeil D₁ m') w :=
      GlobalTheory.PairStep.not_kltAt_of_isNkltCentre X p n hP hn _ w w hw specializes_rfl
    have hsub : closure ({z} : Set X) ⊆ closure ({w} : Set X) := specializes_iff_closure_subset.1 hwz
    have hmono : topologicalKrullDim (closure ({z} : Set X)) ≤ topologicalKrullDim (closure ({w} : Set X)) :=
      (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le
    have hwd : topologicalKrullDim (closure ({w} : Set X)) = ((j + 1 : ℕ) : WithBot ℕ∞) :=
      key _ j (hzd.trans_le hmono) (hdim w hwx hwk)
    have hZw := hZ (Closeds.closure ({w} : Set X)) (j + 1) isIrreducible_singleton.closure
      (by simpa using specializes_iff_mem_closure.1 hwx) (by omega) hwd
    obtain ⟨lam', μ', m'', D₂, hm'', hD₂, hμ', hlam', hnum', hcut'⟩ :=
      GlobalTheory.T.angehrnSiu_cut_lower_centre_dimension hPr X p n hP hn Δ m G r N₀ hN₀ A F a x w (j + 1) (c (j + 1)) lam μ m' D₁ hΔ hklt hm hG hr
        hnef hA ha hF hx hwx (by omega) hwd (Or.inr hw) hcj hZw hm' hD₁ hμ hnum hlc
    refine ⟨j, lam', μ', m'', D₂, le_rfl, hm'', hD₂, hμ', ?_, hnum', by simpa using hcut'⟩
    rw [hsj]
    push_cast at hlam' ⊢
    linarith
  have hall : ∀ i, i < n → S (n - 1 - i) := by
    intro i
    induction i with
    | zero => intro _; simpa using first
    | succ i ih =>
      intro hi
      have h := ih (by omega)
      rw [show n - 1 - i = (n - 1 - (i + 1)) + 1 by omega] at h
      exact step _ (by omega) h
  intro j hj
  have h := hall (n - 1 - j) (by omega)
  rwa [show n - 1 - (n - 1 - j) = j by omega] at h

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIsAlgClosed
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDivPt

theorem exists_pow_eq_of_isAlgClosed : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (n : ℕ), 0 < n →
      ∀ g : Over.mk x ⟶ A, ∃ g' : Over.mk x ⟶ A, g' ^ n = g := by
  intro S A _ hA k _ _ x n hn g
  have hc := hA.comm
  obtain ⟨hfin, -, hsurj⟩ := GlobalTheory.KthRoot.finite_flat_surjective_mulN_any S A hA n hn
  have : IsFinite (pullback.snd (mulN A n).left g.left) := by
    haveI := hfin; infer_instance
  have : Surjective (pullback.snd (mulN A n).left g.left) := by
    haveI := hsurj; infer_instance
  obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.H1.SectionDivision.exists_section (pullback.snd (mulN A n).left g.left)
  have hb' : (t ≫ pullback.fst (mulN A n).left g.left) ≫ (mulN A n).left = g.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht, Category.id_comp]
  have hw : (t ≫ pullback.fst (mulN A n).left g.left) ≫ A.hom = (Over.mk x).hom := by
    rw [← Over.w (mulN A n), ← Category.assoc, hb', Over.w g]
  refine ⟨Over.homMk _ hw, ?_⟩
  have e : ∀ b : Over.mk x ⟶ A, b ^ n = b ≫ mulN A n := fun b => by
    rw [GlobalTheory.MulFlatSurj.mulN_eq_pow, MonObj.comp_pow, Category.comp_id]
  rw [e]
  exact Over.OverMorphism.ext hb'

end GlobalTheory.AbDivPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeToPHeckeTranslateHarrisTaylorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primeToP_hecke_translate_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∃ (o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsHecke g c k N o o' ψ := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.exists_isHecke) | (exact GlobalTheory.UPel.HT.Hecke.exists_isHecke) | (intros; apply GlobalTheory.UPel.HT.Hecke.exists_isHecke <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstDeRhamHomologyProjectiveOverTensorIntegers
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CrysProj

theorem hdR_projective : ∀ (F : Type) [Field F] [NumberField F] (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ a : OAct (𝓞 F) A₀, letI := tensorModule (dp0 k) (𝟙 _) a; Module.Projective (k ⊗[ℤ] 𝓞 F) (HdR A₀) := by
  intro F _ _ k _ A₀ _ _ hA a
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp
  · haveI : Fact (ringChar k).Prime := ⟨hp⟩
    refine GlobalTheory.T.de_rham_cohomology_projective_module F k ?_ A₀ hA a
    intro B₀ _ _ hB b
    set K := AlgebraicClosure k
    haveI : CharP K (ringChar k) := charP_of_injective_algebraMap (algebraMap k K).injective _
    obtain ⟨Λ, _, π, hπ, hker, hp2, hann⟩ := _root_.GlobalTheory.exists_flat_lift_mod_p_sq (ringChar k) K
    have hI : RingHom.ker π ^ 2 = 0 := by
      rw [hker, Ideal.span_singleton_pow, hp2, Ideal.span_singleton_eq_bot.2 rfl]; rfl
    obtain ⟨hfin, hfree, f, hf, hk⟩ := GlobalTheory.T.crystal_finite_free_reduces_to_deRham F Λ K π hπ hI B₀ hB b
    letI := tensorModule (divided₂ hI) (spMap π) b
    haveI := isScalarTower_tensorModule (divided₂ hI) (spMap π) b
    letI := tensorModule (dp0 K) (𝟙 _) b
    exact _root_.GlobalTheory.FlatLift.projective_reduction_of_flat_lift (ringChar k) F Λ K π hπ hker hp2 hann _ hfin hfree _ f hf hk
  · haveI : CharP k 0 := hp ▸ ringChar.charP k
    haveI : CharZero k := CharP.charP_to_charZero k
    letI := tensorModule (dp0 k) (𝟙 _) a
    exact _root_.GlobalTheory.projective_charZero_tensor_ringOfIntegers F k _

end GlobalTheory.CrysProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorHodgeFiltrationNaturalityStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_hodgeFiltration_naturality : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∀ (d : ℕ) (s : Sp (TrivSqZeroExt k (Fin d → k)) ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)) (c : (Fin d → k) →ₗ[k] k) (s' : Sp (DualNumber k) ⟶ Sp R) (o' : GlobalTheory.UPel.HT.Obj b N s') (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (n : GlobalTheory.UPel.HT.ObjMap o' o (spMap (TrivSqZeroExt.map c).toRingHom)) (x : HdR o₀.A) (y : primDR o₀.A →ₗ[k] (Fin d → k)), GlobalTheory.FODef.IsFilLiftV m.cart x y → IsFilLift m'.cart x (c ∘ₗ y) := by
  first | (exact @GlobalTheory.HTUniv.Nat.main) | (exact GlobalTheory.HTUniv.Nat.main) | (intros; apply GlobalTheory.HTUniv.Nat.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRhoPartLieDeRhamQuotientStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_rho_part_lie_deRham_quotient : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → GlobalTheory.HTRho.jSub (GlobalTheory.HTCount.crysAct o₀) (fun i => β.comp (b.t i)) ⊤ ≤ (Fil o₀.A ⊔ LinearMap.range (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1)) ∧ ∀ i, Module.finrank k (HdR o₀.A ⧸ ((Fil o₀.A ⊔ LinearMap.range (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1)) ⊔ GlobalTheory.HTRho.mSub (GlobalTheory.HTCount.crysAct o₀) (β.comp (b.t i)) ⊤)) = D.m := by
  first | (exact @GlobalTheory.HTLieRho.lie_rho_quot) | (exact GlobalTheory.HTLieRho.lie_rho_quot) | (intros; apply GlobalTheory.HTLieRho.lie_rho_quot  <;> assumption)
end

