module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeForMatchedFrames
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.SmallKerInv
open GlobalTheory.FinPl
variable {D : D7}
end GlobalTheory.SmallKerInv
namespace GlobalTheory.SmallKerInv
open GlobalTheory.FinPl
variable {D : D7}
end GlobalTheory.SmallKerInv
namespace GlobalTheory.SmallKerInv
open GlobalTheory.FinPl
theorem small_kernel_invariant : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → BigR fun {D} _ _ _ _ T _ _ _ _ _ R sc => ∀ (G : GridData R.toLevCh sc) (W : G.Weil), W.Over R → ∀ (B : Frames G)
  (ρ : RealMatch W), ρ.Over R → ∀ (t : T) (i j : Fin D.R.m) Θ Θ', IsMatched B t ρ i j Θ Θ' → ∀ g g₁,
  ∃ (L : GlobalTheory.FinPl.Lat (G.V (.grid i j))) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    L.FG ∧ Submodule.span D.host.E (L : Set (Fin (G.V (.grid i j)).rank → D.host.E)) = ⊤ ∧
    ∀ κ, GlobalTheory.FinPl.InK (G.V (.grid i j)) L (fun v => v ∉ S) κ → ∀ u, kerSmall W Θ' g g₁ (u * κ) = kerSmall W Θ' g g₁ u := by
  intro _ _ _ _ _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS => ?_⟩⟩
  intro G W hW B ρ hρ t i j Θ Θ' hΘ g g₁
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, he, ⟨φ₁, φ₂, h1, -⟩, -⟩, -, rfl⟩ := hΘ
  have hm := W.om_is (.mu t i j) ⟨i.2.le, j.2⟩
  have hc := W.om_is (.chi (i : ℕ) j) ⟨i.2, j.2.le⟩
  have s0 := (node_isV G hL (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩).sd
  have s1 := (node_isV G hL (X := .grid (i : ℕ) ((j : ℕ) + 1)) ⟨i.2.le, j.2⟩).sd
  have s2 := (node_isV G hL (X := .grid ((i : ℕ) + 1) (j : ℕ)) ⟨i.2, j.2.le⟩).sd
  set good : Pl D → Prop := fun v => Tame D v ∧
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.chrS (.mu t i j)) v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.chrT (.mu t i j)) v ∧
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.chrS (.chi (i : ℕ) j)) v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.chrT (.chi (i : ℕ) j)) v
    with hgood
  have hev : ∀ᶠ v : Pl D in Filter.cofinite, good v := by
    filter_upwards [GlobalTheory.FinPl.eventually_extUnram_two_notMem D,
      GlobalTheory.FinPl.ShapeSecond.ae_charUnramAt _ hm.hecS.1, GlobalTheory.FinPl.ShapeSecond.ae_charUnramAt _ hm.hecT.1,
      GlobalTheory.FinPl.ShapeSecond.ae_charUnramAt _ hc.hecS.1, GlobalTheory.FinPl.ShapeSecond.ae_charUnramAt _ hc.hecT.1]
      with v h0 h1 h2 h3 h4
    exact ⟨⟨h0.1, Or.inl h0.2⟩, h1, h2, h3, h4⟩
  have hfin : {v | ¬ good v}.Finite := Filter.eventually_cofinite.1 hev
  classical
  have hfull : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
      IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
    intro V Λ hΛ
    haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
    refine ⟨?_⟩
    obtain ⟨s, hs⟩ := hΛ.1.fg
    apply eq_top_iff.mpr
    intro y _
    let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
      ∑ i, ∑ j, star (x i) * V.gram i j * y j
    obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
    have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
      exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
    let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
      carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
      zero_mem' := by refine ⟨0, ?_⟩; simp [f]
      add_mem' := by
        rintro x z ⟨b, hb⟩ ⟨c, hc⟩
        refine ⟨b + c, ?_⟩
        change (b : D.host.E) + c = _
        rw [hb, hc]
        simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
      smul_mem' := by
        rintro c x ⟨b, hb⟩
        refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
        simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change star (c : D.host.E) * _ = _
        ring }
    have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
      intro x hx
      obtain ⟨b, hb⟩ := ha x hx
      exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
    have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
      apply (hΛ.2 _).2
      intro x hx
      have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
      obtain ⟨b, hb⟩ := hxP
      refine ⟨b, ?_⟩
      rw [hb]
      dsimp only [f, Pi.smul_apply]
      simp only [smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.subset_span hy
    have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
      (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
    change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
      ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
    exact this
  refine ⟨G.Λ (.grid i j), hfin.toFinset ∪ (locPl G t).image (fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)),
    s0.1.fg, (by letI := hfull _ _ s0; exact Submodule.IsFullLattice.span_eq_top), ?_⟩
  intro κ hκ u
  have hgd : ∀ v, v ∉ hfin.toFinset ∪ (locPl G t).image (fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → good v := by
    intro v hv
    by_contra h
    exact hv (Finset.mem_union_left _ (hfin.mem_toFinset.2 h))
  have hoff : ∀ PP ∈ locPl G t,
      ¬ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∉ hfin.toFinset ∪ (locPl G t).image (fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) :=
    fun PP hPP h => h (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hPP))
  unfold kerSmall
  refine Finsupp.sum_congr fun d hd => ?_
  obtain ⟨P, -, hP⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hd)
  obtain ⟨d', hd', hd''⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hP)
  have hdd := Finsupp.support_single_subset hd''
  rw [Finset.mem_singleton] at hdd
  subst hdd
  obtain ⟨⟨hsb1, hth1⟩, ⟨hsb2, hth2⟩⟩ := h1 d' hd'
  have hv1 := ρ.vT_is t i j i.2.le j.2
  have hv2 := ρ.vX_is i j i.2 j.2.le
  congr 1
  congr 1
  · show thetaKO (W.om (.mu t i j)) (u * κ) g _ = thetaKO (W.om (.mu t i j)) u g _
    unfold thetaKO
    have e1 : ((u * κ, g) : GA D (G.pS (.mu t i j)) × GA D (G.pT (.mu t i j))) = (u, g) * (κ, 1) := by simp
    rw [e1, map_mul, Module.End.mul_apply]
    refine congrArg (fun x => W.om (.mu t i j) (u, g) x 0) ?_
    exact om_fock_fix _ _ _ _ _ _ _ hm W.θ_is _ _ _
      (fun v hv => ⟨s0, s1, (hgd v hv).1, (hgd v hv).2.1, (hgd v hv).2.2.1⟩) e _ he hoff _ _ _
      hv1.2.theta hv1.2.lat hth1 _ _ _ _ _ κ 1 hκ (inK_one _ _ _)
  · show thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) (u * κ) _ = thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) u _
    unfold thetaKO
    have e2 : ((negGA _ g₁, u * κ) : GA D (G.pS (.chi (i : ℕ) j)) × GA D (G.pT (.chi (i : ℕ) j))) =
        (negGA _ g₁, u) * (1, κ) := by simp
    rw [e2, map_mul, Module.End.mul_apply]
    refine congrArg (fun x => W.om (.chi (i : ℕ) j) (negGA _ g₁, u) x 0) ?_
    exact om_fock_fix _ _ _ _ _ _ _ hc W.θ_is _ _ _
      (fun v hv => ⟨isSelfDualC_neg s2, s0, (hgd v hv).1, (hgd v hv).2.2.2.1, (hgd v hv).2.2.2.2⟩) e _ he hoff _ _ _
      hv2.2.theta hv2.2.lat hth2 _ _ _ _ _ 1 κ (inK_one _ _ _) hκ
end GlobalTheory.SmallKerInv
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_small_kernel_invariant : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → BigR fun {D} _ _ _ _ T _ _ _ _ _ R sc => ∀ (G : GridData R.toLevCh sc) (W : G.Weil), W.Over R → ∀ (B : Frames G)
  (ρ : RealMatch W), ρ.Over R → ∀ (t : T) (i j : Fin D.R.m) Θ Θ', IsMatched B t ρ i j Θ Θ' → ∀ g g₁,
  ∃ (L : GlobalTheory.FinPl.Lat (G.V (.grid i j))) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    L.FG ∧ Submodule.span D.host.E (L : Set (Fin (G.V (.grid i j)).rank → D.host.E)) = ⊤ ∧
    ∀ κ, GlobalTheory.FinPl.InK (G.V (.grid i j)) L (fun v => v ∉ S) κ → ∀ u, kerSmall W Θ' g g₁ (u * κ) = kerSmall W Θ' g g₁ u := by
  first | exact @_root_.GlobalTheory.SmallKerInv.small_kernel_invariant | exact _root_.GlobalTheory.SmallKerInv.small_kernel_invariant | (intros; apply _root_.GlobalTheory.SmallKerInv.small_kernel_invariant <;> assumption)
end
