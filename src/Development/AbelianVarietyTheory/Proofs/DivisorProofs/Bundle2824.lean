module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfSpan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1982
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0935
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TwoRunDatumBoundUnitAtIndefinitePoint
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsEmptyOfNotAll
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitModulusRationalPhaseMemCoefficientField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelVectorMovedByRootsOfUnity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1680
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2810
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1695
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2520
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2807
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2781
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2510
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2772
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2800
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2726
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2805
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivativeSubmoduleStable
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
open GlobalTheory.BigOn.Exp.SerBase
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.SerBase

theorem eq_zero_of_cuspA_bot {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (fw : FWTie T R κ v₀) (j : Fin D.R.m)
    (hc : T.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n = ⊥) (x : Fin (R.nW j) → D.what₂.LL) : x = 0 := by
  obtain ⟨n, b, hb, -, -, -, hsp⟩ := fw.ks j
  have hWK : ∀ z ∈ (R.FW j).WK, z = 0 := fun z hz => by
    obtain ⟨f, hf⟩ := (fw.e j).surjective ⟨z, hz⟩
    have hf0 : f = 0 := by
      have h1 : (f : T.R ((j : ℕ) + 1)) ∈ (⊥ : Submodule T.Q.c.F (T.R ((j : ℕ) + 1))) := hc ▸ f.2
      exact Subtype.ext ((Submodule.mem_bot _).1 h1)
    have := congrArg Subtype.val hf
    rw [hf0, map_zero] at this
    exact this.symm
  have h0 : Set.range b ⊆ {0} := by
    rintro _ ⟨k, rfl⟩; exact hWK _ (hb k)
  have : x ∈ Submodule.span D.what₂.LL (Set.range b) := by rw [hsp]; trivial
  have h2 := Submodule.span_mono h0 this
  simpa using h2

theorem adForm_smul {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (c : D.what₂.LL) (x : Fin (R.nW i) → D.what₂.LL) : adForm R i (c • x) = sg0 D A c • adForm R i x := by
  unfold adForm
  rw [LinearMap.map_smulₛₗ, map_smul]

theorem adForm_zero {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) :
    adForm R i 0 = 0 := by
  unfold adForm
  rw [map_zero, map_zero]

theorem kerRat_framed (hP : GlobalTheory.Published.CuspRapidDecay) (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hR : GlobalTheory.Published.RayClassFieldSt)
    (hS : GlobalTheory.SerStd.SeriesRatS) {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F}
    {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {F : Face D A3.A}
    {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
    {O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)} {t : D.ntw.Tw} {j : Fin D.R.m}
    {hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j} (hH : RatHyp T Rl F κ v₀ O t j hV) (hph : ∀ k, Rl.phs k = 1)
    (v : HeightOneSpectrum (𝓞 D.what₂.LL)) {χ ξR ω φ}
    (hK : KerDat Rl.toRealDat j (Rl.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver Rl.toRealDat (Rl.mu v) (ownAt D v)) ω φ)
    {h : GA D (Vc D j)} (hh : h ∈ GfC (Vc D j)) {y : (Rl.cV j).W} (hy : InCoefLat Rl.toRealDat j h y)
    (u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ) (hu : ∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j (sg0 D A3.A) τ) :
    ∃ x, adForm Rl.toRealDat j x (fun τ => u τ) = singleSeries Rl.toRealDat j ω φ h y u := by
  obtain ⟨gramR, c0R, c0L, hFT, P, hPm, rfl⟩ := hy
  obtain ⟨ph, hph1, hphC⟩ := hS D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ hH.laws hH.core.lev hH.core.grp hH.core.fam
    hH.core.models hH.core.thP hH.tieIn j hV hH.frame hH.std gramR c0R c0L hFT u hu
  have hRP : IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph := fun C hC _ => hphC C hC
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_adelicForm_eq_rationalPhase_kernelSeries hP hA hR D Γ Pl0 I0 T0 A3 T Rl cG S YS F κ v₀ O t j hV hH gramR c0R c0L hFT u hu ph hRP v χ ξR ω φ hK
    h hh P hPm
  have hph0 : ph ≠ 0 := fun e => by rw [e, norm_zero] at hph1; exact zero_ne_one hph1
  by_cases hc : T.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n = ⊥
  · refine ⟨0, ?_⟩
    rw [eq_zero_of_cuspA_bot hH.fw.some j hc x, adForm_zero] at hx
    rw [adForm_zero]
    funext g
    have e := congrFun hx.symm g
    have e2 : ph * singleSeries Rl.toRealDat j ω φ h (c0L j P) u g = 0 := e
    exact ((mul_eq_zero.1 e2).resolve_left hph0).symm
  · obtain ⟨c, hcph⟩ := _root_.GlobalTheory.PhaseOneOnto.phase_mem_coefField hP hA hR D Γ Pl0 I0 T0 A3 T Rl cG S YS F κ v₀ O t j hV hH gramR c0R c0L hFT u hu hph hc ph
      hph1 hRP
    refine ⟨c⁻¹ • x, ?_⟩
    rw [adForm_smul]
    funext g
    have e := congrFun hx g
    have e2 : adForm Rl.toRealDat j x (fun τ => u τ) g = ph * singleSeries Rl.toRealDat j ω φ h (c0L j P) u g := e
    show sg0 D A3.A c⁻¹ * adForm Rl.toRealDat j x (fun τ => u τ) g = _
    rw [e2, map_inv₀, hcph, ← mul_assoc, inv_mul_cancel₀ hph0, one_mul]


end GlobalTheory.BigOn.Exp.SerBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelThetaSeriesSpanOverClassRepresentatives
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

namespace GlobalTheory.OneKernelSpan

theorem inCoefLat_move : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (Q : Finset (Pl D.host.E)) (h h' : GA D (Vc D i)) (γ : GQ (Vc D i)) (k : Bridge.Gf (Vc D i)), k ∈ dataLevel R i Q → fin (Vc D i) h = Bridge.ratF (Vc D i) γ * fin (Vc D i) h' * k → ∀ w, InCoefLat R i h w → InCoefLat R i h' ((R.cV i).ρ ((γ : GA D (Vc D i))⁻¹) w) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i Q h h' γ k hk e w hw
  obtain ⟨gramR, c0R, c0L, hT, P, hP, rfl⟩ := hw
  refine ⟨gramR, c0R, c0L, hT, ?_⟩
  have hst : Formalism.UG.bc (swapAE D) (k : GL (Fin (Vc D i).rank) _) ∈ St (R.βV i) := Formalism.L2.DIV.parLev_St hk.1
  obtain ⟨γE, hγ, hl⟩ := GlobalTheory.HLatMove.hLat_rat_mul_stab (Vc D i) (R.βV i) (R.ΛV i) (hR.lev.βV i) γ
  rw [e, hl (fin (Vc D i) h') k hst, Formalism.L2.Col.nabAtr_gmap, MulEquiv.apply_symm_apply] at hP
  obtain ⟨P', hP', rfl⟩ := hP
  refine ⟨P', hP', ?_⟩
  have h1 := (hT.mapL i).1 γ γE hγ P'
  change (R.cV i).ρ ((γ : GA D (Vc D i))⁻¹) (c0L i ((rhoVr (labLL D) (lamV D i) γE) P')) = c0L i P'
  rw [h1]
  change ((R.cV i).ρ ((γ : GA D (Vc D i))⁻¹) * (R.cV i).ρ (γ : GA D (Vc D i))) (c0L i P') = c0L i P'
  rw [← map_mul, inv_mul_cancel, map_one]
  rfl

theorem pt_theta_of_kerDat {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (hR : GlobalTheory.Hk3.Core R F)
    {i : Fin D.R.m} {ξ : Formalism.L2.Host.HChar D.host.E} {χ : (AE D)ˣ →* Circle} {ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {Q : Finset (Pl D.host.E)} {ω : WeilRep D i} {φ : WO (Vc D i) (Wc D i) → ℂ} (hK : KerDat R i ξ χ ξR Q ω φ)
    (P : PolF D (Wc D i).rank (Vc D i).rank) :
    IsThetaFunO R.ψ (Vc D i) (Wc D i)
      (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) φ P) := by
  have hθ : IsInfFam R.θ := hR.models.inf
  have hφ : IsThetaFunO R.ψ (Vc D i) (Wc D i) φ := by
    obtain ⟨⟨hψ, h0⟩, e, -, h⟩ := hK.vec
    exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ h h0.theta
  exact (GlobalTheory.OrientedHeis.om_pureTensorO D _ _ _ _ _ _ _ hK.weil hθ (fun _ => 1) (fun _ => 1) (R.BV i) _
      (cart (R.MW i (sg0 D A))) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) _ 1 1
      (fun τ => by rw [Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.JointHarm.compAt_mt_one', Matrix.mul_one, Matrix.one_mul]) (fun _ => rfl) (fun _ => rfl) _ hφ P).1

theorem series_rat : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ γ ∈ GQ (Vc D i), ∀ h w, singleSeries R i ω φ (γ * h) w = singleSeries R i ω φ h w := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξ χ ξR Q ω φ hK γ hγ h w
  funext v g
  have := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ hK.weil _ (pt_theta_of_kerDat hR hK (R.ioP i (PiTensorProduct.tprod ℂ v) w))).1 γ hγ 1 (one_mem _) h g
  rw [one_mul] at this
  exact this

theorem series_level : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → (∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → ∀ κ ∈ GfC (Vc D i), fin (Vc D i) κ ∈ dataLevel R i Q → ∃ z : D.what₂.LL, (∃ n : ℕ, 0 < n ∧ z ^ n = 1) ∧ ∀ h w, singleSeries R i ω φ (h * κ) w = D.what₂.embLL z • singleSeries R i ω φ h w := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξ χ ξR Q ω φ hK hval κ hκ hk
  obtain ⟨h1, -⟩ := _root_.GlobalTheory.KerMove.kerDat_move D G Pl0 T0 A Ks R F hR i ξ χ ξR Q ω φ hK hval
  obtain ⟨z, n, hn, hz, hzω⟩ := h1 κ hκ hk
  refine ⟨z, ⟨n, hn, hz⟩, fun h w => ?_⟩
  funext v g
  have hom := GlobalTheory.FiniteFock.om_pureTensorO_of_finite _ _ _ _ _ _ _ hR.models.inf hK.weil _ _ _ _ _
    (pt_theta_of_kerDat hR hK) κ hκ 1 (one_mem _) _ hzω (R.ioP i (PiTensorProduct.tprod ℂ v) w)
  have := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ hK.weil _ (pt_theta_of_kerDat hR hK (R.ioP i (PiTensorProduct.tprod ℂ v) w))).2 κ 1 _ hom h g
  rw [mul_one] at this
  exact this

theorem series_real : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ (h u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∀ w, singleSeries R i ω φ (h * u) w = singleSeries R i ω φ h ((R.cV i).ρ u w) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξ χ ξR Q ω φ hK h u hu w
  funext v g
  unfold singleSeries Datum.thetaKO
  rw [show ((h * u, g) : GA D (Vc D i) × GA D (Wc D i)) = (h, g) * (u, 1) from Prod.ext rfl (mul_one g).symm,
    map_mul, Module.End.mul_apply, _root_.GlobalTheory.RealTwistKer.weil_kernel_real D G Pl0 T0 A Ks R F hR i ξ χ ξR Q ω φ hK u hu _ (pt_theta_of_kerDat hR hK _),
    _root_.GlobalTheory.FockAnyDatum.om_ioP_of_datum D G Pl0 T0 A Ks R F hR i ξR Q φ hK.vec u hu]


set_option maxHeartbeats 2000000 in
theorem kernelSpanOverClasses_of : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → ∀ (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ), KernelSpanOverClasses R i U ψ ph v (ownAt D v) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i v hv hmu hval U ψ ph ω φ hk Cl h hh
  obtain ⟨χ, ξR, hK⟩ := _root_.GlobalTheory.OnBaseKer.kerDat_of_isBaseKernel D G Pl0 T0 A Ks R F hR i v hv hmu ω φ hk
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.iUnion_subset fun c x hx => ?_))
  · rintro x ⟨g, hg, w, hw, hx⟩
    obtain ⟨c, ⟨γA, hγA⟩, k, e⟩ := hh.2 (fin (Vc D i) g)
    obtain ⟨κ, hκ, hκe⟩ := GlobalTheory.TraceIncl.KernLaws.exists_finite_lift (Vc D i) (k : Bridge.Gf (Vc D i))
    obtain ⟨u, hu_def⟩ : ∃ u : GA D (Vc D i), u = κ⁻¹ * ((h c)⁻¹ * (γA⁻¹ * g)) := ⟨_, rfl⟩
    have e1 : fin (Vc D i) g = fin (Vc D i) (γA * h c * κ) := by
      refine e.trans ?_
      rw [← GlobalTheory.TraceIncl.KernLaws.fin_mul, ← GlobalTheory.TraceIncl.KernLaws.fin_mul, hκe]
      rfl
    have e2 : finHom (Vc D i) g = finHom (Vc D i) (γA * h c * κ) := congrArg Subtype.val e1
    have hu : u ∈ GinfC (Vc D i) := by
      refine MonoidHom.mem_ker.2 ?_
      rw [hu_def, map_mul, map_mul, map_mul, map_inv (finHom (Vc D i)) κ, map_inv (finHom (Vc D i)) (h c),
        map_inv (finHom (Vc D i)) γA, e2, map_mul, map_mul]
      simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel]
    have hg' : g = γA * (h c * κ) * u := by
      rw [hu_def]
      simp only [mul_assoc, mul_inv_cancel_left]
    obtain ⟨z, ⟨n, hn, hz⟩, hzl⟩ := series_level D G Pl0 T0 A Ks R F hR i _ χ ξR _ ω φ hK hval κ hκ (by rw [hκe]; exact k.2)
    have hρ : (R.cV i).ρ u w = (R.cV i).ρ (γA⁻¹) w := by
      have hc1 := (hR.models.cV i).1
      rw [hu_def, map_mul, Module.End.mul_apply, hc1 _ (inv_mem hκ), Module.End.one_apply, map_mul, Module.End.mul_apply,
        hc1 _ (inv_mem (hh.1 c)), Module.End.one_apply, map_mul, Module.End.mul_apply, hc1 _ hg, Module.End.one_apply]
    have key : ∀ v', singleSeries R i ω φ g w v' =
        D.what₂.embLL z • singleSeries R i ω φ (h c) ((R.cV i).ρ (γA⁻¹) w) v' := by
      intro v'
      have h1 := series_real D G Pl0 T0 A Ks R F hR i _ χ ξR _ ω φ hK (γA * (h c * κ)) u hu w
      rw [← hg'] at h1
      have h2 := series_rat D G Pl0 T0 A Ks R F hR i _ χ ξR _ ω φ hK γA hγA (h c * κ) ((R.cV i).ρ u w)
      have h3 := hzl (h c) ((R.cV i).ρ u w)
      rw [h1, h2, h3, hρ]
      rfl
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn.ne'] at hz
      exact zero_ne_one hz
    have hzI : IsIntegral ℤ z := IsIntegral.of_pow hn (by rw [hz]; exact isIntegral_one)
    have hx'' : z⁻¹ • x ∈ seriesAt R i U ψ ph ω φ (h c) := by
      refine ⟨_, inCoefLat_move D G Pl0 T0 A Ks R F hR i _ g (h c) ⟨γA, hγA⟩ k k.2 e w hw, fun v' => ?_⟩
      rw [adForm_smul]
      change D.what₂.embLL z⁻¹ • adForm R i x (fun ρ => v' ρ) = _
      rw [hx v', key v', map_smul, smul_comm ph, smul_smul, ← map_mul, inv_mul_cancel₀ hz0, map_one, one_smul]
    have : x = (⟨z, hzI⟩ : 𝓞 D.what₂.LL) • (z⁻¹ • x) := by
      have e3 : (⟨z, hzI⟩ : 𝓞 D.what₂.LL) • (z⁻¹ • x) = z • (z⁻¹ • x) := rfl
      rw [e3, smul_smul, mul_inv_cancel₀ hz0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_iUnion.2 ⟨c, hx''⟩))
  · obtain ⟨w, hw, hx⟩ := hx
    exact ⟨h c, hh.1 c, w, hw, hx⟩

end GlobalTheory.OneKernelSpan

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverOpenImmersionNormalisedThetaClosure
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegOpen

theorem isIso_stalkMap_of_isHom {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M M' : RatModel o Ω}
    {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' (AlgHom.id o Ω) f) :
    IsDominant f ∧ IsIso (f.stalkMap (genericPoint M'.Z)) := by
  have hid : spMap (AlgHom.id o Ω).toRingHom ≫ M.pt = M.pt :=
    (congrArg (· ≫ M.pt) (Spec.map_id _)).trans (Category.id_comp _)
  have : IsDominant (M'.pt ≫ f) := by
    rw [hf, hid]; infer_instance
  have hd : IsDominant f := IsDominant.of_comp M'.pt f
  refine ⟨hd, ?_⟩
  have hz : f (genericPoint M'.Z) = genericPoint M.Z := GlobalTheory.apply_genericPoint_of_isDominant f
  have key : ∀ a, M'.stalkHom (genericPoint M'.Z) (f.stalkMap (genericPoint M'.Z) a) =
      M.stalkHom (f (genericPoint M'.Z)) a := by
    intro a
    obtain ⟨U, hzU, s, rfl⟩ := M.Z.presheaf.germ_exist a
    rw [Scheme.Hom.germ_stalkMap_apply]
    exact (M'.stalkHom_germ (U := f ⁻¹ᵁ U) hzU _).trans ((hf.valF_app ⟨_, hzU⟩ s).trans (M.stalkHom_germ hzU s).symm)
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun a b h => M.stalkHom_injective _ ?_, fun b => ?_⟩
  · rw [← key, ← key, h]
  · have hx : M'.stalkHom (genericPoint M'.Z) b ∈ M.O (f (genericPoint M'.Z)) := by
      rw [hz, M.O_genericPoint]; exact Algebra.mem_top
    obtain ⟨a, ha⟩ := (M.stalkEquiv _).surjective ⟨_, hx⟩
    refine ⟨a, M'.stalkHom_injective _ ?_⟩
    rw [key]
    exact congrArg Subtype.val ha

end GlobalTheory.SiegOpen

namespace GlobalTheory.SiegOpen

theorem level_openImmersion : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → QFin f → ∀ (Y X : RatModel o Ω) (q : Y.Z ⟶ F.X), LevAt F β u Y q → X.IsNm S.th → Geo.Tor.IsNormalScheme X.Z → ∃ d : Y.Z ⟶ X.Z, X.IsHom Y (AlgHom.id o Ω) d ∧ IsOpenImmersion d := by
  intro g n hg hn hodd F W hW P rig m N f hTh o Ω _ _ _ _ β S ρ u hSys hQ Y X q hLev hNm hXn

  have hYdiv : Y.HasDiv S.th := _root_.GlobalTheory.SiegTh.ThInt.thetaInt g n hg hn hodd F W hW P rig m N f hTh o Ω β S ρ u hSys Y (q ≫ f)
    hLev.1 (by rw [← Category.assoc, hLev.2.2.2.2, Category.assoc])

  obtain ⟨d, hd⟩ := hNm.exists_isHom (M' := Y) (φ := AlgHom.id o Ω) hYdiv (RatModel.isIntegrallyClosed_O hLev.1)
  refine ⟨d, hd, ?_⟩
  have hid : spMap (AlgHom.id o Ω).toRingHom ≫ X.pt = X.pt :=
    (congrArg (· ≫ X.pt) (Spec.map_id _)).trans (Category.id_comp _)
  have hYd : Y.pt ≫ d = X.pt := hd.trans hid

  obtain ⟨e, hSymE, hPe⟩ := _root_.GlobalTheory.SiegTh.exists_symE_pCrd g n hg hn hodd F W hW P rig m N f hTh o Ω β S ρ u hSys
  have hSame := _root_.GlobalTheory.SiegTh.sameScale_theta_symE g n hg hn hodd F W hW P rig m N f hTh o Ω β S ρ u hSys X e hXn hNm.1 hSymE
  have hXe : X.HasDiv e := fun z => by
    obtain ⟨i, hi⟩ := hNm.1 z
    obtain ⟨j, hj, -⟩ := hSame z i hi
    exact ⟨j, hj⟩
  obtain ⟨hX, hXs, hXP⟩ := _root_.GlobalTheory.SiegTh.CrdMapBC.exists_map_of_hasDiv o Ω (cycAway n) β X N e hXe
  have hfs : f ≫ PSpace.str (cycAway n) N = F.s := hTh.2.2.2.2.2.2.2.1

  have heq : d ≫ hX = q ≫ f := by
    refine _root_.GlobalTheory.SiegCrd.eq_of_generic_pCrd (cycAway n) N Y.Z (Y.s ≫ spMap β) (d ≫ hX) (q ≫ f) Ω Y.pt e ?_ ?_ Y.gen ?_ ?_
    · rw [Category.assoc, hXs, ← Category.assoc, hd.inducedModelMorphism_comp_structureMap]
    · rw [Category.assoc, hfs, hLev.2.2.2.1]
    · rw [← Category.assoc, hYd]; exact hXP
    · rw [← Category.assoc, hLev.2.2.2.2]; exact hPe _ rfl

  have : LocallyOfFiniteType F.s := by
    haveI := F.smooth
    haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
    infer_instance
  have : LocallyOfFiniteType (f ≫ PSpace.str (cycAway n) N) := by rw [hfs]; assumption
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (PSpace.str (cycAway n) N)
  haveI : LocallyQuasiFinite f :=
    LocallyQuasiFinite.of_finite_preimage_singleton f (GlobalTheory.SiegMin.finite_preimage_singleton_of_qFin f hQ)
  haveI : IsFinite q := hLev.2.1
  haveI : LocallyQuasiFinite (d ≫ hX) := by rw [heq]; infer_instance
  haveI : LocallyQuasiFinite d := LocallyQuasiFinite.of_comp d hX

  haveI := Y.sep
  haveI := Y.qc
  haveI := Y.lft
  haveI := X.sep
  haveI : IsSeparated (d ≫ X.s) := by rw [hd.inducedModelMorphism_comp_structureMap]; infer_instance
  haveI : QuasiCompact (d ≫ X.s) := by rw [hd.inducedModelMorphism_comp_structureMap]; infer_instance
  haveI : LocallyOfFiniteType (d ≫ X.s) := by rw [hd.inducedModelMorphism_comp_structureMap]; infer_instance
  haveI : IsSeparated d := IsSeparated.of_comp d X.s
  haveI : QuasiCompact d := QuasiCompact.of_comp d X.s
  haveI : LocallyOfFiniteType d := locallyOfFiniteType_of_comp d X.s
  obtain ⟨h1, h2⟩ := isIso_stalkMap_of_isHom hd

  exact GlobalTheory.isOpenImmersion_of_quasiFinite_of_isIso_stalkMap d fun z => (hXn z).2

end GlobalTheory.SiegOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightInductionSymmetricFirstTwo
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt.VSwap

theorem finite_coheight_one_mem_supp {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z] [CompactSpace Z]
    (D : CartierDiv Z) : {z : Z | Order.coheight z = 1 ∧ z ∈ D.supp}.Finite := by
  classical
  have : IsNoetherian Z := {}
  obtain ⟨S, hS, hc, hi, hU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible D.supp.isClosed
  refine (hS.image fun T => if h : IsIrreducible T then h.genericPoint else genericPoint Z).subset
    fun z hz => ?_
  obtain ⟨T, hT, hzT⟩ := Set.mem_sUnion.1 (hU.le hz.2)
  refine ⟨T, hT, ?_⟩
  simp only [dif_pos (hi T hT)]
  have hg := (hi T hT).isGenericPoint_genericPoint (hc T hT)
  have h₁ : z ≤ (hi T hT).genericPoint := hg.specializes hzT
  have h₂ : (hi T hT).genericPoint < genericPoint Z := by
    refine lt_of_le_not_ge (genericPoint_specializes _) fun e => ?_
    have e' : _ = genericPoint Z := (Specializes.antisymm e (genericPoint_specializes _)).eq
    exact D.genericPoint_notMem_supp (e' ▸ hU.ge (Set.mem_sUnion.2 ⟨T, hT, hg.mem⟩))
  by_contra hne
  have h₃ := Order.coheight_add_one_le (lt_of_le_not_ge h₁ fun e => hne (Specializes.antisymm h₁ e).eq)
  have h₄ := Order.coheight_add_one_le h₂
  rw [hz.1] at h₃
  have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
  exact absurd h₅ (by decide)

section

variable (hI : ArchInteg) (hR : ArchRecip) {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y]
  [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} (hq : IsAmb q) {e : ℕ} (hd : topologicalKrullDim Y = (e + 1 + 1 : ℕ))
  {T : ∀ d : ℕ, (Fin d → HermLB q) → Y → ℝ} (hT : IsMix q (e + 1) T) (L : Fin e → HermLB q)


include hI hR hq hd hT in
theorem add_first (N M A : HermLB q) {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r)
    {u : A.B.ι → Y.functionFieldˣ} (hu : IsRatSec A.B u) {t : (M.tens A).B.ι → Y.functionFieldˣ}
    (ht : IsRatSec (M.tens A).B t) :
    recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) (M.tens A) ht =
      recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M hr +
        recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) A hu := by
  have hp : IsRatSec (M.tens A).B (fun c : M.B.ι × A.B.ι => r c.1 * u c.2) := PtHtComb.isRatSec_tens hr hu
  rw [_root_.GlobalTheory.MixHt.recVal_indep_sec hI hR k Y q hq e hd T hT (M.tens A) (Fin.cons N L) t ht _ hp]
  exact _root_.GlobalTheory.MixHt.recVal_tens hI k Y q hq (e + 1) hd (T (e + 1) (Fin.cons N L)) (Fin.cons N L) M A r hr u hu _ hp
    fun _ _ _ _ => rfl


include hI hR hq hd hT in
theorem swap_of_sec (M N : HermLB q) (t : N.B.Sec) (ht : genericPoint Y ∈ nonzeroLocus t)
    {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) {r' : N.B.ι → Y.functionFieldˣ} (hr' : IsRatSec N.B r') :
    recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M hr =
      recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N hr' := by
  have : IsNoetherian Y := hq.isNoetherian
  set S : Set Y := {genericPoint Y} ∪ {z | Order.coheight z = 1 ∧ z ∈ (divOfSec N.isLB t ht).supp} with hS
  have hfin : S.Finite := (Set.finite_singleton _).union (finite_coheight_one_mem_supp _)
  obtain ⟨B, s, v, hsS, hvS⟩ := _root_.GlobalTheory.MixHt.exists_tens_sec_finite_subset_nonzeroLocus k Y q hq M S hfin
  have hs : genericPoint Y ∈ nonzeroLocus s := hsS (Set.mem_union_left _ rfl)
  have hv : genericPoint Y ∈ nonzeroLocus v := hvS (Set.mem_union_left _ rfl)
  have hcov : ∀ z : Y, Order.coheight z = 1 → z ∉ nonzeroLocus t → z ∈ S := fun z hz hzt =>
    Set.mem_union_right _ ⟨hz, by_contra fun h => hzt ((notMem_supp_divOfSec (hL := N.isLB) (s := t) (hs := ht)).1 h)⟩
  have R1 := _root_.GlobalTheory.MixHt.recVal_cons_recip hR k Y q hq e hd T hT (M.tens B) N L s t hs ht fun z hz =>
    (em (z ∈ nonzeroLocus t)).elim Or.inr fun h => Or.inl (hsS (hcov z hz h))
  have R2 := _root_.GlobalTheory.MixHt.recVal_cons_recip hR k Y q hq e hd T hT B N L v t hv ht fun z hz =>
    (em (z ∈ nonzeroLocus t)).elim Or.inr fun h => Or.inl (hvS (hcov z hz h))
  have A1 := add_first hI hR hq hd hT L N M B hr (isRatSec_ratOfSec v hv) (isRatSec_ratOfSec s hs)
  have A2 := _root_.GlobalTheory.MixHt.recVal_tens_cons hI k Y q hq e hd T hT N (ratOfSec t ht) (isRatSec_ratOfSec t ht) M B L
  rw [_root_.GlobalTheory.MixHt.recVal_indep_sec hI hR k Y q hq e hd T hT N (Fin.cons M L) r' hr' _ (isRatSec_ratOfSec t ht)]
  linarith

end

theorem main : ArchInteg → ArchRecip → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y]
    (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T, IsMix q (e + 1) T →
    ∀ (M N : HermLB q) (L : Fin e → HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r)
    (r' : N.B.ι → Y.functionFieldˣ) (hr' : IsRatSec N.B r'),
    recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M hr =
      recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N hr' := by
  intro hI hR k _ Y _ _ q hq e hd T hT M N L r hr r' hr'
  obtain ⟨A, s, u, hsS, huS⟩ := _root_.GlobalTheory.MixHt.exists_tens_sec_finite_subset_nonzeroLocus k Y q hq N {genericPoint Y} (Set.finite_singleton _)
  have hs : genericPoint Y ∈ nonzeroLocus s := hsS rfl
  have hu : genericPoint Y ∈ nonzeroLocus u := huS rfl
  have hp := PtHtComb.isRatSec_tens hr' (isRatSec_ratOfSec u hu)
  have K1 := swap_of_sec hI hR hq hd hT L M (N.tens A) s hs hr hp
  have K2 := swap_of_sec hI hR hq hd hT L M A u hu hr (isRatSec_ratOfSec u hu)
  have A3 := _root_.GlobalTheory.MixHt.recVal_tens_cons hI k Y q hq e hd T hT M r hr N A L
  have A4 := add_first hI hR hq hd hT L M N A hr' (isRatSec_ratOfSec u hu) hp
  linarith

end GlobalTheory.MixHt.VSwap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPresentationOfSeriesPairsStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidifiedExtension_presentation_of_series_pairs : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), c.IsLawOf μ → (∀ s w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n s) → (∀ n, u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i)) → ρ (s, w) = G.rigMk (z, u)) → IsRigOf μ ρ := by
  first | exact @GlobalTheory.Katz.isRigOf_rigMk | exact GlobalTheory.Katz.isRigOf_rigMk | (intros; apply GlobalTheory.Katz.isRigOf_rigMk <;> assumption)
end

