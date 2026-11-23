module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0798
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0813
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0946
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0846
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0820
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0776
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0790
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0829
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorThetaLiftOfBaseLevelLaw
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1820
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2845
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0883
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0782
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0801
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0827

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCentralFlipTranslateHalfPlacesThetaPair
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

noncomputable section

namespace GlobalTheory.LevelSeries

theorem exists_central_flip_step : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ), ∃ z : GA D V, z ∈ GfC V ∧ (∀ l : ℕ, (∀ PP ∈ T, ((l : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → OneAt V l z) ∧ ∀ eT : AE D, IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ x : (AE D)ˣ, IsFlipDet V eT m x ∧ ∀ (M u : ℕ) (e e' : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (O : Subring ℂ), M = m * u → (∀ PP ∈ T, ((u : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → IsIdemSum e P → T ⊆ P → IsIdemSum e' ((P \ T) ∪ T.image Formalism.L2.DIV.conjPl) → zeta M ∈ O → ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O, ∃ F ∈ trSp ψ V W ΛV ΛW f₀ e' M O, om (z, 1) (flipScal χW V W T m x • F) = f := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hV T m
  by_cases h : ∃ eT : AE D, IsIdemSum eT T ∧ m ≠ 0
  · obtain ⟨eT₀, h0, hm0⟩ := h
    obtain ⟨z, hzG, hzOne, hzmt⟩ := _root_.GlobalTheory.LevelSeries.flip_central_exists D V T m eT₀ h0 hm0
    refine ⟨z, hzG, hzOne, ?_⟩
    intro eT heT hodd hcop hmT
    have h1 : eT₀ * eT = eT := GlobalTheory.Tow.idemSum_mul_of_subset heT h0 subset_rfl
    have h2 : eT * eT₀ = eT₀ := GlobalTheory.Tow.idemSum_mul_of_subset h0 heT subset_rfl
    have hEq : eT = eT₀ := by rw [← h1, mul_comm, h2]
    subst hEq
    have hidem : eT * eT = eT := GlobalTheory.Tow.idemSum_mul_of_subset heT heT subset_rfl
    have hinv : incA D ((m : D.host.E)⁻¹) * (m : AE D) = 1 := by
      rw [← map_natCast (incA D) m, ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hm0), map_one]
    have hpq : incA D ((m : D.host.E)⁻¹) ^ V.rank * (m : AE D) ^ V.rank = 1 := by
      rw [← mul_pow, hinv, one_pow]
    have hunit : (eT * incA D ((m : D.host.E)⁻¹) ^ V.rank + (1 - eT)) * (eT * (m : AE D) ^ V.rank + (1 - eT)) = 1 := by
      linear_combination (eT * eT) * hpq + (2 - incA D ((m : D.host.E)⁻¹) ^ V.rank - (m : AE D) ^ V.rank) * hidem
    let x : (AE D)ˣ := Units.mkOfMulEqOne _ _ hunit
    have hx : IsFlipDet V eT m x := hunit
    refine ⟨x, hx, ?_⟩
    obtain ⟨lam, Y, hY, hYd, hYc, hom⟩ := _root_.GlobalTheory.LevelSeries.moved_vacuum_eq_mean D ψ θ V W χV χW om ΛV ΛW sW f₀ hV T m eT z heT hodd hcop hmT hzG hzmt
    have hlam := _root_.GlobalTheory.FlipScal.moved_vacuum_factor D ψ θ V W χV χW om ΛV ΛW sW f₀ hV T m eT z x lam Y heT hodd hcop hmT hzG hzmt hx hY hYd hYc hom
    subst hlam
    have hs : flipScal χW V W T m x ≠ 0 := by
      unfold flipScal
      refine mul_ne_zero (inv_ne_zero (Circle.coe_ne_zero _)) (inv_ne_zero ?_)
      rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
      exact Nat.cast_pos.2 (Nat.pos_of_ne_zero (flipIdx_ne_zero V W T hm0))
    intro M u e e' P O hM hu he hTP he' hz
    exact GlobalTheory.T.centralFlip_maps_halfTranslates_span D ψ θ V W χV χW om ΛV ΛW sW f₀ hV T m eT z _ Y heT hodd hcop hmT hzmt hs hY hom M u e e' P O hM hu he hTP
      (_root_.GlobalTheory.FlipIdemSum.idemSum_flip_subset D e eT e' P T he heT hTP he') hz
  · refine ⟨1, (GfC V).one_mem, fun l _ => oneAt_one V l, ?_⟩
    intro eT heT hodd
    exact absurd ⟨eT, heT, (Nat.pos_of_ne_zero (by rintro rfl; exact (Nat.not_odd_zero hodd))).ne'⟩ h

end GlobalTheory.LevelSeries

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeChoiceFlatScalarConjTwist
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.FlatConj.flat_conj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (t t' : T0), VStd D i → FixBase T R i τ → ConjTup R τ t t' → ∀ f f', IsFlatVec R i t f → IsFlatVec R i t' f' → ∃ (z : GA D (Vc D i)) (c c' : ℂ) (s : (AE D)ˣ), IsCentAt i (R.Q t) z ∧ f = c • R.ωP i t (z, 1) (R.vP i t) ∧ f' = c' • R.ωP i t' (z, 1) (R.vP i t') ∧ c' = ((R.xi t' s : Circle) : ℂ) * τ c := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC hQG i τ t t' hV hFix hct f f' hf hf'
  obtain ⟨z, B, ε, r, ψP, hz, hB, hprim, hform⟩ := _root_.GlobalTheory.FlatConj.flatVec_factored_form D G Pl0 T0 A T R F hC hQG i t hV
  obtain ⟨s1, e1⟩ := hform t rfl f hf
  obtain ⟨s2, e2⟩ := hform t' hct.1 f' hf'
  obtain ⟨h1, hne, -, -⟩ := GlobalTheory.ConjRes.conj_res D G Pl0 T0 A T R F κ v₀ hC τ t t' hct
  have hg : ∀ PP ∈ R.Q t, ∃ a : (kP PP)ˣ, τ (GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t PP) r) =
      ((R.xiR t' PP a : ℂˣ) : ℂ) ^ r * GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) r := by
    intro PP hP
    obtain ⟨a, -, ha⟩ := (@GlobalTheory.complexMatrixGaussSum_norm_integral_galois (kP PP) (GlobalTheory.FlatConj.resField PP) (GlobalTheory.FlatConj.resFintype PP) (Classical.decEq _)
      (ψP PP) (R.xiR t PP) r (hprim PP hP) (hne PP hP) _ rfl).2.2.2 τ (R.xiR t' PP) (h1 PP hP)
    exact ⟨a, ha⟩
  choose a ha using hg
  let v : Pl D.host.E → ℂ := fun PP => if h : PP ∈ R.Q t then ((R.xiR t' PP (a PP h) : ℂˣ) : ℂ) else 1
  obtain ⟨s3, e3⟩ := GlobalTheory.FlatConj.prod_val (R.xi t') (R.Q t) v fun PP hP => by
    simp only [v, dif_pos hP]
    exact GlobalTheory.FlatConj.xiR_val hC t' PP (hct.1 ▸ hP) _
  have hprod : ∏ PP ∈ R.Q t, τ (GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t PP) r) =
      (∏ PP ∈ R.Q t, v PP) ^ r * ∏ PP ∈ R.Q t, GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) r := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun PP hP => ?_
    simp only [v, dif_pos hP]
    exact ha PP hP
  refine ⟨z, _, _, s2 * s1⁻¹ * s3 ^ (-((r : ℤ) * ε)), hz, e1, e2, ?_⟩
  have hX : ((R.xi t' s1 : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hV3 : ((R.xi t' s3 : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have key : τ (B * (∏ PP ∈ R.Q t, GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t PP) r) ^ ε * ((R.xi t s1 : Circle) : ℂ)) =
      B * ((∏ PP ∈ R.Q t, v PP) ^ r * ∏ PP ∈ R.Q t, GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) r) ^ ε *
        ((R.xi t' s1 : Circle) : ℂ) := by
    rw [map_mul, map_mul, map_zpow₀, map_prod, hprod, hB τ hFix, ← hct.2 s1]
  rw [key, e3]
  simp only [map_mul, map_inv, map_zpow, Circle.coe_mul, Circle.coe_inv, Circle.coe_zpow]
  rw [mul_zpow, ← zpow_natCast, ← _root_.zpow_mul, _root_.zpow_neg]
  have hW : ((R.xi t' s3 : Circle) : ℂ) ^ ((r : ℤ) * ε) ≠ 0 := zpow_ne_zero _ hV3
  field_simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProjectedThetaLiftExtremalVectorEqClassSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.LiftClassSum

theorem exists_projected_thetaLift_eq_sum : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q → ∀ y : (X.R.HV j t).H,
    (∀ (h : Bridge.Gf (Vc D j)) (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
        (X.R.HV j t).e y (h * (k : Bridge.Gf (Vc D j))) = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • (X.R.HV j t).e y h) →
    ∃ F ∈ (Y.Z.ρ.B i j b).formsC (Y.Z.ρ.tw i b 0 ∅ 1),
      (X.R.HW j (sg0 D X.A3.A)).e (X.R.thG j t y) (X.geo.v₀ j _) = Y.Z.ρ.sum i j b 0 ∅ 1 F := by
  intro D X E Y i j b t hxi hQ y hy
  obtain ⟨y', hy', he⟩ := _root_.GlobalTheory.ProjLiftLaw.projLift_law D X E Y i j b t hxi hQ y hy
  obtain ⟨F, hF, hs⟩ := _root_.GlobalTheory.LiftClassSum.exists_thetaLift_eq_classSum D X E Y i j b t hxi hQ y' hy'
  exact ⟨F, hF, he.trans (hs.trans (LinearMap.congr_fun (sum_eq_classSum_ωP D X E Y i j b t hxi hQ) F).symm)⟩

end GlobalTheory.LiftClassSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistConjugateTuplesSameRealisationExtension
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TwConj


open Classical in
theorem hasTuples_of_conj : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
  ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (ph : Fin D.R.m → ℂ) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)),
    Formalism.IndefR.Links.HostHyp D → GlobalTheory.BigOn.Exp.TwConj.Laws T R F κ v₀ O ph j B →
    ∀ (ψ ψ' : Twist D Circle) (t : T0) (τ : ℂ ≃+* ℂ), IsTupOf R B ψ t → ConjChar τ ψ ψ' → FixDat B τ →
      GlobalTheory.BigOn.Exp.TwConj.HasTuples T R κ v₀ O ph j B ψ ψ' := by
  intro hDS hCW h1 h2 h3 D G _ _ Pl0 T0 A T _ R F κ v₀ O ph j B hH hL ψ ψ' t τ ht hc hf
  have hC := hL.1
  obtain ⟨n, hn⟩ := GlobalTheory.ConjExt.exists_conj_pow hC.lev t
  obtain ⟨a, -, ha, b, hb⟩ := hn τ
  have hxi' : B.de.chi * ψ'.chi = R.xi t ^ a := by
    refine MonoidHom.ext fun x => Circle.ext ?_
    rw [ha x, ht.1]
    simp only [MonoidHom.mul_apply, Circle.coe_mul, map_mul, hf.1, hc.2]
  have hQ' : R.Q t = B.de.Q ∪ ψ'.Q := by rw [hc.1, ht.2]
  by_cases hχ : R.xiH t ^ a = R.xiH t
  · have e : R.xi t ^ a = R.xi t :=
      GlobalTheory.ChrEqUnique.idc_unique D _ _ _ (GlobalTheory.ConjExt.chrEq_pow (hC.lev.xi t) a) (by rw [hχ]; exact hC.lev.xi t)
    exact hasTuples_of_laws hL Ext.refl ht ⟨by rw [hxi', e], hQ'⟩
  · have h0 : R.xiH t ≠ 1 := fun h => hχ (by rw [h, one_pow])
    have h0a : R.xiH t ^ a ≠ 1 := fun h => h0 (by rw [← hb, h, one_pow])
    have hlev := twLev_of_core hC hL.2.2.2.2.1 t
    have hleva := GlobalTheory.TwLevPow.twLev_pow R F hC _ _ _ _ hlev a b hb
    obtain ⟨A0, R0, F0, v0, O0, hL0, hE0, hxi0, htr⟩ := GlobalTheory.BaseRestrict.restrict_to_base T R F κ v₀ O ph j B hL
    have hT0 := htr _ _ _ _ hlev
    have hT0a := htr _ _ _ _ hleva
    obtain ⟨T', A', R', F', v', O', hL', hE', htup⟩ := _root_.GlobalTheory.TupExt.extend_tuples h1 h2 h3 hDS hCW T R0 F0 κ v0 O0 ph j B hH hL0 Bool
      (fun b => if b then R.xiH t ^ a else R.xiH t) (fun b => if b then R.xi t ^ a else R.xi t) (fun _ => R.Q t)
      (fun b => if b then (fun PP => R.xiR t PP ^ a) else R.xiR t)
      (fun b => by cases b <;> assumption)
      (fun x y hxy => by
        cases x <;> cases y
        · rfl
        · exact absurd hxy.symm hχ
        · exact absurd hxy hχ
        · rfl)
      (fun b t0 => by rw [hxi0]; cases b; exacts [h0, h0a])
      (fun p hp => by
        obtain ⟨𝔭, h𝔭, h𝔭'⟩ := hT0.Q_de p hp
        exact ⟨𝔭, h𝔭, fun _ => h𝔭'⟩)
    obtain ⟨s, hs1, hs2⟩ := htup false
    obtain ⟨s', hs1', hs2'⟩ := htup true
    exact hasTuples_of_laws hL' (hE0.trans hE') (t := s) (t' := s')
      ⟨hs1.trans ht.1, hs2.trans ht.2⟩ ⟨hs1'.trans hxi'.symm, hs2'.trans hQ'⟩

end GlobalTheory.BigOn.Exp.TwConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalSeriesCoeffBoundedInSupOfTwistSeriesSid
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
noncomputable section
namespace GlobalTheory.XiBound

theorem exists_pow_mul_mem {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] {l : O} (hl : l ∈ IsLocalRing.maximalIdeal O) (z : K) :
    ∃ (n : ℕ) (o : O), algebraMap O K o = algebraMap O K (l ^ n) * z := by
  by_cases h0 : l = 0
  · exact ⟨1, 0, by simp [h0]⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨⟨a, d⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors O) z
  have hd : (d : O) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  obtain ⟨k, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
  have he : e ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hw
    exact (IsLocalRing.mem_maximalIdeal _).1 hl (hw ▸ w.isUnit)
  have hdvd : (d : O) ∣ l ^ k := by
    rw [hv, hw, mul_pow, ← pow_mul]
    exact mul_dvd_mul (Units.isUnit v).dvd (pow_dvd_pow ϖ (Nat.le_mul_of_pos_left k (Nat.pos_of_ne_zero he)))
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨k, a * t, ?_⟩
  simp only at hz
  rw [ht, map_mul, map_mul, ← hz]
  ring

theorem main : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → XiBdd Y.Z.rd := by
  intro hA hR hI D X E Y hF hP i hi j b s h P hd
  classical
  obtain ⟨u, c, hu, hK⟩ := GlobalTheory.XiIntComb.xi_int_comb hA hR hI D X E Y hF hP i hi j b s h P hd
  have hν : Y.Z.ν i j b ≠ 0 := (Y.Z.scalar i j b).ne
  have hFa : Faithful (Y.Z.rd i j b) :=
    realRd_faithful D X.Γ X.Pl0 X.I0 X.T X.A3 _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b (Y.Z.ν i j b)
      hν X.unif X.char.models.HW (Y.Z.vec j) ((_root_.GlobalTheory.TwUnit.isKsForm_and_unit D X E Y).1 _ (Nat.le_add_left _ _) j.2)
  have hinj := hFa.injective
  set lam : ℂ := (Y.Z.ν i j b)⁻¹ * (((D.ntw.l i : ℕ) : ℂ) ^ c * u) with hlam

  have step : ∀ Q M, InRange D.ntw i Q → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a x,
      Y.Z.rd i j b x = Y.Z.ρ.xi i j b D.nexp Q M h P a →
      ∃ x' ∈ D.nexp.Bsup i ((j : ℕ) + 1) b, Y.Z.rd i j b x' = lam • Y.Z.rd i j b x := by
    intro Q M hQ hs a x hx
    obtain ⟨n, o, m, hm, he⟩ := hK Q M hQ hs a
    let y : NX.Fm Y.S i ((j : ℕ) + 1) b :=
      ∑ k, ((show NX.KB Y.S i b from algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (o k)) • ((1 : NX.KB Y.S i b) ⊗ₜ[Y.S.Ks] m k) :
        NX.KB Y.S i b ⊗[Y.S.Ks] NX.FmK Y.S ((j : ℕ) + 1))
    have hy : y ∈ NX.Bsup Y.S i ((j : ℕ) + 1) b := by
      refine Submodule.sum_mem _ fun k _ => ?_
      exact (NX.Bsup Y.S i ((j : ℕ) + 1) b).smul_mem (o k) (Submodule.subset_span ⟨m k, hm k, rfl⟩)
    have hey : evK Y.YS X.geo.v₀ Y.Z.good i j b y = ∑ k, Y.Z.ρ.eO i b (o k) • evW Y.YS X.geo.v₀ j (Subtype.val (m k)) := by
      refine (map_sum (evK Y.YS X.geo.v₀ Y.Z.good i j b) (fun k => ((show NX.KB Y.S i b from algebraMap (D.ntw.O i)
        (FractionRing (D.ntw.O i)) (o k)) • ((1 : NX.KB Y.S i b) ⊗ₜ[Y.S.Ks] m k) : NX.KB Y.S i b ⊗[Y.S.Ks] NX.FmK Y.S ((j : ℕ) + 1)))
        Finset.univ).trans (Finset.sum_congr rfl fun k _ => ?_)
      rw [TensorProduct.smul_tmul', evK_tmul, smul_eq_mul, mul_one]
      rfl
    let x' := (Y.YS.eF i _ b (Nat.le_add_left _ _) j.2).symm y
    refine ⟨x', (Y.sup i _ b (Nat.le_add_left _ _) j.2 x').2 (by simp only [x', LinearEquiv.apply_symm_apply]; exact hy), ?_⟩
    change (Y.Z.ν i j b)⁻¹ • evK Y.YS X.geo.v₀ Y.Z.good i j b (Y.YS.eF i _ b (Nat.le_add_left _ _) j.2 x') = _
    rw [show Y.YS.eF i _ b (Nat.le_add_left _ _) j.2 x' = y from LinearEquiv.apply_symm_apply _ _, hey, ← he, hx, hlam,
      smul_smul]
  by_cases hex : ∃ μ : FractionRing (D.ntw.O i), Y.Z.ρ.e i b μ = lam
  · obtain ⟨μ, hμ⟩ := hex
    obtain ⟨N, o, ho⟩ := exists_pow_mul_mem (K := FractionRing (D.ntw.O i)) (D.ntw.O_l i) μ⁻¹
    refine ⟨N, fun Q M hQ hs a x hx => ?_⟩
    obtain ⟨x', hx'B, hx'⟩ := step Q M hQ hs a x hx
    have hμx : x' = μ • x := hinj (by rw [hx', map_smulₛₗ, hμ])
    by_cases hμ0 : μ = 0
    · exfalso
      rw [hμ0, map_zero, hlam] at hμ
      have hl : ((D.ntw.l i : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (D.ntw.lPrime i).out.ne_zero
      exact mul_ne_zero (inv_ne_zero hν) (mul_ne_zero (pow_ne_zero _ hl) hu) hμ.symm
    have : ((D.ntw.l i : D.ntw.O i) ^ N) • x = o • x' := by
      rw [hμx, ← algebraMap_smul (FractionRing (D.ntw.O i)) o, ← algebraMap_smul (FractionRing (D.ntw.O i)) ((D.ntw.l i : D.ntw.O i) ^ N),
        smul_smul, ho, mul_assoc, inv_mul_cancel₀ hμ0, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ hx'B
  · refine ⟨0, fun Q M hQ hs a x hx => ?_⟩
    obtain ⟨x', -, hx'⟩ := step Q M hQ hs a x hx
    by_cases h0 : Y.Z.rd i j b x = 0
    · rw [hinj (h0.trans (map_zero _).symm), smul_zero]
      exact Submodule.zero_mem _
    · exact absurd (hFa.mem_range_of_smul h0 ⟨x, rfl⟩ ⟨x', hx'⟩) hex

end GlobalTheory.XiBound
end
end

