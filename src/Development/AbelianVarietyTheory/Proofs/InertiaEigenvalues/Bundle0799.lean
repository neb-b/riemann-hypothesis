module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjFourierCoefficientsConjugateTuples
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0789
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0109
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GalRulGalRul
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0108
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0684
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0102
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.Columns.DecoFin

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRootOfUnityCoverFunctionReferenceTuple
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GalRef

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH
  Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct


set_option maxHeartbeats 1000000 in
theorem val_of_cXiAt {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {n r : ℕ} (V : HSp D) (hr : V.rank = r) (d : DeltaDat Xo c n)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : GlobalTheory.Member.IotaOK Dw V ι) (hpq : 1 ≤ Dw.p + Dw.q)
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hx₀ : ∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 →
      ReciprocityTheory.ChartRestriction.G.FD.gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) =
        Matrix.diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn Dw.q (a : ℕ) : ℝ) : ℂ))
    (hA : d.l₂.A = 1) (hs : d.cδ ∈ sec d.Xo₂ d.c₂ 0 0) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (hxi : ∀ h : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V h)) = 1)
    (U₂ : Unf d.Xo₂ d.c₂ (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)) r)
    (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r) (c0 : ℂ) (hc0 : c0 ≠ 0)
    (hv : GlobalTheory.OneMapAll.CXiAt V hr c.F.val.toRingHom d U₂ dict₂ ι x₀ xi c0) :
    (∀ y : FrPt d.Xo₂ d.c₂ (CAt (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F))),
      toC (evR d.Xo₂ d.c₂ d.cδ y) = c0) ∧
      Nonempty (FrPt d.Xo₂ d.c₂ (CAt (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)))) := by
  classical
  subst hr
  obtain ⟨hU, hW, g₀, e₀, F, ik, φ, th, hth, hD, hval⟩ := hv
  have hσ : GoodEmb d.c₂ (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)) := by
    have e : c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F) = d.c₂.F.val.toRingHom := RingHom.ext fun _ => rfl
    rw [e]; rfl
  have val₀ : ∀ h : GA D V, ∃ hx : (dict₂ h).2 ∈ (U₂.X (dict₂ h).1).dom,
      toC (evR d.Xo₂ d.c₂ d.cδ (U₂.un _ ⟨_, hx⟩)) = c0 := by
    intro h
    obtain ⟨γ, hγ, hΛ, hm, -⟩ := hD.2 h
    have hv := hval h γ ⟨hγ, hΛ, hm⟩
    rw [hxi (γ * h), Units.val_one, mul_one] at hv
    by_cases hx : (dict₂ h).2 ∈ (U₂.X (dict₂ h).1).dom
    · refine ⟨hx, ?_⟩
      rw [← hv]
      show _ = (if h' : (dict₂ h).2 ∈ (U₂.X (dict₂ h).1).dom then toC (evR d.Xo₂ d.c₂ d.cδ (U₂.un _ ⟨_, h'⟩)) else 0)
      rw [dite_eq_left hx]
    · exfalso
      apply hc0
      rw [← hv]
      show (if h' : (dict₂ h).2 ∈ (U₂.X (dict₂ h).1).dom then toC (evR d.Xo₂ d.c₂ d.cδ (U₂.un _ ⟨_, h'⟩)) else 0) = 0
      rw [dite_eq_right hx]
  choose hdom val₀ using val₀
  refine ⟨fun y => ?_, ⟨U₂.un _ ⟨_, hdom 1⟩⟩⟩
  obtain ⟨h, hh⟩ := GlobalTheory.TwistTie.exists_dict_over V U₂ dict₂ ι e₀ F ik φ th x₀ hσ hA hpq hU hW hD hι hth
    (fun k τ hτ => by
      rw [(hW k).1, (hU.2.1 k).1]
      exact hx₀ τ (((hU.2.1 k).2 τ).1 hτ)) hdom y
  rw [GlobalTheory.WeightZeroValue.evR_eq_of_same_point hs hh]
  exact val₀ h

end GlobalTheory.GalRef

namespace GlobalTheory.GalRef

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory


set_option maxHeartbeats 1000000 in
theorem mem_of_val {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) (hs : d.cδ ∈ sec d.Xo₂ d.c₂ 0 0) (c0 : ℂ) (m : ℕ)
    (hm : 0 < m) (hc0 : c0 ^ m = 1)
    (hval : ∀ y : FrPt d.Xo₂ d.c₂ (CAt (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F))),
      toC (evR d.Xo₂ d.c₂ d.cδ y) = c0)
    (y₀ : FrPt d.Xo₂ d.c₂ (CAt (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)))) : c0 ∈ c.F := by
  have hS : Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  let σ₂ : d.c₂.F →+* ℂ := c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)
  have hσ₂ : ∀ a : d.c₂.F, σ₂ a ∈ c.F := fun a => (d.eF.symm a).2
  have hfix : ∀ τ : ℂ ≃+* ℂ, (∀ x ∈ c.F, τ x = x) → τ c0 = c0 := by
    intro τ hτ
    let φ : CAt σ₂ →ₐ[d.c₂.F] CAt σ₂ :=
      { toRingHom := (τ : ℂ →+* ℂ)
        commutes' := fun a => hτ _ (hσ₂ a) }
    obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw d.l₂ d.Xo₂ d.c₂ _ _ φ y₀
    have hx : z.x = spMap (τ : ℂ →+* ℂ) ≫ y₀.x := hz.1
    have e := GlobalTheory.GalTw.CharSec.conj_value σ₂ σ₂ τ (RingHom.ext fun a => (hτ _ (hσ₂ a)).symm) hs y₀ z hx
    rw [hval, hval] at e
    exact e.symm
  let K := c.F
  let L := IntermediateField.adjoin K {c0}
  have hint : IsIntegral K c0 := by
    refine IsIntegral.of_pow hm ?_
    rw [hc0]; exact isIntegral_one
  haveI : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional hint
  haveI : FiniteDimensional ℚ K := c.fin
  haveI : FiniteDimensional ℚ L := Module.Finite.trans K L
  haveI : Countable L := (Module.finBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance
  have hr : IsIntegral K (⟨c0, IntermediateField.mem_adjoin_simple_self K c0⟩ : L) := by
    refine IsIntegral.of_pow hm ?_
    have : (⟨c0, IntermediateField.mem_adjoin_simple_self K c0⟩ : L) ^ m = 1 := Subtype.ext (by simpa using hc0)
    rw [this]; exact isIntegral_one
  obtain ⟨a, ha⟩ := GlobalTheory.CompRat.FixedConst.mem_range_of_fixed (K := K) (L := L) L.val hr fun τ hτ => hfix τ fun x hx => hτ ⟨x, hx⟩
  have : ((algebraMap K L a : L) : ℂ) = c0 := congrArg Subtype.val ha
  rw [← this]
  exact a.2

end GlobalTheory.GalRef

namespace GlobalTheory.GalRef

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj


set_option maxHeartbeats 1000000 in
theorem eq_const_of_val {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) (hs : d.cδ ∈ sec d.Xo₂ d.c₂ 0 0) (a : d.c₂.F)
    (hval : ∀ y : FrPt d.Xo₂ d.c₂ (CAt (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F))),
      toC (evR d.Xo₂ d.c₂ d.cδ y) = ((d.eF.symm a : c.F) : ℂ)) :
    d.cδ = a • (1 : Rul d.Xo₂ d.c₂) := by
  have h1 : (1 : Rul d.Xo₂ d.c₂) ∈ sec d.Xo₂ d.c₂ 0 0 := GlobalTheory.LevelCover.one_mem_sec_zero _ _
  have hz : d.cδ + (-a) • (1 : Rul d.Xo₂ d.c₂) = 0 := by
    refine GlobalTheory.GalTw.CharSec.sec_eq_zero_of_complex (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F))
      (add_mem hs (Submodule.smul_mem _ _ h1)) fun y => ?_
    have e1 : evR d.Xo₂ d.c₂ (1 : Rul d.Xo₂ d.c₂) y = 1 :=
      evalAt_one _ _ y (GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂ _ y)
    have e2 : evR d.Xo₂ d.c₂ d.cδ y = algebraMap d.c₂.F _ a := hval y
    unfold evR at e1 e2 ⊢
    rw [evalAt_add, evalAt_smul, e1, e2, mul_one, map_neg, add_neg_cancel]
  rw [neg_smul, ← sub_eq_add_neg, sub_eq_zero] at hz
  exact hz

end GlobalTheory.GalRef

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.GalRef


set_option maxHeartbeats 4000000 in
theorem exists_root_galRul_isSum : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ M : OMDat T.toCore R i T0 id, M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → M.lev = (O i).lev → (∀ c, ExtC R i (inC (O i).c') (O i).c0' c ↔ ExtC R i (inC M.c') M.c0' c) → Normal ℚ M.c'.F → GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 → (∀ t x, ((R.xi t x : Circle) : ℂ) ∈ M.c'.F) → (∀ t t' : T0, R.Q t' = R.Q t → ∃ e, SameCover M t t' e) → ∃ c₀ : M.c'.F, IsRoot1 ((c₀ : M.c'.F) : ℂ) ∧ ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (hf : Fixes M.c' ta) (x x' : M.Cl' A.μ0 → VsV D i M.c'.F), (∀ k, M.io (x' k) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (M.io (x k))) → ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank, GlobalTheory.OneMapAll.IsSum M A.μ0 x f → (ta c₀ * c₀⁻¹)⁻¹ • galRul hf f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank ∧ GlobalTheory.OneMapAll.IsSum M A.μ0 x' ((ta c₀ * c₀⁻¹)⁻¹ • galRul hf f) := by
  intro hC D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hnV hcore hfin hfw hioE hQG i hpins htie M hM hlev hext hnorm hcurve hxiF
    hsame
  obtain ⟨fw⟩ := hfw
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hσ : GoodEmb T.Q.c M.s0 := rfl
  obtain ⟨hι, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T fw.laws _ hj _ hσ (Wc D i) M.hV (rank_Wc i)
  have hpq : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by
    obtain ⟨h1, -, h3⟩ := (GlobalTheory.Member.exists_iotaOK D T.Q fw.laws.pins _ hj).2
    omega
  have hRxi : R.xi A.μ0 = 1 :=
    MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hcore.lev.xi_base ▸ hcore.lev.xi A.μ0))
  have hxi1 : ∀ h : GA D (Wc D i), M.xi A.μ0 (Matrix.GeneralLinearGroup.det (finHom (Wc D i) h)) = 1 := fun h => by
    obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D (Wc D i)).1 h
    have e : _ = ((R.xi A.μ0 x : Circle) : ℂ) := (hM.tuple A.μ0).xi h x hx
    rw [hRxi, MonoidHom.one_apply, Circle.coe_one] at e
    exact Units.ext e
  obtain ⟨c0, ⟨m, hm, hc0⟩, hv⟩ := hM.cxi
  obtain ⟨hd, hA, hN⟩ := hM.cov A.μ0
  have hs := hd.2.2.2.2.2.2.2.1
  have hc0ne : c0 ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hc0
    exact zero_ne_one hc0
  obtain ⟨hval, ⟨y₀⟩⟩ := GlobalTheory.GalRef.val_of_cXiAt (Wc D i) (rank_Wc i) (M.dδ A.μ0) (iotaW T i) hι hpq _ hx₀ hA hs
    (M.xi A.μ0) hxi1 (M.U₂ A.μ0) (M.dict₂ A.μ0) c0 hc0ne (hv A.μ0)
  have hmem := GlobalTheory.GalRef.mem_of_val (M.dδ A.μ0) hs c0 m hm hc0 hval y₀
  let c₀ : M.c'.F := ⟨c0, hmem⟩
  have hc₀ne : c₀ ≠ 0 := fun h => hc0ne (congrArg Subtype.val h)
  have hcδ : (M.dδ A.μ0).cδ = (M.dδ A.μ0).eF c₀ • (1 : Rul (M.dδ A.μ0).Xo₂ (M.dδ A.μ0).c₂) :=
    GlobalTheory.GalRef.eq_const_of_val _ hs _ fun y => by
      rw [hval y, AlgEquiv.symm_apply_apply]
  refine ⟨c₀, ⟨m, hm, hc0⟩, ?_⟩
  intro τ ta hta hfb hf x x' hx f hfs hsum
  have h₂ : Fixes (M.dδ A.μ0).c₂ (covAut (M.dδ A.μ0) ta) := GlobalTheory.GalTw.fixes_covAut (M.dδ A.μ0) hA hf
  have hka : ta c₀ * c₀⁻¹ ≠ 0 := mul_ne_zero ((map_ne_zero ta).2 hc₀ne) (inv_ne_zero hc₀ne)
  have hgal : galRul h₂ (M.dδ A.μ0).cδ = (M.dδ A.μ0).eF (ta c₀ * c₀⁻¹) • (M.dδ A.μ0).cδ := by
    rw [hcδ, GlobalTheory.GalTw.Test.galRul_const, covAut_apply_eF, smul_smul, ← map_mul, mul_assoc, inv_mul_cancel₀ hc₀ne,
      mul_one]
  have hcx : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra (M.dδ A.μ0).c₂.F k] (y₂ : FrPt (M.dδ A.μ0).Xo₂ (M.dδ A.μ0).c₂ k),
      evR (M.dδ A.μ0).Xo₂ (M.dδ A.μ0).c₂ (galRul h₂ (M.dδ A.μ0).cδ) y₂ =
        algebraMap (M.dδ A.μ0).c₂.F k ((M.dδ A.μ0).eF (ta c₀ * c₀⁻¹)) * evR (M.dδ A.μ0).Xo₂ (M.dδ A.μ0).c₂ (M.dδ A.μ0).cδ y₂ := by
    intro k _ _ _ y₂
    rw [hgal]
    exact evalAt_smul _ _ _ _ y₂
  have hsame0 : SameCover M A.μ0 A.μ0 (Equiv.refl _) :=
    ⟨⟨_, rfl⟩, HEq.rfl, HEq.rfl, rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩
  have hconj : ConjTup R τ (id A.μ0) (id A.μ0) := ⟨rfl, fun x => by simp [hRxi]⟩
  obtain ⟨u, s, w', hu, hw'e, hw⟩ := _root_.GlobalTheory.ConjDatum.conj_coeff D G Pl0 T0 A T R F κ v₀ hcore ⟨fw⟩ i T0 id M hM τ ta hta hfb A.μ0 A.μ0
    (Equiv.refl _) hsame0 hconj
  obtain ⟨hvol, hep⟩ := _root_.GlobalTheory.ConjScalar.conj_vol_ep D G Pl0 T0 A T R F κ v₀ hcore ⟨fw⟩ i T0 id M hM τ ta hta hfb A.μ0 A.μ0
    (Equiv.refl _) hsame0 hconj
  have hu1 : u = 1 := by
    apply Subtype.ext
    rw [hu]
    simp [hRxi]
  have hw'1 : w' = M.w A.μ0 := funext fun k => eq_of_heq (hw'e k)
  subst hu1 hw'1
  have hio : ∀ v, M.io v ∈ HHa (T.Q.Dw ((i : ℕ) + 1)).mult (Vc D i).rank M.c'.F ComplexEmbedding.conjugate
      (InPsi T.Q.H) (fun τ k => wtA (κ i) (τ, k)) := fun v => by
    obtain ⟨-, cga, -, -, hr, -⟩ := hM.io
    have hv := hr.le (LinearMap.mem_range_self M.io v)
    exact (Submodule.span_le (p := GlobalTheory.FrameRead.CoefMap.harmSub _ _ _ _ _ _)).2 (fun _ hP => hP) hv
  have key := GlobalTheory.GalTw.isThClsD_galRul hC _ _ _ _ _ M.c' ta hf _ (M.dδ A.μ0) h₂ hN hs (M.dδ A.μ0).cδ
    (ta c₀ * c₀⁻¹) 1 hka one_ne_zero hcx (M.Cl' A.μ0) (M.w A.μ0) (M.w A.μ0) (M.La A.μ0) (M.Nc A.μ0) (M.gam A.μ0)
    (M.vol A.μ0) (M.ep A.μ0) _ M.io (wtA (κ i)) hio hw x x' hx _ f hfs hsum
  rw [mul_one] at key
  refine ⟨key.1, ?_⟩
  have e1 : ta (M.vol A.μ0) = M.vol A.μ0 := hvol
  have e2 : (fun k => ta (M.ep A.μ0 k)) = M.ep A.μ0 := funext hep
  have k2 := key.2
  rw [e1, e2] at k2
  exact k2

end GlobalTheory.GalRef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepGoodTwist
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilTwistExists

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isHeckeChar_mul' {χ χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) (h' : IsHeckeChar D χ') :
    IsHeckeChar D (χ * χ') :=
  ⟨h.1.mul h'.1, fun x => by rw [MonoidHom.mul_apply, h.2 x, h'.2 x, mul_one]⟩

theorem isHeckeChar_inv' {χ : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) : IsHeckeChar D χ⁻¹ :=
  ⟨h.1.inv, fun x => by rw [MonoidHom.inv_apply, h.2 x, inv_one]⟩

theorem resEta_zero_of_real {χ ξ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D ξ n) (hr : ∀ a, χ (idF D a) = 1) :
    ResEta D χ 0 :=
  ⟨h.1, fun η _ a => by rw [hr, pow_zero]⟩

theorem exists_isWeil : ∀ (D : D7) (S T : HSp D) (B : Base S T), GlobalTheory.Published.WeilRepresentationUnitaryPair → B.Good →
    IsStdChar D B.F.ψ (-1) → ∀ t : Twist D Circle, t.Good → ∃ ω, B.IsWeil t.chi ω := by
  intro D S T B hW hB hψ t ht
  have hEta : ResEta D B.eta 1 := hB.eta.2.2.1
  have h0 : ResEta D (B.mu * t.chi) 0 := by
    refine resEta_zero_of_real hEta fun a => ?_
    rw [MonoidHom.mul_apply, Base.mu, MonoidHom.mul_apply, hB.real, ht.real, hB.de.real, one_mul, one_mul]
  have hH : IsHeckeChar D (B.mu * t.chi) :=
    isHeckeChar_mul' (isHeckeChar_mul' hB.hecke hB.de.isHeckeChar) ht.isHeckeChar
  have hS : ResEta D (B.mu * t.chi) S.rank :=
    Formalism.L2.Theta.resEta_parity h0 (by rw [Nat.even_iff.1 hB.even])
  have hT : ResEta D (B.mu * t.chi * B.eta⁻¹) T.rank := by
    have h1 := Formalism.L2.Theta.resEta_mul h0 (Formalism.L2.Theta.resEta_inv hEta)
    exact Formalism.L2.Theta.resEta_parity h1 (by rw [Nat.odd_iff.1 hB.odd])
  exact hW D B.F.ψ S T _ _ hψ hH (isHeckeChar_mul' hH (isHeckeChar_inv' hB.eta.1)) hS hT

end GlobalTheory.WeilTwistExists

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinPartMulIncAMem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.HeckeDetChar

open Formalism.L2.JoinChr
open Formalism.L2.NTheta (IsIdemAt)

variable {D : D7}

theorem place_eq {e : AE D} {P P' : Pl D.host.E} (h : IsIdemAt e P) (h' : IsIdemAt e P') : P = P' := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
  · rw [h.2 x hx, h'.2 x hx]

theorem finPart_mem {e : AE D} {P : Pl D.host.E} (he : IsIdemAt e P) : finPart D e ∈ intAE D := by
  by_contra hc
  have := (he.2 1 one_ne_zero).2 (by
    rwa [show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, inv_one, RingHom.map_one, mul_one])
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)

theorem finPart_mul_incA_mem {e : AE D} {P : Pl D.host.E} (he : IsIdemAt e P) {x : D.host.E}
    (hx : P.valuation D.host.E x ≤ 1) : finPart D (e * incA D x) ∈ intAE D := by
  obtain ⟨n, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer x hx
  have hd : (d : 𝓞 D.host.E) ∉ P.asIdeal := d.2
  have hd0 : (d : 𝓞 D.host.E) ≠ 0 := fun h0 => hd (h0 ▸ zero_mem _)
  have hdE : ((d : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    intro h0; apply hd0; exact RingOfIntegers.ext h0
  have hxe : x = (n : D.host.E) * ((d : 𝓞 D.host.E) : D.host.E)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hdE]; exact h
  have h1 : finPart D (e * incA D (((d : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D :=
    not_not.1 (mt (he.2 _ hd0).2 hd)
  rw [hxe, RingHom.map_mul (incA D), show e * (incA D (n : D.host.E) * incA D (((d : 𝓞 D.host.E) : D.host.E)⁻¹)) =
    incA D (n : D.host.E) * (e * incA D (((d : 𝓞 D.host.E) : D.host.E)⁻¹)) by ring, RingHom.map_mul (finPart D)]
  exact GlobalTheory.HeckeConj.mul_mem_intAE D (GlobalTheory.SplitIndex.finPart_incA_mem n) h1

theorem idem_mul_eq_zero {Q : Finset (Pl D.host.E)} (hS : SplitSet Q) {P : Pl D.host.E}
    (hoff : Bridge.SplitOff P (Q : Set (Pl D.host.E))) {e : AE D} (he : IsIdemAt e P) :
    (idem Q + cA D (idem Q)) * e = 0 := by
  have hc : IsIdemAt (cA D e) (conjPl P) := GlobalTheory.MovedIdem.isIdemAt_conj he fun _ => Iff.rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [idem, map_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_eq_zero fun Q' hQ' => ?_
  have he' := hS.isIdemAt hQ'
  rw [add_mul]
  have a1 : idemAt Q' * e = 0 := by
    rcases GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero he'.1 he.1 with h | h
    · rw [h] at he'
      exact absurd (place_eq he he' ▸ hQ' : P ∈ (Q : Set (Pl D.host.E))) hoff.2.1
    · exact h
  have a2 : cA D (idemAt Q') * e = 0 := by
    rcases GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero he'.1 hc.1 with h | h
    · rw [h] at he'
      have hPQ := place_eq hc he'
      refine absurd ?_ (hoff.2.2 Q' hQ')
      rw [← hPQ]
      ext x
      rw [Formalism.L2.Col.mem_conjIdeal]
      rfl
    · have := congrArg (cA D) h
      rwa [map_mul, GlobalTheory.MovedIdem.cA_cA, map_zero] at this
  rw [a1, a2, add_zero]

theorem chi_eq_one {χ : (AE D)ˣ →* Circle} {Q : Finset (Pl D.host.E)} (hχ : GlobalTheory.ExportSeries.UnramOutside χ Q)
    {e : AE D} {P : Pl D.host.E} (he : IsIdemAt e P) (hQ : (idem Q + cA D (idem Q)) * e = 0) (x : (AE D)ˣ)
    (y y' : AE D) (hx : (x : AE D) = 1 + e * (y - 1)) (hx' : ((x⁻¹ : (AE D)ˣ) : AE D) = 1 + e * (y' - 1))
    (hy : finPart D (e * y) ∈ intAE D) (hy' : finPart D (e * y') ∈ intAE D) : χ x = 1 := by
  have key : ∀ w : AE D, finPart D (e * w) ∈ intAE D → finPart D (1 + e * (w - 1)) ∈ intAE D := fun w hw => by
    rw [show 1 + e * (w - 1) = 1 - e + e * w by ring, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one]
    exact add_mem (sub_mem (GlobalTheory.HeckeConj.one_mem_intAE D) (finPart_mem he)) hw
  refine hχ x ?_ ?_ ?_ ?_
  · rw [hx, RingHom.map_add (f := _), RingHom.map_one, RingHom.map_mul, GlobalTheory.StepVec.infPart_idemAt he, zero_mul, add_zero]
  · rw [hx]; exact key y hy
  · rw [hx']; exact key y' hy'
  · rw [hx, mul_add, mul_one, ← mul_assoc, hQ, zero_mul, add_zero]

theorem locE_pow {e : AE D} (he : e * e = e) (a : AE D) (k : ℕ) :
    (1 + e * (a - 1)) ^ k = 1 + e * (a ^ k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    linear_combination (a ^ k - 1) * (a - 1) * he

theorem isPlIdem {e : AE D} {P : Pl D.host.E} (he : IsIdemAt e P) : IsPlIdem D e P := by
  obtain ⟨⟨h1, h2, v, ε, hv, hs⟩, h3⟩ := he
  exact ⟨h1, ⟨v, ε, hv, Or.inl ⟨h2, hs⟩⟩, h3⟩

theorem locU_inv {e : AE D} (he : e * e = e) (k : D.host.Eˣ) :
    (((locU he k)⁻¹ : (AE D)ˣ) : AE D) = locE D e ((k⁻¹ : D.host.Eˣ) : D.host.E) := by
  have hmul : locU he k * locU he k⁻¹ = 1 := by
    apply Units.ext
    rw [Units.val_mul, locU_val, locU_val, locE_mul_locE he, Units.mul_inv, Units.val_one]
    simp [locE]
  rw [inv_eq_of_mul_eq_one_right hmul, locU_val]

theorem val_unif {P : Pl D.host.E} {ϖ : 𝓞 D.host.E} (hP : ϖ ∈ P.asIdeal) (hP2 : ϖ ∉ P.asIdeal ^ 2) :
    P.valuation D.host.E (ϖ : D.host.E) = WithZero.exp (-1 : ℤ) := by
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; exact hP2 (zero_mem _)
  rw [show (ϖ : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E ϖ from rfl, P.valuation_of_algebraMap]
  have a1 := (P.intValuation_lt_one_iff_mem ϖ).2 hP
  have a2 := (P.intValuation_le_pow_iff_mem ϖ 2).not.2 hP2
  rw [P.intValuation_eq_exp_neg_multiplicity hϖ0] at a1 a2 ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at a1
  rw [WithZero.exp_le_exp] at a2
  congr 1
  push_cast at a2
  omega

theorem chi_detAt : ∀ {D : D7} {χ : (AE D)ˣ →* Circle} {c : Formalism.L2.Host.HChar D.host.E}, ChrEq χ c →
    ∀ {Q : Finset (Pl D.host.E)}, GlobalTheory.ExportSeries.UnramOutside χ Q → GlobalTheory.ExportSeries.SplitSet Q → ∀ {P : Pl D.host.E},
    Bridge.SplitOff P (Q : Set (Pl D.host.E)) → ∀ {V : HSp D} {k : ℕ} {α : GA D V}, IsHeckeAt V P k α →
    ∀ {z : (AE D)ˣ}, IsDetAt (idemAt P) V α z → ((χ z : Circle) : ℂ) = ((c.val P : ℂˣ) : ℂ) ^ k := by
  intro D χ c hχc Q hU hS P hoff V k α hα z hz
  obtain ⟨e, ϖ, he, hϖP, hϖP2, hH⟩ := hα
  rw [idemAt_eq he] at hz
  obtain ⟨-, -, -, -, u, u', hu, hu', huu, hdet⟩ := hH
  have hQe := idem_mul_eq_zero hS hoff he
  have hee : e * e = e := he.1.1
  have hv := val_unif hϖP hϖP2
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact WithZero.exp_ne_zero hv.symm
  set ϖU : D.host.Eˣ := Units.mk0 (ϖ : D.host.E) hϖ0 with hϖU

  let wU : (AE D)ˣ := ⟨1 + e * (u - 1), 1 + e * (u' - 1),
    by linear_combination (u - 1) * (u' - 1) * hee + huu,
    by linear_combination (u - 1) * (u' - 1) * hee + huu⟩
  have hw : χ wU = 1 := chi_eq_one hU he hQe wU u u' rfl rfl
    (by rw [RingHom.map_mul]; exact GlobalTheory.HeckeConj.mul_mem_intAE D (finPart_mem he) hu)
    (by rw [RingHom.map_mul]; exact GlobalTheory.HeckeConj.mul_mem_intAE D (finPart_mem he) hu')

  have hz' : z = locU hee ϖU ^ k * wU := by
    apply Units.ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, locU_val, locE, locE_pow hee, hz]
    show e * (mt V α).det + (1 - e) = (1 + e * (incA D (ϖ : D.host.E) ^ k - 1)) * (1 + e * (u - 1))
    linear_combination hdet - (incA D (ϖ : D.host.E) ^ k - 1) * (u - 1) * hee

  have h1 : ((χ (locU hee ϖU) : Circle) : ℂ) = ((c.locK P ϖU : ℂˣ) : ℂ) :=
    hχc.2 P e (isPlIdem he) ϖU _ (locU_val hee ϖU)

  set rU : D.host.Eˣ := ϖU * (Formalism.L2.Host.unif P)⁻¹ with hrU
  have hvπ : P.valuation D.host.E ((Formalism.L2.Host.unif P : D.host.Eˣ) : D.host.E) = WithZero.exp (-1 : ℤ) := by
    have := Formalism.L2.Host.unif_spec P
    unfold Formalism.L2.Host.IsUnifAt at this
    rw [← this]
    show _ = Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) _)
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _).symm
  have hvr : P.valuation D.host.E (rU : D.host.E) = 1 := by
    rw [hrU, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hvπ, hϖU, Units.val_mk0, hv]
    exact mul_inv_cancel₀ (WithZero.exp_ne_zero)
  have hr1 : χ (locU hee rU) = 1 := by
    refine chi_eq_one hU he hQe _ (incA D (rU : D.host.E)) (incA D ((rU⁻¹ : D.host.Eˣ) : D.host.E)) rfl
      (locU_inv hee rU) (finPart_mul_incA_mem he hvr.le) (finPart_mul_incA_mem he ?_)
    rw [Units.val_inv_eq_inv_val, map_inv₀, hvr, inv_one]
  have hr2 : ((χ (locU hee rU) : Circle) : ℂ) = ((c.locK P rU : ℂˣ) : ℂ) :=
    hχc.2 P e (isPlIdem he) rU _ (locU_val hee rU)
  rw [hr1] at hr2
  have hval : ((c.locK P ϖU : ℂˣ) : ℂ) = ((c.val P : ℂˣ) : ℂ) := by
    have : ϖU = rU * Formalism.L2.Host.unif P := by rw [hrU, inv_mul_cancel_right]
    rw [this, map_mul, Units.val_mul, ← hr2, Formalism.L2.Host.HChar.val]
    simp
  rw [hz', map_mul, map_pow, hw, mul_one, Circle.coe_pow, h1, hval]

end GlobalTheory.HeckeDetChar
end
end

