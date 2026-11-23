module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateIntertwinerValuesSobolevContinuous
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingReindex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0197
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0347
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0348
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HkRelFrOfTransportIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0352
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerContinuousRepresentativePowerBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjRepBound


set_option maxHeartbeats 1000000 in
theorem contRep_bound : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → 1 ≤ (D.sp.Y 0).rank → ∃ m : ℕ, ∀ u : (MP R).Vec, ∃ C : ℝ, ∀ y : X.B.I.GA, ‖GlobalTheory.ConjRowMult.contRepL X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) y‖ ≤ C * (GlobalTheory.Count.tau1 X.B.I y)⁻¹ ^ m := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h h1 h2 h3 hH hι t c ht hcl hc Φ hΦ hrep hrank
  classical
  have hn : 1 ≤ X.B.I.n := by
    rw [← GlobalTheory.Core.Mi.rank_eq X h]
    exact hrank
  have hg : 1 ≤ X.B.g := by
    rw [X.g_eq]
    exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hexp : ∀ τ, ∀ Y ∈ lieAt (D.sp.Y 0) τ, ∀ s : ℝ,
      NormedSpace.exp (s • Y) ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ) := fun τ Y hY s =>
    GlobalTheory.SmoothAutCheck.exp_mem_UH (Formalism.IndefR.Eqv.gramAt_isUnit D (D.sp.Y 0) τ) hY s
  obtain ⟨-, hfin, -, hpl, -⟩ := GlobalTheory.ConjRowAut.iota_data R.θ h3.inf hexp X.B.I h
  have hιt : (iotaX X h t).1 = 1 := hfin t ht
  have hcomm : ∀ z : X.B.I.GA, z.2 = 1 → iotaX X h t * z = z * iotaX X h t := by
    intro z hz
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_mul, hιt]
    · simp [Prod.snd_mul, hz]
  have hsymm : ∀ z, iotaX X h ((iotaX X h).toMulEquiv.symm z) = z := fun z =>
    (iotaX X h).toMulEquiv.apply_symm_apply z
  obtain ⟨f, hfdef⟩ : ∃ f : (MP R).Vec → X.B.I.GA → ℂ, ∀ u,
      f u = GlobalTheory.ConjRowMult.contRepL X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) :=
    ⟨_, fun _ => rfl⟩
  have hf : ∀ u, Formalism.L2.SG.EvalTOntoRep.IsContRep X
      (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) (f u) := by
    intro u
    obtain ⟨ψ, hψ⟩ := hrep u
    rw [hfdef, GlobalTheory.ConjRowMult.contRepL_spec X hψ]
    exact hψ
  have hK : ∀ u, ∀ k ∈ X.B.I.Kg X.B.g, ∀ y, f u (y * (1, k)) = f u y := by
    intro u k hk y
    obtain ⟨S, -, hS⟩ := Submodule.mem_map.mp hΦ
    have hΦz : ∀ z, Φ z = X.B.Re (S z) := fun z => by rw [← hS]; rfl
    have hR : X.B.R (1, k) (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) =
        Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u)) := by
      rw [hΦz]
      exact ContinuousLinearMap.ext_iff.mp (GlobalTheory.Dec.CuspFrame.re_fixed X.B k hk) _
    have hr := Formalism.L2.SG.EvalTOntoRep.contRep_reg X (hf u) ((1, k) : X.B.I.GA)
    rw [hR] at hr
    exact congrFun (Formalism.L2.SG.EvalTOntoRep.contRep_unique X hr (hf u)) y
  have he := _root_.GlobalTheory.ConjEquivReal.conjMap_update_real hDS R F X h h1 h2 h3 hH hι t c ht hcl hc Φ hΦ hrep
  have hs := _root_.GlobalTheory.ConjRowCont.conjMap_sobCont hDS R F X h h1 h2 h3 hH hι t c ht hcl hc Φ hΦ hrep
  obtain ⟨m, hm⟩ := _root_.GlobalTheory.SobolevBound.derivative_closed_class_bound X.B hn hg
  have hW : ∀ g ∈ Set.range f, (∃ G, GlobalTheory.Dec.IsContRep X.B G g) ∧
      (∀ k ∈ X.B.I.Kg X.B.g, ∀ y, g (y * (1, k)) = g y) ∧
      ∀ (v : NumberField.InfinitePlace X.B.I.F) (E : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie (X.B.I.ε v)), ∃ g' ∈ Set.range f,
        ∀ y, HasDerivAt (fun s : ℝ => g (y * GlobalTheory.SobolevBound.onePar X.B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace X.B v E) s))
          (g' y) 0 := by
    rintro _ ⟨u, rfl⟩
    refine ⟨⟨_, hf u⟩, hK u, fun v E => ?_⟩
    obtain ⟨τ, Y, hY, hYt⟩ := hpl v E.1 E.2
    have h2s : ∀ s : ℝ, (iotaX X h (oneP R.θ (D.sp.Y 0) τ Y s)).2 = 1 := fun s => (hYt s).1
    have hone : ∀ s : ℝ, iotaX X h (oneP R.θ (D.sp.Y 0) τ Y s) =
        GlobalTheory.SobolevBound.onePar X.B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace X.B v E) s := fun s =>
      GlobalTheory.RepSmooth.eq_onePar X.B v E s (hYt s).1 (hYt s).2.1 (hYt s).2.2
    refine ⟨f (Function.update u τ (GlobalTheory.RepSmooth.der u τ hY)), ⟨_, rfl⟩, fun y => ?_⟩
    have key := (GlobalTheory.RepSmooth.hasDerivAt_switch he hs τ u hY (iotaX X h).toMulEquiv
      (fun s => iotaX X h (oneP R.θ (D.sp.Y 0) τ Y s)) (fun _ => rfl) (y * iotaX X h t)).star
    have hfun : (fun s : ℝ => f u (y * GlobalTheory.SobolevBound.onePar X.B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace X.B v E) s)) =
        fun s => star (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u ((iotaX X h).toMulEquiv.symm
          (y * iotaX X h t * iotaX X h (oneP R.θ (D.sp.Y 0) τ Y s)))) := by
      funext s
      erw [GlobalTheory.ConjRowMult.conjMap_apply X (MP R) c Φ h t]
      rw [star_star, ← hone s, hfdef]
      congr 1
      erw [map_mul, map_inv, hsymm]
      rw [mul_assoc y, hcomm _ (h2s s), ← mul_assoc, mul_inv_cancel_right]
    have hval : f (Function.update u τ (GlobalTheory.RepSmooth.der u τ hY)) y =
        star (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t (Function.update u τ (GlobalTheory.RepSmooth.der u τ hY))
          ((iotaX X h).toMulEquiv.symm (y * iotaX X h t))) := by
      erw [GlobalTheory.ConjRowMult.conjMap_apply X (MP R) c Φ h t]
      rw [star_star]
      erw [map_mul, map_inv, hsymm]
      rw [mul_inv_cancel_right, hfdef]
    rw [hfun, hval]
    exact key
  refine ⟨m, fun u => ?_⟩
  have hb := hm (Set.range f) hW (f u) ⟨u, rfl⟩
  rw [hfdef] at hb
  exact hb

end GlobalTheory.ConjRepBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDerivAt0CompLinearIff
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.PullbackSections
noncomputable section

namespace GlobalTheory.ThetaWitness

theorem isDerivAt0_comp_linear_iff {g g' : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (he : IsHolTo Set.univ e) (L : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (w : Fin g' → ℂ)
    (v : Sp (DualNumber ℂ) ⟶ X) : IsDerivAt0 (fun z => e (L z)) w v ↔ IsDerivAt0 e (L w) v := by
  have key : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 →
      ∀ (U : X.Opens) (_ : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)), fderiv ℂ (fun z => valAt' (e (L z)) U f) 0 w =
        fderiv ℂ (fun z => valAt' (e z) U f) 0 (L w) := by
    intro h0 U hU f
    have hmem : (0 : Fin g → ℂ) ∈ {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ e b ⁻¹ᵁ U} := by
      refine ⟨trivial, ?_⟩
      rw [← h0]
      intro x _
      exact hU (Set.mem_univ _)
    have hd : DifferentiableAt ℂ (fun z => valAt' (e z) U f) 0 :=
      ((he U f).2 0 hmem).differentiableAt ((he U f).1.mem_nhds hmem)
    let L' := LinearMap.toContinuousLinearMap L
    have hd' : HasFDerivAt (fun z => valAt' (e z) U f) (fderiv ℂ (fun z => valAt' (e z) U f) 0) (L' 0) := by
      rw [map_zero]; exact hd.hasFDerivAt
    have := (hd'.comp (0 : Fin g' → ℂ) L'.hasFDerivAt).fderiv
    exact DFunLike.congr_fun this w
  unfold IsDerivAt0
  simp only [map_zero]
  exact and_congr_right fun h0 => forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => by
    rw [key h0 U hU f]

theorem ex_eq_of_der {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} {t : SAB H S}
    {y₁ y₂ : Sp ℂ ⟶ S} (hy : y₁ = y₂) {D : Datum H} {g₁ g₂ : ℕ} {ty : Fin g₁ → (E →+* ℂ)}
    {P : D.La →+ (Fin g₁ → ℂ)} (hP : IsPeriod D ty P) {e₁ : (Fin g₁ → ℂ) → (Over.mk y₁ ⟶ t.G)}
    (he₁ : GlobalTheory.UnifPoint.IsExp e₁) (hk₁ : ∀ z, e₁ z = 1 ↔ z ∈ P.range)
    {e₂ : (Fin g₂ → ℂ) → (Over.mk y₂ ⟶ t.G)} (he₂ : GlobalTheory.UnifPoint.IsExp e₂) (hc₂ : {z | e₂ z = 1}.Countable)
    (L : (Fin g₁ → ℂ) ≃ₗ[ℂ] (Fin g₂ → ℂ))
    (huniq : ∀ w w' v, IsDerivAt0 (fun z => (e₁ z).left) w v → IsDerivAt0 (fun z => (e₁ z).left) w' v → w = w')
    (hb : ∀ a, ∃ v, IsDerivAt0 (fun z => (e₁ z).left) (Pi.single a 1) v ∧
      IsDerivAt0 (fun z => (e₂ z).left) (L (Pi.single a 1)) v) :
    ∀ z, (e₁ z).left = (e₂ (L z)).left := by
  subst hy
  have hL : Continuous L := L.toLinearMap.continuous_of_finiteDimensional
  have hLd : Differentiable ℂ L := (LinearMap.toContinuousLinearMap L.toLinearMap).differentiable
  have hhol : IsHolTo Set.univ (fun z => (e₂ (L z)).left) := fun U f => by
    obtain ⟨h1, h2⟩ := he₂.2.2.1 U f
    refine ⟨?_, ?_⟩
    · exact h1.preimage hL
    · refine h2.comp hLd.differentiableOn ?_
      intro z hz; exact ⟨trivial, hz.2⟩
  obtain ⟨h, hh⟩ := GlobalTheory.UnifPoint.exists_linearEquiv_of_period hP he₁ hk₁ (e₀ := fun z => e₂ (L z))
    (fun z w => by simp only [map_add (f := _)]; exact he₂.1 _ _) (he₂.2.1.comp L.surjective) hhol
    (by
      refine (hc₂.preimage_of_injOn L.injective.injOn).mono ?_
      intro z hz; exact hz)
  have hid : ∀ a, h (Pi.single a 1) = Pi.single a 1 := fun a => by
    obtain ⟨v, h1, h2⟩ := hb a
    have d2 := (isDerivAt0_comp_linear_iff _ he₂.2.2.1 L.toLinearMap _ v).2 h2
    have d3 : IsDerivAt0 (fun z => (e₁ (h z)).left) (Pi.single a 1) v := by
      convert d2 using 2 with z
      rw [hh]; rfl
    have d4 := (isDerivAt0_comp_linear_iff _ he₁.2.2.1 h.toLinearMap _ v).1 d3
    exact huniq _ _ v d4 h1
  have hlin : h.toLinearMap = LinearMap.id :=
    LinearMap.pi_ext' fun a => LinearMap.ext_ring (by simpa using hid a)
  have hid' : ∀ z, h z = z := fun z => LinearMap.congr_fun hlin z
  intro z
  rw [← hh z, hid']

end GlobalTheory.ThetaWitness

namespace GlobalTheory.ThetaWitness

theorem theta_value_indep : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (W₁ W₂ : UnfAt U k x)
    (Y₁ : UnitAt W₁) (Y₂ : UnitAt W₂) (v : Fin r → E),
    Complex.exp (-(Real.pi / 2 * hermForm Y₁.Hm (fun j => perFr (U.X k) x.1 v (relab c σ (W₁.e j).1) (W₁.e j).2)
        (fun j => perFr (U.X k) x.1 v (relab c σ (W₁.e j).1) (W₁.e j).2))) *
        Y₁.θ (fun j => perFr (U.X k) x.1 v (relab c σ (W₁.e j).1) (W₁.e j).2) =
      Complex.exp (-(Real.pi / 2 * hermForm Y₂.Hm (fun j => perFr (U.X k) x.1 v (relab c σ (W₂.e j).1) (W₂.e j).2)
        (fun j => perFr (U.X k) x.1 v (relab c σ (W₂.e j).1) (W₂.e j).2))) *
        Y₂.θ (fun j => perFr (U.X k) x.1 v (relab c σ (W₂.e j).1) (W₂.e j).2) := by
  intro E _ _ _ H Dw l Xo c σ r U k x W₁ W₂ Y₁ Y₂ v
  let L : (Fin W₁.g → ℂ) ≃ₗ[ℂ] (Fin W₂.g → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ (W₂.e.trans W₁.e.symm)
  have hL : ∀ z j, L z j = z (W₁.e.symm (W₂.e j)) := fun z j => rfl
  have hLd : Differentiable ℂ L := (LinearMap.toContinuousLinearMap L.toLinearMap).differentiable
  have hp : (fun j => perFr (U.X k) x.1 v (relab c σ (W₂.e j).1) (W₂.e j).2) =
      L (fun j => perFr (U.X k) x.1 v (relab c σ (W₁.e j).1) (W₁.e j).2) := by
    funext j
    rw [hL]
    generalize hs : W₁.e (W₁.e.symm (W₂.e j)) = s
    rw [Equiv.apply_symm_apply] at hs
    subst hs; rfl
  rw [hp]
  generalize (fun j => perFr (U.X k) x.1 v (relab c σ (W₁.e j).1) (W₁.e j).2) = z

  have hPL : ∀ a, L (W₁.Pm a) = W₂.Pm ((W₂.φ k).symm (W₁.φ k a)) := fun a => by
    funext j
    rw [hL, W₁.pm_eq, W₂.pm_eq, LinearEquiv.apply_symm_apply]
    generalize hs : W₁.e (W₁.e.symm (W₂.e j)) = s
    rw [Equiv.apply_symm_apply] at hs
    subst hs; rfl
  have hEF : ∀ a b, (W₂.F.Di (W₂.ik k)).EF ((W₂.φ k).symm (W₁.φ k a)) ((W₂.φ k).symm (W₁.φ k b)) =
      (W₁.F.Di (W₁.ik k)).EF a b := fun a b => by
    have h1 := W₂.isom k ((W₂.φ k).symm (W₁.φ k a)) ((W₂.φ k).symm (W₁.φ k b))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, ← W₁.isom k a b] at h1
    exact_mod_cast h1

  have hspan : Submodule.span ℝ (Set.range W₁.Pm) = ⊤ := W₁.per.2.2.2.1
  have hHH : ∀ z w, hermForm Y₂.Hm (L z) (L w) = hermForm Y₁.Hm z w := fun z w => by
    have := GlobalTheory.KeyFam.SamePeriod.hermForm_eq_of_im Y₂.Hm L.toLinearMap Y₁.Hm LinearMap.id hspan (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      simp only [LinearEquiv.coe_coe, LinearMap.id_coe, id_eq]
      rw [hPL, hPL, Y₂.c1, Y₁.c1, hEF]) z w
    simpa using this

  have hexp : ∀ W : UnfAt U k x, GlobalTheory.UnifPoint.IsExp (W.F.ex (W.ik k) W.Pm) := fun W =>
    ⟨W.F.ex_add _ _ W.per, W.F.ex_onto _ _ W.per, GlobalTheory.ClassUniq.isHolTo_ex W.F _ _ W.per,
      (W.F.ex_diff _ _ W.per).1, (W.F.ex_diff _ _ W.per).2⟩
  have hLs : ∀ a, L (Pi.single a 1) = Pi.single (W₂.e.symm (W₁.e a)) 1 := fun a => by
    funext j
    rw [hL]
    simp only [Pi.single_apply]
    exact if_congr (by rw [Equiv.symm_apply_eq, Equiv.eq_symm_apply]) rfl rfl
  have hex : ∀ z, (W₁.F.ex (W₁.ik k) W₁.Pm z).left = (W₂.F.ex (W₂.ik k) W₂.Pm (L z)).left :=
    ex_eq_of_der (t := Xo.univ.t) (W₁.pt.symm.trans W₂.pt) W₁.per (hexp W₁) (W₁.F.ex_ker _ _ W₁.per) (hexp W₂)
      ((GlobalTheory.UnifPoint.countable_periods W₂.per).mono fun z hz => (W₂.F.ex_ker _ _ W₂.per z).1 hz) L
      (fun w w' v h h' => by
        have tn := GlobalTheory.isDerivAt0_ex_isTanAt _ _ _ _ Xo _ _ _ W₁.F (W₁.ik k) W₁.Pm W₁.per
        exact (tn.2.2 v (tn.1 w v h)).unique h h')
      (fun a => ⟨(U.un k x).u (W₁.e a).1 (W₁.e a).2, by simpa using W₁.der (W₁.e a).1 (W₁.e a).2, by
        rw [hLs]; simpa using W₂.der (W₁.e a).1 (W₁.e a).2⟩)

  have hper1 : ∀ a ∈ W₁.Pm.range, ∀ z, W₁.F.ex (W₁.ik k) W₁.Pm (z + a) = W₁.F.ex (W₁.ik k) W₁.Pm z :=
    fun a ha z => by
      rw [W₁.F.ex_add _ _ W₁.per, (W₁.F.ex_ker _ _ W₁.per a).2 ha]
      exact @_root_.mul_one _ (CategoryTheory.Hom.monoid).toMulOneClass _
  have hcov : ∀ z, ∃ j, ⊤ ≤ (W₁.F.ex (W₁.ik k) W₁.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z =>
    GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB _
  have tr : ∀ j z, ⊤ ≤ (W₁.F.ex (W₁.ik k) W₁.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      ⊤ ≤ (W₂.F.ex (W₂.ik k) W₂.Pm (L z)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun j z hz => by rw [← hex]; exact hz
  have hspan' : Submodule.span ℝ (W₁.Pm.range : Set (Fin W₁.g → ℂ)) = ⊤ := by
    rw [AddMonoidHom.coe_range]; exact hspan
  have hfr : ∀ j z, ⊤ ≤ (W₁.F.ex (W₁.ik k) W₁.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → Y₂.fr j (L z) = Y₁.fr j z :=
    GlobalTheory.UnitFrameGen.frames_eq W₁.Pm.range hspan' (fun j => {z | ⊤ ≤ (W₁.F.ex (W₁.ik k) W₁.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
      (fun j => GlobalTheory.FamilyUnif_isOpen_ex W₁.F _ _ W₁.per _) hcov
      (fun j a ha z hz => by rw [Set.mem_setOf_eq, hper1 a ha]; exact hz)
      Y₁.fr (fun j z => Y₂.fr j (L z))
      (fun j j' z => valAt' (W₁.F.ex (W₁.ik k) W₁.Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val)
      (fun a z => Real.exp (Real.pi * (hermForm Y₁.Hm z a).re + Real.pi / 2 * (hermForm Y₁.Hm a a).re))
      Y₁.c2 (fun j => (Y₂.c2 j).comp hLd.differentiableOn fun z hz => tr j z hz) Y₁.c3
      (fun j j' z h1 h2 => Y₁.c4 j j' z ((GlobalTheory.top_le_preimage_inf _ _ _).2 ⟨h1, h2⟩))
      (fun j j' z h1 h2 => by
        have e2 := Y₂.c4 j j' (L z) ((GlobalTheory.top_le_preimage_inf _ _ _).2 ⟨tr _ _ h1, tr _ _ h2⟩)
        rw [← hex] at e2
        exact e2)
      (fun j hz => by
        have t0 := tr j 0 hz
        simp only [map_zero] at t0 ⊢
        rw [Y₁.c5 j hz, Y₂.c5 j t0])
      (by
        rintro j _ ⟨a, rfl⟩ z hz
        exact GlobalTheory.UnitFrameGen.norm_factor Y₁.Hm _ _ _ _ _ (Y₁.c6 a j z).1 ((Y₁.c6 a j z).2 hz))
      (by
        rintro j _ ⟨a, rfl⟩ z hz
        have := GlobalTheory.UnitFrameGen.norm_factor Y₂.Hm _ _ _ _ _ (Y₂.c6 ((W₂.φ k).symm (W₁.φ k a)) j (L z)).1
          ((Y₂.c6 ((W₂.φ k).symm (W₁.φ k a)) j (L z)).2 (tr j z hz))
        rw [← hPL, hHH, hHH, ← map_add (f := _)] at this
        exact this)

  have hθ : Y₂.θ (L z) = Y₁.θ z := by
    obtain ⟨j, hj⟩ := hcov z
    have hw0 : (W₁.F.ex (W₁.ik k) W₁.Pm z).left ≫ Xo.univ.t.G.hom = (U.un k x).x :=
      (Over.w (W₁.F.ex (W₁.ik k) W₁.Pm z)).trans W₁.pt.symm
    let p : Over.mk (U.un k x).x ⟶ Xo.univ.t.G := Over.homMk (W₁.F.ex (W₁.ik k) W₁.Pm z).left hw0
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) p)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) p)
    have v1 := Y₁.c7 j z _ e1 e2 hj
    have v2 := Y₂.c7 j (L z) _ (e1.trans (hex z)) e2 (tr j z hj)
    rw [hfr j z hj] at v2
    exact mul_right_cancel₀ (Y₁.c3 j z hj) (v2.symm.trans v1)
  rw [hHH, hθ]

end GlobalTheory.ThetaWitness
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualBesselCoreVertexLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSelfDual_besselCoreVertexLattice : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Frames G), Std F → ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m), IsSelfDualC (F.V₀ ρ) (lat0 F ρ h) := by
  first | exact @GlobalTheory.AscFin.isSelfDualC_lat0 | exact GlobalTheory.AscFin.isSelfDualC_lat0 | (intros; apply GlobalTheory.AscFin.isSelfDualC_lat0 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KeepsLatticeAtPlaceOfIntegralLocalBasisConjugateStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keepsLatticeAtPlace_of_integral_localBasisConjugates : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (π₁ π₂ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
  (∀ z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
      (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
        v.adicCompletionIntegers F) ∧
      (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
        v.adicCompletionIntegers F)) →
  ∀ A : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (∀ i j, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (A).map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) → (∀ i j, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (A).map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) := by
  first | exact @GlobalTheory.KeepInt.keepLat | exact GlobalTheory.KeepInt.keepLat | (intros; apply GlobalTheory.KeepInt.keepLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LamF
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl.Jet

open Complex

variable {D : D7}

def fmR {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z : VCx D.what₂.Tau S.rank T.rank) :
    GlobalTheory.FockCompare.RW T S :=
  fun τ => fockMat A B τ (z τ)

def omF {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z e : VCx D.what₂.Tau S.rank T.rank) : ℝ :=
  GlobalTheory.OrientedHeis.omO S T (fmR A B z) (fmR A B e)

def gD {ι : Type} [Fintype ι] {a b : ℕ} (c : ι → ℝ) (z e : VCx ι a b) : ℝ :=
  2 * ∑ τ, ∑ i, ∑ j, c τ * (z τ i j * conj (e τ i j)).re

def lamF {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (z : VCx D.what₂.Tau S.rank T.rank) : ℂ :=
  (1 / 2 : ℂ) * (-((Real.pi : ℂ) * I) * (omF A B z (Formalism.L2.Ker.coordX l) : ℂ)
    - (Real.pi : ℂ) * (omF A B z (I • Formalism.L2.Ker.coordX l) : ℂ)
    - (1 / 2 : ℂ) * (gD (fw D) z (Formalism.L2.Ker.coordX l) : ℂ)
    + (I / 2) * (gD (fw D) z (I • Formalism.L2.Ker.coordX l) : ℂ))

def crOp {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (Φ : VCx D.what₂.Tau S.rank T.rank → ℂ) (z : VCx D.what₂.Tau S.rank T.rank) : ℂ :=
  lamF A B l z * Φ z + (1 / 2 : ℂ) *
    (fderiv ℝ Φ z (Formalism.L2.Ker.coordX l) - I * fderiv ℝ Φ z (I • Formalism.L2.Ker.coordX l))

end GlobalTheory.FockTransl.Jet

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieDividedHomTangentImageBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLieImg IsLinHom IsThGen IsHeckeIsog)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeLieBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem epsMul_comp_epsMul {R : Type} [CommRing R] (a b : R) :
    (epsMul a).comp (epsMul b) = epsMul (a * b) :=
  RingHom.ext fun z => by
    ext <;> simp [epsMul, mul_smul]

theorem epsMul_one' {R : Type} [CommRing R] : epsMul (1 : R) = RingHom.id _ :=
  RingHom.ext fun z => by
    ext <;> simp [epsMul]

theorem spMap_epsMul_cancel {R : Type} [CommRing R] {u : R} (hu : IsUnit u) {Z : Scheme.{0}}
    {f g : Sp (DualNumber R) ⟶ Z} (h : spMap (epsMul u) ≫ f = spMap (epsMul u) ≫ g) : f = g := by
  obtain ⟨u, rfl⟩ := hu
  have e : spMap (epsMul ((u⁻¹ : Rˣ) : R)) ≫ spMap (epsMul (u : R)) = 𝟙 _ := by
    rw [GlobalTheory.Frames.ChgBC.spMap_comp_ring, epsMul_comp_epsMul, Units.inv_mul, epsMul_one',
      GlobalTheory.Frames.ChgBC.spMap_id]
  calc f = spMap (epsMul ((u⁻¹ : Rˣ) : R)) ≫ spMap (epsMul (u : R)) ≫ f := by
        rw [← Category.assoc, e, Category.id_comp]
    _ = g := by rw [h, ← Category.assoc, e, Category.id_comp]

end GlobalTheory.HeckeLieBC

namespace GlobalTheory.HeckeLieBC

open GlobalTheory.HeckeFrCompare (toFib_fst toFib_snd)

theorem lieImg_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (T Ω : Type) [CommRing T] [CommRing Ω] (χ : T →+* Ω) (x x' : Sp T ⟶ Xo.X)
    (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ : Gx x ⟶ Gx x') (Ψ₁ : Gx x₁ ⟶ Gx x₁') (p : ℕ)
    (v w : Sp (DualNumber T) ⟶ Xo.univ.t.G.left) (w₁ : Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left),
    IsUnit (p : Ω) → IsFib χ Ψ Ψ₁ → IsLieImg p Ψ v w → IsLieImg p Ψ₁ (spMap (dualMap χ) ≫ v) w₁ →
      w₁ = spMap (dualMap χ) ≫ w := by
  intro E _ _ _ H Dw l Xo T Ω _ _ χ x x' x₁ x₁' Ψ Ψ₁ p v w w₁ hp hF hL hL₁
  obtain ⟨pm, pm', hc, hc', hcomm, -⟩ := hF
  obtain ⟨-, -, a, ha, hw⟩ := hL
  obtain ⟨-, -, a₁, ha₁, hw₁⟩ := hL₁

  have hfib : GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.toFib x₁ (spMap (algebraMap Ω (DualNumber Ω))) a₁ ≫ pm =
      spMap (dualMap χ) ≫ GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.toFib x (spMap (algebraMap T (DualNumber T))) a := by
    apply GlobalTheory.Frames.ChgBC.gx_ext
    · rw [Category.assoc, hc.2.1, toFib_snd, Category.assoc, toFib_snd, ha₁, ha]
    · rw [Category.assoc, hc.2.2, GlobalTheory.HeckeFrCompare.toFib_fst_assoc, Category.assoc, toFib_fst,
        GlobalTheory.Frames.ChgBC.spMap_comp_ring, GlobalTheory.Frames.ChgBC.spMap_comp_ring, GlobalTheory.Frames.ChgBC.dualMap_alg]
  have hpush : GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.push Ψ₁ (spMap (algebraMap Ω (DualNumber Ω))) a₁ =
      spMap (dualMap χ) ≫ GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.push Ψ (spMap (algebraMap T (DualNumber T))) a := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.push
    rw [← hc'.2.1, reassoc_of% hcomm, reassoc_of% hfib]
  apply spMap_epsMul_cancel hp
  rw [hw₁, hpush, ← hw, ← Category.assoc, ← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring,
    GlobalTheory.Frames.ChgBC.spMap_comp_ring, GlobalTheory.Frames.ChgBC.dualMap_eps, map_natCast]

end GlobalTheory.HeckeLieBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SetIntegralPreimageEqZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setIntegral_preimage_eq_zero_of_fourier_eq_zero : ∀ (Y : Type) [MeasurableSpace Y] (m : Measure Y) (F : Y → ℂ), Integrable F m → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (p : Y → E), Measurable p → (∀ l : E →L[ℝ] ℝ, ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * F y ∂m = 0) → ∀ s : Set E, MeasurableSet s → ∫ y in p ⁻¹' s, F y ∂m = 0 := by
  first | exact @GlobalTheory.FourierPush.setIntegral_preimage_eq_zero | exact GlobalTheory.FourierPush.setIntegral_preimage_eq_zero | (intros; apply GlobalTheory.FourierPush.setIntegral_preimage_eq_zero <;> assumption)
end

