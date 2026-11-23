module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralTsumOfFactor
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0278
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1032
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0276
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPart

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarInnerProductFormulaUnitCoefficient
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace

open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.UnitCoefIP

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
theorem exists_scalar : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R →
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (μ' η' : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (H : HMod (Bridge.Gf (Vc D i) → c.W)),
  GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io →
  IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) →
  Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y →
  H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) →
  ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, (∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) →
  ∀ ev : Pl D.host.E → List ℤ → ℂ, ∃ C : ℂ, ∀ y₁ ∈ GlobalTheory.LiftLower.partH R i σ ev, ∀ (y₂ : (R.HW i σ).H) (w : c.W), ‖w‖ = 1 →
    GlobalTheory.AdelicScalar.l2 (R.νV i A.μ0) (R.fdV i A.μ0) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e y₁ fun ρ => v ρ)) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e y₂ fun ρ => v ρ)) = C * inner ℂ y₁ y₂ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F _hirr _hS hI hFo hZ hδ i σ s m μ' η' ω B f₀ f c io H hd hν _hy _hH v hv ev
  have hC := hd.1
  obtain ⟨⟨μ, 𝓧⟩, hμ⟩ := hd.2.2.2.2.2.2.2.1.1.2.norm.1
  obtain ⟨⟨Fr, hFr⟩, hFr2⟩ := (hC.models.νW i).1.2.2 R.θ hC.models.inf
  obtain ⟨mR, hmR⟩ := (hFr2 Fr hFr).1
  choose δ _hδpos hδ' using hδ i σ
  have hδv : ∀ ρ, ∫ b, ‖⟪((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ),
      (R.MW i σ).rep ρ (realMat (Wc D i) Fr ρ b) ((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ‖ ^ 2 ∂(mR ρ) = δ ρ :=
    fun ρ => (hδ' ρ Fr hFr (mR ρ) (hmR ρ) (v ρ) (hv ρ)).2
  have hW := GlobalTheory.LiftScalarL.inner_HW R hC.models.HW i σ
  set N : ℝ := ∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℝ) with hN
  have hN0 : (N : ℂ) ≠ 0 := by
    have : 0 < N := Finset.prod_pos fun ρ _ => by
      have := one_le_dimK i σ ρ
      positivity
    exact_mod_cast this.ne'
  by_cases h0 : typePart R i σ A.μ0 R.triv ev = ⊥
  · refine ⟨0, fun y₁ hy₁ y₂ w _ => ?_⟩
    have e1 : y₁ = 0 := by
      rw [← GlobalTheory.LiftLower.typePart_base hC.lev, h0] at hy₁
      exact (Submodule.mem_bot ℂ).1 hy₁
    subst e1
    simp [l2, Lift.pet, upLift, petW]
  · obtain ⟨Bf, -, -, -, hK⟩ := hZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd μ 𝓧 hμ ev h0
    refine ⟨(((R.νV i A.μ0) (R.fdV i A.μ0)).toReal : ℂ) * (Formalism.E.fock (deltaAtEmb D i σ) (deltaAtEmb D i σ) * (∏ ρ, (δ ρ : ℂ)) *
      ((Nat.card R.triv.H : ℂ) * (Datum.nrm2 μ 𝓧 f : ℂ) *
        (GlobalTheory.LFun.LSD D (finS R A.μ0) Bf μ' ((1 + (D.R.t : ℂ)) / 2) / (dOff D (finS R A.μ0) : ℂ)))) / N,
      fun y₁ hy₁ y₂ w hw => ?_⟩
    have hm : ∀ x, (R.HW i σ).e x ∈ R.Wall i σ := HMod_mem (hC.models.HW i σ)
    have hw' : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw]; simp
    have hy' : y₁ ∈ typePart R i σ A.μ0 R.triv ev := by
      rw [GlobalTheory.LiftLower.typePart_base hC.lev]; exact hy₁
    have hK1 := hK _ (Submodule.mem_comap.1 hy') _ (hm y₂)
    have hIP := isMultiplicityInner_of_model (R.HW i σ) hW y₁ y₂
    have key := GlobalTheory.LiftScalarL.l2_upwardLift R hI hFo hd hν hμ hFr hmR (hm y₁) (hm y₂) hIP _ hK1 v δ hδv w hw'
    refine key.trans ?_
    rw [hW y₁ y₂]
    field_simp

end GlobalTheory.UnitCoefIP

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSmoothVectorNeZeroOfDiscreteSeriesHom
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SmoothAvg

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {H : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : GA D V →* (H →L[ℂ] H)}


open Classical in
theorem norm_apply_eq (hπ : IsUnitaryRep π) {Ψ : ContinuousMultilinearMap ℂ M.H H} (hΨ : Ψ ∈ homDS M π ⊤)
    (y : ∀ τ, M.H τ) : ‖Ψ y‖ = ‖Ψ (fun τ => unitVec (H := M.H τ))‖ * ∏ τ, ‖y τ‖ := by
  have h := inner_eq_bePi (isIrrUnitary_dsRep M) hπ hΨ hΨ y y
  rw [bePi] at h
  simp only [inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖Ψ y‖ ^ 2 = (‖Ψ (fun τ => unitVec (H := M.H τ))‖ * ∏ τ, ‖y τ‖) ^ 2 := by
    rw [mul_pow, ← Finset.prod_pow]
    exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)) two_ne_zero).1 h2


open Classical in
theorem isClosed_homDS : IsClosed (homDS M π ⊤ : Set (ContinuousMultilinearMap ℂ M.H H)) := by
  refine isClosed_of_closure_subset fun Φ hΦ => ⟨fun _ => trivial, fun i g y => ?_⟩
  have hc : IsClosed {Ψ : ContinuousMultilinearMap ℂ M.H H |
      Ψ (Function.update y i (dsRep M i g (y i))) = π (embW V (placeOf D i) g) (Ψ y)} :=
    isClosed_eq (continuous_eval_const _) ((π _).continuous.comp (continuous_eval_const _))
  exact closure_minimal (fun Ψ (hΨ : Ψ ∈ homDS M π ⊤) => hΨ.2 i g y) hc hΦ

end GlobalTheory.SmoothAvg

namespace GlobalTheory.SmoothAvg

theorem nonarchimedeanGroup_GfC (D : D7) (V : HSp D) : NonarchimedeanGroup (GfC V) :=
  haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GFin D.sp.cm.sig V.gram
  NonarchimedeanGroup.nonarchimedean_of_emb (finPtsEquiv D.sp.cm.sig V.gram).toMonoidHom
    (finPtsEquiv D.sp.cm.sig V.gram).toHomeomorph.isOpenEmbedding

theorem exists_smooth_ne_zero : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsUnitaryRep π → ∀ (hU : IsSubrep π ⊤) (Φ : homDS M π ⊤), Φ ≠ 0 → ∃ Ψ ∈ GlobalTheory.PRep.smoothPart (finPartDS M hU), Ψ ≠ 0 := by
  intro D V S M H _ _ _ π hπ hU Φ hΦ
  let u : ∀ τ, M.H τ := fun τ => unitVec (H := M.H τ)
  let f : homDS M π ⊤ →L[ℂ] H :=
    (ContinuousMultilinearMap.apply ℂ M.H H u).comp (homDS M π ⊤).subtypeL
  have hnorm : ∀ Ψ : homDS M π ⊤, ‖Ψ‖ ≤ ‖f Ψ‖ := fun Ψ => by
    refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun y => ?_
    exact (norm_apply_eq hπ Ψ.2 y).le
  have hinj : Function.Injective f := fun a b h => by
    have h0 : ‖a - b‖ ≤ 0 := by simpa [map_sub, h] using hnorm (a - b)
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)
  haveI : CompleteSpace (homDS M π ⊤) := (isClosed_homDS (π := π)).completeSpace_coe
  have hclosed : IsClosed (Set.range f) :=
    (f.antilipschitz_of_bound (K := 1) fun x => by simpa using hnorm x).isClosed_range f.uniformContinuous
  have hequiv : ∀ (g : GfC V) (Ψ : homDS M π ⊤), f (finPartDS M hU g Ψ) = π g (f Ψ) := fun g Ψ => rfl
  have hv : f Φ ≠ 0 := fun h => hΦ (hinj (by rw [h, map_zero]))
  haveI := nonarchimedeanGroup_GfC D V
  have hcont : Continuous fun g : GfC V => π g (f Φ) := (hπ.continuous_apply _).comp continuous_subtype_val
  have hN : {g : GfC V | dist (π g (f Φ)) (f Φ) < ‖f Φ‖ / 2} ∈ nhds (1 : GfC V) :=
    (isOpen_lt (hcont.dist continuous_const) continuous_const).mem_nhds (by simp [norm_pos_iff.2 hv])
  obtain ⟨K, hK⟩ := NonarchimedeanGroup.is_nonarchimedean _ hN
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  let O : Set H := Set.range fun k : K => π ((k : GfC V) : GA D V) (f Φ)
  let C : Set H := closure (convexHull ℝ O)
  have hCconv : Convex ℝ C := (convex_convexHull ℝ O).closure
  have hvO : f Φ ∈ O := ⟨1, by simp⟩
  have hCne : C.Nonempty := ⟨f Φ, subset_closure (subset_convexHull ℝ O hvO)⟩
  obtain ⟨w, hwC, hw⟩ := exists_norm_eq_iInf_of_complete_convex hCne isClosed_closure.isComplete hCconv 0
  have hmin : ∀ x ∈ C, ‖w‖ ≤ ‖x‖ := fun x hx => by
    have h1 := ciInf_le (f := fun z : C => ‖0 - (z : H)‖)
      ⟨0, by rintro _ ⟨z, rfl⟩; exact norm_nonneg _⟩ ⟨x, hx⟩
    rw [← hw] at h1
    simpa using h1
  have hball : C ⊆ Metric.closedBall (f Φ) (‖f Φ‖ / 2) :=
    closure_minimal (convexHull_min (by rintro _ ⟨k, rfl⟩; exact Metric.mem_closedBall.2 (hK k.2).le)
      (convex_closedBall _ _)) Metric.isClosed_closedBall
  have hw0 : w ≠ 0 := by
    rintro rfl
    have h1 := Metric.mem_closedBall.1 (hball hwC)
    rw [dist_zero_left] at h1
    exact hv (norm_le_zero_iff.1 (by linarith))
  have hRconv : Convex ℝ (Set.range f) := by
    have h1 := ((LinearMap.range (f : homDS M π ⊤ →ₗ[ℂ] H)).restrictScalars ℝ).convex
    rw [Submodule.coe_restrictScalars, LinearMap.coe_range, ContinuousLinearMap.coe_coe] at h1
    exact h1
  have hOR : O ⊆ Set.range f := by
    rintro _ ⟨k, rfl⟩
    exact ⟨finPartDS M hU k Φ, hequiv _ _⟩
  obtain ⟨Ψ, hΨ⟩ : w ∈ Set.range f := closure_minimal (convexHull_min hOR hRconv) hclosed hwC
  have hinv : ∀ k : K, π ((k : GfC V) : GA D V) w = w := by
    intro k
    let T : H →L[ℝ] H := (π ((k : GfC V) : GA D V)).restrictScalars ℝ
    have hTO : T '' O ⊆ O := by
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      refine ⟨k * j, ?_⟩
      simp [T]
    have hTC : T '' C ⊆ C := by
      refine (image_closure_subset_closure_image T.continuous).trans (closure_mono ?_)
      exact (T.toLinearMap.image_convexHull O).trans_subset (convexHull_mono hTO)
    have hx : π ((k : GfC V) : GA D V) w ∈ C := hTC ⟨w, hwC, rfl⟩
    have hn : ‖π ((k : GfC V) : GA D V) w‖ = ‖w‖ := hπ.norm_apply _ _
    have hmid : (1 / 2 : ℝ) • (w + π ((k : GfC V) : GA D V) w) ∈ C := by
      have h1 := hCconv hwC hx (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simpa [smul_add] using h1
    have h1 := hmin _ hmid
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h1
    have hp := parallelogram_law_with_norm ℂ w (π ((k : GfC V) : GA D V) w)
    rw [hn] at hp
    have h2 : ‖w - π ((k : GfC V) : GA D V) w‖ ^ 2 ≤ 0 := by
      nlinarith [norm_nonneg w, norm_nonneg (w + π ((k : GfC V) : GA D V) w)]
    have h3 : ‖w - π ((k : GfC V) : GA D V) w‖ = 0 := by nlinarith [norm_nonneg (w - π ((k : GfC V) : GA D V) w)]
    exact (sub_eq_zero.1 (norm_eq_zero.1 h3)).symm
  refine ⟨Ψ, GlobalTheory.SmGL.mem_smoothPart_of_nhds (Filter.mem_of_superset (K.isOpen.mem_nhds K.one_mem) fun g hg => ?_),
    fun h => hw0 (by rw [← hΨ, h, map_zero])⟩
  exact hinj (by rw [hequiv, hΨ]; exact hinv ⟨g, hg⟩)

end GlobalTheory.SmoothAvg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSymplecticLieEqExpOneParam
section
open scoped Matrix

noncomputable section

namespace GlobalTheory.SymplecticOneParam

variable {l : Type} [Fintype l] [DecidableEq l]

theorem eq_exp_of_continuous_oneParameter (g : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ) (hc : Continuous g)
    (h0 : g 0 = 1) (hadd : ∀ s t, g (s + t) = g s * g t) :
    HasDerivAt g (deriv g 0) 0 ∧ ∀ t : ℝ, g t = NormedSpace.exp (t • deriv g 0) := by
  letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (l ⊕ l) (l ⊕ l) ℝ) := FiniteDimensional.complete ℝ _
  have hsm := GlobalTheory.contDiff_of_continuous_oneParameter (Matrix (l ⊕ l) (l ⊕ l) ℝ) g hc h0 hadd
  have hdiff : Differentiable ℝ g := hsm.differentiable (by simp)
  set Z := deriv g 0 with hZ
  have hd0 : HasDerivAt g Z 0 := (hdiff 0).hasDerivAt
  have hdt : ∀ t, HasDerivAt g (g t * Z) t := by
    intro t
    have h1 : HasDerivAt (fun s => g (s - t)) Z t := by
      have h := hd0
      rw [← sub_self t] at h
      exact h.comp_sub_const t t
    have h2 := h1.const_mul (g t)
    have h3 : (fun s => g t * g (s - t)) = g := by
      funext s; rw [← hadd, add_sub_cancel]
    rwa [h3] at h2
  refine ⟨hd0, fun t => ?_⟩
  set h : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ := fun s => g s * NormedSpace.exp (s • (-Z)) with hh
  have hderh : ∀ s, HasDerivAt h 0 s := by
    intro s
    have he := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-Z) s
    have := (hdt s).fun_mul he
    have key : g s * Z * NormedSpace.exp (s • -Z) + g s * (-Z * NormedSpace.exp (s • -Z)) = 0 := by
      rw [neg_mul, mul_neg, mul_assoc, add_neg_cancel]
    exact this.congr_deriv key
  have hconst : h t = h 0 := is_const_of_deriv_eq_zero (fun s => (hderh s).differentiableAt)
    (fun s => (hderh s).deriv) t 0
  have hh0 : h 0 = 1 := by simp [hh, h0]
  have hinv : NormedSpace.exp (t • (-Z)) * NormedSpace.exp (t • Z) = 1 := by
    rw [smul_neg, ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_left, neg_add_cancel,
      NormedSpace.exp_zero]
  calc g t = g t * (NormedSpace.exp (t • (-Z)) * NormedSpace.exp (t • Z)) := by rw [hinv, mul_one]
    _ = h t * NormedSpace.exp (t • Z) := by rw [hh, mul_assoc]
    _ = NormedSpace.exp (t • Z) := by rw [hconst, hh0, one_mul]

theorem exists_mem_sp_eq_exp : ∀ (l : Type) [Fintype l] [DecidableEq l] (g : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ),
    Continuous g → g 0 = 1 →
    (∀ s t, g (s + t) = g s * g t) → (∀ t, g t ∈ Matrix.symplecticGroup l ℝ) →
    ∃ Z ∈ LieAlgebra.Symplectic.sp l ℝ, ∀ t : ℝ, g t = NormedSpace.exp (t • Z) := by
  intro l _ _ g hc h0 hadd hsym
  obtain ⟨hd, hexp⟩ := eq_exp_of_continuous_oneParameter g hc h0 hadd
  refine ⟨deriv g 0, ?_, hexp⟩
  set Z := deriv g 0 with hZ
  letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra
  let T : Matrix (l ⊕ l) (l ⊕ l) ℝ →L[ℝ] Matrix (l ⊕ l) (l ⊕ l) ℝ :=
    LinearMap.toContinuousLinearMap (Matrix.transposeLinearEquiv (l ⊕ l) (l ⊕ l) ℝ ℝ).toLinearMap
  have hT : HasDerivAt (fun t => (g t)ᵀ) Zᵀ 0 := T.hasFDerivAt.comp_hasDerivAt 0 hd
  have hF := (hT.mul_const (Matrix.J l ℝ)).fun_mul hd
  have hconst : (fun t => (g t)ᵀ * Matrix.J l ℝ * g t) = fun _ => Matrix.J l ℝ := by
    funext t
    have := SymplecticGroup.transpose_mem (hsym t)
    rw [SymplecticGroup.mem_iff, Matrix.transpose_transpose] at this
    exact this
  rw [hconst] at hF
  have huniq := hF.unique (hasDerivAt_const (0 : ℝ) (Matrix.J l ℝ))
  rw [h0, Matrix.transpose_one, mul_one, one_mul, add_eq_zero_iff_eq_neg] at huniq
  show Z ∈ skewAdjointMatricesLieSubalgebra (Matrix.J l ℝ)
  rw [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint,
    Matrix.IsAdjointPair, huniq, mul_neg]

end GlobalTheory.SymplecticOneParam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniquePureTensorRestrictedFamily
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PureTensorExists

theorem existsUnique_isPure : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ), IsRestricted ψ θ S T sS sT ΛS ΛT f₀ x → ∃! f, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC x hx
  classical
  have hstd : IsStdChar D ψ (-1) := GlobalTheory.PlaceTensor.base_std hB
  have hf0 : IsThetaFunO ψ S T f₀ := GlobalTheory.PlaceTensor.base_theta hB

  have build : ∀ (s : Finset (Place D)) (y : Place D → WO S T → ℂ),
      IsRestricted ψ θ S T sS sT ΛS ΛT f₀ y → (∀ p, y p ≠ f₀ → p ∈ s) →
        ∃ f, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ y f := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro y _ hy
      have hconst : y = fun _ => f₀ := by
        funext p
        by_contra hne
        exact absurd (hy p hne) (by simp)
      subst hconst
      exact ⟨f₀, (_root_.GlobalTheory.LocalPure.isPure_base_and_local D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC).1⟩
    · intro q s _ ih y hyR hy

      have hres : IsRestricted ψ θ S T sS sT ΛS ΛT f₀ (Function.update y q f₀) := by
        refine ⟨fun p => ?_, ?_⟩
        · by_cases hpq : p = q
          · subst hpq
            simpa using GlobalTheory.PlaceTensor.base_isLocal hB p
          · simpa [Function.update_apply, hpq] using hyR.1 p
        · refine hyR.2.subset fun p hp => ?_
          by_cases hpq : p = q
          · subst hpq
            simp at hp
          · simpa [Function.update_apply, hpq] using hp
      have hsub : ∀ p, Function.update y q f₀ p ≠ f₀ → p ∈ s := by
        intro p hp
        by_cases hpq : p = q
        · subst hpq
          simp at hp
        · have hp' : y p ≠ f₀ := by simpa [Function.update_apply, hpq] using hp
          rcases Finset.mem_insert.1 (hy p hp') with h | h
          · exact absurd h hpq
          · exact h
      obtain ⟨f, hf⟩ := ih (Function.update y q f₀) hres hsub
      obtain ⟨f', hf', -⟩ := _root_.GlobalTheory.PlaceTensorStep.change_factor D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC
        (Function.update y q f₀) y f q hf (by simp)
        (fun p hp => (Function.update_of_ne hp f₀ y).symm) (hyR.1 q)
      exact ⟨f', hf'⟩
  obtain ⟨f, hf⟩ := build hx.2.toFinset x hx (fun p hp => by simpa using hp)
  refine ⟨f, hf, fun g hg => ?_⟩

  obtain ⟨hHaar, hFD, -⟩ := id hC
  have hfT : IsThetaFunO ψ S T f := hf.2.1
  have hgT : IsThetaFunO ψ S T g := hg.2.1
  have hIP := _root_.GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hstd hC
  have hd : IsThetaFunO ψ S T (g - f) := GlobalTheory.WeilVacMove.isTheta_sub hgT hfT
  have hz : g - f = 0 := by
    refine GlobalTheory.HeisTotal.eq_zero_of_orthogonal_translates D ψ hstd S T f₀ (g - f) hf0
      (GlobalTheory.PlaceTensor.base_ne_zero hB) hd μ 𝓕 hHaar hFD fun w => ?_
    have hw : IsThetaFunO ψ S T (heisO ψ S T w f₀) :=
      (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hstd S T).1 w f₀ hf0
    have e1 : ipO μ 𝓕 g (heisO ψ S T w f₀) = ipO μ 𝓕 f (heisO ψ S T w f₀) := by
      rw [(hg.2.2 w).2, (hf.2.2 w).2]
    have e2 : ipO μ 𝓕 (heisO ψ S T w f₀) g = ipO μ 𝓕 (heisO ψ S T w f₀) f := by
      rw [(hIP g _ hgT hw).2.1, (hIP f _ hfT hw).2.1, e1]
    have e3 := ((hIP (g - f) _ hd hw).2.2.2.1 f hfT).2
    rw [sub_add_cancel] at e3
    have e4 : ipO μ 𝓕 (heisO ψ S T w f₀) (g - f) = 0 := by
      linear_combination e2 - e3
    exact e4
  exact sub_eq_zero.1 hz

end GlobalTheory.PureTensorExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExtendRestrictionFinitePointsEq
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdelicRestrict

theorem ext_restrict {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (Ψ : GA D V → c.W)
    (hΨ : ∀ γ ∈ GQ V, ∀ k, Lev.finE V k ∈ lev D.sp.cm V.gram β L → ∀ h,
      Ψ (γ * h * k) = Lev.levChi V β L k • c.ρ k⁻¹ (Ψ h)) (h : GA D V) :
    c.ext (fun u => Ψ (GlobalTheory.AdelicScalar.finLift V u)) h = Ψ h := by
  set h₀ := GlobalTheory.AdelicScalar.finLift V ((finHom V).rangeRestrict h) with eh₀
  have m₀ : h₀ ∈ GfC V := GlobalTheory.AdelicScalar.finLift_mem V _
  have s₀ : finHom V h₀ = finHom V h :=
    congrArg Subtype.val (GlobalTheory.AdelicScalar.finLift_spec V ((finHom V).rangeRestrict h))
  set k := h₀⁻¹ * h with ek
  have hk1 : finHom V k = 1 := by rw [ek, map_mul, map_inv, s₀, inv_mul_cancel]
  have hkE : Lev.finE V k = 1 := by
    unfold Lev.finE
    rw [MonoidHom.comp_apply, hk1, map_one]
  have hkL : Lev.finE V k ∈ lev D.sp.cm V.gram β L := by rw [hkE]; exact Subgroup.one_mem _
  have hχ : Lev.levChi V β L k = 1 := by
    unfold Lev.levChi
    rw [hkE]
    have := map_one (levChar D.sp.cm V.gram β L)
    have e : levFn β L 1 = (levChar D.sp.cm V.gram β L 1 : ℂˣ) := rfl
    rw [e, this]
    rfl
  have hlaw := hΨ 1 (Subgroup.one_mem _) k hkL h₀
  have eh : 1 * h₀ * k = h := by rw [ek, one_mul, mul_inv_cancel_left]
  rw [eh, hχ, one_smul] at hlaw
  change c.ρ h⁻¹ (Ψ (GlobalTheory.AdelicScalar.finLift V ((finHom V).rangeRestrict h))) = Ψ h
  rw [← eh₀, hlaw]
  have hρ : c.ρ h⁻¹ = c.ρ k⁻¹ := by
    rw [← eh, one_mul, _root_.mul_inv_rev, map_mul, hc.1 _ (inv_mem m₀), mul_one]
  rw [hρ]

end GlobalTheory.AdelicRestrict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartLocalToFiniteAdelicComponentNeStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePart_localToFiniteAdelic_component_ne : ∀ {D : D7} (V : HSp D) {v u : HeightOneSpectrum (𝓞 D.host.F)}, u ≠ v → ∀ (g : Gv V v), (Formalism.IndefR.Lev.finE V (locFin V v g : GA D V)).val.map (Formalism.UG.prV (E := D.host.E) u) = 1 := by
  first | exact @GlobalTheory.LocFinComp.finE_locFin_map_prV_ne | exact GlobalTheory.LocFinComp.finE_locFin_map_prV_ne | (intros; apply GlobalTheory.LocFinComp.finE_locFin_map_prV_ne <;> assumption)
end

