module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericLieMultiplicitiesUniformisedGroup
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelFamilyNearbyPeriodsSameComponent
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSiegelFamilyOverNumberField
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NotInjOnOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueIndependentNormalForm
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsEqCexpQuadraticOfEquivalentFactors
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0387
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0402
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0467
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0558
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0206

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedEtaleCompletion
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.CharRank

open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.Serre GlobalTheory.EigenSplit Matrix GlobalTheory.LieUnif
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts)
open scoped CategoryTheory.Obj

theorem trace_of_unif_loc {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    {D : DegData R (maximalIdeal R)} {P : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (maximalIdeal R) D P G) {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X] {oD : D.OAct O}
    {oP : P.OAct O} {aG : OAct O G} (hl : U.OLinear O oD oP aG.toRingAct) [IsCommMonObj D.toPre.P.A]
    [Smooth D.toPre.P.A.hom] {g h r : ℕ} {v : Fin g → (epsR R ⟶ G)} (hv : IsLieBasis v)
    {ρ : O →+* Module.End R (Fin g → R)} (hρ : ∀ a c, prodPts (ρ a c) v = prodPts c v ≫ aG.act a)
    {w : Fin h → (epsR R ⟶ D.toPre.P.A)} (hw : IsLieBasis w)
    {ρB : O →+* Module.End R (Fin h → R)}
    (hρB : ∀ a c, prodPts (ρB a c) w = prodPts c w ≫ (ofRingAct oD.onB.toRingAct).act a)
    (b : Module.Basis (Fin r) ℤ D.toPre.X) (a : O) :
    LinearMap.trace R _ (ρ a) = LinearMap.trace R _ (ρB a) + (latTrace b a : R) := by
  have key : ∀ e : ℕ, LinearMap.trace R _ (ρ a) - (LinearMap.trace R _ (ρB a) + (latTrace b a : R)) ∈
      maximalIdeal R ^ (e + 1) := fun e => by
    let f := Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))
    have : IsLocalRing (R ⧸ maximalIdeal R ^ (e + 1)) := by
      have : Nontrivial (R ⧸ maximalIdeal R ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 fun h =>
        (maximalIdeal.isMaximal R).ne_top (top_le_iff.1 (h.symm.le.trans (Ideal.pow_le_self (Nat.succ_ne_zero e))))
      exact IsLocalRing.of_surjective' f Ideal.Quotient.mk_surjective
    have := U.smooth
    obtain ⟨v', ρ', hv', hρ', hM⟩ := ToricRank.exists_action_pullback hv hρ f
    obtain ⟨w', ρB', hw', hρB', hMB⟩ := ToricRank.exists_action_pullback hw hρB f
    let gc := U.gt e
    have := gc.q_hom
    have := gc.i_hom
    have := gc.q_flat
    have := gc.q_surj
    have := gc.q_affine
    have := (H1.torus_dim (Sp (R ⧸ maximalIdeal R ^ (e + 1))) D.toPre.X).smooth
    have : Smooth gc.q.left := by
      refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
        ((H1.torsor_pullback gc.i gc.q gc.isKernel).map (Over.forget _)).flip
        ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact gc.q.left)⟩ ?_
      exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
    let aK := @Diag.diagAct (Sp (R ⧸ maximalIdeal R ^ (e + 1))) O _ D.toPre.X _ (Module.compHom _ (starRingEnd O))
    let MK : O → Matrix (Fin r) (Fin r) (R ⧸ maximalIdeal R ^ (e + 1)) := fun x =>
      (LinearMap.toMatrix b b (DistribSMul.toAddMonoidHom D.toPre.X (star x)).toIntLinearMap).map (Int.castRingHom _)
    have hvK := Diag.isLieBasis_dualBasis (R := R ⧸ maximalIdeal R ^ (e + 1)) b
    have hMK : ∀ x i, IsLieComb (MK x i) (fun i => Diag.lieVec (Diag.dualBasis _ b i))
        (Diag.lieVec (Diag.dualBasis _ b i) ≫ aK.act x) := fun x i =>
      Diag.isLieComb_comp_diagMap b b (DistribSMul.toAddMonoidHom D.toPre.X (star x)) i
    have hi : IsLinearHom aK (aG.pullback (thick R _ e) G) gc.i := ⟨inferInstance, fun x => by
      obtain ⟨t, ht, hi⟩ := hl.i_lin e x
      obtain rfl := ConstBasis.eq_diagMap (DistribSMul.toAddMonoidHom D.toPre.X (star x)) ht
      exact hi.symm⟩
    have h := trace_level (K := splitTorus (Sp (R ⧸ maximalIdeal R ^ (e + 1))) D.toPre.X) (aK := aK)
      (aG := aG.pullback (thick R _ e) G) (aB := (ofRingAct oD.onB.toRingAct).pullback (thick R _ e) _)
      (i := gc.i) (q := gc.q) hi ⟨inferInstance, hl.q_lin e⟩ gc.isKernel hvK hv' hw' a
      (MK a) ((LinearMap.toMatrix' (ρ a))ᵀ.map f) ((LinearMap.toMatrix' (ρB a))ᵀ.map f)
      (fun c => (ConstBasis.prodPts_act hvK hMK a c).symm) (fun c => by rw [← hM, hρ']) (fun c => by rw [← hMB, hρB'])
    rw [← Ideal.Quotient.eq, map_add (f := _), map_intCast, trace_map_eq, trace_map_eq, h]
    refine (add_comm _ _).trans (congrArg _ ?_)
    simp [MK, latTrace, Matrix.trace]
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top,
    Ideal.mem_iInf]
  intro n
  exact Ideal.pow_le_pow_right (Nat.le_succ n) (key n)

theorem lieMult_unif_loc {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R]
    [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (t : SAB H (Sp R))
    (P : PELUnif (maximalIdeal R) t) (F : Type) [Field F] [IsAlgClosed F] (f : R →+* F) (hf : Function.Injective f)
    (τ : 𝓞 E →+* F) (N : ℕ) (hN : LieMult t.act (spMap f) τ N) :
    letI := H.starRing; ∃ n, LieMult (ofRingAct P.oD.onB.toRingAct) (spMap f) τ n ∧
      n + Module.finrank (𝓞 E) P.D.toPre.X = N := by
  classical
  letI := H.starRing
  haveI : CharZero F := ⟨fun a b h => Nat.cast_injective (R := R) (hf (by simpa using h))⟩
  have := P.U.smooth
  have : Smooth P.D.toPre.P.A.hom := P.D.toPre.P.smoothDim.smooth
  obtain ⟨g, v, hv⟩ := Chart.exists_isLieBasis t.G P.U.smooth
  obtain ⟨ρ, hρ⟩ := LieEigen.exists_action hv t.act
  obtain ⟨h, w, hw⟩ := Chart.exists_isLieBasis P.D.toPre.P.A this
  obtain ⟨ρB, hρB⟩ := LieEigen.exists_action hw (ofRingAct P.oD.onB.toRingAct)
  let b := Module.finBasis ℤ P.D.toPre.X
  have htr := trace_of_unif_loc P.U.toUnifPre P.lin hv hρ hw hρB b
  obtain ⟨v', ρ', hv', hρ', hM⟩ := ToricRank.exists_action_pullback hv hρ f
  obtain ⟨w', ρB', hw', hρB', hMB⟩ := ToricRank.exists_action_pullback hw hρB f
  let aG := t.act.pullback (spMap f) t.G
  let aB := (ofRingAct P.oD.onB.toRingAct).pullback (spMap f) P.D.toPre.P.A
  haveI := Module.Finite.of_basis (Lie.basis aG hv')
  haveI := Module.Finite.of_basis (Lie.basis aB hw')
  have tG : ∀ a, LinearMap.trace F (Lie aG) (Module.toModuleEnd F (Lie aG) a) = f (LinearMap.trace R _ (ρ a)) :=
    fun a => by rw [trace_map_eq]; exact trace_lie hv' aG a _ (fun c => by rw [← hM, hρ'])
  have tB : ∀ a, LinearMap.trace F (Lie aB) (Module.toModuleEnd F (Lie aB) a) = f (LinearMap.trace R _ (ρB a)) :=
    fun a => by rw [trace_map_eq]; exact trace_lie hw' aB a _ (fun c => by rw [← hMB, hρB'])
  let σ : (E →+* F) → 𝓞 E →+* F := fun i => i.comp (algebraMap (𝓞 E) E)
  have hinj : Function.Injective σ := fun i j hij =>
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) hij
  have hσ : IsSplitting σ := by
    simpa using isSplitting_of_isDomain hinj (NumberField.Embeddings.card E F) (RingHom.id F)
      (isUnit_discr_of_charZero F)
  obtain ⟨j, rfl⟩ : ∃ j, σ j = τ :=
    ⟨IsFractionRing.lift (injective_of_charZero τ), RingHom.ext fun x => IsFractionRing.lift_algebraMap (injective_of_charZero τ) x⟩
  have : Module.Finite (𝓞 E) P.D.toPre.X := .of_restrictScalars_finite ℤ _ _
  have he : ∀ {X : Over (Sp F)} [GrpObj X] [IsCommMonObj X] (a : OAct (𝓞 E) X),
      Lie.eig a (σ j) = eigenSub (Module.toModuleEnd F (Lie a)) (σ j) := fun a =>
    Submodule.ext fun v => by rw [mem_eigenSub]; rfl
  have hm := mult_eq hinj (fun i => Module.finrank F (eigenSub (Module.toModuleEnd F (Lie aG)) (σ i)))
    (fun i => Module.finrank F (eigenSub (Module.toModuleEnd F (Lie aB)) (σ i)))
    (Module.finrank (𝓞 E) P.D.toPre.X) (fun a => by
      have hT := trace_eq_sum hσ (torusRep (𝓞 E) P.D.toPre.X F) a
      simp only [fun i => finrank_eigenSub_torusRep (X := P.D.toPre.X) (σ i) (injective_of_charZero _)] at hT
      rw [← trace_eq_sum hσ, ← trace_eq_sum hσ, ← hT, tG, tB, htr, trace_torusRep b, map_add (f := _), map_intCast]) j
  rw [Lie.lieMult_iff_finrank (isLinearPullback_pullback _ (spMap f)), he] at hN
  refine ⟨_, ?_, hm.symm.trans hN.2⟩
  rw [Lie.lieMult_iff_finrank (isLinearPullback_pullback _ (spMap f)), he]
  exact ⟨inferInstance, rfl⟩

theorem bar_rt_neg {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : H.bar H.rt = -H.rt := by
  have h1 : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
  refine (sq_eq_sq_iff_eq_or_eq_neg.mp h1).resolve_left fun h => ?_
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h2 : starRingEnd ℂ (φ (H.rt : E)) = φ (H.rt : E) := by
    rw [← IsCMField.complexEmbedding_complexConj, ← H.bar_eq, h]
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h2
  have h3 : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (φ.comp (algebraMap (𝓞 E) E)) H.rt_sq
    rw [map_pow, map_neg, map_natCast] at this
    exact this
  rw [hr] at h3
  have h4 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h3
  have h5 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg r]

theorem exists_chars {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [IsAlgClosed K] [CharZero K] (δ : K) (hδ : δ ^ 2 = -(H.d : K)) :
    ∃ τ₁ τ₂ : 𝓞 E →+* K, τ₁ H.rt = δ ∧ τ₂ H.rt ≠ δ := by
  let e₀ : E →ₐ[ℚ] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let τ₀ : 𝓞 E →+* K := e₀.toRingHom.comp (algebraMap (𝓞 E) E)
  let τ' : 𝓞 E →+* K := τ₀.comp (H.bar : 𝓞 E →+* 𝓞 E)
  have h' : τ' H.rt = -τ₀ H.rt := by
    change τ₀ (H.bar H.rt) = _
    rw [bar_rt_neg, map_neg]
  have h0 : (τ₀ H.rt) ^ 2 = δ ^ 2 := by rw [← map_pow, H.rt_sq, map_neg, map_natCast, hδ]
  have hne : δ ≠ -δ := fun h => by
    have h2 : δ = 0 := by
      have : (2 : K) * δ = 0 := by linear_combination h
      exact (mul_eq_zero.1 this).resolve_left two_ne_zero
    rw [h2] at hδ
    have : (H.d : K) = 0 := by linear_combination hδ
    exact H.d_prime.ne_zero (by exact_mod_cast this)
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h0 with h | h
  · exact ⟨τ₀, τ', h, by rw [h', h]; exact fun e => hne e.symm⟩
  · exact ⟨τ', τ₀, by rw [h', h, neg_neg], by rw [h]; exact fun e => hne e.symm⟩

end GlobalTheory.CharRank
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImHermFormPer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw GlobalTheory.KeyCl GlobalTheory.LocM
open Filter Topology Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WeilStd


open ReciprocityTheory.PTheta Matrix in
theorem im_hermForm_per {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g))
    (k k' : Fin g → ℤ) {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ρ : (Fin g → ℂ) → ℂ) (hρd : Differentiable ℂ ρ) (hρ0 : ∀ z, ρ z ≠ 0)
    (χ : (Fin g ⊕ Fin g → ℤ) → ℂ) (hχ : ∀ r, χ r ≠ 0)
    (h : ∀ r z, ρ (z + per τ r) * (χ r * Complex.exp (Real.pi * hermForm Hm (F z) (F (per τ r)) +
        Real.pi / 2 * hermForm Hm (F (per τ r)) (F (per τ r)))) * theta (Key.halfVec k) (Key.halfVec k') z τ =
      ρ z * theta (Key.halfVec k) (Key.halfVec k') (z + per τ r) τ)
    (p q : Fin g ⊕ Fin g → ℤ) :
    (hermForm Hm (F (per τ p)) (F (per τ q))).im = omegaStd p q := by

  classical
  have hper : ∀ r : Fin g ⊕ Fin g → ℤ, per τ r =
      τ *ᵥ ofIntVec (fun i => r (Sum.inl i)) + ofIntVec (fun i => r (Sum.inr i)) := fun r => rfl
  have qp : ∀ r z, theta (Key.halfVec k) (Key.halfVec k') (z + per τ r) τ =
      autFactor (Key.halfVec k) (Key.halfVec k') τ (fun i => r (Sum.inl i)) (fun i => r (Sum.inr i)) z *
        theta (Key.halfVec k) (Key.halfVec k') z τ := fun r z => by
    rw [hper, ← add_assoc]
    exact thetaQuasiPeriod_holds (Fin g) _ _ z τ _ _ hτ.1
  choose c₁ hc₁ using fun r : Fin g ⊕ Fin g → ℤ =>
    NormalUnique.autFactor_eq_exp (Key.halfVec k) (Key.halfVec k') τ (fun i => r (Sum.inl i)) (fun i => r (Sum.inr i))
  let lin₁ : (Fin g ⊕ Fin g → ℤ) → (Fin g → ℂ) →ₗ[ℂ] ℂ := fun r =>
    { toFun := fun v => -(2 * Real.pi * Complex.I) * (ofIntVec (fun i => r (Sum.inl i)) ⬝ᵥ v)
      map_add' := fun v w => by simp only [dotProduct_add]; ring
      map_smul' := fun s v => by simp only [dotProduct_smul, smul_eq_mul, RingHom.id_apply]; ring }
  let lin₂ : (Fin g ⊕ Fin g → ℤ) → (Fin g → ℂ) →ₗ[ℂ] ℂ := fun r =>
    { toFun := fun v => (Real.pi : ℂ) * hermForm Hm (F v) (F (per τ r))
      map_add' := fun v w => by simp only [map_add (f := _), hermForm, add_dotProduct]; ring
      map_smul' := fun s v => by simp only [map_smul, hermForm, smul_dotProduct, smul_eq_mul, RingHom.id_apply]; ring }
  let c₂ : (Fin g ⊕ Fin g → ℤ) → ℂ := fun r =>
    Complex.log (χ r) + Real.pi / 2 * hermForm Hm (F (per τ r)) (F (per τ r))
  have e1 : ∀ r v, Complex.exp (lin₁ r v + c₁ r) =
      autFactor (Key.halfVec k) (Key.halfVec k') τ (fun i => r (Sum.inl i)) (fun i => r (Sum.inr i)) v := fun r v => by
    rw [hc₁]; rfl
  have e2 : ∀ r v, Complex.exp (lin₂ r v + c₂ r) = χ r * Complex.exp (Real.pi * hermForm Hm (F v) (F (per τ r)) +
      Real.pi / 2 * hermForm Hm (F (per τ r)) (F (per τ r))) := fun r v => by
    rw [show lin₂ r v + c₂ r = Complex.log (χ r) + (Real.pi * hermForm Hm (F v) (F (per τ r)) +
      Real.pi / 2 * hermForm Hm (F (per τ r)) (F (per τ r))) from by
        show (Real.pi : ℂ) * hermForm Hm (F v) (F (per τ r)) + (Complex.log (χ r) +
          Real.pi / 2 * hermForm Hm (F (per τ r)) (F (per τ r))) = _
        ring, Complex.exp_add, Complex.exp_log (hχ r)]
  have hfac : ∀ r v, Complex.exp (lin₁ r v + c₁ r) * ρ v = Complex.exp (lin₂ r v + c₂ r) * ρ (v + per τ r) := by
    intro r v
    have d₁ : Differentiable ℂ fun z => Complex.exp (lin₁ r z + c₁ r) * ρ z -
        Complex.exp (lin₂ r z + c₂ r) * ρ (z + per τ r) :=
      ((((LinearMap.toContinuousLinearMap (lin₁ r)).differentiable.add_const (c₁ r)).cexp).mul hρd).sub
        ((((LinearMap.toContinuousLinearMap (lin₂ r)).differentiable.add_const (c₂ r)).cexp).mul
          (hρd.comp (differentiable_id.add_const _)))
    rcases entire_eq_zero_or_eq_zero_of_mul_eq_zero _ (fun z => theta (Key.halfVec k) (Key.halfVec k') z τ) d₁
      (differentiable_theta hτ _ _) (fun z => by
        simp only [e1, e2]
        have h1 := h r z
        have h2 := qp r z
        linear_combination (-ρ z) * h2 - h1) with h0 | h0
    · exact sub_eq_zero.1 (h0 v)
    · exact absurd (funext h0) (theta_ne_zero hτ _ _)
  have key := alternating_eq_of_equivalent_factors (per τ) lin₁ lin₂ c₁ c₂ hρd.continuous hρ0 hfac p q
  set X := hermForm Hm (F (per τ p)) (F (per τ q)) with hX
  have k2 : -(2 * Real.pi * Complex.I) * (ofIntVec (fun i => p (Sum.inl i)) ⬝ᵥ per τ q) -
      -(2 * Real.pi * Complex.I) * (ofIntVec (fun i => q (Sum.inl i)) ⬝ᵥ per τ p) =
      (Real.pi : ℂ) * hermForm Hm (F (per τ q)) (F (per τ p)) - (Real.pi : ℂ) * X := key
  rw [hermForm_conj_symm_of_isHermitian Hm hH, ← hX, hper, hper, dotProduct_add, dotProduct_add] at k2
  have sym : ofIntVec (fun i => p (Sum.inl i)) ⬝ᵥ τ *ᵥ ofIntVec (fun i => q (Sum.inl i)) =
      ofIntVec (fun i => q (Sum.inl i)) ⬝ᵥ τ *ᵥ ofIntVec (fun i => p (Sum.inl i)) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hτ.1.eq, dotProduct_comm]
  have sc : X - star X = 2 * (X.im : ℂ) * Complex.I := by
    have := Complex.sub_conj X
    push_cast at this
    exact this
  have om : ((omegaStd p q : ℤ) : ℂ) = ofIntVec (fun i => p (Sum.inl i)) ⬝ᵥ ofIntVec (fun i => q (Sum.inr i)) -
      ofIntVec (fun i => q (Sum.inl i)) ⬝ᵥ ofIntVec (fun i => p (Sum.inr i)) := by
    simp only [omegaStd, ofIntVec, dotProduct, ← Finset.sum_sub_distrib]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have G : (2 * Real.pi * Complex.I) * (((omegaStd p q : ℤ) : ℂ) - (X.im : ℂ)) = 0 := by
    rw [om]
    linear_combination -k2 - (2 * Real.pi * Complex.I) * sym + (Real.pi : ℂ) * sc
  rcases mul_eq_zero.1 G with h0 | h0
  · exact absurd h0 Complex.two_pi_I_ne_zero
  · exact_mod_cast (sub_eq_zero.1 h0).symm

end GlobalTheory.WeilStd

namespace GlobalTheory.WeilStd


open GlobalTheory.NormalUnique in
theorem weilIs_per : ∀ (x : KeyIn ℂ) (g : ℕ) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ),
    x.P.g = g → τ.IsSymm → (τ.map Complex.im).PosDef → charHalf g a b → c ≠ 0 →
    (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
    u.IsFn x.th (fun z => c * thetaChar τ a b z) →
    ∀ (n : ℕ) (p q : Fin g ⊕ Fin g → ℤ) (e : ℂˣ), 0 < n →
      (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd p q : ℂ) / n) →
      Out.WeilIs x.P.A x.P.L n (u.ex ((n : ℂ)⁻¹ • per τ p)) (u.ex ((n : ℂ)⁻¹ • per τ q)) (unitOn e) := by
  intro x g u τ a b c hg hτs hτp hab hc hΛ hfn n p q e hn he
  subst hg
  obtain ⟨u₁, Hm, χ, Ef, hA, -, h1, h2, -, -, hE, -, hW⟩ := thetaUnifAV_all x.P x.rig x.rig_gen
  obtain ⟨F, hF, hFl, -, -⟩ := HomLinear.exists_linear_of_isMonHom x.P.A x.P.A x.P.isAb x.P.isAb x.P.L x.P.L
    x.P.g x.P.g u u₁ h1 h2 (𝟙 x.P.A) inferInstance
  simp only [Category.comp_id] at hF
  obtain ⟨ρ, hρd, hρ0, -, hρ⟩ := NormalUnique.exists_frame_ratio x.P.isLB u₁ u F hF
  obtain ⟨θ₁, hθ₁⟩ := exists_isFn x.P.isLB u₁ x.th
  have hT := (isThetaFn_and_ne_zero_of_isFn x u₁ Hm χ θ₁ hA hθ₁).1
  have hrel : ∀ z, c * thetaChar τ a b z = ρ z * θ₁ (F z) := hρ x.th θ₁ _ hθ₁ hfn
  have hmem : ∀ r, F (per τ r) ∈ u₁.Λ := fun r => hFl _ ((hΛ _).2
    ⟨fun i => r (Sum.inr i), fun i => r (Sum.inl i), by simp only [per]; rw [add_comm]⟩)
  obtain ⟨k, rfl⟩ : ∃ k : Fin x.P.g → ℤ, a = fun i => (k i : ℂ) / 2 :=
    ⟨fun i => if a i = 0 then 0 else 1, funext fun i => by rcases hab.1 i with h | h <;> simp [h]⟩
  obtain ⟨k', rfl⟩ : ∃ k : Fin x.P.g → ℤ, b = fun i => (k i : ℂ) / 2 :=
    ⟨fun i => if b i = 0 then 0 else 1, funext fun i => by rcases hab.2 i with h | h <;> simp [h]⟩
  simp only [SpMove.thetaChar_half] at hrel
  have hχ : ∀ l, χ l ≠ 0 := fun l => norm_ne_zero_iff.1 (by rw [hA.2.2.1]; exact one_ne_zero)
  have key := WeilStd.im_hermForm_per (τ := τ) ⟨hτs, hτp⟩ k k' hA.1 F ρ hρd hρ0 (fun r => χ ⟨_, hmem r⟩)
    (fun r => hχ _) (fun r z => by
      have eA := hrel (z + per τ r)
      have eB := hT.2 ⟨_, hmem r⟩ (F z)
      have eC := hrel z
      rw [pow_one] at eB
      rw [map_add (f := _)] at eA
      apply mul_left_cancel₀ hc
      linear_combination (ρ (z + per τ r) * (χ ⟨_, hmem r⟩ * Complex.exp (Real.pi * hermForm Hm (F z) (F (per τ r)) +
        Real.pi / 2 * hermForm Hm (F (per τ r)) (F (per τ r))))) * eC - ρ z * eA - ρ z * ρ (z + per τ r) * eB) p q
  have hEf : Ef ⟨_, hmem p⟩ ⟨_, hmem q⟩ = omegaStd p q := by
    have := hE ⟨_, hmem p⟩ ⟨_, hmem q⟩
    rw [key] at this
    exact_mod_cast this
  have hw := hW n ⟨_, hmem p⟩ ⟨_, hmem q⟩ e hn (by rw [he, hEf])
  have e1 : u.ex ((n : ℂ)⁻¹ • per τ p) = u₁.ex ((n : ℂ)⁻¹ • F (per τ p)) := by rw [← map_smul, hF]
  have e2 : u.ex ((n : ℂ)⁻¹ • per τ q) = u₁.ex ((n : ℂ)⁻¹ • F (per τ q)) := by rw [← map_smul, hF]
  rw [e1, e2]
  exact hw

end GlobalTheory.WeilStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndexBoundCoefficientFieldOfExactSmallField
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AtMember

open GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize

theorem odd_of_mem_levelPrimes (P : Pre) {p : ℕ} (hp : p ∈ P.host.levelPrimes) : Odd p := by
  have h := (P.level_cond p hp).2
  have h2 : (2 : ℕ) ∣ P.host.QS * P.host.q * P.host.d := ((((dvd_pow_self 2 (Nat.succ_ne_zero _)).trans P.host.tower_dvd).mul_right _).mul_right _)
  rw [Nat.odd_iff, ← Nat.mod_mod_of_dvd p h2, h]


set_option maxHeartbeats 4000000 in
theorem fieldTies_of_ksExact : GlobalTheory.NT.RayField → ∀ (X : Stages) (f : Fr X.B.toPre) (δ : Fld.FieldDat X.B.toPre),
    X.B.KsExact δ f → FieldTies X.toD7 (Fr.at X f) := by
  intro hR X f δ hx
  have := GlobalTheory.Mem.FieldsEx.host_cplx X.B.toPre
  have hFO : FO X.toD7 = X.B.KsC := SetLike.ext fun z => (mem_FO_assembled_iff X z).trans (X.B.mem_KsC).symm
  have hxe : X.B.KsC = Fld.listField δ f := hx
  obtain ⟨hray, -, hchar, -⟩ := Base.KsExact.lower hx
  have key : ∀ p, (p = X.B.host.pde ∨ p = X.B.host.pde') → FieldOK0 X.toD7 p := by
    intro p hp
    have hpl : p ∈ X.B.host.levelPrimes := by
      rcases hp with rfl | rfl
      exacts [X.B.host.pde_level.1, X.B.host.pde_level.2]
    have hpp : p.Prime := (X.B.toPre.level_cond p hpl).1
    have hdvd : X.B.host.g 0 * X.B.host.g 1 * p ∣ Fld.modulus X.B.toPre := by
      rcases hp with rfl | rfl
      · exact dvd_mul_right _ _
      · exact ⟨X.B.host.pde, by unfold Fld.modulus; ring⟩
    have hpd : p ∣ Fld.modulus X.B.toPre := (dvd_mul_left p _).trans hdvd
    refine ⟨hp, hermitianCodeWordStages_ringOfIntegers_full _, hermitianCodeWordStages_has_rootOfUnity _, ?_, ?_, TypeNormPin.hermitianCodeWordStages_typeNorms_principal _,
      fun h => Nat.not_prime_zero (X.B.toPre.level_cond 0 h).1, ?_⟩
    · rw [hFO]
      exact hray (GlobalTheory.Mem.RayRoots.rootOne_mem_of_isRayFieldIn X.B.host.E X.B.host.φ₀ (Fld.modulus X.B.toPre) p δ.ray (Fld.modulus_ne_zero _) hpd δ.isRay)
    · have hn0 : 0 < X.B.host.g 0 * X.B.host.g 1 * p :=
        Nat.mul_pos (Nat.mul_pos (X.B.host.g_prime 0).pos (X.B.host.g_prime 1).pos) hpp.pos
      refine GlobalTheory.FieldSize.curveOver_of_weberSet X.toD7 _ hn0 ?_ fun L hL => ?_
      · rw [hFO]
        exact X.B.imField_le_KsC ⟨_, rfl⟩
      · have hodd : Odd (X.B.host.g 0 * X.B.host.g 1 * p) :=
          ((odd_of_mem_levelPrimes X.B.toPre (X.B.host.g_level 0)).mul
            (odd_of_mem_levelPrimes X.B.toPre (X.B.host.g_level 1))).mul (odd_of_mem_levelPrimes X.B.toPre hpl)
        have h3 : 3 ≤ X.B.host.g 0 * X.B.host.g 1 * p := by
          have a := (X.B.host.g_prime 0).two_le
          have b := (X.B.host.g_prime 1).two_le
          have c := hpp.two_le
          have := Nat.mul_le_mul (Nat.mul_le_mul a b) c
          omega
        rw [hFO]
        exact (GlobalTheory.FieldSize.WeberRay.weberSet_subset_ray X.B.toPre δ L hL _ hodd h3 hdvd).trans fun z hz => hray hz
    · rcases hp with rfl | rfl
      exacts [X.B.toPre.level_split _ X.B.host.pde_level.1, X.B.toPre.level_split _ X.B.host.pde_level.2]
  refine ⟨key _ (Or.inl rfl), key _ (Or.inr rfl), fun x => ?_, fun x => ?_, fun L hL => ?_⟩
  · rw [hFO]
    exact GlobalTheory.Mem.ValFin.mem_of_orderDvd X.B.host.E f.del X.B.KsC f.isDel.fin
      ((le_sup_right.trans (le_sup_left.trans le_sup_left)).trans hchar) x
  · rw [hFO]
    exact GlobalTheory.Mem.ValFin.mem_of_orderDvd X.B.host.E f.del' X.B.KsC f.isDel'.fin ((le_sup_right.trans le_sup_left).trans hchar) x
  · have hle : FO X.toD7 ≤ δ.Om := by
      rw [hFO, hxe]
      exact GlobalTheory.Mem.FieldsEx.listField_le_Om δ f
    exact GlobalTheory.FieldSize.sz_mono_and_of_le.2 _ _ _ _ hle (_root_.GlobalTheory.FieldSize.sz_Om_poR hR X.B.toPre δ L hL)

end GlobalTheory.AtMember

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndexZeroOffTwistedPlaces
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.R3.Rw.St.idx_zero_off_twisted : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), P.Wt = x.m.z.W1 (F0K K.s (w.D x.o.Z)) → ∀ v, v ∉ P.Wt → ∀ j, 1 ≤ j → j ≤ B.R.m →
      (w.D x.o.Z).what₂.Ij (w.D x.o.Z).what₂.mu0 j v = 0 ∧ (w.D x.o.Z).what₂.jw (w.D x.o.Z).what₂.mu0 j v = 0 := by
  intro K B f T w hO hF hP P x hη hW v hv j hj1 hj2
  classical
  let Zr : ReadL x.m.z.R x.m.z.F x.s.p0 x.r.Y := (x.rowsAre hη).Z
  obtain ⟨G, Y, -⟩ := GlobalTheory.PointGeometry.exists_geo (w.st x.o.Z).toD7.what₂.LL
  let Fm : ∀ k, GlobalTheory.ProvisionalDivX.MjForm (w.st x.o.Z).toD7 k := fun k =>
    ⟨mjH Zr k, jM Zr k, mjH_good Zr x.m.intersectionNumber_baseChange k, jM_basis Zr x.m.intersectionNumber_baseChange k, jM_lat Zr x.m.z.pins x.m.intersectionNumber_baseChange k,
      mjLat_sub Zr x.m.z.pins x.m.intersectionNumber_baseChange k, MjModel.jM_metric_all Zr x.m.intersectionNumber_baseChange k⟩
  let Xd : DivX (w.st x.o.Z).toD7 := GlobalTheory.provisionalDivX (w.st x.o.Z).toD7 G Y
    (fun p _ => (GlobalTheory.WittFracComplex.nonempty_ringHom_complex p).some)
    (fun p _ r => (GlobalTheory.nonempty_admissibleModel _ p _ (max r 2) 1 (by omega)).some) Fm
  have hMj := mjHTie_of_eq Zr Xd rfl (HEq.refl (jM Zr))
  have hIdx : IdxDefs (w.st x.o.Z).toD7 Xd := (P.q.num x.o.η x.o.hη x.o.V x.o.S x.o.N x.o.G).idx Xd
  have hT := GlobalTheory.T.numbers_eq_concreteNumbers_at_baseLevel _ _ _ _ _ _ _ x.m.z.R x.m.z.F x.m.z.cG x.s.p0 x.r.Y Zr Xd _ x.m.z.pins x.m.intersectionNumber_baseChange hMj hIdx
  have hv' : v ∉ x.m.z.W1 (F0K K.s (w.D x.o.Z)) := hW ▸ hv
  have h0 : x.r.Y.tup (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A.μ0 = (w.D x.o.Z).what₂.mu0 := by
    rw [x.r.tup]; exact x.m.y.tup0
  have hIj := hT.Ij
  have hjw := hT.jw
  have hv2 := fun (i : Fin (w.st x.o.Z).toD7.R.m) (w' : HeightOneSpectrum (𝓞 (w.st x.o.Z).toD7.what₂.LL))
      (hw' : w' ∈ ({(w.st x.o.Z).toD7.plEq v, Formalism.DivisionValues.conjPl ((w.st x.o.Z).toD7.plEq v)} : Set _)) =>
    not_or.1 (fun h => hv' ⟨i, w', hw', h⟩)
  have hm : (w.st x.o.Z).toD7.R.m = B.R.m := rfl
  obtain ⟨i, rfl⟩ : ∃ i : Fin (w.st x.o.Z).toD7.R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  rw [← h0]
  have hp : (w.st x.o.Z).toD7.plEq v ∈ ({(w.st x.o.Z).toD7.plEq v, Formalism.DivisionValues.conjPl ((w.st x.o.Z).toD7.plEq v)} : Set _) :=
    Set.mem_insert _ _
  refine ⟨?_, ?_⟩
  · exact (hIj i _ v).trans (not_not.1 (hv2 i _ hp).1)
  · exact (hjw i _ v).trans (not_not.1 (not_or.1 (hv2 i _ hp).2).1)
end

