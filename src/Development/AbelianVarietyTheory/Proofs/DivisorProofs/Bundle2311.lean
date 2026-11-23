module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1534
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1998
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2107
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0721
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfCharZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RetractionLiftObstructionZeroOfLiftedSection
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem appLE_apply_of_eq_id {X : Scheme.{0}} {g : X ⟶ X} (hg : g = 𝟙 X) {U V : X.Opens} (e : V ≤ g ⁻¹ᵁ U)
    (e' : V ≤ U) (x : Γ(X, U)) : (g.appLE U V e).hom x = (X.presheaf.map (homOfLE e').op).hom x := by
  subst hg
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
  rfl

theorem appLE_appLE_of_retr {X₀ Z₀ : Scheme.{0}} {j₀ : X₀ ⟶ Z₀} {f₀ : Z₀ ⟶ X₀} (hjf : j₀ ≫ f₀ = 𝟙 X₀)
    (U : X₀.Opens) (U' : Z₀.Opens) (U'' : X₀.Opens) (e₁ : U' ≤ f₀ ⁻¹ᵁ U) (e₂ : U'' ≤ j₀ ⁻¹ᵁ U')
    (e : U'' ≤ U) (x : Γ(X₀, U)) :
    (j₀.appLE U' U'' e₂).hom ((f₀.appLE U U' e₁).hom x) = (X₀.presheaf.map (homOfLE e).op).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  exact appLE_apply_of_eq_id hjf _ e x

theorem ext_tri_res_pull1 {R₀ : Type} [CommRing R₀] (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁]
    {X X' X'' : Scheme.{0}} {ψ : X'' ⟶ X'} {φ : X' ⟶ X} {s' : X' ⟶ Sp R₀} {s'' : X'' ⟶ Sp R₀}
    (h' : ψ ≫ s' = s'' ≫ spMap (RingHom.id R₀)) (a : CatCoh.H1 (ext R₁ (OAff s'))) :
    (extMap R₁ (cechTriplePullbackSecond (φ := φ) h')).pull1 ((extMap R₁ (pairRes φ s')).pull1 a) =
      (extMap R₁ (cechTripleRestrictFirst ψ φ s'')).pull1 ((extMap R₁ (pairPull h')).pull1 a) := by
  rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
  refine CoefMap.pullCohomologyOne_eq_of_natTrans ((extMap R₁ (pairRes φ s')).comp (extMap R₁ (cechTriplePullbackSecond (φ := φ) h')))
    ((extMap R₁ (pairPull h')).comp (extMap R₁ (cechTripleRestrictFirst ψ φ s''))) { app U := 𝟙 _ } (fun U b ↦ ?_) a
  erw [mp_id]
  induction b using TensorProduct.induction_on with
  | zero => (erw [map_zero]) <;> rfl
  | tmul x y => rfl
  | add x y hx hy => erw [map_add, map_add, hx, hy]

theorem retractionLiftObstruction_zero_of_liftedSection_alt : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ Z₀ X Z : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (s : X ⟶ Sp R) (t : Z ⟶ Sp R) (i : X₀ ⟶ X) (k : Z₀ ⟶ Z) (hi : IsPullback i s₀ s (spMap π)) (hkk : IsPullback k t₀ t (spMap π)) (S : Sys I π s₀) (S' : Sys I π t₀) (P : S.Presents s i) (P' : S'.Presents t k) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (j₀ : X₀ ⟶ Z₀) (hj : j₀ ≫ t₀ = s₀ ≫ spMap (RingHom.id R₀)) (j : X ⟶ Z), j₀ ≫ f₀ = 𝟙 X₀ → j ≫ t = s → i ≫ j = j₀ ≫ k → ∀ (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T), (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l → ∀ (w : GlobForm s₀) (c : GlobalTheory.CatCoh.H1 (ext R₁ (OAff t₀))), (ofSys S).IsOb1 (pairPre S' f₀) (pairPull h) l α w ((extMap R₁ (pairRes f₀ t₀)).pull1 c) → IsExtendedPullbackDegOne R₁ hj c 0 := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ Z₀ X Z s₀ t₀ s t i k hi hkk S S' P P' f₀ h j₀ hj j hjf hjt hij l hl w c hob
  obtain ⟨l', hl'L, hl'N⟩ := _root_.GlobalTheory.Obs.exists_chart_lifts R R₀ I hI π hπ hk Z₀ X₀ Z X t₀ s₀ t s k i hkk hi S' S P' P j₀ hj j hjt hij
  have hle : ∀ T : (Triple j₀ f₀)ᵒᵖ, T.unop.1.1 ≤ T.unop.1.2.2 := fun T x hx ↦ by
    have h1 := T.unop.2.2 (T.unop.2.1 hx)
    have e := congrArg (fun g : X₀ ⟶ X₀ ↦ g.base x) hjf
    simp at e
    exact e ▸ h1
  let L'' : Pre I π (OTriple j₀ f₀ s₀) := (ofSys S).restrict (cechTripleProjFirstThird j₀ f₀ ⋙ pairFst (j₀ ≫ f₀))
  let u : ∀ T : (Triple j₀ f₀)ᵒᵖ, (pairPre S' f₀).B ((cechTriplePullbackSecond (φ := f₀) hj).G.obj T) →ₐ[R] L''.B T :=
    fun T ↦ l' ((cechTripleProjFirstSecond j₀ f₀).obj T)
  let v : ∀ T : (Triple j₀ f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj ((cechTriplePullbackSecond (φ := f₀) hj).G.obj T)) →ₐ[R] L''.B T :=
    fun T ↦ mp S.F (homOfLE (hle T)).op
  have hvan := _root_.GlobalTheory.Obs.obstructionPullback_eq_zero_of_naturalLift R R₀ I hI π hπ hk R₁ α (AffOp X₀) (OAff s₀) (Pair f₀)ᵒᵖ (OPair f₀ t₀) (ofSys S)
    (pairPre S' f₀) (pairPull h) l (Triple j₀ f₀)ᵒᵖ (OTriple j₀ f₀ s₀) L'' (cechTriplePullbackSecond hj) u v hl
    (fun T b ↦ hl'L ((cechTripleProjFirstSecond j₀ f₀).obj T) b)
    (fun T T' a b ↦ by
      have e1 : (cechTripleProjFirstThird j₀ f₀ ⋙ pairFst (j₀ ≫ f₀)).map a = (pairFst j₀).map ((cechTripleProjFirstSecond j₀ f₀).map a) :=
        Quiver.Hom.unop_inj (Subsingleton.elim _ _)
      have e2 : (pairFst f₀).map ((cechTripleProjSecondThird j₀ f₀).map a) = (pairSnd j₀).map ((cechTripleProjFirstSecond j₀ f₀).map a) :=
        Quiver.Hom.unop_inj (Subsingleton.elim _ _)
      change mp S.F ((cechTripleProjFirstThird j₀ f₀ ⋙ pairFst (j₀ ≫ f₀)).map a) (l' ((cechTripleProjFirstSecond j₀ f₀).obj T) b) =
        l' ((cechTripleProjFirstSecond j₀ f₀).obj T') (mp S'.F ((pairFst f₀).map ((cechTripleProjSecondThird j₀ f₀).map a)) b)
      rw [e1, e2]
      exact hl'N ((cechTripleProjFirstSecond j₀ f₀).map a) b)
    (fun T b ↦ by
      change S.p _ (mp S.F _ b) = (j₀.appLE _ _ _).hom ((f₀.appLE _ _ _).hom (S.p _ b))
      exact (S.nat _ b).trans (appLE_appLE_of_retr hjf _ _ _ _ _ (hle T) _).symm)
    (fun T T' a b ↦ by
      change mp S.F _ (mp S.F _ b) = mp S.F _ (mp S.F _ b)
      exact (mp_comp S.F _ _ b).symm.trans ((congrArg (fun q ↦ mp S.F q b)
        (Quiver.Hom.unop_inj (Subsingleton.elim _ _))).trans (mp_comp S.F _ _ b)))
    w ((extMap R₁ (pairRes f₀ t₀)).pull1 c) hob
  rw [ext_tri_res_pull1] at hvan
  have inj := (_root_.GlobalTheory.Obs.PairExt.pairRes_ext_bijective R₀ R₁ Z₀ X₀ s₀ j₀).2 X₀ f₀
  unfold IsExtendedPullbackDegOne
  rw [map_zero]
  exact inj (hvan.trans (map_zero _).symm)

end GlobalTheory.Obs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianLieMeasureFrameBoxLe
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.FrameBox
open Matrix

theorem riemLie_frameBox_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r), 1 ≤ r → IsIdent p q Ψ G x σ A e → ∀ t : ℝ, 0 < t → riemLie Ψ G x {X | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < t} ≤ ENNReal.ofReal ((3 * t) ^ (Ψ.card * (r ^ 2 - 1))) := by
  classical
  intro E _ _ _ r κ p q Ψ G x σ A e hr hI t ht
  set W := (realLie Ψ G).comap (fromFrame x) with hW
  set z : Fin r := ⟨0, hr⟩ with hz
  set d := sgnR σ e with hd_def
  have hd : ∀ τ a, d τ a = 1 ∨ d τ a = -1 := fun τ a => by
    simp only [d, sgnR]; split_ifs <;> simp
  have hinv := det_ne_zero_of_isIdent hI
  have hvW : ∀ k, boxVec d z k ∈ W := fun k =>
    (_root_.GlobalTheory.CovTop.VolUp.FrameBox.mem_comap_realLie_iff_skewCond E r κ p q Ψ G x σ A e hI _).2 (_root_.GlobalTheory.CovTop.VolUp.FrameBox.skewCond_boxVec E r Ψ d z hd k)
  let K := Ψ × {ab : Fin r × Fin r // ab ≠ (z, z)}
  let w : K → W := fun k => ⟨boxVec d z k, hvW k⟩
  have hdual := GlobalTheory.T.skewHermitianCoordinate_dual_basisVector E r Ψ d z hd
  have hcoord : ∀ (g : K → ℝ) j, boxCoord z j ((∑ k, g k • w k : W) : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) = g j := by
    intro g j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, w, hdual, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Fintype.sum_eq_single j (fun k hk => by rw [if_neg (Ne.symm hk)])]
    rw [if_pos rfl]
  have hli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have := hcoord g j
    rw [hg] at this
    simpa using this.symm
  have hcardK : Fintype.card K = Ψ.card * (r ^ 2 - 1) := by
    simp [K, Fintype.card_prod, Fintype.card_coe, sq]
  have hfin : Fintype.card K = Module.finrank ℝ W := by
    refine le_antisymm hli.fintype_card_le_finrank ?_
    rw [hcardK]
    rcases Ψ.eq_empty_or_nonempty with h0 | ⟨τ0, hτ0⟩
    · have hs : Subsingleton W := ⟨fun a b => Subtype.ext (PiLp.ext fun m => by
        have := m.1.2; simp [h0] at this)⟩
      rw [Module.finrank_zero_of_subsingleton]; exact Nat.zero_le _
    · have hG : G.det ≠ 0 := by
        intro h
        apply (hinv ⟨τ0, hτ0⟩).2
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
      exact finrank_comap_realLie_le Ψ G x hr hG fun τ => (hinv τ).1
  have hspan : Submodule.span ℝ (Set.range w) = ⊤ := hli.span_eq_top_of_card_eq_finrank' hfin
  have hrep : ∀ Y : W, Y = ∑ k, boxCoord z k (Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) • w k := by
    intro Y
    have hYs : Y ∈ Submodule.span ℝ (Set.range w) := hspan ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun ℝ |>.1 hYs
    have h2 : ∀ j, boxCoord z j (Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) = c j := by
      intro j
      rw [← hc]
      exact hcoord _ j
    simp_rw [h2]; exact hc.symm
  set S := {X : Ψ → Fin r → Fin r → ℂ | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < t} with hS_def
  have hSo : IsOpen S := by
    simp only [hS_def, Set.setOf_forall]
    refine isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => isOpen_lt ?_ continuous_const
    have : Continuous fun X : Ψ → Fin r → Fin r → ℂ => Matrix.of (X τ) := continuous_apply τ
    exact (((continuous_const.matrix_mul this).matrix_mul continuous_const).matrix_elem a b).norm
  have hf : Measurable (fun Y : W => fromFrame x Y.1) :=
    ((fromFrame x).comp W.subtype).continuous_of_finiteDimensional.measurable
  unfold riemLie
  rw [Measure.map_apply hf hSo.measurableSet, OrthonormalBasis.addHaar_eq_volume]
  have key1 : ∀ τ (M : Matrix (Fin r) (Fin r) ℂ),
      (mat x τ)⁻¹ * (mat x τ * M * (mat x τ)⁻¹) * mat x τ = M := fun τ M => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ (hinv τ).1.isUnit,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hinv τ).1.isUnit]
  have hsub : (fun Y : W => fromFrame x Y.1) ⁻¹' S ⊆
      {y : W | ∃ c : K → ℝ, (∀ k, |c k| ≤ t) ∧ y = ∑ k, c k • w k} := by
    intro Y hY
    have hY' : ∀ τ a b, ‖(Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) (τ, a, b)‖ < t := by
      intro τ a b
      have := hY τ a b
      have e1 : Matrix.of (fromFrame x Y.1 τ) =
          mat x τ * Matrix.of (fun a b => (Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) (τ, a, b)) * (mat x τ)⁻¹ := rfl
      rwa [e1, key1] at this
    refine ⟨fun k => boxCoord z k (Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)), fun k => ?_, hrep Y⟩
    obtain ⟨τ, ⟨⟨a, b⟩, hab⟩⟩ := k
    simp only [boxCoord]
    split_ifs
    · exact (Complex.abs_re_le_norm _).trans (hY' _ _ _).le
    · exact (Complex.abs_im_le_norm _).trans (hY' _ _ _).le
    · exact (Complex.abs_im_le_norm _).trans (hY' _ _ _).le
  refine (measure_mono hsub).trans ((GlobalTheory.T.volume_coordinateBox_le_hadamard W K w t ht.le hfin).trans (ENNReal.ofReal_le_ofReal ?_))
  have hn : ∀ k, ‖w k‖ = √2 := fun k => _root_.GlobalTheory.CovTop.VolUp.FrameBox.norm_boxVec E r Ψ d z hd k
  simp only [hn, Finset.prod_const, Finset.card_univ]
  rw [hcardK, ← mul_pow]
  have h2 : 2 * t * √2 ≤ 3 * t := by
    have hs : √2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    nlinarith
  exact pow_le_pow_left₀ (by positivity) h2 _

end GlobalTheory.CovTop.VolUp.FrameBox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedIdentificationsGenericFibreAgree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.GenEqual

theorem key {X₁ X₂ X₃ XE S₁ S₂ S₃ SE : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {L₃ : LB X₃} {LE : LB XE}
    (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (hL₃ : L₃.IsLB) (hLE : LE.IsLB)
    (Fp : X₃ ⟶ X₁) (Φ : X₃ ⟶ X₂) (κ : XE ⟶ X₃)
    (e₁ : S₁ ⟶ X₁) (e₂ : S₂ ⟶ X₂) (e₃ : S₃ ⟶ X₃) (eE : SE ⟶ XE)
    (t₁ : S₃ ⟶ S₁) (t₂ : S₃ ⟶ S₂) (sE : SE ⟶ S₃) (pE : XE ⟶ SE) (hpE : eE ≫ pE = 𝟙 _)
    (hsurj : Function.Surjective pE.appTop.hom) (hc : eE ≫ κ = sE ≫ e₃)
    (r₁ : LB.Gen (L₁.pull e₁)) (r₂ : LB.Gen (L₂.pull e₂)) (r₃ : LB.Gen (L₃.pull e₃)) (rE : LB.Gen (LE.pull eE))
    (wp : LB.Iso L₃ (L₁.pull Fp)) (w : LB.Iso L₃ (L₂.pull Φ)) (F₁ : XE ⟶ X₁) (F₂ : XE ⟶ X₂) (h₁ : κ ≫ Fp = F₁) (h₂ : κ ≫ Φ = F₂) (u₁ : LB.Iso LE (L₁.pull F₁))
    (u₂ : LB.Iso LE (L₂.pull F₂)) (gp : PGen wp) (gw' : PGen w) (g₁ : PGen u₁) (g₂ : PGen u₂)
    (mp : PMaps wp (K := PUnit) (fun _ => e₃) (fun _ => e₁) (fun _ => 1) r₃ r₁ t₁)
    (mw : PMaps w (K := PUnit) (fun _ => e₃) (fun _ => e₂) (fun _ => 1) r₃ r₂ t₂)
    (m₁ : PMaps u₁ (K := PUnit) (fun _ => eE) (fun _ => e₁) (fun _ => 1) rE r₁ (sE ≫ t₁))
    (m₂ : PMaps u₂ (K := PUnit) (fun _ => eE) (fun _ => e₂) (fun _ => 1) rE r₂ (sE ≫ t₂))
    (Z : Scheme.{0}) (f : Z ⟶ XE) (z : Z) (j : L₂.ι) (i : L₃.ι) (k : LE.ι) (l : L₁.ι)
    (hj : F₂ (f z) ∈ L₂.U j) (hi : κ (f z) ∈ L₃.U i) (hk : f z ∈ LE.U k) (hl : F₁ (f z) ∈ L₁.U l) :
    gw w (f ≫ κ) z j i * (gw wp (f ≫ κ) z l i)⁻¹ = gw u₂ f z j k * (gw u₁ f z l k)⁻¹ := by
  subst h₁ h₂
  obtain ⟨v, Tv⟩ := exists_cancel hL₁ wp u₁ gp g₁ hL₃ hLE
  have gv := Tv.pgen_cancel hL₁ gp g₁
  have rv := Tv.pmaps_cancel hL₁ (fun _ => hc) mp m₁
  obtain ⟨u, Tu⟩ := exists_comp hL₃ w v gw' gv hL₂ hLE
  have gu := Tu.pgen_comp hL₃ gw' gv
  have ru := Tu.pmaps_comp hL₃ (fun _ => hc) mw rv
  have e := GlobalTheory.OverMove.gw_eq_of_pmaps hL₂ hLE pE eE hpE hsurj rfl gu g₂ rfl ru m₂ f z j k
  rw [← e, Tu Z f z j i k hj hi hk, Tv Z f z l i k hl hi hk]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem genequal : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')) (p : IsPullDeg ρ D₁ D₃) (q₁ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) (q₂ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) (Φ : D₃.P.A.left ⟶ D₂.P.A.left) (κ : E.P.A.left ⟶ D₃.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ → κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ → κ ≫ Φ = GlobalTheory.PsiEvenPull.proj q₂ → ∀ w : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w → PMaps w (K := PUnit) (fun _ => eSec D₃.P.A) (fun _ => eSec D₂.P.A) (fun _ => 1) D₃.rig D₂.rig (spMap ρ) → ∀ (Z : Scheme.{0}) (f : Z ⟶ E.P.A.left) (z : Z) (j : D₂.P.L.ι) (i : D₃.P.L.ι) (k : E.P.L.ι) (l : D₁.P.L.ι), GlobalTheory.PsiEvenPull.proj q₂ (f z) ∈ D₂.P.L.U j → κ (f z) ∈ D₃.P.L.U i → f z ∈ E.P.L.U k → GlobalTheory.PsiEvenPull.proj q₁ (f z) ∈ D₁.P.L.U l → gw w (f ≫ κ) z j i * (gw p.w (f ≫ κ) z l i)⁻¹ = gw q₂.w f z j k * (gw q₁.w f z l k)⁻¹ := by
  intro R R' _ _ _ _ ρ D₁ D₂ D₃ E p q₁ q₂ Φ κ _ hκ hκp hκΦ w hw hr Z f z j i k l hj hi hk hl
  have hs : spMap ((algebraMap R' (FractionRing R')).comp ρ) = spMap (algebraMap R' (FractionRing R')) ≫ spMap ρ := by
    rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl
  have m₁ := GlobalTheory.FieldPull.pmaps_rig q₁
  have m₂ := GlobalTheory.FieldPull.pmaps_rig q₂
  rw [hs] at m₁ m₂
  exact key D₁.P.isLB D₂.P.isLB D₃.P.isLB E.P.isLB (GlobalTheory.PsiEvenPull.proj p) Φ κ (eSec D₁.P.A) (eSec D₂.P.A)
    (eSec D₃.P.A) (eSec E.P.A) (spMap ρ) (spMap ρ) (spMap (algebraMap R' (FractionRing R'))) E.P.A.hom
    (Over.w η[E.P.A]) (GlobalTheory.globalFns_holds _ E.P.A E.P.isAb).2 (cubeMapOf hκ).e_comm D₁.rig D₂.rig D₃.rig E.rig
    p.w w _ _ hκp hκΦ q₁.w q₂.w ((isGen_iff _).1 p.w_gen) hw ((isGen_iff _).1 q₁.w_gen) ((isGen_iff _).1 q₂.w_gen)
    (GlobalTheory.FieldPull.pmaps_rig p) hr m₁ m₂ Z f z j i k l hj hi hk hl

end GlobalTheory.GenEqual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomFiniteOfQuasiFiniteCompleteLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.QuasiFiniteLocal

theorem finite_quotient_of_pow_le_of_span {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    [IsNoetherianRing S] {I J : Ideal S} (T : Set S) (hT : T.Finite)
    (h : ∀ s : S, ∃ t ∈ Submodule.span A T, s - t ∈ I) {N : ℕ}
    (hN : I ^ N ≤ J) : Module.Finite A (S ⧸ J) := by
  have key : ∀ N : ℕ, ∃ F : Submodule A S, F.FG ∧ F ⊔ (I ^ N).restrictScalars A = ⊤ := by
    intro N
    induction N with
    | zero => exact ⟨⊥, Submodule.fg_bot, by simp⟩
    | succ N ih =>
      obtain ⟨F, hF, hF'⟩ := ih
      obtain ⟨G, hG⟩ : (I ^ N).FG := IsNoetherian.noetherian _
      refine ⟨F ⊔ Submodule.span A (Set.image2 (· * ·) T (G : Set S)),
        hF.sup (Submodule.fg_span (hT.image2 _ G.finite_toSet)), ?_⟩
      rw [eq_top_iff, ← hF', sup_assoc]
      refine sup_le_sup_left (fun x hx => ?_) _
      have hx' : x ∈ Submodule.span S (G : Set S) := hG.ge hx
      obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.1 hx'
      refine sum_mem fun y hy => ?_
      obtain ⟨t, ht, ha⟩ := h (c y)
      have e : c y • y = t * y + y * (c y - t) := by rw [smul_eq_mul]; ring
      rw [e]
      refine Submodule.add_mem_sup ?_ ?_
      · have hmul : ∀ u ∈ Submodule.span A T,
            u * y ∈ Submodule.span A (Set.image2 (· * ·) T (G : Set S)) := by
          intro u hu
          induction hu using Submodule.span_induction with
          | mem u hu => exact Submodule.subset_span (Set.mem_image2_of_mem hu hy)
          | zero => simp
          | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
          | smul a u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hu
        exact hmul t ht
      · rw [pow_succ]
        exact Ideal.mul_mem_mul (hG.le (Ideal.subset_span hy)) ha
  obtain ⟨F, hF, hF'⟩ := key N
  have : Module.Finite A F := Module.Finite.iff_fg.2 hF
  refine Module.Finite.of_surjective ((Ideal.Quotient.mkₐ A J).toLinearMap ∘ₗ F.subtype) fun s => ?_
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hF'.ge (Submodule.mem_top (x := s)))
  exact ⟨⟨y, hy⟩, Ideal.Quotient.eq.2 (by simpa using hN hz)⟩

theorem finite_of_quasiFinite : ∀ (A R : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (b : A →+* R) [IsLocalHom b], IsAdicComplete (maximalIdeal A) A → (∀ p : Ideal R, p.IsPrime → (maximalIdeal A).map b ≤ p → p = maximalIdeal R) → ((residue R).comp b).Finite → b.Finite := by
  intro A R _ _ _ _ _ _ b _ hc hq hres
  letI : Algebra A R := b.toAlgebra
  have hb : algebraMap A R = b := rfl
  have hle : (maximalIdeal A).map (algebraMap A R) ≤ maximalIdeal R := by
    refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    rw [Ideal.mem_comap, hb, mem_maximalIdeal, mem_nonunits_iff]
    exact fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit b a h)
  have hrad : maximalIdeal R ≤ ((maximalIdeal A).map (algebraMap A R)).radical := by
    rw [Ideal.radical_eq_sInf]
    exact le_sInf fun p ⟨hJp, hp⟩ => (hq p hp hJp).ge
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)

  obtain ⟨T0, hT0⟩ : (⊤ : Submodule A (ResidueField R)).FG := by
    letI : Algebra A (ResidueField R) := ((residue R).comp b).toAlgebra
    exact hres.fg_top
  classical
  let lift : ResidueField R → R := Function.surjInv (residue_surjective (R := R))
  have hlift : ∀ t, residue R (lift t) = t := Function.surjInv_eq _
  let L : R →ₗ[A] ResidueField R :=
    { toFun := residue R
      map_add' := map_add _
      map_smul' := fun a x => by
        show residue R (b a * x) = residue R (b a) * residue R x
        exact map_mul _ _ _ }
  have hfin : Module.Finite A (R ⧸ (maximalIdeal A).map (algebraMap A R)) := by
    refine finite_quotient_of_pow_le_of_span (I := maximalIdeal R) (lift '' (T0 : Set _))
      ((T0.finite_toSet).image _) (fun s => ?_) hN
    have hs : residue R s ∈ Submodule.map L (Submodule.span A (lift '' (T0 : Set _))) := by
      rw [Submodule.map_span, ← Set.image_comp]
      have e : (⇑L ∘ lift) = id := funext fun t => hlift t
      rw [e, Set.image_id, hT0]
      trivial
    obtain ⟨t, ht, hts⟩ := hs
    refine ⟨t, ht, ?_⟩
    rw [← residue_eq_zero_iff, map_sub]
    exact sub_eq_zero.2 hts.symm
  have : IsHausdorff ((maximalIdeal A).map (algebraMap A R)) R :=
    IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hle)
  haveI := hc
  exact GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal A)

end GlobalTheory.QuasiFiniteLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimLeOfIsEtaleCompletion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.ringKrullDim_le_of_isEtaleCompletion : ∀ (O A : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ψ : O →+* A) [IsLocalHom ψ], IsEtaleCompletion ψ → ringKrullDim A ≤ ringKrullDim O := by
  intro O A _ _ _ _ _ _ ψ _ h
  letI : Algebra O A := ψ.toAlgebra
  have hmap : (maximalIdeal O).map (algebraMap O A) = maximalIdeal A := h.2.1
  have hlo : (maximalIdeal A).LiesOver (maximalIdeal O) := by
    refine ⟨?_⟩
    rw [Ideal.under_def]
    exact (IsLocalRing.maximalIdeal_comap ψ).symm
  have key := Ideal.height_le_height_add_of_liesOver (maximalIdeal O) (maximalIdeal A)
  rw [hmap, Ideal.map_quotient_self] at key
  have h0 : (⊥ : Ideal (A ⧸ maximalIdeal A)).height = 0 := by
    simp
  rw [h0, add_zero] at key
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact_mod_cast key
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiStarMulKillsPointOfTrivialPairing
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

open GlobalTheory.CechPic

theorem lam_rosati_field (K : Type) [Field K] (P : PolAV (Sp K)) (O : Type) [Ring O] [StarRing O] (oA : P.OAct O)
    (o : O) {T' : Over (Sp K)} (x z : T' ⟶ P.A) :
    haveI := P.isAb.comm
    lam (cls P.L P.isLB) (x ≫ oA.act (star o)) z = lam (cls P.L P.isLB) x (z ≫ oA.act o) := by
  haveI := P.isAb.comm
  haveI := oA.hom (star o)
  haveI := oA.hom o
  have hr := oA.rosati (star o)
  rw [star_star] at hr
  obtain ⟨u, hu, -⟩ := exists_ros GlobalTheory.globalFns_holds P.isAb P.isLB _ _ hr
  have h := GlobalTheory.EndRosati.cls_of_rosati P.isLB u hu x z
  show _ - _ - _ + _ = _ - _ - _ + _
  rw [h]

theorem kill_of_lam_triv : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (O : Type) [Ring O] [StarRing O] (oA : P.OAct O) (e f : O) (H : Over (Sp K)) (a : H ⟶ P.A) (r : P.A ⟶ H), r ≫ a = oA.act e → ∀ (T : Over (Sp K)) (y : T ⟶ P.A), (∃ t : LB.Gen (letI := P.isAb.comm; (abelian₂ P.A P.L).pull (lift (snd H T ≫ y) (fst H T ≫ a ≫ oA.act f) : H ⊗ T ⟶ G2 P.A).left), t.IsGen) → y ≫ oA.act (star e * star f) = toUnit T ≫ η[P.A] := by
  intro K _ P O _ _ oA e f H a r hra T y ⟨t, ht⟩
  haveI := P.isAb.comm
  have h0 : lam (cls P.L P.isLB) (snd H T ≫ y) (fst H T ≫ a ≫ oA.act f) = 0 := by
    have := (cls_eq_zero_iff (pull_isLB (GlobalTheory.FullSiegel.isLB_lam P.isLB) _)).2 ⟨t, ht⟩
    rwa [GlobalTheory.FullSiegel.cls_lam_pull P.isLB] at this
  have h1 : lam (cls P.L P.isLB) (fst T P.A ≫ y) ((snd T P.A ≫ oA.act e) ≫ oA.act f) = 0 := by
    have := congrArg (pull (lift (snd T P.A ≫ r) (fst T P.A)).left) h0
    rw [pull_lam, map_zero, lift_snd_assoc, lift_fst_assoc, Category.assoc, reassoc_of% hra] at this
    rw [Category.assoc]
    exact this
  have h2 := (lam_rosati_field K P O oA f _ _).trans h1
  have h3 := (lam_rosati_field K P O oA e _ (snd T P.A)).trans h2
  have hb : ((fst T P.A ≫ y) ≫ oA.act (star f)) ≫ oA.act (star e) = fst T P.A ≫ y ≫ oA.act (star e * star f) := by
    rw [oA.map_mul]; simp only [Category.assoc]
  rw [hb] at h3
  have h4 := congrArg (pull (lift (snd P.A T) (fst P.A T)).left) h3
  rw [pull_lam, map_zero, lift_fst_assoc, lift_snd] at h4
  have hg : ∃ t : ((abelian₂ P.A P.L).pull (lift (snd P.A T ≫ y ≫ oA.act (star e * star f)) (fst P.A T)).left).Gen,
      t.IsGen := by
    refine (cls_eq_zero_iff (pull_isLB (GlobalTheory.FullSiegel.isLB_lam P.isLB) _)).1 ?_
    rw [GlobalTheory.FullSiegel.cls_lam_pull P.isLB]
    exact h4
  exact (GlobalTheory.FullSiegel.eq_one_of_lam_triv P.isLB P.rigid P.ktriv T _ hg).trans (Hom.one_def ..)

end GlobalTheory.Mum
end
end

