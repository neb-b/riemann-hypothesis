module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDeltaPsi
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0029
public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusLiftLemmasOfAdmitted
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0644
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexEqLocalUnitaryIndexAtInert
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.InertLatIndex

open GlobalTheory.InertLoc Formalism.UG

theorem finPart_surjective (D : D7) : Function.Surjective (finPart D) := by
  intro b
  obtain ⟨a, ha⟩ := Algebra.TensorProduct.map_surjective (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
    (fun b => ⟨pairA D.host.F 0 b, rfl⟩) Function.surjective_id b
  exact ⟨a, ha⟩

theorem ker_finPart_le {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : AE D} {σ : LP D P →+* LP D P}
    {π : AE D →+* LP D P} (hC : Chart e σ π) : RingHom.ker (finPart D) ≤ RingHom.ker π := by
  intro a ha
  rw [RingHom.mem_ker] at ha ⊢
  refine (hC.2.2.1 a).2 ?_
  refine GlobalTheory.LatVac.tensor_prod_eq_zero (F := D.host.F) (A := _) (B := _) _ ?_ ?_
  · show infPart D (e * a) = 0
    rw [map_mul, hC.1.2.2, zero_mul]
  · show finPart D (e * a) = 0
    rw [map_mul, ha, mul_zero]

theorem mem_span_basisFun {K : Type} [Field K] (O : ValuationSubring K) {n : Type} [Fintype n] [DecidableEq n]
    (z : n → K) : z ∈ Submodule.span O (Set.range (Pi.basisFun K n)) ↔ ∀ i, z i ∈ O := by
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro i
      rw [Pi.basisFun_apply]
      by_cases hij : j = i
      · subst hij; simp
      · simp [Pi.single_apply, Ne.symm hij]
    | zero => intro i; simp
    | add x y _ _ hx hy => intro i; exact add_mem (hx i) (hy i)
    | smul a x _ hx => intro i; exact mul_mem a.2 (hx i)
  · intro hz
    have : z = ∑ i, (⟨z i, hz i⟩ : O) • Pi.basisFun K n i := by
      conv_lhs => rw [← (Pi.basisFun K n).sum_repr z]
      rfl
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem finMat_apply {D : D7} {W : HSp D} (x : GA D W) (i j : Fin W.rank) :
    finMat D.sp.cm.sig W.gram x i j = finPart D (Formalism.L2.Theta.mt W x i j) := rfl

theorem finMat_sub_one_eq {D : D7} {W : HSp D} {e : AE D} (x : GA D W) (hx : SuppF W e x) (i j : Fin W.rank) :
    finMat D.sp.cm.sig W.gram x i j - (1 : Matrix (Fin W.rank) (Fin W.rank)
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) i j =
      finPart D e * (finMat D.sp.cm.sig W.gram x i j - (1 : Matrix (Fin W.rank) (Fin W.rank)
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) i j) := by
  have h1ij : (1 : Matrix (Fin W.rank) (Fin W.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) i j =
      finPart D ((1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) i j) := by
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  rw [h1ij, finMat_apply, ← RingHom.map_sub, ← RingHom.map_mul, ← Matrix.sub_apply, hx i j]

theorem finMat_mulVec_fix {D : D7} {W : HSp D} {e : AE D} (x : GA D W) (hx : SuppF W e x)
    (y : Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    finMat D.sp.cm.sig W.gram x *ᵥ (y - finPart D e • y) = y - finPart D e • y := by
  funext i
  have key : ∀ j, finMat D.sp.cm.sig W.gram x i j * (y - finPart D e • y) j =
      (1 : Matrix (Fin W.rank) (Fin W.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) i j *
        (y - finPart D e • y) j := by
    intro j
    have := finMat_sub_one_eq x hx i j
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (y j) * this
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl (fun j _ => key j)]
  simp [Matrix.one_apply]

theorem inv_mulVec_conj {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n] (β g : GL n K) (w : n → K) :
    (β⁻¹).1 *ᵥ ((β.1 * g.1 * (β⁻¹).1) *ᵥ w) = g.1 *ᵥ ((β⁻¹).1 *ᵥ w) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]


set_option maxHeartbeats 1000000 in
theorem latIndex_eq_of_chart {D : D7} {W : HSp D} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : AE D}
    {σ : LP D P →+* LP D P} {π : AE D →+* LP D P} {β : GL (Fin W.rank) (LP D P)}
    (α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (hα : finPart D e = α ⊗ₜ[D.host.F] (1 : D.host.E))
    (hαint : ∀ a ∈ intAf D.host.F, α * a ∈ intAf D.host.F)
    (hC : Chart e σ π) (hF : Frame W e σ π β) (x : GA D W) (hx : SuppF W e x) (g : GL (Fin W.rank) (LP D P))
    (hxg : (Formalism.L2.Theta.mt W x).map π = β.1 * g.1 * (β⁻¹).1) :
    latIndex W x = ((Submodule.span (P.adicCompletionIntegers D.host.E)
        (Set.range (Pi.basisFun (LP D P) (Fin W.rank)))).map
        ((g.1 : Matrix (Fin W.rank) (Fin W.rank) (LP D P)).mulVecLin.restrictScalars
          (P.adicCompletionIntegers D.host.E))).toAddSubgroup.relIndex
      (Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (LP D P) (Fin W.rank)))).toAddSubgroup := by
  let πf : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →+* LP D P :=
    (RingHom.liftOfSurjective (finPart D) (finPart_surjective D)) ⟨π, ker_finPart_le hC⟩
  have hπf : ∀ a, πf (finPart D a) = π a := fun a => RingHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hπe : π e = 1 := by
    have h0 : e * (e - 1) = 0 := by rw [mul_sub, hC.1.1, mul_one, sub_self]
    have := (hC.2.2.1 (e - 1)).2 h0
    rwa [RingHom.map_sub, RingHom.map_one, sub_eq_zero] at this
  let T : (Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+
      (Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    (finMat D.sp.cm.sig W.gram x).mulVecLin.toAddMonoidHom
  let p : (Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+
      (Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := DistribSMul.toAddMonoidHom _ (finPart D e)
  let Φ : (Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin W.rank → LP D P) :=
    ((β⁻¹).1 : Matrix (Fin W.rank) (Fin W.rank) (LP D P)).mulVecLin.toAddMonoidHom.comp
      (πf.toAddMonoidHom.compLeft (Fin W.rank))
  let h : (Fin W.rank → LP D P) →+ (Fin W.rank → LP D P) :=
    ((g.1 : Matrix (Fin W.rank) (Fin W.rank) (LP D P)).mulVecLin.restrictScalars
      (P.adicCompletionIntegers D.host.E)).toAddMonoidHom
  have hΦ : ∀ y, Φ y = (β⁻¹).1 *ᵥ (fun k => πf (y k)) := fun y => rfl
  have h1 : ∀ y ∈ Formalism.L2.NTheta.LamHat W, p y ∈ Formalism.L2.NTheta.LamHat W := by
    have hle : Formalism.L2.NTheta.LamHat W ≤ (Formalism.L2.NTheta.LamHat W).comap p := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨a, ha, z, hz, rfl⟩
      show p _ ∈ Formalism.L2.NTheta.LamHat W
      apply AddSubgroup.subset_closure
      refine ⟨α * a, hαint a ha, z, hz, ?_⟩
      funext i
      show finPart D e * (a ⊗ₜ[D.host.F] z i) = _
      rw [hα, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact fun y hy => hle hy
  have h2 : ∀ y, T (p y) = p (T y) := fun y => by
    show finMat D.sp.cm.sig W.gram x *ᵥ (finPart D e • y) = finPart D e • (finMat D.sp.cm.sig W.gram x *ᵥ y)
    exact Matrix.mulVec_smul _ _ _
  have h3 : ∀ y, T (y - p y) = y - p y := fun y => finMat_mulVec_fix x hx y
  have h4 : ∀ y, Φ y = 0 → p y = 0 := by
    intro y hy
    have h0 : ∀ k, πf (y k) = 0 := by
      intro k
      have := congrArg (fun w => β.1 *ᵥ w) hy
      simp only [hΦ, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at this
      exact congrFun this k
    funext k
    obtain ⟨a, ha⟩ := finPart_surjective D (y k)
    have hπa : π a = 0 := by rw [← hπf, ha]; exact h0 k
    show finPart D e * y k = 0
    rw [← ha, ← RingHom.map_mul, (hC.2.2.1 a).1 hπa, RingHom.map_zero]
  have h5 : ∀ y, Φ (T y) = h (Φ y) := by
    intro y
    have hmap : (finMat D.sp.cm.sig W.gram x).map πf = β.1 * g.1 * (β⁻¹).1 := by
      rw [← hxg]
      exact Matrix.ext fun i j => hπf _
    have hT : (fun k => πf ((finMat D.sp.cm.sig W.gram x *ᵥ y) k)) =
        (finMat D.sp.cm.sig W.gram x).map πf *ᵥ (fun k => πf (y k)) :=
      funext fun k => RingHom.map_mulVec πf _ y k
    show Φ (finMat D.sp.cm.sig W.gram x *ᵥ y) = g.1 *ᵥ Φ y
    rw [hΦ, hΦ, hT, hmap]
    exact inv_mulVec_conj β g _
  have hmapΦ : (Formalism.L2.NTheta.LamHat W).map Φ =
      (Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (LP D P) (Fin W.rank)))).toAddSubgroup := by
    ext z
    rw [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]
    refine Iff.trans ?_ (mem_span_basisFun _ z).symm
    constructor
    · rintro ⟨y, hy, rfl⟩
      choose a ha using fun k => finPart_surjective D (y k)
      have hpy : (fun i => finPart D (e * a i)) ∈ Formalism.L2.NTheta.LamHat W := by
        have := h1 y hy
        convert this using 1
        funext i
        show finPart D (e * a i) = finPart D e * y i
        rw [RingHom.map_mul, ha]
      have hi := (hF.2 a).1 hpy
      have hz : Φ y = (β⁻¹).1 *ᵥ fun k => π (a k) := by
        rw [hΦ]
        congr 1
        funext k
        rw [← ha, hπf]
      rw [hz]
      exact hi
    · intro hz
      choose a ha using fun k => hC.2.1 ((β.1 *ᵥ z) k)
      have hb : (β⁻¹).1 *ᵥ (fun k => π (a k)) = z := by
        have : (fun k => π (a k)) = β.1 *ᵥ z := funext ha
        rw [this, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      refine ⟨fun i => finPart D (e * a i), (hF.2 a).2 ?_, ?_⟩
      · rw [hb]; exact hz
      · rw [hΦ]
        convert hb using 2
        funext k
        rw [hπf, RingHom.map_mul, hπe, one_mul]
  unfold latIndex
  rw [GlobalTheory.index_transfer_along_projection (Formalism.L2.NTheta.LamHat W) T p Φ h h1 h2 h3 h4 h5, hmapΦ,
    Submodule.map_toAddSubgroup]
  rfl

theorem latIndex_chart_eq : ∀ (D : D7) (W : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (σ : GlobalTheory.InertLoc.LP D P →+* GlobalTheory.InertLoc.LP D P) (π : AE D →+* GlobalTheory.InertLoc.LP D P) (β : GL (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) (ι : Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) →* GA D W), GlobalTheory.InertLoc.Chart (algebraMap (AF D.host.F) (AE D) ε) σ π → GlobalTheory.InertLoc.Frame W (algebraMap (AF D.host.F) (AE D) ε) σ π β → GlobalTheory.InertLoc.GrpChart W (algebraMap (AF D.host.F) (AE D) ε) σ π β ι → ∀ (g : Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P))), latIndex W (ι g) = ((Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (GlobalTheory.InertLoc.LP D P) (Fin W.rank)))).map (((g : GL (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P)).mulVecLin.restrictScalars (P.adicCompletionIntegers D.host.E))).toAddSubgroup.relIndex (Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (GlobalTheory.InertLoc.LP D P) (Fin W.rank)))).toAddSubgroup := by
  intro D W v ε hε P σ π β ι hC hF hG g
  obtain ⟨α, hεα, hα1, hα0⟩ := hε
  have hα : finPart D (algebraMap (AF D.host.F) (AE D) ε) = α ⊗ₜ[D.host.F] (1 : D.host.E) := by
    subst hεα; rfl
  have hαint : ∀ a ∈ intAf D.host.F, α * a ∈ intAf D.host.F := by
    intro a ha w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw; rw [hα1, one_mul]; exact ha w
    · rw [hα0 w hw, zero_mul]; exact zero_mem _
  exact latIndex_eq_of_chart α hα hαint hC hF (ι g) (hG.1 g) g.1 (hG.2.1 g)

end GlobalTheory.InertLatIndex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremCConst25OfHypotheses
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem theoremC_of_admitted_inputs :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    ∀ (CR CA CB CK : ℝ), LiftingTheory.adm23 D HW F → Formalism.MainNotions.N.LetterConditionGlobal D HW F →
      ElementDenominator.HerrClassNaturalExtension D.loc D.locA HW F → CrystallineLiftingBounds.adm22 D HW F → InvariantsGenerators.LitFont D HW F →
      RamifiedCoefficientChains.Stmt D HW F Cm 25 CR CA CB CK :=
  fun D HW F Cm CR CA CB CK h23 hC4 hHerr a22 hFont =>
    Formalism.MainNotions.RamifiedCoefficientChains.Asm.theorem_of_literature_hypotheses D HW F Cm CR CA CB CK h23 hC4 hHerr a22 hFont

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeLocalGlobal
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Polynomial

namespace GlobalTheory.TypeAbove

theorem conj_over_split (D : D7) {p : ℕ} {w w' : PlE D.host} (hw : w ∈ placesOver D.host.E p)
    (hs : IsSplitPl D.host w) (hc : IsConjPl D.host w w') :
    w' ∈ placesOver D.host.E p ∧ IsSplitPl D.host w' := by
  have h := (GlobalTheory.ConjPlaceOff.isConjPl_iff D w w').1 hc
  refine ⟨?_, ?_⟩
  · have e := (h ((p : ℕ) : 𝓞 D.host.E)).1 hw
    rwa [map_natCast] at e
  · obtain ⟨x, hx, hcx⟩ := (GlobalTheory.ConjPlaceOff.isSplitPl_iff D w).1 hs
    exact (GlobalTheory.ConjPlaceOff.isSplitPl_iff D w').2 ⟨_, (h x).1 hx, fun h' => hcx ((h _).2 h')⟩

end GlobalTheory.TypeAbove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedWeilDeligneEqDiagonalInv
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem unr_eq_diag_inv : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (y : WD h), y.unr → ∃ α : Fin y.lpDim → ℂˣ, y = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  intro E Ω _ _ _ _ _ A w h y hy
  obtain ⟨n, c, rfl⟩ := GlobalTheory.WeilDeligne.Unram.exists_diag hy
  have hn : (WD.mk (WDRep.diag h c)).lpDim = n := by simp
  refine ⟨fun i => (c (Fin.cast hn i))⁻¹, ?_⟩
  simp only [inv_inv]
  refine WD.sound ⟨LinearEquiv.funCongrLeft ℂ ℂ (finCongr hn), fun σ v => funext fun k => ?_,
    fun v => by simp⟩
  simp [LinearEquiv.funCongrLeft_apply]

end GlobalTheory.LocLanglands
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationEqOneOfCongruentGlobalApprox
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory
namespace OrdZeroUnit

variable {E : Type} [Field E] [NumberField E]

theorem norm_modEq_one (a : ℕ) (y : 𝓞 E) :
    (((Algebra.norm ℤ (1 + (a : 𝓞 E) * y) : ℤ)) : ZMod a) = 1 := by
  classical
  let b := Module.Free.chooseBasis ℤ (𝓞 E)
  rw [Algebra.norm_eq_matrix_det b, ← eq_intCast (Int.castRingHom (ZMod a)), RingHom.map_det]
  have : (Int.castRingHom (ZMod a)).mapMatrix (Algebra.leftMulMatrix b (1 + (a : 𝓞 E) * y)) = 1 := by
    rw [map_add (f := _), map_one, map_mul, map_natCast, map_add (f := _), map_one, map_mul, map_natCast,
      ← map_natCast (algebraMap (ZMod a) (Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 E))
        (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (ZMod a))), ZMod.natCast_self, map_zero, zero_mul, add_zero]
  rw [this, Matrix.det_one]

theorem isUnit_of_valuation_eq_one (z : E) (hz : z ≠ 0) (h : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E z = 1) :
    ∃ u : 𝓞 E, IsUnit u ∧ algebraMap (𝓞 E) E u = z := by
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E z (fun v => (h v).le)
  obtain ⟨y', hy'⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E z⁻¹
    (fun v => by rw [map_inv₀, h v, inv_one])
  have hyy : y * y' = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    rw [map_mul, hy, hy', mul_inv_cancel₀ hz, map_one]
  exact ⟨y, ⟨⟨y, y', hyy, by rw [mul_comm]; exact hyy⟩, rfl⟩, hy⟩

end OrdZeroUnit
end GlobalTheory

namespace GlobalTheory
namespace OrdZeroUnit

theorem valuation_eq_one_of_approx : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E),
    x ≠ 0 → Valued.v x ≤ 1 → (∀ a : ℕ, 0 < a → ∀ t : w.adicCompletion E, t ≠ 0 → ∃ k : Eˣ,
      (∀ v : HeightOneSpectrum (𝓞 E), v ≠ w →
        v.valuation E (((k : E) - 1) / (a : E)) ≤ 1 ∧ v.valuation E ((k : E)⁻¹) ≤ 1) ∧
      Valued.v (algebraMap E (w.adicCompletion E) (k : E) - x) ≤ Valued.v t) → Valued.v x = 1 := by
  intro E _ _ w x hx0 hx1 hyp
  by_contra hne
  have hlt : Valued.v x < 1 := lt_of_le_of_ne hx1 hne
  have hxpos : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
  have ht0 : x * x ≠ 0 := mul_ne_zero hx0 hx0
  have htx : Valued.v (x * x) < Valued.v x := by
    rw [map_mul]
    calc Valued.v x * Valued.v x < 1 * Valued.v x := mul_lt_mul_of_pos_right hlt (zero_lt_iff.2 hxpos)
      _ = Valued.v x := one_mul _

  have hw_eq : ∀ k : E, Valued.v (algebraMap E (w.adicCompletion E) k - x) ≤ Valued.v (x * x) →
      w.valuation E k = Valued.v x := by
    intro k hk
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact Valuation.map_eq_of_sub_lt _ (lt_of_le_of_lt hk htx)

  have hoff : ∀ (a : ℕ), 0 < a → ∀ (k : E), k ≠ 0 → ∀ v : HeightOneSpectrum (𝓞 E),
      v.valuation E ((k - 1) / (a : E)) ≤ 1 → v.valuation E k⁻¹ ≤ 1 →
      v.valuation E k = 1 ∧ v.valuation E (k - 1) ≤ 1 := by
    intro a ha k hk0 v h1 h2
    have hva : v.valuation E (a : E) ≤ 1 := by
      rw [← map_natCast (algebraMap (𝓞 E) E)]; exact v.valuation_le_one _
    have ha0 : (a : E) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'
    have hk1 : v.valuation E (k - 1) ≤ 1 := by
      have : k - 1 = ((k - 1) / a) * a := by field_simp
      rw [this, map_mul]
      calc v.valuation E ((k - 1) / a) * v.valuation E (a : E) ≤ 1 * 1 := mul_le_mul' h1 hva
        _ = 1 := one_mul _
    have hk : v.valuation E k ≤ 1 := by
      have : k = (k - 1) + 1 := by ring
      rw [this]
      exact (Valuation.map_add _ _ _).trans (max_le hk1 (by rw [map_one]))
    refine ⟨le_antisymm hk ?_, hk1⟩
    calc 1 = v.valuation E (k * k⁻¹) := by rw [mul_inv_cancel₀ hk0, map_one]
      _ = v.valuation E k * v.valuation E k⁻¹ := map_mul _ _ _
      _ ≤ v.valuation E k * 1 := mul_le_mul' le_rfl h2
      _ = v.valuation E k := mul_one _

  obtain ⟨k₀, hk₀off, hk₀w⟩ := hyp 1 one_pos (x * x) ht0
  have hw0 := hw_eq _ hk₀w
  have hk₀0 : (k₀ : E) ≠ 0 := k₀.ne_zero
  have hoff0 : ∀ v, v ≠ w → v.valuation E (k₀ : E) = 1 := fun v hv =>
    (hoff 1 one_pos _ hk₀0 v (hk₀off v hv).1 (hk₀off v hv).2).1
  obtain ⟨k₀', hk₀'⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E (k₀ : E) (fun v => by
    by_cases hv : v = w
    · subst hv; rw [hw0]; exact hx1
    · exact (hoff0 v hv).le)
  set R : ℕ := (Algebra.norm ℤ k₀').natAbs with hR
  set q : ℕ := Ideal.absNorm w.asIdeal with hq
  have hqmem : (q : 𝓞 E) ∈ w.asIdeal := Ideal.absNorm_mem _
  have hqpos : 0 < q := Nat.pos_of_ne_zero (fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h))
  set a : ℕ := q * (R + 1) + 1 with ha
  have hapos : 0 < a := Nat.succ_pos _
  have hanot : (a : 𝓞 E) ∉ w.asIdeal := by
    intro h
    have h1 : (1 : 𝓞 E) ∈ w.asIdeal := by
      have := w.asIdeal.sub_mem h (w.asIdeal.mul_mem_right (((R + 1 : ℕ)) : 𝓞 E) hqmem)
      rw [ha] at this; push_cast at this; simpa using this
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hwa : w.valuation E (a : E) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 E) E) a]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 hanot

  obtain ⟨k, hkoff, hkw⟩ := hyp a hapos (x * x) ht0
  have hwk := hw_eq _ hkw
  have hk0 : (k : E) ≠ 0 := k.ne_zero
  have hoffk : ∀ v, v ≠ w → v.valuation E (k : E) = 1 ∧ v.valuation E ((k : E) - 1) ≤ 1 :=
    fun v hv => hoff a hapos _ hk0 v (hkoff v hv).1 (hkoff v hv).2
  obtain ⟨kk, hkk⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E (k : E) (fun v => by
    by_cases hv : v = w
    · subst hv; rw [hwk]; exact hx1
    · exact (hoffk v hv).1.le)

  obtain ⟨u, hu, hue⟩ := isUnit_of_valuation_eq_one ((k : E) / k₀) (div_ne_zero hk0 hk₀0) (fun v => by
    rw [map_div₀]
    by_cases hv : v = w
    · subst hv; rw [hw0, hwk, div_self hxpos]
    · rw [(hoffk v hv).1, hoff0 v hv, div_one])
  have hkku : kk = u * k₀' := by
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    rw [map_mul, hkk, hue, hk₀', div_mul_cancel₀ _ hk₀0]
  have hNk : (Algebra.norm ℤ kk).natAbs = R := by
    rw [hkku, map_mul, Int.natAbs_mul, Int.isUnit_iff_natAbs_eq.1 (hu.map _), one_mul]

  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E (((k : E) - 1) / (a : E))
    (fun v => by
      by_cases hv : v = w
      · subst hv
        rw [map_div₀, hwa, div_one, ← hkk, ← map_one (algebraMap (𝓞 E) E), ← map_sub]
        exact v.valuation_le_one _
      · exact (hkoff v hv).1)
  have hkky : kk = 1 + (a : 𝓞 E) * y := by
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    have ha0 : (a : E) ≠ 0 := Nat.cast_ne_zero.2 hapos.ne'
    rw [map_add (f := _), map_one, map_mul, map_natCast, hy, hkk]
    field_simp
    ring
  have hcong := norm_modEq_one a y
  rw [← hkky] at hcong
  have hdvd : (a : ℤ) ∣ Algebra.norm ℤ kk - 1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub 1 _ a).1 (by rw [hcong, Int.cast_one])
  have hN1 : Algebra.norm ℤ kk = 1 := by
    obtain ⟨c, hc⟩ := hdvd
    have hA : ((R : ℤ) + 2) ≤ (a : ℤ) := by
      rw [ha]; push_cast
      nlinarith [(Nat.one_le_cast (α := ℤ)).2 hqpos, (Nat.cast_nonneg R : (0 : ℤ) ≤ R)]
    have hR0 : (0 : ℤ) ≤ R := Nat.cast_nonneg R
    rcases Int.natAbs_eq (Algebra.norm ℤ kk) with h | h <;> rw [hNk] at h <;> rw [h] at hc ⊢
    · rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
      · nlinarith
      · subst hc0; linarith
      · nlinarith
    · rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
      · nlinarith
      · subst hc0; linarith
      · nlinarith

  have hunit : IsUnit kk := by
    rw [← Ideal.span_singleton_eq_top, ← Ideal.absNorm_eq_one_iff, Ideal.absNorm_span_singleton, hN1]
    rfl
  have hmem : kk ∈ w.asIdeal := by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
    change w.valuation E (algebraMap (𝓞 E) E kk) < 1
    rw [hkk, hwk]; exact hlt
  exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hunit)

end OrdZeroUnit
end GlobalTheory
end

