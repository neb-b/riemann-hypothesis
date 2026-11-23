module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
public import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsThetaPt
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif.ThetaPtEx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

theorem exists_chart_top {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (p : Sp ℂ ⟶ X) :
    ∃ j, ⊤ ≤ p ⁻¹ᵁ L.U j := by
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1
    (hL.cover.ge (Set.mem_univ (p (default : PrimeSpectrum ℂ))))
  refine ⟨j, fun q _ => ?_⟩
  obtain rfl : q = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact hj

theorem exists_gen (hT : Out.SecTwistSt) (y : Sp ℂ ⟶ Xo.X) {Z : Type} (ex : Z → (Over.mk y ⟶ Xo.univ.t.G))
    (θ : Z → ℂ) (fr : Xo.univ.t.PP.L.ι → Z → ℂ) (κ : ℂ) (hκ : κ ≠ 0) (hθ : ∃ z, θ z ≠ 0)
    (hfr : ∀ j z, ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0)
    (s : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom y)).Sec)
    (hs : ∀ j z (x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom y),
        x ≫ pullback.fst _ _ = (ex z).left → x ≫ pullback.snd _ _ = 𝟙 _ →
        ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
        valAt' x ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom y)).U (fun _ => j))
          (s.f (fun _ => j)) = θ z * fr j z) :
    ∃ t : LB.Sec (PPx y), SecGen y t ∧
      ∀ j z (pt : Sp ℂ ⟶ Gx y), pt ≫ Formalism.L2.PjFree.gxFst y = (ex z).left → pt ≫ Formalism.L2.PjFree.gxSnd y = 𝟙 (Sp ℂ) →
        ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
        valAt' pt ((PPx y).U (fun _ => j)) (t.f (fun _ => j)) = κ * θ z * fr j z := by
  obtain ⟨s', hs'⟩ := _root_.GlobalTheory.FibreSection.exists_sec_same_values E H Dw l Xo y s
  have hw : ∀ z, (ex z).left ≫ Xo.univ.t.G.hom = 𝟙 (Sp ℂ) ≫ y := fun z =>
    (Over.w (ex z)).trans (Category.id_comp y).symm
  have key : ∀ j z (pt : Sp ℂ ⟶ Gx y), pt ≫ Formalism.L2.PjFree.gxFst y = (ex z).left → pt ≫ Formalism.L2.PjFree.gxSnd y = 𝟙 (Sp ℂ) →
      ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx y).U (fun _ => j)) ((SecPull.scalSec y κ s').f (fun _ => j)) = κ * θ z * fr j z := by
    intro j z pt h1 h2 h3
    have e1 := (_root_.GlobalTheory.sec_values_complex_fibre hT E H Dw l Xo y s').1 κ (fun _ => j) pt h2
    have e2 := hs' j pt (pullback.lift (ex z).left (𝟙 _) (hw z)) ((pullback.lift_fst _ _ _).trans h1.symm)
      (pullback.lift_snd _ _ _) h2
    have e3 := hs j z (pullback.lift (ex z).left (𝟙 _) (hw z)) (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _) h3
    refine e1.trans ?_
    rw [e2, e3, mul_assoc]
  refine ⟨SecPull.scalSec y κ s', ?_, key⟩
  obtain ⟨z, hz⟩ := hθ
  obtain ⟨j, hj⟩ := exists_chart_top Xo.univ.t.PP.isLB (ex z).left
  let pt : Sp ℂ ⟶ Gx y := pullback.lift (f := (Over.mk y).hom) (g := Xo.univ.t.G.hom) (𝟙 _) (ex z).left (hw z).symm
  have h1 : pt ≫ Formalism.L2.PjFree.gxFst y = (ex z).left := pullback.lift_snd _ _ _
  have h2 : pt ≫ Formalism.L2.PjFree.gxSnd y = 𝟙 (Sp ℂ) := pullback.lift_fst _ _ _
  refine (_root_.GlobalTheory.sec_values_complex_fibre hT E H Dw l Xo y _).2.1.2 ⟨fun _ => j, pt, h2, ?_⟩
  rw [key j z pt h1 h2 hj]
  exact mul_ne_zero (mul_ne_zero hκ hz) (hfr j z hj)

theorem exists_thetaPt : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ κ : ℂ, κ ≠ 0 → ∃ y : FrPt Xo c (CAt σ), IsThetaPt T b κ y := by
  intro hT E _ _ _ H Dw l Xo c σ g e F r M k T b hb κ hκ
  have hP := T.isPer _ hb
  obtain ⟨u, hu, htan, heig, hbas⟩ := GlobalTheory.T.exists_tangent_eigenbasis_exponential E H Dw l Xo c σ g e F k _ hP
  obtain ⟨s, hs⟩ := T.fr_sec b hb
  obtain ⟨hdet, hsym, hpos, -⟩ := T.norm b hb
  obtain ⟨w, hw⟩ := ((_root_.GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g T.c₁ T.c₂ T.half₁ T.half₂).1 _ hsym hpos).2
  have hθ : ∃ z, thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z) ≠ 0 :=
    ⟨(T.h b)⁻¹ *ᵥ w, by rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]⟩
  obtain ⟨t, ht, hval⟩ := exists_gen hT (F.u k (T.Pf (T.co b))) (F.ex k (T.Pf (T.co b)))
    (fun z => thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z)) (fun j z => T.fr j (b, z)) κ hκ hθ
    (fun j z hz => T.fr_ne j b z hb hz) s hs
  exact ⟨⟨F.u k (T.Pf (T.co b)), F.over_σ k _ hP, u, htan, heig, hbas, t, ht⟩, rfl, hu, hval⟩

end GlobalTheory.FrameUnif.ThetaPtEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsValuationSubringComplexComapValEq
section
namespace GlobalTheory

theorem exists_valuationSubring_complex_comap_val_eq (F : IntermediateField ℚ ℂ)
    (U : ValuationSubring F) (p : ℕ) (hp : (p : F) ∈ U.nonunits) :
    ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits ∧ W.comap F.val.toRingHom = U := by
  obtain ⟨W, hW⟩ : ∃ W : ValuationSubring ℂ, W.comap (algebraMap F ℂ) = U :=
    exists_valuationSubring_comap_eq U _
  refine ⟨W, ?_, hW⟩
  rw [ValuationSubring.mem_nonunits_iff_or] at hp ⊢
  rcases hp with h | h
  · left
    simpa using congrArg (algebraMap F ℂ) h
  · right
    rw [← hW, ValuationSubring.mem_comap] at h
    simpa using h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExtendGenAndCorrOfGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Exist

theorem extendGen : extendGenSt.{0} :=
  (GlobalTheory.cubical_extends_and_extendGen GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
    GlobalTheory.GenExtend.existsUnique_gen_extend).2

end GlobalTheory.Exist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteDimensionalCuspSectionsVanishingOffDomainStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_cuspSections_vanishing_offDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Comp : Type) [Fintype Comp] (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r) (W : Submodule ℂ (Formalism.L2.PjFree.FDSec X)), W ≤ Formalism.L2.PjFree.holSub X la → (∀ P ∈ W, ∀ k, ∀ x ∉ (X k).dom, P k x = 0) → FiniteDimensional ℂ W := by
  first | exact @GlobalTheory.CuspSecFinData.finiteDimensional_of_le_holSub | exact GlobalTheory.CuspSecFinData.finiteDimensional_of_le_holSub | (intros; apply GlobalTheory.CuspSecFinData.finiteDimensional_of_le_holSub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFramesDifferByUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.IntLie

section Pull

variable {S' S₀ : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S₀} [GrpObj G] {f : S' ⟶ S₀}
  {φ : G'.left ⟶ G.left}

theorem one_push₀ (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  let e0 : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    show ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = T.hom ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
  have h1 : (e0 * e0).left = ((1 : T ⟶ G') * 1).left ≫ φ := h.2 T 1 1 e0 e0 rfl rfl
  rw [_root_.mul_one] at h1
  have h2 : e0 * e0 = e0 := Over.OverMorphism.ext h1
  have h3 : e0 = 1 := mul_eq_left.1 h2
  rw [← h3]
  rfl

theorem one_push (h : IsGrpPullback G' G f φ) (T' : Over S') (T : Over S₀) (g : T'.left ⟶ T.left)
    (hg : g ≫ T.hom = T'.hom ≫ f) : (1 : T' ⟶ G').left ≫ φ = g ≫ (1 : T ⟶ G).left := by
  let δ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk g hg
  rw [← one_push₀ h T', ← MonObj.comp_one δ]
  rfl

theorem mul_push (h : IsGrpPullback G' G f φ) (T' : Over S') (T : Over S₀) (g : T'.left ⟶ T.left)
    (hg : g ≫ T.hom = T'.hom ≫ f) (a b : T' ⟶ G') (a₀ b₀ : T ⟶ G) (ha : a.left ≫ φ = g ≫ a₀.left)
    (hb : b.left ≫ φ = g ≫ b₀.left) : (a * b).left ≫ φ = g ≫ (a₀ * b₀).left := by
  let δ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk g hg
  rw [← h.2 T' a b (δ ≫ a₀) (δ ≫ b₀) ha.symm hb.symm, ← MonObj.comp_mul]
  rfl

theorem prod_push (h : IsGrpPullback G' G f φ) (T' : Over S') (T : Over S₀) (g : T'.left ⟶ T.left)
    (hg : g ≫ T.hom = T'.hom ≫ f) {m : ℕ} (a : Fin m → (T' ⟶ G')) (a₀ : Fin m → (T ⟶ G))
    (ha : ∀ j, (a j).left ≫ φ = g ≫ (a₀ j).left) :
    ((List.ofFn a).prod).left ≫ φ = g ≫ ((List.ofFn a₀).prod).left := by
  induction m with
  | zero => simpa using one_push h T' T g hg
  | succ m ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    exact mul_push h T' T g hg _ _ _ _ (ha 0) (ih _ _ fun j => ha j.succ)

theorem isIso_of_pull {G₁ G₂ : Over S₀} [GrpObj G₁] [GrpObj G₂] {ψ : G₁.left ⟶ G₂.left}
    (h : IsGrpPullback G₁ G₂ (𝟙 _) ψ) : IsIso ψ :=
  h.1.isIso_fst_of_isIso

end Pull

theorem spMap_comp₂ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem spMap_frac_cancel {V K A : Type} [CommRing V] [CommRing K] [Algebra V K] [IsFractionRing V K] [CommRing A]
    (g h : Sp A ⟶ Sp K) (e : g ≫ spMap (algebraMap V K) = h ≫ spMap (algebraMap V K)) : g = h := by
  rw [← Spec.map_preimage g, ← Spec.map_preimage h] at e ⊢
  simp only [spMap, ← Spec.map_comp] at e
  have e1 := Spec.map_injective e
  congr 1
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (nonZeroDivisors V)
  exact congrArg CommRingCat.Hom.hom e1

theorem dualMap_alg {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    (dualMap f).comp (algebraMap A (DualNumber A)) = (algebraMap B (DualNumber B)).comp f := by
  apply RingHom.ext
  intro r
  ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_epsMul {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    (dualMap f).comp (epsMul a) = (epsMul (f a)).comp (dualMap f) := by
  apply RingHom.ext
  intro r
  ext <;> simp [dualMap, epsMul, _root_.mul_comm]

theorem epsMul_alg {A : Type} [CommRing A] (a : A) :
    (epsMul a).comp (algebraMap A (DualNumber A)) = algebraMap A (DualNumber A) := by
  ext s <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem comb_generic {V K : Type} [CommRing V] [CommRing K] [Algebra V K] [IsFractionRing V K]
    {x : Sp K ⟶ Xo.X} {G : SAB H (Sp V)} {t : SAB H (Sp K)} (m₁ : SABMap t Xo.univ.t x)
    (m₂ : SABMap t G (spMap (algebraMap V K))) {m : ℕ} (ub : Fin m → (epsOver V V ⟶ G.G))
    (u' : Fin m → (Sp (DualNumber K) ⟶ t.G.left))
    (hu : ∀ j, u' j ≫ m₂.φ = spMap (dualMap (algebraMap V K)) ≫ (ub j).left)
    (w : epsOver V V ⟶ G.G) (w' : Sp (DualNumber K) ⟶ t.G.left)
    (hw : w' ≫ m₂.φ = spMap (dualMap (algebraMap V K)) ≫ w.left) (a : Fin m → V) (ha : IsComb ub a w) :
    IsCombAt x (fun j => u' j ≫ m₁.φ) (fun j => algebraMap V K (a j)) (w' ≫ m₁.φ) := by
  obtain ⟨U, hU, hwU⟩ := ha
  have hδ : spMap (dualMap (algebraMap V K)) ≫
      spMap ((algebraMap V (DualNumber V)).comp (algebraMap V V)) =
      spMap (algebraMap K (DualNumber K)) ≫ spMap (algebraMap V K) := by
    rw [spMap_comp₂, spMap_comp₂]
    show spMap ((dualMap (algebraMap V K)).comp (algebraMap V (DualNumber V))) = _
    rw [dualMap_alg]
  have hov : ∀ (z : epsOver V V ⟶ G.G) (z' : Sp (DualNumber K) ⟶ t.G.left),
      z' ≫ m₂.φ = spMap (dualMap (algebraMap V K)) ≫ z.left →
      z' ≫ t.G.hom = spMap (algebraMap K (DualNumber K)) := by
    intro z z' hz
    apply spMap_frac_cancel (V := V)
    rw [Category.assoc, ← m₂.cart.1.w, ← Category.assoc, hz, Category.assoc, Over.w z]
    exact hδ
  let T' : Over (Sp K) := Over.mk (spMap (algebraMap K (DualNumber K)))
  let Y : Fin m → (T' ⟶ t.G) := fun j => Over.homMk (spMap (epsMul (algebraMap V K (a j))) ≫ u' j) (by
    show (spMap (epsMul (algebraMap V K (a j))) ≫ u' j) ≫ t.G.hom = spMap (algebraMap K (DualNumber K))
    rw [Category.assoc, hov _ _ (hu j), spMap_comp₂, epsMul_alg])
  have hB := prod_push m₂.cart T' (epsOver V V) (spMap (dualMap (algebraMap V K))) hδ Y U (fun j => by
    show (spMap (epsMul (algebraMap V K (a j))) ≫ u' j) ≫ m₂.φ = _
    rw [Category.assoc, hu j, hU j, ← Category.assoc, ← Category.assoc, spMap_comp₂, spMap_comp₂,
      dualMap_epsMul])
  have hY : ((List.ofFn Y).prod).left = w' := by
    apply m₂.cart.1.hom_ext
    · rw [hB, ← hwU]
      exact hw.symm
    · rw [hov _ _ hw]
      exact Over.w _
  let Z : Fin m → (tEps x ⟶ Xo.univ.t.G) := fun j => Over.homMk ((Y j).left ≫ m₁.φ) (by
    show ((Y j).left ≫ m₁.φ) ≫ Xo.univ.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ x
    rw [Category.assoc, m₁.cart.1.w, ← Category.assoc, Over.w (Y j)]
    rfl)
  have hA := prod_push m₁.cart T' (tEps x) (𝟙 _) (Category.id_comp _) Y Z (fun j => (Category.id_comp _).symm)
  refine ⟨Z, fun j => Category.assoc _ _ _, ?_⟩
  rw [← hY]
  exact ((Category.id_comp _).symm.trans hA.symm)

theorem tan_eig_iff {V K : Type} [CommRing V] [Field K] [Algebra V K] (io : c.F →+* K) {G G₂ : SAB H (Sp V)}
    (n : SABMap G G₂ (𝟙 _)) (τ : E →+* ℂ) (w : epsOver V V ⟶ G.G) (w₂ : epsOver V V ⟶ G₂.G)
    (h : w.left ≫ n.φ = w₂.left) :
    (IsTan w ↔ IsTan w₂) ∧ (IsEigV c io G τ w ↔ IsEigV c io G₂ τ w₂) := by
  have := isIso_of_pull n.cart
  constructor
  · have h1 := one_push n.cart (ptOver V V) (ptOver V V) (𝟙 _) (by simp)
    rw [Category.id_comp] at h1
    unfold IsTan
    rw [← h, ← h1, ← Category.assoc]
    exact (cancel_mono n.cm.F).symm
  · unfold IsEigV
    refine forall_congr' fun a => forall_congr' fun z => forall_congr' fun _ => ?_
    rw [Over.comp_left, Over.comp_left, ← h, Category.assoc, ← n.act a, ← Category.assoc, ← Category.assoc]
    exact (cancel_mono n.cm.F).symm

theorem mul_eq_one_of_comb {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) {m : ℕ}
    (u u₂ : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (hu : ∀ i, IsTanAt x (u i))
    (huniq : ∀ i, ∃! a : Fin m → S, IsCombAt x u a (u i)) (A B : Matrix (Fin m) (Fin m) S)
    (hA : ∀ i, IsCombAt x u (A i) (u₂ i)) (hB : ∀ i, IsCombAt x u₂ (B i) (u i)) : B * A = 1 := by
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, -, -⟩ := GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo S x
  choose b hb using fun i => (htan _).1 (hu i)
  obtain rfl : u = fun i => v (b i) := funext fun i => (hb i).symm
  obtain rfl : u₂ = fun i => v (∑ j, A i j • b j) := funext fun i => (hcomb _ b _ _).1 (hA i)
  ext i k
  have h1 := (hcomb _ (fun i => ∑ j, A i j • b j) _ _).1 (hB i)
  have h2 : IsCombAt x (fun i => v (b i)) ((B * A) i) (v (b i)) := by
    refine (hcomb _ b _ _).2 (h1.trans (congrArg v ?_))
    simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    exact Finset.sum_comm
  have h3 : IsCombAt x (fun i => v (b i)) ((1 : Matrix (Fin m) (Fin m) S) i) (v (b i)) := by
    refine (hcomb _ b _ _).2 (congrArg v ?_)
    simp [Matrix.one_apply]
  exact congrFun ((huniq i).unique h2 h3) k

theorem integral_frames_differ_by_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y y' : FrPt Xo c T.Fr) (G G₂ : SAB H (Sp T.V)) (t t₂ : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t y.x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t₂ Xo.univ.t y'.x) (n₂ : SABMap t₂ G₂ (spMap (algebraMap T.V T.Fr))) (k : SABMap t t₂ (𝟙 _)) (n : SABMap G G₂ (𝟙 _)), y'.x = y.x → k.φ ≫ n₁.φ = m₁.φ → m₂.φ ≫ n.φ = k.φ ≫ n₂.φ → ∀ (ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G)) (ub₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G₂.G)), ((∀ τ i, IsTan (ub τ i)) ∧ (∀ τ i, IsEigV c io G τ (ub τ i)) ∧ (∀ τ (w : epsOver T.V T.V ⟶ G.G), IsTan w → IsEigV c io G τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub τ) a w) ∧ ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t.G.left, u' ≫ m₁.φ = y.u τ i ∧ u' ≫ m₂.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub τ i).left) → ((∀ τ i, IsTan (ub₂ τ i)) ∧ (∀ τ i, IsEigV c io G₂ τ (ub₂ τ i)) ∧ (∀ τ (w : epsOver T.V T.V ⟶ G₂.G), IsTan w → IsEigV c io G₂ τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub₂ τ) a w) ∧ ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t₂.G.left, u' ≫ n₁.φ = y'.u τ i ∧ u' ≫ n₂.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub₂ τ i).left) → ∀ τ : E →+* ℂ, ∃ A : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V, IsUnit A.det ∧ ∀ i, IsCombAt y.x (y.u τ) (fun j => algebraMap T.V T.Fr (A i j)) (y'.u τ i) := by
  intro E _ _ _ H Dw l Xo c T io
  let _ := io.toAlgebra
  intro y y' G G₂ t t₂ m₁ m₂ n₁ n₂ k n hx hk hn ub ub₂ ⟨ht, he, hb, hl⟩ ⟨ht₂, he₂, hb₂, hl₂⟩ τ
  have := isIso_of_pull n.cart
  have := isIso_of_pull k.cart
  have hnw : n.φ ≫ G₂.G.hom = G.G.hom := n.cart.1.w.trans (Category.comp_id _)
  choose u' hu1 hu2 using hl τ
  choose u₂ hv1 hv2 using hl₂ τ
  let w : Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G) := fun i => Over.homMk ((ub₂ τ i).left ≫ inv n.φ) (by
    rw [← hnw, Category.assoc, IsIso.inv_hom_id_assoc]
    exact Over.w _)
  have hw : ∀ i, (w i).left ≫ n.φ = (ub₂ τ i).left := fun i => by
    show ((ub₂ τ i).left ≫ inv n.φ) ≫ n.φ = _
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  let w₂ : Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G₂.G) := fun i => Over.homMk ((ub τ i).left ≫ n.φ) (by
    rw [Category.assoc, hnw]
    exact Over.w _)
  have hw₂ : ∀ i, (ub τ i).left ≫ n.φ = (w₂ i).left := fun i => rfl
  choose A hA using fun i => (hb τ (w i) ((tan_eig_iff io n τ _ _ (hw i)).1.2 (ht₂ τ i))
    ((tan_eig_iff io n τ _ _ (hw i)).2.2 (he₂ τ i))).exists
  choose B hB using fun i => (hb₂ τ (w₂ i) ((tan_eig_iff io n τ _ _ (hw₂ i)).1.1 (ht τ i))
    ((tan_eig_iff io n τ _ _ (hw₂ i)).2.1 (he τ i))).exists
  have hA' : ∀ i, IsCombAt y.x (y.u τ) (fun j => algebraMap T.V T.Fr (A i j)) (y'.u τ i) := by
    intro i
    have h := comb_generic m₁ m₂ (ub τ) u' hu2 (w i) (u₂ i ≫ inv k.φ) (by
      rw [← cancel_mono n.φ, Category.assoc, Category.assoc, hn, IsIso.inv_hom_id_assoc, hv2, Category.assoc,
        hw]) (A i) (hA i)
    rw [funext hu1, ← hk, Category.assoc, IsIso.inv_hom_id_assoc, hv1] at h
    exact h
  have hB' : ∀ i, IsCombAt y.x (y'.u τ) (fun j => algebraMap T.V T.Fr (B i j)) (y.u τ i) := by
    intro i
    have h := comb_generic n₁ n₂ (ub₂ τ) u₂ hv2 (w₂ i) (u' i ≫ k.φ) (by
      rw [Category.assoc, ← hn, ← Category.assoc, hu2, Category.assoc, hw₂]) (B i) (hB i)
    rw [funext hv1, Category.assoc, hk, hu1, hx] at h
    exact h
  refine ⟨Matrix.of A, ?_, hA'⟩
  have h1 := mul_eq_one_of_comb y.x (y.u τ) (y'.u τ) (y.tan τ)
    (fun i => y.basis τ _ (y.tan τ i) (y.eig τ i))
    ((Matrix.of A).map (algebraMap T.V T.Fr)) ((Matrix.of B).map (algebraMap T.V T.Fr)) hA' hB'
  have h2 : Matrix.of B * Matrix.of A = 1 := by
    apply Matrix.map_injective (IsFractionRing.injective T.V T.Fr)
    show (Matrix.of B * Matrix.of A).map (algebraMap T.V T.Fr) = (1 : Matrix _ _ T.V).map (algebraMap T.V T.Fr)
    rw [Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  exact Matrix.isUnit_det_of_left_inverse h2

end GlobalTheory.IntLie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ModuliExistsNumberFieldPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem moduli_exists_numberField_point :
    N1c → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → Formalism.L2.PjFree.XoNumPt Xo c := by
  intro hN E _ _ _ H Dw l Xo c hr
  obtain ⟨x⟩ := (PeriodExists.typeFn_period_exist E H Dw).2.2 hN hr l Xo c
  obtain ⟨L, _, _, hfin, y, hy, -⟩ := moduli_exists_algebraic_point E H Dw l Xo c ⊤ ⟨x, trivial⟩
  have : NumberField L := NumberField.of_module_finite c.F L
  refine ⟨L, inferInstance, this, algebraMap c.F L, y ≫ pullback.fst _ _, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hy]
  simp only [sOf, spMap, ← Spec.map_comp]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NatCastMemMaximalIdealOfOverLa
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

open IsDedekindDomain

theorem modelAtSt_of_good : PartI → N1ab → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → ∀ la, Formalism.L2.Pj.ModelAtSt Xo c la := by
  intro hP hN E _ _ _ H Dw l Xo c hpq hg la
  exact Formalism.L2.Pj.modelAtSt_of (Formalism.L2.Pj.partIAt_of hP hN Xo c hpq) hg la

end GlobalTheory.Frames
end

