module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsChartLiftOfFiniteCover
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ToPtIdPtBijective
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0363
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0259
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0350

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsChartLiftOfFiniteCover
section
open GlobalTheory.WH GlobalTheory.PD GlobalTheory.W1 GlobalTheory.CechDR KaehlerDifferential
open scoped TensorProduct
theorem _root_.GlobalTheory.T.exists_chart_lift_of_finite_cover : ∀ (d a : ℕ) (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K] [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (x : Fin (d + 1) → F) (j2 : K →ₐ[ℂ] K'),
  IsFinCover ℂ K x → IsFinCover ℂ K' x →
  (∀ (i : Fin (d + 1)) (e : rB ℂ K' x {i} →ₐ[ℂ] ℂ), ∃ j : Fin (d + 1), ∀ v ∈ R2 x j2 {j}, ∃ (b : K') (hb : b ∈ rB ℂ K' x {i}), e ⟨b, hb⟩ ≠ 0 ∧ b * v ∈ rB ℂ K' x {i}) →
  IsReduced ((rB ℂ K' x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ K' x j⟩ : rB ℂ K' x {0})))) →
  (∀ (i : Fin (d + 1)), i ≠ 0 → ∀ e : rB ℂ K' x {i} →ₐ[ℂ] ℂ, ¬ IsFix (rB ℂ K' x {i}) e j2 (rB ℂ K x {i})) →
  (∀ e : rB ℂ K' x {0} →ₐ[ℂ] ℂ, IsFix (rB ℂ K' x {0}) e j2 (rB ℂ K x {0}) → ∀ j : Fin d, e ⟨_, tco_mem ℂ K' x j⟩ = 0) →
  ∀ (Fx : Finset (fib ℂ K' x)), (∀ e : fib ℂ K' x, e ∈ Fx ↔ IsFix (rB ℂ K' x {0}) e.1 j2 (rB ℂ K x {0})) →
  (∀ e ∈ Fx, ∀ (b : K) (hb1 : algebraMap K K' b ∈ rB ℂ K' x {0}), b ∈ rB ℂ K x {0} → e.1 ⟨_, hb1⟩ = 0 →
    ∃ (c : K) (hc1 : algebraMap K K' c ∈ rB ℂ K' x {0}), c ∈ rB ℂ K x {0} ∧ e.1 ⟨_, hc1⟩ ≠ 0 ∧
      ∃ g : Fin d → K, (∀ l, g l ∈ rB ℂ K x {0}) ∧ c * b = ∑ l, g l * algebraMap F K (x l.succ / x 0)) →
  ∀ A : fib ℂ K' x → Matrix (Fin d) (Fin d) ℂ,
  (∀ e ∈ Fx, ∀ m : Fin d, ∃ (c : K') (hc : c ∈ rB ℂ K' x {0}) (g : Fin d → K') (hg : ∀ l, g l ∈ rB ℂ K' x {0}), e.1 ⟨c, hc⟩ ≠ 0 ∧
    c * j2 (algebraMap F K (x m.succ / x 0)) = ∑ l, g l * algebraMap F K' (x l.succ / x 0) ∧ ∀ l, e.1 ⟨g l, hg l⟩ = e.1 ⟨c, hc⟩ * A e m l) →
  (∀ e ∈ Fx, (1 - A e).det ≠ 0) →
  ∀ u : ∀ p : ℕ, (cech fun I => omB ℂ K (rB ℂ K x I) a).H p →ₗ[ℂ] (cech fun I => omB ℂ K (rB ℂ K x I) a).H p,
  (∀ (p : ℕ) (b : Finset (Fin (d + 1)) → DR ℂ K) (hb : b ∈ (cech fun I => omB ℂ K (rB ℂ K x I) a).Z p),
    ∃ bt ∈ (cech fun s : Finset (Fin (d + 1) ⊕ₗ Fin (d + 1)) => omB ℂ K' (RY x j2 (lft s) (rgt s)) a).Z p,
      (∀ J, bt (uni ∅ J) = pr2L j2 (b J)) ∧
      ∃ h : trC (k := ℂ) (K := K) (L := K') (fun I => bt (uni I ∅)) ∈ (cech fun I => omB ℂ K (rB ℂ K x I) a).Z p,
        u p (Submodule.Quotient.mk ⟨b, hb⟩) = Submodule.Quotient.mk ⟨_, h⟩) →
  (∀ p : ℕ, FiniteDimensional ℂ ((cech fun I => omB ℂ K (rB ℂ K x I) a).H p)) →
  ∑ p ∈ Finset.range (d + 1), (-1 : ℂ) ^ p * LinearMap.trace ℂ _ (u p) =
    ∑ e ∈ Fx, (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A e).map Polynomial.C)).coeff a / (1 - A e).det := by
  first | exact @UpperTheory.Cb.exists_chart_lift_of_finite_cover | exact UpperTheory.Cb.exists_chart_lift_of_finite_cover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteCoverProjSpaceReducedFibreOrigin
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential

namespace GlobalTheory.PD.FibRed

theorem quotEquiv_of_germ {X : Scheme.{0}} [IsIntegral X] [Algebra ℂ X.functionField] {F : Type} [Field F] [Algebra ℂ F]
    [Algebra F X.functionField] [IsScalarTower ℂ F X.functionField] {d : ℕ} (x : Fin (d + 1) → F) (U : X.Opens)
    (hg : genericPoint X ∈ U) (t : Fin d → Γ(X, U))
    (hring : ∀ y, y ∈ rB ℂ X.functionField x {0} ↔ ∃ f : Γ(X, U), (X.presheaf.germ U (genericPoint X) hg).hom f = y)
    (ht : ∀ j, (X.presheaf.germ U (genericPoint X) hg).hom (t j) = algebraMap F X.functionField (x j.succ / x 0)) :
    Nonempty ((Γ(X, U) ⧸ Ideal.span (Set.range t)) ≃+*
      (rB ℂ X.functionField x {0} ⧸ Ideal.span (Set.range fun j : Fin d =>
        (⟨_, tco_mem ℂ X.functionField x j⟩ : rB ℂ X.functionField x {0})))) := by
  set g := (X.presheaf.germ U (genericPoint X) hg).hom
  have hinj : Function.Injective g := germ_injective_of_isIntegral X _ hg
  let g' : Γ(X, U) →+* rB ℂ X.functionField x {0} :=
    g.codRestrict (rB ℂ X.functionField x {0}).toSubring fun f => (hring _).2 ⟨f, rfl⟩
  have hbij : Function.Bijective g' := by
    refine ⟨fun a b h => hinj (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨f, hf⟩ := (hring y).1 y.2
    exact ⟨f, Subtype.ext hf⟩
  let e := RingEquiv.ofBijective g' hbij
  refine ⟨Ideal.quotientEquiv _ _ e ?_⟩
  rw [Ideal.map_span, ← Set.range_comp]
  congr 2
  funext j
  exact Subtype.ext (ht j).symm

theorem exists_finCover_fibre_reduced : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ X.functionField], inst = ffAlg p → IsProjOver p → ∀ S : Finset (CxPts p (RingHom.id ℂ)), ∃ (F : IntermediateField ℂ X.functionField) (x : Fin (d + 1) → F) (U : Fin (d + 1) → X.Opens), IsFinCover ℂ X.functionField x ∧ IsAffCover p U (rB ℂ X.functionField x) ∧ IsReduced ((rB ℂ X.functionField x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ X.functionField x j⟩ : rB ℂ X.functionField x {0})))) ∧ ∀ y ∈ S, y ∈ CxPts.ptsIn p (RingHom.id ℂ) (U 0) ∧ ∀ j : Fin d, ∀ (hg : genericPoint X ∈ U 0) (f : Sec p (U 0)), (X.presheaf.germ (U 0) (genericPoint X) hg).hom f = algebraMap F X.functionField (x j.succ / x 0) → CxPts.ev p (RingHom.id ℂ) (U 0) f y = 0 := by
  intro X _ p d _ inst hinst hproj S
  obtain ⟨N, ι, hι, hιp⟩ := hproj
  obtain ⟨n, f, hf, hn, hcov, hgen, hS, htr⟩ := GlobalTheory.T.exists_forms_transversal_at_complexPoints X p d N ι hι hιp S
  obtain ⟨F, x, hFC, hAC, hx⟩ := GlobalTheory.T.exists_finiteCover_affineCover_of_forms_no_commonZero X p d hinst N ι hι hιp n f hf hn hcov hgen
  set U0 := GlobalTheory.EtProj.fOpen ι (f 0) with hU0
  set t : Fin d → Γ(X, U0) := fun j => GlobalTheory.EtProj.fRatio ι (f j.succ) (f 0) (hf j.succ) (hf 0) with ht_def
  have hx0 : x 0 = 1 := by
    apply (algebraMap F X.functionField).injective
    rw [hx 0, GlobalTheory.EtProj.fRatio_self, map_one, map_one]
  have ht : ∀ j, (X.presheaf.germ U0 (genericPoint X) (hgen 0)).hom (t j) =
      algebraMap F X.functionField (x j.succ / x 0) := by
    intro j
    rw [hx0, div_one, hx j.succ]
  have hring : ∀ y, y ∈ rB ℂ X.functionField x {0} ↔
      ∃ g : Γ(X, U0), (X.presheaf.germ U0 (genericPoint X) (hgen 0)).hom g = y := by
    intro y
    have hle : ({0} : Finset (Fin (d + 1))).inf (fun i => GlobalTheory.EtProj.fOpen ι (f i)) = U0 := by simp [hU0]
    rw [hAC.ring {0} (Finset.singleton_nonempty 0) y]
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨X.presheaf.map (homOfLE hle.ge).op g, ?_⟩
      exact X.presheaf.germ_res_apply (homOfLE hle.ge) _ _ g
    · rintro ⟨g, rfl⟩
      refine ⟨X.presheaf.map (homOfLE hle.le).op g, ?_⟩
      exact X.presheaf.germ_res_apply (homOfLE hle.le) _ _ g
  obtain ⟨E⟩ := quotEquiv_of_germ x U0 (hgen 0) t hring ht
  have hU0aff : IsAffineOpen U0 := by
    simpa [hU0] using hAC.affine {0} (Finset.singleton_nonempty 0)
  haveI : Smooth p := SmoothOfRelativeDimension.smooth d p
  haveI hart : IsArtinianRing (Γ(X, U0) ⧸ Ideal.span (Set.range t)) := by
    haveI := GlobalTheory.T.isArtinianRing_rB_quot_span_tco_of_isFinCover ℂ X.functionField F d x hFC
    exact RingEquiv.isArtinianRing E.symm
  have hred : IsReduced (Γ(X, U0) ⧸ Ideal.span (Set.range t)) := by
    refine GlobalTheory.T.isReduced_quotient_of_artinian_of_maximal_le' _ _ hart fun m hm hIm => ?_
    obtain ⟨y, hy, rfl⟩ := GlobalTheory.T.exists_complexPoint_ker_eval_eq_maximal X p U0 hU0aff m hm
    refine htr y hy fun j => ?_
    exact hIm (Ideal.subset_span ⟨j, rfl⟩)
  refine ⟨F, x, fun i => GlobalTheory.EtProj.fOpen ι (f i), hFC, hAC, ?_, fun y hyS => ⟨(hS y hyS).1, ?_⟩⟩
  · haveI := hred
    exact isReduced_of_injective E.symm E.symm.injective
  · intro j hg g hgj
    have : g = t j := by
      apply germ_injective_of_isIntegral X _ hg
      exact hgj.trans (ht j).symm
    rw [this]
    exact (hS y hyS).2 j

end GlobalTheory.PD.FibRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TuplesHaveLocalModelsOfStandardColumnObjects
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

theorem modelsAt_of_part : GlobalTheory.TwV.Lt.AdmAtEnt2 → GlobalTheory.TwV.Lt.CurveEx → ∀ (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)), Part w Z (ofObj O) → ModelsAt (w.D Z) O := by
  intro hA hC B f T w Z O hP hL hk
  obtain ⟨⟨t, hJ⟩, he⟩ := GlobalTheory.Svd.jointsAt_all_std B f T w Z O hP hL
  have hS : OrbitPlaces.Stab0 (w.D Z) := GlobalTheory.Pdv.stepZero_trivial_stabilisers_trueColumns w.I w.ok w.pins w.l Z O.ex.lev
  exact _root_.GlobalTheory.TwV.modelsOK_of_joints hA hC t (fun μ _ => hJ μ) he hS hk

end GlobalTheory.Svd
end

