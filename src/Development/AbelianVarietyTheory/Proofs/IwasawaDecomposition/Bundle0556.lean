module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0543
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0541
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0530
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesGeneratingAtPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR (pGl fGl)
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.FormalPoint GlobalTheory.AdicColimit GlobalTheory.RayEv.Transport
open GlobalTheory.TorusInvariance (wVal)
open GlobalTheory.EndRosati (push)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RayEv.Transport

section Helpers

variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem exists_fn_of_formal (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (hF : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = 1)
    (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ a : Γ(Y, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval s r z J = gs r z ⊤ a := by
  obtain ⟨t, hv⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ h => (hF U h).trans (Fintype.prod_empty _).symm) s
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨(Y.presheaf.map (homOfLE le).op).hom (t.f PEmpty.elim), fun Z r z J hJ => ?_⟩
  rw [← hv Z r z J hJ, sval_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (gs_res r z le trivial _).symm

theorem mem_pow_of_gs {W : Type} [CommRing W] (J : Ideal W) (n : ℕ) (a : W)
    (h : ∀ z, gs (adicLevelι J n) z ⊤ (toΓ W a) = 0) : a ∈ J ^ n := by
  have h1 : (adicLevelι J n).appTop.hom (toΓ W a) = 0 := fn_ext (V := ⊤) fun z _ =>
    (gs_pull (𝟙 _) (adicLevelι J n) z ⊤ trivial _).trans (by
      rw [Category.id_comp, h z]; exact (DVR.gs_zero (𝟙 _) z ⊤ trivial).symm)
  have h2 := congrArg (fun q => q.hom (toΓ W a))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ n))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  rw [h1, map_zero] at h2
  have h3 : (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom (toΓ W a) = a := by
    simp only [toΓ]; exact Iso.inv_hom_id_apply _ _
  rw [h3] at h2
  exact Ideal.Quotient.eq_zero_iff_mem.1 h2.symm

theorem toΓ_hom {W : Type} [CommRing W] (a : Γ(Sp W, ⊤)) :
    toΓ W ((Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom a) = a := by
  simp only [toΓ]; exact Iso.hom_inv_id_apply _ _

end Helpers

theorem exists_adic_expansion : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (W : Type) [CommRing W] (φ : R →+* W) (ξ : GtPt D.toPre (Over.mk (spMap φ))) (x' : Over.mk (spMap φ) ⟶ G), IsPointOf U ξ x' → ∀ (b : Sp W ⟶ D.toPre.P.A.left), ξ.b.left = b → ∀ (g' : Frame U.LG.L (Y := Sp W) x'.left) (g : Frame D.toPre.P.L b), g'.IsGen → g.IsGen → FrRel U (T := Sp W) x'.left b g' g → ∀ (k : ℕ) (σ : H0 U.LG.L k) (F : ∀ α, D.toPre.SecB k α), (∀ e, U.ExpandsAt e k σ F) → ∃ (s : W) (t : D.toPre.X → W), (∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JL), Good U.LG.L z JL → sval σ (r ≫ x'.left) z JL = gs r z ⊤ (toΓ W s) * (val g' r z JL ^ k).val) ∧ (∀ (α : D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JM), Good D.toPre.P.L z JM → sval (F α) (r ≫ b) z JM * (val (ξ.s α) r z JM).val = gs r z ⊤ (toΓ W (t α)) * (val g r z JM ^ k).val) ∧ ∀ e : ℕ, ∃ S : Finset D.toPre.X, (∀ α ∉ S, t α ∈ I.map φ ^ (e + 1)) ∧ s - ∑ α ∈ S, t α ∈ I.map φ ^ (e + 1) := by
  intro R _ _ I D A G _ _ U W _ φ ξ x' hx b hb g' g hg' hg hfr k σ F hexp
  subst hb
  have hL := U.LG.isLB
  have hM := D.toPre.P.isLB

  obtain ⟨a, ha⟩ := exists_fn_of_formal hL
    (φ := Sum.elim (fun _ : Fin 1 => x'.left ≫ 𝟙 G.left) (fun _ : PUnit.{1} => x'.left))
    (ε := Sum.elim (fun _ => (k : ℤ)) (fun _ => -((k : ℤ) * 1)))
    (fun U _ h => by simp [Fintype.prod_sum_type])
    (pullMulSec σ x'.left (LB.invGen U.LG.L _ _ (GeneratorPullback.powGen U.LG.L _ _ g' k))
      (DVR.invGen_isGen _ _ _ _ (DVR.powGen_isGen _ _ _ _ hg' k)))
  have h1 : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JL), Good U.LG.L z JL →
      sval σ (r ≫ x'.left) z JL = gs r z ⊤ a * (val g' r z JL ^ k).val := by
    intro Z r z JL hJL
    have e₁ := (ha Z r z JL hJL).symm.trans (sval_pullMulSec σ x'.left _ _ r z hJL)
    rw [val_inv, show val (GeneratorPullback.powGen U.LG.L _ _ g' k) r z JL = val g' r z JL ^ k from map_pow _ _ _] at e₁
    rw [e₁, _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, _root_.mul_one]

  have ht : ∀ α, ∃ c : Γ(Sp W, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JM), Good D.toPre.P.L z JM →
      sval (F α) (r ≫ ξ.b.left) z JM * (val (ξ.s α) r z JM).val = gs r z ⊤ c * (val g r z JM ^ k).val := by
    intro α
    obtain ⟨c, hc⟩ := exists_fn_of_formal hM
      (φ := Sum.elim (fun i => ξ.b.left ≫ D.toPre.famφB α i)
        (Sum.elim (DegPre.gtφT D.toPre (Over.mk (spMap φ)) ξ.b α) (fun _ : PUnit.{1} => ξ.b.left)))
      (ε := Sum.elim (DegPre.famε k) (Sum.elim DegPre.gtε (fun _ => -((k : ℤ) * 1))))
      (fun U _ h => by
        have e := GlobalTheory.ConstTerm.prod_factors (fun i => h (ξ.b.left ≫ D.toPre.famφB α i)) k
        have e₀ : ∀ i, h (DegPre.gtφT D.toPre (Over.mk (spMap φ)) ξ.b α i) =
            ![h (ξ.b.left ≫ D.toPre.famφB α 1), h (ξ.b.left ≫ D.toPre.famφB α 2),
              h (ξ.b.left ≫ D.toPre.famφB α 0), h (ξ.b.left ≫ D.toPre.famφB α 3)] i := by
          intro i
          fin_cases i <;> simp [GlobalTheory.ConstTerm.comp_famφB]
        simp only [← e₀] at e
        have e₁ : ξ.b.left ≫ D.toPre.famφB α 0 = ξ.b.left := Category.comp_id _
        rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [← _root_.mul_assoc, e, e₁]
        simp)
      (pullMulSec (F α) ξ.b.left
        (LB.mulGen D.toPre.P.L _ _ _ _ (ξ.s α) (LB.invGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ g k)))
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (ξ.isGen α)
          (DVR.invGen_isGen _ _ _ _ (DVR.powGen_isGen _ _ _ _ hg k))))
    refine ⟨c, fun Z r z JM hJM => ?_⟩
    have e₁ := (hc Z r z JM hJM).symm.trans (sval_pullMulSec (F α) ξ.b.left _ _ r z hJM)
    rw [val_mul hJM, val_inv,
      show val (GeneratorPullback.powGen D.toPre.P.L _ _ g k) r z JM = val g r z JM ^ k from map_pow _ _ _] at e₁
    rw [e₁, Units.val_mul, _root_.mul_assoc, _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, _root_.mul_one]
  choose c hc using ht
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom a,
    fun α => (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom (c α), fun Z r z JL hJL => ?_,
    fun α Z r z JM hJM => ?_, fun e => ?_⟩
  · rw [toΓ_hom]; exact h1 Z r z JL hJL
  · rw [toΓ_hom]; exact hc α Z r z JM hJM
  · set J := I.map φ
    obtain ⟨S, hS⟩ := DVR.expandsAt_val U e k σ F (hexp e)
    have hy₁ : reduction I x' e ≫ fGl I G e = adicLevelι J (e + 1) ≫ x'.left := reduction_fstG I x' e
    obtain ⟨hy₂, hy₃⟩ := (hasCoords_iff U e ξ _ _).1 (hx e _ (adicLevelι J (e + 1)) (reduction I x' e) hy₁)
    have gM : ∀ z : Sp (W ⧸ J ^ (e + 1)), ∃ JM, Good D.toPre.P.L z JM := fun z => by
      choose C hC using fun ψ : Sp (W ⧸ J ^ (e + 1)) ⟶ D.toPre.P.A.left => exists_chart hM (ψ z)
      exact ⟨C, hC⟩
    have gL : ∀ z : Sp (W ⧸ J ^ (e + 1)), ∃ JL, Good U.LG.L z JL := fun z => by
      choose C hC using fun ψ : Sp (W ⧸ J ^ (e + 1)) ⟶ G.left => exists_chart hL (ψ z)
      exact ⟨C, hC⟩
    refine ⟨S, fun α hα => mem_pow_of_gs J (e + 1) _ fun z => ?_, mem_pow_of_gs J (e + 1) _ fun z => ?_⟩
    · obtain ⟨JM, hJM⟩ := gM z
      have h0 := (hS _ (reduction I x' e) z JM hJM).1 α hα
      rw [hy₂] at h0
      have h2 := hc α _ (adicLevelι J (e + 1)) z JM hJM
      rw [h0, zero_mul] at h2
      rw [toΓ_hom]
      exact (Units.mul_left_eq_zero _).1 h2.symm
    · obtain ⟨JM, hJM⟩ := gM z
      obtain ⟨JL, hJL⟩ := gL z
      have hE := (hS _ (reduction I x' e) z JM hJM).2 (JL (reduction I x' e ≫ fGl I G e)) (hJL _)
      have hw := hfr e _ (adicLevelι J (e + 1)) (reduction I x' e) hy₁ z JM JL hJM hJL
      have hsv : DVR.sv U k σ (reduction I x' e ≫ fGl I G e) z (JL (reduction I x' e ≫ fGl I G e)) =
          sval σ (adicLevelι J (e + 1) ≫ x'.left) z JL := by
        rw [← hy₁]; exact (sval_of σ _ z JL _ fun _ => by rw [Category.comp_id]).symm
      have hwv : DVR.wv U e (reduction I x' e) z (JM (reduction I x' e ≫ pGl U e))
          (JL (reduction I x' e ≫ fGl I G e)) = wVal U e z JM JL (reduction I x' e) := rfl
      have hterm : ∀ α ∈ S, sval (F α) (reduction I x' e ≫ pGl U e) z JM *
          (val (DVR.tG U e α) (reduction I x' e) z JM).val =
          gs (adicLevelι J (e + 1)) z ⊤ (c α) * (val g (adicLevelι J (e + 1)) z JM ^ k).val := fun α _ => by
        rw [hy₃ α z JM hJM, hy₂]; exact hc α _ _ z JM hJM
      rw [hsv, h1 _ _ z JL hJL, Finset.sum_congr rfl hterm, ← Finset.sum_mul, hwv, hw, mul_pow,
        Units.val_mul] at hE
      have hfin : gs (adicLevelι J (e + 1)) z ⊤ a = ∑ α ∈ S, gs (adicLevelι J (e + 1)) z ⊤ (c α) := by
        refine (Units.mul_left_inj (wVal U e z JM JL (reduction I x' e) ^ k *
          val g' (adicLevelι J (e + 1)) z JL ^ k)).1 ?_
        rw [Units.val_mul]
        linear_combination hE
      have gsub : ∀ x y : Γ(Sp W, ⊤), gs (adicLevelι J (e + 1)) z ⊤ (x - y) =
          gs (adicLevelι J (e + 1)) z ⊤ x - gs (adicLevelι J (e + 1)) z ⊤ y := fun x y => by
        simp only [gs_eq _ z ⊤ trivial, map_sub]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, toΓ_hom, gsub, DVR.gs_fsum _ z ⊤ trivial, hfin, sub_eq_zero]
      exact Finset.sum_congr rfl fun α _ => by rw [toΓ_hom]

end GlobalTheory.RayEv.Transport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericFibreGroupFactorsUniversalCartesian
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.GenericFibrePoint

theorem fibre_map_univ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (yF : Sp ℂ ⟶ Xo.XF c) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), IsGrpPullback x.P.A Y.t.G (yF ≫ Y.j) φ → LBIso x.P.L (Y.t.PP.L.pull φ) → ∃ φ' : x.P.A.left ⟶ Y.oF.t.G.left, φ' ≫ Y.m.φ = φ ∧ φ' ≫ Y.oF.t.G.hom = x.P.A.hom ≫ yF ∧ IsGrpPullback x.P.A Xo.univ.t.G (yF ≫ pullback.fst _ _) (φ' ≫ Y.m0.toSABMap.φ) ∧ LBIso x.P.L (Xo.univ.t.PP.L.pull (φ' ≫ Y.m0.toSABMap.φ)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y yF x φ hgp hL
  have hsq : φ ≫ Y.t.G.hom = (x.P.A.hom ≫ yF) ≫ (Y.jQ ≫ pullback.fst _ _) := by
    rw [hgp.1.w, Category.assoc]; rfl
  let φ' : x.P.A.left ⟶ Y.oF.t.G.left := Y.m.cart.1.lift φ (x.P.A.hom ≫ yF) hsq
  have h1 : φ' ≫ Y.m.φ = φ := Y.m.cart.1.lift_fst _ _ _
  have h2 : φ' ≫ Y.oF.t.G.hom = x.P.A.hom ≫ yF := Y.m.cart.1.lift_snd _ _ _
  have hn : IsGrpPullback x.P.A Y.t.G (yF ≫ (Y.jQ ≫ pullback.fst _ _)) (φ' ≫ Y.m.φ) := by
    rw [h1]; exact hgp
  have hc : IsGrpPullback x.P.A Y.oF.t.G yF φ' := IsGrpPullback.cancel Y.m.cart hn h2
  refine ⟨φ', h1, h2, hc.comp Y.m0.toSABMap.cart, ?_⟩
  obtain ⟨w, hw, -⟩ := Y.m.lin
  obtain ⟨w0, hw0, -⟩ := Y.m0.toSABMap.lin
  have k : LBIso (Y.t.PP.L.pull Y.m.φ) (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) :=
    LBIso.trans (pull_isLB Y.t.PP.isLB _) Y.oF.t.PP.isLB (pull_isLB Xo.univ.t.PP.isLB _)
      (LBIso.symm ⟨w, hw⟩) ⟨w0, hw0⟩
  have k' : LBIso (Y.t.PP.L.pull φ) (Xo.univ.t.PP.L.pull (φ' ≫ Y.m0.toSABMap.φ)) :=
    GlobalTheory.Spread.lbIso_pull_comp φ' h1.symm rfl k
  exact LBIso.trans x.P.isLB (pull_isLB Y.t.PP.isLB _) (pull_isLB Xo.univ.t.PP.isLB _) hL k'

end GlobalTheory.GenericFibrePoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramSmoothOfHolomorphicFrames
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts GlobalTheory.TrueCx GlobalTheory.Toroidal GlobalTheory.ShFam
open GlobalTheory.TrueCx.TorHolo GlobalTheory.TrueCx.TorFrHolo
open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_comp_hom isDerivAt0_unique)
open Filter Topology
open scoped ContDiff CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GramFamily

section Pull

variable {K : Type} [CommRing K] {Y : Scheme.{0}} {p : Y ⟶ Sp K} {σ : K →+* ℂ} {D : ℕ}

end Pull

section LocalBasis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X Y : Scheme.{0}}

variable {K : Type} [CommRing K] {p : Y ⟶ Sp K} {σ : K →+* ℂ}

end LocalBasis

section Family

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) {σ : c.F →+* ℂ}

theorem isHolTo_cxPt {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) {n : ℕ} {B : Set (Fin n → ℂ)} (hB : IsOpen B)
    (x : (Fin n → ℂ) → (U.X k).dom) (hd : ∀ τ a c, DifferentiableOn ℂ (fun b => mat (x b).1 τ a c) B) :
    IsHolTo B fun b => (cxPt Z (U.un k (x b))).1 := by
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, -, hun⟩ := hU
  choose P hP hP' hx _ using hun k
  have h1 := (F.hol (ik k) n B (fun b => P (x b)) hB ⟨fun b _ => hP' _, fun a => differentiableOn_pi.2 fun i => by
    simp only [hP]
    exact differentiableOn_perFr _ (fun b _ => (x b).2) hd _ _ _⟩).1
  refine isHolTo_comp (isHolTo_of_fst _ _ hB _ (fun b => ptC_snd _) ?_) Z.jQ
  simp only [ptC_fst]
  exact LocLift.isHolTo_congr h1 fun b _ => hx _

end Family

end GlobalTheory.GramFamily
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H0NeBotOfHorizontalFunction
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
open Set GlobalTheory.CxPts GlobalTheory.Cartier.CartierDiv

namespace GlobalTheory.ShFam.Hor.Sec

section General

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ} {R : AnRead p σ d}
  {A : Set (CxPts p σ)}

theorem eqOn_of_dense (hA : Dense A) {T : Set (CxPts p σ)} (hT : IsOpen T) {f g : CxPts p σ → ℂ}
    (hf : R.HoloOn T f) (hg : R.HoloOn T g) (h : EqOn f g (T ∩ A)) : EqOn f g T :=
  h.of_subset_closure (hf.continuousOn hT) (hg.continuousOn hT) inter_subset_left (hA.open_subset_closure_inter hT)

theorem exists_holoOn_of_local (hA : Dense A) {S : Set (CxPts p σ)} {u : CxPts p σ → ℂ}
    (h : ∀ y ∈ S, ∃ (T : Set (CxPts p σ)) (f : CxPts p σ → ℂ), IsOpen T ∧ y ∈ T ∧ R.HoloOn T f ∧ EqOn f u (T ∩ A)) :
    ∃ f, R.HoloOn S f ∧ EqOn f u (S ∩ A) := by
  choose! T f hT hy hf he using h
  refine ⟨fun y => f y y, AnRead.holoOn_of_cover (T := fun y : S => T y) (fun y => hT y y.2)
    (fun y hS => ⟨⟨y, hS⟩, hy y hS⟩) fun y => ((hf y y.2).mono inter_subset_right).congr fun z hz => ?_,
    fun y hS => he y hS.1 ⟨hy y hS.1, hS.2⟩⟩
  exact eqOn_of_dense hA ((hT z hz.1).inter (hT y y.2)) ((hf z hz.1).mono inter_subset_left)
    ((hf y y.2).mono inter_subset_right)
    (fun w hw => (he z hz.1 ⟨hw.1.1, hw.2⟩).trans (he y y.2 ⟨hw.1.2, hw.2⟩).symm) ⟨hy z hz.1, hz.2⟩

theorem isHolTo_symm (c : AlgChart p σ d) {B : Set (ReciprocityTheory.L2DbarEstimates.V d)} (hB : IsOpen B) (h : B ⊆ c.e.target) :
    IsHolTo B fun b => (c.e.symm b).1 := fun U f => by
  refine ⟨?_, (c.holo U f).mono fun b hb => ⟨h hb.1, hb.2⟩⟩
  exact (c.e.continuousOn_symm.mono h).isOpen_inter_preimage hB (isOpen_ptsIn U)

variable [IsIntegral Y]

theorem ev_mul_eq {U V W : Y.Opens} {a : Γ(Y, U)} {b : Γ(Y, V)} {c : Γ(Y, W)} {y : CxPts p σ}
    (hU : y ∈ ptsIn p σ U) (hV : y ∈ ptsIn p σ V) (hW : y ∈ ptsIn p σ W)
    (h : ∀ h₁ h₂ h₃, fnOf U h₁ a * fnOf V h₂ b = fnOf W h₃ c) : ev p σ U a y * ev p σ V b y = ev p σ W c y := by
  have hy : y ∈ ptsIn p σ (U ⊓ V ⊓ W) := mem_ptsIn_inf.2 ⟨mem_ptsIn_inf.2 ⟨hU, hV⟩, hW⟩
  rw [← ev_res (inf_le_left.trans inf_le_left) hy, ← ev_res (inf_le_left.trans inf_le_right) hy,
    ← ev_res inf_le_right hy, ← ev_mul]
  congr 1
  exact fn_ext fun _ => by rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, h]

theorem holSec_ne_bot [Nonempty (CxPts p σ)] (hA : Dense A) (D : CartierDiv Y) (W : Y → Y.Opens)
    (δ : Y → Y.functionFieldˣ) (hW : ∀ y, y ∈ W y) (hδ : ∀ y, ∀ y' ∈ W y, D.IsEqn y' (δ y))
    (u : Y → CxPts p σ → ℂ) (hu : ∀ y, R.HoloOn (ptsIn p σ (W y)) (u y))
    (h0 : ∀ y, ∀ z ∈ ptsIn p σ (W y) ∩ A, u y z ≠ 0)
    (hc : ∀ y y' (r : Γ(Y, W y ⊓ W y')), (∀ h, fnOf _ h r = (δ y : Y.functionField) / (δ y' : Y.functionField)) →
      ∀ z ∈ ptsIn p σ (W y ⊓ W y') ∩ A, u y z = ev p σ _ r z * u y' z) :
    R.holSec (toLB D) ≠ ⊥ := by
  choose r hr using fun (i : (toLB D).ι) (y : Y) => exists_unit_fnOf_eq (U := (toLB D).U i ⊓ W y)
    (f := (i.1.2 : Y.functionField) / (δ y : Y.functionField))
    fun x hx => (hδ y x hx.2).iff_unitAt.1 (i.2.2 x hx.1)
  let pt (z : CxPts p σ) : Y := z.1 (IsLocalRing.closedPoint ℂ)
  have hpt (z : CxPts p σ) : z ∈ ptsIn p σ (W (pt z)) := mem_ptsIn.2 (hW _)
  let s (i : (toLB D).ι) (z : CxPts p σ) : ℂ := ev p σ _ (r i (pt z)).val z * u (pt z) z
  have key {i y z} (hi : z ∈ ptsIn p σ ((toLB D).U i)) (hy : z ∈ ptsIn p σ (W y)) :
      s i z = ev p σ _ (r i y).val z * u y z := by
    obtain ⟨t, ht⟩ := exists_unit_fnOf_eq (U := W (pt z) ⊓ W y)
      (f := (δ (pt z) : Y.functionField) / (δ y : Y.functionField))
      fun x hx => (hδ y x hx.2).iff_unitAt.1 (hδ _ x hx.1)
    have hz := mem_ptsIn_inf.2 ⟨hpt z, hy⟩
    have e : u (pt z) z = ev p σ _ t.val z * u y z :=
      eqOn_of_dense (R := R) hA (isOpen_ptsIn _) ((hu _).mono (ptsIn_mono inf_le_left))
        ((R.holoOn_ev _ t.val).mul ((hu y).mono (ptsIn_mono inf_le_right))) (hc _ _ _ ht) hz
    rw [← ev_mul_eq (a := (r i (pt z)).val) (b := t.val) (mem_ptsIn_inf.2 ⟨hi, hpt z⟩) hz (mem_ptsIn_inf.2 ⟨hi, hy⟩)
      fun _ _ _ => by rw [hr, hr, ht, div_mul_div_cancel₀ (Units.ne_zero _)], _root_.mul_assoc, ← e]
  have hs : s ∈ R.holSec (toLB D) := by
    refine ⟨⟨fun i j z hi hj => ?_, fun i z hi => ?_⟩, fun i => ?_⟩
    · have e := ev_mul_eq (a := ((toLB D).g i j).val) (b := (r j (pt z)).val) (c := (r i (pt z)).val)
        (mem_ptsIn_inf.2 ⟨hi, hj⟩) (mem_ptsIn_inf.2 ⟨hj, hpt z⟩) (mem_ptsIn_inf.2 ⟨hi, hpt z⟩)
        fun _ _ _ => by rw [hr, hr, fnOf_toLB_g, div_mul_div_cancel₀ (Units.ne_zero _)]
      simp only [s]
      rw [← e, _root_.mul_assoc]
      rfl
    · simp only [s]
      rw [ev_of_notMem (fun h => hi (mem_ptsIn_inf.1 h).1), zero_mul]
    · exact AnRead.holoOn_of_cover (T := fun y => ptsIn p σ (W y)) (fun y => isOpen_ptsIn _)
        (fun z _ => ⟨_, hpt z⟩) fun y =>
        ((AnRead.holoOn_ev_of_subset (r i y).val fun _ => mem_ptsIn_inf.2).mul
          ((hu y).mono inter_subset_right)).congr fun z hz => key hz.1 hz.2
  obtain ⟨z, hz⟩ := hA.nonempty
  intro hb
  rw [hb, Submodule.mem_bot] at hs
  let i : (toLB D).ι := ⟨(W (pt z), δ (pt z)), gen_mem (hW _), hδ _⟩
  exact mul_ne_zero (ev_ne_zero (mem_ptsIn_inf.2 ⟨hpt z, hpt z⟩) (r i (pt z)).isUnit) (h0 _ z ⟨hpt z, hz⟩)
    (congrFun (congrFun hs i) z)

end General

section Flag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ}

theorem logGrowth_inv {h : CxFr Z σ → ℂ} (hg : LogGrowth h) : LogGrowth fun a => (h a)⁻¹ := fun x₀ => by
  obtain ⟨N, φ, h₁, h₂, h₃, h₄, h₅⟩ := hg x₀
  refine ⟨N, φ, h₁, h₂, h₃, h₄, fun V _ _ _ B a hB ha hN b₀ hb => ?_⟩
  obtain ⟨C, k, hk⟩ := h₅ V B a hB ha hN b₀ hb
  exact ⟨C, k, hk.mono fun b hb hi => ⟨(hb hi).2, by rw [inv_inv]; exact (hb hi).1⟩⟩

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ' : k →+* ℂ} {d : ℕ}

theorem inner_iff {π : Y ⟶ gen Z} {z : CxPts p σ'} {x : CxPts (genStr Z) σ} (h : x.1 = z.1 ≫ π) :
    Inner x ↔ z ∈ ptsIn p σ' (π ⁻¹ᵁ (genBd Z).compl) := by
  rw [Inner, h, mem_ptsIn]
  rfl

theorem exists_extension (R : AnRead p σ' d) (π : Y ⟶ gen Z)
    (hA : Dense (ptsIn p σ' (π ⁻¹ᵁ (genBd Z).compl))) {S : Set (CxPts p σ')} (hS : IsOpen S)
    {a : CxPts p σ' → CxFr Z σ} (ha : ∀ z ∈ S, (a z).1.1 = z.1 ≫ π)
    (hf : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V)
      (x : V → CxPts p σ'), IsOpen B → IsHolTo B (fun b => (x b).1) → MapsTo x B S → HolFam B fun b => a (x b))
    {h : CxFr Z σ → ℂ}
    (hh : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V)
      (a : V → CxFr Z σ), IsOpen B → HolFam B a → (∀ b ∈ B, Inner (a b).1) → DifferentiableOn ℂ (fun b => h (a b)) B)
    (hg : LogGrowth h) :
    ∃ f, R.HoloOn S f ∧ EqOn f (fun z => h (a z)) (S ∩ ptsIn p σ' (π ⁻¹ᵁ (genBd Z).compl)) := by
  refine exists_holoOn_of_local hA fun y hy => ?_
  obtain ⟨N, φ, hN, hyN, hφ, hφ0, hgr⟩ := hg (a y).1
  obtain ⟨N', hN', rfl⟩ := isOpen_induced_iff.1 hN
  obtain ⟨i, hi⟩ := R.cover y
  set c := R.chart i
  let T : Set (CxPts p σ') := S ∩ (fun z => z.1 ≫ π) ⁻¹' N'
  have hT : IsOpen T := hS.inter (hN'.preimage ((Points.continuous_comp π).comp continuous_subtype_val))
  have hTN (z) (hz : z ∈ T) : (a z).1 ∈ Subtype.val ⁻¹' N' := by
    rw [mem_preimage, ha z hz.1]; exact hz.2
  have hyT : y ∈ T := ⟨hy, by rw [mem_preimage, ← ha y hy]; exact hyN⟩
  let B := c.e.target ∩ c.e.symm ⁻¹' T
  have hB : IsOpen B := ChartGlue.isOpen_over c.e hT
  have hfam {B' : Set (ReciprocityTheory.L2DbarEstimates.V d)} (hB' : IsOpen B') (e : B' ⊆ B) : HolFam B' fun b => a (c.e.symm b) :=
    hf _ B' c.e.symm hB' (isHolTo_symm c hB' (e.trans inter_subset_left)) fun b hb => (e hb).2.1
  have hφB : DifferentiableOn ℂ (fun b => φ (a (c.e.symm b)).1) B :=
    hφ _ B (fun b => (a (c.e.symm b)).1) hB (hfam hB subset_rfl).1 fun b hb => hTN _ hb.2
  have hin (z) (hz : z ∈ T) : φ (a z).1 ≠ 0 ↔ z ∈ ptsIn p σ' (π ⁻¹ᵁ (genBd Z).compl) :=
    (hφ0 _ (hTN z hz)).trans (inner_iff (ha z hz.1))
  have hB' : IsOpen {b ∈ B | φ (a (c.e.symm b)).1 ≠ 0} :=
    hφB.continuousOn.isOpen_inter_preimage hB isOpen_ne
  obtain ⟨u, hu, he⟩ := GlobalTheory.T.riemann_extension_of_log_growth _ B _ (fun b => h (a (c.e.symm b))) hB hφB
    (hh _ _ _ hB' (hfam hB' (sep_subset _ _)) fun b hb => (hφ0 _ (hTN _ hb.1.2)).1 hb.2)
    (fun b hb => by
      have hs := c.e.map_target hb.1
      have h₁ := hA.open_subset_closure_inter (c.e.open_source.inter hT) ⟨hs, hb.2⟩
      have h₂ := (c.e.continuousAt hs).continuousWithinAt.mem_closure_image h₁
      rw [c.e.right_inv hb.1] at h₂
      refine closure_mono ?_ h₂
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨ChartGlue.mem_over c.e hz.1.1 hz.1.2, ?_⟩
      rw [c.e.left_inv hz.1.1]
      exact (hin z hz.1.2).2 hz.2)
    fun b hb => by
      obtain ⟨C, n, hn⟩ := hgr _ B _ hB (hfam hB subset_rfl) (fun b hb => hTN _ hb.2) b hb
      refine ⟨C, n, ?_⟩
      filter_upwards [hn, hB.mem_nhds hb] with b' h₁ h₂ h₃
      exact (h₁ ((hφ0 _ (hTN _ h₂.2)).1 h₃)).1
  refine ⟨c.e.source ∩ T, u ∘ c.e, c.e.open_source.inter hT, ⟨hi, hyT⟩,
    AnRead.holoOn_of_chart c (hu.congr fun b hb => congrArg u (c.e.right_inv hb.1)), fun z hz => ?_⟩
  have := he (x := c.e z) ⟨ChartGlue.mem_over c.e hz.1.1 hz.1.2, by
    rw [c.e.left_inv hz.1.1]; exact (hin z hz.1.2).2 hz.2⟩
  simpa only [c.e.left_inv hz.1.1, Function.comp_apply] using this

end Flag

end GlobalTheory.ShFam.Hor.Sec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolomorphicUniformisationExpModelFiber
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem pushEx_hol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → IsHolTo Set.univ (fun z => (pushEx Z Fu y i P p hu hp z).left) := by
  intro E _ _ _ H Dw l Xo c O _ β Z g ty σ₀ Fu y i P p hu hp hP
  have h1 := (Fu.hol i 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  have hw : ∀ (b : Fin 0 → ℂ) (z : Fin g → ℂ), (Fu.ex i P z).left ≫ Xo.univ.t.G.hom =
      (fun _ => y) b ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) := fun _ z => by
    rw [Over.w (Fu.ex i P z), ← hu]; rfl
  have h2 := GlobalTheory.TrueCx.TorFrHolo.isHolTo_lift Z.m0.toSABMap.cart.1 isOpen_univ
    (fun (_ : Fin 0 → ℂ) z => (Fu.ex i P z).left) (fun _ => y) h1
    (GlobalTheory.TrueCx.TorHolo.isHolTo_const isOpen_univ y) hw
  have h3 := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h2 Z.m.φ
  exact GlobalTheory.LocLift.isHolTo_comp h3 isOpen_univ (β := fun z => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
    fun _ _ => ⟨trivial, trivial⟩

end GlobalTheory.ShFam.Hor.LogCh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerVectorBlockTriangularFrameChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pluckerVector_blockTriangular_frame_change : ∀ (T : Type) (m : T → ℕ) (S : Type) [CommRing S] (M : ℕ) (c c' : Let m → Fin (M + 1) → S) (d : Let m → S) (k : ℕ) (e : Fin k → Let m), Tri c c' d → Down e → plk c' e = (∏ l, d (e l)) • plk c e := by
  first | exact @GlobalTheory.FlagEmb.plk_tri | exact GlobalTheory.FlagEmb.plk_tri | (intros; apply GlobalTheory.FlagEmb.plk_tri <;> assumption)
end

