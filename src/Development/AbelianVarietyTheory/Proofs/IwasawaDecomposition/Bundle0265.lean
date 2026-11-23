module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
public import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.LocalRingCardinality.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CayleyOperatorPowEqSignedSumPartialDerivs
section
open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

set_option autoImplicit false

namespace GlobalTheory.CayleyBlock

theorem dList_append' {σ : Type} [DecidableEq σ] (l₁ l₂ : List σ) :
    dList (l₁ ++ l₂) = dList l₁ * dList l₂ := by
  simp [dList, List.map_append, List.prod_append]

theorem smallList_cons' {p q : ℕ} (σ : Equiv.Perm (Fin p)) (τ : Fin q → Equiv.Perm (Fin p)) :
    smallList (Fin.cons σ τ : Fin (q + 1) → Equiv.Perm (Fin p)) =
      (List.finRange p).map (fun j => (σ j, j)) ++ smallList τ := by
  simp [smallList, List.finRange_succ, List.flatMap_cons, List.flatMap_map]

theorem sgnProd_cons' {p q : ℕ} (σ : Equiv.Perm (Fin p)) (τ : Fin q → Equiv.Perm (Fin p)) :
    sgnProd (Fin.cons σ τ : Fin (q + 1) → Equiv.Perm (Fin p)) =
      (Equiv.Perm.sign σ : ℤ) * sgnProd τ := by
  simp [sgnProd, Fin.prod_univ_succ]

theorem cayMono_eq_dList' {p : ℕ} (σ : Equiv.Perm (Fin p)) :
    cayMono p ℂ σ = dList ((List.finRange p).map fun j => (σ j, j)) := by
  simp [cayMono, dList, List.map_map]
  rfl

theorem cayOp_pow_eq_sum (p q : ℕ) :
    cayOp p ℂ ^ q = ∑ τ : Fin q → Equiv.Perm (Fin p), sgnProd τ • dList (smallList τ) := by
  induction q with
  | zero => simp [smallList, sgnProd, dList]
  | succ q ih =>
    rw [pow_succ', ih, cayOp, Finset.sum_mul_sum,
      ← (Fin.consEquiv (fun _ => Equiv.Perm (Fin p))).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    change _ = sgnProd (Fin.cons σ τ : Fin (q + 1) → Equiv.Perm (Fin p)) •
      dList (smallList (Fin.cons σ τ : Fin (q + 1) → Equiv.Perm (Fin p)))
    rw [smallList_cons', sgnProd_cons', dList_append', cayMono_eq_dList', smul_mul_smul, mul_smul]

end GlobalTheory.CayleyBlock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernFormPolyCoeffTopOfNegHermitianSquare
section
open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PointFormSign

theorem curvPoly_eq_smul_sum {n m : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) :
    curvPoly G v = ∑ a, ∑ b, (X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) •
      (curv G v (coordVec a) (coordVec b)).map C := by
  ext i j
  simp [curvPoly, Matrix.sum_apply, mul_comm]

theorem sqPoly_eq_smul_sum {n m r : ℕ} (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) :
    sqPoly T = ∑ a, ∑ b, (X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) •
      (T (coordVec a) * (T (coordVec b))ᴴ).map C := by
  refine Matrix.ext fun i j => ?_
  simp only [sqPoly, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mul_comm]

theorem curvPoly_of_negSq {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) (S : Matrix (Fin m) (Fin m) ℂ)
    (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ)
    (h : ∀ ξ η, curv G v ξ η = S⁻¹ * (-(T ξ * (T η)ᴴ)) * S) :
    curvPoly G v = S⁻¹.map C * (-(sqPoly T)) * S.map C := by
  have key : ∀ M : Matrix (Fin m) (Fin m) ℂ,
      (S⁻¹ * (-M) * S).map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) = -(S⁻¹.map C * M.map C * S.map C) := by
    intro M
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_neg _ (fun a => map_neg C a), Matrix.mul_neg, Matrix.neg_mul]
  rw [curvPoly_eq_smul_sum, sqPoly_eq_smul_sum]
  simp only [h, key]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Finset.sum_neg_distrib, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_neg]

theorem charpolyRev_neg_coeff_dim {R : Type*} [CommRing R] [Nontrivial R] {m : ℕ} (P : Matrix (Fin m) (Fin m) R) :
    (Matrix.charpolyRev (-P)).coeff m = P.det := by
  rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
    Polynomial.revAt_le le_rfl, Nat.sub_self]
  have h := Matrix.det_eq_sign_charpoly_coeff (-P)
  rw [Matrix.det_neg, Fintype.card_fin] at h
  have h2 : ((-1 : R) ^ m) * ((-1) ^ m) = 1 := by rw [← mul_pow]; simp
  calc (-P).charpoly.coeff 0 = ((-1) ^ m * (-1) ^ m) * (-P).charpoly.coeff 0 := by rw [h2, one_mul]
    _ = P.det := by rw [mul_assoc, ← h, ← mul_assoc, h2, one_mul]

theorem chernPoly_top_of_negSq {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) (S : Matrix (Fin m) (Fin m) ℂ)
    (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) (hS : IsUnit S.det)
    (h : ∀ ξ η, curv G v ξ η = S⁻¹ * (-(T ξ * (T η)ᴴ)) * S) :
    chernPoly G v m = (-1) ^ m * (sqPoly T).det := by
  rw [chernPoly, charpolyRev_neg_coeff_dim, curvPoly_of_negSq G v S T h, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_neg, Fintype.card_fin]
  have h1 : (S⁻¹.map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ)).det * (S.map C).det = 1 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det, ← map_mul,
      ← Matrix.det_mul, Matrix.nonsing_inv_mul _ hS, Matrix.det_one, map_one]
  calc (S⁻¹.map C).det * ((-1) ^ m * (sqPoly T).det) * (S.map C).det
      = ((S⁻¹.map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ)).det * (S.map C).det) * ((-1) ^ m * (sqPoly T).det) := by ring
    _ = (-1) ^ m * (sqPoly T).det := by rw [h1, one_mul]

end GlobalTheory.PointFormSign
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffComposedPartialDerivListOfNodup
section
set_option autoImplicit false

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

namespace GlobalTheory.CayleyBlock

theorem coeff_dList_of_nodup {σ : Type} [DecidableEq σ] (l : List σ) (hl : l.Nodup) (m : σ →₀ ℕ)
    (hm : ∀ v ∈ l, m v = 0) (G : MvPolynomial σ ℂ) :
    AddMonoidAlgebra.coeff (dList l G) m = AddMonoidAlgebra.coeff G (m + (l.map fun v => Finsupp.single v 1).sum) := by
  induction l generalizing m with
  | nil => simp [dList]
  | cons v l ih =>
    have hc : dList (v :: l) G = pderiv v (dList l G) := by
      simp [dList]
    rw [List.nodup_cons] at hl
    have h0 : m v = 0 := hm v (List.mem_cons_self ..)
    have h1 : ∀ w ∈ l, (m + Finsupp.single v 1 : σ →₀ ℕ) w = 0 := by
      intro w hw
      have hne : w ≠ v := fun h => hl.1 (h ▸ hw)
      rw [Finsupp.add_apply, hm w (List.mem_cons_of_mem _ hw), Finsupp.single_eq_of_ne hne, add_zero]
    rw [hc, MvPolynomial.coeff_pderiv, ih hl.2 _ h1, h0, List.map_cons, List.sum_cons, add_assoc]
    simp

end GlobalTheory.CayleyBlock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionEmbeddingCompatibleClosuresStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_embedding_compatible_closures : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (w : HeightOneSpectrum (𝓞 E)) (W : HeightOneSpectrum (𝓞 K)) (j : K → Kbar w) (f : w.adicCompletion E →+* W.adicCompletion K) (b : Kbar w ≃+* Kbar W), Continuous f → (∀ x, b (algebraMap _ _ x) = algebraMap _ _ (f x)) → (∀ x : K, b (j x) = algebraMap (W.adicCompletion K) _ (algebraMap K (W.adicCompletion K) x)) → (∀ x : E, f (algebraMap E _ x) = algebraMap K _ (algebraMap E K x)) → letI := f.toAlgebra; Neutral.B1.normGroup (w.adicCompletion E) (IntermediateField.adjoin (w.adicCompletion E) (Set.range j)) = (Units.map (Algebra.norm (w.adicCompletion E) : W.adicCompletion K →* w.adicCompletion E)).range := by
  first | exact @GlobalTheory.normGroup_adjoin_eq_norm_range_completion | exact GlobalTheory.normGroup_adjoin_eq_norm_range_completion | (intros; apply GlobalTheory.normGroup_adjoin_eq_norm_range_completion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsLiftModel
section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory

theorem ringOfIntegers_hom_complex_injective (F : Type) [Field F] [NumberField F] (τ : 𝓞 F →+* ℂ) :
    Function.Injective τ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [Ideal.under_def, RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
  exact RingHom.injective_int _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexSpanRationalLiftFormsEqBasePart
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3.RatSpan

theorem span_jW_wp : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (p : A3.fam3.base3.Ix), Submodule.span ℂ ((Z.jW i) '' ((s0Of R F).Wp i p : Set (Fin ((s0Of R F).dW i) → D.what₂.LL))) = (R.Wp3 i p).comap (Y.mj.eW i) := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH _ i p
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim

  have hpt : ∀ y : Fin (((R.toCx3 F).data F.cr false).dW i) → D.what₂.LL,
      (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y) =
        Tw.mk (twAt D.what₂.embLL A3.A.v0) (Y.mj.eW i (Z.jW i y)) := by
    intro y
    rw [Z.jW_read]
    refine (GlobalTheory.Mem.LiftTheta.liftWeight_complexPoint_eq_twist R.toRealDat F.lv2 false i y).trans ?_
    exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0))
      (congrArg ((R.FW i).j (sg0 D A3.A)) (Fintype.linearCombination_apply _ _ _)).symm
  have hmem : ∀ y, y ∈ (s0Of R F).Wp i p ↔ Z.jW i y ∈ (R.Wp3 i p).comap (Y.mj.eW i) := by
    intro y
    show (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y) ∈ (R.toCx3 F).Wp i p ↔ _
    exact (Iff.of_eq (congrArg (· ∈ (R.toCx3 F).Wp i p) (hpt y))).trans Iff.rfl
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact (hmem y).1 hy
  · intro x hx
    have hnP : 0 < RealDat.nP F.lv2 false := RealDat.nP_pos (F := F.lv2) false
    have hinj : Function.Injective (Y.mj.eW i) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro d hd
      have h1 : RealDat.nP F.lv2 false * ‖d‖ ^ 2 = 0 := by rw [← Y.mj.eW_norm i d, hd]; simp
      have h2 : ‖d‖ ^ 2 = 0 := by
        rcases mul_eq_zero.1 h1 with h | h
        · exact absurd h hnP.ne'
        · exact h
      exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2)
    have hw := (R.toCx3 F).principal_form_injective false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) i
    set U : Submodule ℂ ((R.toCx3 F).W i) := Submodule.span ℂ
      ((fun y => (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y)) '' ((R.toCx3 F).WpK false i p : Set _)) with hU
    have hUT : U = (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) := by
      apply Submodule.eq_of_le_of_finrank_le
      · rw [hU, Submodule.span_le]
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨hy, LinearMap.mem_range_self _ _⟩
      · rw [← (R.toCx3 F).finrank_WpK F.cr false hR.h4pos hR.kForm hR.ewNorm hR.types0 hR.lifts0.1 hR.ratTh
          hR.liftHyp0.h3W hR.partsW i p]
        exact (finrank_le_cpt A3.A.v0.embedding ((R.toCx3 F).w0C false i) hw U ((R.toCx3 F).WpK false i p)
          (fun y hy => Submodule.subset_span ⟨y, hy, rfl⟩)).trans (Submodule.finrank_mono inf_le_left)
    have hWS : Y.mj.eW i x ∈ R.toRealDat.WS F.lv2 false i (sg0 D A3.A) := by
      rw [hH.aux.levelW false i (sg0 D A3.A), ← Y.mj.eW_range i]
      exact LinearMap.mem_range_self _ _
    rw [← GlobalTheory.Mem.LiftTheta.goodForm_span] at hWS
    have h1 : Tw.mk (twAt D.what₂.embLL A3.A.v0) (Y.mj.eW i x) ∈ U := by
      rw [hUT]
      refine ⟨hx, ?_⟩
      have h2 := Submodule.mem_map_of_mem (f := Tw.mkL (twAt D.what₂.embLL A3.A.v0) (R.HW i (sg0 D A3.A)).H) hWS
      rw [Submodule.map_span] at h2
      refine (Submodule.span_le.2 ?_) h2
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      refine ⟨Pi.single k 1, ?_⟩
      have h3 := GlobalTheory.Mem.LiftTheta.liftWeight_complexPoint_eq_twist R.toRealDat F.lv2 false i (Pi.single k 1)
      exact (congrArg ((R.toCx3 F).w0C false i) (cpt_single A3.A.v0.embedding k).symm).trans h3
    let outL : (R.toCx3 F).W i →ₛₗ[cj (twAt D.what₂.embLL A3.A.v0)] (R.HW i (sg0 D A3.A)).H :=
      { toFun := fun z => Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) z
        map_add' := fun a b => Tw.out_add (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) a b
        map_smul' := fun c a => Tw.out_smul (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) c a }
    have h4 : Y.mj.eW i x ∈ U.map outL := Submodule.mem_map_of_mem (f := outL) h1
    rw [hU, Submodule.map_span, ← Set.image_comp] at h4
    have h5 : Submodule.span ℂ ((outL ∘ fun y => (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y)) ''
        ((R.toCx3 F).WpK false i p : Set _)) ≤
        (Submodule.span ℂ ((Z.jW i) '' (((R.toCx3 F).WpK false i p : Set (Fin ((R.toCx3 F).dW false i) → D.what₂.LL)) :
          Set (Fin (((R.toCx3 F).data F.cr false).dW i) → D.what₂.LL)))).map (Y.mj.eW i) := by
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨Z.jW i y, Submodule.subset_span ⟨y, hy, rfl⟩, ?_⟩
      show Y.mj.eW i (Z.jW i y) = Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H)
        ((R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y))
      exact (congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H)) (hpt y)).symm
    obtain ⟨x', hx', hxx⟩ := h5 h4
    rw [← hinj hxx]
    exact hx'

end GlobalTheory.Mem.R3.RatSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstantCoeffCayleyOperatorPowDeterminantPow
section
open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

namespace GlobalTheory

theorem cayOp_pow_cayDet_pow (p s k : ℕ) :
    (cayOp p ℂ ^ k) (cayDet p ℂ ^ (s + k)) =
      (∏ t ∈ Finset.range k, ∏ j ∈ Finset.range p, (s + 1 + t + j)) • cayDet p ℂ ^ s := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ← add_assoc, cayley p ℂ (s + k + 1), Nat.add_sub_cancel,
      map_nsmul, ih, smul_smul, Finset.prod_range_succ]
    congr 1
    rw [mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    ring

theorem prod_succ_mul_factorial (j q : ℕ) :
    (∏ t ∈ Finset.range q, (1 + t + j)) * j.factorial = (q + j).factorial := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.prod_range_succ, mul_right_comm, ih, show q + 1 + j = (q + j) + 1 by ring,
      Nat.factorial_succ]
    ring

theorem constantCoeff_cayOp_pow_cayDet_pow : ∀ (p q : ℕ),
    constantCoeff ((cayOp p ℂ ^ q) (cayDet p ℂ ^ q)) =
      ∏ i ∈ Finset.range p, (((q + i).factorial : ℂ) / i.factorial) := by
  intro p q
  have h := cayOp_pow_cayDet_pow p 0 q
  rw [zero_add] at h
  rw [h, pow_zero, map_nsmul, map_one, nsmul_eq_mul, mul_one, Finset.prod_comm]
  push_cast
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [eq_div_iff (by exact_mod_cast (Nat.factorial_pos j).ne')]
  have := prod_succ_mul_factorial j q
  simp only [zero_add] at *
  exact_mod_cast this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetMulConjDet
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open Formalism.L2.Host (HChar atFin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.DetLift

theorem det_mul_conj_det {A B : Type} [CommRing A] [CommRing B] (σ : A →+* A) (ι : B →+* A) {n : ℕ} {g : GL (Fin n) A}
    (hg : g ∈ Formalism.UG.UJ σ ((1 : Matrix (Fin n) (Fin n) B).map ι)) :
    (g : Matrix (Fin n) (Fin n) A).det * σ (g : Matrix (Fin n) (Fin n) A).det = 1 := by
  have h : Formalism.UG.cT σ (g : Matrix (Fin n) (Fin n) A) * (1 : Matrix (Fin n) (Fin n) B).map ι * (g : Matrix (Fin n) (Fin n) A) =
      (1 : Matrix (Fin n) (Fin n) B).map ι := hg
  rw [Matrix.map_one _ (map_zero ι) (map_one ι), mul_one] at h
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose, Matrix.det_one] at h2
  rw [mul_comm, RingHom.map_det]
  exact h2

theorem exists_isDetLift : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (n : ℕ) (g : GL (Fin n) (AfE H.F H.E)), g ∈ Formalism.L2.Herm.UstdAf (host_cmData R H) n → ∃ a : Neutral.B1.Ideles H.E, IsDetLift (host_cmData R H) g a := by
  intro R H n g hg
  have hr := (DetClass.exists_detClass R H (host_cmData R H).sig (fun x => bridge_star_holds R H x) (afIso H.F H.E)
    (afIso_tmul_one H.F H.E) (mem_rInt_iff H.F H.E)).1
  have hd : Matrix.GeneralLinearGroup.det g ∈ U1 (host_cmData R H).sig :=
    Units.ext (det_mul_conj_det _ _ hg)
  obtain ⟨x, hx⟩ := hr.ge hd
  obtain ⟨a, rfl⟩ := finAf_surjective H.F H.E x
  exact ⟨a, hx⟩

end GlobalTheory.Mem.DetLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DictionaryRationalElementAnalyticPointStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dictionary_rational_element_analytic_point : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (W : HSp D) (r : ℕ) (hr : W.rank = r) (U : Unf Xo c σ r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (g₀ : ℕ) (e₀ : Fin g₀ ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : ReciprocityTheory.ChartRestriction.G.Geo.Tor.FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e₀ j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (θ : InfFam D) (Z₀ : Fam W), GoodEmb c σ → IsUnf U → 1 ≤ r → IsInfFam θ → (∀ k τ, IsInfEmb τ.1 (th k τ)) → DictLat U W hr dict ι e₀ F ik φ th x₀ → (∀ ρ, x₀ (tauE D ρ) = Matrix.reindex (finCongr hr) (finCongr hr) (Z₀ ρ)) → ∀ h : GA D W, ∃ γ ∈ GQ W, MarkBy U W hr dict ι F ik φ h γ ∧ latW hr (U.X (dict h).1).Λ = latG W (γ * h) ∧ (∀ eT : D.what₂.Tau ≃ (U.X (dict h).1).Ψ, (∀ ρ, (eT ρ).1 = tauE D ρ) → (dict h).2 = frOf hr eT (mvZ θ (γ * h) Z₀)) ∧ ∀ (hx : (dict h).2 ∈ (U.X (dict h).1).dom) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X (dict h).1).Λ) (idx : Fin g ≃ (U.X (dict h).1).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), IsSympl (U.X (dict h).1) bas → Matched c σ (U.X (dict h).1) idx e → letI : Algebra c.F ℂ := σ.toAlgebra; ∀ (A : AnFib (U.X (dict h).1) bas idx e (dict h).2 (U.X (dict h).1).Λ (ptC U (dict h).1 ⟨(dict h).2, hx⟩)) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)), (∀ a, mk a ∈ (U.X (dict h).1).Λ) → MarkAd hr l ι (γ * h) mk → A.Marked mk := by
  first | exact @GlobalTheory.OneMapRef.DictPt.dict_point | exact GlobalTheory.OneMapRef.DictPt.dict_point | (intros; apply GlobalTheory.OneMapRef.DictPt.dict_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EasyInputs
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.EasyInputs

theorem smAll (D : D7) : SmAll D := fun V S M τ => by
  obtain ⟨w, hw, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (GlobalTheory.GardingVec.sm_ne_bot D V S M τ)
  exact ⟨⟨w, hw⟩, by simpa using h0⟩

theorem dimOK (D : D7) : DimOK D := fun i σ ρ => GlobalTheory.Mem.WeylDimPos.dimK_kapAt_Wc_pos D i σ ρ

theorem cartanOK (D : D7) : CartanOK D := by
  refine ⟨fun V S M _ τ => GlobalTheory.Chain.VacVec.cart_isCartanInv M τ, fun V hs hp τ => ?_⟩
  have h := GlobalTheory.RepsObj.gramAt_posDef hp hs τ
  exact ⟨by simp, by simp, by simpa using h⟩

theorem spOK (D : D7) : SpOK D := by
  refine ⟨fun τ => Or.inl ?_, fun τ => Or.inl (D.X'_posDef τ)⟩
  have hm : D.R.m - 1 ≤ D.R.m := Nat.sub_le _ _
  show (D.sp.Y (min (D.R.m - 1) D.R.m)).sig τ = ((D.sp.Y (min (D.R.m - 1) D.R.m)).rank, 0)
  rw [min_eq_left hm, D.Y_sigval _ hm τ, D.sp.Y_rank _ hm, sigYD]
  have := D.R.two_le_m
  have h1 : (D.R.m - (D.R.m - 1)) / 2 = 0 := by omega
  rw [h1, Nat.sub_zero]

theorem selfDualOK (D : D7) : SelfDualOK D := by
  rintro V β Λ N ⟨-, hd, hN, h1, h2⟩
  have hM0 : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hL := (GlobalTheory.PlaceModel.isSelfDualC_latFrame V).1
  rw [← GlobalTheory.PlaceModel.coe_latFrame] at h1 h2
  refine ⟨⟨?_, ?_⟩, fun y => ?_⟩
  · let f : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) :=
      (LinearMap.lsmul D.host.E (Fin V.rank → D.host.E) (N : D.host.E)⁻¹).restrictScalars (𝓞 D.host.E)
    refine (hL.fg.map f).of_le fun x hx => ⟨_, h2 x hx, ?_⟩
    change (N : D.host.E)⁻¹ • ((N : D.host.E) • x) = x
    rw [smul_smul, inv_mul_cancel₀ hM0, one_smul]
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · rw [← GlobalTheory.SDFrameLattice.mem_dualL_iff, hd]


open scoped Pointwise in
theorem petAll (D : D7) : PetAll D := by
  intro V μ 𝓕 hμ h𝓕 F hc hl h0 hi
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun g => by positivity) hi]
  have hs : Function.support (fun g => ‖F g‖ ^ 2) = Function.support F := by
    ext g
    simp [Function.mem_support]
  rw [hs, pos_iff_ne_zero]
  intro hz
  have hinv : ∀ γ : GQ V, γ • Function.support F = Function.support F := fun γ => by
    ext g
    rw [Set.mem_smul_set_iff_inv_smul_mem, Function.mem_support, Function.mem_support]
    have : F (γ⁻¹ • g) = F g := hl _ (γ⁻¹).2 g
    rw [this]
  have hzero := h𝓕.measure_zero_of_invariant _ hinv hz
  exact (hc.isOpen_support.measure_pos μ (Function.support_nonempty_iff.2 h0)).ne' hzero

theorem easy_inputs : ∀ D : D7, CartanOK D ∧ SelfDualOK D ∧ SpOK D ∧ DimOK D ∧ PetAll D ∧ SmAll D := fun D =>
  ⟨cartanOK D, selfDualOK D, spOK D, dimOK D, petAll D, smAll D⟩

end GlobalTheory.Mem.EasyInputs
end

