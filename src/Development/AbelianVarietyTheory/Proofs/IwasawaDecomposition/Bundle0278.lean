module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0264
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyExt
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
public import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Formalism.LocalToGlobal.PlaceMapInjectivity.MapPlInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Lean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0267
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdjointCompositeLiftRowMemSpanGoodRationalFormsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoint_compositeLift_row_mem_span_goodRationalForms : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → ∀ (uE : D.what₂.EE →ₗ[ℂ] R.HE.H), (∀ y, (Y.Ish.jE y).1 = PiTensorProduct.lift (R.HE.e (uE y))) → ∀ y, LinearMap.adjoint (R.Th A3.A.μ0) (uE y) ∈ Submodule.span ℂ (Set.range fun x => R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 ((rE D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec x))) := by
  first | exact @GlobalTheory.UpKeep3.adjoint_mem_span_rowForm | exact GlobalTheory.UpKeep3.adjoint_mem_span_rowForm | (intros; apply GlobalTheory.UpKeep3.adjoint_mem_span_rowForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardBaseRowsLabelEqRowsPartFinrankStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_baseRows_label_eq_rowsPart_finrank : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ cOf : D.what₂.FT → A3.fam3.base3.Ix, (∀ σ, HasLab Y σ (cOf σ)) → ∀ p : A3.fam3.base3.Ix, ∑ σ ∈ Finset.univ.filter (fun σ => cOf σ = p), D.what₂.nRows0 σ = Module.finrank D.what₂.LL ((s0Of R F).Ep p) := by
  first | exact @GlobalTheory.Mem.R3.LabCount.cnt | exact GlobalTheory.Mem.R3.LabCount.cnt | (intros; apply GlobalTheory.Mem.R3.LabCount.cnt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyDualTamePart
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.CyclotomicNorms Polynomial Module

namespace GlobalTheory.WeilDeligne.LabDual

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem charpoly_dualMap (f : End ℂ V) : (f.dualMap).charpoly = f.charpoly := by
  classical
  rw [← LinearMap.charpoly_toMatrix f (finBasis ℂ V),
    ← LinearMap.charpoly_toMatrix f.dualMap (finBasis ℂ V).dualBasis, ← Matrix.charpoly_transpose,
    LinearMap.dualMap_def, LinearMap.toMatrix_transpose, Matrix.transpose_transpose]

theorem exists_proj (a : WDRep h V) : ∃ e : End ℂ V, (∀ v, e v ∈ a.tameSpace) ∧
    (∀ v ∈ a.tameSpace, e v = v) ∧
    (∀ σ : Weil h, (σ : G E Ω) ∈ Wild E A → e * a.ρ σ = e) ∧
    ∀ f ∈ a.dual.tameSpace, ∀ v, f (e v) = f v := by
  classical
  let K : Subgroup (Weil h) := (Wild E A).subgroupOf (Weil h)
  let P : Subgroup (End ℂ V)ˣ := K.map a.ρ.toHomUnits
  have hfin : Finite P := by
    refine Set.Finite.of_finite_image (f := Units.val) (a.smooth.finite_range.subset ?_)
      Units.val_injective.injOn
    rintro _ ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩
    exact ⟨⟨σ, Wild_le_Ine hσ⟩, rfl⟩
  have := Fintype.ofFinite P
  have hc : (Fintype.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨(Fintype.card P : ℂ)⁻¹ • ∑ p : P, (p.1 : End ℂ V), fun v => ?_, fun v hv => ?_,
    fun σ hσ => ?_, fun f hf v => ?_⟩
  · refine a.mem_tameSpace.mpr fun σ hσ => ?_
    rw [← End.mul_apply, mul_smul_comm, Finset.mul_sum]
    congr 2
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨_, σ, hσ, rfl⟩ : P)) _ _ fun p => rfl
  · have : ∀ p : P, (p.1 : End ℂ V) v = v := by
      rintro ⟨_, σ, hσ, rfl⟩
      exact a.mem_tameSpace.mp hv σ hσ
    simp [this, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hc]
  · rw [smul_mul_assoc, Finset.sum_mul]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulRight (⟨_, σ, hσ, rfl⟩ : P)) _ _ fun p => rfl
  · have : ∀ p : P, f ((p.1 : End ℂ V) v) = f v := by
      rintro ⟨_, σ, hσ, rfl⟩
      have := LinearMap.congr_fun (a.dual.mem_tameSpace.mp hf σ⁻¹ (K.inv_mem hσ)) v
      simpa using this
    simp [this, hc]

theorem charpoly_dual_tamePart (a : WDRep h V) (σ : Weil h) :
    (a.dual.tamePart.ρ σ).charpoly = (a.tamePart.ρ σ⁻¹).charpoly := by
  obtain ⟨e, h1, h2, h3, h4⟩ := exists_proj a
  let r : a.dual.tameSpace →ₗ[ℂ] Dual ℂ a.tameSpace :=
    a.tameSpace.dualRestrict ∘ₗ a.dual.tameSpace.subtype
  have hr : Function.Bijective r := by
    refine ⟨(injective_iff_map_eq_zero r).mpr fun f hf => ?_, fun φ => ?_⟩
    · ext v
      rw [← h4 f.1 f.2 v]
      exact LinearMap.congr_fun hf ⟨e v, h1 v⟩
    · refine ⟨⟨φ ∘ₗ e.codRestrict _ h1, a.dual.mem_tameSpace.mpr fun u hu => ?_⟩, ?_⟩
      · ext v
        exact congrArg φ (Subtype.ext
          (LinearMap.congr_fun (h3 u⁻¹ ((Wild E A).inv_mem hu)) v))
      · ext v
        exact congrArg φ (Subtype.ext (h2 v v.2))
  rw [← charpoly_dualMap (a.tamePart.ρ σ⁻¹),
    ← LinearEquiv.charpoly_conj (LinearEquiv.ofBijective r hr)]
  congr 1
  refine LinearMap.ext fun v => ?_
  obtain ⟨v, rfl⟩ := (LinearEquiv.ofBijective r hr).surjective v
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  rfl

theorem tameEig_lpDual (x : WD h) {γ : G E Ω} (hγ : γ ∈ Ine (F := E) A) :
    WD.tameEig (WD.lpDual x) γ = (WD.tameEig x γ).map (·⁻¹) := by
  obtain ⟨k, hk, -, hk1⟩ := WD.exists_pow_tameEig x hγ
  induction x using WD.ind with
  | hP m a =>
    have hγ' := Ine_le_Weil h hγ
    obtain ⟨n, h0, -, hn⟩ := a.tame_tamePart.exists_pow_eq_one (γ := ⟨γ, hγ'⟩) hγ
    have hp : n * k - 1 + 1 = n * k := Nat.sub_add_cancel (Nat.mul_pos h0 hk)
    have h1 : a.tamePart.ρ (⟨γ, hγ'⟩ : Weil h)⁻¹ = a.tamePart.ρ ⟨γ, hγ'⟩ ^ (n * k - 1) := by
      rw [← one_mul (a.tamePart.ρ _), ← one_pow k, ← hn, ← pow_mul, ← hp, pow_succ, mul_assoc,
        ← map_mul, mul_inv_cancel, map_one, mul_one, hp]
    have h2 := GlobalTheory.CharpolyPow.roots_charpoly_pow ℂ _ (n * k - 1)
      (LinearMap.toMatrix (finBasis ℂ _) (finBasis ℂ _) (a.tamePart.ρ ⟨γ, hγ'⟩))
    rw [LinearMap.toMatrix_pow, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix] at h2
    rw [WD.tameEig_mk _ hγ'] at hk1
    rw [WD.lpDual_mk, WD.tameEig_mk _ hγ', WD.tameEig_mk _ hγ', charpoly_dual_tamePart, h1, h2]
    refine Multiset.map_congr rfl fun z hz => eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, hp, pow_mul', hk1 z hz, one_pow]

theorem rootsBar_lab_lpDual : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (g : ℕ) [Fact g.Prime] (τ : Fbar g →* ℂ) (γ : G E Ω), ∀ x : WD h,
    rootsBar (WD.lab τ γ (WD.lpDual x)) = (rootsBar (WD.lab τ γ x)).map (·⁻¹) := by
  intro E Ω _ _ _ _ _ A w h g _ τ γ x
  by_cases H : TeichmullerInertiaLabelCondition A w τ γ
  · refine Multiset.map_injective H.2.2.injective ?_
    rw [WD.map_rootsBar_lab H, tameEig_lpDual x H.2.1, ← WD.map_rootsBar_lab H, Multiset.map_map,
      Multiset.map_map]
    refine Multiset.map_congr rfl fun y _ => ?_
    show (τ y)⁻¹ = τ y⁻¹
    rcases eq_or_ne y 0 with rfl | hy
    · rw [inv_zero, H.2.2.map_zero, inv_zero]
    · exact inv_eq_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel₀ hy, map_one])
  · simp [WD.lab_of_not H, rootsBar]

end GlobalTheory.WeilDeligne.LabDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernFormPolyCoeffTopOfNegHermitianSquareStatement
section
open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernFormPolyCoeff_top_of_neg_hermitianSquare : ∀ {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) (S : Matrix (Fin m) (Fin m) ℂ)
    (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ), IsUnit S.det →
    (∀ ξ η, curv G v ξ η = S⁻¹ * (-(T ξ * (T η)ᴴ)) * S) → chernPoly G v m = (-1) ^ m * (sqPoly T).det := by
  first | exact @GlobalTheory.PointFormSign.chernPoly_top_of_negSq | exact GlobalTheory.PointFormSign.chernPoly_top_of_negSq | (intros; apply GlobalTheory.PointFormSign.chernPoly_top_of_negSq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ExtConj
variable {F : Type} [Field F] [NumberField F]

theorem valuation_lt_one_iff {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (y : AlgebraicClosure F) :
    e.O.valuation y < 1 ↔ e.w y < 1 := by
  rw [ReciprocityTheory.Gal.valuation_lt_one_iff', e.mem_O, e.mem_O, map_inv₀]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have h0 : 0 < e.w y := e.w.pos hy
    simp only [hy, false_or, not_le, one_lt_inv₀ h0]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

theorem lies_over {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (x : 𝓞 F) :
    e.O.valuation (algebraMap F (AlgebraicClosure F) (x : F)) < 1 ↔ x ∈ v.asIdeal := by
  rw [valuation_lt_one_iff, e.w_alg, ← FinitePlace.norm_embedding]
  exact FinitePlace.norm_lt_one_iff_mem F v x

theorem conj (v : HeightOneSpectrum (𝓞 F)) (e e' : Ext v) :
    ∃ g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, ∀ x, e'.w x = e.w (g x) := by
  obtain ⟨g, hg⟩ := ReciprocityTheory.Gal.exists_smul_eq_of_over (lies_over e) (lies_over e')
  refine ⟨g⁻¹, ?_⟩
  let u : AbsoluteValue (AlgebraicClosure F) ℝ :=
    e.w.comp (f := (g⁻¹ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F).toRingEquiv.toRingHom) (g⁻¹).injective
  have hu (x) : u x = e.w (g⁻¹ x) := rfl
  have he : u.IsEquiv e'.w := AbsoluteValue.isEquiv_iff_lt_one_iff.2 fun x => by
    rw [hu, ← valuation_lt_one_iff, ← valuation_lt_one_iff, ← hg, ReciprocityTheory.Gal.smul_valuation_lt_one_iff]
  obtain ⟨c, hc, hce⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have h1 : e'.w (algebraMap F _ (a : F)) < 1 := (valuation_lt_one_iff e' _).1 ((lies_over e' a).2 ha)
  have h0 : 0 < e'.w (algebraMap F _ (a : F)) := e'.w.pos (by simpa using ha0)
  have h2 : u (algebraMap F _ (a : F)) = e'.w (algebraMap F _ (a : F)) := by
    rw [hu, AlgEquiv.commutes, e.w_alg, e'.w_alg]
  have h3 := congrFun hce (algebraMap F _ (a : F))
  simp only [h2] at h3
  have hc1 : c = 1 := by
    have h4 := congrArg Real.log h3
    rw [Real.log_rpow h0] at h4
    have := (Real.log_neg h0 h1).ne
    exact mul_right_cancel₀ this (by rw [h4, one_mul])
  intro x
  rw [← hu, ← hce, hc1]
  simp

theorem factor {K : Type} [Field K] {X : Scheme.{0}} (y : Sp K ⟶ X) (x : X) (h : below y = x) :
    ∃ ψ : X.residueField x ⟶ CommRingCat.of K, Spec.map ψ ≫ X.fromSpecResidueField x = y := by
  subst h
  exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X y⟩

theorem below_comp {K : Type} [Field K] {X : Scheme.{0}} (x : X) (ψ : X.residueField x ⟶ CommRingCat.of K) :
    below (K := K) (Spec.map ψ ≫ X.fromSpecResidueField x) = x :=
  (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply x _)

theorem closed_point_geometric_fibres_finite {k K : Type} [Field k] [Field K] [Algebra k K] [IsAlgClosed K] {X : Scheme.{0}} (s : X ⟶ Sp k)
    [LocallyOfFiniteType s] (x : X) (hx : IsClosed ({x} : Set X)) :
    Nonempty {y : {y : Sp K ⟶ X // y ≫ s = spMap (algebraMap k K)} // below y.1 = x} ∧
      Finite {y : {y : Sp K ⟶ X // y ≫ s = spMap (algebraMap k K)} // below y.1 = x} := by
  have := isClosed_singleton_iff_isClosedImmersion.1 hx
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ s)
  have hfin : IsFinite (Spec.map φ) := by
    rw [hφ]
    exact isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 inferInstance
  letI : Algebra k (X.residueField x) := φ.hom.toAlgebra
  haveI : Module.Finite k (X.residueField x) := (IsFinite.SpecMap_iff φ).1 hfin
  have hP (ψ : X.residueField x →ₐ[k] K) :
      (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField x) ≫ s = spMap (algebraMap k K) := by
    have h : φ ≫ CommRingCat.ofHom ψ.toRingHom = CommRingCat.ofHom (algebraMap k K) :=
      CommRingCat.hom_ext ψ.comp_algebraMap
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    exact congrArg Spec.map h
  let P : (X.residueField x →ₐ[k] K) → {y : {y : Sp K ⟶ X // y ≫ s = spMap (algebraMap k K)} // below y.1 = x} :=
    fun ψ => ⟨⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField x, hP ψ⟩,
      below_comp x _⟩
  refine ⟨⟨P IsAlgClosed.lift⟩, Finite.of_surjective P ?_⟩
  rintro ⟨⟨y, hy⟩, hyx⟩
  obtain ⟨ψ, h⟩ := factor y x hyx
  have h2 : Spec.map (φ ≫ ψ) = Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [Spec.map_comp, hφ, ← Category.assoc, h]
    exact hy
  have h3 := Spec.map_injective h2
  exact ⟨⟨ψ.hom, fun a => congrArg (fun t => t.hom a) h3⟩, Subtype.ext (Subtype.ext h)⟩

theorem pts (Y : Var F) (x : Y.X) (hx : IsClosed ({x} : Set Y.X)) :
    Nonempty {y : AlgPt Y // below y.1 = x} ∧ Finite {y : AlgPt Y // below y.1 = x} :=
  closed_point_geometric_fibres_finite Y.str x hx

theorem main : ∀ (F : Type) [Field F] [NumberField F] , (∀ v : HeightOneSpectrum (𝓞 F), Nonempty (Ext v)) ∧ (∀ Y : Var F, ∀ x : Y.X, IsClosed ({x} : Set Y.X) → Nonempty {y : AlgPt Y // below y.1 = x} ∧ Finite {y : AlgPt Y // below y.1 = x}) ∧ ∀ (v : HeightOneSpectrum (𝓞 F)) (e e' : Ext v), ∃ g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, ∀ x, e'.w x = e.w (g x) :=
  fun _ _ _ => ⟨GlobalTheory.TrueGeoModel.nonempty_ext, pts, conj⟩

end GlobalTheory.TrueGeo.ExtConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffComposedPartialDerivListOfNodupStatement
section
open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_composedPartialDerivList_of_nodup : ∀ {σ : Type} [DecidableEq σ] (l : List σ), l.Nodup → ∀ (m : σ →₀ ℕ), (∀ v ∈ l, m v = 0) → ∀ (G : MvPolynomial σ ℂ), AddMonoidAlgebra.coeff (dList l G) m = AddMonoidAlgebra.coeff G (m + (l.map fun v => Finsupp.single v 1).sum) := by
  first | exact @GlobalTheory.CayleyBlock.coeff_dList_of_nodup | exact GlobalTheory.CayleyBlock.coeff_dList_of_nodup | (intros; apply GlobalTheory.CayleyBlock.coeff_dList_of_nodup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexSpanRationalLiftFormsEqBasePartStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexSpan_rationalLiftForms_eq_basePart : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (p : A3.fam3.base3.Ix), Submodule.span ℂ ((Z.jW i) '' ((s0Of R F).Wp i p : Set (Fin ((s0Of R F).dW i) → D.what₂.LL))) = (R.Wp3 i p).comap (Y.mj.eW i) := by
  first | exact @GlobalTheory.Mem.R3.RatSpan.span_jW_wp | exact GlobalTheory.Mem.R3.RatSpan.span_jW_wp | (intros; apply GlobalTheory.Mem.R3.RatSpan.span_jW_wp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousSplitCentre
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.IdeleCovolume GlobalTheory.HeckeOne Matrix

noncomputable section

namespace GlobalTheory.OneRep.SplitTwist

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_splitCentre : Continuous (splitCentre E a) := by
  have e : splitCentre E a = fun t : ℝ =>
      GeneralLinearGroup.scalar (Fin a) (infId E (expU fun _ : InfinitePlace E => (t : ℂ))) :=
    funext splitCentre_eq_scalar
  rw [e]
  refine Continuous.units_map _ ?_ |>.comp ((continuous_infId E).comp
    (continuous_expU.comp (continuous_pi fun _ => Complex.continuous_ofReal)))
  change Continuous fun x : Ad E => Matrix.diagonal fun _ : Fin a => x
  exact (continuous_pi fun _ => continuous_id).matrix_diagonal

end GlobalTheory.OneRep.SplitTwist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EllTInclTTprod
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.SchurTensor

theorem ellT_inclT_tprod {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : ∀ τ, M.H τ) (v : M.Vec) :
    ellT M w (inclT M (PiTensorProduct.tprod ℂ v)) = ∏ τ, ⟪w τ, (v τ : M.H τ)⟫_ℂ := by
  simp [ellT, inclT]

theorem schur_tensor : ∀ (D : D7) (θ : InfF D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), SchurMult θ M J χ μ 𝓕 → IsInfFam θ → IsQuot V μ 𝓕 → ∀ x ∈ MultT θ M J χ, ∀ y ∈ MultT θ M J χ, ∀ (v : SmT M) (w : M.Vec), IsCuspForm θ V (y (PiTensorProduct.tprod ℂ w)) ∧ IntegrableOn (fun g => star (x v g) * y (PiTensorProduct.tprod ℂ w) g) 𝓕 μ ∧ ∫ g in 𝓕, star (x v g) * y (PiTensorProduct.tprod ℂ w) g ∂μ = ipT M μ 𝓕 y x * star (ellT M (fun τ => (w τ : M.H τ)) (inclT M v)) := by
  intro D θ V S M J χ μ 𝓕 hS hθ hq x hx y hy v w
  have hx' := (mem_multT θ M J χ x).1 hx
  have hy' := (mem_multT θ M J χ y).1 hy
  have hm := (GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ _).1 hy'
  have hI := ipM_spec M μ 𝓕 _ _ (hS hθ hq.1 hq.2 _ hx' _ hy')
  refine ⟨⟨hm.aut w, hm.cusp w⟩, ?_⟩
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c u =>
    obtain ⟨h1, h2⟩ := hI u w
    have e : (fun g => star (x (c • PiTensorProduct.tprod ℂ u) g) * y (PiTensorProduct.tprod ℂ w) g) =
        fun g => star c * (star (x (PiTensorProduct.tprod ℂ u) g) * y (PiTensorProduct.tprod ℂ w) g) := by
      funext g
      rw [map_smul, Pi.smul_apply, smul_eq_mul, star_mul', mul_assoc]
    rw [e]
    refine ⟨h1.const_mul _, ?_⟩
    rw [integral_const_mul, map_smul, map_smul, ellT_inclT_tprod, smul_eq_mul, star_mul', star_prod]
    refine (congrArg (star c * ·) h2).trans ?_
    have e2 : ∏ τ, star ⟪(w τ : M.H τ), (u τ : M.H τ)⟫_ℂ = ∏ τ, ⟪(u τ : M.H τ), (w τ : M.H τ)⟫_ℂ :=
      Finset.prod_congr rfl fun τ _ => inner_conj_symm _ _
    rw [e2, ipT]
    ring
  | add a b ha hb =>
    have e : (fun g => star (x (a + b) g) * y (PiTensorProduct.tprod ℂ w) g) =
        fun g => star (x a g) * y (PiTensorProduct.tprod ℂ w) g + star (x b g) * y (PiTensorProduct.tprod ℂ w) g := by
      funext g
      rw [map_add (f := _), Pi.add_apply, star_add, add_mul]
    rw [e]
    refine ⟨ha.1.add hb.1, ?_⟩
    rw [integral_add ha.1 hb.1, ha.2, hb.2, map_add (f := _), map_add (f := _), star_add, mul_add]

end GlobalTheory.Mem.SchurTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColsTiedSym
section
noncomputable section

namespace GlobalTheory.Mem.SRe.ColRe

open Formalism.BasicNotions Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.SRe NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)


set_option maxHeartbeats 4000000 in
def colsRe (C : ColsTiedSym D) : ColsTiedSym (reD D Z) := (by with_unfolding_all exact ((@ColsTiedSym.mk (reD D Z) (hermRe Z C.herm) ((by with_unfolding_all exact ((fun u => formsRe Z (C.forms u)) :)))
    ((by with_unfolding_all exact (C.eV :)))
    ((by with_unfolding_all exact (C.piU :)))
    ((by with_unfolding_all exact (C.res :)))
    ((by with_unfolding_all exact (C.car0 :)))
    ((by with_unfolding_all exact (C.carC :)))
    ((by with_unfolding_all exact (C.carM :)))
    ((by with_unfolding_all exact (C.carP :)))
    ((by with_unfolding_all exact (C.lattice₂ :)))
    ((by with_unfolding_all exact (C.pr :)))
    ((by with_unfolding_all exact (C.prk :)))
    ((by with_unfolding_all exact (C.prC :)))
    ((by with_unfolding_all exact (C.z0 :)))
    ((by with_unfolding_all exact (C.ga :)))
    ((by with_unfolding_all exact (C.sp :)))
    ((by with_unfolding_all exact (C.piG :)))
    ((by with_unfolding_all exact (C.fr0 :)))
    ((by with_unfolding_all exact (C.gl_const :)))
    ((by with_unfolding_all exact (C.chi :)))
    ((by with_unfolding_all exact (C.frame_level_zero_const :)))
    ((by with_unfolding_all exact (C.frP_const :)))) :))


set_option maxHeartbeats 4000000 in
theorem sameF_colsRe (C : ColsTiedSym D) :
    SameForms0LevelsAndValues Z (fun u => (C.forms u).to0) (fun u => ((colsRe Z C).forms u).to0) := by
  intro u
  refine ⟨?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact ((Eq.refl (C.forms u).to0.cls0.lev) :))
  · exact (by with_unfolding_all exact ((Eq.refl (C.forms u).to0.cls0.y) :))
  · exact (by with_unfolding_all exact ((Eq.refl (C.forms u).to0.val0.eY) :))


set_option maxHeartbeats 4000000 in
theorem exists_colsTiedSym (D : D7) (Z : New D) (C : ColsTiedSym D) :
    ∃ C' : ColsTiedSym (reD D Z), SameForms0LevelsAndValues Z (fun u => (C.forms u).to0) (fun u => (C'.forms u).to0) :=
  ⟨colsRe Z C, sameF_colsRe Z C⟩

end GlobalTheory.Mem.SRe.ColRe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexificationOfDefiniteGroupFormsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complexification_of_definiteGroupForms' : ∀ (K O : Type) [Field K] [NumberField K] [StarRing K] [CommRing O] (o : O →+* K) (σ : K →+* ℂ) (G : Type) [Group G] [Fintype G] (m : Mat1 K G) (e : MonoidAlgebra K G), (∀ x, σ (star x) = starRingEnd ℂ (σ x)) → (∀ y, IsIntegral ℤ (o y)) → m.Laws σ e → ∃ s : Sp1 O (σ.comp o) G, Nonempty (Tie1 σ m s) := by
  intro K O _ _ _ _ o σ G _ _ m e hσ ho hm
  first
  | exact SpOfMat.exists_complexification_of_definiteGroupForms K O o σ G m e hσ ho hm
  | exact SpOfMat.exists_complexification_of_definiteGroupForms K O o σ G m e hσ ho hm hm.lat
end

