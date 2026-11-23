module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeterminantSectionRule
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.PremisesOfProper
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1852
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1853
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedFlatCoordinates
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0128
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEigenBasisTransportPullbackDvr
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.BdryUnit
open AlgebraicGeometry CategoryTheory Limits

set_option autoImplicit false

noncomputable section

open MonObj MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.IntEigTransport

theorem isTan_iff_isTangent' {V : Type} [CommRing V] {G : Over (Sp V)} [GrpObj G] (w : epsR V ⟶ G) :
    IsTan (V := V) (R := V) (G := G) w ↔ IsTangent w := by
  have : (1 : ptOver V V ⟶ G).left = η[G].left := by
    show spMap (algebraMap V V) ≫ _ = _
    rw [show spMap (algebraMap V V) = 𝟙 _ from Spec.map_id _]
    exact Category.id_comp _
  unfold IsTan IsTangent
  rw [this]

theorem transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (φ : c.F →+* T.V), (algebraMap T.V T.Fr).comp φ = io → ∀ (G : SAB H (Sp T.V)) (S : Scheme.{0}) (t : SAB H S) (x : Sp T.V ⟶ S) (n : SABMap G t x) (τ : E →+* ℂ) (k : ℕ) (ub : Fin k → (epsOver T.V T.V ⟶ G.G)), (∀ i, IsTan (ub i)) → (∀ i, IsEigV c io G τ (ub i)) → (∀ w : epsOver T.V T.V ⟶ G.G, IsTan w → IsEigV c io G τ w → ∃! a : Fin k → T.V, IsComb ub a w) → ∃ v : Fin k → (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.epsAt x ⟶ t.G), GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsEigenBasis t.act x (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ) v ∧ ∀ i, (v i).left = (ub i).left ≫ n.φ := by
  intro E _ _ _ H l c T io φ hio G S t x n τ k ub htan heig hbas
  have hz : ∀ (a : 𝓞 E) (z : T.V), algebraMap T.V T.Fr z = io (embK c τ a) → z = φ (embK c τ a) := by
    intro a z hz
    apply IsFractionRing.injective T.V T.Fr
    rw [hz, ← hio]; rfl
  have hE : ∀ w : epsR T.V ⟶ G.G, IsEigV c io G τ w ↔
      ∀ a, (w ≫ G.act.act a).left = spMap (epsScaleR (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ a)) ≫ w.left := by
    intro w
    constructor
    · intro h a
      exact h a (φ (embK c τ a)) (by rw [← hio]; rfl)
    · intro h a z hz'
      rw [hz a z hz']
      exact h a
  have hC : ∀ (a : Fin k → T.V) (w : epsR T.V ⟶ G.G), IsComb ub a w ↔ IsLieComb a ub w := fun a w => Iff.rfl
  have hv : GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsEigBasis G.act (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ) ub := by
    refine ⟨fun i => ⟨(isTan_iff_isTangent' _).1 (htan i), (hE _).1 (heig i)⟩, fun w hw => ?_⟩
    exact (existsUnique_congr fun a => hC a w).1 (hbas w ((isTan_iff_isTangent' _).2 hw.1) ((hE w).2 hw.2))
  obtain ⟨u, hu, hu'⟩ := GlobalTheory.FlatRow.exists_eigenBasis n hv
  exact ⟨u, hu, fun i => (hu' i).symm⟩

end GlobalTheory.IntEigTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberCurveOfClassEqSmulAddStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersectionNumber_curve_of_class_eq_smul_add : ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (L M M' : LB X) (hL : L.IsLB) (hM : M.IsLB) (hM' : M'.IsLB) (a b : ℕ) (C : Closeds X), IsCompleteCurve k C → cls L hL = a • cls M hM + b • cls M' hM' → interNumRed k C ![L] = a * interNumRed k C ![M] + b * interNumRed k C ![M'] := by
  first | exact @GlobalTheory.interNumRed_of_cls_eq_nsmul_add | exact GlobalTheory.interNumRed_of_cls_eq_nsmul_add | (intros; apply GlobalTheory.interNumRed_of_cls_eq_nsmul_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigLineBundleOfSmulClassEqAmpleAtAddNefStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBigLineBundle_of_smul_class_eq_ampleAt_add_nef : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N₁ N₂ : LB X) (hN : N.IsLB) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB) (a : ℕ) (x : X), IsNef k N → 0 < a → a • cls N hN = cls N₁ h₁ + cls N₂ h₂ → AmpleAt N₁ x → IsNef k N₂ → IsBig k N := by
  first | exact @GlobalTheory.isBig_of_smul_cls_eq_add_ampleAt | exact GlobalTheory.isBig_of_smul_cls_eq_add_ampleAt | (intros; apply GlobalTheory.isBig_of_smul_cls_eq_add_ampleAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralInConeDegreeOfValuativeBound
section
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DegVal.ValInt

theorem ratFunc_top_fg {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (h : (⊤ : IntermediateField K Ω).FG) :
    (⊤ : IntermediateField K (RatFunc Ω)).FG := by
  classical
  obtain ⟨S, hS⟩ := h
  refine ⟨insert RatFunc.X (S.image (algebraMap Ω (RatFunc Ω))), ?_⟩
  set F := IntermediateField.adjoin K
    (↑(insert RatFunc.X (S.image (algebraMap Ω (RatFunc Ω)))) : Set (RatFunc Ω)) with hF
  have hX : (RatFunc.X : RatFunc Ω) ∈ F := IntermediateField.subset_adjoin _ _ (by simp)
  have hc : ∀ a : Ω, algebraMap Ω (RatFunc Ω) a ∈ F := by
    intro a
    have ha : a ∈ IntermediateField.adjoin K (S : Set Ω) := hS ▸ IntermediateField.mem_top
    have hm : algebraMap Ω (RatFunc Ω) a ∈
        (IntermediateField.adjoin K (S : Set Ω)).map (IsScalarTower.toAlgHom K Ω (RatFunc Ω)) := ⟨a, ha, rfl⟩
    rw [IntermediateField.adjoin_map] at hm
    refine IntermediateField.adjoin.mono K _ _ ?_ hm
    rintro _ ⟨y, hy, rfl⟩
    exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hy))
  have hp : ∀ p : Polynomial Ω, algebraMap (Polynomial Ω) (RatFunc Ω) p ∈ F := by
    intro p
    induction p using Polynomial.induction_on with
    | C a => rw [RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C]; exact hc a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial n a ih => rw [pow_succ, ← mul_assoc, map_mul, RatFunc.algebraMap_X]; exact mul_mem ih hX
  refine eq_top_iff.2 fun x _ => ?_
  rw [← RatFunc.num_div_denom x]
  exact div_mem (hp _) (hp _)

theorem isIntegral_of_map_subalgebra {K R L : Type} [Field K] [CommRing R] [Algebra K R] [CommRing L] [Algebra K L]
    (φ : R →ₐ[K] L) (hφ : Function.Injective φ) (B : Subalgebra K R) (y : R)
    (h : IsIntegral (B.map φ) (φ y)) : IsIntegral B y := by
  let e := B.equivMapOfInjective φ hφ
  obtain ⟨p, hm, hp⟩ := h
  refine ⟨p.map e.symm.toRingHom, hm.map _, hφ ?_⟩
  rw [map_zero, ← hp]
  change φ.toRingHom _ = _
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map]
  congr 1
  ext x
  exact congrArg Subtype.val (e.apply_symm_apply x)

theorem coneAlg_fg {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    [FiniteDimensional K V] (ev : V →ₗ[K] Ω) : (coneAlg ev).FG := by
  let b := Module.finBasis K V
  let ψ : V →ₗ[K] Polynomial Ω := (LinearMap.mulLeft K (Polynomial.X : Polynomial Ω)) ∘ₗ
    (IsScalarTower.toAlgHom K Ω (Polynomial Ω)).toLinearMap ∘ₗ ev
  have e : coneAlg ev = Algebra.adjoin K (ψ '' Set.range b) := by
    rw [← Algebra.adjoin_span, ← Submodule.map_span, b.span_eq, Submodule.map_top]
    rfl
  exact Subalgebra.fg_def.2 ⟨_, (Set.finite_range b).image ψ, e.symm⟩

theorem isIntDeg_of_valBound : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω), CharZero K → FiniteDimensional K V → (⊤ : IntermediateField K Ω).FG →
    ∀ (τ : ℕ) (t : Ω), ValBound ev τ t → IsIntDeg ev τ t := by
  intro K V Ω _ _ _ _ _ ev hK hV hfg τ t hb
  have := hK
  have := hV
  let φ : Polynomial Ω →ₐ[K] RatFunc Ω := IsScalarTower.toAlgHom K (Polynomial Ω) (RatFunc Ω)
  have hφ : Function.Injective φ := RatFunc.algebraMap_injective Ω
  have hφa : ∀ p, φ p = algebraMap (Polynomial Ω) (RatFunc Ω) p := fun _ => rfl
  refine isIntegral_of_map_subalgebra φ hφ _ _ (_root_.GlobalTheory.DegVal.isIntegral_of_forall_realValuation_le_one K (RatFunc Ω) (ratFunc_top_fg hfg)
    ((coneAlg ev).map φ) ((coneAlg_fg ev).map φ) _ fun μ hμ => ?_)
  have hK1 : ∀ a : K, a ≠ 0 → μ (algebraMap K (RatFunc Ω) a) = 1 := by
    intro a ha
    have h1 : μ (algebraMap K (RatFunc Ω) a) ≤ 1 := hμ _ (Subalgebra.algebraMap_mem _ a)
    have h2 : μ (algebraMap K (RatFunc Ω) a⁻¹) ≤ 1 := hμ _ (Subalgebra.algebraMap_mem _ a⁻¹)
    have h3 : μ (algebraMap K (RatFunc Ω) a) * μ (algebraMap K (RatFunc Ω) a⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel₀ ha, map_one, map_one]
    refine le_antisymm h1 ?_
    calc (1 : ℝ≥0) = _ := h3.symm
      _ ≤ μ (algebraMap K (RatFunc Ω) a) := mul_le_of_le_one_right zero_le h2
  obtain ⟨v, hv⟩ := hb (μ.comap (algebraMap Ω (RatFunc Ω))) fun a ha => by
    rw [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply]; exact hK1 a ha
  rw [Valuation.comap_apply, Valuation.comap_apply] at hv
  have hXv : μ (RatFunc.X * algebraMap Ω (RatFunc Ω) (ev v)) ≤ 1 := by
    refine hμ _ (Subalgebra.mem_map.2 ⟨_, Algebra.subset_adjoin ⟨v, rfl⟩, ?_⟩)
    rw [hφa, map_mul, RatFunc.algebraMap_X, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
  rw [hφa, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C, map_mul, map_pow]
  calc μ RatFunc.X ^ τ * μ (algebraMap Ω (RatFunc Ω) t)
      ≤ μ RatFunc.X ^ τ * μ (algebraMap Ω (RatFunc Ω) (ev v)) ^ τ := mul_le_mul_of_nonneg_left hv zero_le
    _ = μ (RatFunc.X * algebraMap Ω (RatFunc Ω) (ev v)) ^ τ := by rw [map_mul, mul_pow]
    _ ≤ 1 := pow_le_one₀ zero_le hXv

end GlobalTheory.DegVal.ValInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleBaseChangeFieldExtensionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNefLineBundle_baseChange_field_extension : GlobalTheory.Published.NefNumerics → ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → letI := algebraΓOfHom p; letI := algebraΓOfHom q; ∀ L : LB Y, IsNef k L → IsNef E (L.pull π) := by
  first | exact @GlobalTheory.NefFieldExt.isNef_baseChange | exact GlobalTheory.NefFieldExt.isNef_baseChange | (intros; apply GlobalTheory.NefFieldExt.isNef_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor

namespace GlobalTheory.DetLine

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E}

section Generic

variable {S X : Scheme.{0}} {F : Type} [Field F]

def FrameCover (t : SAB H S) (π : X ⟶ S) (s : X ⟶ Sp F) (V : Set X) (χ : 𝓞 E →+* F) (p q : ℕ) : Prop :=
  ∀ z ∈ V, ∃ (W : X.Opens) (hW : IsAffineOpen W) (j : F →+* Γ(X, W))
    (v : Fin p → (epsAt ((show Sp Γ(X, W) ⟶ X from hW.fromSpec) ≫ π) ⟶ t.G))
    (w : Fin q → (epsAt ((show Sp Γ(X, W) ⟶ X from hW.fromSpec) ≫ π) ⟶ t.G)),
    z ∈ W ∧ IsFrame t π s V χ j (show Sp Γ(X, W) ⟶ X from hW.fromSpec) v w

def IsChg (t : SAB H S) (π : X ⟶ S) {p q : ℕ} {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R')
    (x : Sp R ⟶ X) (v : Fin p → (epsAt (x ≫ π) ⟶ t.G)) (w : Fin q → (epsAt (x ≫ π) ⟶ t.G))
    (x' : Sp R' ⟶ X) (v' : Fin p → (epsAt (x' ≫ π) ⟶ t.G)) (w' : Fin q → (epsAt (x' ≫ π) ⟶ t.G))
    (M : Matrix (Fin p) (Fin p) R') (N : Matrix (Fin q) (Fin q) R') : Prop :=
  x' = spMap g ≫ x ∧
    (∀ i, FramedFlatCoordinates.IsCombination (x' ≫ π) (M i) (fun k => spMap (Chart.dualMapR g) ≫ (v k).left) (v' i)) ∧
    ∀ i, FramedFlatCoordinates.IsCombination (x' ≫ π) (N i) (fun k => spMap (Chart.dualMapR g) ≫ (w k).left) (w' i)

def locPt (Y : Scheme.{0}) (y : Y) : Sp (Y.presheaf.stalk y) ⟶ Y := Y.fromSpecStalk y

def genPt (Y : Scheme.{0}) [IsIntegral Y] : Sp Y.functionField ⟶ Y := Y.fromSpecStalk (genericPoint Y)

def UnitAtPt (t : SAB H S) (π : X ⟶ S) (s : X ⟶ Sp F) (V : Set X) (χ : 𝓞 E →+* F) {p q : ℕ}
    {Y : Scheme.{0}} [IsIntegral Y] (io : Y ⟶ X) (v₀ : Fin p → (epsAt ((genPt Y ≫ io) ≫ π) ⟶ t.G))
    (w₀ : Fin q → (epsAt ((genPt Y ≫ io) ≫ π) ⟶ t.G)) (δ : Y.functionField) (y : Y) : Prop :=
  ∃ (j : F →+* Y.presheaf.stalk y) (v : Fin p → (epsAt ((locPt Y y ≫ io) ≫ π) ⟶ t.G))
    (w : Fin q → (epsAt ((locPt Y y ≫ io) ≫ π) ⟶ t.G)) (M : Matrix (Fin p) (Fin p) Y.functionField)
    (N : Matrix (Fin q) (Fin q) Y.functionField) (u : (Y.presheaf.stalk y)ˣ),
    IsFrame t π s V χ j (locPt Y y ≫ io) v w ∧
    IsChg t π (algebraMap (Y.presheaf.stalk y) Y.functionField) (locPt Y y ≫ io) v w (genPt Y ≫ io) v₀ w₀ M N ∧
    N.det * algebraMap (Y.presheaf.stalk y) Y.functionField u = M.det * δ

end Generic

variable {D : Datum H} {l : Level H}

theorem comp_chi (c : Coeff l) (τ : E →+* ℂ) {R : Type} [CommRing R] (j : c.F →+* R) :
    j.comp (HermitianCompactForm.chi c τ) = FramedFlatCoordinates.chr c τ j := rfl

theorem comp_chi_bar (c : Coeff l) (τ : E →+* ℂ) {R : Type} [CommRing R] (j : c.F →+* R) :
    j.comp ((HermitianCompactForm.chi c τ).comp (H.bar : 𝓞 E →+* 𝓞 E)) = FramedFlatCoordinates.chr c (conjEmb τ) j := by
  refine RingHom.ext fun a => congrArg j (Subtype.ext ?_)
  change τ ((H.bar a : 𝓞 E) : E) = starRingEnd ℂ (τ (a : E))
  rw [H.bar_eq]
  exact IsCMField.complexEmbedding_complexConj E τ _

section Laws

variable {S X : Scheme.{0}} {c : Coeff l} {t : SAB H S} {π : X ⟶ S} {s : X ⟶ Sp c.F} {V : Set X} {τ : E →+* ℂ}
  {p q : ℕ} {R R' : Type} [CommRing R] [CommRing R']

theorem exists_pull (g : R →+* R') {j : c.F →+* R} {x : Sp R ⟶ X} {v : Fin p → (epsAt (x ≫ π) ⟶ t.G)}
    {w : Fin q → (epsAt (x ≫ π) ⟶ t.G)} (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) {x' : Sp R' ⟶ X}
    (hx : x' = spMap g ≫ x) :
    ∃ (v' : Fin p → (epsAt (x' ≫ π) ⟶ t.G)) (w' : Fin q → (epsAt (x' ≫ π) ⟶ t.G)),
      IsFrame t π s V (HermitianCompactForm.chi c τ) (g.comp j) x' v' w' ∧
      (∀ i, (v' i).left = spMap (Chart.dualMapR g) ≫ (v i).left) ∧
      ∀ i, (w' i).left = spMap (Chart.dualMapR g) ≫ (w i).left := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e : x' ≫ π = spMap g ≫ x ≫ π := by rw [hx, Category.assoc]
  rw [comp_chi_bar] at h4
  obtain ⟨v', a, a'⟩ := DetExtendZero.exists_basis (FlatRow.eigStable t c) g e (τ := τ) h3
  obtain ⟨w', b, b'⟩ := DetExtendZero.exists_basis (FlatRow.eigStable t c) g e (τ := conjEmb τ) h4
  refine ⟨v', w', ⟨?_, ?_, a, by rw [comp_chi_bar]; exact b⟩, a', b'⟩
  · rw [hx, Category.assoc, h1, DetExtendZero.spMap_comp]
  · rintro _ ⟨z, rfl⟩
    rw [hx, Scheme.Hom.comp_apply]
    exact h2 ⟨_, rfl⟩

theorem exists_chg (g : R →+* R') {j : c.F →+* R} {j' : c.F →+* R'} {x : Sp R ⟶ X}
    {v : Fin p → (epsAt (x ≫ π) ⟶ t.G)} {w : Fin q → (epsAt (x ≫ π) ⟶ t.G)} {x' : Sp R' ⟶ X}
    {v' : Fin p → (epsAt (x' ≫ π) ⟶ t.G)} {w' : Fin q → (epsAt (x' ≫ π) ⟶ t.G)}
    (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) (h' : IsFrame t π s V (HermitianCompactForm.chi c τ) j' x' v' w') (hx : x' = spMap g ≫ x) :
    j' = g.comp j ∧ ∃ M N, IsChg t π g x v w x' v' w' M N := by
  obtain ⟨v₁, w₁, h₁, a, b⟩ := exists_pull g h hx
  have hj : j' = g.comp j := by
    have := h'.1.symm.trans h₁.1
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  subst hj
  choose M hM using fun i => (h₁.2.2.1.2 _ (h'.2.2.1.1 i)).exists
  choose N hN using fun i => (h₁.2.2.2.2 _ (h'.2.2.2.1 i)).exists
  refine ⟨rfl, Matrix.of M, Matrix.of N, hx, fun i => ?_, fun i => ?_⟩
  · simp only [← a]; exact hM i
  · simp only [← b]; exact hN i

theorem sec_chg {σ : Rule t π p q} (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ) {g : R →+* R'} {j : c.F →+* R}
    {j' : c.F →+* R'} {x : Sp R ⟶ X} {v : Fin p → (epsAt (x ≫ π) ⟶ t.G)} {w : Fin q → (epsAt (x ≫ π) ⟶ t.G)}
    {x' : Sp R' ⟶ X} {v' : Fin p → (epsAt (x' ≫ π) ⟶ t.G)} {w' : Fin q → (epsAt (x' ≫ π) ⟶ t.G)}
    (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) (h' : IsFrame t π s V (HermitianCompactForm.chi c τ) j' x' v' w') {M N}
    (hc : IsChg t π g x v w x' v' w' M N) : N.det * g (σ R x v w) = M.det * σ R' x' v' w' := by
  obtain ⟨v₁, w₁, h₁, a, b⟩ := exists_pull g h hc.1
  obtain rfl := (exists_chg g h h' hc.1).1
  rw [← hσ.1 R R' g (Chart.dualMapR g) j _ x x' v w v₁ w₁ (fun a => by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by ext <;> simp [Chart.dualMapR]) h h₁ hc.1 a b]
  refine hσ.2 R' _ x' v₁ w₁ v' w' M N h₁ h' (fun i => ?_) fun i => ?_
  · have := hc.2.1 i
    simp only [← a] at this
    exact this
  · have := hc.2.2 i
    simp only [← b] at this
    exact this

theorem isSection_of_chg {σ : Rule t π p q}
    (hσ : ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (j : c.F →+* R) (j' : c.F →+* R') x v w x' v' w' M N,
      IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w → IsFrame t π s V (HermitianCompactForm.chi c τ) j' x' v' w' → IsChg t π g x v w x' v' w' M N →
      N.det * g (σ R x v w) = M.det * σ R' x' v' w') : IsSection t π s V (HermitianCompactForm.chi c τ) σ := by
  refine ⟨fun R R' _ _ g gε j j' x x' v w v' w' h1 h2 h h' hx a b => ?_, fun R _ j x v w v' w' M N h h' a b => ?_⟩
  · obtain rfl : gε = Chart.dualMapR g := by
      refine RingHom.ext fun z => ?_
      have e : z = algebraMap R _ z.fst + algebraMap R _ z.snd * DualNumber.eps := by
        ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [e, map_add (f := _), map_mul, h1, h1, h2]
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
    have := hσ R R' g j j' x v w x' v' w' 1 1 h h' ⟨hx, fun i => ?_, fun i => ?_⟩
    · simpa using this.symm
    · simp only [← a]; exact DetExtendZero.comb_one (fun k => (h'.2.2.1.1 k).1) i
    · simp only [← b]; exact DetExtendZero.comb_one (fun k => (h'.2.2.2.1 k).1) i
  · refine hσ R R (RingHom.id R) j j x v w x v' w' M N h h'
      ⟨by rw [DetExtendZero.spMap_id, Category.id_comp], fun i => ?_, fun i => ?_⟩
    · simp only [DetExtendZero.dual_id, Category.id_comp]; exact a i
    · simp only [DetExtendZero.dual_id, Category.id_comp]; exact b i

end Laws

section Concrete

variable (Xo : Moduli D l) (c : Coeff l)

abbrev FrU (U : Set (Xo.XF c)) (τ : E →+* ℂ) {R : Type} [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ Xo.XF c)
    (v : Fin D.p → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)) (w : Fin D.q → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)) : Prop :=
  IsFrame Xo.univ.t (toX Xo c) (toF Xo c) U (HermitianCompactForm.chi c τ) j x v w

abbrev RuleU : Type 1 := Rule Xo.univ.t (toX Xo c) D.p D.q

abbrev SecU (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σ : RuleU Xo c) : Prop :=
  IsSection Xo.univ.t (toX Xo c) (toF Xo c) U (HermitianCompactForm.chi c τ) σ

abbrev NzU (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σ : RuleU Xo c) : Prop :=
  NowhereZero Xo.univ.t (toX Xo c) (toF Xo c) U (HermitianCompactForm.chi c τ) σ

variable {Xo c} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)

abbrev FrY (V : Set (gen Y)) (τ : E →+* ℂ) {R : Type} [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ gen Y)
    (v : Fin D.p → (epsAt (x ≫ genι Y) ⟶ Y.t.G)) (w : Fin D.q → (epsAt (x ≫ genι Y) ⟶ Y.t.G)) : Prop :=
  IsFrame Y.t (genι Y) (genStr Y) V (HermitianCompactForm.chi c τ) j x v w

abbrev RuleY : Type 1 := Rule Y.t (genι Y) D.p D.q

abbrev SecY (V : Set (gen Y)) (τ : E →+* ℂ) (σ : RuleY Y) : Prop :=
  IsSection Y.t (genι Y) (genStr Y) V (HermitianCompactForm.chi c τ) σ

abbrev NzY (V : Set (gen Y)) (τ : E →+* ℂ) (σ : RuleY Y) : Prop :=
  NowhereZero Y.t (genι Y) (genStr Y) V (HermitianCompactForm.chi c τ) σ

variable {Y}

def Match (τ : E →+* ℂ) {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Y.X} (f : EigFrame Y φ x)
    (v : Fin D.p → (epsAt x ⟶ Y.t.G)) (w : Fin D.q → (epsAt x ⟶ Y.t.G)) : Prop :=
  (∀ (i : Fin D.p) (k : Fin (D.mult τ)), (i : ℕ) = k → (v i).left = f.v τ k) ∧
    ∀ (i : Fin D.q) (k : Fin (D.mult (conjEmb τ))), (i : ℕ) = k → (w i).left = f.v (conjEmb τ) k

def PerData (c : Coeff l) (e : c.F →+* ℂ) (Di : Datum H) {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (P : Di.La →+ (Fin g → ℂ)) (W : Pad.Letter D → Fin g → ℂ) (Q : Di.La →+ (Pad.Letter D → ℂ)) : Prop :=
  Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (herm Hm z z).re) ∧ Submodule.span ℝ (Set.range P) = ⊤ ∧
    (∀ a b, (herm Hm (P a) (P b)).im = Di.EF a b) ∧ LinearIndependent ℂ W ∧ (∀ v, P v = ∑ z, Q v z • W z) ∧
    ∀ (a : 𝓞 E) v (z : Pad.Letter D), Q (a • v) z = Formalism.L2.PjFree.relab c e z.1 (a : E) * Q v z

def MatchVec (τ : E →+* ℂ) {g : ℕ} (W : Pad.Letter D → Fin g → ℂ) (V : Fin D.p → Fin g → ℂ)
    (W₀ : Fin D.q → Fin g → ℂ) : Prop :=
  (∀ (i : Fin D.p) (k : Fin (D.mult τ)), (i : ℕ) = k → V i = W ⟨τ, k⟩) ∧
    ∀ (i : Fin D.q) (k : Fin (D.mult (conjEmb τ))), (i : ℕ) = k → W₀ i = W ⟨conjEmb τ, k⟩

end Concrete

end GlobalTheory.DetLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelHalfSplit
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SplitLevel

theorem level_halfSplit : ∀ (D : D7) (T : Core D), LawsM T → ∀ (_ : ErrX D), ∃ π π' : 𝓞 D.host.E, HalfSplit T.Q.l (D.host.g 0) (D.host.g 1) π π' := by
  intro D T h EX
  have hp : ∀ i, piOf T EX i * T.Q.H.bar (piOf T EX i) = ((D.host.g i : ℕ) : 𝓞 D.host.E) := fun i => by
    rw [bar_core]; exact piOf_mul_barE T EX i
  have hM : T.Q.l.Mb = Ideal.span {piOf T EX 0 * piOf T EX 1} := by
    rw [← Ideal.span_singleton_mul_span_singleton, span_piOf T h, span_piOf T h, Mb_eq T h]
  exact ⟨piOf T EX 0, piOf T EX 1, D.host.g_prime 0, D.host.g_prime 1, D.host.g_ne,
    by rw [level_M T h, mul_comm], hp 0, hp 1, hM,
    GlobalTheory.LevelSplit.splitsIn_level_prime D 0, GlobalTheory.LevelSplit.splitsIn_level_prime D 1⟩

end GlobalTheory.SplitLevel
end

