module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0846
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0982
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWEigenpartEqRowsFullHecke
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1058

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthEqChartValueAndSum
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth

namespace GlobalTheory.FactorDepth

theorem nuFac_eq_nuFacC_and_nuProd_eq_nuP :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing;
      ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io)
        (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p),
        (∀ (f : Lt1 Dw) (k : ℕ), nuFac p y f k = nuFacC Ch X f k) ∧
          ∀ cx : Lt1 Dw → ℕ, nuProd p y cx = nuP p y cx := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ T io y Ch X
  have hc : ∀ (Ch' : IntegralChartA3 Xo c T io y) (X' : ValExt T p) (f : Lt1 Dw) (k : ℕ),
      nuFacC Ch' X' f k = nuFacC Ch X f k := fun Ch' X' f k =>
    (GlobalTheory.T.detFactorDepthInChart_chart_independent E H Dw l Xo c p T io y Ch' Ch X' f k).trans
      (GlobalTheory.T.detFactorDepthInChart_independent_closedField E H Dw l Xo c p T io y Ch X' X f k)
  have h1 : ∀ (f : Lt1 Dw) (k : ℕ), nuFac p y f k = nuFacC Ch X f k := fun f k =>
    le_antisymm (nuFac_le Ch X f k) (le_nuFac fun Ch' X' => (hc Ch' X' f k).ge)
  refine ⟨h1, fun cx => ?_⟩
  have h2 : ∀ (Ch' : IntegralChartA3 Xo c T io y) (X' : ValExt T p), nuProdC Ch' X' cx = nuP p y cx := by
    intro Ch' X'
    rw [GlobalTheory.T.detProductDepthInChart_eq_sum_factorDepths E H Dw l Xo c p T io y Ch' X' cx, nuP]
    exact Finset.sum_congr rfl fun f _ => (hc Ch' X' f (cx f)).trans (h1 f (cx f)).symm
  exact le_antisymm (iInf_le_of_le Ch (iInf_le_of_le X (h2 Ch X).le))
    (le_iInf₂ fun Ch' X' => (h2 Ch' X').ge)

end GlobalTheory.FactorDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetTwistedSylvesterSqMulDetPowEqResultantSq
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc

theorem sign_sq_eq_one_of_pow {k : Type} [Field k] (n : ℕ) : ((-1 : k) ^ n) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]

theorem det_adL_sq_mul_det_pow : ∀ (k : Type) [Field k] (a b : ℕ) (A : GL (Fin a) k)
    (B : Matrix (Fin b) (Fin b) k),
    LinearMap.det (GlobalTheory.LeviDesc.adL A B) ^ 2 * A.val.det ^ (2 * b)
      = resultant A.val.charpoly B.charpoly ^ 2 := by
  intro k _ a b A B
  let e : Matrix (Fin a) (Fin b) k ≃ₗ[k] ((Fin b → k) →ₗ[k] (Fin a → k)) := Matrix.toLin'
  let F : ((Fin b → k) →ₗ[k] (Fin a → k)) →ₗ[k] ((Fin b → k) →ₗ[k] (Fin a → k)) :=
    LinearMap.llcomp k (Fin b → k) (Fin a → k) (Fin a → k) (Matrix.toLin' A.val)
  let G : ((Fin b → k) →ₗ[k] (Fin a → k)) →ₗ[k] ((Fin b → k) →ₗ[k] (Fin a → k)) :=
    LinearMap.lcomp k (Fin a → k) (Matrix.toLin' B)
  have hcomp : F ∘ₗ ((e : _ →ₗ[k] _) ∘ₗ GlobalTheory.LeviDesc.adL A B ∘ₗ (e.symm : _ →ₗ[k] _)) = F - G := by
    apply LinearMap.ext
    intro ψ
    obtain ⟨X, rfl⟩ := e.surjective ψ
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.sub_apply, F, G, e, LinearMap.llcomp_apply, LinearMap.lcomp_apply,
      GlobalTheory.LeviDesc.adL, LinearMap.coe_mk, AddHom.coe_mk]
    change Matrix.toLin' A.val ∘ₗ Matrix.toLin' (X - (A⁻¹ : GL (Fin a) k).val * X * B)
      = Matrix.toLin' A.val ∘ₗ Matrix.toLin' X - Matrix.toLin' X ∘ₗ Matrix.toLin' B
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, ← map_sub]
    congr 1
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mul]
  have h1 := congrArg LinearMap.det hcomp
  rw [LinearMap.det_comp, LinearMap.det_conj, GlobalTheory.DetAdResultant.det_ad_eq_resultant,
    Matrix.charpoly_toLin', Matrix.charpoly_toLin'] at h1
  have hz : (0 : (Fin b → k) →ₗ[k] (Fin b → k)).charpoly = X ^ b := by
    rw [← (Matrix.toLin' : Matrix (Fin b) (Fin b) k ≃ₗ[k] _).map_zero, Matrix.charpoly_toLin',
      Matrix.charpoly_zero, Fintype.card_fin]
  have hF0 : F - LinearMap.lcomp k (Fin a → k) (0 : (Fin b → k) →ₗ[k] (Fin b → k)) = F := by
    apply LinearMap.ext
    intro ψ
    apply LinearMap.ext
    intro v
    simp [F]
  have h0 : LinearMap.det F = (-1) ^ (a * b) * A.val.charpoly.coeff 0 ^ b := by
    have h := GlobalTheory.DetAdResultant.det_ad_eq_resultant k (Fin a → k) (Fin b → k) (Matrix.toLin' A.val) 0
    rw [hF0, Matrix.charpoly_toLin', hz] at h
    rw [h, natDegree_X_pow, resultant_X_pow_right _ _ _ le_rfl, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  rw [← h1, h0, pow_mul, Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin, mul_pow ((-1 : k) ^ a),
    sign_sq_eq_one_of_pow, one_mul]
  have hs := sign_sq_eq_one_of_pow (k := k) (a * b)
  linear_combination (-(LinearMap.det (GlobalTheory.LeviDesc.adL A B) ^ 2 * (A.val.charpoly.coeff 0 ^ b) ^ 2)) * hs

end GlobalTheory.LeviDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSpaceOfClosedImmersionContainsDiagonal
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagPush

theorem dbl_of_isClosedImmersion_lift : ∀ (F : Type) [Field F] (Y : Var F) (Z : Scheme.{0}) [IsIntegral Z] (p₁ p₂ : Z ⟶ Y.X) (h : p₁ ≫ Y.str = p₂ ≫ Y.str), IsClosedImmersion (Limits.pullback.lift p₁ p₂ h) → Limits.pullback.diagonal Y.str (genericPoint Y.X) ∈ Set.range (Limits.pullback.lift p₁ p₂ h) → IsProjOver (p₁ ≫ Y.str) ∧ ∃ δ : Y.X ⟶ Z, IsClosedImmersion δ ∧ δ ≫ p₁ = 𝟙 _ ∧ δ ≫ p₂ = 𝟙 _ ∧ ∀ (K : Type) [Field K] (w : Sp K ⟶ Z), w ≫ p₁ = w ≫ p₂ → w (IsLocalRing.closedPoint K) ∈ Set.range δ := by
  intro F _ Y Z _ p₁ p₂ h hi hη
  have hp₁ : p₁ = Limits.pullback.lift p₁ p₂ h ≫ Limits.pullback.fst Y.str Y.str :=
    (Limits.pullback.lift_fst _ _ _).symm
  have hp₂ : p₂ = Limits.pullback.lift p₁ p₂ h ≫ Limits.pullback.snd Y.str Y.str :=
    (Limits.pullback.lift_snd _ _ _).symm
  refine ⟨?_, ?_⟩
  · rw [hp₁, Category.assoc]
    exact ProjSpace.isProjOver_comp_of_isClosedImmersion _
      (ProjSpace.isProjOver_pullback Y.isProjOver Y.isProjOver)
  have hc : IsClosed (Set.range (Limits.pullback.lift p₁ p₂ h)) :=
    (Limits.pullback.lift p₁ p₂ h).isClosedEmbedding.isClosed_range
  have hrange : Set.range (Limits.pullback.diagonal Y.str) ⊆ Set.range (Limits.pullback.lift p₁ p₂ h) := by
    rintro _ ⟨y, rfl⟩
    have hs := ((genericPoint_spec Y.X).specializes (Set.mem_univ y)).map
      (Limits.pullback.diagonal Y.str).continuous
    exact hs.mem_closed hc hη
  have hle : (Limits.pullback.lift p₁ p₂ h).ker ≤ (Limits.pullback.diagonal Y.str).ker := by
    refine le_trans ?_ (ReducedSubgroup.vanishingIdeal_le_ker _ ⟨_, hc⟩ hrange)
    rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    exact (Limits.pullback.lift p₁ p₂ h).range_subset_ker_support
  have hδ := IsClosedImmersion.lift_fac (Limits.pullback.lift p₁ p₂ h) (Limits.pullback.diagonal Y.str) hle
  refine ⟨IsClosedImmersion.lift _ _ hle, ?_, ?_, ?_, ?_⟩
  · have : IsClosedImmersion (IsClosedImmersion.lift _ _ hle ≫ Limits.pullback.lift p₁ p₂ h) := by
      rw [hδ]; infer_instance
    exact IsClosedImmersion.of_comp _ (Limits.pullback.lift p₁ p₂ h)
  · have e₁ := hδ =≫ Limits.pullback.fst Y.str Y.str
    rwa [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.diagonal_fst] at e₁
  · have e₂ := hδ =≫ Limits.pullback.snd Y.str Y.str
    rwa [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.diagonal_snd] at e₂
  · intro K _ w hw
    have e : w = (w ≫ p₁) ≫ IsClosedImmersion.lift _ _ hle := by
      rw [← cancel_mono (Limits.pullback.lift p₁ p₂ h), Category.assoc, hδ]
      apply Limits.pullback.hom_ext
      · simp only [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.diagonal_fst, Category.comp_id]
      · simp only [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.diagonal_snd, Category.comp_id, hw]
    refine ⟨(w ≫ p₁) (IsLocalRing.closedPoint K), ?_⟩
    have e' := congrArg (fun f : Sp K ⟶ Z => f (IsLocalRing.closedPoint K)) e
    exact e'.symm

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigensystemGoodFormsThetaTargetOccursOnRows
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.OccW

theorem level_eq_trivial_of_subgroup_eq_bot {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {LL : Type} [CommRing LL]
    (L : LevelP Pg r LL) (h : L.H = ⊥) : L = LevelP.triv Pg r LL := by
  obtain ⟨H, chi⟩ := L
  simp only at h
  subst h
  unfold LevelP.triv
  congr 1
  ext x
  have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.mp x.2)
  subst hx
  simp

theorem levPOf_bot {D : D7} {G K : Type} [Group G] [Field K] {Pg : Finset (Pl D.host.E)} {r : ℕ} (eG : G ≃* G0 Pg r)
    (σ : K →+* ℂ) (ψ : (⊥ : Subgroup G) →* Kˣ) : levPOf eG σ ⊥ ψ = LevelP.triv Pg r ℂ := by
  apply level_eq_trivial_of_subgroup_eq_bot
  show Subgroup.comap eG.symm.toMonoidHom ⊥ = ⊥
  ext x
  simp

end GlobalTheory.OccW


open GlobalTheory.OccW in
theorem GlobalTheory.Hk3.eec_ne_bot_of_wcc_ne_bot : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → SchurAll R → GoodStable A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R → ∀ SF, IsSF R SF → ∀ i c, Wcc R SF i c ≠ ⊥ → EEc R SF c ≠ ⊥ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hOk hCore hSchur hGood hCusp hMult SF hSF i c hW
  have hdim := _root_.GlobalTheory.DimFull.dim_parts_full R F hOk hCore hSchur hGood hCusp hMult SF hSF ⊥ 1 i c
  rw [inv_one, levPOf_bot] at hdim
  have hWle : Wcc R SF i c ≤ (R.Wat i (sg0 D A) R.triv).comap (R.HW i _).e :=
    Submodule.comap_mono inf_le_left
  rw [inf_eq_left.mpr hWle] at hdim
  intro hE
  rw [hE, bot_inf_eq, finrank_bot] at hdim
  exact hW (Submodule.finrank_eq_zero.mp hdim)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticPolynomialsBoundedFinite
section
open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

namespace GlobalTheory.BCT.GeoFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem norm_coeff_le {n : ℕ} {P : E[X]} (hP : P ∈ Ell E n) (τ : E →+* ℂ) (i : ℕ) :
    ‖τ (P.coeff i)‖ ≤ n.choose i := by
  obtain ⟨hm, hd, -, hr⟩ := hP
  have h := Polynomial.coeff_le_of_roots_le (f := τ) (B := 1) i hm (IsAlgClosed.splits _)
    (fun z hz => (hr τ z hz).le)
  rw [one_pow, one_mul, hd, Polynomial.coeff_map] at h
  exact h

theorem valued_algebraMap (w : Pl E) (k : E) :
    Valued.v (algebraMap E (w.adicCompletion E) k) = w.valuation E k :=
  Formalism.UG.P.levelaf_valued_algebraMap w k

theorem valuation_conjE (w : Pl E) (k : E) :
    w.valuation E (GlobalTheory.SplitPts.conjE E k) = (conjSrc (GlobalTheory.SplitPts.conjE E) w).valuation E k := by
  have h := (conjLoc_spec (GlobalTheory.SplitPts.conjE E) w).2.2 (algebraMap E _ k)
  rw [(conjLoc_spec (GlobalTheory.SplitPts.conjE E) w).2.1, valued_algebraMap, valued_algebraMap] at h
  exact h

theorem valuation_coeff_le {n : ℕ} {S : Set (Pl E)} (hS : IsSection S) {γ : Pl E → WithZero (Multiplicative ℤ)} (hγ0 : ∀ w, γ w ≠ 0)
    {P : E[X]} (hP : P ∈ Ell E n) (hPS : ∀ w ∈ S, (∀ i, Valued.v ((atPl w P).coeff i) ≤ γ w) ∧
      (γ w)⁻¹ ≤ Valued.v ((atPl w P).coeff 0)) (w : Pl E) (i : ℕ) :
    w.valuation E (P.coeff i) ≤ if w ∈ S then γ w else γ (conjSrc (GlobalTheory.SplitPts.conjE E) w) ^ 2 := by
  have hv : ∀ u ∈ S, (∀ j, u.valuation E (P.coeff j) ≤ γ u) ∧ (γ u)⁻¹ ≤ u.valuation E (P.coeff 0) := by
    intro u hu
    obtain ⟨h1, h2⟩ := hPS u hu
    refine ⟨fun j => ?_, ?_⟩
    · have := h1 j
      rwa [atPl, Polynomial.coeff_map, valued_algebraMap] at this
    · rwa [atPl, Polynomial.coeff_map, valued_algebraMap] at h2
  split_ifs with hw
  · exact (hv w hw).1 i
  obtain ⟨hm, hd, -, hr⟩ := hP
  have hrec := _root_.GlobalTheory.monic_coeff_natDegree_sub_eq_mul_complexConj E n P hm hd hr
  obtain ⟨u, ⟨hu, huw⟩, -⟩ := hS w
  rcases GlobLev.eq_or_eq_conjSrc huw with rfl | rfl
  · exact absurd hu hw
  set u := conjSrc (GlobalTheory.SplitPts.conjE E) w
  by_cases hi : i ≤ n
  swap
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Valuation.map_zero]
    exact zero_le'
  have hci : P.coeff i = P.coeff 0 * GlobalTheory.SplitPts.conjE E (P.coeff (n - i)) := by
    have := hrec (n - i) (Nat.sub_le n i)
    rwa [Nat.sub_sub_self hi] at this
  have hc0 : P.coeff 0 * GlobalTheory.SplitPts.conjE E (P.coeff 0) = 1 := by
    have := hrec 0 (Nat.zero_le n)
    rw [Nat.sub_zero, ← hd, ← Polynomial.leadingCoeff, hm.leadingCoeff] at this
    exact this.symm
  have hv0 : w.valuation E (P.coeff 0) * u.valuation E (P.coeff 0) = 1 := by
    rw [← valuation_conjE, ← Valuation.map_mul, hc0, Valuation.map_one]
  have hw0 : w.valuation E (P.coeff 0) ≤ γ u := by
    rw [eq_inv_of_mul_eq_one_left hv0]
    have hu0 : u.valuation E (P.coeff 0) ≠ 0 := right_ne_zero_of_mul_eq_one hv0
    exact (inv_le_comm₀ (zero_lt_iff.2 hu0) (zero_lt_iff.2 (hγ0 u))).2 (hv u hu).2
  rw [hci, Valuation.map_mul, valuation_conjE, sq]
  exact mul_le_mul' hw0 ((hv u hu).1 _)

theorem finite_ell_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S →
    ∀ γ : Pl E → WithZero (Multiplicative ℤ), (∀ w, γ w ≠ 0) → (∀ᶠ w in cofinite, γ w = 1) →
    {P : E[X] | P ∈ Ell E n ∧ ∀ w ∈ S, (∀ i, Valued.v ((atPl w P).coeff i) ≤ γ w) ∧
      (γ w)⁻¹ ≤ Valued.v ((atPl w P).coeff 0)}.Finite := by
  intro E _ _ _ n S hS γ hγ0 hγ1
  set σ := GlobalTheory.SplitPts.conjE E
  set β : Pl E → WithZero (Multiplicative ℤ) := fun w => if w ∈ S then γ w else γ (conjSrc σ w) ^ 2 with hβ
  have hβ1 : ∀ᶠ w in cofinite, β w ≤ 1 := by
    have h2 : ∀ᶠ w in cofinite, γ (conjSrc σ w) = 1 := (conjSrc_injective σ).tendsto_cofinite.eventually hγ1
    filter_upwards [hγ1, h2] with w h1 h2
    simp only [hβ]
    split_ifs
    · exact h1.le
    · rw [h2, one_pow]
  obtain ⟨D, hD0, hD⟩ := GlobalTheory.T.exists_common_denominator_of_valuation_le_cofinite E β hβ1
  have hD0' : (D : E) ≠ 0 := by exact_mod_cast hD0
  set r : ℕ → ℝ := fun i => (∑ τ : E →+* ℂ, ‖τ (D : E)‖) * n.choose i with hr
  set X : Fin (n + 1) → Set E := fun i => {x | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ r i} with hXd
  have hX : ∀ i, (X i).Finite := fun i => Embeddings.finite_of_norm_le E ℂ (r i)
  refine Set.Finite.of_finite_image (f := fun (P : E[X]) (i : Fin (n + 1)) => (D : E) * P.coeff i)
    ((Set.Finite.pi hX).subset ?_) ?_
  · rintro _ ⟨P, ⟨hP, hPS⟩, rfl⟩ i -
    refine ⟨hD _ fun w => valuation_coeff_le hS hγ0 hP hPS w i, fun φ => ?_⟩
    rw [map_mul, norm_mul]
    exact mul_le_mul (Finset.single_le_sum (f := fun τ : E →+* ℂ => ‖τ (D : E)‖) (fun τ _ => norm_nonneg _)
      (Finset.mem_univ φ)) (norm_coeff_le hP φ i) (norm_nonneg _)
      (Finset.sum_nonneg fun τ _ => norm_nonneg _)
  · intro P hP Q hQ hPQ
    ext k
    by_cases hk : k ≤ n
    · exact mul_left_cancel₀ hD0' (congrFun hPQ ⟨k, Nat.lt_succ_of_le hk⟩)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hP.1.2.1]; omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hQ.1.2.1]; omega)]

end GlobalTheory.BCT.GeoFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOrEqOfUnderMaximalRealSubfieldEqCMFieldStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_or_eq_of_under_maximalRealSubfield_eq_CMField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w u u' : Pl E), u ≠ w → u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → u'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → u' = w ∨ u' = u := by
  first | exact @GlobalTheory.BCT.FiberTwo.eq_or_eq_of_under_eq | exact GlobalTheory.BCT.FiberTwo.eq_or_eq_of_under_eq | (intros; apply GlobalTheory.BCT.FiberTwo.eq_or_eq_of_under_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordsBaseChange
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField Set MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX isPushout_sections)
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing GlobalTheory.TopForm GlobalTheory.ChartGlue

namespace GlobalTheory

section BaseChange

variable {k k' : Type} [CommRing k] [CommRing k'] {ρ : k →+* k'} {Y Y' : Scheme.{0}} {p : Y ⟶ Sp k}
  {p' : Y' ⟶ Sp k'} {r : Y' ⟶ Y} {σ : k →+* ℂ} {τ : k' →+* ℂ} {D : ℕ} {m : CxPts p' τ → CxPts p σ}

theorem CxPts.ev_appLE_of_comp (hm : ∀ z, (m z).1 = z.1 ≫ r) {U : Y.Opens} {W : Y'.Opens} (h : W ≤ r ⁻¹ᵁ U)
    (g : Γ(Y, U)) {z : CxPts p' τ} (hz : z ∈ ptsIn p' τ W) :
    ev p' τ W ((r.appLE U W h).hom g) z = ev p σ U g (m z) :=
  (ev_res h hz _).trans (ev_of_comp hm U g z).symm

def CxPts.bcMap (w : r ≫ p = p' ≫ spMap ρ) (τ : k' →+* ℂ) (z : CxPts p' τ) : CxPts p (τ.comp ρ) :=
  ⟨z.1 ≫ r, by
    rw [Category.assoc, w, ← Category.assoc, z.2, spMap, spMap, spMap, ← Spec.map_comp]
    rfl⟩

theorem CxPts.bijective_bcMap (H : IsPullback r p' p (spMap ρ)) (τ : k' →+* ℂ) :
    Function.Bijective (bcMap H.w τ) := by
  refine ⟨fun z z' h => Subtype.ext (H.hom_ext (congrArg Subtype.val h) (z.2.trans z'.2.symm)), fun y => ?_⟩
  have e : y.1 ≫ p = spMap τ ≫ spMap ρ := by
    rw [y.2, spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  exact ⟨⟨H.lift y.1 (spMap τ) e, H.lift_snd _ _ _⟩, Subtype.ext (H.lift_fst _ _ _)⟩

theorem etale_coords_baseChange (H : IsPullback r p' p (spMap ρ)) {U : Y.Opens} (hU : IsAffineOpen U)
    {x : Fin D → Γ(Y, U)} (hx : (MvPolynomial.eval₂Hom (algX p U) x).Etale) :
    (MvPolynomial.eval₂Hom (algX p' (r ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤))
      fun a => (r.appLE U _ inf_le_left).hom (x a)).Etale := by
  letI := ρ.toAlgebra
  letI := MvPolynomial.algebraMvPolynomial (R := k) (S := k') (σ := Fin D)
  have h₁ := (CommRingCat.isPushout_of_isPushout k k' (MvPolynomial (Fin D) k) (MvPolynomial (Fin D) k')).flip
  have h₂ := isPushout_sections p p' r H U hU
  have e₁ : CommRingCat.ofHom (algX p U) = CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin D) k)) ≫
      CommRingCat.ofHom (MvPolynomial.eval₂Hom (algX p U) x) := by
    ext a
    exact (MvPolynomial.eval₂Hom_C _ _ a).symm
  have e₂ : CommRingCat.ofHom (algX p' (r ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤)) =
      CommRingCat.ofHom (algebraMap k' (MvPolynomial (Fin D) k')) ≫
      CommRingCat.ofHom (MvPolynomial.eval₂Hom (algX p' (r ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤))
        fun a => (r.appLE U _ inf_le_left).hom (x a)) := by
    ext a
    exact (MvPolynomial.eval₂Hom_C _ _ a).symm
  rw [e₁, e₂] at h₂
  have h₃ := h₂.of_left (CommRingCat.hom_ext (MvPolynomial.ringHom_ext (fun a => ?_) fun a => ?_)) h₁
  · have := RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange
    exact MorphismProperty.of_isPushout (P := RingHom.toMorphismProperty RingHom.Etale) h₃.flip hx
  · change (r.appLE U _ _).hom (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a)) =
      MvPolynomial.eval₂Hom _ _ (MvPolynomial.map ρ (MvPolynomial.C a))
    rw [MvPolynomial.map_C, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
    exact RingHom.congr_fun (appLE_comp_algX H.w (inf_le_left : r ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤ ≤ _)) a
  · change (r.appLE U _ _).hom (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X a)) =
      MvPolynomial.eval₂Hom _ _ (MvPolynomial.map ρ (MvPolynomial.X a))
    rw [MvPolynomial.map_X, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']

theorem AlgChart.exists_baseChange (H : IsPullback r p' p (spMap ρ)) (hm : ∀ z, (m z).1 = z.1 ≫ r)
    (c : AlgChart p σ D) {z : CxPts p' τ} (hz : m z ∈ c.e.source) :
    ∃ c' : AlgChart p' τ D, z ∈ c'.e.source ∧ ∃ h : c'.U ≤ r ⁻¹ᵁ c.U,
      ∀ a, c'.x a = (r.appLE c.U c'.U h).hom (c.x a) := by
  have hU : IsAffineOpen (r ⁻¹ᵁ c.U ⊓ p' ⁻¹ᵁ ⊤) := by
    rw [show r ⁻¹ᵁ c.U ⊓ p' ⁻¹ᵁ ⊤ = r ⁻¹ᵁ c.U from inf_top_eq _]
    exact isAffineOpen_preimage_of_isPullback H c.affine
  obtain ⟨⟨e, U, hU', x, hx, h₁, h₂, h₃⟩, hy, hU', hx'⟩ := AlgChart.exists_of_etale hU _
    (etale_coords_baseChange H c.affine c.etale)
    (mem_ptsIn_inf.2 ⟨(mem_ptsIn_preimage hm).2 (c.source_subset hz), mem_ptsIn_top⟩ : z ∈ ptsIn p' τ _)
  dsimp only at hU'
  subst hU'
  dsimp only at hx'
  subst hx'
  exact ⟨_, hy, inf_le_left, fun _ => rfl⟩

variable [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p']

variable {B : LB Y} {B' : LB Y'}


omit [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p'] in
theorem Vanishing.cval_pullChart (hm : ∀ z, (m z).1 = z.1 ≫ r) (b : ChartPull B' B r) (w : r ≫ p = p' ≫ spMap ρ)
    (f : H0 p B ⊤) {i : B'.ι} {z : CxPts p' τ} (hz : z ∈ ptsIn p' τ (B'.U i)) :
    cval τ (pullChart (W := ⊤) b w le_top f) i z = cval σ f (b.idx i) (m z) :=
  ev_appLE_of_comp hm (inf_le_inf le_top (b.le i)) _ (mem_ptsIn_inf.2 ⟨mem_ptsIn_top, hz⟩)

end BaseChange

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]

namespace HilbertSamuel

end HilbertSamuel

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyFiniteAdelicUnitaryComponentMemIntegraStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_finiteAdelicUnitaryComponent_mem_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ x : finU (E := E) (n := n), ∀ᶠ w in cofinite, toSub (UL n w) (cLoc w (x : UA E n)) ∈ KL n w := by
  first | exact @GlobalTheory.BCT.LocAE.eventually_mem_KL | exact GlobalTheory.BCT.LocAE.eventually_mem_KL | (intros; apply GlobalTheory.BCT.LocAE.eventually_mem_KL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryPointCutToFibreUnionStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelicUnitaryPoint_cut_to_fibreUnion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : Set (Pl E)),
    (∀ u v : Pl E, u.under (𝓞 (maximalRealSubfield E)) = v.under (𝓞 (maximalRealSubfield E)) → u ∈ P → v ∈ P) →
    ∀ g ∈ finU (E := E) (n := n), ∃ x ∈ finU (E := E) (n := n), ∀ v : Pl E, cLoc v x = if v ∈ P then cLoc v g else 1 := by
  first | exact @GlobalTheory.FibreCut.exists_cut | exact GlobalTheory.FibreCut.exists_cut | (intros; apply GlobalTheory.FibreCut.exists_cut <;> assumption)
end

