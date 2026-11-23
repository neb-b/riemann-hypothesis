module

public import Mathlib
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
public import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0351
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0315
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0352
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOfEtalePunctured
section
open IsLocalRing

namespace GlobalTheory.PurityStep

theorem finite_quot (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A] (f : R) : Module.Finite (R ⧸ Ideal.span {f}) (A ⧸ (Ideal.span {f}).map (algebraMap R A)) :=
  Module.Finite.of_restrictScalars_finite R _ _

theorem lowDim (R : Type) [CommRing R] [IsRegularLocalRing R] (h : ringKrullDim R ≤ 2) :
    PurityFree R := by
  intro A _ _ _ hA _
  refine GlobalTheory.AnnRegSeq.free_of_modDepthGE 2 R A hA ?_
  have h1 : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  have : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ ((2 : ℕ) : WithBot ℕ∞) := by
    rw [h1]; exact_mod_cast h
  exact_mod_cast this

theorem hyperplane (R : Type) [CommRing R] [IsRegularLocalRing R]
    (hc : IsAdicComplete (maximalIdeal R) R) (hd : 3 ≤ ringKrullDim R) (f : R)
    (hf : f ∈ maximalIdeal R) (hf2 : f ∉ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ Ideal.span {f})]
    (hP : PurityFree (R ⧸ Ideal.span {f})) : PurityFree R := by
  intro A _ _ _ hA het
  have h3 := _root_.GlobalTheory.LocalLefschetz.depth_three R hc hd f hf hf2 hP A hA het
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf2 (zero_mem _)
  have hreg := _root_.GlobalTheory.isSMulRegular_of_etale_punctured_of_depth_pos R A (ReciprocityTheory.CA.ModDepthGE.mono (by norm_num) hA) het f hf0
  haveI := finite_quot R A f
  exact GlobalTheory.T.moduleFree_of_regular_of_free_quotient_local R A f hf hreg (hP _ (_root_.GlobalTheory.modDepthGE_quotient_map_span_singleton R A f hf hreg 2 h3) (_root_.GlobalTheory.etale_quotient_of_etale_punctured R A f het))

theorem purityFree_of_ringKrullDim (n : ℕ) : ∀ (S : Type) [CommRing S] [IsRegularLocalRing S],
    ringKrullDim S = n → PurityFree S := by
  induction n with
  | zero =>
    intro S _ _ hS
    exact lowDim S (by rw [hS]; norm_num)
  | succ n ih =>
    intro S _ _ hS
    by_cases h2 : n + 1 ≤ 2
    · exact lowDim S (by rw [hS]; exact_mod_cast h2)
    refine _root_.GlobalTheory.PurityStep.purityFree_of_complete S fun S' _ _ hc hd' => ?_
    rw [hS] at hd'
    have hsq : ¬ maximalIdeal S' ≤ maximalIdeal S' ^ 2 := by
      intro h
      have h0 := GlobalTheory.AnnRegSeq.maximalIdeal_eq_bot_of_le_sq h
      have := ringKrullDim_eq_zero_of_isField ((IsLocalRing.isField_iff_maximalIdeal_eq (R := S')).mpr h0)
      rw [this] at hd'
      exact absurd hd' (by norm_cast)
    obtain ⟨f, hf, hf2⟩ := Set.not_subset.mp hsq
    haveI := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isLocalRing_quotient_span_singleton hf
    haveI hQ := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.quotient_span_singleton hf hf2
    have hdim := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one hf hf2
    have hsp : ((maximalIdeal (S' ⧸ Ideal.span {f})).spanFinrank : WithBot ℕ∞) =
        ringKrullDim (S' ⧸ Ideal.span {f}) := IsRegularLocalRing.spanFinrank_maximalIdeal
    rw [← hsp, hd'] at hdim
    have hk : (maximalIdeal (S' ⧸ Ideal.span {f})).spanFinrank = n := by
      have : (maximalIdeal (S' ⧸ Ideal.span {f})).spanFinrank + 1 = n + 1 := by
        exact_mod_cast hdim
      omega
    refine hyperplane S' hc ?_ f hf hf2 (ih _ ?_)
    · rw [hd']; exact_mod_cast (by omega : 3 ≤ n + 1)
    · rw [← hsp, hk]

theorem free_of_etale_punctured : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], (((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) → 3 ≤ ringKrullDim R → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → Module.Free R A := by
  intro R A _ _ _ _ _ _ _ _ _ _ hreg hd het
  haveI : IsRegularLocalRing R := (isRegularLocalRing_iff R).mpr hreg
  refine purityFree_of_ringKrullDim _ R hreg.symm A (_root_.GlobalTheory.modDepthGE_two_of_isIntegrallyClosed_of_isRegularLocalRing R A (le_trans (by norm_num) hd)) het

end GlobalTheory.PurityStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeSheafHomValueAtCechNerveSimplexBijectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeSheafHomValueAt_cechNerveSimplex_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (Y X : Scheme.{0}) (f : Y ⟶ X) (k : ℕ) (Z : Scheme.{0}) (x : Z ⟶ X) (y : Fin (k + 1) → (Z ⟶ Y)) (h : ∀ i, y i ≫ f = x), IsLimit (WidePullbackCone.mk (f := fun _ : Fin (k + 1) => f) x y h) → Function.Bijective (fun s : (free R).obj ((cech f).obj (op (SimplexCategory.mk k))) ⟶ F => GlobalTheory.EtC.val s Z (cechPt f k x y h)) := by
  intro R _ F Y X f k Z x y h hc
  have e : ∀ U : Scheme.{0}, Function.Bijective
      (fun g : U ⟶ Z => ((cech f).obj (op (SimplexCategory.mk k))).map g.op (cechPt f k x y h)) := by
    intro U
    have hb := CechPts.bij f k x y h hc U
    refine ⟨fun g g' hg => hb.1 ((CechPts.map_cechPt f k x y h g).symm.trans (hg.trans (CechPts.map_cechPt f k x y h g'))), fun v => ?_⟩
    obtain ⟨g, hg⟩ := hb.2 v
    exact ⟨g, (CechPts.map_cechPt f k x y h g).trans hg⟩
  let P := (cech f).obj (op (SimplexCategory.mk k))
  have evaluate (s : (free R).obj P ⟶ F) (U : Scheme.{0}) (v : P.obj (op U)) :
      val s U v =
        ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ s.hom).app (op U)).hom
          (ModuleCat.freeMk (ULift.up v)) := rfl
  have hext (s s' : (free R).obj P ⟶ F) (hs : ∀ U v, val s U v = val s' U v) : s = s' := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _ F.property
    apply NatTrans.ext
    funext U
    apply ModuleCat.free_hom_ext
    rintro ⟨v⟩
    have hv := hs U.unop v
    rw [evaluate, evaluate] at hv
    exact hv
  have hex (φ : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
      (hφ : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (v : P.obj (op U)),
        φ V (P.map g.op v) = Sec.res g (φ U v)) :
      ∃ s : (free R).obj P ⟶ F, ∀ U v, val s U v = φ U v := by
    let s := GlobalTheory.EtC.FreeHom.desc P F φ hφ
    refine ⟨s, ?_⟩
    intro U v
    rw [evaluate]
    have hdesc : toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ s.hom =
        GlobalTheory.EtC.FreeHom.descP P F φ hφ := by
      have h := ((sheafificationAdjunction Scheme.etaleTopology.{0}
        (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).apply_symm_apply
          (GlobalTheory.EtC.FreeHom.descP P F φ hφ)
      rw [Adjunction.homEquiv_unit] at h
      exact h
    rw [hdesc]
    change (ModuleCat.freeDesc _).hom (ModuleCat.freeMk (ULift.up v)) = _
    erw [ModuleCat.freeDesc_apply]
    rfl
  have hnat (s : (free R).obj P ⟶ F) (V U : Scheme.{0}) (g : V ⟶ U) (v : P.obj (op U)) :
      val s V (P.map g.op v) = Sec.res g (val s U v) := by
    rw [evaluate, evaluate]
    let η := toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ s.hom
    change (η.app (op V)).hom (ModuleCat.freeMk (ULift.up (P.map g.op v))) =
      (F.obj.map g.op).hom ((η.app (op U)).hom (ModuleCat.freeMk (ULift.up v)))
    rw [← GlobalTheory.EtC.FreeHom.freePresheaf_map_freeMk P g.op v]
    exact congrArg (fun m => m.hom (ModuleCat.freeMk (ULift.up v))) (η.naturality g.op)
  constructor
  · intro s s' hs
    change val s Z (cechPt f k x y h) = val s' Z (cechPt f k x y h) at hs
    apply hext
    intro U v
    obtain ⟨g, rfl⟩ := (e U).2 v
    dsimp only
    rw [hnat s U Z g, hnat s' U Z g, hs]
  · intro a
    choose c hc0 using fun (U : Scheme.{0}) (v : ((cech f).obj (op (SimplexCategory.mk k))).obj (op U)) => (e U).2 v
    have hc' : ∀ (U : Scheme.{0}) (v : ((cech f).obj (op (SimplexCategory.mk k))).obj (op U)),
        ((cech f).obj (op (SimplexCategory.mk k))).map (c U v).op (cechPt f k x y h) = v := hc0
    obtain ⟨s, hs⟩ := hex (fun U v => Sec.res (c U v) a) (by
      intro V U g v
      have h1 : c V (((cech f).obj (op (SimplexCategory.mk k))).map g.op v) = g ≫ c U v := by
        apply (e V).1
        change ((cech f).obj (op (SimplexCategory.mk k))).map (c V _).op (cechPt f k x y h) =
          ((cech f).obj (op (SimplexCategory.mk k))).map (g ≫ c U v).op (cechPt f k x y h)
        rw [hc' V, op_comp, Functor.map_comp_apply, hc' U v]
      dsimp only
      rw [h1]
      simp [Sec.res])
    refine ⟨s, ?_⟩
    change val s Z (cechPt f k x y h) = a
    rw [hs]
    have h2 : c Z (cechPt f k x y h) = 𝟙 Z := by
      apply (e Z).1
      change ((cech f).obj (op (SimplexCategory.mk k))).map (c Z _).op (cechPt f k x y h) =
        ((cech f).obj (op (SimplexCategory.mk k))).map (𝟙 Z).op (cechPt f k x y h)
      rw [hc' Z, op_id, P.map_id]
      exact (types_id_apply (P.obj (op Z)) (cechPt f k x y h)).symm
    rw [h2]
    simp [Sec.res]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusShapeOfSidePreserving
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

open Polynomial SemidirectProduct in
open scoped Classical in
private lemma isCl_apply_eq_of_isConj {G : Type} [Group G] {f : G → ℂ}
    (hf : _root_.GlobalTheory.Shin.IsCl f) {a b : G} (h : IsConj a b) : f a = f b := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  have := hf a c⁻¹
  rw [inv_inv] at this
  exact this.symm


open Polynomial SemidirectProduct in
open scoped Classical in
theorem _root_.GlobalTheory.Shin.shLift_isNorm_and_twisted_inv : ∀ (F F' : Type) [Field F] [Field F']
    [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) →
    ∀ (n : ℕ) (f : GL (Fin n) F → ℂ), _root_.GlobalTheory.Shin.IsCl f →
    (∀ δ γ, _root_.GlobalTheory.Shin.IsNorm s δ γ → _root_.GlobalTheory.Shin.shLift s f δ = f γ) ∧
    ∀ δ y : GL (Fin n) F', _root_.GlobalTheory.Shin.shLift s f
      (y⁻¹ * δ * _root_.GlobalTheory.Shin.galAct F F' n s y) = _root_.GlobalTheory.Shin.shLift s f δ := by
  intro F F' _ _ _ _ s hs n f hf
  have hconj := (_root_.GlobalTheory.Shin.NrmBasic.main F F' s hs n).2.2.1
  refine ⟨fun δ γ hδ => ?_, fun δ y => ?_⟩
  · unfold _root_.GlobalTheory.Shin.IsNorm at hδ
    unfold _root_.GlobalTheory.Shin.shLift
    have hex : ∃ γ, _root_.GlobalTheory.Shin.IsNorm s δ γ := ⟨γ, hδ⟩
    rw [dite_eq_left hex]
    have hspec : IsConj (_root_.GlobalTheory.Shin.incl F F' n hex.choose) (_root_.GlobalTheory.Shin.nrm s δ) :=
      hex.choose_spec
    exact isCl_apply_eq_of_isConj hf
      (_root_.GlobalTheory.Shin.isConj_of_isConj_incl F F' n _ _ (hspec.trans hδ.symm))
  · have hN : IsConj (_root_.GlobalTheory.Shin.nrm s δ)
        (_root_.GlobalTheory.Shin.nrm s (y⁻¹ * δ * _root_.GlobalTheory.Shin.galAct F F' n s y)) := by
      rw [hconj δ y, isConj_iff]
      exact ⟨y⁻¹, by rw [inv_inv]⟩
    unfold _root_.GlobalTheory.Shin.shLift
    by_cases hex : ∃ γ, _root_.GlobalTheory.Shin.IsNorm s δ γ
    · have hspec : IsConj (_root_.GlobalTheory.Shin.incl F F' n hex.choose) (_root_.GlobalTheory.Shin.nrm s δ) :=
        hex.choose_spec
      have hex' : ∃ γ, _root_.GlobalTheory.Shin.IsNorm s (y⁻¹ * δ * _root_.GlobalTheory.Shin.galAct F F' n s y) γ :=
        ⟨hex.choose, hspec.trans hN⟩
      have hspec' : IsConj (_root_.GlobalTheory.Shin.incl F F' n hex'.choose)
          (_root_.GlobalTheory.Shin.nrm s (y⁻¹ * δ * _root_.GlobalTheory.Shin.galAct F F' n s y)) :=
        hex'.choose_spec
      rw [dite_eq_left hex, dite_eq_left hex']
      exact isCl_apply_eq_of_isConj hf
        (_root_.GlobalTheory.Shin.isConj_of_isConj_incl F F' n _ _
          (hspec'.trans (hspec.trans hN).symm))
    · have hex' : ¬ ∃ γ, _root_.GlobalTheory.Shin.IsNorm s (y⁻¹ * δ * _root_.GlobalTheory.Shin.galAct F F' n s y) γ :=
        fun ⟨γ, hγ⟩ => hex ⟨γ, (show IsConj (_root_.GlobalTheory.Shin.incl F F' n γ) _ from hγ).trans hN.symm⟩
      rw [dite_eq_right hex, dite_eq_right hex']

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceLocalIndexColength
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

namespace GlobalTheory.Nef.LocalIndex

open GlobalTheory.Nef.OrdCalc

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem const_le_one (v : Place k F) (c : k) : v.1 (algebraMap k F c) ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  · exact (v.2.2 c hc).le

theorem div_unif (v : Place k F) {π : F} (hπ : π ≠ 0) (h1 : ord v π = 1) {y : F}
    (hy : v.1 y < 1) : v.1 (π⁻¹ * y) ≤ 1 := by
  by_cases h0 : y = 0
  · simp [h0]
  have h2 := (le_one_iff v y h0).1 hy.le
  have h3 : ord v y ≠ 0 := fun h => hy.ne ((eq_one_iff v y h0).2 h)
  have h4 : ord v π⁻¹ = -1 := by
    have := ord_zpow v π (-1)
    rw [zpow_neg_one, h1] at this; simpa using this
  rw [le_one_iff v _ (mul_ne_zero (inv_ne_zero hπ) h0), ord_mul v _ _ (inv_ne_zero hπ) h0, h4]
  omega

theorem exists_residue (v : Place k F)
    (hres : ∀ x : F, v.1 x ≤ 1 → ∃ c : k, v.1 (x - algebraMap k F c) < 1) :
    ∃ f : F →ₗ[k] k, ∀ y, v.1 y ≤ 1 → f y = 0 → v.1 y < 1 := by
  let m : Submodule k F :=
    { carrier := {y | v.1 y < 1}
      add_mem' := fun {a b} ha hb => v.1.map_add_lt ha hb
      zero_mem' := by simp
      smul_mem' := fun c y hy => by
        show v.1 (c • y) < 1
        rw [Algebra.smul_def, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (const_le_one v c)) hy }
  have h1 : (1 : F) ∉ m := by
    show ¬ v.1 1 < 1
    simp
  obtain ⟨f, hf, hk⟩ := Submodule.exists_le_ker_of_notMem h1
  refine ⟨f, fun y hy h0 => ?_⟩
  obtain ⟨c, hc⟩ := hres y hy
  have h2 : f (y - algebraMap k F c) = 0 := hk hc
  rw [map_sub, h0, Algebra.algebraMap_eq_smul_one, map_smul, zero_sub, neg_eq_zero, smul_eq_mul,
    mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · simpa [h2] using hc
  · exact absurd h2 hf

theorem mulVec_int (v : Place k F) {n : ℕ} (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F)
    (hu : ∀ i j, v.1 (u i j) ≤ 1) (hx : ∀ i, v.1 (x i) ≤ 1) (i : Fin n) :
    v.1 (u.mulVec x i) ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  apply Valuation.map_sum_le
  intro j _
  rw [map_mul]
  exact mul_le_one' (hu i j) (hx j)

theorem exists_primitive (v : Place k F) {n : ℕ} (a : Matrix (Fin n) (Fin n) F) (hd : a.det ≠ 0)
    (hlt : v.1 a.det < 1) :
    ∃ (c : Fin n → F) (i : Fin n), c i = 1 ∧ (∀ l, v.1 (c l) ≤ 1) ∧ ∀ l, v.1 (a.mulVec c l) < 1 := by
  have hn : ¬ ∀ i j, v.1 (a⁻¹ i j) ≤ 1 := by
    intro h
    have h1 := (det_adj_int v n _ h).1
    have h2 : v.1 (a.det * a⁻¹.det) < 1 := by
      rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right' h1) hlt
    rw [← Matrix.det_mul, Matrix.mul_nonsing_inv a (isUnit_iff_ne_zero.2 hd)] at h2
    simp at h2
  push Not at hn
  obtain ⟨i0, j, hj⟩ := hn
  have hb : (fun l => a⁻¹ l j) ≠ 0 := by
    intro h
    have := congrFun h i0
    simp only [Pi.zero_apply] at this
    rw [this] at hj
    simp at hj
  obtain ⟨i, hi, -, -, hmax⟩ := nrm_max v n _ hb
  have hvi : 1 < v.1 (a⁻¹ i j) := lt_of_lt_of_le hj (hmax i0)
  have hpos : 0 < v.1 (a⁻¹ i j) := lt_trans zero_lt_one hvi
  refine ⟨(a⁻¹ i j)⁻¹ • fun l => a⁻¹ l j, i, ?_, fun l => ?_, fun l => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]; exact inv_mul_cancel₀ hi
  · simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    rw [inv_mul_le_iff₀ hpos, mul_one]; exact hmax l
  · rw [Matrix.mulVec_smul]
    have e : a.mulVec (fun l => a⁻¹ l j) l = (1 : Matrix (Fin n) (Fin n) F) l j := by
      rw [← Matrix.mul_nonsing_inv a (isUnit_iff_ne_zero.2 hd)]; rfl
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀, e]
    rw [inv_mul_lt_iff₀ hpos, mul_one]
    refine lt_of_le_of_lt ?_ hvi
    by_cases h : l = j <;> simp [Matrix.one_apply, h]

theorem exists_functional_inv_mulVec_integral_of_order (v : Place k F)
    (hres : ∀ x : F, v.1 x ≤ 1 → ∃ c : k, v.1 (x - algebraMap k F c) < 1) (n N : ℕ) :
    ∀ a : Matrix (Fin n) (Fin n) F, a.det ≠ 0 → (∀ i j, v.1 (a i j) ≤ 1) → ord v a.det = N →
      ∃ φ : (Fin n → F) →ₗ[k] (Fin N → k), ∀ x : Fin n → F, (∀ i, v.1 (x i) ≤ 1) → φ x = 0 →
        ∀ i, v.1 (a⁻¹.mulVec x i) ≤ 1 := by
  induction N with
  | zero =>
    intro a hd ha hN
    have hu : Unimod v a := ⟨ha, (eq_one_iff v _ hd).2 (by simpa using hN)⟩
    exact ⟨0, fun x hx _ i => mulVec_int v _ x (unimod_mul_inv v n a a hu hu).2.1 hx i⟩
  | succ N ih =>
    intro a hd ha hN
    obtain ⟨π, hπ, hπ1⟩ := exists_unif v
    obtain ⟨f, hf⟩ := exists_residue v hres
    have hlt : v.1 a.det < 1 := lt_of_le_of_ne (det_adj_int v n a ha).1 (fun h => by
      have := (eq_one_iff v _ hd).1 h
      omega)
    obtain ⟨c, i, hci, hc, hac⟩ := exists_primitive v a hd hlt
    set T : Matrix (Fin n) (Fin n) F := (1 : Matrix (Fin n) (Fin n) F).updateCol i (π⁻¹ • c) with hT
    have hTd : T.det = π⁻¹ := by
      rw [hT, ← Matrix.cramer_apply, Matrix.cramer_one]; simp [hci]
    have h4 : ord v π⁻¹ = -1 := by
      have := ord_zpow v π (-1)
      rw [zpow_neg_one, hπ1] at this; simpa using this
    have hd' : (a * T).det ≠ 0 := by
      rw [Matrix.det_mul, hTd]; exact mul_ne_zero hd (inv_ne_zero hπ)
    have ha' : ∀ l j, v.1 ((a * T) l j) ≤ 1 := by
      intro l j
      by_cases h : j = i
      · have e : (a * T) l j = π⁻¹ * a.mulVec c l := by
          subst h
          simp only [hT, Matrix.mul_apply, Matrix.updateCol_self, Matrix.mulVec, dotProduct,
            Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
          exact Finset.sum_congr rfl fun _ _ => by ring
        rw [e]; exact div_unif v hπ hπ1 (hac l)
      · have e : (a * T) l j = a l j := by
          conv_rhs => rw [← Matrix.mul_one a]
          simp only [hT, Matrix.mul_apply, Matrix.updateCol_ne h]
        rw [e]; exact ha l j
    have hN' : ord v (a * T).det = N := by
      rw [Matrix.det_mul, hTd, ord_mul v _ _ hd (inv_ne_zero hπ), hN, h4]; push_cast; ring
    obtain ⟨φ, hφ⟩ := ih (a * T) hd' ha' hN'
    let ψ : (Fin n → F) →ₗ[k] k :=
      f ∘ₗ (LinearMap.proj i) ∘ₗ ((Matrix.mulVecLin (a * T)⁻¹).restrictScalars k)
    refine ⟨LinearMap.pi fun j => Fin.cases ψ (fun j => (LinearMap.proj j) ∘ₗ φ) j,
      fun x hx h0 l => ?_⟩
    have h1 : φ x = 0 := funext fun j => by simpa using congrFun h0 j.succ
    have h2 : f ((a * T)⁻¹.mulVec x i) = 0 := by simpa [ψ] using congrFun h0 0
    have hy := hφ x hx h1
    have hyi := div_unif v hπ hπ1 (hf _ (hy i) h2)
    have e : a⁻¹ = T * (a * T)⁻¹ := by
      rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv T (isUnit_iff_ne_zero.2 (hTd ▸ inv_ne_zero hπ)), Matrix.one_mul]
    rw [e, ← Matrix.mulVec_mulVec]
    generalize (a * T)⁻¹.mulVec x = y at hy hyi
    simp only [Matrix.mulVec, dotProduct]
    apply Valuation.map_sum_le
    intro j _
    by_cases h : j = i
    · subst h
      have e2 : T l j * y j = c l * (π⁻¹ * y j) := by
        simp only [hT, Matrix.updateCol_self, Pi.smul_apply, smul_eq_mul]; ring
      rw [e2, map_mul]
      exact mul_le_one' (hc l) hyi
    · rw [map_mul]
      refine mul_le_one' ?_ (hy j)
      simp only [hT, Matrix.updateCol_ne h]
      by_cases h' : l = j <;> simp [Matrix.one_apply, h']

end GlobalTheory.Nef.LocalIndex


open GlobalTheory.Nef.OrdCalc GlobalTheory.Nef.LocalIndex in
theorem GlobalTheory.Nef.local_index : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (v : Place k F) (n : ℕ) (h : Matrix (Fin n) (Fin n) F), h.det ≠ 0 → (∀ i j, v.1 (h⁻¹ i j) ≤ 1) → ∃ (N : ℕ) (φ : (Fin n → F) →ₗ[k] (Fin N → k)), (N : ℤ) = -ord v h.det ∧ ∀ x : Fin n → F, (∀ i, v.1 (x i) ≤ 1) → φ x = 0 → ∀ i, v.1 (h.mulVec x i) ≤ 1 := by
  intro k F _ _ _ _ _ hF v n h hd hi
  have e : h⁻¹.det = h.det⁻¹ := by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hd' : h⁻¹.det ≠ 0 := e ▸ inv_ne_zero hd
  have h0 := (le_one_iff v _ hd').1 (det_adj_int v n _ hi).1
  have h1 : ord v h⁻¹.det = -ord v h.det := by
    have := ord_zpow v h.det (-1)
    rw [zpow_neg_one] at this; rw [e, this]; ring
  obtain ⟨N, hN⟩ := Int.eq_ofNat_of_zero_le h0
  obtain ⟨φ, hφ⟩ := exists_functional_inv_mulVec_integral_of_order v (_root_.GlobalTheory.Nef.place_isDVR_residue k F hF v).2 n N h⁻¹ hd' hi hN
  rw [Matrix.nonsing_inv_nonsing_inv h (isUnit_iff_ne_zero.2 hd)] at hφ
  exact ⟨N, φ, by rw [← hN, h1], hφ⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinNonconstantFourierSumSmoothHolomorphic
section
noncomputable section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo

theorem bOne_isGood : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F),
    GlobalTheory.HeckeTwo.IsGood (GlobalTheory.HeckeTwo.bOne 𝔞 𝔟) := by
  intro F _ _ _ 𝔞 𝔟
  refine _root_.GlobalTheory.HeckeTwo.isGood_of_tsum F _ (fun p σ z => fTerm σ z (p : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) ×
      NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F)).1.out.1 p.2.1) _
    (fun p σ hσ => _root_.GlobalTheory.HeckeTwo.fTerm_contDiffOn F _ _ p.1.out.2.2 σ hσ) (fun p w z hz => _root_.GlobalTheory.HeckeTwo.fTerm_wirtWord_differentiableOn F _ _ p.1.out.2.2 w z hz)
    (_root_.GlobalTheory.HeckeTwo.fTerm_deriv_summable_bound F 𝔞 𝔟) ?_
  intro σ hσ z hz
  obtain ⟨u, hu, hb⟩ := _root_.GlobalTheory.HeckeTwo.fTerm_deriv_summable_bound F 𝔞 𝔟 {σ} isCompact_singleton (by simpa using hσ) {z} isCompact_singleton
    (by simpa using hz) 0
  have hs : Summable (fun p : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) =>
      fTerm σ z p.1.out.1 p.2.1) := by
    refine Summable.of_norm_bounded hu fun p => ?_
    have := hb p σ rfl z rfl
    rwa [norm_iteratedFDeriv_zero] at this
  unfold bOne
  exact (hs.tsum_prod' fun c => hs.prod_factor c).symm

end GlobalTheory.HeckeTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBijectiveOfQuasiIsoStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hypercohomologyPullback_bijective_of_quasiIso : ∀ (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) [QuasiIso f] (I : Cx R) [I.IsKInjective] (n : ℤ), Function.Bijective (cpull f I n) := by
  first | (exact @GlobalTheory.EtC.cpull_bijective_of_quasiIso) | (exact GlobalTheory.EtC.cpull_bijective_of_quasiIso) | (intros; apply GlobalTheory.EtC.cpull_bijective_of_quasiIso  <;> assumption)
end

