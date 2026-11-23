module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1045
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0009
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1327
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0538
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0735
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1324
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1325
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartSingleton
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArchDimZero

theorem volume_univ_zero : (volume : Measure (ReciprocityTheory.L2DbarEstimates.V 0)) Set.univ = 1 := by
  have h := (stdOrthonormalBasis ℝ (ReciprocityTheory.L2DbarEstimates.V 0)).volume_parallelepiped
  rwa [Set.eq_univ_of_forall (s := parallelepiped _) fun v =>
    (Subsingleton.elim 0 v) ▸ ⟨0, by simp, by simp⟩] at h

variable {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}

theorem exists_chart (hq : IsArithVar q 0) {σ : k →+* ℂ} (y : CxPts q σ) :
    ∃ c : AlgChart q σ 0, y ∈ c.e.source := by
  obtain ⟨U, x, hU, hg, hx⟩ := GenericEtale.exists_etale_coords hq
  have hy : y ∈ ptsIn q σ U := by
    rw [mem_ptsIn, show y.1 (IsLocalRing.closedPoint ℂ) = genericPoint Y from
      TwistTop.under_eq_genericPoint hq y]
    exact hg
  obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hU x hx hy
  exact ⟨c, hc⟩

theorem isProper (hq : IsArithVar q 0) : IsProper q := by
  obtain ⟨N, j, _, hj⟩ := hq.isProjOver
  have := isProper_str k N
  exact hj ▸ inferInstance

theorem chernPart_singleton (hq : IsArithVar q 0) (L : HermLB q) (σ : k →+* ℂ) (ε : ℤˣ)
    (y : CxPts q σ) : (L.φ σ).chernPart 0 ε {y} = ENNReal.ofReal (ε : ℤ) := by
  have := isProper hq
  obtain ⟨c, hc⟩ := exists_chart hq y
  rw [Weight.chernPart_apply (L.cInf σ) ε c (measurableSet_singleton y)
    (Set.singleton_subset_iff.2 hc)]
  have e : c.e '' {y} = Set.univ := Set.eq_univ_of_forall fun v => ⟨y, rfl, Subsingleton.elim _ _⟩
  simp [e, AlgChart.chernDens_zero, volume_univ_zero]

theorem finite_cxPts (hq : IsArithVar q 0) (σ : k →+* ℂ) : Finite (CxPts q σ) := by
  have := HtSelfInter.finite_ringHom hq
  obtain ⟨e⟩ := HtSelfInter.nonempty_equiv hq
  have : Finite (Σ σ : k →+* ℂ, CxPts q σ) := .of_equiv _ e.symm
  exact .of_injective _ (sigma_mk_injective (i := σ))

theorem chernInt_univ (hq : IsArithVar q 0) (L : HermLB q) (σ : k →+* ℂ) (f : CxPts q σ → ℝ) :
    (L.φ σ).chernInt 0 Set.univ f = ∑ᶠ y, f y := by
  have := isProper hq
  have := finite_cxPts hq σ
  let := Fintype.ofFinite (CxPts q σ)
  have h₁ : (L.φ σ).chernPart 0 1 = Measure.count := Measure.ext_iff_singleton.2 fun y => by
    rw [chernPart_singleton hq L σ 1 y, Measure.count_singleton]
    simp
  have h₂ : (L.φ σ).chernPart 0 (-1) = 0 := Measure.ext_iff_singleton.2 fun y => by
    rw [chernPart_singleton hq L σ (-1) y]
    simp
  rw [Weight.chernInt, h₁, h₂, Measure.restrict_univ, Measure.restrict_univ, integral_zero_measure,
    sub_zero, integral_fintype (Integrable.of_finite (μ := Measure.count) (f := f)), finsum_eq_sum_of_fintype]
  simp [Measure.real]

theorem main : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar q 0 → ∀ (M N : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), N.archInt M 0 hr = ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ, logNorm (M.φ σ) r y := by
  intro k _ Y _ q hq M N r hr
  unfold HermLB.archInt
  refine finsum_congr fun σ => ?_
  have hS : offSupp q σ (M.div hr) = Set.univ := Set.eq_univ_of_forall fun y => mem_offSupp.2 fun h =>
    CartierDiv.genericPoint_notMem_supp _ (TwistTop.under_eq_genericPoint hq y ▸ h)
  rw [hS, chernInt_univ hq]

end GlobalTheory.ArchDimZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFormsMulClosed
section
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.CxForm.FormMul

variable {n : ℕ}

theorem repr_mul (a b : Alt n) (S : Finset (Fin (n + n))) :
    (bas n).repr (a * b) S = ∑ p : Finset (Fin (n + n)) × Finset (Fin (n + n)),
      (bas n).repr a p.1 * (bas n).repr b p.2 * (bas n).repr (bas n p.1 * bas n p.2) S := by
  conv_lhs => rw [← (bas n).sum_repr a, ← (bas n).sum_repr b]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun T _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [smul_mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem repr_coefwise (T : (V n → ℂ) → ℂ) (H : V n → Alt n) (S : Finset (Fin (n + n))) :
    (bas n).repr (coefwise T H) S = T (fun x => (bas n).repr (H x) S) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [coefwise, map_sum, Finsupp.single_apply]

theorem coefwise_mul {v : V n} {T : (V n → ℂ) → ℂ}
    (hsum : ∀ f : Finset (Fin (n + n)) × Finset (Fin (n + n)) → V n → ℂ, (∀ p, DifferentiableAt ℝ (f p) v) →
      T (fun x => ∑ p, f p x) = ∑ p, T (f p))
    (hmul : ∀ f g : V n → ℂ, DifferentiableAt ℝ f v → DifferentiableAt ℝ g v →
      T (fun x => f x * g x) = f v * T g + T f * g v)
    (hconst : ∀ c : ℂ, T (fun _ => c) = 0)
    {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    coefwise T (fun x => F x * G x) = coefwise T F * G v + F v * coefwise T G := by
  refine (bas n).ext_elem fun S => ?_
  have e : (fun x => (bas n).repr (F x * G x) S) = fun x => ∑ p : Finset (Fin (n + n)) × Finset (Fin (n + n)),
      (bas n).repr (F x) p.1 * (bas n).repr (G x) p.2 * (bas n).repr (bas n p.1 * bas n p.2) S :=
    funext fun x => repr_mul _ _ _
  rw [repr_coefwise, e, map_add (f := _), Finsupp.add_apply, repr_mul (coefwise T F), repr_mul (F v)]
  simp only [repr_coefwise]
  rw [hsum (fun p x => (bas n).repr (F x) p.1 * (bas n).repr (G x) p.2 * (bas n).repr (bas n p.1 * bas n p.2) S)
    (fun p => ((hF p.1).mul (hG p.2)).mul (differentiableAt_const _)), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hmul (fun x => (bas n).repr (F x) p.1 * (bas n).repr (G x) p.2) (fun _ => (bas n).repr (bas n p.1 * bas n p.2) S)
    ((hF p.1).mul (hG p.2)) (differentiableAt_const _), hconst,
    hmul (fun x => (bas n).repr (F x) p.1) (fun x => (bas n).repr (G x) p.2) (hF p.1) (hG p.2)]
  ring

theorem exists_ι_mul (y : Alt n) : ∃ y' : Alt n, ∀ m, ExteriorAlgebra.ι ℂ m * y = y' * ExteriorAlgebra.ι ℂ m := by
  induction y using ExteriorAlgebra.induction with
  | algebraMap r => exact ⟨algebraMap ℂ _ r, fun m => (Algebra.commutes r _).symm⟩
  | ι x => exact ⟨-ExteriorAlgebra.ι ℂ x, fun m => by
      rw [neg_mul]; exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap m x)⟩
  | mul a b ha hb =>
    obtain ⟨a', ha⟩ := ha
    obtain ⟨b', hb⟩ := hb
    exact ⟨a' * b', fun m => by rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]⟩
  | add a b ha hb =>
    obtain ⟨a', ha⟩ := ha
    obtain ⟨b', hb⟩ := hb
    exact ⟨a' + b', fun m => by rw [mul_add, ha, hb, add_mul]⟩

theorem sum_mul_leibniz {v : V n} (g : Fin n → (Fin n ⊕ Fin n → ℂ)) (T : Fin n → (V n → ℂ) → ℂ)
    (hsum : ∀ a, ∀ f : Finset (Fin (n + n)) × Finset (Fin (n + n)) → V n → ℂ, (∀ p, DifferentiableAt ℝ (f p) v) →
      T a (fun x => ∑ p, f p x) = ∑ p, T a (f p))
    (hmul : ∀ a, ∀ f g : V n → ℂ, DifferentiableAt ℝ f v → DifferentiableAt ℝ g v →
      T a (fun x => f x * g x) = f v * T a g + T a f * g v)
    (hconst : ∀ a, ∀ c : ℂ, T a (fun _ => c) = 0)
    {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    ∃ y : Alt n, ∑ a, ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) (fun x => F x * G x) =
      (∑ a, ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) F) * G v +
        y * ∑ a, ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) G := by
  obtain ⟨y, hy⟩ := exists_ι_mul (F v)
  refine ⟨y, ?_⟩
  have h (a : Fin n) : ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) (fun x => F x * G x) =
      ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) F * G v + y * (ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) G) := by
    simp only [coefwise_mul (hsum a) (hmul a) (hconst a) hF hG, mul_add, ← mul_assoc, hy]
  rw [Finset.sum_congr rfl fun a _ => h a, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]

theorem delAt_mul {v : V n} {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    ∃ y : Alt n, delAt (fun x => F x * G x) v = delAt F v * G v + y * delAt G v :=
  sum_mul_leibniz (fun a => Pi.single (.inl a) 1) (fun a f => del f v (coordVec a))
    (fun a f hf => by rw [del_sum (fun p _ => hf p), ContinuousLinearMap.sum_apply])
    (fun a f g hf hg => del_mul hf hg _) (fun a c => by rw [del_const]; rfl) hF hG

theorem dbarAt_mul {v : V n} {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    ∃ y : Alt n, dbarAt (fun x => F x * G x) v = dbarAt F v * G v + y * dbarAt G v :=
  sum_mul_leibniz (fun a => Pi.single (.inr a) 1) (fun a f => dbar f v (coordVec a))
    (fun a f hf => by rw [dbar_sum (fun p _ => hf p), ContinuousLinearMap.sum_apply])
    (fun a f g hf hg => dbar_mul hf hg _) (fun a c => by rw [dbar_const]; rfl) hF hG

variable {M : Type} [TopologicalSpace M]

theorem loc_mul (A : HolAtlas M n) (α β : A.Fld) (i : A.ι) (v : V n) :
    A.loc (α * β) i v = A.loc α i v * A.loc β i v := by
  unfold HolAtlas.loc
  split_ifs
  · rfl
  · simp

theorem differentiableAt_coef {A : HolAtlas M n} {α : A.Fld} (h : A.IsForm α) (x : A.Pt) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun v => (bas n).repr (A.loc α x.1.1 v) S) x.crd :=
  ((h.smooth x.1.1 S).contDiffAt ((A.e x.1.1).open_target.mem_nhds (x.ch.map_source x.2))).differentiableAt
    (by simp)

end GlobalTheory.CxForm.FormMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientSpaceEndomorphismScalarSchur
section
set_option autoImplicit false
noncomputable section
open NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MvPolynomial
open scoped Matrix

namespace GlobalTheory.CoefSchur

theorem polyAction_ten (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (h : ι → GL (Fin n) K) (f : ι → MvPolynomial (Fin n × Fin n) K) :
    actP lam h (ten f) = ten fun τ => sqAct K n (lam τ) (h τ) (f τ) := by
  have hb := (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n (fun τ => ((h τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ)).1
  simp only [actP, ten, detTwK, trAct, sqAct, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_prod, hb, map_smul]
  rw [Finset.prod_smul]

theorem natW_anti {n : ℕ} (lam : DomWeight n) : Antitone lam.natW := by
  intro i j hij
  have := lam.anti hij
  unfold DomWeight.natW
  omega

theorem ten_ext_mem (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) :
    (ten fun τ => extremal K n (lam τ)) ∈ VV K lam :=
  Submodule.subset_span ⟨fun τ => extremal K n (lam τ),
    fun τ => Formalism.GradedWeylDivisibility.hwMem K n n le_rfl _ (natW_anti (lam τ)), rfl⟩

theorem endo_scalar : ∀ (K : Type) [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (g : Module.End K (VV K lam)),
    (∀ (h : ι → GL (Fin n) K) v, g (rhoK lam h v) = rhoK lam h (g v)) → ∃ a : K, ∀ v, g v = a • v := by
  intro K _ _ ι _ n lam g hg
  set v0 : VV K lam := ⟨_, ten_ext_mem K lam⟩ with hv0
  have hw0 := (_root_.GlobalTheory.CoefWtLine.weight_line K lam).1
  have hgw := GlobalTheory.T.weylTensorCoefSpace_endomorphism_preserves_torus_weight K lam g hg v0 hw0
  obtain ⟨a, ha⟩ := (_root_.GlobalTheory.CoefWtLine.weight_line K lam).2 _ (g v0).2 hgw
  have ha' : g v0 = a • v0 := Subtype.ext ha
  refine ⟨a, ?_⟩
  let W : Submodule K (Pol K ι n) := Submodule.map (VV K lam).subtype (LinearMap.ker (g - a • LinearMap.id))
  have hS : ∀ τ, nablaSq K n (lam τ) ≤ Submodule.span K (Set.range fun x : GL (Fin n) K => sqAct K n (lam τ) x (extremal K n (lam τ))) :=
    fun τ => _root_.GlobalTheory.nablaSq_le_span_extremal K n (lam τ)
  have hle := GlobalTheory.T.weylTensorCoefSpace_le_span_pure_tensors K lam _ hS
  have hW : VV K lam ≤ W := by
    refine hle.trans (Submodule.span_le.2 ?_)
    rintro P ⟨f, hf, rfl⟩
    choose h hh using hf
    have e : ten f = ten fun τ => sqAct K n (lam τ) (h τ) (extremal K n (lam τ)) := by
      congr 1; funext τ; exact (hh τ).symm
    refine ⟨rhoK lam h v0, ?_, ?_⟩
    · rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hg, ha', map_smul, sub_self]
    · rw [e, ← polyAction_ten]; rfl
  intro v
  obtain ⟨w, hw, hwv⟩ := hW v.2
  have : w = v := Subtype.ext hwv
  subst this
  simpa [sub_eq_zero] using hw

end GlobalTheory.CoefSchur
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompInfRTensorInlA
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open scoped TensorProduct

noncomputable section
open Matrix
namespace GlobalTheory.StdPar.UnipArch

section Lin

variable {A : Type} [CommRing A] {n r : ℕ}

theorem mem_span_cols_iff (C : Matrix (Fin n) (Fin r) A) (I : Set (Fin r)) (y : Fin n → A) :
    y ∈ Submodule.span A ((fun i => Cᵀ i) '' I) ↔ ∃ a : Fin r → A, (∀ l, l ∉ I → a l = 0) ∧ C *ᵥ a = y := by
  first
  | exact @_root_.GlobalTheory.ColumnSumLemma.main
  | exact _root_.GlobalTheory.ColumnSumLemma.main
  | (apply _root_.GlobalTheory.ColumnSumLemma.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ColumnSumLemma.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ColumnSumLemma.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ColumnSumLemma.main ..)

variable (P : Fin r → Fin r → Prop) (hPt : ∀ i l j, P i l → P l j → P i j) (hPlt : ∀ i l, P i l → i < l)
include hPt



end Lin

section Glue

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open GlobalTheory.AutFunCompare (evW sgW)


variable (F) in
def inlA : Ainf F →ₗ[F] AF F := LinearMap.inl F (Ainf F) (Af F)


variable (F) in
def inrA : Af F →ₗ[F] AF F := LinearMap.inr F (Ainf F) (Af F)


variable (F E) in
def glueInf (c : ∀ w : InfinitePlace F, w.Completion ⊗[F] E) : AF F ⊗[F] E :=
  (inlA F).rTensor E (∑ w, (sgW w).rTensor E (c w))

theorem map_evW_sum_sgW (c : ∀ w : InfinitePlace F, w.Completion ⊗[F] E) (w : InfinitePlace F) :
    Algebra.TensorProduct.map (evW w) (AlgHom.id F E) (∑ w', (sgW w').rTensor E (c w')) = c w := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single w]
  · induction c w using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      show (evW w (sgW w a)) ⊗ₜ[F] x = a ⊗ₜ[F] x
      congr 1
      exact Pi.single_eq_same w a
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  · intro w' _ hw'
    induction c w' using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      show (evW w (sgW w' a)) ⊗ₜ[F] x = 0
      rw [show evW w (sgW w' a) = 0 from Pi.single_eq_of_ne (Ne.symm hw') a, TensorProduct.zero_tmul]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]
  · simp

theorem compInf_rTensor_inlA (z : Ainf F ⊗[F] E) (w : InfinitePlace F) :
    compInf F E w ((inlA F).rTensor E z) = Algebra.TensorProduct.map (evW w) (AlgHom.id F E) z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a x => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]

theorem compInf_glueInf (c : ∀ w : InfinitePlace F, w.Completion ⊗[F] E) (w : InfinitePlace F) :
    compInf F E w (glueInf F E c) = c w := by
  rw [glueInf, compInf_rTensor_inlA, map_evW_sum_sgW]

theorem sndA_rTensor_inlA (z : Ainf F ⊗[F] E) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) ((inlA F).rTensor E z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a x =>
    show (sndA F (inlA F a)) ⊗ₜ[F] x = 0
    rw [show sndA F (inlA F a) = 0 from rfl, TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]

theorem sndA_glueInf (c : ∀ w : InfinitePlace F, w.Completion ⊗[F] E) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (glueInf F E c) = 0 :=
  sndA_rTensor_inlA _

@[simp] theorem glueInf_zero : glueInf F E (fun _ => 0) = 0 := by
  simp only [glueInf, map_zero, Finset.sum_const_zero]

theorem tens_ext {z z' : AF F ⊗[F] E} (h1 : ∀ w, compInf F E w z = compInf F E w z')
    (h2 : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z = Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z') :
    z = z' := by
  have hz : ∀ z : AF F ⊗[F] E, z = (inlA F).rTensor E (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) +
      (inrA F).rTensor E (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, map_zero, add_zero]
    | tmul x y =>
      show x ⊗ₜ[F] y = (inlA F (fstA F x)) ⊗ₜ[F] y + (inrA F (sndA F x)) ⊗ₜ[F] y
      rw [← TensorProduct.add_tmul]
      congr 1
      exact Prod.ext (add_zero _).symm (zero_add _).symm
    | add x y hx hy =>
      simp only [map_add (f := _)]
      rw [add_add_add_comm, ← hx, ← hy]
  have hc : ∀ (w : InfinitePlace F) (z : AF F ⊗[F] E), compInf F E w z =
      Algebra.TensorProduct.map (evW w) (AlgHom.id F E) (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) := by
    intro w z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul x y => rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  rw [hz z, hz z', h2, GlobalTheory.AutFunCompare.infTens_ext (fun w => (hc w z).symm.trans ((h1 w).trans (hc w z')))]

end Glue

section Main

end Main

end GlobalTheory.StdPar.UnipArch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLocalOperatorStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_local_operator : ∀ {F : Type} [Field F] [NumberField F] {κ κ₁ : Type} [Fintype κ] [Fintype κ₁] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ), IsLocOp e → IsLocOp (conjLin e) := by
  first | exact @GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin | exact GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin | (intros; apply GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermEqZeroStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspidal_of_isCuspForm' : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsCuspForm φ → GroundTheory.Automorphic.AutomorphicForm.IsCuspidal (K := E) (n := a) φ.1 := by
  first | exact @GlobalTheory.CuspRep.IsCuspForm.constantTerm_eq_zero | exact GlobalTheory.CuspRep.IsCuspForm.constantTerm_eq_zero | (intros; apply GlobalTheory.CuspRep.IsCuspForm.constantTerm_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveDegreeNonnegZmodFibreOfNefOnFiniteFieldFibrStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curveDegree_nonneg_zmodFibre_of_nefOnFiniteFieldFibres : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k) (L : HermLB q) (p : ℕ) [Fact p.Prime], ArInt.NefFib L → ∀ (Z : Scheme.{0}) (i : Z ⟶ pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod p) Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod p) ((L.B.pull (pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))).pull i) 1 := by
  first | exact @GlobalTheory.NefFibPrime.topSelf_nonneg_of_nefFib | exact GlobalTheory.NefFibPrime.topSelf_nonneg_of_nefFib | (intros; apply GlobalTheory.NefFibPrime.topSelf_nonneg_of_nefFib <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeNonnegOfCurveDegreeNonnegOverZmodStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_nonneg_of_curveDegree_nonneg_over_zmod : ∀ (p : ℕ) [Fact p.Prime] (V : Scheme.{0}) [Algebra (ZMod p) Γ(V, ⊤)], IsProjOver (strHom (ZMod p) (X := V)) → topologicalKrullDim V ≤ 1 → ∀ N : LB V, N.IsLB → (∀ (Z : Scheme.{0}) (i : Z ⟶ V) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod p) Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod p) (N.pull i) 1) → 0 ≤ degOfRank (ZMod p) (toMod N) 1 := by
  first | exact @GlobalTheory.CurveDevissage.degOfRank_nonneg | exact GlobalTheory.CurveDevissage.degOfRank_nonneg | (intros; apply GlobalTheory.CurveDevissage.degOfRank_nonneg <;> assumption)
end

