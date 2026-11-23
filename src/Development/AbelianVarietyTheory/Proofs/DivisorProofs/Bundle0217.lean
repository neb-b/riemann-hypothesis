module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0165
public import Formalism.SatakeDualWeyl.Statement
public import GroundTheory.GlobalFields.TateThesis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0163

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFiltrationPreimageIffEvalMem
section
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory.FilPreMem

theorem poly_mem (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ))
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (N : ℕ) (F : Submodule w.valuationSubring (S → Fin N → C))
    (hF : ∀ x ∈ F, GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.unif a x ∈ F) (f : Polynomial (Int0 v)) :
    ∀ y ∈ F, (fun s i => ((f.eval (liftA hv a s) : Int0 v) : C) * y s i) ∈ F := by
  induction f using Polynomial.induction_on with
  | C c =>
    intro y hy
    have := F.smul_mem (⟨(c : C), (hv _).1 c.2⟩ : w.valuationSubring) hy
    convert this using 1
    funext s i
    simp only [Polynomial.eval_C]
    rfl
  | add p q hp hq =>
    intro y hy
    have := F.add_mem (hp y hy) (hq y hy)
    convert this using 1
    funext s i
    simp only [Polynomial.eval_add, Subring.coe_add, Pi.add_apply, add_mul]
  | monomial n c h =>
    intro y hy
    have := hF _ (h y hy)
    convert this using 1
    funext s i
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.unif, Pi.smul_apply, smul_eq_mul, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Subring.coe_mul,
      Subring.coe_pow, pow_succ, liftA]
    ring

theorem filPre_mem_iff : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ)) (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ) (F : Submodule w.valuationSubring (S → Fin N → C)), (∀ x ∈ F, GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.unif a x ∈ F) → ∀ x, x ∈ (Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F}) ↔ evalVec (liftA hv a) N x ∈ F := by
  intro C _ w v hv S _ _ a N F hF x
  let T : Submodule (RS (liftA hv a)) (Fin N → RS (liftA hv a)) :=
    { carrier := {x | evalVec (liftA hv a) N x ∈ F}
      zero_mem' := by
        show evalVec (liftA hv a) N 0 ∈ F
        have : evalVec (liftA hv a) N 0 = 0 := by
          funext s i; simp [evalVec]
        rw [this]; exact F.zero_mem
      add_mem' := by
        intro x y hx hy
        show evalVec (liftA hv a) N (x + y) ∈ F
        rw [evalVec_add]; exact F.add_mem hx hy
      smul_mem' := by
        intro r x hx
        show evalVec (liftA hv a) N (r • x) ∈ F
        induction r using AdjoinRoot.induction_on with
        | ih f =>
          have := poly_mem C w v hv S a N F hF f _ hx
          convert this using 1
          funext s i
          simp [evalVec, ev] }
  constructor
  · intro hx
    have : (Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F}) ≤ T := Submodule.span_le.2 (fun y hy => hy)
    exact this hx
  · intro hx
    exact Submodule.subset_span hx

end GlobalTheory.FilPreMem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIdealTransformOfForallSmulMem
section
open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

def idealTransform (S : Type) [CommRing S] (I : Ideal S) (A : Type) [CommRing A] [Algebra S A] :
    Subalgebra S (FractionRing S ⊗[S] A) where
  carrier := {z | ∃ k : ℕ, ∀ a ∈ I ^ k,
    a • z ∈ (Algebra.TensorProduct.includeRight : A →ₐ[S] FractionRing S ⊗[S] A).range}
  mul_mem' := by
    rintro z w ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨k + l, fun a ha => ?_⟩
    rw [pow_add] at ha
    refine Submodule.mul_induction_on ha (fun b hb c hc => ?_) (fun u v hu hv => ?_)
    · rw [← smul_mul_smul_comm]
      exact mul_mem (hk b hb) (hl c hc)
    · rw [add_smul]; exact add_mem hu hv
  add_mem' := by
    rintro z w ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨max k l, fun a ha => ?_⟩
    rw [smul_add]
    exact add_mem (hk a (Ideal.pow_le_pow_right (le_max_left _ _) ha))
      (hl a (Ideal.pow_le_pow_right (le_max_right _ _) ha))
  algebraMap_mem' := by
    intro r
    refine ⟨0, fun a _ => ?_⟩
    exact ⟨algebraMap S A (a * r), by simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, smul_tmul', mul_smul]⟩

theorem mem_idealTransform_of_forall_smul_mem {S : Type} [CommRing S] [IsNoetherianRing S]
    {I : Ideal S} {A : Type} [CommRing A] [Algebra S A] (z : FractionRing S ⊗[S] A)
    (h : ∀ a ∈ I, a • z ∈ idealTransform S I A) : z ∈ idealTransform S I A := by
  let R := (Algebra.TensorProduct.includeRight : A →ₐ[S] FractionRing S ⊗[S] A).range
  let Q : Ideal S := Submodule.comap (LinearMap.toSpanSingleton S _ z) (Subalgebra.toSubmodule R)
  have hQ : ∀ a, a ∈ Q ↔ a • z ∈ R := fun a => by simp [Q]
  have hrad : I ≤ Q.radical := by
    intro a ha
    obtain ⟨k, hk⟩ := h a ha
    refine ⟨k + 1, ?_⟩
    rw [hQ, pow_succ, mul_smul]
    exact hk _ (Ideal.pow_mem_pow ha k)
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian I)
  exact ⟨n, fun a ha => (hQ a).1 (hn ha)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPolynomialEvalFreeLatticeIffExistsEval
section
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory.EvalVecRange

def toW {C : Type} [Field C] {w : Valuation C ℝ≥0} {v : AddValuation C (WithTop ℝ)}
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) : Int0 v →+* w.valuationSubring where
  toFun x := ⟨x, (hv x).1 x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def toV {C : Type} [Field C] {w : Valuation C ℝ≥0} {v : AddValuation C (WithTop ℝ)}
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) : w.valuationSubring →+* Int0 v where
  toFun x := ⟨x, (hv x).2 x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem ev_mk {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {S : Type} [Fintype S]
    [DecidableEq S] (b : S → Int0 v) (s : S) (g : Polynomial (Int0 v)) :
    ev b s (AdjoinRoot.mk _ g) = g.eval (b s) := by
  unfold ev
  rw [AdjoinRoot.liftAlgHom_mk]
  rfl

theorem evalVec_range : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ))
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (N : ℕ) (y : S → Fin N → C),
    y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y := by
  intro C _ w v hv S _ _ a N y
  constructor
  · intro hy
    choose f hf using hy
    refine ⟨fun i => AdjoinRoot.mk _ ((f i).map (toV hv)), ?_⟩
    funext s i
    simp only [evalVec]
    rw [ev_mk, Polynomial.eval_map, hf i s]
    have : liftA hv a s = toV hv (a s) := rfl
    rw [this, Polynomial.eval₂_hom]
    rfl
  · rintro ⟨x, rfl⟩ i
    obtain ⟨g, hg⟩ := AdjoinRoot.mk_surjective (x i)
    refine ⟨g.map (toW hv), fun s => ?_⟩
    simp only [evalVec]
    rw [← hg, ev_mk, Polynomial.eval_map]
    have : a s = toW hv (liftA hv a s) := rfl
    rw [this, Polynomial.eval₂_hom]
    rfl

end GlobalTheory.EvalVecRange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTraceDualSignedPositiveConeIffTotallyPositive
section
open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory.Div.LipschitzCone

theorem sign_cone_iff (x y w : ℝ) (hx : x ≠ 0) (hw : 0 < w) :
    0 < (SignType.sign (x * w) : ℝ) * y ↔ 0 < y * x := by
  rw [sign_mul, sign_pos hw, mul_one]
  rcases lt_or_gt_of_ne hx with h | h
  · rw [sign_neg h]
    simp only [SignType.coe_neg, SignType.coe_one, neg_mul, one_mul, Left.neg_pos_iff]
    constructor
    · intro hy; exact mul_pos_of_neg_of_neg hy h
    · intro hyx
      by_contra hc
      push_neg at hc
      have := mul_nonpos_of_nonneg_of_nonpos hc h.le
      linarith
  · rw [sign_pos h]
    simp only [SignType.coe_one, one_mul]
    constructor
    · intro hy; exact mul_pos hy h
    · intro hyx; exact pos_of_mul_pos_left hyx h.le

theorem cone_iff : ∀ (F : Type) [Field F] [NumberField F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (b : F), b ≠ 0 →
    ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∀ ν : F,
      ν ∈ GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.dualCone (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞) (fun τ => ((τ b : ℝ) : ℂ) * z τ) ↔
        (ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ τ : F →+* ℝ, 0 < τ (ν * b)) := by
  intro F _ _ 𝔞 b hb z hz ν
  have ha : (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := 𝔞.ne_zero
  have hM : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 ≠ 0 := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual]
    exact FractionalIdeal.dual_ne_zero ℤ ℚ ha
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.dualCone
  simp only [Set.mem_setOf_eq]
  rw [GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.mem_traceDual_iff hM, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual, FractionalIdeal.dual_dual]
  refine and_congr Iff.rfl (forall_congr' fun τ => ?_)
  rw [Complex.im_ofReal_mul, map_mul τ ν b]
  exact sign_cone_iff _ _ _ ((map_ne_zero τ).2 hb) (hz τ)

end GlobalTheory.Div.LipschitzCone
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGETwoOfRegularQuotientNoSocle
section
open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

theorem modDepthGE_two_of_isSMulRegular_of_quotSMulTop :
    ∀ (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] (M : Type) [AddCommGroup M]
      [Module S M] [Module.Finite S M] [Nontrivial M] (x : S), x ∈ maximalIdeal S →
      IsSMulRegular M x →
      (∀ u : M, (∀ a ∈ maximalIdeal S, a • u ∈ x • (⊤ : Submodule S M)) →
        u ∈ x • (⊤ : Submodule S M)) →
      ReciprocityTheory.CA.ModDepthGE S M 2 := by
  intro S _ _ _ M _ _ _ _ x hxm hreg hsoc
  obtain ⟨y, hym, hyreg⟩ : ∃ y ∈ maximalIdeal S, IsSMulRegular (QuotSMulTop x M) y := by
    by_contra hno
    push_neg at hno
    have hfin := associatedPrimes.finite S (QuotSMulTop x M)
    have hsub : (maximalIdeal S : Set S) ⊆
        ⋃ p ∈ associatedPrimes S (QuotSMulTop x M), (p : Set S) := by
      intro y hy
      rw [biUnion_associatedPrimes_eq_compl_regular]
      exact hno y hy
    obtain ⟨p, hp, hmp⟩ := (Ideal.subset_union_prime (s := hfin.toFinset) (f := id) ⊥ ⊥
      (fun p hp _ _ => (hfin.mem_toFinset.mp hp).isPrime)).mp (by simpa using hsub)
    rw [hfin.mem_toFinset] at hp
    have hpm : p = maximalIdeal S :=
      (le_antisymm (le_maximalIdeal (hp.isPrime.ne_top)) hmp)
    rw [hpm] at hp
    obtain ⟨-, w, hw⟩ := isAssociatedPrime_iff.mp hp
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hu : ∀ a ∈ maximalIdeal S, a • u ∈ x • (⊤ : Submodule S M) := by
      intro a ha
      rw [hw, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero] at ha
      exact ha
    apply (maximalIdeal.isMaximal S).ne_top
    rw [hw, Ideal.eq_top_iff_one, Submodule.mem_colon_singleton, Submodule.mem_bot, one_smul,
      Submodule.Quotient.mk_eq_zero]
    exact hsoc u hu
  refine ⟨[x, y], rfl, (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption), ?_⟩
  rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
    (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption),
    RingTheory.Sequence.isWeaklyRegular_cons_iff, RingTheory.Sequence.isWeaklyRegular_cons_iff]
  exact ⟨hreg, hyreg, RingTheory.Sequence.IsWeaklyRegular.nil _ _⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularGroupRowVecAndConjRightActions
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.Act

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.Act.redGL_mul (N : ℕ) (γ δ : SL(2, ℤ)) :
    _root_.GlobalTheory.WpFam.redGL N (γ * δ) = _root_.GlobalTheory.WpFam.redGL N γ * _root_.GlobalTheory.WpFam.redGL N δ := by
  unfold _root_.GlobalTheory.WpFam.redGL
  simp [map_mul]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.Act.redGL_one (N : ℕ) : _root_.GlobalTheory.WpFam.redGL N 1 = 1 := by
  unfold _root_.GlobalTheory.WpFam.redGL
  simp

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.Act.vmul_vmul {N : ℕ} (x : Fin 2 → ZMod N) (α β : GL (Fin 2) (ZMod N)) :
    _root_.GlobalTheory.WpFam.vmul (_root_.GlobalTheory.WpFam.vmul x α) β = _root_.GlobalTheory.WpFam.vmul x (α * β) := by
  unfold _root_.GlobalTheory.WpFam.vmul
  simp [Matrix.vecMul_vecMul]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.Act.vmul_one {N : ℕ} (x : Fin 2 → ZMod N) : _root_.GlobalTheory.WpFam.vmul x 1 = x := by
  unfold _root_.GlobalTheory.WpFam.vmul
  simp

theorem isRAct_gact (N : ℕ) (D : GL (Fin 2) (ZMod N)) : IsRAct (gact N D) := by
  constructor
  · intro x; simp [gact, redGL_one]
  · intro x γ δ; simp only [gact, redGL_mul]; group


open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.Act.rightActions : ∀ (N : ℕ), _root_.GlobalTheory.QFam.IsRAct (_root_.GlobalTheory.WpFam.vact N) ∧ (∀ D, _root_.GlobalTheory.QFam.IsRAct (_root_.GlobalTheory.WpFam.gact N D)) ∧ (∀ (x : Fin 2 → ZMod N) α β, _root_.GlobalTheory.WpFam.vmul (_root_.GlobalTheory.WpFam.vmul x α) β = _root_.GlobalTheory.WpFam.vmul x (α * β)) ∧ (∀ x : Fin 2 → ZMod N, _root_.GlobalTheory.WpFam.vmul x 1 = x) ∧ (∀ (x : Fin 2 → ZMod N) α, _root_.GlobalTheory.WpFam.vmul x α = 0 ↔ x = 0) ∧ (∀ (M : ℕ) (x : Fin 2 → ZMod N) α, _root_.GlobalTheory.WpFam.vmul (M • x) α = M • _root_.GlobalTheory.WpFam.vmul x α) ∧ (∀ (x : Fin 2 → ZMod N) (a : (ZMod N)ˣ), _root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a) = ![x 0, (a : ZMod N) * x 1]) ∧ (∀ γ δ, _root_.GlobalTheory.WpFam.redGL N (γ * δ) = _root_.GlobalTheory.WpFam.redGL N γ * _root_.GlobalTheory.WpFam.redGL N δ) ∧ _root_.GlobalTheory.WpFam.redGL N 1 = 1 := by
  intro N
  refine ⟨?_, ?_, _root_.GlobalTheory.WpFam.Act.vmul_vmul, _root_.GlobalTheory.WpFam.Act.vmul_one, ?_, ?_, ?_,
    _root_.GlobalTheory.WpFam.Act.redGL_mul N, _root_.GlobalTheory.WpFam.Act.redGL_one N⟩
  · refine ⟨fun x => ?_, fun x γ δ => ?_⟩
    · unfold _root_.GlobalTheory.WpFam.vact
      rw [_root_.GlobalTheory.WpFam.Act.redGL_one, _root_.GlobalTheory.WpFam.Act.vmul_one]
    · unfold _root_.GlobalTheory.WpFam.vact
      rw [_root_.GlobalTheory.WpFam.Act.vmul_vmul, _root_.GlobalTheory.WpFam.Act.redGL_mul]
  · intro D
    refine ⟨fun α => ?_, fun α γ δ => ?_⟩
    · unfold _root_.GlobalTheory.WpFam.gact
      rw [_root_.GlobalTheory.WpFam.Act.redGL_one]
      group
    · unfold _root_.GlobalTheory.WpFam.gact
      rw [_root_.GlobalTheory.WpFam.Act.redGL_mul]
      group
  · intro x α
    constructor
    · intro h
      have key := congrArg (fun y => _root_.GlobalTheory.WpFam.vmul y α⁻¹) h
      simp only [_root_.GlobalTheory.WpFam.Act.vmul_vmul, mul_inv_cancel, _root_.GlobalTheory.WpFam.Act.vmul_one] at key
      rw [key]
      unfold _root_.GlobalTheory.WpFam.vmul
      simp
    · rintro rfl
      unfold _root_.GlobalTheory.WpFam.vmul
      simp
  · intro M x α
    unfold _root_.GlobalTheory.WpFam.vmul
    rw [Matrix.smul_vecMul]
  · intro x a
    unfold _root_.GlobalTheory.WpFam.vmul _root_.GlobalTheory.WpFam.dg
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]

end GlobalTheory.WpFam.Act
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPolynomialEqZeroOfVanishSkewHermitianStatement
section
set_option autoImplicit false
noncomputable section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPolynomial_eq_zero_of_vanish_skewHermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → σ ≠ AlgHom.id F E → Module.finrank F E = 2 →
    ∀ {ι : Type} [Fintype ι] (ψ : ι → (E →+* ℂ)), Function.Injective (fun τ => (ψ τ).comp (algebraMap F E)) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Formalism.UG.cT (σ : E →+* E) J = J → J.det ≠ 0 →
    ∀ Q : MvPolynomial (ι × Fin n × Fin n) ℂ,
      (∀ S : Matrix (Fin n) (Fin n) E, Formalism.UG.cT (σ : E →+* E) S * J + J * S = 0 →
        MvPolynomial.eval (fun p => ψ p.1 (S p.2.1 p.2.2)) Q = 0) → Q = 0 := by
  first | exact @GlobalTheory.SkewDense.eq_zero_of_vanish_skew | exact GlobalTheory.SkewDense.eq_zero_of_vanish_skew | (intros; apply GlobalTheory.SkewDense.eq_zero_of_vanish_skew <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NarrowGaussConvolutionDense
section
open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory.NarrowGauss

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def gauss (c : ℝ) (hc : 0 < c) : SchwartzMap E ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearEquiv.smulOfNeZero ℝ E (Real.sqrt (c / Real.pi))
      (Real.sqrt_ne_zero'.2 (div_pos hc Real.pi_pos))).toContinuousLinearEquiv)
    (GroundTheory.Global.gaussianSchwartz E)

theorem gauss_apply (c : ℝ) (hc : 0 < c) (x : E) :
    gauss c hc x = Complex.exp (-(c : ℂ) * ‖x‖ ^ 2) := by
  rw [gauss, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply]
  have h : -Real.pi * ‖(LinearEquiv.smulOfNeZero ℝ E (Real.sqrt (c / Real.pi))
      (Real.sqrt_ne_zero'.2 (div_pos hc Real.pi_pos))).toContinuousLinearEquiv x‖ ^ 2
      = -c * ‖x‖ ^ 2 := by
    simp only [LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.smulOfNeZero_apply,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      Real.sq_sqrt (div_pos hc Real.pi_pos).le]
    field_simp
  rw [h, Complex.ofReal_exp]
  push_cast
  ring_nf

theorem fourier_gauss (c : ℝ) (hc : 0 < c) (w : E) :
    (𝓕 (gauss (E := E) c hc) : SchwartzMap E ℂ) w = (Real.pi / (c : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ) *
      Complex.exp (-Real.pi ^ 2 * ‖w‖ ^ 2 / c) := by
  rw [SchwartzMap.fourier_coe]
  have : (⇑(gauss c hc) : E → ℂ) = fun v ↦ Complex.exp (-(c : ℂ) * ‖v‖ ^ 2) :=
    funext (gauss_apply c hc)
  rw [this, fourier_gaussian_innerProductSpace (by simpa using hc)]

theorem fourierInv_gauss_mul_eq (f u : SchwartzMap E ℂ) (b : ℝ) (hb : 0 < b)
    (hu : ∀ y, u y = Complex.exp (-((b * ‖y‖ ^ 2 : ℝ) : ℂ)) * (𝓕 f : SchwartzMap E ℂ) y) :
    ∃ (c : ℝ) (s : ℂ), 0 < c ∧ ∀ y, (𝓕⁻ u : SchwartzMap E ℂ) y =
      s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) := by
  set c : ℝ := Real.pi ^ 2 / b with hc_def
  have hc : 0 < c := by positivity
  set K : ℂ := (Real.pi / (c : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ) with hK
  have hK0 : K ≠ 0 := by
    rw [hK]
    exact Complex.cpow_ne_zero_iff.2 (Or.inl (div_ne_zero (by exact_mod_cast Real.pi_ne_zero)
      (by exact_mod_cast hc.ne')))
  set g : SchwartzMap E ℂ := gauss c hc
  set v : SchwartzMap E ℂ := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f g
  have huv : u = K⁻¹ • (𝓕 v : SchwartzMap E ℂ) := by
    ext ξ
    rw [SchwartzMap.smul_apply, SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply,
      ContinuousLinearMap.mul_apply', fourier_gauss, ← hK, hu, smul_eq_mul]
    have e : Complex.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / c) = Complex.exp (-((b * ‖ξ‖ ^ 2 : ℝ) : ℂ)) := by
      congr 1
      rw [hc_def]
      push_cast
      field_simp
    rw [e]
    field_simp
  refine ⟨c, K⁻¹, hc, fun y ↦ ?_⟩
  rw [huv, FourierTransform.fourierInv_smul, FourierTransform.fourierInv_fourier_eq,
    SchwartzMap.smul_apply, smul_eq_mul, SchwartzMap.convolution_apply, convolution_def]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun a ↦ ?_)
  simp only [ContinuousLinearMap.mul_apply', g, gauss_apply]
  push_cast
  ring_nf

end GlobalTheory.NarrowGauss

open GlobalTheory.NarrowGauss in
theorem GlobalTheory.narrowGauss_convolution_dense :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : SchwartzMap E ℂ),
    f ∈ closure {u : SchwartzMap E ℂ | ∃ (c : ℝ) (s : ℂ), 0 < c ∧
      ∀ y, u y = s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))} := by
  intro E _ _ _ _ _ f
  have h1 := _root_.GlobalTheory.GaussCutoff.mem_closure_gauss_mul E (𝓕 f : SchwartzMap E ℂ)
  have h2 := map_mem_closure (f := fun w : SchwartzMap E ℂ ↦ (𝓕⁻ w : SchwartzMap E ℂ))
    (t := {u : SchwartzMap E ℂ | ∃ (c : ℝ) (s : ℂ), 0 < c ∧
      ∀ y, u y = s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))})
    FourierTransform.continuous_fourierInv h1 (fun u hu ↦ by
      obtain ⟨b, hb, hu⟩ := hu
      exact fourierInv_gauss_mul_eq f u b hb hu)
  simpa [FourierTransform.fourierInv_fourier_eq] using h2
end

