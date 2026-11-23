module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCB
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulFix
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace GlobalTheory.SplitInvFormF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E}
  {ψ : AddChar (AF F) ℂ}


variable (σ) in
def conjHalf (e : AEF F E) (nS nT : ℕ) : AddSubgroup (WOF F E nS nT) where
  carrier := {u | ∀ i j, cAF σ e * u i j = u i j}
  add_mem' := fun {a b} ha hb i j => by
    simp only [Set.mem_setOf_eq] at ha hb
    rw [Matrix.add_apply, mul_add, ha i j, hb i j]
  zero_mem' := fun i j => by simp
  neg_mem' := fun {a} ha i j => by
    simp only [Set.mem_setOf_eq] at ha
    rw [Matrix.neg_apply, mul_neg, ha i j]


variable (σ JS JT xi0 ψ) in
def heisL (w : WOF F E nS nT) : (WOF F E nS nT → ℂ) →ₗ[ℂ] (WOF F E nS nT → ℂ) where
  toFun := heisOF σ JS JT xi0 ψ w
  map_add' := GlobalTheory.WeilPartsF.heisOF_add w
  map_smul' := fun c f => GlobalTheory.WeilPartsF.heisOF_smul c w f


variable (σ JS JT xi0 ψ) in
def commF (u y : WOF F E nS nT) : ℂ :=
  ψ (symplOHF σ JS JT xi0 u y - symplOHF σ JS JT xi0 y u)

theorem heisOF_heisOF (u y : WOF F E nS nT) (f : WOF F E nS nT → ℂ) :
    heisOF σ JS JT xi0 ψ u (heisOF σ JS JT xi0 ψ y f) =
      ψ (symplOHF σ JS JT xi0 u y) • heisOF σ JS JT xi0 ψ (u + y) f := by
  funext w
  simp only [heisOF, Pi.smul_apply, smul_eq_mul]
  rw [GlobalTheory.HeisThetaF.symplOHF_add_left w u y, GlobalTheory.HeisThetaF.symplOHF_add_right w u y,
    AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, add_assoc]
  ring

theorem heisOF_comm (u y : WOF F E nS nT) (f : WOF F E nS nT → ℂ) :
    heisOF σ JS JT xi0 ψ u (heisOF σ JS JT xi0 ψ y f) =
      commF σ JS JT xi0 ψ u y • heisOF σ JS JT xi0 ψ y (heisOF σ JS JT xi0 ψ u f) := by
  rw [heisOF_heisOF, heisOF_heisOF, smul_smul, add_comm y u, commF, ← AddChar.map_add_eq_mul, sub_add_cancel]

theorem heisOF_zero (f : WOF F E nS nT → ℂ) : heisOF σ JS JT xi0 ψ 0 f = f := by
  funext w
  simp only [heisOF, add_zero, GlobalTheory.HeisThetaF.symplOHF_zero_right, AddChar.map_zero_eq_one, one_mul]

theorem cAF_cAF {e : AEF F E} (he : IsSplitIdemF σ e) : cAF σ (cAF σ e) = e := by
  obtain ⟨-, -, v, ε, -, h⟩ := he
  have h2 := congrArg (cAF σ) h
  rw [map_add (f := _), GlobalTheory.HeisThetaF.cAF_algebraMap] at h2
  linear_combination h2 - h

theorem hOF_half {e : AEF F E} (he : IsSplitIdemF σ e) {x y : WOF F E nS nT} (hx : x ∈ conjHalf σ e nS nT)
    (hy : y ∈ conjHalf σ e nS nT) : hOF σ JS JT x y = 0 := by
  have hcc := cAF_cAF he
  have h2 : e * cAF σ e = 0 := he.2.1
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
    Finset.sum_eq_zero fun d _ => ?_
  have e1 : cAF σ (y c b) = e * cAF σ (y c b) := by
    conv_lhs => rw [← hy c b]
    rw [map_mul, hcc]
  rw [e1, ← hx d a]
  linear_combination (incAF F E (JS⁻¹ a b) * cAF σ (y c b) * incAF F E (JT c d) * x d a) * h2

theorem symplOHF_half {e : AEF F E} (he : IsSplitIdemF σ e) {x y : WOF F E nS nT} (hx : x ∈ conjHalf σ e nS nT)
    (hy : y ∈ conjHalf σ e nS nT) : symplOHF σ JS JT xi0 x y = 0 := by
  simp only [symplOHF, symplOF, hOF_half he hx hy, mul_zero, map_zero]

theorem exists_nsmul_fix {e : AEF F E} (he : IsSplitIdemF σ e) {u : WOF F E nS nT} (hu : u ∈ conjHalf σ e nS nT)
    {g : WOF F E nS nT → ℂ} (hg : IsThetaFunOF σ JS JT xi0 ψ g) :
    ∃ k : ℕ, 0 < k ∧ heisOF σ JS JT xi0 ψ (k • u) g = g := by
  obtain ⟨he1, he2, v, ε, hpl, hsum⟩ := he
  obtain ⟨α, rfl, hα1, hα0⟩ := id hpl
  obtain ⟨U, hU, hUf⟩ := hg.level
  haveI : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  haveI : ContinuousSMul (AF F) (AEF F E) := IsModuleTopology.toContinuousSMul (AF F) (AEF F E)
  set ε' := algebraMap (AF F) (AEF F E) (pairA F 0 α) with hε'
  have hcc : cAF σ e * cAF σ e = cAF σ e := by rw [← map_mul, he1]
  have hce : cAF σ e * ε' = cAF σ e := by
    rw [← hsum]
    linear_combination he2 + hcc
  have hu' : ∀ i j, ε' * u i j = u i j := fun i j => by
    have := hu i j
    calc ε' * u i j = ε' * (cAF σ e * u i j) := by rw [this]
      _ = (cAF σ e * ε') * u i j := by ring
      _ = u i j := by rw [hce, this]
  let φ : Af F → WOF F E nS nT := fun t i j => algebraMap (AF F) (AEF F E) (pairA F 0 t) * u i j
  have hφ : Continuous φ := by
    have h1 : Continuous fun t : Af F => algebraMap (AF F) (AEF F E) (pairA F 0 t) := by
      have : Continuous fun t : Af F => pairA F 0 t := continuous_const.prodMk continuous_id
      have h2 : Continuous fun c : AF F => algebraMap (AF F) (AEF F E) c := by
        simp only [Algebra.algebraMap_eq_smul_one]
        exact continuous_smul.comp (continuous_id.prodMk continuous_const)
      exact h2.comp this
    exact continuous_pi fun i => continuous_pi fun j => h1.mul continuous_const
  have h0 : φ 0 = 0 := by
    funext i j
    show algebraMap (AF F) (AEF F E) (pairA F 0 0) * u i j = 0
    rw [show pairA F 0 0 = (0 : AF F) from rfl, map_zero, zero_mul]
  have hV : φ ⁻¹' (U : Set (WOF F E nS nT)) ∈ nhds (0 : Af F) :=
    (hU.preimage hφ).mem_nhds (by rw [Set.mem_preimage, h0]; exact U.zero_mem)
  obtain ⟨N, hN, hNα⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hV
  have hint : ∀ w, α w ∈ w.adicCompletionIntegers F := fun w => by
    by_cases hw : w = v
    · subst hw
      rw [show α w = 1 from hα1]
      exact one_mem _
    · rw [show α w = 0 from hα0 w hw]
      exact zero_mem _
  have hmem := hNα α hint
  have heq : φ (N • α) = N • u := by
    funext i j
    show algebraMap (AF F) (AEF F E) (pairA F 0 (N • α)) * u i j = (N • u) i j
    rw [show pairA F 0 (N • α) = N • pairA F 0 α by
      show ((0 : Ainf F), N • α) = N • ((0 : Ainf F), α)
      rw [Prod.smul_mk, smul_zero], map_nsmul, smul_mul_assoc, hu' i j, Matrix.smul_apply]
  rw [Set.mem_preimage, heq] at hmem
  refine ⟨N, hN, hUf _ hmem ?_⟩
  ext i j
  show infPartF F E ((N • u) i j) = 0
  rw [Matrix.smul_apply, map_nsmul, ← hu' i j, map_mul, GlobalTheory.WeilPartsF.infPartF_placeIdem hpl, zero_mul, smul_zero]

end GlobalTheory.SplitInvFormF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealChartAdeleTensorAdmissibleCMBase
section
noncomputable section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

namespace GlobalTheory.RealWeilF.CMChart

open Formalism.L2.Fam.ThC

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rc [IsTotallyReal F] (v : InfinitePlace F) : v.Completion ≃+* ℝ :=
  InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)

theorem compF_eq [IsTotallyReal F] (τ : E →+* ℂ) (w : InfinitePlace F) (h : plF (F := F) τ = w) (a : Ainf F) :
    compF (F := F) τ a = (rc w (a w) : ℝ) := by
  subst h
  exact (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal _) _).symm

def rho [IsTotallyReal F] : (InfinitePlace F → ℝ) →+ Ainf F where
  toFun x v := (rc v).symm (x v)
  map_zero' := funext fun v => map_zero (rc v).symm
  map_add' _ _ := funext fun v => map_add (rc v).symm _ _

theorem continuous_rho [IsTotallyReal F] : Continuous (rho (F := F)) :=
  continuous_pi fun v =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.continuous.comp
      (continuous_apply v)

theorem rc_rho [IsTotallyReal F] (x : InfinitePlace F → ℝ) (w : InfinitePlace F) : rc w (rho x w) = x w :=
  (rc w).apply_symm_apply _

def embA (e : E) : Ainf F →+ AEF F E where
  toFun a := pairA F a 0 ⊗ₜ[F] e
  map_zero' := TensorProduct.zero_tmul _ _
  map_add' a b := by
    rw [← TensorProduct.add_tmul]
    congr 1
    exact Prod.ext rfl (add_zero _).symm

theorem continuous_embA (e : E) : Continuous (embA (F := F) e) := by
  haveI := isModuleTopology_AE F E
  have h1 : Continuous fun a : Ainf F => pairA F a 0 :=
    Continuous.prodMk continuous_id continuous_const
  have h2 : Continuous fun a : AF F => a • ((1 : AF F) ⊗ₜ[F] e : AEF F E) :=
    continuous_smul.comp (continuous_id.prodMk continuous_const)
  refine (h2.comp h1).congr fun a => ?_
  show pairA F a 0 • ((1 : AF F) ⊗ₜ[F] e : AEF F E) = pairA F a 0 ⊗ₜ[F] e
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem finPart_embA (e : E) (a : Ainf F) : finPartF F E (embA e a) = 0 :=
  TensorProduct.zero_tmul _ e

theorem infPart_embA (e : E) (a : Ainf F) : infPartF F E (embA e a) = a ⊗ₜ[F] e := rfl

theorem tensor_span {M : Type} [AddCommGroup M] [Module F M] (δ : E)
    (h : ∀ x : E, ∃ u v : F, u • (1 : E) + v • δ = x) (a : M ⊗[F] E) :
    ∃ a₀ a₁ : M, a = a₀ ⊗ₜ[F] (1 : E) + a₁ ⊗ₜ[F] δ := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul m x =>
    obtain ⟨u, v, rfl⟩ := h x
    exact ⟨u • m, v • m, by simp only [TensorProduct.tmul_add, TensorProduct.smul_tmul]⟩
  | add a b ha hb =>
    obtain ⟨a₀, a₁, rfl⟩ := ha
    obtain ⟨b₀, b₁, rfl⟩ := hb
    exact ⟨a₀ + b₀, a₁ + b₁, by simp only [TensorProduct.add_tmul]; abel⟩

theorem exists_gen {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ δ : E, (∀ τ : E →+* ℂ, (τ δ).im ≠ 0) ∧ ∀ x : E, ∃ u v : F, u • (1 : E) + v • δ = x := by
  obtain ⟨-, hc, h2, hσ⟩ := h
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hn : ¬ ComplexEmbedding.IsReal τ₀ := IsTotallyComplex.complexEmbedding_not_isReal τ₀
  have : ∃ δ : E, σ δ ≠ δ := by
    by_contra hcon
    push Not at hcon
    apply hn
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := hσ τ₀ x
    rw [hcon] at this
    exact this.symm
  obtain ⟨δ, hδ⟩ := this
  refine ⟨δ, fun τ hτ => hδ (τ.injective ?_), ?_⟩
  · rw [hσ]
    exact Complex.conj_eq_iff_im.2 hτ
  · have hli : LinearIndependent F ![(1 : E), δ] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h3 := congrArg σ hst
      rw [map_add (f := _), Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, σ.commutes, σ.commutes, map_one, map_zero,
        ← Algebra.smul_def, ← Algebra.smul_def] at h3
      have h4 : t • (σ δ - δ) = 0 := by
        rw [smul_sub, eq_neg_of_add_eq_zero_right h3, eq_neg_of_add_eq_zero_right hst, sub_self]
      have ht : t = 0 := (smul_eq_zero.1 h4).resolve_right (sub_ne_zero.2 hδ)
      rw [ht, zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.1 hst).resolve_right one_ne_zero, ht⟩
    have hsp := hli.span_eq_top_of_card_eq_finrank (by rw [h2]; rfl)
    intro x
    have hx : x ∈ Submodule.span F (Set.range ![(1 : E), δ]) := hsp ▸ Submodule.mem_top
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union,
      Submodule.mem_span_pair] at hx
    exact hx

def fstC {I : Type} (c : I → ℂ) : (I → ℂ) →+ (I → ℝ) where
  toFun z i := (z i).re - (z i).im / (c i).im * (c i).re
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp only [Pi.add_apply, Complex.add_re, Complex.add_im]; ring

def sndC {I : Type} (c : I → ℂ) : (I → ℂ) →+ (I → ℝ) where
  toFun z i := (z i).im / (c i).im
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp only [Pi.add_apply, Complex.add_im]; ring

theorem exists_chart_of_cm {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (tau : InfinitePlace F → (E →+* ℂ))
    (htau : ∀ w, plF (F := F) (tau w) = w) (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) (hθ : IsInfFamF tau θ) :
    ∃ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι := by
  haveI : IsTotallyReal F := h.1
  obtain ⟨δ, hδ, hsp⟩ := exists_gen h
  have hθ' : ∀ w (a : Ainf F) (x : E), θ w (a ⊗ₜ[F] x) = (rc w (a w) : ℝ) * tau w x := by
    intro w a x
    rw [isInfEmb_unique (tau w) (hθ w) (projAt_isInfEmb (tau w)), projAt_tmul, compF_eq _ w (htau w)]
  let c : InfinitePlace F → ℂ := fun w => tau w δ
  let ι : (InfinitePlace F → ℂ) →+ AEF F E :=
    (embA 1).comp (rho.comp (fstC c)) + (embA δ).comp (rho.comp (sndC c))
  have hι : ∀ z, ι z = embA 1 (rho (fstC c z)) + embA δ (rho (sndC c z)) := fun _ => rfl
  refine ⟨ι, ?_, fun z => ?_, fun z w => ?_, fun a hf hi => ?_⟩
  · have c2 : ∀ w, Continuous fun z : InfinitePlace F → ℂ => (z w).im / (c w).im := fun w =>
      (Complex.continuous_im.comp (continuous_apply w)).div_const _
    have c1 : Continuous (fstC c) :=
      continuous_pi fun w => (Complex.continuous_re.comp (continuous_apply w)).sub ((c2 w).mul continuous_const)
    have c3 : Continuous (sndC c) := continuous_pi c2
    exact ((continuous_embA _).comp (continuous_rho.comp c1)).add ((continuous_embA _).comp (continuous_rho.comp c3))
  · rw [hι, RingHom.map_add (f := _), finPart_embA, finPart_embA, add_zero]
  · rw [hι, RingHom.map_add (f := _), infPart_embA, infPart_embA, RingHom.map_add (f := _), hθ', hθ', rc_rho, rc_rho, map_one, mul_one]
    have h0 : (c w).im ≠ 0 := hδ _
    show (((z w).re - (z w).im / (c w).im * (c w).re : ℝ) : ℂ) + (((z w).im / (c w).im : ℝ) : ℂ) * c w = z w
    apply Complex.ext
    · rw [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]; ring
    · rw [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zero_add, div_mul_cancel₀ _ h0]
  · obtain ⟨b₀, b₁, hb⟩ := tensor_span δ hsp (infPartF F E a)
    have key : ∀ w, rc w (b₀ w) = 0 ∧ rc w (b₁ w) = 0 := by
      intro w
      have e := hi w
      rw [hb, RingHom.map_add (f := _), hθ', hθ', map_one, mul_one] at e
      have e1 := congrArg Complex.re e
      have e2 := congrArg Complex.im e
      rw [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zero_add, Complex.zero_im] at e2
      have e3 := (mul_eq_zero.1 e2).resolve_right (hδ _)
      rw [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, e3, zero_mul, add_zero, Complex.zero_re] at e1
      exact ⟨e1, e3⟩
    have z0 : b₀ = 0 := funext fun w => (rc w).map_eq_zero_iff.1 (key w).1
    have z1 : b₁ = 0 := funext fun w => (rc w).map_eq_zero_iff.1 (key w).2
    rw [z0, z1, TensorProduct.zero_tmul, TensorProduct.zero_tmul, add_zero] at hb
    have hp : pairE (infPartF F E a) (finPartF F E a) = a := pairE_eta a
    rw [← hp, hb, hf]
    simp [pairE]

theorem exists_chartF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∃ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι := by
  intro F E _ _ _ _ _ σ B hB θ hθ
  refine exists_chart_of_cm hB.cm (fun w => (B.emb w).1) (fun w => ?_) θ hθ
  show InfinitePlace.mk ((B.emb w).1.comp (algebraMap F E)) = w
  rw [(B.emb w).2, InfinitePlace.mk_embedding]

end GlobalTheory.RealWeilF.CMChart

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceFormOfTwistedNormCharpoly
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TwTraceForm

theorem phi_transpose (a : ℕ) (L : Type) [Field L] :
    (GlobalTheory.Tw.Phi a L)ᵀ = (-1 : L) ^ (a - 1) • GlobalTheory.Tw.Phi a L :=
  (GlobalTheory.antidiag_twisted_norm L (RingEquiv.refl L) (fun _ => rfl) a (GlobalTheory.Tw.Phi a L) (by
    ext i j
    simp only [GlobalTheory.Tw.Phi, Matrix.of_apply]
    have : ((i : ℕ) + (j : ℕ) + 1 = a) ↔ j = i.rev := by
      rw [Fin.ext_iff, Fin.val_rev]; omega
    simp only [this])).1

theorem phi_map (a : ℕ) (L : Type) [Field L] (c : L →+* L) :
    (GlobalTheory.Tw.Phi a L).map c = GlobalTheory.Tw.Phi a L := by
  ext i j
  simp only [GlobalTheory.Tw.Phi, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem phi_transpose_mul (a : ℕ) (L : Type) [Field L] :
    (GlobalTheory.Tw.Phi a L)ᵀ * GlobalTheory.Tw.Phi a L = 1 :=
  mul_eq_one_comm.1 (GlobalTheory.CuspRep.Phi_mul_transpose a L)

theorem gram_eq (a : ℕ) (L : Type) [Field L] (δ : GL (Fin a) L) :
    ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = ((δ⁻¹ : GL (Fin a) L).val)ᵀ * GlobalTheory.Tw.Phi a L := by
  have h : (δ.val * GlobalTheory.Tw.Phi a L)⁻¹ = (GlobalTheory.Tw.Phi a L)ᵀ * (δ⁻¹ : GL (Fin a) L).val := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (δ⁻¹ : GL (Fin a) L).val, Units.inv_mul, Matrix.one_mul,
      phi_transpose_mul]
  rw [h, Matrix.transpose_mul, Matrix.transpose_transpose]

theorem gram_mul_transpose (a : ℕ) (L : Type) [Field L] (δ : GL (Fin a) L) :
    ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ * (δ.val * GlobalTheory.Tw.Phi a L)ᵀ = 1 := by
  rw [gram_eq, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (GlobalTheory.Tw.Phi a L),
    GlobalTheory.CuspRep.Phi_mul_transpose, Matrix.one_mul, ← Matrix.transpose_mul, Units.mul_inv,
    Matrix.transpose_one]

theorem gram_norm (a : ℕ) (L : Type) [Field L] (c : L →+* L) (δ : GL (Fin a) L) :
    (((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ)ᵀ * (δ * thetaGL a c δ).val
      = (-1 : L) ^ (a - 1) • (((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ).map c := by
  have hθ : (thetaGL a c δ).val
      = GlobalTheory.Tw.Phi a L * (((δ⁻¹ : GL (Fin a) L).val).map c)ᵀ * (GlobalTheory.Tw.Phi a L)ᵀ := rfl
  rw [gram_eq, Units.val_mul, hθ, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.map_mul, Matrix.transpose_map, phi_map]
  set Φ := GlobalTheory.Tw.Phi a L
  set Di := (δ⁻¹ : GL (Fin a) L).val
  set X := (Di.map c)ᵀ
  calc Φᵀ * Di * (δ.val * (Φ * X * Φᵀ))
      = Φᵀ * (Di * δ.val) * Φ * X * Φᵀ := by
        simp only [Matrix.mul_assoc]
    _ = X * Φᵀ := by
        rw [Units.inv_mul, Matrix.mul_one, phi_transpose_mul, Matrix.one_mul]
    _ = (-1 : L) ^ (a - 1) • (X * Φ) := by
        rw [phi_transpose, Matrix.mul_smul]

theorem form_asym {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (σ : k ≃+* k)
    (hσ : ∀ x, σ (σ x) = x) (S N : Matrix n n k) (ε : k) (h : S.map σ = ε • (Sᵀ * N))
    (u v : n → k) :
    σ (v ⬝ᵥ S *ᵥ (fun j => σ (u j))) = (ε • N *ᵥ u) ⬝ᵥ S *ᵥ (fun j => σ (v j)) := by
  have h1 : σ (v ⬝ᵥ S *ᵥ (fun j => σ (u j))) = (fun j => σ (v j)) ⬝ᵥ S.map σ *ᵥ u := by
    rw [show σ (v ⬝ᵥ S *ᵥ (fun j => σ (u j))) = (σ : k →+* k) (v ⬝ᵥ S *ᵥ (fun j => σ (u j))) from rfl,
      RingHom.map_dotProduct]
    congr 1
    funext i
    rw [Function.comp_apply, RingHom.map_mulVec]
    congr 1
    funext j
    simp [hσ]
  rw [h1, h, Matrix.smul_mulVec, dotProduct_smul, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, smul_dotProduct, dotProduct_comm, smul_eq_mul]

end GlobalTheory.TwTraceForm

namespace GlobalTheory.TwTraceForm

theorem exists_trace_form : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L), (∀ x, e (K.c x) = c (e x)) → (∀ x, c (c x) = x) → B.g * B.σ B.g = 1 → ∀ (a : ℕ) (Q : L[X]), B.P = Q.map e.symm.toRingHom → Q.Separable → Q.natDegree = a → ∀ δ : GL (Fin a) L, (δ * thetaGL a c δ).val.charpoly = Q → ∃ β : B.Aˣ, B.σ (β : B.A) = β * ((-1) ^ (a - 1) * B.g) ∧ ∃ b : Module.Basis (Fin a) K.E B.A, ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = (Matrix.of fun i j => e (B.herm β (b i) (b j))) := by
  intro K B L _ e c hec hcc hg a Q hBP hQs hQd δ hδ
  classical
  let f : L →+* K.E := e.symm.toRingHom
  have hf : ∀ x, f (c x) = K.c (f x) := by
    intro x
    apply e.injective
    show e (e.symm (c x)) = e (K.c (e.symm x))
    rw [hec, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  set G := ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ with hG
  set N := (δ * thetaGL a c δ).val with hN
  set S := G.map f with hS
  set N' := N.map f with hN'
  set ε : K.E := (-1) ^ (a - 1) with hε
  have hεε : ε * ε = 1 := by rw [hε, ← mul_pow]; simp
  have hkey : Sᵀ * N' = ε • S.map K.c := by
    have h0 := congrArg f.mapMatrix (gram_norm a L c δ)
    rw [map_mul] at h0
    simp only [RingHom.mapMatrix_apply] at h0
    rw [Matrix.transpose_map] at h0
    change Sᵀ * N' = _ at h0
    rw [h0]
    ext i j
    simp [f, hf, hε, Matrix.map_apply, Matrix.smul_apply]
    exact hf _
  have hSc : S.map K.c = ε • (Sᵀ * N') := by rw [hkey, smul_smul, hεε, one_smul]
  set Y := ((δ.val * GlobalTheory.Tw.Phi a L)ᵀ).map f with hY
  have hSY : S * Y = 1 := by
    have h0 := congrArg f.mapMatrix (gram_mul_transpose a L δ)
    rw [map_mul, map_one] at h0
    exact h0
  have hsep : (LinearMap.mulLeft K.E B.g).charpoly.Separable := by
    show B.P.Separable
    rw [hBP]; exact hQs.map
  have hchar : (LinearMap.mulLeft K.E B.g).charpoly = (Matrix.toLin' N').charpoly := by
    rw [Matrix.charpoly_toLin', hN', Matrix.charpoly_map, hδ]
    exact hBP
  obtain ⟨ψ, hψ⟩ := GlobalTheory.UnitLemma.PairClass.exists_intertwine K.E B.A (Fin a → K.E)
    (LinearMap.mulLeft K.E B.g) (Matrix.toLin' N') hsep hchar
  have hψ' : ∀ y, ψ (B.g * y) = N' *ᵥ ψ y := fun y => by simpa using hψ y
  have hc1 : ∀ j : Fin a, (fun k => K.c ((Pi.single j (1 : K.E) : Fin a → K.E) k)) = (Pi.single j 1 : Fin a → K.E) := by
    intro j
    funext k
    by_cases h : k = j
    · subst h; simp
    · simp [h]
  let s : B.A → B.A → K.E := fun y z => ψ y ⬝ᵥ S *ᵥ (fun j => K.c (ψ z j))
  have hadd : ∀ x y z, s (x + y) z = s x z + s y z := by
    intro x y z
    simp only [s, map_add (f := _), add_dotProduct]
  have hlin : ∀ (r : K.E) x z, s (r • x) z = r * s x z := by
    intro r x z
    simp only [s, map_smul, smul_dotProduct, smul_eq_mul]
  have hnd : ∀ y, (∀ z, s y z = 0) → y = 0 := by
    intro y hy
    have hv : ψ y ᵥ* S = 0 := by
      funext j
      have h1 := hy (ψ.symm (Pi.single j 1))
      simp only [s, LinearEquiv.apply_symm_apply] at h1
      rw [hc1 j, Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at h1
      exact h1
    have h2 : ψ y = 0 := by
      rw [← Matrix.vecMul_one (ψ y), ← hSY, ← Matrix.vecMul_vecMul, hv, Matrix.zero_vecMul]
    exact ψ.injective (by rw [h2, map_zero])
  have hsym : ∀ y z, K.c (s z y) = s ((-1 : B.A) ^ (a - 1) * B.g * y) z := by
    intro y z
    have hψε : ψ ((-1 : B.A) ^ (a - 1) * B.g * y) = ε • N' *ᵥ ψ y := by
      have h1 : (-1 : B.A) ^ (a - 1) = algebraMap K.E B.A ε := by simp [hε]
      rw [h1, mul_assoc, ← Algebra.smul_def, map_smul, hψ']
    simp only [s]
    rw [hψε]
    exact form_asym K.c K.c_c S N' ε hSc (ψ y) (ψ z)
  obtain ⟨β, hβ, hs⟩ := (GlobalTheory.SesqAsym.sesq_asym K B hg hsep ((-1) ^ (a - 1))
    (neg_one_pow_eq_or B.A (a - 1))).2 s hadd hlin hnd hsym
  refine ⟨β, hβ, (Pi.basisFun K.E (Fin a)).map ψ.symm, ?_⟩
  ext i j
  simp only [Matrix.of_apply, Module.Basis.map_apply, Pi.basisFun_apply]
  rw [← hs]
  simp only [s, LinearEquiv.apply_symm_apply]
  rw [hc1 j, Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply, hS, Matrix.map_apply]
  exact (e.apply_symm_apply _).symm

end GlobalTheory.TwTraceForm
end

