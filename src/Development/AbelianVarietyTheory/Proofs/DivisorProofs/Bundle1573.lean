module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1560
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1546
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfSchroedingerTranslatesThetaSumZero
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

open scoped Classical

namespace GlobalTheory.ThetaInj

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ,
    (∀ w : (κ → AF F) × (κ → AF F), thetaSum F (schr ψ w Φ) = 0) → Φ = 0 := by
  intro F _ _ ψ hψ κ _ Φ hΦ h
  have hn : ∀ a, ‖ψ a‖ = 1 := GlobalTheory.StdCharFromIsStd.norm_psi hψ
  obtain ⟨a₀, ha₀⟩ := GlobalTheory.StdCharFromIsStd.exists_ne_one hψ
  let ι : (κ → F) → (κ → AF F) := fun ξ i => algebraMap F (AF F) (ξ i)
  have hι0 : ι 0 = 0 := by funext i; simp [ι]
  funext x
  have hΦx : (fun z => Φ (z + x)) ∈ schA F κ := GlobalTheory.SchwartzTranslate.schA_translate F x hΦ
  have hc : Summable fun ξ => ‖Φ (ι ξ + x)‖ := by
    convert GlobalTheory.WeilM.summable_norm_of_mem_schA F hΦx using 1
  have key := GlobalTheory.SchrodingerUniq.coeff_zero_eq_zero
    (χ := fun (y : κ → AF F) (ξ : κ → F) => ψ (ι ξ ⬝ᵥ y))
    (c := fun ξ => Φ (ι ξ + x)) (fun y ξ => hn _)
    (fun y y' ξ => by simp only [dotProduct_add, AddChar.map_add_eq_mul])
    (fun ξ => by simp only [dotProduct_zero, AddChar.map_zero_eq_one])
    (fun y => by simp only [hι0, zero_dotProduct, AddChar.map_zero_eq_one])
    (fun ξ hξ => by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hξ
      have hi' : ξ i ≠ 0 := hi
      refine ⟨Pi.single i (algebraMap F (AF F) (ξ i)⁻¹ * a₀), ?_⟩
      show ψ (ι ξ ⬝ᵥ Pi.single i (algebraMap F (AF F) (ξ i)⁻¹ * a₀)) ≠ 1
      rw [dotProduct_single]
      show ψ (algebraMap F (AF F) (ξ i) * (algebraMap F (AF F) (ξ i)⁻¹ * a₀)) ≠ 1
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi', map_one, one_mul]
      exact ha₀)
    hc (fun y => ?_)
  · simpa [hι0] using key
  · have h' := h (x, y)
    simp only [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr, AddChar.map_add_eq_mul] at h'
    set b := ψ (⅟(2 : AF F) * (x ⬝ᵥ y))
    have hb : b ≠ 0 := by
      intro e
      have h1 : ‖b‖ = 1 := hn _
      rw [e, norm_zero] at h1
      exact zero_ne_one h1
    have e2 : ∑' ξ : κ → F, Φ (ι ξ + x) * ψ (ι ξ ⬝ᵥ y) =
        b⁻¹ * ∑' ξ : κ → F, ψ (ι ξ ⬝ᵥ y) * b * Φ (ι ξ + x) := by
      rw [← tsum_mul_left]; congr 1; funext ξ; field_simp
    rw [e2, h', mul_zero]

end GlobalTheory.ThetaInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationGoodModelsIntertwine
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv

noncomputable section

namespace GlobalTheory.EvTame

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

def HasTameExp {κ κ' : Type} [Fintype κ] [Fintype κ'] (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ))
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι)
    (P : ι → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ' → mixedEmbedding.mixedSpace F) ℂ)
    (g' : ι → (κ' → FiniteAdeleRing (𝓞 F) F) → ℂ), (∀ j, g' j ∈ SB (κ' → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, T (pureA F f g) = ∑ j, pureA F (P j f) (g' j)

theorem pureA_zero {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) :
    pureA F f (0 : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) = 0 := by
  funext x; simp [pureA]

theorem pureA_add {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g₁ g₂ : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    pureA F f (g₁ + g₂) = pureA F f g₁ + pureA F f g₂ := by
  funext x; simp [pureA, mul_add]

theorem pureA_smul {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (c : ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) : pureA F f (c • g) = c • pureA F f g := by
  funext x; simp only [pureA, Pi.smul_apply, smul_eq_mul]; ring

theorem hasTameExp_zero {κ κ' : Type} [Fintype κ] [Fintype κ'] (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) :
    HasTameExp T 0 :=
  ⟨Empty, inferInstance, fun j => j.elim, fun j => j.elim, fun j => j.elim, fun f => by
    letI : IsEmpty Empty := Empty.instIsEmpty
    rw [pureA_zero, map_zero]; simp⟩

theorem HasTameExp.add {κ κ' : Type} [Fintype κ] [Fintype κ'] {T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    {g₁ g₂ : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (h₁ : HasTameExp T g₁) (h₂ : HasTameExp T g₂) :
    HasTameExp T (g₁ + g₂) := by
  obtain ⟨ι₁, _, P₁, k₁, hk₁, e₁⟩ := h₁
  obtain ⟨ι₂, _, P₂, k₂, hk₂, e₂⟩ := h₂
  refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim P₁ P₂, Sum.elim k₁ k₂, ?_, fun f => ?_⟩
  · rintro (j | j)
    · exact hk₁ j
    · exact hk₂ j
  · rw [pureA_add, map_add (f := _), e₁, e₂, Fintype.sum_sum_type]
    rfl

theorem HasTameExp.smul {κ κ' : Type} [Fintype κ] [Fintype κ'] {T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (c : ℂ) (h : HasTameExp T g) : HasTameExp T (c • g) := by
  obtain ⟨ι, _, P, k, hk, e⟩ := h
  refine ⟨ι, inferInstance, P, fun j => c • k j, fun j => Submodule.smul_mem _ c (hk j), fun f => ?_⟩
  rw [pureA_smul, map_smul, e, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => (pureA_smul _ c _).symm

theorem pure_eq_pureA {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) :
    pure f φ = pureA F f (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => evalV F v (y i)) := rfl

end GlobalTheory.EvTame

namespace GlobalTheory.EvTame

open scoped Classical

theorem isTame_of_isEv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E)
    (I : Set (Matrix (Fin n) (Fin d) (AE F E))) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁),
    M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e → IsTame F e := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I e hM hM₁ hE g hg
  obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
  have hs := GlobalTheory.SBSpan.mem_span_restrictedProd F (Fin n × Fin d) g hg
  clear hg
  change HasTameExp e g
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, hφ, hcof, rfl⟩ := hx
    have hvac : ∀ᶠ v in cofinite, φ v = M.vac v := by
      filter_upwards [hcof, hM.std] with v h1 h2
      rw [h1, h2]
    have hSB : ∀ v, ev v (φ v) ∈ SB (Fin n₁ × Fin d₁ → Fv F v) := fun v =>
      (hev v).2 ▸ Submodule.mem_map_of_mem (hφ v)
    have hcof' : ∀ᶠ v in cofinite,
        ev v (φ v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
      filter_upwards [hvac, hM₁.std] with v h1 h2
      rw [h1, (hev v).1, h2]
    refine ⟨Unit, inferInstance, fun _ => ei,
      fun _ y => ∏ᶠ v, ev v (φ v) fun i => evalV F v (y i),
      fun _ => GlobalTheory.AdelicCoordSB.finprod_mem_SB F _ (fun v => ev v (φ v)) hSB hcof', fun f => ?_⟩
    rw [← pure_eq_pureA, hloc f φ hφ hvac, pure_eq_pureA, Fintype.sum_unique]
  | zero => exact hasTameExp_zero e
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

end GlobalTheory.EvTame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.StdVacuum

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F : Type} [Field F] [NumberField F]

theorem indicator_mem_SB {κ : Type} [Fintype κ] (v : HeightOneSpectrum (𝓞 F)) :
    Set.indicator {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} 1 ∈ GlobalTheory.WeilM.SB (κ → Fv F v) := by
  have hU : {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} =
      Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext x; simp
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_integer _
  have hC : IsClosed (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isClosed_integer _
  have hK : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v
  rw [hU]
  have hUo : IsOpen (Set.pi Set.univ (fun _ : κ => (v.adicCompletionIntegers F : Set (Fv F v)))) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => hO)
  have hUc : IsClosed (Set.pi Set.univ (fun _ : κ => (v.adicCompletionIntegers F : Set (Fv F v)))) :=
    isClosed_set_pi (fun _ _ => hC)
  have hUk : IsCompact (Set.pi Set.univ (fun _ : κ => (v.adicCompletionIntegers F : Set (Fv F v)))) :=
    isCompact_univ_pi (fun _ => hK)
  generalize Set.pi Set.univ (fun _ : κ => (v.adicCompletionIntegers F : Set (Fv F v))) = U at hUo hUc hUk ⊢
  refine ⟨IsLocallyConstant.iff_isOpen_fiber.2 fun y => ?_, ?_⟩
  · by_cases h1 : (1 : ℂ) = y
    · have : U.indicator 1 ⁻¹' {y} = U := by
        ext x
        by_cases hx : x ∈ U <;> simp [hx, ← h1]
      rw [this]; exact hUo
    · by_cases h0 : (0 : ℂ) = y
      · have : U.indicator 1 ⁻¹' {y} = Uᶜ := by
          ext x
          by_cases hx : x ∈ U <;> simp [hx, ← h0]
        rw [this]; exact hUc.isOpen_compl
      · have : U.indicator 1 ⁻¹' {y} = ∅ := by
          ext x
          by_cases hx : x ∈ U <;> simp [hx] <;> assumption
        rw [this]; exact isOpen_empty
  · exact hUk.of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal Set.support_indicator_subset hUc)

end GlobalTheory.StdVacuum

open GlobalTheory.AdelicU GlobalTheory.WeilM

namespace GlobalTheory.StdVacuum

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem psi_eq_psiLoc (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (a : AF F) (h : At (evFin F v) a) :
    ψ a = psiLoc ψ v (evFin F v a) := by
  have h1 := h (1 - GlobalTheory.EmbChart.atPlace v 1) (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h1
  have h3 : a = GlobalTheory.EmbChart.atPlace v (evFin F v a) := by
    conv_lhs => rw [h1]
    rw [GlobalTheory.EmbChart.atPlace_mul_right, one_mul]
  conv_lhs => rw [h3]
  rfl

theorem acts_indicator {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (hψ : ∀ x ∈ v.adicCompletionIntegers F, psiLoc ψ v x = 1)
    (h2 : algebraMap F (Fv F v) 2⁻¹ ∈ v.adicCompletionIntegers F)
    (w : (κ → AF F) × (κ → AF F))
    (hw : ∀ k, At (evFin F v) (w.1 k) ∧ evFin F v (w.1 k) ∈ v.adicCompletionIntegers F ∧
      At (evFin F v) (w.2 k) ∧ evFin F v (w.2 k) ∈ v.adicCompletionIntegers F)
    (c : AF F) (hc : At (evFin F v) c ∧ evFin F v c ∈ v.adicCompletionIntegers F) :
    Acts (evFin F v) (schr ψ w) (Set.indicator {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} 1)
      (ψ (⅟(2 : AF F) * c) • Set.indicator {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} 1) := by
  have hAt : ∀ {z : AF F}, At (evFin F v) z → ∀ y : AF F, At (evFin F v) (y * z) := fun hz y u hu => by
    have := hz u hu
    rw [smul_eq_mul] at this ⊢
    rw [mul_left_comm, this, mul_zero]
  have hAtAdd : ∀ {z z' : AF F}, At (evFin F v) z → At (evFin F v) z' → At (evFin F v) (z + z') :=
    fun hz hz' u hu => by rw [smul_add, hz u hu, hz' u hu, add_zero]
  have hAtSum : ∀ f : κ → AF F, (∀ i, At (evFin F v) (f i)) → At (evFin F v) (∑ i, f i) :=
    fun f hf u hu => by rw [Finset.smul_sum]; exact Finset.sum_eq_zero fun i _ => hf i u hu
  have h2' : evFin F v (⅟(2 : AF F)) = algebraMap F (Fv F v) 2⁻¹ := by
    show evFin F v (algebraMap F (AF F) 2⁻¹) = _
    exact AlgHom.commutes _ _
  have hpsi1 : ∀ z : AF F, At (evFin F v) z → evFin F v z ∈ v.adicCompletionIntegers F → ψ z = 1 :=
    fun z hz hz' => by rw [psi_eq_psiLoc ψ v z hz]; exact hψ _ hz'
  have hcψ : ψ (⅟(2 : AF F) * c) = 1 :=
    hpsi1 _ (hAt hc.1 _) (by rw [map_mul, h2']; exact mul_mem h2 hc.2)
  have hw1 : At (evFin F v) w.1 := fun u hu => funext fun k => by
    have := (hw k).1 u hu
    simpa using this
  intro r hr
  rw [hcψ, one_smul]
  funext x
  simp only [tens, schr]
  rw [hr.1 x w.1 hw1]
  by_cases hx : ∀ k, evFin F v (x k) ∈ v.adicCompletionIntegers F
  · have hx' : (fun i => evFin F v ((x + w.1) i)) ∈ {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} :=
      fun k => by simp only [Pi.add_apply, map_add (f := _)]; exact add_mem (hx k) (hw k).2.1
    rw [Set.indicator_of_mem hx', Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈
      {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} from hx)]
    have hA : At (evFin F v) (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) :=
      hAtAdd (hAtSum _ fun i => hAt (hw i).2.2.1 _) (hAt (hAtSum _ fun i => hAt (hw i).2.2.1 _) _)
    have hI : evFin F v (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) ∈ v.adicCompletionIntegers F := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, map_add (f := _), map_mul, map_sum, h2']
      exact add_mem (sum_mem fun i _ => mul_mem (hx i) (hw i).2.2.2)
        (mul_mem h2 (sum_mem fun i _ => mul_mem (hw i).2.1 (hw i).2.2.2))
    rw [hpsi1 _ hA hI, one_mul]
    simp
  · have hx' : (fun i => evFin F v ((x + w.1) i)) ∉ {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} := by
      intro h
      apply hx
      intro k
      have := sub_mem (h k) (hw k).2.1
      simpa using this
    rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem (show (fun i => evFin F v (x i)) ∉
      {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} from hx)]
    simp

end GlobalTheory.StdVacuum

namespace GlobalTheory.StdVacuum

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isVac_of_good {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {Y : Spc F E d} (M : Model σ X Y)
    (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (θ : 𝓞 E) (hθ : (θ : E) + σ θ = 1)
    (T₀ : Set (Matrix (Fin n) (Fin d) E)) (yf zf : Matrix (Fin n) (Fin d) E → Fin n × Fin d → F)
    (hyz : ∀ x, M.co.e (incM F x) = (fun k => algebraMap F (AF F) (yf x k), fun k => algebraMap F (AF F) (zf x k)))
    (hgen : latAtV X Y v ≤ AddSubgroup.closure {z | ∃ a : AF F, At (evFin F v) a ∧
      evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ t ∈ T₀, z = a • incM F t})
    (hψ : ∀ x ∈ v.adicCompletionIntegers F, psiLoc ψ v x = 1)
    (h2 : algebraMap F (Fv F v) 2⁻¹ ∈ v.adicCompletionIntegers F)
    (hc : ∀ t ∈ T₀, ∀ k, algebraMap F (Fv F v) (yf t k) ∈ v.adicCompletionIntegers F ∧
      algebraMap F (Fv F v) (zf t k) ∈ v.adicCompletionIntegers F)
    (hs : ∀ t ∈ T₀, ∀ t' ∈ T₀, algebraMap F (Fv F v) (symp σ (θ : E) X.J Y.J t t') ∈ v.adicCompletionIntegers F) :
    M.IsVac ψ v (Set.indicator {x : Fin n × Fin d → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} 1) := by
  refine ⟨indicator_mem_SB v, fun h => ?_, θ, hθ, fun γ hγ => ?_⟩
  · have := congrFun h 0
    simp [Set.indicator, zero_mem] at this
  · obtain ⟨h1, h3⟩ := GlobalTheory.T.coords_and_symplectic_integral_on_placeLattice σ X.J Y.J (θ : E) v M.co.e.toLinearMap T₀ yf zf hyz hc hs γ (hgen hγ)
    exact acts_indicator ψ v hψ h2 (M.co.e γ) h1 _ h3

end GlobalTheory.StdVacuum

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in
theorem GlobalTheory.StdVacuum.eventually_isVac_indicator : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∀ M : Model σ X Y, (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        M.co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) →
      ∀ᶠ v in Filter.cofinite, M.IsVac B.ψ v (Set.indicator {x : Fin n × Fin d → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} 1) := by
  intro F E _ _ _ _ _ σ B n d X Y r s r' s' hB hX hY M hrat
  classical
  obtain ⟨θ, hθ⟩ := GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hB.cm
    (by haveI := hB.unram; infer_instance)
  choose yf zf hyz using hrat
  obtain ⟨sX, hsX⟩ := hX.lat.fg.restrictScalars (R := ℤ)
  obtain ⟨sY, hsY⟩ := hY.lat.fg.restrictScalars (R := ℤ)
  let f : (Fin n → E) →ₗ[ℤ] (Fin d → E) →ₗ[ℤ] Matrix (Fin n) (Fin d) E :=
    LinearMap.mk₂ ℤ (fun x y => Matrix.vecMulVec x y)
      (fun x x' y => by ext i j; simp [Matrix.vecMulVec_apply, add_mul])
      (fun c x y => by ext i j; simp [Matrix.vecMulVec_apply, mul_assoc])
      (fun x y y' => by ext i j; simp [Matrix.vecMulVec_apply, mul_add])
      (fun c x y => by ext i j; simp [Matrix.vecMulVec_apply, mul_left_comm])
  set T₀ : Set (Matrix (Fin n) (Fin d) E) := Set.image2 (fun x y => f x y) (sX : Set _) (sY : Set _) with hT₀def
  have hT₀ : T₀.Finite := sX.finite_toSet.image2 _ sY.finite_toSet
  have hmem : ∀ x ∈ X.L, ∀ y ∈ Y.L, Matrix.vecMulVec x y ∈ Submodule.span ℤ T₀ := by
    intro x hx y hy
    have hx' : x ∈ Submodule.span ℤ (sX : Set (Fin n → E)) := by
      rw [hsX]; exact hx
    have hy' : y ∈ Submodule.span ℤ (sY : Set (Fin d → E)) := by
      rw [hsY]; exact hy
    have := Submodule.apply_mem_map₂ f hx' hy'
    rwa [Submodule.map₂_span_span] at this
  have hgen : ∀ v : HeightOneSpectrum (𝓞 F), latAtV X Y v ≤ AddSubgroup.closure {z | ∃ a : AF F,
      At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ t ∈ T₀, z = a • incM F t} := by
    intro v
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, hav, x, hx, y, hy, rfl⟩
    let g : Matrix (Fin n) (Fin d) E →+ Matrix (Fin n) (Fin d) (AE F E) :=
      (DistribSMul.toAddMonoidHom _ a).comp
        (AddMonoidHom.mapMatrix (inclR (F := F) (E := E) (AF F)).toAddMonoidHom)
    have h1 : Matrix.vecMulVec x y ∈ AddSubgroup.closure T₀ := by
      rw [← Submodule.span_int_eq_addSubgroupClosure]; exact hmem x hx y hy
    have h2 : g (Matrix.vecMulVec x y) ∈ (AddSubgroup.closure T₀).map g := AddSubgroup.mem_map_of_mem g h1
    rw [AddMonoidHom.map_closure] at h2
    refine AddSubgroup.closure_mono ?_ h2
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨a, ha, hav, t, ht, rfl⟩
  have hV : ∀ᶠ v in Filter.cofinite, (∀ x ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F, psiLoc B.ψ v x = 1) ∧
      algebraMap F (Fv F v) 2⁻¹ ∈ v.adicCompletionIntegers F ∧
      (∀ t ∈ T₀, ∀ k, algebraMap F (Fv F v) (yf t k) ∈ v.adicCompletionIntegers F ∧
        algebraMap F (Fv F v) (zf t k) ∈ v.adicCompletionIntegers F) ∧
      ∀ t ∈ T₀, ∀ t' ∈ T₀, algebraMap F (Fv F v) (symp σ (θ : E) X.J Y.J t t') ∈ v.adicCompletionIntegers F := by
    have hint : ∀ a : F, ∀ᶠ v in Filter.cofinite,
        algebraMap F (Fv F v) a ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F :=
      fun a => (algebraMap F (FiniteAdeleRing (𝓞 F) F) a).2
    refine (GlobalTheory.T.localAddCharComponent_trivial_integers_eventually B.ψ hB.std.1).and ((hint _).and (((Filter.eventually_all_finite hT₀).2
      fun t _ => Filter.eventually_all.2 fun k => (hint _).and (hint _)).and ?_))
    exact (Filter.eventually_all_finite hT₀).2 fun t _ => (Filter.eventually_all_finite hT₀).2 fun t' _ => hint _
  filter_upwards [hV] with v hv
  exact GlobalTheory.StdVacuum.isVac_of_good M B.ψ v θ hθ T₀ yf zf hyz (hgen v) hv.1 hv.2.1 hv.2.2.1 hv.2.2.2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanSchwartzTraceFourierBijective
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

namespace GlobalTheory.ArchFourier

open scoped FourierTransform SchwartzMap

theorem exists_schwartz_fourier_form {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hs : ∀ x y, B x y = B y x)
    (hn : ∀ x, (∀ y, B x y = 0) → x = 0) (μ : Measure V) [μ.IsAddHaarMeasure] :
    ∃ ei : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ), Function.Bijective ei ∧ ∀ (f : 𝓢(V, ℂ)) (y : V),
      ei f y = ∫ x, f x * Complex.exp (-(2 * Real.pi * Complex.I) * (B x y : ℂ)) ∂μ := by
  let T := toEuclidean (E := V)
  obtain ⟨R, hR⟩ := GlobalTheory.exists_equiv_inner_eq_form T B hs hn
  obtain ⟨a, ha, haI, -⟩ := GlobalTheory.exists_pos_integral_comp_equiv_haar T μ
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  let CR := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) R
  let CT := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) T.symm
  let CRi := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) R.symm
  let CTi := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) T
  let Fo := SchwartzMap.fourierTransformCLM ℂ (V := EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) (E := ℂ)
  have h1 : ∀ g, CRi (CR g) = g := fun g => by ext x; simp [CRi, CR]
  have h2 : ∀ g, CR (CRi g) = g := fun g => by ext x; simp [CRi, CR]
  have h3 : ∀ g, CTi (CT g) = g := fun g => by ext x; simp [CTi, CT]
  have h4 : ∀ g, CT (CTi g) = g := fun g => by ext x; simp [CTi, CT]
  have h5 : ∀ g, 𝓕⁻ (Fo g) = g := fun g => by
    simp only [Fo, SchwartzMap.fourierTransformCLM_apply]; exact FourierTransform.fourierInv_fourier_eq g
  have h6 : ∀ g, Fo (𝓕⁻ g) = g := fun g => by
    simp only [Fo, SchwartzMap.fourierTransformCLM_apply]; exact FourierTransform.fourier_fourierInv_eq g
  refine ⟨(a : ℂ) • (CR.comp (Fo.comp CT)), ?_, fun f y => ?_⟩
  · rw [Function.bijective_iff_has_inverse]
    refine ⟨fun g => (a : ℂ)⁻¹ • CTi (𝓕⁻ (CRi g)), fun f => ?_, fun g => ?_⟩
    · simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_smul, h1, h5, h3,
        FourierTransform.fourierInv_smul, smul_smul, inv_mul_cancel₀ ha', one_smul]
    · change (a : ℂ) • CR (Fo (CT ((a : ℂ)⁻¹ • CTi (𝓕⁻ (CRi g))))) = g
      rw [map_smul, map_smul, map_smul, h4, h6, h2, smul_smul, mul_inv_cancel₀ ha', one_smul]
  · have e1 : ((a : ℂ) • (CR.comp (Fo.comp CT))) f y = (a : ℂ) * 𝓕 (fun w => f (T.symm w)) (R y) := rfl
    rw [e1, Real.fourier_eq', ← haI]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ContinuousLinearEquiv.symm_apply_apply, smul_eq_mul, hR]
    rw [mul_comm]
    congr 2
    push_cast
    ring

end GlobalTheory.ArchFourier

namespace GlobalTheory.ArchFourier

noncomputable def traceDot (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y))
    (fun x x' y => by simp only [add_dotProduct, map_add (f := _)])
    (fun c x y => by simp only [smul_dotProduct, map_smul, smul_eq_mul])
    (fun x y y' => by simp only [dotProduct_add, map_add (f := _)])
    (fun c x y => by simp only [dotProduct_smul, map_smul, smul_eq_mul])

theorem traceDot_apply {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x y : κ → mixedEmbedding.mixedSpace F) :
    traceDot F κ x y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y) := rfl

theorem traceDot_comm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x y : κ → mixedEmbedding.mixedSpace F) : traceDot F κ x y = traceDot F κ y x := by
  rw [traceDot_apply, traceDot_apply, dotProduct_comm]

theorem traceDot_nondeg {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x : κ → mixedEmbedding.mixedSpace F) (hx : ∀ y, traceDot F κ x y = 0) : x = 0 := by
  classical
  funext i
  refine GlobalTheory.ArchUniq.Coord.eq_zero_of_trace _ fun b => ?_
  have := hx (Pi.single i b)
  rwa [traceDot_apply, dotProduct_single] at this

theorem exists_fourier_sInf : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → mixedEmbedding.mixedSpace F)]
    [BorelSpace (κ → mixedEmbedding.mixedSpace F)] (μ : Measure (κ → mixedEmbedding.mixedSpace F)) [μ.IsAddHaarMeasure],
    ∃ ei : SInf F κ →L[ℂ] SInf F κ, Function.Bijective ei ∧ ∀ (f : SInf F κ) (y : κ → mixedEmbedding.mixedSpace F),
      ei f y = ∫ x, f x * Complex.exp (-(2 * Real.pi * Complex.I) *
        (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y) : ℝ)) ∂μ := by
  intro F _ _ κ _ _ _ μ _
  classical
  exact exists_schwartz_fourier_form (traceDot F κ) traceDot_comm traceDot_nondeg μ

end GlobalTheory.ArchFourier
end

