module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0871
public import GroundTheory.Brauer.IsBrauerEquivalentIffNonemptyAlgEquiv
public import GroundTheory.Brauer.BaseChangeCSA
public import GroundTheory.Brauer.DoubleCentralizer
public import GroundTheory.Brauer.Degree
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0895
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0893
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace GlobalTheory.SchwartzBox

theorem norm_le_max_comp {V : Type} [NormedAddCommGroup V] {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ ⊕ κ' → V) :
    ‖x‖ ≤ max ‖x ∘ Sum.inl‖ ‖x ∘ Sum.inr‖ := by
  refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).2 fun j => ?_
  cases j with
  | inl i => exact le_max_of_le_left (norm_le_pi_norm (x ∘ Sum.inl) i)
  | inr i => exact le_max_of_le_right (norm_le_pi_norm (x ∘ Sum.inr) i)

def restr (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] {ι κ : Type} [Fintype ι] [Fintype κ] (e : κ → ι) :
    (ι → V) →L[ℝ] (κ → V) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => V) (e i)

theorem restr_apply (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : κ → ι) (x : ι → V) : restr V e x = x ∘ e := rfl

theorem norm_restr_le (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : κ → ι) : ‖restr V e‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun i => norm_le_pi_norm x (e i)

theorem norm_iteratedFDeriv_restr_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {ι κ : Type} [Fintype ι]
    [Fintype κ] (e : κ → ι) (f : SchwartzMap (κ → V) ℂ) (i : ℕ) (x : ι → V) :
    ‖iteratedFDeriv ℝ i (fun y => f (y ∘ e)) x‖ ≤ ‖iteratedFDeriv ℝ i f (x ∘ e)‖ := by
  have h := ContinuousLinearMap.iteratedFDeriv_comp_right (restr V e) (f.smooth ⊤) x (i := i) (by exact_mod_cast le_top)
  have h' : (fun y => f (y ∘ e)) = (f ∘ restr V e) := rfl
  rw [h', h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  calc ‖iteratedFDeriv ℝ i f (restr V e x)‖ * ∏ _j : Fin i, ‖restr V e‖
      ≤ ‖iteratedFDeriv ℝ i f (restr V e x)‖ * 1 := by
        gcongr
        exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => norm_restr_le V e
    _ = _ := mul_one _

theorem exists_schwartz_box {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {κ κ' : Type} [Fintype κ]
    [Fintype κ'] (f₁ : SchwartzMap (κ → V) ℂ) (f₂ : SchwartzMap (κ' → V) ℂ) :
    ∃ f : SchwartzMap (κ ⊕ κ' → V) ℂ, ∀ x, f x = f₁ (x ∘ Sum.inl) * f₂ (x ∘ Sum.inr) := by
  have hs₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : κ ⊕ κ' → V => f₁ (y ∘ Sum.inl)) :=
    (f₁.smooth ⊤).comp (restr V (Sum.inl : κ → κ ⊕ κ')).contDiff
  have hs₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : κ ⊕ κ' → V => f₂ (y ∘ Sum.inr)) :=
    (f₂.smooth ⊤).comp (restr V (Sum.inr : κ' → κ ⊕ κ')).contDiff
  refine ⟨⟨fun x => f₁ (x ∘ Sum.inl) * f₂ (x ∘ Sum.inr), hs₁.mul hs₂, fun k n => ?_⟩, fun _ => rfl⟩
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
    (SchwartzMap.seminorm ℝ k i f₁ * SchwartzMap.seminorm ℝ 0 (n - i) f₂ +
      SchwartzMap.seminorm ℝ 0 i f₁ * SchwartzMap.seminorm ℝ k (n - i) f₂), fun x => ?_⟩
  have hx : ‖x‖ ^ k ≤ ‖x ∘ Sum.inl‖ ^ k + ‖x ∘ Sum.inr‖ ^ k := by
    have h0 : ‖x‖ ^ k ≤ (max ‖x ∘ Sum.inl‖ ‖x ∘ Sum.inr‖) ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_le_max_comp x) k
    refine h0.trans ?_
    have p1 := pow_nonneg (norm_nonneg (x ∘ Sum.inl)) k
    have p2 := pow_nonneg (norm_nonneg (x ∘ Sum.inr)) k
    rcases le_total ‖x ∘ Sum.inl‖ ‖x ∘ Sum.inr‖ with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hL := norm_iteratedFDeriv_mul_le hs₁ hs₂ x (n := n) (by exact_mod_cast le_top)
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => f₁ (y ∘ Sum.inl) * f₂ (y ∘ Sum.inr)) x‖
      ≤ (‖x ∘ Sum.inl‖ ^ k + ‖x ∘ Sum.inr‖ ^ k) * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f₁ (x ∘ Sum.inl)‖ * ‖iteratedFDeriv ℝ (n - i) f₂ (x ∘ Sum.inr)‖ := by
        refine mul_le_mul hx (hL.trans ?_) (norm_nonneg _) (by positivity)
        refine Finset.sum_le_sum fun i _ => ?_
        gcongr
        · exact norm_iteratedFDeriv_restr_le Sum.inl f₁ i x
        · exact norm_iteratedFDeriv_restr_le Sum.inr f₂ (n - i) x
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ((‖x ∘ Sum.inl‖ ^ k * ‖iteratedFDeriv ℝ i f₁ (x ∘ Sum.inl)‖) *
              ‖iteratedFDeriv ℝ (n - i) f₂ (x ∘ Sum.inr)‖ +
           ‖iteratedFDeriv ℝ i f₁ (x ∘ Sum.inl)‖ *
              (‖x ∘ Sum.inr‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f₂ (x ∘ Sum.inr)‖)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ _ := by
        refine Finset.sum_le_sum fun i _ => ?_
        gcongr
        · exact SchwartzMap.le_seminorm ℝ k i f₁ _
        · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ f₂ _ _
        · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ f₁ _ _
        · exact SchwartzMap.le_seminorm ℝ k (n - i) f₂ _

theorem sb_box {X : Type} [TopologicalSpace X] {κ κ' : Type} {g₁ : (κ → X) → ℂ} {g₂ : (κ' → X) → ℂ}
    (hg₁ : g₁ ∈ SB (κ → X)) (hg₂ : g₂ ∈ SB (κ' → X)) :
    (fun z : κ ⊕ κ' → X => g₁ (z ∘ Sum.inl) * g₂ (z ∘ Sum.inr)) ∈ SB (κ ⊕ κ' → X) := by
  obtain ⟨hl₁, hc₁⟩ := hg₁
  obtain ⟨hl₂, hc₂⟩ := hg₂
  let e : (κ ⊕ κ' → X) ≃ₜ (κ → X) × (κ' → X) := Homeomorph.sumArrowHomeomorphProdArrow
  have he : ∀ z, e z = (z ∘ Sum.inl, z ∘ Sum.inr) := fun _ => rfl
  refine ⟨?_, ?_⟩
  · have c₁ : Continuous fun z : κ ⊕ κ' → X => z ∘ Sum.inl := continuous_pi fun i => continuous_apply _
    have c₂ : Continuous fun z : κ ⊕ κ' → X => z ∘ Sum.inr := continuous_pi fun i => continuous_apply _
    exact (hl₁.comp_continuous c₁).mul (hl₂.comp_continuous c₂)
  · refine HasCompactSupport.intro' (K := e ⁻¹' (tsupport g₁ ×ˢ tsupport g₂))
      (e.isCompact_preimage.2 (hc₁.prod hc₂))
      (((isClosed_tsupport _).prod (isClosed_tsupport _)).preimage e.continuous) fun z hz => ?_
    rw [Set.mem_preimage, he, Set.mem_prod, not_and_or] at hz
    rcases hz with h | h
    · simp [image_eq_zero_of_notMem_tsupport h]
    · simp [image_eq_zero_of_notMem_tsupport h]

theorem boxFun_zero_left {R κ κ' : Type} (φ : (κ' → R) → ℂ) : boxFun (0 : (κ → R) → ℂ) φ = 0 := by
  funext x; simp [boxFun]

theorem boxFun_add_left {R κ κ' : Type} (a b : (κ → R) → ℂ) (φ : (κ' → R) → ℂ) :
    boxFun (a + b) φ = boxFun a φ + boxFun b φ := by
  funext x; simp [boxFun, add_mul]

theorem boxFun_smul_left {R κ κ' : Type} (c : ℂ) (a : (κ → R) → ℂ) (φ : (κ' → R) → ℂ) :
    boxFun (c • a) φ = c • boxFun a φ := by
  funext x; simp [boxFun, mul_assoc]

theorem boxFun_zero_right {R κ κ' : Type} (φ : (κ → R) → ℂ) : boxFun φ (0 : (κ' → R) → ℂ) = 0 := by
  funext x; simp [boxFun]

theorem boxFun_add_right {R κ κ' : Type} (φ : (κ → R) → ℂ) (a b : (κ' → R) → ℂ) :
    boxFun φ (a + b) = boxFun φ a + boxFun φ b := by
  funext x; simp [boxFun, mul_add]

theorem boxFun_smul_right {R κ κ' : Type} (c : ℂ) (φ : (κ → R) → ℂ) (a : (κ' → R) → ℂ) :
    boxFun φ (c • a) = c • boxFun φ a := by
  funext x; simp [boxFun]; ring


open scoped Classical in
theorem boxFun_mem_schA (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ'] :
    ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ', boxFun φ₁ φ₂ ∈ schA F (κ ⊕ κ') := by
  intro φ₁ h₁ φ₂ h₂
  have gen : ∀ Φ₁ ∈ {Φ | ∃ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
        (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) ∧ Φ = pureA F f g},
      ∀ Φ₂ ∈ {Φ | ∃ (f : SchwartzMap (κ' → mixedEmbedding.mixedSpace F) ℂ)
        (g : (κ' → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ SB (κ' → FiniteAdeleRing (𝓞 F) F) ∧ Φ = pureA F f g},
      boxFun Φ₁ Φ₂ ∈ schA F (κ ⊕ κ') := by
    rintro _ ⟨f₁, g₁, hg₁, rfl⟩ _ ⟨f₂, g₂, hg₂, rfl⟩
    obtain ⟨f, hf⟩ := exists_schwartz_box f₁ f₂
    refine Submodule.subset_span ⟨f, fun z => g₁ (z ∘ Sum.inl) * g₂ (z ∘ Sum.inr), sb_box hg₁ hg₂, ?_⟩
    funext x
    simp only [boxFun, pureA, hf]
    simp only [Function.comp_def]
    ring
  have gen₂ : ∀ Φ₁ ∈ {Φ | ∃ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
        (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) ∧ Φ = pureA F f g},
      boxFun Φ₁ φ₂ ∈ schA F (κ ⊕ κ') := by
    intro Φ₁ hΦ₁
    induction h₂ using Submodule.span_induction with
    | mem x hx => exact gen Φ₁ hΦ₁ x hx
    | zero => rw [boxFun_zero_right]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [boxFun_add_right]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [boxFun_smul_right]; exact Submodule.smul_mem _ c hx
  induction h₁ using Submodule.span_induction with
  | mem x hx => exact gen₂ x hx
  | zero => rw [boxFun_zero_left]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [boxFun_add_left]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [boxFun_smul_left]; exact Submodule.smul_mem _ c hx

end GlobalTheory.SchwartzBox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotMkEqIffPositiveScalarFormIsomorphic
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx.Form

theorem rel_equivalence {p : ℕ} [Fact p.Prime] (G : HTGroup p) : Equivalence (Form.Rel (G := G)) := by
  have sh_mul : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := by
    intro a b; simp only [sh, map_mul, MulOpposite.unop_mul]
  have sh_one : sh G (1 : G.C) = 1 := by simp only [sh, map_one, MulOpposite.unop_one]
  refine ⟨fun P => ?_, fun {P Q} h => ?_, fun {P Q R} h h' => ?_⟩
  · exact ⟨1, 1, one_pos, by simp [sh_one]⟩
  · obtain ⟨y, s, hs, hβ⟩ := h
    refine ⟨y⁻¹, s⁻¹, inv_pos.mpr hs, ?_⟩
    have e : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
      rw [← sh_mul, Units.inv_mul, sh_one]
    rw [hβ]
    simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, e, mul_one,
      inv_mul_cancel₀ hs.ne', mul_inv_cancel₀ hs.ne', one_smul, Units.inv_mul_cancel_left]
  · obtain ⟨y, s, hs, hβ⟩ := h
    obtain ⟨y', s', hs', hβ'⟩ := h'
    refine ⟨y' * y, s' * s, mul_pos hs' hs, ?_⟩
    rw [hβ', hβ, Units.val_mul, sh_mul]
    simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, mul_comm s]

theorem mk_eq_iff_rel : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Form G),
    Quot.mk Form.Rel P = Quot.mk Form.Rel Q ↔ Form.Rel P Q := by
  intro p _ G P Q
  rw [← (rel_equivalence G).eqvGen_iff]
  exact ⟨Quot.eqvGen_exact, Quot.eqvGen_sound⟩

end GlobalTheory.LKCx.Form
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaisingSpanEqSpanWords
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.HolDS

theorem raisingSpan_eq_span_words : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), IsKMod ε σ D E → ∀ S : Submodule ℂ H, S ≤ D → raisingSpan ε σ S = (Submodule.span ℂ {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ S.comap D.subtype, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x}).map D.subtype := by
  intro n ε H _ _ σ D E hK S hSD
  set Y : Set D := {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧
    ∃ x ∈ S.comap D.subtype, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} with hY
  have hcmp := _root_.GlobalTheory.HolomorphicDiscreteSeriesDecomposition.dRepC_eq_sum n ε H σ D E hK

  have hstab : ∀ a b, ε a = true → ε b = false → ∀ y ∈ Submodule.span ℂ Y, E a b y ∈ Submodule.span ℂ Y := by
    intro a b ha hb y hy
    have hle : Submodule.span ℂ Y ≤ (Submodule.span ℂ Y).comap (E a b) := by
      rw [Submodule.span_le]
      rintro z ⟨l, hl, x, hx, rfl⟩
      apply Submodule.subset_span
      refine ⟨(a, b) :: l, ?_, x, hx, ?_⟩
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact ⟨ha, hb⟩
        · exact hl p hp
      · simp [List.map_cons, List.prod_cons, Module.End.mul_apply]
    exact hle hy
  apply le_antisymm
  · rw [raisingSpan, Submodule.span_le]
    rintro w ⟨l, hl, v, hv, rfl⟩
    have key : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Z ∈ l, Z ∈ pPlus ε) →
        ∃ y ∈ Submodule.span ℂ Y, (y : H) = l.foldr (GlobalTheory.SmVec.dRepC (Jm ε) σ) v := by
      intro l
      induction l with
      | nil =>
        intro _
        refine ⟨⟨v, hSD hv⟩, Submodule.subset_span ⟨[], by simp, ⟨v, hSD hv⟩, hv, by simp⟩, rfl⟩
      | cons Z l ih =>
        intro hl
        obtain ⟨y, hy, hyv⟩ := ih (fun Z' hZ' => hl Z' (List.mem_cons_of_mem _ hZ'))
        have hZ := hl Z List.mem_cons_self
        refine ⟨∑ a, ∑ b, Z a b • E a b y, ?_, ?_⟩
        · refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
          by_cases h : ε a = true ∧ ε b = false
          · exact Submodule.smul_mem _ _ (hstab a b h.1 h.2 y hy)
          · rw [hZ a b h, zero_smul]
            exact Submodule.zero_mem _
        · rw [List.foldr_cons, ← hyv, hcmp Z y]
    obtain ⟨y, hy, hyv⟩ := key l hl
    exact ⟨y, hy, hyv⟩
  · rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨y, ⟨l, hl, x, hx, rfl⟩, rfl⟩
    have key : ∀ l : List (Fin n × Fin n),
        (((l.map fun p : Fin n × Fin n => E p.1 p.2).prod x : D) : H) =
          (l.map fun p : Fin n × Fin n => Matrix.single p.1 p.2 (1 : ℂ)).foldr (GlobalTheory.SmVec.dRepC (Jm ε) σ) (x : H) := by
      intro l
      induction l with
      | nil => simp
      | cons p l ih =>
        rw [List.map_cons, List.map_cons, List.foldr_cons, ← ih, hcmp, List.prod_cons, Module.End.mul_apply]
        congr 1
        rw [Finset.sum_eq_single p.1, Finset.sum_eq_single p.2]
        · simp
        · intro b _ hb; simp [Matrix.single_apply, Ne.symm hb]
        · simp
        · intro a _ ha
          refine Finset.sum_eq_zero fun b _ => ?_
          simp [Matrix.single_apply, Ne.symm ha]
        · simp
    refine Submodule.subset_span ⟨l.map fun p : Fin n × Fin n => Matrix.single p.1 p.2 (1 : ℂ), ?_, (x : H), hx, key l⟩
    intro Z hZ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hZ
    exact single_mem_pPlus (hl p hp).1 (hl p hp).2 1

end GlobalTheory.HolDS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix

namespace GlobalTheory.AdelicSvN

variable {F : Type} [Field F]

def act {R : Type} [CommRing R] [Algebra F R] {κ : Type} [Fintype κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F)
    (w : (κ → R) × (κ → R)) : (κ → R) × (κ → R) :=
  ((g.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2) ∘ Sum.inl, (g.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2) ∘ Sum.inr)

theorem act_one {R : Type} [CommRing R] [Algebra F R] {κ : Type} [Fintype κ] [DecidableEq κ]
    (w : (κ → R) × (κ → R)) : act (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) w = w := by
  have h : (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  simp only [act, h, Matrix.one_mulVec]
  rfl

theorem act_mul {R : Type} [CommRing R] [Algebra F R] {κ : Type} [Fintype κ]
    (g h : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (w : (κ → R) × (κ → R)) : act (g * h) w = act g (act h w) := by
  have e : (g * h).map (algebraMap F R) = g.map (algebraMap F R) * h.map (algebraMap F R) :=
    Matrix.map_mul (f := algebraMap F R)
  simp only [act, e, ← Matrix.mulVec_mulVec, Sum.elim_comp_inl_inr]


variable (F) in
def gens (κ : Type) [Fintype κ] [DecidableEq κ] : Set (Matrix (κ ⊕ κ) (κ ⊕ κ) F) :=
  {g | ∃ A : Matrix κ κ F, IsUnit A.det ∧ g = Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ} ∪
    {g | ∃ C : Matrix κ κ F, Cᵀ = C ∧ g = Matrix.fromBlocks 1 0 (-C) 1} ∪ {Matrix.fromBlocks 0 1 (-1) 0}

variable [NumberField F]

def Realised (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop :=
  ∃ S : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ,
    (∀ φ ∈ schA F κ, S φ ∈ schA F κ) ∧ (∀ φ ∈ schA F κ, ∃ φ' ∈ schA F κ, S φ' = φ) ∧
    (∀ l ∈ (adeleClass F).adm κ, ∃ l' ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ, l' φ = l (S φ)) ∧
    ∀ w, ∀ φ ∈ schA F κ, S (schr ψ w φ) = schr ψ (act g w) (S φ)

theorem realised_one (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ] [DecidableEq κ] :
    Realised ψ (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) :=
  ⟨id, fun φ h => h, fun φ h => ⟨φ, h, rfl⟩, fun l hl => ⟨l, hl, fun _ _ => rfl⟩,
    fun w φ _ => by rw [act_one]; rfl⟩

theorem Realised.mul {ψ : AddChar (AF F) ℂ} {κ : Type} [Fintype κ] {g h : Matrix (κ ⊕ κ) (κ ⊕ κ) F}
    (hg : Realised ψ g) (hh : Realised ψ h) : Realised ψ (g * h) := by
  obtain ⟨S, hS, hSs, hSa, hSi⟩ := hg
  obtain ⟨T, hT, hTs, hTa, hTi⟩ := hh
  refine ⟨S ∘ T, fun φ hφ => hS _ (hT φ hφ), fun φ hφ => ?_, fun l hl => ?_, fun w φ hφ => ?_⟩
  · obtain ⟨φ₁, h₁, rfl⟩ := hSs φ hφ
    obtain ⟨φ₂, h₂, rfl⟩ := hTs φ₁ h₁
    exact ⟨φ₂, h₂, rfl⟩
  · obtain ⟨l₁, hl₁, e₁⟩ := hSa l hl
    obtain ⟨l₂, hl₂, e₂⟩ := hTa l₁ hl₁
    exact ⟨l₂, hl₂, fun φ hφ => (e₂ φ hφ).trans (e₁ _ (hT φ hφ))⟩
  · simp only [Function.comp_apply]
    rw [hTi w φ hφ, hSi _ _ (hT φ hφ), act_mul]

end GlobalTheory.AdelicSvN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularElementSeparableMinpoly
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx

theorem commute_units_conj {A : Type*} [Monoid A] (U : Aˣ) {a e : A} (h : Commute a e) :
    Commute ((U : A) * a * ↑U⁻¹) ((U : A) * e * ↑U⁻¹) := by
  unfold Commute SemiconjBy at *
  calc (U : A) * a * ↑U⁻¹ * ((U : A) * e * ↑U⁻¹) = U * (a * e) * ↑U⁻¹ := by
        simp only [mul_assoc, Units.inv_mul_cancel_left]
    _ = U * (e * a) * ↑U⁻¹ := by rw [h]
    _ = _ := by simp only [mul_assoc, Units.inv_mul_cancel_left]

theorem comm_of_conj {A : Type*} [Monoid A] (U : Aˣ) (e : A)
    (h : ∀ a b : A, Commute a ((U : A) * e * ↑U⁻¹) → Commute b ((U : A) * e * ↑U⁻¹) → Commute a b)
    (a b : A) (ha : Commute a e) (hb : Commute b e) : Commute a b := by
  have h1 := h _ _ (commute_units_conj U ha) (commute_units_conj U hb)
  have h2 := commute_units_conj U⁻¹ h1
  have e1 : ∀ z : A, ((U⁻¹ : Aˣ) : A) * ((U : A) * z * ↑U⁻¹) * ↑(U⁻¹)⁻¹ = z := by
    intro z; simp [mul_assoc]
  rwa [e1, e1] at h2

variable {p : ℕ} [Fact p.Prime]

theorem ubc_val_eq (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t)
    (y : grp G β) (h : G.GAf) (w : AwayP p) :
    ∃ U : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
    ((ubcMap (AfP.eval w) (h⁻¹ * toAfF G β x t hx y * h)).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
      (U : w.1.adicCompletion ℚ ⊗[ℚ] G.C) * ((1 : w.1.adicCompletion ℚ) ⊗ₜ (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) *
        ((U⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) := by
  set φ : AfP p ⊗[ℚ] G.C →ₐ[ℚ] w.1.adicCompletion ℚ ⊗[ℚ] G.C :=
    Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) with hφ
  have hm : ((ubcMap (AfP.eval w) (toAfF G β x t hx y)).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
      φ x * ((1 : w.1.adicCompletion ℚ) ⊗ₜ (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) * φ ↑x⁻¹ := by
    show φ ((x : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ↑x⁻¹) = _
    rw [map_mul, map_mul]
    congr 2
  refine ⟨((ubcMap (AfP.eval w) h).1.1)⁻¹ * Units.map φ.toMonoidHom x, ?_⟩
  rw [map_mul, map_mul, map_inv]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.fst_inv, Units.val_mul, _root_.mul_inv_rev, inv_inv]
  rw [hm]
  simp only [Units.coe_map, MonoidHom.coe_coe, mul_assoc]
  rw [Units.coe_map_inv]
  rfl

end GlobalTheory.LKCx

namespace GlobalTheory.LKCx

end GlobalTheory.LKCx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroCentralizerParabolicCosetStabilizeStatement
section
open MeasureTheory Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_ne_zero_centralizer_parabolicCosetStabilizer : ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b) (γ : GL ι K),
  GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) γ ≤ GlobalTheory.OrbDesc.blockLevi e →
  ∀ K' : Subgroup (GL ι K), IsOpen (K' : Set (GL ι K)) → IsCompact (K' : Set (GL ι K)) →
  ∀ x ∈ GlobalTheory.OrbDesc.blockPar e,
    (GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) γ ⊓ (GlobalTheory.OrbDesc.blockPar e ⊓ K').map (MulAut.conj x).toMonoidHom).relIndex
      (GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) γ ⊓
        ((GlobalTheory.OrbDesc.blockPar e ⊓ K') ⊔ GlobalTheory.OrbDesc.blockUni e).map (MulAut.conj x).toMonoidHom) ≠ 0 := by
  first | (exact @GlobalTheory.OrbDesc.StabIndex.relIndex_twCent_inf_ne_zero) | (exact GlobalTheory.OrbDesc.StabIndex.relIndex_twCent_inf_ne_zero) | (intros; apply GlobalTheory.OrbDesc.StabIndex.relIndex_twCent_inf_ne_zero  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelOfConjInGroupOfCommonForm
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.RelConj

theorem rel_of_conj_in_form : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P P' : Pair G) (B y y' g : G.Cˣ) (s s' sg : ℚ), 0 < s → 0 < s' → 0 < sg → (P.β : G.C) = algebraMap ℚ G.C s * (y * B * sh G y) → (P'.β : G.C) = algebraMap ℚ G.C s' * (y' * B * sh G y') → (g : G.C) * B * sh G g = algebraMap ℚ G.C sg * B → g * (y⁻¹ * P.γ * y) * g⁻¹ = y'⁻¹ * P'.γ * y' → P.Rel P' := by
  intro p _ G P P' B y y' g s s' sg hs hs' hsg hβ hβ' hg hγ
  have shm : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := fun a b => by simp [sh]
  have hyi : ((y⁻¹ : G.Cˣ) : G.C) * y = 1 := Units.inv_mul y
  have hshy : sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
    rw [← shm, hyi]; simp [sh]
  have key : ((y' * g * y⁻¹ : G.Cˣ) : G.C) * P.β * sh G ((y' * g * y⁻¹ : G.Cˣ) : G.C) =
      algebraMap ℚ G.C (s * sg) * (y' * B * sh G y') := by
    rw [hβ, Units.val_mul, Units.val_mul, shm, shm, ← Algebra.smul_def]
    calc (y' : G.C) * g * ((y⁻¹ : G.Cˣ) : G.C) * (s • ((y : G.C) * B * sh G y)) *
          (sh G ((y⁻¹ : G.Cˣ) : G.C) * (sh G g * sh G y'))
        = s • ((y' : G.C) * (g * (((y⁻¹ : G.Cˣ) : G.C) * y) * B * (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C)) * sh G g) * sh G y') := by
          simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
      _ = s • ((y' : G.C) * ((g : G.C) * B * sh G g) * sh G y') := by
          rw [hyi, hshy, mul_one, mul_one]
      _ = s • (sg • ((y' : G.C) * B * sh G y')) := by
          rw [hg, ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]
      _ = _ := by rw [smul_smul, Algebra.smul_def]
  refine ⟨y' * g * y⁻¹, s' / (s * sg), div_pos hs' (mul_pos hs hsg), ?_, ?_⟩
  · rw [key, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ (mul_pos hs hsg).ne', hβ']
  · have e : P'.γ = y' * (y'⁻¹ * P'.γ * y') * y'⁻¹ := by group
    rw [e, ← hγ]; group

end GlobalTheory.RelConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelatedPairsSamePolarizationStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.related_pairs_same_polarization : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Pair G), P.Rel Q → Q.pol = P.pol ∧ Q.c = P.c := by
  first | (exact @GlobalTheory.LKMid.Pair.rel_pol_c) | (exact GlobalTheory.LKMid.Pair.rel_pol_c) | (intros; apply GlobalTheory.LKMid.Pair.rel_pol_c  <;> assumption)
end

