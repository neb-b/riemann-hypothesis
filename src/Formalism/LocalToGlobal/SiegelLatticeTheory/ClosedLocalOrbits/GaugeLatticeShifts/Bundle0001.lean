module

public import Mathlib

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAbs
section
noncomputable section

open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal

set_option linter.dupNamespace false

namespace Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [MeasurableSpace G]

def rk1A {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] (v : V) (w : V') : V' →L[ℂ] V := (innerSL ℂ w).smulRight v

def hsA {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V'] (A : V' →L[ℂ] V) : ℝ :=
  ∑ i, ‖A (stdOrthonormalBasis ℂ V' i)‖ ^ 2

def IsUnitRep [TopologicalSpace G] {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH]
    (σ : G → (HH →L[ℂ] HH)) : Prop :=
  σ 1 = 1 ∧ (∀ x y, σ (x * y) = σ x * σ y) ∧ (∀ x a b, ⟪σ x a, σ x b⟫_ℂ = ⟪a, b⟫_ℂ) ∧
    ∀ a, Continuous (fun x => σ x a)

def IsSchur {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] (μ : Measure G)
    (σ : G → (HH →L[ℂ] HH)) (d : ℝ) : Prop :=
  0 < d ∧ ∀ a b a' b' : HH,
    Integrable (fun x => ⟪b, σ x a⟫_ℂ * conj ⟪b', σ x a'⟫_ℂ) μ ∧
      ∫ x, ⟪b, σ x a⟫_ℂ * conj ⟪b', σ x a'⟫_ℂ ∂μ = ⟪a', a⟫_ℂ * ⟪b, b'⟫_ℂ / (d : ℂ)

def IsHaarSub [TopologicalSpace G] (S : Set G) (μS : Measure G) : Prop :=
  IsClosed S ∧ (1 : G) ∈ S ∧ (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) ∧ (∀ a ∈ S, a⁻¹ ∈ S) ∧
    SigmaFinite μS ∧ μS ≠ 0 ∧ μS Sᶜ = 0 ∧ (∀ s ∈ S, μS.map (fun x => s * x) = μS) ∧
    (∀ K : Set G, IsCompact K → μS K < ⊤) ∧ (∀ s ∈ S, μS.map (fun x => x * s) = μS) ∧ μS.map (fun x => x⁻¹) = μS

def IsFolner (S : Set G) (μS : Measure G) [TopologicalSpace G] : Prop :=
  ∀ K : Set G, IsCompact K → K ⊆ S → ∀ ε : ℝ≥0∞, 0 < ε →
    ∃ Ω : Set G, MeasurableSet Ω ∧ Ω ⊆ S ∧ 0 < μS Ω ∧ μS Ω < ⊤ ∧
      μS Ω ≤ (1 + ε) * μS {t | t ∈ Ω ∧ ∀ k ∈ K, k * t ∈ Ω}

def IsQuot (μ μS ν : Measure G) : Prop :=
  ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f (s * x) ∂μS ∂ν

def IsWAbs [TopologicalSpace G] {HH V : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (μ : Measure G) (σ : G → (HH →L[ℂ] HH)) (d : ℝ) (w : HH)
    (S : Set G) (τ : G → (V →L[ℂ] V)) (ν : Measure G) (W : G → V) : Prop :=
  τ 1 = 1 ∧ (∀ s ∈ S, ∀ t ∈ S, τ (s * t) = τ s * τ t) ∧ (∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ) ∧
    (∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) ∧ Continuous W ∧
    (∀ x, Integrable (fun y => ((d : ℂ) * conj ⟪w, σ y w⟫_ℂ) • W (x * y)) μ ∧
      ∫ y, ((d : ℂ) * conj ⟪w, σ y w⟫_ℂ) • W (x * y) ∂μ = W x) ∧
    ∫⁻ x, ‖W x‖ₑ ∂ν < ⊤ ∧ ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν = 1

def IsDisint {C : Type} [MeasurableSpace C] (μ μS μS' : Measure G) (m : Measure C) (h : C → G) : Prop :=
  ∀ φ : G → ℝ≥0∞, Measurable φ →
    ∫⁻ x, φ x ∂μ = ∫⁻ c, ∫⁻ s, ∫⁻ s', φ (s * h c * s'⁻¹) ∂μS' ∂μS ∂m

def EnergyAbs : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (HH : Type) [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
    (σ : G → (HH →L[ℂ] HH)) (d : ℝ) (w : HH)
    (V V' : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
    (S S' : Set G) (μS μS' ν ν' : Measure G) (τ : G → (V →L[ℂ] V)) (τ' : G → (V' →L[ℂ] V'))
    (W : G → V) (W' : G → V') (C : Type) (_ : MeasurableSpace C) (m : Measure C) (h : C → G),
    IsUnitRep σ → IsSchur μ σ d → ‖w‖ = 1 →
    IsHaarSub S μS → IsHaarSub S' μS' → IsFolner S μS → IsFolner S' μS' →
    SFinite ν → SFinite ν' → IsQuot μ μS ν → IsQuot μ μS' ν' →
    IsWAbs μ σ d w S τ ν W → IsWAbs μ σ d w S' τ' ν' W' →
    IsDisint μ μS μS' m h → Measurable h →
    (∀ c, Integrable (fun x => rk1A (W x) (W' ((h c)⁻¹ * x))) μ) →
    (∀ c, ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', ‖⟪σ z w, σ (s * h c * s'⁻¹) (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W' z'‖ₑ
      ∂μS' ∂μS ∂ν' ∂ν < ⊤) →
    (∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS ∂ν ∂ν < ⊤) →
    (∫⁻ z, ∫⁻ z', ∫⁻ s', ‖⟪σ z w, σ s' (σ z' w)⟫_ℂ‖ₑ * ‖W' z‖ₑ * ‖W' z'‖ₑ ∂μS' ∂ν' ∂ν' < ⊤) →
    ∫⁻ c, ENNReal.ofReal (hsA (∫ x, rk1A (W x) (W' ((h c)⁻¹ * x)) ∂μ)) ∂m ≤ ENNReal.ofReal (1 / d)

end Formalism.L2.SG.Pf.EnergyAbs
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LintegralFinProd
section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM

theorem lintegral_fin_prod : ∀ (m : ℕ) {α : Fin m → Type} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] (f : ∀ i, α i → ℝ≥0∞), (∀ i, Measurable (f i)) →
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i
  | 0, α, _, μ, _, f, _ => by
    simp
  | m + 1, α, _, μ, _, f, hf => by
    have hmp := measurePreserving_piFinSuccAbove μ 0
    set g : α 0 × ((j : Fin m) → α (Fin.succAbove 0 j)) → ℝ≥0∞ :=
      fun z => f 0 z.1 * ∏ i : Fin m, f (Fin.succAbove 0 i) (z.2 i) with hg
    have key : ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ =
        ∫⁻ x, g (MeasurableEquiv.piFinSuccAbove α 0 x) ∂Measure.pi μ := by
      congr 1
      funext x
      rw [Fin.prod_univ_succAbove _ 0]
      rfl
    have hpm : ∫⁻ b, g b ∂((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))) =
        (∫⁻ x, f 0 x ∂μ 0) * ∫⁻ y : (j : Fin m) → α (Fin.succAbove 0 j), ∏ i, f (Fin.succAbove 0 i) (y i)
          ∂(Measure.pi fun j => μ (Fin.succAbove 0 j)) :=
      lintegral_prod_mul (f := f 0) (g := fun y : (j : Fin m) → α (Fin.succAbove 0 j) => ∏ i, f (Fin.succAbove 0 i) (y i))
        (hf 0).aemeasurable
        (Finset.measurable_prod _ fun i _ => (hf _).comp (measurable_pi_apply i)).aemeasurable
    rw [key, hmp.lintegral_comp_emb (MeasurableEquiv.piFinSuccAbove α 0).measurableEmbedding g, hpm,
      lintegral_fin_prod m (fun j => μ (Fin.succAbove 0 j)) (fun j => f (Fin.succAbove 0 j)) (fun j => hf _),
      Fin.prod_univ_succAbove _ 0]

theorem lintegral_pi_prod {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] (f : ∀ i, α i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i := by
  let e := (Fintype.equivFin ι).symm
  have hmp := measurePreserving_piCongrLeft μ e
  rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  have h1 : ∀ g : (∀ i', α (e i')), ∏ i, f i ((MeasurableEquiv.piCongrLeft α e g) i) =
      ∏ i', f (e i') (g i') := by
    intro g
    rw [← Fintype.prod_equiv e (fun i' => f (e i') (MeasurableEquiv.piCongrLeft α e g (e i')))
      (fun i => f i (MeasurableEquiv.piCongrLeft α e g i)) (fun _ => rfl)]
    congr 1
    funext i'
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
  simp only [h1]
  rw [lintegral_fin_prod _ (fun i' => μ (e i')) (fun i' => f (e i')) (fun i' => hf _)]
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

end Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.QuotIndepStmt
section
open MeasureTheory Measure
open scoped ENNReal

set_option linter.dupNamespace false

namespace Formalism.L2.SG.Pf.QuotIndep

def QuotIndep : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (S : Subgroup G), IsClosed (S : Set G) →
    ∀ (μS : Measure S) [μS.IsMulLeftInvariant] [μS.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μS]
      [IsOpenPosMeasure μS] [SFinite μS] (μ ν₁ ν₂ : Measure G),
      (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f ((s : G) * x) ∂μS ∂ν₁) →
      (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f ((s : G) * x) ∂μS ∂ν₂) →
      ∀ f : G → ℝ≥0∞, Measurable f → (∀ (s : S) (x : G), f ((s : G) * x) = f x) →
        ∫⁻ x, f x ∂ν₁ = ∫⁻ x, f x ∂ν₂

end Formalism.L2.SG.Pf.QuotIndep
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfStmt
section
namespace Formalism.L2.SG.Pf.RCoc

def KerBaseChange : Prop :=
  ∀ (K L : Type) [Field K] [Field L] (f : K →+* L) (m p : Type) [Fintype m] [Fintype p] [DecidableEq p]
    (A : Matrix m p K), ∃ P : Matrix p p K, A * P = 0 ∧
      ∀ z : p → L, (A.map f).mulVec z = 0 → (P.map f).mulVec z = z

end Formalism.L2.SG.Pf.RCoc
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfUnfold
section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.L2.SG.Pf.RegroupPf

section OrbitUnfold

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H]

theorem isFund_of_exact (μ : Measure H) (R : Subgroup H) (W : Set H) (hm : MeasurableSet W)
    (hc : ∀ x, ∃ g ∈ R, g * x ∈ W) (hu : ∀ x ∈ W, ∀ g ∈ R, g * x ∈ W → g = 1) :
    IsFundamentalDomain R W μ := by
  refine IsFundamentalDomain.mk' hm.nullMeasurableSet fun x => ?_
  obtain ⟨g, hg, hgx⟩ := hc x
  refine ⟨⟨g, hg⟩, hgx, ?_⟩
  rintro ⟨k, hk⟩ hkx
  have hkx' : k * x ∈ W := hkx
  have h := hu (g * x) hgx (k * g⁻¹) (R.mul_mem hk (R.inv_mem hg))
    (by rwa [mul_assoc, inv_mul_cancel_left])
  exact Subtype.ext (mul_inv_eq_one.mp h)

theorem orbit_unfold (μ : Measure H) [μ.IsMulLeftInvariant]
    (N : Subgroup H) [Countable N] {C : Type*} [Countable C] (act : N → C → C) (h1 : ∀ c, act 1 c = c)
    (hmul : ∀ n m c, act (n * m) c = act n (act m c))
    (F : C → H → ℂ) (hFm : ∀ c, Measurable (F c)) (hFeq : ∀ (n : N) c y, F (act n c) y = F c ((n : H)⁻¹ * y))
    (Ω : Set H) (hΩm : MeasurableSet Ω) (hΩc : ∀ x, ∃ n : N, (n : H) * x ∈ Ω)
    (hΩu : ∀ x ∈ Ω, ∀ n : N, (n : H) * x ∈ Ω → n = 1)
    {J : Type*} (r : J → C) (hcov : ∀ c, ∃ j n, act n (r j) = c) (huniq : ∀ j j' n, act n (r j) = r j' → j = j')
    (ΩJ : J → Set H) (hJm : ∀ j, MeasurableSet (ΩJ j))
    (hJc : ∀ j x, ∃ n : N, act n (r j) = r j ∧ (n : H) * x ∈ ΩJ j)
    (hJu : ∀ j, ∀ x ∈ ΩJ j, ∀ n : N, act n (r j) = r j → (n : H) * x ∈ ΩJ j → n = 1)
    (hint : ∫⁻ y in Ω, ∑' c, ‖F c y‖ₑ ∂μ < ⊤) :
    IntegrableOn (fun y => ∑' c, F c y) Ω μ ∧
      ∫ y in Ω, ∑' c, F c y ∂μ = ∑' j, ∫ y in ΩJ j, F (r j) y ∂μ := by
  classical
  have hsm : ∀ (n : N) (y : H), n⁻¹ • y = (n : H)⁻¹ * y := fun n y => by
    first | rfl | simp [Subgroup.smul_def]
  have hFeq' : ∀ (n : N) (j : J) (y : H), F (act n (r j)) y = F (r j) (n⁻¹ • y) := by
    intro n j y; rw [hFeq, hsm]
  have hrinj : Function.Injective r := fun j j' h => huniq j j' 1 (by rw [h1, h])
  haveI : Countable J := hrinj.countable
  haveI : MeasurableConstSMul N H := by
    first
      | infer_instance
      | exact ⟨fun n => measurable_const_mul (n : H)⟩
  haveI : SMulInvariantMeasure N H μ := by
    first
      | infer_instance
      | exact ⟨fun n ⦃s⦄ _ => measure_preimage_mul μ (n : H) s⟩

  have hΩ : IsFundamentalDomain N Ω μ := by
    refine isFund_of_exact μ N Ω hΩm (fun x => ?_) (fun x hx g hg hgx => ?_)
    · obtain ⟨n, hn⟩ := hΩc x
      exact ⟨n, n.2, hn⟩
    · have := hΩu x hx ⟨g, hg⟩ hgx
      simpa using congrArg Subtype.val this

  have hbij : ∀ y : H, Function.Bijective
      (fun p : ({p : J × N | p.2⁻¹ • y ∈ ΩJ p.1} : Set (J × N)) =>
        act (p : J × N).2 (r (p : J × N).1)) := by
    intro y
    constructor
    · rintro ⟨⟨j, n⟩, hy⟩ ⟨⟨j', n'⟩, hy'⟩ heq
      have hy1 : n⁻¹ • y ∈ ΩJ j := hy
      have hy2 : n'⁻¹ • y ∈ ΩJ j' := hy'
      have heq' : act n (r j) = act n' (r j') := heq
      have e1 : act (n'⁻¹ * n) (r j) = r j' := by
        rw [hmul, heq', ← hmul, inv_mul_cancel, h1]
      obtain rfl : j = j' := huniq j j' _ e1
      have e2 : n'⁻¹ * n = 1 := by
        refine hJu j _ hy1 _ e1 ?_
        have hh : ((n'⁻¹ * n : N) : H) * (n⁻¹ • y) = n'⁻¹ • y := by
          simp only [hsm]
          first | simp [mul_assoc] | group
        rw [hh]
        exact hy2
      obtain rfl : n = n' := (inv_mul_eq_one.mp e2).symm
      rfl
    · intro c
      obtain ⟨j, n0, hc⟩ := hcov c
      obtain ⟨s, hs1, hs2⟩ := hJc j (n0⁻¹ • y)
      have hmem : (n0 * s⁻¹)⁻¹ • y ∈ ΩJ j := by
        have hh : (n0 * s⁻¹)⁻¹ • y = (s : H) * (n0⁻¹ • y) := by
          simp only [hsm]
          first | simp [mul_assoc] | group
        rw [hh]
        exact hs2
      refine ⟨⟨(j, n0 * s⁻¹), hmem⟩, ?_⟩
      show act (n0 * s⁻¹) (r j) = c
      have hsi : act s⁻¹ (r j) = r j := by
        calc act s⁻¹ (r j) = act s⁻¹ (act s (r j)) := by rw [hs1]
          _ = r j := by rw [← hmul, inv_mul_cancel, h1]
      rw [hmul, hsi, hc]
  have key : ∀ (y : H) {M : Type} [AddCommMonoid M] [TopologicalSpace M] (G : C → M),
      ∑' p : J × N, ({p : J × N | p.2⁻¹ • y ∈ ΩJ p.1} : Set (J × N)).indicator
        (fun p => G (act p.2 (r p.1))) p = ∑' c, G c := by
    intro y M _ _ G
    rw [← tsum_subtype]
    exact (Equiv.ofBijective _ (hbij y)).tsum_eq G
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : J × N → H → ℂ,
      Ψ = fun p y => (ΩJ p.1).indicator (F (r p.1)) (p.2⁻¹ • y) := ⟨_, rfl⟩
  have hΨ : ∀ y p, Ψ p y = ({p : J × N | p.2⁻¹ • y ∈ ΩJ p.1} : Set (J × N)).indicator
      (fun p => F (act p.2 (r p.1)) y) p := by
    intro y p
    subst hΨdef
    by_cases h : p.2⁻¹ • y ∈ ΩJ p.1
    · first
        | simp only [Set.indicator_apply, Set.mem_setOf_eq, h, ↓reduceIte, hFeq']
        | simp [Set.indicator_apply, h, hFeq']
    · first
        | simp only [Set.indicator_apply, Set.mem_setOf_eq, h, ↓reduceIte]
        | simp [Set.indicator_apply, h]
  have hΨe : ∀ y p, ‖Ψ p y‖ₑ = ({p : J × N | p.2⁻¹ • y ∈ ΩJ p.1} : Set (J × N)).indicator
      (fun p => ‖F (act p.2 (r p.1)) y‖ₑ) p := by
    intro y p
    rw [hΨ y p]
    by_cases h : p.2⁻¹ • y ∈ ΩJ p.1
    · first
        | simp only [Set.indicator_apply, Set.mem_setOf_eq, h, ↓reduceIte]
        | simp [Set.indicator_apply, h]
    · first
        | simp only [Set.indicator_apply, Set.mem_setOf_eq, h, ↓reduceIte, enorm_zero]
        | simp [Set.indicator_apply, h]
  have hΨm : ∀ p, Measurable (Ψ p) := by
    intro p
    subst hΨdef
    simp only [hsm]
    exact ((hFm _).indicator (hJm _)).comp (measurable_const_mul _)
  have sumC : ∀ y, ∑' p, Ψ p y = ∑' c, F c y := fun y =>
    (tsum_congr (hΨ y)).trans (key y (fun c => F c y))
  have sumE : ∀ y, ∑' p, ‖Ψ p y‖ₑ = ∑' c, ‖F c y‖ₑ := fun y =>
    (tsum_congr (hΨe y)).trans (key y (fun c => ‖F c y‖ₑ))
  have hT : ∑' p : J × N, ∫⁻ x in Ω, ‖Ψ p x‖ₑ ∂μ = ∫⁻ x in Ω, ∑' c, ‖F c x‖ₑ ∂μ := by
    rw [← lintegral_tsum (fun p => (hΨm p).enorm.aemeasurable)]
    exact lintegral_congr (fun x => sumE x)
  have hTfin : ∑' p : J × N, ∫⁻ x in Ω, ‖Ψ p x‖ₑ ∂μ ≠ ⊤ := by
    rw [hT]
    exact hint.ne

  have hIJ : ∀ j, ∫ y in ΩJ j, F (r j) y ∂μ = ∑' n : N, ∫ y in Ω, Ψ (j, n) y ∂μ := by
    intro j
    have hrow : ∫⁻ x, ‖(ΩJ j).indicator (F (r j)) x‖ₑ ∂μ
        = ∑' n : N, ∫⁻ x in Ω, ‖Ψ (j, n) x‖ₑ ∂μ := by
      refine (hΩ.lintegral_eq_tsum' _).trans ?_
      subst hΨdef
      rfl
    have hlt : ∑' n : N, ∫⁻ x in Ω, ‖Ψ (j, n) x‖ₑ ∂μ < ⊤ := by
      refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr hTfin)
      calc ∑' n : N, ∫⁻ x in Ω, ‖Ψ (j, n) x‖ₑ ∂μ
          ≤ ∑' j' : J, ∑' n : N, ∫⁻ x in Ω, ‖Ψ (j', n) x‖ₑ ∂μ :=
            ENNReal.le_tsum (f := fun j' => ∑' n : N, ∫⁻ x in Ω, ‖Ψ (j', n) x‖ₑ ∂μ) j
        _ = ∑' p : J × N, ∫⁻ x in Ω, ‖Ψ p x‖ₑ ∂μ :=
            (ENNReal.tsum_prod (f := fun a b => ∫⁻ x in Ω, ‖Ψ (a, b) x‖ₑ ∂μ)).symm
    have hfi : Integrable ((ΩJ j).indicator (F (r j))) μ := by
      refine ⟨((hFm (r j)).indicator (hJm j)).aestronglyMeasurable, ?_⟩
      first
        | (show ∫⁻ x, ‖(ΩJ j).indicator (F (r j)) x‖ₑ ∂μ < ⊤
           rw [hrow]
           exact hlt)
        | (rw [hasFiniteIntegral_iff_enorm, hrow]
           exact hlt)
    calc ∫ y in ΩJ j, F (r j) y ∂μ = ∫ x, (ΩJ j).indicator (F (r j)) x ∂μ :=
          (integral_indicator (hJm j)).symm
      _ = ∑' n : N, ∫ x in Ω, (ΩJ j).indicator (F (r j)) (n⁻¹ • x) ∂μ :=
          hΩ.integral_eq_tsum' _ hfi
      _ = ∑' n : N, ∫ y in Ω, Ψ (j, n) y ∂μ := by
          subst hΨdef
          rfl
  have hmain : ∫ y in Ω, ∑' c, F c y ∂μ = ∑' p : J × N, ∫ y in Ω, Ψ p y ∂μ := by
    rw [← integral_tsum (fun p => (hΨm p).aestronglyMeasurable) hTfin]
    first
      | simp only [sumC]
      | exact integral_congr_ae (Filter.Eventually.of_forall fun y => (sumC y).symm)
  have hsplit : ∑' p : J × N, ∫ y in Ω, Ψ p y ∂μ
      = ∑' j, ∑' n : N, ∫ y in Ω, Ψ (j, n) y ∂μ := by
    have hasum : Summable fun p : J × N => ∫ y in Ω, Ψ p y ∂μ := by
      refine Summable.of_norm (Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_)
        (ENNReal.summable_toReal hTfin))
      have h0 := norm_integral_le_lintegral_norm (μ := μ.restrict Ω) (Ψ p)
      first
        | simpa only [ofReal_norm_eq_enorm] using h0
        | simpa using h0
        | exact h0
    exact ((hasum.hasSum.prod_fiberwise fun j => (hasum.prod_factor j).hasSum).tsum_eq).symm
  refine ⟨?_, ?_⟩
  · have hEm : Measurable fun y => ∑' c, ‖F c y‖ₑ :=
      Measurable.tsum fun c => (hFm c).enorm
    have hfin_ae : ∀ᵐ y ∂(μ.restrict Ω), ∑' c, ‖F c y‖ₑ < ⊤ := ae_lt_top hEm hint.ne
    have hsN : ∀ y, ∑' c, ‖F c y‖ₑ < ⊤ → Summable fun c => ‖F c y‖ := by
      intro y hy
      have h0 := ENNReal.summable_toReal hy.ne
      first
        | simpa only [toReal_enorm] using h0
        | simpa using h0
    have hgint : Integrable (fun y => (∑' c, ‖F c y‖ₑ).toReal) (μ.restrict Ω) :=
      integrable_toReal_of_lintegral_ne_top hEm.aemeasurable hint.ne
    have hbound : ∀ᵐ y ∂(μ.restrict Ω), ‖∑' c, F c y‖ ≤ (∑' c, ‖F c y‖ₑ).toReal := by
      filter_upwards [hfin_ae] with y hy
      rw [ENNReal.tsum_toReal_eq (fun c => by first | exact enorm_ne_top | simp)]
      simp only [toReal_enorm]
      exact norm_tsum_le_tsum_norm (hsN y hy)
    have hgm : AEStronglyMeasurable (fun y => ∑' c, F c y) (μ.restrict Ω) := by
      haveI : Encodable C := Encodable.ofCountable C
      have hlim : ∀ᵐ y ∂(μ.restrict Ω), Filter.Tendsto (fun s : Finset C => ∑ c ∈ s, F c y)
          Filter.atTop (nhds (∑' c, F c y)) := by
        filter_upwards [hfin_ae] with y hy
        exact (Summable.of_norm (hsN y hy)).hasSum
      have hfs : ∀ s : Finset C, Measurable fun y => ∑ c ∈ s, F c y := fun s => by
        first
          | exact Finset.measurable_sum s (fun c _ => hFm c)
          | fun_prop
      first
        | exact aestronglyMeasurable_of_tendsto_ae Filter.atTop
            (fun s => (hfs s).aestronglyMeasurable) hlim
        | exact (aemeasurable_of_tendsto_metrizable_ae Filter.atTop
            (fun s => (hfs s).aemeasurable) hlim).aestronglyMeasurable
    exact Integrable.mono' hgint hgm hbound
  · rw [hmain, hsplit]
    exact tsum_congr fun j => (hIJ j).symm

end OrbitUnfold

end Formalism.L2.SG.Pf.RegroupPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SigmaFiniteOfFcG
section
noncomputable section

open MeasureTheory Measure Topology
open scoped ENNReal NNReal

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def subOf (H : Set G) (h1 : (1 : G) ∈ H) (hm : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H) (hi : ∀ x ∈ H, x⁻¹ ∈ H) :
    Subgroup G where
  carrier := H
  one_mem' := h1
  mul_mem' := fun {a b} ha hb => hm a ha b hb
  inv_mem' := fun {a} ha => hi a ha

theorem pull (S : Subgroup G) (hS : IsClosed (S : Set G)) (ν : Measure G) (hνc : ν (S : Set G)ᶜ = 0)
    (hνi : ∀ s ∈ S, ν.map (fun x => s * x) = ν) (hνf : IsFiniteMeasureOnCompacts ν) :
    (ν.comap (Subtype.val : S → G)).IsMulLeftInvariant ∧
      IsFiniteMeasureOnCompacts (ν.comap (Subtype.val : S → G)) ∧
      (ν.comap (Subtype.val : S → G)).map Subtype.val = ν := by
  have hme : MeasurableEmbedding (Subtype.val : S → G) :=
    MeasurableEmbedding.subtype_coe hS.measurableSet
  have hmap : (ν.comap (Subtype.val : S → G)).map Subtype.val = ν := by
    rw [hme.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hνc)
  refine ⟨⟨fun g => ?_⟩, ⟨fun K hK => ?_⟩, hmap⟩
  · have h1 : ((ν.comap (Subtype.val : S → G)).map (fun x => g * x)).map Subtype.val = ν := by
      rw [Measure.map_map hme.measurable (measurable_const_mul g)]
      have : (Subtype.val : S → G) ∘ (fun x : S => g * x) =
          (fun x : G => (g : G) * x) ∘ (Subtype.val : S → G) := by
        funext x; rfl
      rw [this, ← Measure.map_map (measurable_const_mul _) hme.measurable, hmap]
      exact hνi g g.2
    calc (ν.comap (Subtype.val : S → G)).map (fun x => g * x)
        = (((ν.comap (Subtype.val : S → G)).map (fun x => g * x)).map Subtype.val).comap
            Subtype.val := (hme.comap_map _).symm
      _ = ν.comap Subtype.val := by rw [h1]
  · rw [hme.comap_apply]
    exact (hK.image continuous_subtype_val).measure_lt_top

theorem haar_unique (S : Subgroup G) (hS : IsClosed (S : Set G)) (μ m : Measure G) (hμ0 : μ ≠ 0)
    (hμc : μ (S : Set G)ᶜ = 0) (hμi : ∀ s ∈ S, μ.map (fun x => s * x) = μ) (hμf : IsFiniteMeasureOnCompacts μ)
    (hmc : m (S : Set G)ᶜ = 0) (hmi : ∀ s ∈ S, m.map (fun x => s * x) = m) (hmf : IsFiniteMeasureOnCompacts m) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ m = c • μ := by
  haveI : LocallyCompactSpace S := hS.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology S :=
    TopologicalSpace.Subtype.secondCountableTopology (S : Set G)
  obtain ⟨hμl, hμk, hμm⟩ := pull S hS μ hμc hμi hμf
  obtain ⟨hml, hmk, hmm⟩ := pull S hS m hmc hmi hmf
  set μ' := μ.comap (Subtype.val : S → G)
  set m' := m.comap (Subtype.val : S → G)
  have hμ := Measure.isMulLeftInvariant_eq_smul μ' (Measure.haar : Measure S)
  have hm := Measure.isMulLeftInvariant_eq_smul m' (Measure.haar : Measure S)
  set d := Measure.haarScalarFactor μ' (Measure.haar : Measure S)
  set c := Measure.haarScalarFactor m' (Measure.haar : Measure S)
  have hd : d ≠ 0 := by
    intro h0
    apply hμ0
    rw [← hμm, hμ, h0, zero_smul, Measure.map_zero]
  refine ⟨((c / d : ℝ≥0) : ℝ≥0∞), ENNReal.coe_ne_top, ?_⟩
  have hm'' : m' = (c / d) • μ' := by
    rw [hm, hμ, smul_smul, div_mul_cancel₀ c hd]
  rw [← hmm, ← hμm, hm'', Measure.map_smul _ measurable_subtype_coe.aemeasurable]
  rfl

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore
end
end

