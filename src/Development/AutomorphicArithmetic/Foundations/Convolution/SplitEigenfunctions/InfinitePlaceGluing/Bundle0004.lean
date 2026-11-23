module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle0001
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0023
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0016
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0020
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0015
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0026
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0019
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0018
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0025

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.AdmissibleRightTranslate
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

private theorem wo_sum (D : Dat ℚ E) {ι : Type} (s : Finset ι) (a : ι → ℂ) (F : ι → GL (Fin 2) (A E) → ℂ)
    (hF : ∀ i, Continuous (F i)) (h : GL (Fin 2) (A E)) :
    Wo D (∑ i ∈ s, a i • F i) h = ∑ i ∈ s, a i * Wo D (F i) h := by
  obtain ⟨hadd, hsmul, -⟩ := UpperTheory.whittakerPeriod_add_smul_and_norm_le E D
  induction s using Finset.induction_on with
  | empty => simp [Wo]
  | insert i s hi ih =>
    have hc : Continuous (∑ x ∈ s, a x • F x) := by
      rw [Finset.sum_fn]
      exact continuous_finsetSum _ fun j _ => (hF j).const_smul _
    rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd _ _ ((hF i).const_smul _) hc, hsmul, ih]

private theorem lie_expand {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ (Lie E 2)) (X : Lie E 2) (f : Sm E 2) :
    (lie E 2 X f).1 = ∑ i, ((b.repr X i : ℝ) : ℂ) • (lie E 2 (b i) f).1 := by
  have h : lie E 2 X = ∑ i, (b.repr X i) • lie E 2 (b i) := by
    conv_lhs => rw [← b.sum_repr X]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul]
  rw [h]
  funext g
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, Submodule.coe_smul_of_tower, Pi.smul_apply, Complex.real_smul, smul_eq_mul]

private theorem pow_bound (D : Dat ℚ E) (P : CuspSub E 2) (hL : ∀ f ∈ P.V, Pp.Lf f.1)
    (hB : ∀ f ∈ P.V, ∃ B : ℝ, ∀ g, ‖f.1 g‖ ≤ B) (r : ℕ) :
    ∀ f ∈ P.V, ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∃ B : ℝ, ∀ y : (A ℚ)ˣ, ∀ k ∈ C,
      |re (y : A ℚ)| ^ r * ‖Wo D f.1 (em E (aE y) * k)‖ ≤ B := by
  obtain ⟨-, -, hnorm⟩ := UpperTheory.whittakerPeriod_add_smul_and_norm_le E D
  induction r with
  | zero =>
    intro f hf C _
    obtain ⟨B, hB'⟩ := hB f hf
    exact ⟨B, fun y k _ => by simpa using hnorm f.1 B _ hB'⟩
  | succ r ih =>
    intro f hf C hC
    let b := Module.finBasis ℝ (Lie E 2)
    have hmem : ∀ X, lie E 2 X f ∈ P.V := fun X => P.stable (.lie X) f hf
    choose Bi hBi using fun i => ih _ (hmem (b i)) C hC
    have hcont : ∀ i, Continuous fun k : GL (Fin 2) (A E) => b.repr (toL (XB D k)) i := fun i =>
      ((LinearMap.continuous_of_finiteDimensional ((Module.Basis.coord b i))).comp (UpperTheory.archimedeanConjugateCurve_oneParameterSubgroup E D 1).2.2.2)
    choose R hR using fun i => hC.exists_bound_of_continuousOn (hcont i).continuousOn
    refine ⟨(∑ i, |R i| * |Bi i|) / (2 * Real.pi), fun y k hk => ?_⟩
    have he := UpperTheory.whittakerCoeff_lieDeriv_unipotent_eq_mul E D f (hL f hf) (fun X => ⟨(hL _ (hmem X)).1, hB _ (hmem X)⟩) y k
    rw [lie_expand b, wo_sum D _ _ _ fun i => (hL _ (hmem (b i))).1] at he
    have hpi : 0 < 2 * Real.pi := by positivity
    have h1 : 2 * Real.pi * (|re (y : A ℚ)| * ‖Wo D f.1 (em E (aE y) * k)‖) ≤
        ∑ i, ‖b.repr (toL (XB D k)) i‖ * ‖Wo D (lie E 2 (b i) f).1 (em E (aE y) * k)‖ := by
      have := congrArg norm he
      rw [norm_mul, norm_mul, norm_mul, norm_mul] at this
      simp only [Complex.norm_I, Complex.norm_real, Complex.norm_ofNat, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one] at this
      rw [mul_assoc] at this
      rw [← this]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      simp
    rw [le_div_iff₀ hpi, pow_succ]
    calc |re (y : A ℚ)| ^ r * |re (y : A ℚ)| * ‖Wo D f.1 (em E (aE y) * k)‖ * (2 * Real.pi)
        = |re (y : A ℚ)| ^ r * (2 * Real.pi * (|re (y : A ℚ)| * ‖Wo D f.1 (em E (aE y) * k)‖)) := by ring
      _ ≤ |re (y : A ℚ)| ^ r * ∑ i, ‖b.repr (toL (XB D k)) i‖ * ‖Wo D (lie E 2 (b i) f).1 (em E (aE y) * k)‖ := by gcongr
      _ = ∑ i, ‖b.repr (toL (XB D k)) i‖ * (|re (y : A ℚ)| ^ r * ‖Wo D (lie E 2 (b i) f).1 (em E (aE y) * k)‖) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i, |R i| * |Bi i| := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h2 := hBi i y k hk
          have h3 := hR i k hk
          have h4 : 0 ≤ |re (y : A ℚ)| ^ r * ‖Wo D (lie E 2 (b i) f).1 (em E (aE y) * k)‖ := by positivity
          exact mul_le_mul (h3.trans (le_abs_self _)) (h2.trans (le_abs_self _)) h4 (abs_nonneg _)

end SlopeTestRemainingChoices

section Main

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

private theorem one_add_pow_le (x : ℝ) (hx : 0 ≤ x) (r : ℕ) : (1 + x) ^ r ≤ 2 ^ r * (1 + x ^ r) := by
  rcases le_total x 1 with h | h
  · calc (1 + x) ^ r ≤ 2 ^ r := pow_le_pow_left₀ (by positivity) (by linarith) r
      _ ≤ 2 ^ r * (1 + x ^ r) := le_mul_of_one_le_right (by positivity) (by have := pow_nonneg hx r; linarith)
  · calc (1 + x) ^ r ≤ (2 * x) ^ r := pow_le_pow_left₀ (by positivity) (by linarith) r
      _ = 2 ^ r * x ^ r := mul_pow _ _ _
      _ ≤ 2 ^ r * (1 + x ^ r) := by gcongr; linarith

private theorem wdec_of (D : Dat ℚ E) (P : CuspSub E 2) (hL : ∀ f ∈ P.V, Pp.Lf f.1)
    (hB : ∀ f ∈ P.V, ∃ B : ℝ, ∀ g, ‖f.1 g‖ ≤ B) (f : Sm E 2) (hf : f ∈ P.V) (C : Set (GL (Fin 2) (A E))) (hC : IsCompact C) :
    ∃ K : Set (FiniteAdeleRing (𝓞 ℚ) ℚ), IsCompact K ∧ ∀ r : ℕ, ∃ B : ℝ,
      ∀ y : (A ℚ)ˣ, ∀ k ∈ C, ‖Wo D f.1 (em E (aE y) * k)‖ ≤ B * ((1 + |re y|) ^ r)⁻¹ ∧
        (Wo D f.1 (em E (aE y) * k) ≠ 0 → (y : A ℚ).2 ∈ K) := by
  obtain ⟨K, hK, hs⟩ := UpperTheory.whittakerCoeff_ne_zero_finiteAdele_mem_compact E D f (P.cusp f hf).1 (hL f hf) C hC
  refine ⟨K, hK, fun r => ?_⟩
  obtain ⟨B₀, h₀⟩ := pow_bound D P hL hB 0 f hf C hC
  obtain ⟨B₁, h₁⟩ := pow_bound D P hL hB r f hf C hC
  refine ⟨2 ^ r * (B₀ + B₁), fun y k hk => ⟨?_, hs y k hk⟩⟩
  have h0 := h₀ y k hk
  have h1 := h₁ y k hk
  rw [pow_zero, one_mul] at h0
  have hp : 0 < (1 + |re (y : A ℚ)|) ^ r := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hp]
  calc ‖Wo D f.1 (em E (aE y) * k)‖ * (1 + |re (y : A ℚ)|) ^ r
      ≤ ‖Wo D f.1 (em E (aE y) * k)‖ * (2 ^ r * (1 + |re (y : A ℚ)| ^ r)) := by
        gcongr
        exact one_add_pow_le _ (abs_nonneg _) r
    _ = 2 ^ r * (‖Wo D f.1 (em E (aE y) * k)‖ + |re (y : A ℚ)| ^ r * ‖Wo D f.1 (em E (aE y) * k)‖) := by ring
    _ ≤ 2 ^ r * (B₀ + B₁) := by gcongr

private def Adm' (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) : Prop :=
  admitted D ω φ ∧ ∀ g, ∫ b in fundamentalSet E, φ (gl (nU b) * g) ∂(adeleMeasure E) = 0

private theorem Adm'.zero' (D : Dat ℚ E) (ω : HChar ℚ) : Adm' D ω (0 : GL (Fin 2) (A E) → ℂ) := by
  refine ⟨⟨continuous_const, fun _ _ => rfl, fun _ _ => by simp, fun _ => by simp, ⟨0, fun _ => by simp⟩,
    fun _ _ _ _ _ => ⟨0, fun _ _ _ _ _ => by simp⟩, fun _ _ => ⟨∅, isCompact_empty, fun _ => ⟨0, fun y k _ => ?_⟩⟩⟩, fun _ => by simp⟩
  have : Wo D (0 : GL (Fin 2) (A E) → ℂ) (em E (aE y) * k) = 0 := by simp [Wo]
  simp [this]

private theorem Adm'.add {D : Dat ℚ E} {ω : HChar ℚ} {φ φ' : GL (Fin 2) (A E) → ℂ} (h : Adm' D ω φ) (h' : Adm' D ω φ') :
    Adm' D ω (φ + φ') := by
  obtain ⟨a, a0⟩ := h
  obtain ⟨b, b0⟩ := h'
  have hc : Continuous (φ + φ') := a.cont.add b.cont
  have hl : ∀ γ g, (φ + φ') (ratGL E 2 γ * g) = (φ + φ') g := fun γ g => by simp [a.left, b.left]
  have hz : ∀ g, ∫ x in fundamentalSet E, (φ + φ') (gl (nU x) * g) ∂(adeleMeasure E) = 0 := fun g => by
    have hi : ∀ {u : GL (Fin 2) (A E) → ℂ}, Continuous u → IntegrableOn (fun x => u (gl (nU x) * g)) (fundamentalSet E) (adeleMeasure E) :=
      fun hu => Pp.intOn (hu.comp (Pp.cont_n.mul continuous_const))
    simp only [Pi.add_apply]
    rw [integral_add (hi a.cont) (hi b.cont), a0, b0, add_zero]
  refine ⟨⟨hc, hl, fun z g => by simp [a.cen, b.cen, mul_add], UpperTheory.integral_unipotentCoordinates_eq_zero_of_cuspidal E D _ ⟨hc, hl⟩ hz, ?_, ?_, ?_⟩, hz⟩
  · obtain ⟨B, hB⟩ := a.bdd
    obtain ⟨B', hB'⟩ := b.bdd
    exact ⟨B + B', fun g => (norm_add_le _ _).trans (add_le_add (hB g) (hB' g))⟩
  · intro C hC c hc r
    obtain ⟨B, hB⟩ := a.decay C hC c hc r
    obtain ⟨B', hB'⟩ := b.decay C hC c hc r
    refine ⟨B + B', fun x y k hk hy => ?_⟩
    rw [add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hB x y k hk hy) (hB' x y k hk hy))
  · intro C hC
    obtain ⟨K, hK, h⟩ := a.wdec C hC
    obtain ⟨K', hK', h'⟩ := b.wdec C hC
    refine ⟨K ∪ K', hK.union hK', fun r => ?_⟩
    obtain ⟨B, hB⟩ := h r
    obtain ⟨B', hB'⟩ := h' r
    refine ⟨B + B', fun y k hk => ?_⟩
    have e := (UpperTheory.whittakerPeriod_add_smul_and_norm_le E D).1 φ φ' a.cont b.cont (em E (aE y) * k)
    obtain ⟨u, v⟩ := hB y k hk
    obtain ⟨u', v'⟩ := hB' y k hk
    rw [e, add_mul]
    refine ⟨(norm_add_le _ _).trans (add_le_add u u'), fun hne => ?_⟩
    by_cases h0 : Wo D φ (em E (aE y) * k) = 0
    · exact Or.inr (v' fun h1 => hne (by rw [h0, h1, add_zero]))
    · exact Or.inl (v h0)

private theorem Adm'.smul {D : Dat ℚ E} {ω : HChar ℚ} {φ : GL (Fin 2) (A E) → ℂ} (c : ℂ) (h : Adm' D ω φ) :
    Adm' D ω (c • φ) := by
  obtain ⟨a, a0⟩ := h
  have hc : Continuous (c • φ) := a.cont.const_smul c
  have hl : ∀ γ g, (c • φ) (ratGL E 2 γ * g) = (c • φ) g := fun γ g => by simp [a.left]
  have hz : ∀ g, ∫ x in fundamentalSet E, (c • φ) (gl (nU x) * g) ∂(adeleMeasure E) = 0 := fun g => by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, a0, mul_zero]
  refine ⟨⟨hc, hl, fun z g => by simp [a.cen, mul_left_comm], UpperTheory.integral_unipotentCoordinates_eq_zero_of_cuspidal E D _ ⟨hc, hl⟩ hz, ?_, ?_, ?_⟩, hz⟩
  · obtain ⟨B, hB⟩ := a.bdd
    refine ⟨‖c‖ * B, fun g => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hB g) (norm_nonneg _)
  · intro C hC c' hc' r
    obtain ⟨B, hB⟩ := a.decay C hC c' hc' r
    refine ⟨‖c‖ * B, fun x y k hk hy => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hB x y k hk hy) (norm_nonneg _)
  · intro C hC
    obtain ⟨K, hK, h⟩ := a.wdec C hC
    refine ⟨K, hK, fun r => ?_⟩
    obtain ⟨B, hB⟩ := h r
    refine ⟨‖c‖ * B, fun y k hk => ?_⟩
    obtain ⟨u, v⟩ := hB y k hk
    have e := (UpperTheory.whittakerPeriod_add_smul_and_norm_le E D).2.1 c φ (em E (aE y) * k)
    rw [e, norm_mul, mul_assoc]
    exact ⟨mul_le_mul_of_nonneg_left u (norm_nonneg _), fun hne => v (right_ne_zero_of_mul hne)⟩

private theorem wo_translate (D : Dat ℚ E) (f : GL (Fin 2) (A E) → ℂ) (h g : GL (Fin 2) (A E)) :
    Wo D (fun x => f (x * h)) g = Wo D f (g * h) := by
  simp only [Wo, mul_assoc]

private theorem admissible_two_sided_translate (hD : DecE) (D : Dat ℚ E) (P : CuspSub E 2) (ω : HChar ℚ) (hc : CenN P ω) (hu : Unit1 ω)
    (f : Sm E 2) (hf : f ∈ P.V) (h : GL (Fin 2) (A E)) : Adm' D ω fun g => f.1 (g * h) := by
  have hL : ∀ f ∈ P.V, Pp.Lf f.1 := fun f hf => (hD E P f hf).1
  have hB : ∀ f ∈ P.V, ∃ B : ℝ, ∀ g, ‖f.1 g‖ ≤ B := UpperTheory.exists_bound_cuspForm_of_unitary_centralCharacter E P ω hc hu
  obtain ⟨hl, h0, hd⟩ := hD E P f hf
  have hcp : ∀ {C : Set (GL (Fin 2) (A E))}, IsCompact C → IsCompact ((· * h) '' C) := fun hC => hC.image (continuous_mul_const h)
  have hz : ∀ g, ∫ b in fundamentalSet E, f.1 (gl (nU b) * g * h) ∂(adeleMeasure E) = 0 := fun g => by
    simp only [mul_assoc]
    exact h0 _
  have hc' : Continuous fun g => f.1 (g * h) := hl.1.comp (continuous_mul_const h)
  have hl' : ∀ γ g, f.1 (ratGL E 2 γ * g * h) = f.1 (g * h) := fun γ g => by rw [mul_assoc, hl.2]
  refine ⟨⟨hc', hl', fun z g => ?_, UpperTheory.integral_unipotentCoordinates_eq_zero_of_cuspidal E D _ ⟨hc', hl'⟩ hz, ?_, ?_, ?_⟩, hz⟩
  · rw [mul_assoc, hc f hf]
  · obtain ⟨B, hB'⟩ := hB f hf
    exact ⟨B, fun g => hB' _⟩
  · intro C hC c hc r
    obtain ⟨B, hB'⟩ := hd _ (hcp hC) c hc r
    refine ⟨B, fun b a k hk ha => ?_⟩
    rw [mul_assoc]
    exact hB' b a _ ⟨k, hk, rfl⟩ ha
  · intro C hC
    obtain ⟨K, hK, hr⟩ := wdec_of D P hL hB f hf _ (hcp hC)
    refine ⟨K, hK, fun r => ?_⟩
    obtain ⟨B, hB'⟩ := hr r
    refine ⟨B, fun y k hk => ?_⟩
    simp only [wo_translate, mul_assoc]
    simpa only [mul_assoc] using hB' y (k * h) ⟨k, hk, rfl⟩

end Main

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.trAdm_of :
    DecE → TrAdm := by
  intro hD E _ _ _ D P ω χ hc hu _ φ hφ
  refine (Submodule.span_induction (p := fun φ _ => Adm' D ω φ) ?_ (Adm'.zero' D ω) (fun _ _ _ _ a b => a.add b)
    (fun c _ _ a => a.smul c) hφ).1
  rintro _ ⟨f, hf, h, rfl⟩
  exact admissible_two_sided_translate hD D P ω hc hu f hf h
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.WhittakerLieDerivativeLinear
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.SH

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

private theorem re_iy (y : ℝ) (hy : y ≠ 0) : re ((iy y : (A ℚ)ˣ) : A ℚ) = y := by
  have h : iy y = TR.infId ℚ ⟨fun _ => y, fun _ => y⁻¹, funext fun _ => mul_inv_cancel₀ hy, funext fun _ => inv_mul_cancel₀ hy⟩ := dif_neg hy
  have h2 : ∀ x, TR.pInf ℚ (TR.sInf ℚ x) = x := fun x => (TR.infEq ℚ).symm_apply_apply x
  rw [h, re]
  change TR.pInf ℚ (1 - TR.sInf ℚ 1 + TR.sInf ℚ (fun _ => y)) _ = y
  simp [h2]

private def Q (D : Dat ℚ E) (L N : ℕ) (f : Sm E 2) (X : Lie E 2) : Prop :=
  (∀ (y : (A ℚ)ˣ) x, Wo D (lie E 2 X f).1 (em E (aE y) * infGL E 2 x) ≠ 0 → ∀ v, Bad N v → Dv L v ((y : A ℚ) - 1)) ∧
  ∀ t ∈ UU, (∀ v, Dv L v ((t : A ℚ) - 1)) → ∀ (y : (A ℚ)ˣ) x,
    Wo D (lie E 2 X f).1 (em E (aE (y * t)) * infGL E 2 x) = Wo D (lie E 2 X f).1 (em E (aE y) * infGL E 2 x)

private theorem eig_smul {w : H.P E} {B : Multiset ℂˣ} {f : GL (Fin 2) (A E) → ℂ} (c : ℂ)
    (h : UpperTheory.V.Af.Smo.EigAt w B f) : UpperTheory.V.Af.Smo.EigAt w B (c • f) := fun g => by
  have h0 := h g
  refine ⟨h0.card, fun g' k hk => ?_, fun ϖ hϖ j hj g' => ?_⟩
  · simpa using congrArg (c * ·) (h0.inv g' k hk)
  · have h1 := h0.eig ϖ hϖ j hj g'
    simp only [Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [mul_left_comm, ← h1, ← smul_eq_mul, smul_finsum]
    exact finsum_congr fun x => by rw [smul_eq_mul, mul_left_comm]

private theorem gd_smul {D : Dat ℚ E} {P : CuspSub E 2} {L N : ℕ} {f : Sm E 2} {X : Lie E 2} {c : ℂ}
    (hG : Gd D P L N f.1) (hm : (lie E 2 X f).1 ∈ Tr P) (hQ : Q D L N f X) :
    Gd D P L N (c • (lie E 2 X f).1) := by
  have hs : ∀ h, Wo D (c • (lie E 2 X f).1) h = c * Wo D (lie E 2 X f).1 h := fun h => (UpperTheory.whittakerPeriod_add_smul_and_norm_le E D).2.1 c _ h
  refine ⟨hG.pos, hG.dvd, hG.same, (Tr P).smul_mem c hm, hG.pl, fun w hw => ?_, fun k hk g => ?_, fun y x hne => ?_, fun t ht hL y x => ?_⟩
  · obtain ⟨h1, B, h2, h3⟩ := hG.fix w hw
    refine ⟨fun g k hk => ?_, B, h2, eig_smul c (UpperTheory.lie_action_preserves_satake_eigen_at_place E w B f X h3)⟩
    simpa using congrArg (c * ·) (UpperTheory.lie_action_preserves_fixed_at_place E w f X h1 g k hk)
  · have := UpperTheory.lie_action_preserves_right_invariance_finite_adelic E k hk.1 f X (hG.lev k hk) g
    simpa using congrArg (c * ·) this
  · rw [hs] at hne
    exact hQ.1 y x (right_ne_zero_of_mul hne)
  · rw [hs, hs, hQ.2 t ht hL y x]

private theorem q_cv {D : Dat ℚ E} {P : CuspSub E 2} {L N : ℕ} {f : Sm E 2} (k : GL (Fin 2) (A E))
    (hG : Gd D P L N f.1) (hc : Continuous f.1) (hX : Continuous (lie E 2 (toL (XB D k)) f).1)
    (hB : ∃ B : ℝ, ∀ g, ‖(lie E 2 (toL (XB D k)) f).1 g‖ ≤ B) : Q D L N f (toL (XB D k)) := by
  obtain ⟨h0, hadd, hd, -⟩ := UpperTheory.archimedeanConjugateCurve_oneParameterSubgroup E D k
  have key : ∀ g, HasDerivAt (fun t : ℝ => Wo D f.1 (g * infGL E 2 (cv D k t)))
      (Wo D (lie E 2 (toL (XB D k)) f).1 g) 0 := fun g =>
    UpperTheory.hasDerivAt_whittakerPeriod_oneParameter E D f (cv D k) _ g h0 hadd hd hc hX hB
  refine ⟨fun y x hne v hv => ?_, fun t ht hL y x => ?_⟩
  · by_contra hcon
    have hz : (fun s : ℝ => Wo D f.1 (em E (aE y) * infGL E 2 x * infGL E 2 (cv D k s))) = fun _ => 0 := funext fun s => by
      by_contra h1
      rw [mul_assoc, ← map_mul] at h1
      exact hcon (hG.supp y _ h1 v hv)
    have h2 := key (em E (aE y) * infGL E 2 x)
    rw [hz] at h2
    exact hne (h2.unique (hasDerivAt_const _ _))
  · have h1 := key (em E (aE (y * t)) * infGL E 2 x)
    have h2 := key (em E (aE y) * infGL E 2 x)
    have e : (fun s : ℝ => Wo D f.1 (em E (aE (y * t)) * infGL E 2 x * infGL E 2 (cv D k s))) =
        fun s : ℝ => Wo D f.1 (em E (aE y) * infGL E 2 x * infGL E 2 (cv D k s)) := funext fun s => by
      rw [mul_assoc, mul_assoc, ← map_mul, hG.tor t ht hL y]
    rw [e] at h1
    exact h1.unique h2

private theorem lieDerivative_linear (f : Sm E 2) (a b c : ℝ) (X Y Z : Lie E 2) :
    (lie E 2 (a • X + b • Y + c • Z) f).1 = (a : ℂ) • (lie E 2 X f).1 + (b : ℂ) • (lie E 2 Y f).1 + (c : ℂ) • (lie E 2 Z f).1 := by
  rw [map_add (f := _), map_add (f := _), map_smul, map_smul, map_smul]
  funext g
  simp

private theorem whittaker_lieDerivative_linear {D : Dat ℚ E} {f : Sm E 2} (hc : ∀ X, Continuous (lie E 2 X f).1) (a b c : ℝ) (X Y Z : Lie E 2)
    (h : GL (Fin 2) (A E)) :
    Wo D (lie E 2 (a • X + b • Y + c • Z) f).1 h = a * Wo D (lie E 2 X f).1 h + b * Wo D (lie E 2 Y f).1 h + c * Wo D (lie E 2 Z f).1 h := by
  obtain ⟨h1, h2, -⟩ := UpperTheory.whittakerPeriod_add_smul_and_norm_le E D
  rw [lieDerivative_linear, h1 _ _ (((hc X).const_smul _).add ((hc Y).const_smul _)) ((hc Z).const_smul _),
    h1 _ _ ((hc X).const_smul _) ((hc Y).const_smul _), h2, h2, h2]

private theorem quadraticCondition_linear {D : Dat ℚ E} {L N : ℕ} {f : Sm E 2} (hc : ∀ X, Continuous (lie E 2 X f).1) (a b c : ℝ) {X Y Z : Lie E 2}
    (hX : Q D L N f X) (hY : Q D L N f Y) (hZ : Q D L N f Z) : Q D L N f (a • X + b • Y + c • Z) := by
  refine ⟨fun y x hne v hv => ?_, fun t ht hL y x => ?_⟩
  · rw [whittaker_lieDerivative_linear hc] at hne
    by_contra hcon
    have h1 : Wo D (lie E 2 X f).1 (em E (aE y) * infGL E 2 x) = 0 := by
      by_contra h; exact hcon (hX.1 y x h v hv)
    have h2 : Wo D (lie E 2 Y f).1 (em E (aE y) * infGL E 2 x) = 0 := by
      by_contra h; exact hcon (hY.1 y x h v hv)
    have h3 : Wo D (lie E 2 Z f).1 (em E (aE y) * infGL E 2 x) = 0 := by
      by_contra h; exact hcon (hZ.1 y x h v hv)
    exact hne (by rw [h1, h2, h3]; ring)
  · rw [whittaker_lieDerivative_linear hc, whittaker_lieDerivative_linear hc, hX.2 t ht hL y x, hY.2 t ht hL y x, hZ.2 t ht hL y x]

private theorem xb_dec (D : Dat ℚ E) (t : ℝ) :
    toL (XB D (em E (rot t))) = (Real.cos t ^ 2) • toL (XB D (em E (rot 0))) + (Real.sin t ^ 2) • toL (XB D (em E (rot (Real.pi / 2)))) +
      (Real.cos t * Real.sin t) • ((2 : ℝ) • toL (XB D (em E (rot (Real.pi / 4)))) + (-1 : ℝ) • toL (XB D (em E (rot 0))) +
        (-1 : ℝ) • toL (XB D (em E (rot (Real.pi / 2))))) := by
  have c4 : Real.cos (Real.pi / 4) ^ 2 = 1 / 2 := by
    rw [Real.cos_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have s4 : Real.sin (Real.pi / 4) ^ 2 = 1 / 2 := by
    rw [Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have m4 : Real.cos (Real.pi / 4) * Real.sin (Real.pi / 4) = 1 / 2 := by
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four, ← pow_two, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  rw [UpperTheory.conj_lie_element_embed_rotation_eq_trig_matrix E D t, UpperTheory.conj_lie_element_embed_rotation_eq_trig_matrix E D 0, UpperTheory.conj_lie_element_embed_rotation_eq_trig_matrix E D (Real.pi / 2), UpperTheory.conj_lie_element_embed_rotation_eq_trig_matrix E D (Real.pi / 4), c4, s4, m4]
  simp only [Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two]
  funext i j w
  fin_cases i <;> fin_cases j <;> simp <;> ring

end UpperTheory.ConvolutionTheory.RankTwoDescent.SH

open UpperTheory.ConvolutionTheory.RankTwoDescent.SH in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.shift_of :
    TrAdm → Shift := by
  intro hT E _ _ _ D P ω χ hC hU hχ L N φ hG
  have adm := hT E D P ω χ hC hU hχ
  obtain ⟨f, rfl, -⟩ := UpperTheory.exists_smooth_lie_action_mem_cuspidal_translates E P 0 φ hG.mem
  have hmem : ∀ X, (lie E 2 X f).1 ∈ Tr P := fun X => by
    obtain ⟨f', hf', hm⟩ := UpperTheory.exists_smooth_lie_action_mem_cuspidal_translates E P X f.1 hG.mem
    rwa [show f' = f from Subtype.ext hf'] at hm
  have hc : ∀ X, Continuous (lie E 2 X f).1 := fun X => (adm _ (hmem X)).cont
  have hb : ∀ X, ∃ B : ℝ, ∀ g, ‖(lie E 2 X f).1 g‖ ≤ B := fun X => (adm _ (hmem X)).bdd
  have hf0 := adm _ hG.mem
  have hq : ∀ k, Q D L N f (toL (XB D k)) := fun k => q_cv k hG hf0.cont (hc _) (hb _)
  set b0 : Lie E 2 := toL (XB D (em E (rot 0))) with hb0
  set b1 : Lie E 2 := toL (XB D (em E (rot (Real.pi / 2)))) with hb1
  set b2 : Lie E 2 := toL (XB D (em E (rot (Real.pi / 4)))) with hb2
  set b3 : Lie E 2 := (2 : ℝ) • b2 + (-1 : ℝ) • b0 + (-1 : ℝ) • b1 with hb3
  have hq3 : Q D L N f b3 := quadraticCondition_linear hc _ _ _ (hq _) (hq _) (hq _)
  set κ : ℂ := (2 * Real.pi * Complex.I)⁻¹ with hκ
  have hκ0 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  refine ⟨κ • (lie E 2 b1 f).1, κ • (lie E 2 b3 f).1, κ • (lie E 2 b0 f).1, gd_smul hG (hmem _) (hq _), gd_smul hG (hmem _) hq3,
    gd_smul hG (hmem _) (hq _), fun y t hy => ?_⟩
  obtain ⟨-, h2, -⟩ := UpperTheory.whittakerPeriod_add_smul_and_norm_le E D
  have e := UpperTheory.whittakerCoeff_lieDeriv_unipotent_eq_mul E D f ⟨hf0.cont, hf0.left⟩ (fun X => ⟨hc X, hb X⟩) (iy y) (em E (rot t))
  rw [xb_dec D t, whittaker_lieDerivative_linear hc, re_iy y hy, ← map_mul] at e
  rw [h2, h2, h2]
  have e' : (y : ℂ) * Wo D f.1 (em E (aE (iy y) * rot t)) = κ * ((2 * Real.pi * Complex.I * (y : ℂ)) * Wo D f.1 (em E (aE (iy y) * rot t))) := by
    rw [hκ]; field_simp
  rw [e', ← e, hκ]
  push_cast
  ring

end
end

