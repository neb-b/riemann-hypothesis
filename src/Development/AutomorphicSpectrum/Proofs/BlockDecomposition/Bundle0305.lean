module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import GroundTheory.AutomorphicForms.Bundle0024
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAvoidOne
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuationAlt
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0285
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsGradedMapGlueD

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PermutationBlockCounts
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.CellSizes

theorem card_blk_fiber {α : Type} {N : ℕ} {m : α → Type} [DecidableEq α] [∀ i, Fintype (m i)]
    (e : (Σ i, m i) ≃ Fin N) (i : α) :
    (Finset.univ.filter fun x : Fin N => blk e x = i).card = Fintype.card (m i) := by
  have h : (Finset.univ.filter fun x : Fin N => blk e x = i) =
      (Finset.univ : Finset (m i)).map
        ⟨fun y => e ⟨i, y⟩, fun a b hab => by simpa using e.injective hab⟩ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro rfl
      exact ⟨(e.symm x).2, e.apply_symm_apply x⟩
    · rintro ⟨y, rfl⟩
      exact blk_apply e i y
  rw [h, Finset.card_map, Finset.card_univ]

theorem sizes_sum : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (e' : (Σ j, m' j) ≃ Fin N) (w : Equiv.Perm (Fin N)), (∀ i, ∑ j, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = Fintype.card (m i)) ∧ ∀ j, ∑ i, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = Fintype.card (m' j) := by
  intro α _ _ N m _ _ β' _ _ m' _ _ e e' w
  constructor
  · intro i
    have h := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter fun x : Fin N => blk e x = i)
      (t := (Finset.univ : Finset β')) (f := fun x => blk e' (w.symm x))
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    simp only [Finset.filter_filter] at h
    rw [← h]
    exact card_blk_fiber e i
  · intro j
    have h := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter fun x : Fin N => blk e' (w.symm x) = j)
      (t := (Finset.univ : Finset α)) (f := fun x => blk e x)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    simp only [Finset.filter_filter] at h
    have h2 : (Finset.univ.filter fun x : Fin N => blk e' (w.symm x) = j).card =
        (Finset.univ.filter fun y : Fin N => blk e' y = j).card :=
      Finset.card_equiv w.symm (by simp)
    simp only [and_comm (a := blk e _ = _)]
    rw [← h, h2]
    exact card_blk_fiber e' j

end GlobalTheory.CompanionTheory.CellSizes
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RadicalSubspaceFacts
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.RadicalForm

variable {K : Type} [Field K] {n : ℕ}

noncomputable def cols (S : Submodule K (Fin n → K)) : Fin (Module.finrank K S) → (Fin n → K) :=
  fun j => (Module.finBasis K S j : Fin n → K)

theorem cols_li (S : Submodule K (Fin n → K)) : LinearIndependent K (cols S) :=
  (Module.finBasis K S).linearIndependent.map' S.subtype S.ker_subtype

theorem cols_span (S : Submodule K (Fin n → K)) : Submodule.span K (Set.range (cols S)) = S := by
  have h : Set.range (cols S) = S.subtype '' Set.range (Module.finBasis K S) := by
    rw [← Set.range_comp]; rfl
  rw [h, Submodule.span_image, (Module.finBasis K S).span_eq, Submodule.map_top,
    Submodule.range_subtype]

def form (σ : K →+* K) (D : Matrix (Fin n) (Fin n) K) (u v : Fin n → K) : K :=
  (fun i => σ (u i)) ⬝ᵥ (D *ᵥ v)

theorem form_add_left (σ : K →+* K) (D : Matrix (Fin n) (Fin n) K) (u u' v : Fin n → K) :
    form σ D (u + u') v = form σ D u v + form σ D u' v := by
  simp [form, dotProduct, add_mul, Finset.sum_add_distrib]

theorem form_smul_left (σ : K →+* K) (D : Matrix (Fin n) (Fin n) K) (c : K) (u v : Fin n → K) :
    form σ D (c • u) v = σ c * form σ D u v := by
  simp [form, dotProduct, Finset.mul_sum, mul_assoc]

theorem form_zero_left (σ : K →+* K) (D : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    form σ D 0 v = 0 := by
  simp [form, dotProduct]

theorem mem_perpD (σ : K →+* K) (d : GL (Fin n) K) (W : Submodule K (Fin n → K)) (v : Fin n → K) :
    v ∈ perpD σ d W ↔ ∀ x ∈ W, form σ (d⁻¹).val x v = 0 := by
  have h1 : d.val * (d⁻¹).val = 1 := Units.mul_inv d
  have h2 : (d⁻¹).val * d.val = 1 := Units.inv_mul d
  constructor
  · rintro ⟨y, hy, rfl⟩ x hx
    have hy' : ∀ x ∈ W, ∑ i, σ (x i) * y i = 0 := hy
    have h3 : (d⁻¹).val *ᵥ (Matrix.toLin' d.val y) = y := by
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
    simp only [form, h3]
    exact hy' x hx
  · intro h
    refine ⟨(d⁻¹).val *ᵥ v, fun x hx => h x hx, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

theorem form_swap (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) (D γ : Matrix (Fin n) (Fin n) K)
    (hγ : D * γ = (D.map σ)ᵀ) (u v : Fin n → K) :
    form σ D u (γ *ᵥ v) = σ (form σ D v u) := by
  simp only [form, Matrix.mulVec_mulVec, hγ]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, mulVec, map_sum, map_mul, hσ, transpose_apply, map_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem entry {κ κ' : Type} [Fintype κ] [Fintype κ'] (σ : K →+* K)
    (D : Matrix (Fin n) (Fin n) K) (M : Matrix (Fin n) κ K) (N : Matrix (Fin n) κ' K) (i j) :
    ((M.map σ)ᵀ * D * N) i j = form σ D (fun k => M k i) (fun k => N k j) := by
  rw [Matrix.mul_assoc]; rfl

theorem entry_mulVec {κ κ' : Type} [Fintype κ] [Fintype κ'] (σ : K →+* K)
    (D : Matrix (Fin n) (Fin n) K) (M : Matrix (Fin n) κ K) (N : Matrix (Fin n) κ' K)
    (c : κ' → K) (i) :
    (((M.map σ)ᵀ * D * N) *ᵥ c) i = form σ D (fun k => M k i) (N *ᵥ c) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]; rfl

theorem exists_adapted (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) (d : GL (Fin n) K)
    (γ : Matrix (Fin n) (Fin n) K) (hγ : (d⁻¹).val * γ = ((d⁻¹).val.map σ)ᵀ)
    (W : Submodule K (Fin n → K)) (hW : W.map (Matrix.toLin' γ) = W) :
    ∃ (a b : ℕ) (B : Matrix (Fin n) (Fin a) K) (A : Matrix (Fin n) (Fin b) K),
      LinearIndependent K (fromCols B A)ᵀ ∧
      Submodule.span K (Set.range Bᵀ) = W ⊓ perpD σ d W ∧
      Submodule.span K (Set.range (fromCols B A)ᵀ) = W ∧
      ((fromCols B A).map σ)ᵀ * (d⁻¹).val * B = 0 ∧ (B.map σ)ᵀ * (d⁻¹).val * fromCols B A = 0 ∧
      ((A.map σ)ᵀ * (d⁻¹).val * A).det ≠ 0 := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (W ⊓ perpD σ d W)
  have hC : (W ⊓ perpD σ d W) ⊔ (Q ⊓ W) = W := by
    rw [← sup_inf_assoc_of_le Q (inf_le_left : W ⊓ perpD σ d W ≤ W), hQ.sup_eq_top, top_inf_eq]
  have hdis : Disjoint (W ⊓ perpD σ d W) (Q ⊓ W) := hQ.disjoint.mono_right inf_le_left
  obtain ⟨a, u, hu, hus⟩ : ∃ (a : ℕ) (u : Fin a → Fin n → K), LinearIndependent K u ∧
      Submodule.span K (Set.range u) = W ⊓ perpD σ d W := ⟨_, _, cols_li _, cols_span _⟩
  obtain ⟨b, v, hv, hvs⟩ : ∃ (b : ℕ) (v : Fin b → Fin n → K), LinearIndependent K v ∧
      Submodule.span K (Set.range v) = Q ⊓ W := ⟨_, _, cols_li _, cols_span _⟩
  have hum : ∀ j, u j ∈ W ⊓ perpD σ d W := fun j => hus ▸ Submodule.subset_span ⟨j, rfl⟩
  have hvm : ∀ j, v j ∈ Q ⊓ W := fun j => hvs ▸ Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin a) K, Bᵀ = u := ⟨(Matrix.of u)ᵀ, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin b) K, Aᵀ = v := ⟨(Matrix.of v)ᵀ, rfl⟩
  have hT : ((fromCols B A)ᵀ : _ → _ → K) = Sum.elim u v := by
    subst hB hA
    funext s k
    rcases s with j | j <;> rfl
  have hspan : Submodule.span K (Set.range (fromCols B A)ᵀ) = W := by
    rw [hT, Set.Sum.elim_range, Submodule.span_union, hus, hvs, hC]
  have hli : LinearIndependent K (fromCols B A)ᵀ := by
    rw [hT]
    exact hu.sum_type hv (by rw [hus, hvs]; exact hdis)
  have hFW : ∀ s, (fun k => fromCols B A k s) ∈ W := fun s => by
    have : (fun k => fromCols B A k s) ∈ Submodule.span K (Set.range (fromCols B A)ᵀ) :=
      Submodule.subset_span ⟨s, rfl⟩
    rwa [hspan] at this
  have hr : ∀ w ∈ W ⊓ perpD σ d W, ∀ x ∈ W, form σ (d⁻¹).val x w = 0 := fun w hw x hx =>
    (mem_perpD σ d W w).1 hw.2 x hx
  have hl : ∀ w ∈ W ⊓ perpD σ d W, ∀ x ∈ W, form σ (d⁻¹).val w x = 0 := fun w hw x hx => by
    rw [← hW] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    rw [Matrix.toLin'_apply, form_swap σ hσ _ γ hγ, hr w hw x' hx', map_zero]
  have hBc : ∀ j, (fun k => B k j) = u j := fun j => congrFun hB j
  have hAc : ∀ j, (fun k => A k j) = v j := fun j => congrFun hA j
  refine ⟨_, _, B, A, hli, by rw [hB]; exact hus, hspan, ?_, ?_, ?_⟩
  · ext i j
    rw [entry, hBc]
    exact hr _ (hum j) _ (hFW i)
  · ext i j
    rw [entry, hBc]
    exact hl _ (hum i) _ (hFW j)
  · intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hAv : A *ᵥ c = ∑ j, c j • v j := by
      rw [Matrix.mulVec_eq_sum, hA]
      exact Finset.sum_congr rfl fun j _ => op_smul_eq_smul _ _
    have hyC : A *ᵥ c ∈ Q ⊓ W := by
      rw [hAv]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvm j)
    have hyW : A *ᵥ c ∈ W := hyC.2
    have hcol : ∀ s, form σ (d⁻¹).val (fun k => fromCols B A k s) (A *ᵥ c) = 0 := by
      rintro (j | j)
      · have h := hl _ (hum j) _ hyW
        rw [← hBc j] at h
        exact h
      · have := congrFun hc j
        rw [entry_mulVec] at this
        exact this
    have hperp : A *ᵥ c ∈ perpD σ d W := by
      rw [mem_perpD]
      intro x hx
      rw [← hspan] at hx
      induction hx using Submodule.span_induction with
      | mem x h =>
        obtain ⟨s, rfl⟩ := h
        exact hcol s
      | zero => exact form_zero_left _ _ _
      | add x y _ _ hx hy => rw [form_add_left, hx, hy, add_zero]
      | smul a x _ hx => rw [form_smul_left, hx, mul_zero]
    have hy0 : A *ᵥ c = 0 := by
      have := hdis.le_bot (show A *ᵥ c ∈ _ from ⟨⟨hyW, hperp⟩, hyC⟩)
      simpa using this
    apply hc0
    have hsum : ∑ j, c j • v j = 0 := by rw [← hAv, hy0]
    funext j
    exact Fintype.linearIndependent_iff.1 hv c hsum j

theorem radical : Radical := by
  intro E _ _ _ n d W hW
  have hσ : ∀ x, conjE E (conjE E x) = x := fun x => NumberField.IsCMField.complexConj_apply_apply E x
  refine exists_adapted (conjE E) hσ d (nrm d).val ?_ W hW
  have h2 : (d⁻¹).val * d.val = 1 := Units.inv_mul d
  rw [nrm, Units.val_mul, ← mul_assoc, h2, one_mul, thetaR_val]

end GlobalTheory.CompanionTheory.RadicalForm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayClassPartialZetaIntegrality
section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Integrality

theorem eqOn_compl_one {H R : ℂ → ℂ} (hH : DifferentiableOn ℂ H {1}ᶜ) (hR : DifferentiableOn ℂ R {1}ᶜ)
    (h : ∀ s : ℂ, 1 < s.re → H s = R s) : Set.EqOn H R {1}ᶜ := by
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; first | exact Cardinal.one_lt_two | norm_num | exact_mod_cast (show (1:ℕ) < 2 by norm_num)) 1).isPreconnected
  have hmem : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by
    rw [Set.mem_compl_singleton_iff]; norm_num
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hnhds : {s : ℂ | 1 < s.re} ∈ nhds (2 : ℂ) := hopen.mem_nhds (by norm_num)
  exact (hH.analyticOnNhd isOpen_compl_singleton).eqOn_of_preconnected_of_eventuallyEq
    (hR.analyticOnNhd isOpen_compl_singleton) hconn hmem (Filter.eventually_of_mem hnhds fun s hs => h s hs)

theorem coneWeight_int {F : Type} [Field F] [NumberField F] {r : ℕ} (l : ℕ) (A : Ideal (𝓞 F)) (y : 𝓞 F)
    (v : Fin r → 𝓞 F) (m : Fin r → ℕ) : ∃ z : ℤ, coneWeight l A y v m = z := by
  unfold coneWeight
  split_ifs
  · exact ⟨(l : ℤ) - 1, by push_cast; ring⟩
  · exact ⟨-1, by push_cast; ring⟩

theorem exists_pow_mul_sum {J : Type} (S : Finset J) (l : ℕ) (q : J → ℚ) (K : J → ℕ) (z : J → ℤ)
    (h : ∀ j, (l : ℚ) ^ K j * q j = z j) : ∃ (K' : ℕ) (Z : ℤ), (l : ℚ) ^ K' * ∑ j ∈ S, q j = Z := by
  refine ⟨∑ j ∈ S, K j, ∑ j ∈ S, (l : ℤ) ^ (∑ i ∈ S, K i - K j) * z j, ?_⟩
  rw [Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hle : K j ≤ ∑ i ∈ S, K i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj
  rw [← h j, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem padicValRat_int_div_nonneg (l : ℕ) [Fact l.Prime] (Z : ℤ) (D : ℕ) (hD : D ≠ 0) (h : ¬ l ∣ D) :
    0 ≤ padicValRat l ((Z : ℚ) / (D : ℚ)) := by
  rcases eq_or_ne Z 0 with rfl | hZ
  · simp
  have hZ' : (Z : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hZ
  have hD' : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hD
  rw [padicValRat.div hZ' hD', padicValRat.of_int, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd h]
  simp

theorem classTwist_value_int : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 𝔠 : Ideal (𝓞 F)) (J : Type) [Fintype J] (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime → (∀ j i, v j i ∉ 𝔠 * 𝔟) → ∀ T : ℂ → ℂ, DifferentiableOn ℂ T {1}ᶜ → (∀ s : ℂ, 1 < s.re → HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} => (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) (T s)) → ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, T (1 - (k : ℂ)) = (q : ℂ) ∧ ∀ l : ℕ, l.Prime → l ≠ Ideal.absNorm 𝔠 → ¬ l ∣ Ideal.absNorm 𝔟 → 0 ≤ padicValRat l q := by
  intro F _ _ _ 𝔣 𝔞 𝔟 𝔠 J _ r y v hP h𝔠 hN hv T hT hS k hk
  obtain ⟨hb, hy, hvv, hr, e, he⟩ := hP
  letI : Fintype (F →+* ℝ) := Fintype.ofEquiv (F →+* ℂ) (realEmbeddingsEquiv F).symm
  set l := Ideal.absNorm 𝔠 with hl_def
  have hl0 : 0 < l := hN.pos
  have hcard : Fintype.card (F →+* ℝ) = Module.finrank ℚ F := by
    rw [Fintype.card_congr (realEmbeddingsEquiv F)]
    convert NumberField.Embeddings.card F ℂ
  have hNb : Ideal.absNorm 𝔟 ≠ 0 := fun h => hb (Ideal.absNorm_eq_zero_iff.mp h)
  have hNbC : ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hNb
  have hw : ∀ j, GoodWeight l (coneWeight l (𝔠 * 𝔟) (y j) (v j)) := fun j =>
    goodWeight_coneWeight hb hN (hy j).1 (fun i => (hvv j i).1) (hv j)
  have hcont : ∀ j, ∃ Tj : ℂ → ℂ, Differentiable ℂ Tj ∧
      (∀ s : ℂ, 1 < s.re → HasSum (fun m => (coneWeight l (𝔠 * 𝔟) (y j) (v j) m : ℂ) *
        coneTerm (fun (σ : F →+* ℝ) i => σ ((v j i : 𝓞 F) : F)) (fun (σ : F →+* ℝ) => σ ((y j : 𝓞 F) : F)) s m) (Tj s)) := by
    intro j
    obtain ⟨Tj, hd, hs, -⟩ := abelContinuation (F →+* ℝ) (r j) l (fun (σ : F →+* ℝ) i => σ ((v j i : 𝓞 F) : F))
      (fun (σ : F →+* ℝ) => σ ((y j : 𝓞 F) : F)) (coneWeight l (𝔠 * 𝔟) (y j) (v j)) (by rw [hcard]; exact hr j) hl0
      (fun σ i => (hvv j i).2 σ) (fun σ => (hy j).2 σ) (hw j)
    exact ⟨Tj, hd, hs⟩
  choose Tc hTcd hTcs using hcont
  have key : ∀ (s : ℂ) (p : (j : J) × (Fin (r j) → ℕ)),
      (classWeight l 𝔠 (e p).1 : ℂ) * ((Ideal.absNorm (e p).1 : ℕ) : ℂ) ^ (-s) =
        ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s * ((coneWeight l (𝔠 * 𝔟) (y p.1) (v p.1) p.2 : ℂ) *
          coneTerm (fun (σ : F →+* ℝ) i => σ ((v p.1 i : 𝓞 F) : F)) (fun (σ : F →+* ℝ) => σ ((y p.1 : 𝓞 F) : F)) s p.2) := by
    rintro s ⟨j, m⟩
    dsimp only
    have hx : (e ⟨j, m⟩).1 * 𝔟 = Ideal.span {conePt (y j) (v j) m} := he ⟨j, m⟩
    have hwt : classWeight l 𝔠 (e ⟨j, m⟩).1 = coneWeight l (𝔠 * 𝔟) (y j) (v j) m := by
      unfold classWeight coneWeight
      rw [le_iff_mem_mul_of_span (𝔠 := 𝔠) hb hx]
    have hnorm : Ideal.absNorm (Ideal.span {conePt (y j) (v j) m}) =
        Ideal.absNorm (e ⟨j, m⟩).1 * Ideal.absNorm 𝔟 := by rw [← hx, map_mul]
    rw [hwt, coneTerm_eq_absNorm_cpow (hy j).2 (fun i => (hvv j i).2) s m, hnorm, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow, mul_left_comm (((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s),
      mul_left_comm (((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s), ← Complex.cpow_add _ _ hNbC, add_neg_cancel,
      Complex.cpow_zero, mul_one]
  have hRs : ∀ s : ℂ, 1 < s.re → T s = ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s * ∑ j, Tc j s := by
    intro s hs
    have h1 := (e.hasSum_iff.mpr (hS s hs))
    have h2 : HasSum (fun p : (j : J) × (Fin (r j) → ℕ) => ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s *
        ((coneWeight l (𝔠 * 𝔟) (y p.1) (v p.1) p.2 : ℂ) *
          coneTerm (fun (σ : F →+* ℝ) i => σ ((v p.1 i : 𝓞 F) : F)) (fun (σ : F →+* ℝ) => σ ((y p.1 : 𝓞 F) : F)) s p.2)) (T s) := by
      convert h1 using 1
      funext p
      exact (key s p).symm
    have h3 := h2.sigma (fun j => (hTcs j s hs).mul_left (((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s))
    rw [Finset.mul_sum]
    exact h3.unique (hasSum_fintype _)
  have hRd : DifferentiableOn ℂ (fun s => ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s * ∑ j, Tc j s) {1}ᶜ := by
    intro s _
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.mul
    · exact differentiableAt_id.const_cpow (Or.inl hNbC)
    · have hsd := DifferentiableAt.sum (u := Finset.univ) (fun j _ => hTcd j s)
      have hfun : (fun t => ∑ j, Tc j t) = ∑ j, Tc j := by
        funext t
        simp [Finset.sum_apply]
      rw [hfun]
      exact hsd
  have heq := eqOn_compl_one hT hRd (fun s hs => hRs s hs)
  have hint : ∀ j, ∃ (qj : ℚ) (K : ℕ) (z : ℤ), Tc j (-((k - 1 : ℕ) : ℂ)) = qj ∧ (l : ℚ) ^ K * qj = z := by
    intro j
    refine GlobalTheory.T.cone_zeta_special_value_denominator_bound (F →+* ℝ) (r j) l (fun (σ : F →+* ℝ) i => σ ((v j i : 𝓞 F) : F)) (fun (σ : F →+* ℝ) => σ ((y j : 𝓞 F) : F))
      (coneWeight l (𝔠 * 𝔟) (y j) (v j)) (by rw [hcard]; exact hr j) hl0 (fun σ i => (hvv j i).2 σ)
      (fun σ => (hy j).2 σ) (hw j) (fun m => coneWeight_int l _ _ _ m) (Tc j) (hTcd j).differentiableOn
      (hTcs j) (k - 1) (fun m => ?_)
    have h1 : ∏ σ : F →+* ℝ, (σ ((y j : 𝓞 F) : F) + ∑ i, σ ((v j i : 𝓞 F) : F) * (m i : ℝ)) =
        ((Ideal.absNorm (Ideal.span {conePt (y j) (v j) m}) : ℕ) : ℝ) := by
      rw [← prod_real_embeddings_eq_absNorm _ (totPos_conePt (hy j).2 (fun i => (hvv j i).2) m)]
      exact Finset.prod_congr rfl fun σ _ => (embedding_conePt σ (y j) (v j) m).symm
    refine ⟨(Ideal.absNorm (Ideal.span {conePt (y j) (v j) m})) ^ (k - 1), ?_⟩
    try beta_reduce
    rw [Finset.prod_pow, h1]
    first | norm_cast | (push_cast; ring) | simp
  choose qj Kj zj hqj hzj using hint
  obtain ⟨K', Z, hZ⟩ := exists_pow_mul_sum Finset.univ l qj Kj zj hzj
  have hs0 : (1 - (k : ℂ)) = -(((k - 1 : ℕ)) : ℂ) := by rw [Nat.cast_sub hk]; push_cast; ring
  have hmem : (1 - (k : ℂ)) ∈ ({1}ᶜ : Set ℂ) := by
    rw [Set.mem_compl_singleton_iff, Ne, sub_eq_self]; exact_mod_cast (by omega : k ≠ 0)
  have hval : T (1 - (k : ℂ)) = ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ (1 - (k : ℂ)) * ∑ j, (qj j : ℂ) := by
    rw [heq hmem]
    dsimp only
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hs0]; exact hqj j
  have hlK : (l : ℚ) ^ K' ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hl0.ne')
  have hsum : ∑ j, qj j = (Z : ℚ) / (l : ℚ) ^ K' := by
    rw [eq_div_iff hlK, mul_comm]; exact hZ
  have hD : l ^ K' * Ideal.absNorm 𝔟 ^ (k - 1) ≠ 0 := mul_ne_zero (pow_ne_zero _ hl0.ne') (pow_ne_zero _ hNb)
  refine ⟨(Z : ℚ) / ((l ^ K' * Ideal.absNorm 𝔟 ^ (k - 1) : ℕ) : ℚ), ?_, ?_⟩
  · rw [hval, hs0, Complex.cpow_neg, Complex.cpow_natCast, ← Rat.cast_sum, hsum]
    push_cast
    ring
  · intro l' hl' hne hndvd
    haveI := Fact.mk hl'
    apply padicValRat_int_div_nonneg l' Z _ hD
    intro hdvd
    rcases (Nat.Prime.dvd_mul hl').mp hdvd with h | h
    · exact hne ((Nat.prime_dvd_prime_iff_eq hl' hN).mp (hl'.dvd_of_dvd_pow h))
    · exact hndvd (hl'.dvd_of_dvd_pow h)

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Integrality
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionCompatibleIteratedInjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

namespace GlobalTheory.CompanionTheory.FormalAlg.IterInj

theorem restriction_compatible_iterated_injective (ι : Type) [LinearOrder ι] (A : Type) [CommRing A] (P : Finset ι → Type)
    [∀ S, AddCommGroup (P S)] [∀ S, Module (MvPolynomial ι A) (P S)]
    (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S')
    (hid : ∀ S (h : S ⊆ S) a, res S S h a = a)
    (hcomp : ∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a,
      res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a)
    (hloc : ∀ (S : Finset ι) (j : ι) (a : P S), S.Nonempty →
      res S (insert j S) (Finset.subset_insert j S) a = 0 →
      ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • a = 0)
    (S : Finset ι) (hS : S.Nonempty) (T : Finset ι) :
    ∀ (S' : Finset ι) (_ : S' = S ∪ T) (h : S ⊆ S') (a : P S), res S S' h a = 0 →
      ∃ l : ℕ, xProd A T ^ l • a = 0 := by
  induction T using Finset.induction_on with
  | empty =>
    intro S' hS' h a ha
    have : S' = S := by simpa using hS'
    subst this
    refine ⟨0, ?_⟩
    rw [hid] at ha
    simpa using ha
  | insert j T' hj ih =>
    intro S' hS' h a ha
    have hS'' : S' = insert j (S ∪ T') := by
      rw [hS', Finset.union_insert]
    subst hS''
    have hsub : S ⊆ S ∪ T' := Finset.subset_union_left
    have hb : res (S ∪ T') (insert j (S ∪ T')) (Finset.subset_insert j _) (res S (S ∪ T') hsub a) = 0 := by
      rw [hcomp]; exact ha
    obtain ⟨k, hk⟩ := hloc (S ∪ T') j _ (hS.mono hsub) hb
    have h2 : res S (S ∪ T') hsub ((MvPolynomial.X j : MvPolynomial ι A) ^ k • a) = 0 := by
      rw [map_smul]; exact hk
    obtain ⟨l, hl⟩ := ih (S ∪ T') rfl hsub _ h2
    refine ⟨k + l, ?_⟩
    have hx : xProd A (insert j T') = MvPolynomial.X j * xProd A T' := by
      simp [xProd, Finset.prod_insert hj]
    have : (xProd A (insert j T')) ^ (k + l) =
        ((MvPolynomial.X j : MvPolynomial ι A) ^ l * xProd A T' ^ k) *
          (xProd A T' ^ l * (MvPolynomial.X j : MvPolynomial ι A) ^ k) := by
      rw [hx, mul_pow]; ring
    rw [this, mul_smul _ (xProd A T' ^ l * _), mul_smul (xProd A T' ^ l), hl, smul_zero]

theorem iter_localisation_injective : ∀ (ι : Type) [LinearOrder ι] (A : Type) [CommRing A] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S'), (∀ S (h : S ⊆ S) a, res S S h a = a) → (∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a) → (∀ (S : Finset ι) (j : ι) (a : P S), S.Nonempty → res S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • a = 0) → (∀ (T S : Finset ι) (a : P S), S.Nonempty → res S (S ∪ T) Finset.subset_union_left a = 0 → ∃ l : ℕ, xProd A T ^ l • a = 0) := by
  intro ι _ A _ P _ _ res hid hcomp hloc T S a hS ha
  exact restriction_compatible_iterated_injective ι A P res hid hcomp hloc S hS T (S ∪ T) rfl Finset.subset_union_left a ha

end GlobalTheory.CompanionTheory.FormalAlg.IterInj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeFinitePlaces
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.Dblock.SzFinProof

theorem finite_one_lt_norm_cW {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : Ad E) :
    {w : HeightOneSpectrum (𝓞 E) | 1 < ‖cW w a‖}.Finite := by
  delta PositivityTheory.Rg.BcB.cW GlobalTheory.CuspRep.pLoc GlobalTheory.CuspRep.pFin
  have h := RestrictedProduct.eventually _ _ (RingHom.snd (InfiniteAdeleRing E) (Af E) a)
  refine (Filter.eventually_cofinite.mp h).subset ?_
  intro w hw
  simp only [Set.mem_ofPred_eq, RingHom.comp_apply, RestrictedProduct.evalRingHom_apply] at hw ⊢
  intro hmem
  exact absurd hw (not_lt.mpr (Valued.toNormedField.norm_le_one_iff.mpr
    ((IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hmem)))

theorem szFin : SzFin := by
  intro E _ _ _ ι κ _ _ A
  refine (Set.Finite.biUnion (s := (Set.univ : Set (ι × κ))) Set.finite_univ
    fun p _ => finite_one_lt_norm_cW (A p.1 p.2)).subset ?_
  intro w hw
  change 1 < ⨆ p : ι × κ, ‖(A.map (PositivityTheory.Rg.BcB.cW w)) p.1 p.2‖ at hw
  rcases isEmpty_or_nonempty (ι × κ) with hι | hι
  · rw [Real.iSup_of_isEmpty] at hw
    exact absurd hw (by norm_num)
  · obtain ⟨p, hp⟩ := exists_lt_of_lt_ciSup hw
    exact Set.mem_biUnion (Set.mem_univ p) hp

end GlobalTheory.CompanionTheory.Dblock.SzFinProof
end

