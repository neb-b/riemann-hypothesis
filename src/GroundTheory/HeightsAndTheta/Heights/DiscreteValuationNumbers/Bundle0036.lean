module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleSectionFormsTools
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0031

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleSectionForms
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo FlagBundleSectionForms

noncomputable section

theorem FlagBundleSectionForms.proof : FlagBundleSectionForms.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hP _ N E _ _ B w b hfl M a φ hφ Φ _ _ t ht i
  have hc0 : ∀ k, ∃ j : ι k, y ⟨k, j⟩ ≠ 0 := by
    intro k
    obtain ⟨j, hj⟩ := hP.relevant k
    refine ⟨j, fun h0 => hj ?_⟩
    simp [pointIdeal, RingHom.mem_ker, pointConeMap, h0]
  choose c hY using hc0
  have hsc : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hY k
  obtain ⟨ψ, hψint, hψlow, hψi⟩ := exists_flag_dual y B w b hfl c hsc i
  obtain ⟨u, hu, hψ⟩ := hφ.generate c hsc ψ hψint
  have hstar : t i * algebraMap Ω Φ (chartPow y c (b i))⁻¹ =
      ∑ l, algebraMap Ω Φ (u l * chartPow y c (-a)) *
        projCoord y w φ (truncCoord t ((i : ℕ) + 1)) ⟨none, l⟩ := by
    have h1 : ∑ j, truncCoord t ((i : ℕ) + 1) j * algebraMap Ω Φ (ψ (w j)) =
        t i * algebraMap Ω Φ (chartPow y c (b i))⁻¹ := by
      rw [Finset.sum_eq_single i]
      · simp [truncCoord, hψi]
      · intro j _ hji
        rcases lt_or_gt_of_ne hji with h | h
        · simp [hψlow j h]
        · have : ¬ (j : ℕ) < (i : ℕ) + 1 := by
            have : (i : ℕ) < j := h
            omega
          simp [truncCoord, this]
      · simp
    rw [← h1, hψ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [projCoord, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      map_sum, map_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [chartPow, Pi.neg_apply]
    ring
  obtain ⟨n, U, hUh, hUe⟩ : ∃ (n : ℕ) (U : Fin M → MRing (bundleIdx ι M) F),
      (∀ l, IsMultiHomog (U l) (liftNat fun _ => n)) ∧
      ∀ l, eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1)))
        (U l) = algebraMap Ω Φ (u l * segreVec y c ^ n) := by
    have h := fun l => chartRing_forms y w φ (truncCoord t ((i : ℕ) + 1)) c hsc (hu l)
    choose n U hU hUe using h
    refine ⟨∑ l, n l, fun l => U l * chartMono M c (fun _ => ∑ l, n l - n l), fun l => ?_, fun l => ?_⟩
    · have hle : n l ≤ ∑ l, n l := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
      have hd : liftNat (K := K) (fun _ => ∑ l, n l) =
          liftNat (fun _ => n l) + liftNat (fun _ => ∑ l, n l - n l) := by
        funext o; cases o <;> simp [liftNat]; omega
      rw [hd]
      exact (hU l).mul (chartMono_homog M c _)
    · have hle : n l ≤ ∑ l, n l := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
      rw [eval₂_mul, hUe, eval_chartMono, ← map_mul]
      congr 1
      rw [Finset.prod_pow, mul_assoc, ← segreVec, ← pow_add, Nat.add_sub_cancel' hle]
  let α : K → ℕ := fun k => (|a k| + |b i k| - a k).toNat
  let β : K → ℕ := fun k => (|a k| + |b i k| + n - b i k).toNat
  have hid : segreVec y c ^ n * ∏ k, y ⟨k, c k⟩ ^ α k =
      (∏ k, y ⟨k, c k⟩ ^ β k) * chartPow y c (b i) * chartPow y c (-a) := by
    rw [segreVec_pow, ← chartPow_natCast, ← chartPow_natCast, ← chartPow_add hY, ← chartPow_add hY,
      ← chartPow_add hY]
    congr 1
    funext k
    have h1 := le_abs_self (a k)
    have h2 := neg_abs_le (a k)
    have h3 := le_abs_self (b i k)
    have h4 := neg_abs_le (b i k)
    simp only [Pi.add_apply, Pi.neg_apply, α, β]
    omega
  let f : MRing (bundleIdx ι M) F := ∑ l, U l * chartMono M c α * X ⟨none, l⟩
  let g : MRing (bundleIdx ι M) F := chartMono M c β
  have hg : eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) g
      = algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ β k) := eval_chartMono y w φ _ c β
  have hp : algebraMap Ω Φ (chartPow y c (b i)) ≠ 0 :=
    (map_ne_zero _).2 (chartPow_ne_zero hY _)
  have hf : eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) f
      = t i * eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
        (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) g := by
    rw [hg]
    calc _ = ∑ l, algebraMap Ω Φ (u l * chartPow y c (-a)) *
            projCoord y w φ (truncCoord t ((i : ℕ) + 1)) ⟨none, l⟩ *
            algebraMap Ω Φ ((∏ k, y ⟨k, c k⟩ ^ β k) * chartPow y c (b i)) := by
          simp only [f, eval₂_sum, eval₂_mul, eval₂_X, hUe, eval_chartMono]
          refine Finset.sum_congr rfl fun l _ => ?_
          have hl : algebraMap Ω Φ (u l * segreVec y c ^ n) * algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ α k) =
              algebraMap Ω Φ (u l * chartPow y c (-a)) *
                algebraMap Ω Φ ((∏ k, y ⟨k, c k⟩ ^ β k) * chartPow y c (b i)) := by
            rw [← map_mul, ← map_mul]
            congr 1
            rw [mul_assoc, hid]
            ring
          rw [mul_comm _ (projCoord _ _ _ _ _), mul_assoc, hl]
          ring
      _ = t i * algebraMap Ω Φ (chartPow y c (b i))⁻¹ *
            algebraMap Ω Φ ((∏ k, y ⟨k, c k⟩ ^ β k) * chartPow y c (b i)) := by
          rw [hstar, Finset.sum_mul]
      _ = t i * algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ β k) := by
          rw [map_inv₀, map_mul]
          field_simp
  have hg0 : eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
      (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) g ≠ 0 := by
    rw [hg]
    exact (map_ne_zero _).2 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hY k))
  refine ⟨fun o => Option.elim o 1 (fun k => n + α k), liftNat β, f, g, ?_, chartMono_homog M c β, ?_,
    fun hmem => ?_, fun hmem => ?_, hf⟩
  · refine IsWeightedHomogeneous.sum _ _ _ fun l _ => ?_
    have h := ((hUh l).mul (chartMono_homog (F := F) M c α)).mul
      (isWeightedHomogeneous_X F (blockWeight (bundleIdx ι M)) ⟨none, l⟩)
    convert h using 1
    funext o
    cases o <;> simp [liftNat, blockWeight, Pi.single_apply]
  · funext o
    cases o with
    | none => simp [liftNat, zetaDeg, liftDeg]
    | some k =>
      have h1 := le_abs_self (a k)
      have h2 := neg_abs_le (a k)
      have h3 := le_abs_self (b i k)
      have h4 := neg_abs_le (b i k)
      simp only [liftNat, zetaDeg, liftDeg, Option.elim, Pi.add_apply, Pi.sub_apply, α, β]
      omega
  · exact (mul_ne_zero (ht.ne_zero i) hg0) (hf ▸ eval_eq_zero_of_mem_projIdeal y w φ _ hmem)
  · exact hg0 (eval_eq_zero_of_mem_projIdeal y w φ _ hmem)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagLineSectionSplit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

set_option linter.unusedSectionVars false

namespace FlagLineSectionProof

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type*} [Field Ω] {F : Type*} [Field F]
  [Algebra F Ω] {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]

theorem exists_adapted (y : (Σ k, ι k) → Ω) (B : ChartBundle F (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hB : IsFlagFrame y B w b) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) (i : Fin N) :
    ∃ v ∈ B.lat c, (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = chartZ y c (b i) := by
  have h : chartZ y c (b i) ∈ degLat F y (b i) c := ⟨1, one_mem _, by simp [chartZ]⟩
  rw [← hB.graded c hc i] at h
  obtain ⟨v, hv, h1, h2⟩ := h
  exact ⟨v, hv, h1, h2⟩

theorem exists_dual_first (y : (Σ k, ι k) → Ω) (B : ChartBundle F (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hB : IsFlagFrame y B w b) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) (h0 : 0 < N) :
    ∃ ψ : Module.Dual Ω E, (∀ v ∈ B.lat c, ψ v ∈ chartRing F (segreVec y) c) ∧
      ψ (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩) = 1 := by
  have hlive := live_of_segreVec_ne_zero hc
  choose e he hup hdiag using exists_adapted y B w b hB c hc
  have hm : ∀ i, chartZ y c (b i) ≠ 0 := fun i => chartZ_ne_zero hlive _
  have hspan : ∀ n : ℕ, ∀ i : Fin N, (i : ℕ) = n → w i ∈ Submodule.span Ω (Set.range e) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hi
      have hsum := w.sum_repr (e i)
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsum
      have hrest : ∑ j ∈ Finset.univ.erase i, w.repr (e i) j • w j ∈
          Submodule.span Ω (Set.range e) := by
        refine Submodule.sum_mem _ fun j hj => ?_
        rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with hlt | hgt
        · exact Submodule.smul_mem _ _ (ih j (by rw [← hi]; exact hlt) j rfl)
        · rw [hup i j hgt, zero_smul]
          exact Submodule.zero_mem _
      have hei : e i ∈ Submodule.span Ω (Set.range e) := Submodule.subset_span ⟨i, rfl⟩
      have h1 : w.repr (e i) i • w i ∈ Submodule.span Ω (Set.range e) := by
        rw [eq_sub_of_add_eq hsum]
        exact Submodule.sub_mem _ hei hrest
      rw [hdiag] at h1
      have h2 := Submodule.smul_mem _ (chartZ y c (b i))⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ (hm i), one_smul] at h2
  have htop : ⊤ ≤ Submodule.span Ω (Set.range e) := by
    rw [← w.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hspan i i rfl
  have hcard : Fintype.card (Fin N) = Module.finrank Ω E := by
    rw [Module.finrank_eq_card_basis w]
  set eb := basisOfTopLeSpanOfCardEqFinrank e htop hcard with heb_def
  have heb : ∀ i, eb i = e i := fun i => by
    rw [heb_def, coe_basisOfTopLeSpanOfCardEqFinrank]
  set ψ : Module.Dual Ω E := eb.coord ⟨0, h0⟩ with hψ_def
  have hψe : ∀ i, ψ (e i) ∈ chartRing F (segreVec y) c := by
    intro i
    rw [← heb, hψ_def, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hint : ∀ n : ℕ, n ≤ N → ∀ v ∈ B.lat c, (∀ j : Fin N, n ≤ (j : ℕ) → w.repr v j = 0) →
      ψ v ∈ chartRing F (segreVec y) c := by
    intro n
    induction n with
    | zero =>
      intro _ v _ hv
      have : v = 0 := w.repr.injective (by ext j; simp [hv j (Nat.zero_le _)])
      simp [this]
    | succ n ih =>
      intro hn v hvB hv
      set i : Fin N := ⟨n, hn⟩ with hi_def
      have hmem : w.repr v i ∈ degLat F y (b i) c := by
        rw [← hB.graded c hc i]
        refine ⟨v, hvB, fun j hj => hv j ?_, rfl⟩
        rw [Fin.lt_def] at hj
        simp only [hi_def] at hj
        omega
      obtain ⟨α, hα, hαv⟩ := hmem
      have hv' : v - α • e i ∈ B.lat c := (B.lat c).sub_mem hvB (B.stable c α hα _ (he i))
      have hrec := ih (by omega) _ hv' (fun j hj => by
        rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
        rcases Nat.lt_or_ge n (j : ℕ) with hlt | hge
        · rw [hv j (by omega), hup i j (by rw [Fin.lt_def]; exact hlt), mul_zero, sub_zero]
        · have hji : j = i := Fin.ext (by simp only [hi_def]; omega)
          rw [hji, hdiag, hαv]
          simp [chartZ])
      have hsplit : ψ v = ψ (v - α • e i) + α * ψ (e i) := by
        simp [map_sub, smul_eq_mul]
      rw [hsplit]
      exact add_mem hrec (mul_mem hα (hψe i))
  refine ⟨ψ, fun v hv => hint N le_rfl v hv (fun j hj => absurd j.isLt (by omega)), ?_⟩
  have he0 : e ⟨0, h0⟩ = chartZ y c (b ⟨0, h0⟩) • w ⟨0, h0⟩ := by
    conv_lhs => rw [← w.sum_repr (e ⟨0, h0⟩)]
    rw [Finset.sum_eq_single ⟨0, h0⟩]
    · rw [hdiag]
    · intro j _ hj
      rw [hup _ j (by rw [Fin.lt_def]; exact Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))), zero_smul]
    · simp
  have h1 : ψ (e ⟨0, h0⟩) = 1 := by
    rw [← heb, hψ_def, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
  rw [he0, map_smul, smul_eq_mul] at h1
  rw [mul_comm]
  exact h1

theorem chart_data (y : (Σ k, ι k) → Ω) (B : ChartBundle F (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hB : IsFlagFrame y B w b) {M : ℕ}
    (a : K → ℤ) (φ : Fin M → Module.Dual Ω E) (hφ : IsTwistedDualGens y B a φ) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) (h0 : 0 < N) :
    (∀ l, φ l (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a) ∈ chartRing F (segreVec y) c) ∧
      ∃ v : Fin M → Ω, (∀ l, v l ∈ chartRing F (segreVec y) c) ∧
        ∑ l, v l * (φ l (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a)) = 1 := by
  have hlive := live_of_segreVec_ne_zero hc
  have hsplit : chartZ y c (b ⟨0, h0⟩ - a) = chartZ y c (b ⟨0, h0⟩) * chartZ y c (-a) := by
    rw [sub_eq_add_neg, chartZ_add hlive]
  have hinv : chartZ y c a * chartZ y c (-a) = 1 := by
    rw [← chartZ_add hlive, add_neg_cancel]
    simp [chartZ]
  refine ⟨fun l => ?_, ?_⟩
  · obtain ⟨v0, hv0, hup, hdiag⟩ := exists_adapted y B w b hB c hc ⟨0, h0⟩
    have hv0eq : v0 = chartZ y c (b ⟨0, h0⟩) • w ⟨0, h0⟩ := by
      conv_lhs => rw [← w.sum_repr v0]
      rw [Finset.sum_eq_single ⟨0, h0⟩]
      · rw [hdiag]
      · intro j _ hj
        rw [hup j (by rw [Fin.lt_def]; exact Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))), zero_smul]
      · simp
    obtain ⟨α, hα, hαe⟩ := hφ.sections c hc l v0 hv0
    rw [hv0eq, map_smul, smul_eq_mul] at hαe
    have hαe' : chartZ y c (b ⟨0, h0⟩) * φ l (w ⟨0, h0⟩) = α * chartZ y c a := hαe
    have : φ l (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a) = α := by
      rw [hsplit]
      linear_combination chartZ y c (-a) * hαe' + α * hinv
    rw [this]
    exact hα
  · obtain ⟨ψ, hψ, hψ1⟩ := exists_dual_first y B w b hB c hc h0
    obtain ⟨u, hu, hψeq⟩ := hφ.generate c hc ψ hψ
    refine ⟨u, hu, ?_⟩
    have h := LinearMap.congr_fun hψeq (w ⟨0, h0⟩)
    rw [LinearMap.sum_apply] at h
    simp only [LinearMap.smul_apply, smul_eq_mul] at h
    rw [← hψ1, h, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hsplit]
    simp only [chartZ, Pi.neg_apply]
    ring

end FlagLineSectionProof

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PJoinVariety
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar)

noncomputable section

namespace JoinVariety

variable {K : Type} {ι : K → Type}

def varEquiv : Option (Σ k, ι k) ≃ (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) where
  toFun
    | none => ⟨.inr (), (0 : Fin 1)⟩
    | some p => liftVar (ι := ι) ptIdx p
  invFun
    | ⟨.inl k, i⟩ => some ⟨k, i⟩
    | ⟨.inr _, _⟩ => none
  left_inv := by
    rintro (_ | ⟨k, i⟩) <;> rfl
  right_inv := by
    rintro ⟨(k | u), i⟩
    · rfl
    · cases u
      have : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst this
      rfl

theorem liftVar_injective : Function.Injective (liftVar (ι := ι) ptIdx) :=
  (varEquiv (ι := ι)).injective.comp (Option.some_injective _)

def retr (F : Type) [Field F] :
    MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) F →ₐ[F] MvPolynomial (Σ k, ι k) F :=
  aeval fun t => match t with
    | ⟨.inl k, i⟩ => X ⟨k, i⟩
    | ⟨.inr _, _⟩ => 1

theorem retr_rename (F : Type) [Field F] (p : MvPolynomial (Σ k, ι k) F) :
    retr F (rename (liftVar (ι := ι) ptIdx) p) = p := by
  have : (retr F).comp (rename (liftVar (ι := ι) ptIdx)) = AlgHom.id F _ := by
    ext ⟨k, i⟩
    simp [retr, liftVar]
  exact congrArg (fun φ => φ p) this

end JoinVariety

open JoinVariety in
theorem JoinVariety.proof : JoinVariety.Statement := by
  intro F _ K _ ι _ V n hV
  obtain ⟨⟨hprime, ⟨S0, hS0, hspan⟩, hrel⟩, hdim⟩ := hV
  set V' := V.map (rename (liftVar (ι := ι) ptIdx))

  let Φ : Polynomial (MvPolynomial (Σ k, ι k) F) ≃ₐ[F] MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) F :=
    (optionEquivLeft F (Σ k, ι k)).symm.trans (renameEquiv F varEquiv)
  have hΦC : (Φ : Polynomial (MvPolynomial (Σ k, ι k) F) →+* _).comp Polynomial.C =
      (rename (liftVar (ι := ι) ptIdx) : MvPolynomial (Σ k, ι k) F →ₐ[F] _).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have h1 : (optionEquivLeft F (Σ k, ι k)).symm (Polynomial.C (C r)) = C r := by
        rw [AlgEquiv.symm_apply_eq]; simp
      show renameEquiv F varEquiv ((optionEquivLeft F (Σ k, ι k)).symm (Polynomial.C (C r))) = _
      rw [h1]
      simp
    · intro s
      have h1 : (optionEquivLeft F (Σ k, ι k)).symm (Polynomial.C (X s)) = X (some s) := by
        rw [AlgEquiv.symm_apply_eq]; simp
      show renameEquiv F varEquiv ((optionEquivLeft F (Σ k, ι k)).symm (Polynomial.C (X s))) = _
      rw [h1]
      simp [varEquiv]
  have hV' : V' = (V.map (Polynomial.C : MvPolynomial (Σ k, ι k) F →+* Polynomial (MvPolynomial (Σ k, ι k) F))).map (Φ : Polynomial (MvPolynomial (Σ k, ι k) F) →+* _) := by
    rw [Ideal.map_map, hΦC]
    rfl

  have hmem : ∀ y, y ∈ V' → retr F y ∈ V := by
    have : V' ≤ V.comap (retr F : _ →ₐ[F] MvPolynomial (Σ k, ι k) F).toRingHom := by
      rw [Ideal.map_le_iff_le_comap]
      intro v hv
      simpa [Ideal.mem_comap, retr_rename] using hv
    exact fun y hy => this hy
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hV']
    exact Ideal.map_isPrime_of_equiv _
  · refine ⟨rename (liftVar (ι := ι) ptIdx) '' S0, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨a, ha⟩ := hS0 f hf
      refine ⟨Sum.elim a 0, ?_⟩
      classical
      intro m hm k
      rw [support_rename_of_injective liftVar_injective] at hm
      obtain ⟨m0, hm0, rfl⟩ := Finset.mem_image.mp hm
      cases k with
      | inl k =>
        change ∑ i : ι k, (Finsupp.mapDomain (liftVar (ι := ι) ptIdx) m0)
          (liftVar (ι := ι) ptIdx ⟨k, i⟩) = a k
        simp only [Finsupp.mapDomain_apply_of_injective liftVar_injective]
        exact ha m0 hm0 k
      | inr u =>
        simp only [Sum.elim_inr, Pi.zero_apply]
        refine Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_of_notMem_range _ _ ?_
        rintro ⟨p, hp⟩
        cases hp
    · change V.map _ = _
      rw [hspan, Ideal.map_span]
  · rintro (k | u)
    · obtain ⟨i, hi⟩ := hrel k
      refine ⟨i, fun h => hi ?_⟩
      have := hmem _ h
      simpa [retr] using this
    · refine ⟨(0 : Fin 1), fun h => hprime.ne_top ?_⟩
      have := hmem _ h
      rw [Ideal.eq_top_iff_one]
      simpa [retr] using this
  · have e1 : (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (Sum.elim ι ptIdx) ⧸ V') ≃+*
        Polynomial (MvPolynomial (Σ k, ι k) F ⧸ V) :=
      (Ideal.quotientEquiv _ _ Φ.toRingEquiv hV').symm.trans
        (Ideal.polynomialQuotientEquivQuotientPolynomial V).symm
    refine (ringKrullDim_eq_of_ringEquiv
      (S := Polynomial (MvPolynomial (Σ k, ι k) F ⧸ V)) e1).trans ?_
    rw [Polynomial.ringKrullDim_of_isNoetherianRing]
    change ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ V) + 1 = _
    rw [hdim, Fintype.card_sum, Fintype.card_unit]
    norm_cast

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalQuotFinsum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem LocalQuotFinsum.proof (h : LocalQuotPrimes.Statement.{u}) : LocalQuotFinsum.Statement.{u} := by
  intro R _ P U _ hPU F F' hF hF' hFF'
  have hP := h R P U hPU
  set S : Set (Ideal R) := {G | G.IsPrime ∧ P ≤ G ∧ G ≤ U} with hS
  set T : Set (Ideal (localQuot P U)) := {p | p.IsPrime} with hT
  have h1 : ∑ᶠ G, F G = ∑ᶠ G ∈ S, F G := by
    rw [← finsum_mem_univ]
    apply finsum_mem_inter_support_eq'
    intro G hG
    exact ⟨fun _ => hF G hG, fun _ => Set.mem_univ G⟩
  have h2 : ∑ᶠ p, F' p = ∑ᶠ p ∈ T, F' p := by
    rw [← finsum_mem_univ]
    apply finsum_mem_inter_support_eq'
    intro p hp
    exact ⟨fun _ => hF' p hp, fun _ => Set.mem_univ p⟩
  have hbij : S.BijOn (fun G => G.map (localQuotMap P U)) T := by
    refine ⟨fun G hG => (hP.1 G hG.1 hG.2.1 hG.2.2).1, ?_, ?_⟩
    · intro G₁ hG₁ G₂ hG₂ he
      have e₁ := (hP.1 G₁ hG₁.1 hG₁.2.1 hG₁.2.2).2
      have e₂ := (hP.1 G₂ hG₂.1 hG₂.2.1 hG₂.2.2).2
      simp only at he
      rw [← e₁, ← e₂, he]
    · intro p hp
      obtain ⟨hle, hleU, hmap⟩ := hP.2 p hp
      exact ⟨p.comap (localQuotMap P U), ⟨by have : p.IsPrime := hp; exact Ideal.comap_isPrime _ p, hle, hleU⟩, hmap⟩
  rw [h1, h2]
  exact finsum_mem_eq_of_bijOn _ hbij fun G hG => hFF' G hG.1 hG.2.1 hG.2.2

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

