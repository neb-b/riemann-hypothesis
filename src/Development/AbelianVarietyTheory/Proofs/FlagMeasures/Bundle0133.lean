module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepSpaceProps
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.StepLoc

open GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem kset_inUJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) : inUJ ε g := by
  have h1 : gᴴ * g = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hg.1
    simpa [Matrix.star_eq_conjTranspose] using this
  unfold inUJ
  rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem inG_conj {ε : Fin n → Bool} {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) (hX : inG ε X) :
    inG ε (g * X * gᴴ) := by
  have h2 : gᴴ * Jm ε = Jm ε * gᴴ := by
    have := congrArg Matrix.conjTranspose hg.2
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_conjTranspose] at this
    exact this.symm
  unfold inG at *
  calc (g * X * gᴴ)ᴴ * Jm ε + Jm ε * (g * X * gᴴ)
      = g * Xᴴ * (gᴴ * Jm ε) + (Jm ε * g) * X * gᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = g * (Xᴴ * Jm ε + Jm ε * X) * gᴴ := by
        rw [h2, ← hg.2]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX]; simp

theorem exp_conj_mul {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) :
    NormedSpace.exp (t • (g * X * gᴴ)) * g = g * NormedSpace.exp (t • X) := by
  have h1 : gᴴ * g = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hg
    simpa [Matrix.star_eq_conjTranspose] using this
  have hi : g⁻¹ = gᴴ := Matrix.inv_eq_left_inv h1
  have hu : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).mpr (Matrix.isUnit_det_of_left_inverse h1)
  have : t • (g * X * gᴴ) = g * (t • X) * g⁻¹ := by
    rw [hi]; simp
  rw [this, Matrix.exp_conj _ _ hu, hi, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem orbit_conj {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsCRepOn (UJset ε) σ) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) (hX : inG ε X) (w : H) :
    orbit σ (g * X * gᴴ) (σ g w) = fun t => σ g (orbit σ X w t) := by
  funext t
  have a1 := hσ.2 _ (exp_indefinite_unitary_holds n ε _ (inG_conj hg hX) t) g (kset_inUJ hg)
  have a2 := hσ.2 g (kset_inUJ hg) _ (exp_indefinite_unitary_holds n ε _ hX t)
  rw [exp_conj_mul hg.1, a2] at a1
  exact (congrArg (fun T : H →L[ℂ] H => T w) a1).symm

theorem dAct_conj {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsCRepOn (UJset ε) σ) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) (hX : inG ε X) {w : H}
    (hw : DifferentiableAt ℝ (orbit σ X w) 0) :
    dAct σ (g * X * gᴴ) (σ g w) = σ g (dAct σ X w) := by
  unfold dAct
  rw [orbit_conj hσ hg hX]
  exact (((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hw.hasDerivAt).deriv

theorem dAct_add_smul {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {X : Matrix (Fin n) (Fin n) ℂ}
    {w w' : H} (hw : DifferentiableAt ℝ (orbit σ X w) 0) (hw' : DifferentiableAt ℝ (orbit σ X w') 0)
    (c : ℂ) : dAct σ X (w + c • w') = dAct σ X w + c • dAct σ X w' := by
  have : orbit σ X (w + c • w') = fun t => orbit σ X w t + c • orbit σ X w' t := by
    funext t
    simp [orbit]
  unfold dAct
  rw [this]
  exact (hw.hasDerivAt.fun_add (hw'.hasDerivAt.fun_const_smul c)).deriv

theorem dAct_zero (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) :
    dAct σ X 0 = 0 := by
  have : orbit σ X 0 = fun _ => 0 := by
    funext t
    simp [orbit]
  unfold dAct
  rw [this]
  simp

theorem lowKSub_stable (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    IsKStableOn ε σ (lowKSub ε lam σ) := by
  intro g hg v hv
  have : lowKSub ε lam σ ≤ (lowKSub ε lam σ).comap (σ g : H →ₗ[ℂ] H) := by
    refine sSup_le fun S hS => ?_
    intro x hx
    exact (le_sSup hS : S ≤ lowKSub ε lam σ) (hS.2.1 g hg x hx)
  exact this hv

theorem dWord_mem {ε : Fin n → Bool} {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {P : ℕ} {l : List (Matrix (Fin n) (Fin n) ℂ)} {u : H} (hl : l.length ≤ P) (hX : ∀ X ∈ l, inG ε X)
    (hu : u ∈ lowKSub ε lam σ) : dWord σ l u ∈ stepSpace ε lam σ P :=
  Submodule.subset_span ⟨l, u, hl, hX, hu, rfl⟩

theorem dWord_conj {ε : Fin n → Bool} {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsCRepOn (UJset ε) σ) (hd : ∀ P, ∀ w ∈ stepSpace ε lam σ P, IsDiffVec ε σ w)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) {u : H} (hu : u ∈ lowKSub ε lam σ)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (hX : ∀ X ∈ l, inG ε X) :
    σ g (dWord σ l u) = dWord σ (l.map fun X => g * X * gᴴ) (σ g u) := by
  induction l with
  | nil => rfl
  | cons Y l ih =>
    have hl : ∀ X ∈ l, inG ε X := fun X h => hX X (List.mem_cons_of_mem _ h)
    have hY : inG ε Y := hX Y List.mem_cons_self
    change σ g (dAct σ Y (dWord σ l u)) =
      dAct σ (g * Y * gᴴ) (dWord σ (l.map fun X => g * X * gᴴ) (σ g u))
    rw [← ih hl, dAct_conj hσ hg hY (hd _ _ (dWord_mem le_rfl hl hu) Y hY)]

end GlobalTheory.StepLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumGraphEqSumEntN
section
noncomputable section

namespace GlobalTheory.GLm

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem sum_graph_eq_sum_entN {A : Type} [AddCommMonoid A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A)
    (S : Finset ℕ) (f : ℕ → ℕ) :
    (∑ a : Fin N, ∑ b : Fin N, if (a : ℕ) ∈ S ∧ (b : ℕ) = f a then M a b else 0) =
      ∑ a ∈ S, entN M a (f a) := by
  have h1 : ∀ a : Fin N, (∑ b : Fin N, if (a : ℕ) ∈ S ∧ (b : ℕ) = f a then M a b else 0) =
      if (a : ℕ) ∈ S then entN M a (f a) else 0 := by
    intro a
    by_cases ha : (a : ℕ) ∈ S
    · rw [if_pos ha]
      by_cases hf : f a < N
      · rw [Finset.sum_eq_single ⟨f a, hf⟩]
        · split_ifs with hc
          · unfold entN
            rw [dite_eq_left ⟨a.isLt, hf⟩]
          · exact absurd ⟨ha, rfl⟩ hc
        · intro b _ hb
          rw [if_neg]
          intro h
          exact hb (Fin.ext h.2)
        · intro h
          exact absurd (Finset.mem_univ _) h
      · rw [Finset.sum_eq_zero]
        · unfold entN
          rw [dite_eq_right (fun hh => hf hh.2)]
        · intro b _
          rw [if_neg]
          intro h
          exact hf (h.2 ▸ b.isLt)
    · rw [if_neg ha]
      exact Finset.sum_eq_zero (fun b _ => if_neg (fun h => ha h.1))
  rw [Finset.sum_congr rfl (fun a _ => h1 a)]
  rw [Fin.sum_univ_eq_sum_range (fun a => if a ∈ S then entN M a (f a) else 0) N]
  rw [← Finset.sum_filter]
  apply Finset.sum_subset
  · intro a ha
    exact (Finset.mem_filter.mp ha).2
  · intro a haS hnot
    have hlt : ¬ a < N := fun hlt => hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, haS⟩)
    unfold entN
    rw [dite_eq_right (fun hh => hlt hh.1)]

theorem phI_last_iff {N : ℕ} (k s : ℕ) (a b : Fin N) :
    phI k s s a b ↔ (a : ℕ) < b ∧ ¬ (s ≤ (a : ℕ) ∧ (a : ℕ) < s + k ∧ (b : ℕ) = s + k) := by
  simp only [phI, IsW, Fin.lt_iff_val_lt_val]
  constructor <;> intro h <;> omega

variable {g : ℕ} [Fact g.Prime]

theorem inPat_phI_last_iff {N : ℕ} (k s : ℕ) (M : Mt g N) :
    InPat (phI k s s) M ↔ IsUniUp M ∧ ∀ a, s ≤ a → a < s + k → entN M a (s + k) = 0 := by
  unfold InPat IsUniUp
  constructor
  · intro h
    refine ⟨fun a b => ⟨fun hba => ?_, fun hab => ?_⟩, fun a h1 h2 => ?_⟩
    · have hv := Fin.lt_iff_val_lt_val.mp hba
      have hn : ¬ phI k s s a b := by
        rw [phI_last_iff]
        omega
      rw [h a b hn, Matrix.one_apply_ne]
      intro e
      rw [e] at hv
      omega
    · subst hab
      have hn : ¬ phI k s s a a := by
        rw [phI_last_iff]
        omega
      rw [h a a hn, Matrix.one_apply_eq]
    · unfold entN
      split_ifs with hh
      · have hn : ¬ phI k s s (⟨a, hh.1⟩ : Fin N) ⟨s + k, hh.2⟩ := by
          rw [phI_last_iff]
          exact fun h' => h'.2 ⟨h1, h2, rfl⟩
        rw [h _ _ hn, Matrix.one_apply_ne]
        intro e
        simp only [Fin.mk.injEq] at e
        omega
      · rfl
  · rintro ⟨hU, hz⟩ ⟨a, ha⟩ ⟨b, hb⟩ hn
    rw [phI_last_iff] at hn
    rcases lt_trichotomy a b with hab | hab | hab
    · have hw : s ≤ a ∧ a < s + k ∧ b = s + k := by
        by_contra hc
        exact hn ⟨hab, hc⟩
      obtain ⟨hw1, hw2, rfl⟩ := hw
      have h0 := hz a hw1 hw2
      unfold entN at h0
      rw [dite_eq_left ⟨ha, hb⟩] at h0
      rw [Matrix.one_apply_ne]
      · exact h0
      · intro e
        simp only [Fin.mk.injEq] at e
        omega
    · subst hab
      rw [(hU _ _).2 rfl, Matrix.one_apply_eq]
    · rw [(hU _ _).1 (Fin.mk_lt_mk.mpr hab), Matrix.one_apply_ne]
      intro e
      simp only [Fin.mk.injEq] at e
      omega

private theorem sum_sum_ite_eq_sum_entN_of_iff {A : Type} [AddCommMonoid A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A)
    (P : ℕ → ℕ → Prop) [∀ a b, Decidable (P a b)] (S : Finset ℕ) (f : ℕ → ℕ)
    (h : ∀ a b : ℕ, b < N → (P a b ↔ a ∈ S ∧ b = f a)) :
    (∑ a : Fin N, ∑ b : Fin N, if P (a : ℕ) (b : ℕ) then M a b else 0) = ∑ a ∈ S, entN M a (f a) := by
  rw [← sum_graph_eq_sum_entN]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  by_cases hp : P a b
  · rw [if_pos hp, if_pos ((h a b b.isLt).1 hp)]
  · rw [if_neg hp, if_neg (fun hq => hp ((h a b b.isLt).2 hq))]

theorem sumAt_eeI_eq_phiJ {N : ℕ} (k s : ℕ) (hN : N = k + 2 * s + 1) (M : Mt g N) :
    sumAt (eeI k s) M = phiJ k s M := by
  subst hN
  have hsplit : sumAt (eeI k s) M =
      (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1),
        if (b : ℕ) = a + 1 ∧ (b : ℕ) < s then M a b else 0) +
      (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1),
        if (a : ℕ) + 1 = s ∧ (b : ℕ) = s + k then M a b else 0) +
      (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1),
        if (b : ℕ) = a + 1 ∧ s + k ≤ (a : ℕ) then M a b else 0) +
      (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1),
        if (b : ℕ) = a + 1 ∧ s ≤ (a : ℕ) ∧ (b : ℕ) < s + k then M a b else 0) := by
    unfold sumAt
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    have hb := b.isLt
    unfold eeI IsW
    split_ifs <;> first | omega | simp
  have h1 : (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1),
      if (b : ℕ) = a + 1 ∧ (b : ℕ) < s then M a b else 0) =
      ∑ a ∈ Finset.range (s - 1), entN M a (a + 1) :=
    sum_sum_ite_eq_sum_entN_of_iff M (fun a b => b = a + 1 ∧ b < s) _ (fun a => a + 1)
      (fun a b _ => by simp only [Finset.mem_range]; constructor <;> intro h <;> omega)
  have h2 : (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1),
      if (a : ℕ) + 1 = s ∧ (b : ℕ) = s + k then M a b else 0) =
      ∑ a ∈ (Finset.range s).filter (fun a => a + 1 = s), entN M a (s + k) :=
    sum_sum_ite_eq_sum_entN_of_iff M (fun a b => a + 1 = s ∧ b = s + k) _ (fun _ => s + k)
      (fun a b _ => by simp only [Finset.mem_filter, Finset.mem_range]; constructor <;> intro h <;> omega)
  have h3 : (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1),
      if (b : ℕ) = a + 1 ∧ s + k ≤ (a : ℕ) then M a b else 0) =
      ∑ i ∈ Finset.range s, entN M (s + k + i) (s + k + i + 1) := by
    rw [sum_sum_ite_eq_sum_entN_of_iff M (fun a b => b = a + 1 ∧ s + k ≤ a) (Finset.Ico (s + k) (s + k + s)) (fun a => a + 1)
      (fun a b hb => by simp only [Finset.mem_Ico]; constructor <;> intro h <;> omega)]
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  have h4 : (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1),
      if (b : ℕ) = a + 1 ∧ s ≤ (a : ℕ) ∧ (b : ℕ) < s + k then M a b else 0) =
      ∑ a ∈ Finset.range (k - 1), entN M (s + a) (s + a + 1) := by
    rw [sum_sum_ite_eq_sum_entN_of_iff M (fun a b => b = a + 1 ∧ s ≤ a ∧ b < s + k) (Finset.Ico s (s + (k - 1))) (fun a => a + 1)
      (fun a b _ => by simp only [Finset.mem_Ico]; constructor <;> intro h <;> omega)]
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  have key : (∑ a ∈ (Finset.range s).filter (fun a => a + 1 = s), entN M a (s + k)) +
      (∑ i ∈ Finset.range s, entN M (s + k + i) (s + k + i + 1)) =
      (if 1 ≤ s then entN M (s - 1) (s + k) + entN M (s + k) (s + k + 1) else 0) +
      ∑ i ∈ Finset.range (s - 1), entN M (s + k + 1 + i) (s + k + 2 + i) := by
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs
      simp
    · obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      have hB : (Finset.range (t + 1)).filter (fun a => a + 1 = t + 1) = {t} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        omega
      have hC : (∑ i ∈ Finset.range (t + 1), entN M (t + 1 + k + i) (t + 1 + k + i + 1)) =
          (∑ i ∈ Finset.range (t + 1 - 1), entN M (t + 1 + k + 1 + i) (t + 1 + k + 2 + i)) +
            entN M (t + 1 + k) (t + 1 + k + 1) := by
        rw [Finset.sum_range_succ', Nat.add_sub_cancel]
        simp only [add_zero]
        congr 1
        exact Finset.sum_congr rfl (fun i _ => by congr 1 <;> omega)
      rw [hB, Finset.sum_singleton, hC, if_pos (show 1 ≤ t + 1 by omega), Nat.add_sub_cancel]
      ring
  rw [hsplit, h1, h2, h3, h4]
  unfold phiJ
  linear_combination key

theorem ePat_last_eq_eJ : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (N k s : ℕ), N = k + 2 * s + 1 →
    ePat g N (phI k s s) (eeI k s) ψ = eJ g N k s ψ := by
  intro g _ ψ N k s hN
  have hP : (InPat (phI k s s) : Mt g N → Prop) =
      fun M => IsUniUp M ∧ ∀ a, s ≤ a → a < s + k → entN M a (s + k) = 0 :=
    funext fun M => propext (inPat_phI_last_iff k s M)
  have hφ : (sumAt (eeI k s) : Mt g N → ZMod g) = phiJ k s := funext fun M => sumAt_eeI_eq_phiJ k s hN M
  unfold ePat eJ
  rw [hP, hφ]

end GlobalTheory.GLm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportFrameAlongUnitaryAdelic
section
noncomputable section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.FrMap

theorem hform_eq_dot {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J : Matrix (Fin n) (Fin n) A)
    (x y : Fin n → A) : hform s J x y = (fun i => s (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J M : Matrix (Fin n) (Fin n) A)
    (x y : Fin n → A) : hform s J (M *ᵥ x) (M *ᵥ y) = hform s (cT s M * J * M) x y := by
  rw [hform_eq_dot, hform_eq_dot]
  have h1 : (fun i => s ((M *ᵥ x) i)) = (M.map s) *ᵥ (fun i => s (x i)) := by
    funext i; simp [mulVec, dotProduct, map_sum]
  rw [h1, cT, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose, dotProduct_comm, dotProduct_mulVec,
    dotProduct_comm]

theorem inModL_map {A : Type} [CommRing A] {O : Subring A} {n : ℕ} {Λ Λ' : Submodule O (Fin n → A)} (m : ℕ)
    (P : Matrix (Fin n) (Fin n) A) (hP : ∀ z ∈ Λ, P *ᵥ z ∈ Λ') {S S' : Set (Fin n → A)}
    (hS : ∀ s ∈ S, P *ᵥ s ∈ S') {x : Fin n → A} (hx : InModL Λ m S x) : InModL Λ' m S' (P *ᵥ x) := by
  obtain ⟨s, hs, z, hz, rfl⟩ := hx
  let f : (Fin n → A) →ₗ[O] (Fin n → A) := (Matrix.mulVecLin P).restrictScalars O
  refine ⟨P *ᵥ s, ?_, P *ᵥ z, hP z hz, by rw [mulVec_add, mulVec_smul]⟩
  have : f s ∈ Submodule.span O (f '' S) := by
    rw [← Submodule.map_span]; exact Submodule.mem_map_of_mem hs
  exact Submodule.span_mono (by rintro _ ⟨t, ht, rfl⟩; exact hS t ht) this

theorem transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Λ Λ' : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F)) (g k : ℕ) (h : UPts σ J (Ad F)), (∀ x, (h⁻¹).1.1 *ᵥ x ∈ Λ' ↔ x ∈ Λ) → ∀ Fr : AdFrame σ J Λ g k, ∃ Fr' : AdFrame σ J Λ' g k, ∀ y : UPts σ J (Ad F), (Fr.InK y.1 ↔ Fr'.InK (h⁻¹ * y * h : UPts σ J (Ad F)).1) ∧ Fr.chi y.1 = Fr'.chi (h⁻¹ * y * h : UPts σ J (Ad F)).1 := by
  intro F E _ _ _ _ _ n σ J Λ Λ' g k h hΛ Fr
  set M : Matrix (Fin n) (Fin n) (E ⊗[F] Ad F) := h.1.1 with hM
  set Mi : Matrix (Fin n) (Fin n) (E ⊗[F] Ad F) := (h⁻¹).1.1 with hMi
  have hMMi : M * Mi = 1 := by
    rw [hM, hMi]; show (h.1 * h.1⁻¹).val = 1; rw [mul_inv_cancel]; rfl
  have hMiM : Mi * M = 1 := by
    rw [hM, hMi]; show (h.1⁻¹ * h.1).val = 1; rw [inv_mul_cancel]; rfl
  have hinvM : ∀ u v, hR σ J (Ad F) (M *ᵥ u) (M *ᵥ v) = hR σ J (Ad F) u v := by
    intro u v; unfold hR; rw [hform_mulVec]; congr 1; exact h.2
  have hinvMi : ∀ u v, hR σ J (Ad F) (Mi *ᵥ u) (Mi *ᵥ v) = hR σ J (Ad F) u v := by
    intro u v; unfold hR; rw [hform_mulVec]; congr 1; exact (h⁻¹).2
  have hΛ'' : ∀ x, x ∈ Λ' ↔ M *ᵥ x ∈ Λ := by
    intro x; rw [← hΛ (M *ᵥ x), mulVec_mulVec, hMiM, one_mulVec]
  have hMiΛ : ∀ z ∈ Λ, Mi *ᵥ z ∈ Λ' := fun z hz => (hΛ z).2 hz
  have hMΛ' : ∀ z ∈ Λ', M *ᵥ z ∈ Λ := fun z hz => (hΛ'' z).1 hz
  have hMMiv : ∀ v, M *ᵥ (Mi *ᵥ v) = v := fun v => by rw [mulVec_mulVec, hMMi, one_mulVec]
  have hMiMv : ∀ v, Mi *ᵥ (M *ᵥ v) = v := fun v => by rw [mulVec_mulVec, hMiM, one_mulVec]
  let Fr' : AdFrame σ J Λ' g k :=
    { eps := Fr.eps, eps_idem := Fr.eps_idem, eps_orth := Fr.eps_orth, eps_int := Fr.eps_int,
      eps_full := by
        intro y hy
        obtain ⟨z, hz, e⟩ := Fr.eps_full (M *ᵥ y) (hMΛ' y hy)
        refine ⟨Mi *ᵥ z, hMiΛ z hz, ?_⟩
        have := congrArg (Mi *ᵥ ·) e
        simp only [mulVec_smul, hMiMv] at this
        exact this
      b := fun i => Mi *ᵥ Fr.b i, bd := fun i => Mi *ᵥ Fr.bd i,
      b_mem := fun i => hMiΛ _ (Fr.b_mem i), bd_mem := fun i => hMiΛ _ (Fr.bd_mem i),
      b_eps := fun i => by
        show Mi *ᵥ Fr.b i = Fr.eps • (Mi *ᵥ Fr.b i)
        rw [← mulVec_smul, ← Fr.b_eps i]
      bd_eps := fun i => by
        show Mi *ᵥ Fr.bd i = sigR σ (Ad F) Fr.eps • (Mi *ᵥ Fr.bd i)
        rw [← mulVec_smul, ← Fr.bd_eps i]
      dual := fun i j => by
        show ∃ t ∈ OAd F E, hR σ J (Ad F) (Mi *ᵥ Fr.bd i) (Mi *ᵥ Fr.b j) - _ = _
        rw [hinvMi]; exact Fr.dual i j
      span := by
        intro y hy
        have := inModL_map g Mi hMiΛ (S' := Set.range (fun i => Mi *ᵥ Fr.b i) ∪ Set.range (fun i => Mi *ᵥ Fr.bd i))
          (by rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩); exacts [Or.inl ⟨i, rfl⟩, Or.inr ⟨i, rfl⟩])
          (Fr.span (M *ᵥ y) (hMΛ' y hy))
        rwa [hMiMv] at this
      psi := Fr.psi, psi_add := Fr.psi_add, psi_int := Fr.psi_int, psi_rat := Fr.psi_rat }
  refine ⟨Fr', fun y => ?_⟩
  set Y : Matrix (Fin n) (Fin n) (E ⊗[F] Ad F) := y.1.1 with hY
  have hconj : ((h⁻¹ * y * h : UPts σ J (Ad F)).1 : Matrix (Fin n) (Fin n) (E ⊗[F] Ad F)) = Mi * Y * M := rfl
  have hc1 : M * (Mi * Y * M) = Y * M := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hMMi, Matrix.one_mul]
  have hc3 : M * (Mi * Y * M - 1) = (Y - 1) * M := by
    rw [Matrix.mul_sub, hc1, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul]
  have hc4 : (Mi * Y * M - 1) * Mi = Mi * (Y - 1) := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, hMMi, Matrix.mul_one, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]
  have hc5 : (Mi * Y * M) * Mi = Mi * Y := by
    rw [Matrix.mul_assoc, hMMi, Matrix.mul_one]
  constructor
  · unfold AdFrame.InK
    rw [hconj]
    have key1 : ∀ x, (Mi * Y * M) *ᵥ x ∈ Λ' ↔ Y *ᵥ (M *ᵥ x) ∈ Λ := by
      intro x; rw [hΛ'', mulVec_mulVec, hc1, ← mulVec_mulVec]
    have key2 : ∀ x, (Mi * Y * M - 1) *ᵥ x ∈ Λ' ↔ (Y - 1) *ᵥ (M *ᵥ x) ∈ Λ := by
      intro x; rw [hΛ'', mulVec_mulVec, hc3, ← mulVec_mulVec]
    have keyd : ∀ x, (∀ z ∈ Λ', hR σ J (Ad F) z x ∈ OAd F E) ↔ (∀ z ∈ Λ, hR σ J (Ad F) z (M *ᵥ x) ∈ OAd F E) := by
      intro x; constructor
      · intro H z hz; have := H _ (hMiΛ z hz); rwa [← hinvM, hMMiv] at this
      · intro H z hz; have := H _ (hMΛ' z hz); rwa [hinvM] at this
    refine and_congr ?_ (and_congr ?_ ?_)
    · show (∀ x, x ∈ Λ ↔ Y *ᵥ x ∈ Λ) ↔ (∀ x, x ∈ Λ' ↔ (Mi * Y * M) *ᵥ x ∈ Λ')
      constructor
      · intro H x; rw [hΛ'', key1]; exact H _
      · intro H x; have := H (Mi *ᵥ x); rwa [hΛ'', key1, hMMiv] at this
    · constructor
      · intro H x hx; rw [key2]; exact H _ ((keyd x).1 hx)
      · intro H x hx
        have := H (Mi *ᵥ x) ((keyd _).2 (by rwa [hMMiv]))
        rwa [key2, hMMiv] at this
    · refine forall_congr' fun i => ?_
      show _ ↔ InModL Λ' g ((fun j => Mi *ᵥ Fr.b j) '' {j | j.1 < i.1}) ((Mi * Y * M - 1) *ᵥ (Mi *ᵥ Fr.b i))
      rw [mulVec_mulVec, hc4, ← mulVec_mulVec]
      constructor
      · intro H
        exact inModL_map g Mi hMiΛ (by rintro _ ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩) H
      · intro H
        have := inModL_map g M hMΛ' (S' := Fr.b '' {j | j.1 < i.1})
          (by rintro _ ⟨j, hj, rfl⟩; exact ⟨j, hj, (hMMiv _).symm⟩) H
        rwa [hMMiv] at this
  · unfold AdFrame.chi
    rw [hconj]
    show Fr.psi _ = Fr.psi _
    congr 2
    unfold supSum
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · show hR σ J (Ad F) (Fr.bd i) (Y *ᵥ Fr.b _) = hR σ J (Ad F) (Mi *ᵥ Fr.bd i) ((Mi * Y * M) *ᵥ (Mi *ᵥ Fr.b _))
      rw [mulVec_mulVec, hc5, ← mulVec_mulVec, hinvMi]
    · rfl

end GlobalTheory.St.G.FrMap
end
end

