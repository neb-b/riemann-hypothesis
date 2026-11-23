module

public import Mathlib
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0011

@[expose] public section

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvKir
section
noncomputable section
open GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.PRep

namespace DiscreteGroups.sglob.LConv

open DiscreteGroups.sglob.LConvKir in
theorem kirBump : KirBump := by
  intro k _ _ _ _ ψ hψc hψ m V _ _ ρ hsm v₀
  have key : ∀ j, j ≤ m → ∃ v : V, ∀ l : Module.Dual ℂ V, IsFunctional ψ ρ l →
      l v = l v₀ ∧ (l v₀ = 0 → ∀ g, InH j g → l (ρ g v) = 0) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨v₀, fun l _ => ⟨rfl, fun h0 g hg => by rw [InH_zero g hg, map_one, Module.End.one_apply]; exact h0⟩⟩
    | succ j ih =>
      intro hj
      obtain ⟨v, hv⟩ := ih (by omega)
      obtain ⟨v', hv'⟩ := step ψ hψc hψ ρ hsm j (by omega) v
      exact ⟨v', fun l hl => ⟨(hv' l hl).1.trans (hv l hl).1,
        fun h0 g hg => (hv' l hl).2 ((hv l hl).2 h0) g hg⟩⟩
  obtain ⟨v, hv⟩ := key m le_rfl
  exact ⟨v, fun l hl => ⟨(hv l hl).1, fun h0 g => (hv l hl).2 h0 _ (InH_corner g)⟩⟩

end DiscreteGroups.sglob.LConv
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvSepT
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle} (hψ : Continuous ψ) {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ}
  {B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ} (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B)

def WSp : Submodule ℂ (GL (Fin m) k → ℂ) where
  carrier := Set.range (Wf ψ hψ I B)
  zero_mem' := ⟨0, Wf_eq_zero hψ hI hB (by simp)⟩
  add_mem' := by
    rintro _ _ ⟨y, rfl⟩ ⟨z, rfl⟩
    exact ⟨y + z, Wf_add hψ hI hB y z⟩
  smul_mem' := by
    rintro c _ ⟨y, rfl⟩
    exact ⟨(starRingEnd ℂ) c • y, by rw [Wf_smul hψ hI hB, Complex.conj_conj]⟩

def Phi (y : WT (m := m) ψ) : WSp hψ hI hB := ⟨Wf ψ hψ I B y, y, rfl⟩

def tauRep : Representation ℂ (GL (Fin m) k) (WSp hψ hI hB) where
  toFun x :=
    { toFun := fun w => ⟨fun g => (w : GL (Fin m) k → ℂ) (g * x), by
        obtain ⟨y, hy⟩ := w.2
        exact ⟨rhoW ψ x y, funext fun g => by rw [← Wf_right hψ, hy]⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext w g
    simp
  map_mul' x y := by
    ext w g
    simp [mul_assoc]

theorem tauRep_apply (x : GL (Fin m) k) (w : WSp hψ hI hB) (g : GL (Fin m) k) :
    ((tauRep hψ hI hB x w : WSp hψ hI hB) : GL (Fin m) k → ℂ) g = (w : GL (Fin m) k → ℂ) (g * x) := rfl

theorem tauRep_Phi (x : GL (Fin m) k) (y : WT (m := m) ψ) :
    tauRep hψ hI hB x (Phi hψ hI hB y) = Phi hψ hI hB (rhoW ψ x y) :=
  Subtype.ext (funext fun g => Wf_right hψ y g x)

theorem isSmooth_tau : IsSmooth (tauRep hψ hI hB) := fun w => by
  obtain ⟨y, hy⟩ := w.2
  obtain ⟨K, hKo, -, hK⟩ := exists_fix y
  let S : Subgroup (GL (Fin m) k) :=
    { carrier := {g | tauRep hψ hI hB g w = w}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at *
        rw [hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at *
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hle : K ≤ S := fun κ hκ => by
    show tauRep hψ hI hB κ w = w
    refine Subtype.ext (funext fun g => ?_)
    rw [tauRep_apply, ← hy, Wf_right hψ, hK κ hκ]
  exact Subgroup.isOpen_mono hle hKo

theorem isIrreducible_tau
    (hZ : ∀ Z : Submodule ℂ (WT (m := m) ψ), (∀ g, ∀ z ∈ Z, rhoW ψ g z ∈ Z) →
      (∀ z ∈ Z, B z z = 0) ∨ ∀ x : WT (m := m) ψ, ∃ z ∈ Z, B (x - z) (x - z) = 0)
    {x₀ : WT (m := m) ψ} (hx₀ : B x₀ x₀ ≠ 0) : (tauRep hψ hI hB).IsIrreducible := by
  have hne : Wf ψ hψ I B x₀ ≠ 0 := fun h => hx₀ (by rw [← repr hψ hI hB x₀ x₀, h]; simp; exact map_zero I)
  haveI : Nontrivial (WSp hψ hI hB) := ⟨⟨Phi hψ hI hB x₀, 0, fun h => hne (congrArg Subtype.val h)⟩⟩
  haveI : Nontrivial (Subrepresentation (tauRep hψ hI hB)) := ⟨⊥, ⊤, fun h => by
    have := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top (α := Submodule ℂ (WSp hψ hI hB)) this⟩
  have hPadd : ∀ a b, Phi hψ hI hB (a + b) = Phi hψ hI hB a + Phi hψ hI hB b := fun a b =>
    Subtype.ext (Wf_add hψ hI hB a b)
  have hPsmul : ∀ (c : ℂ) a, Phi hψ hI hB (c • a) = (starRingEnd ℂ) c • Phi hψ hI hB a := fun c a =>
    Subtype.ext (Wf_smul hψ hI hB c a)
  have hPof : ∀ w : WSp hψ hI hB, ∃ y, Phi hψ hI hB y = w := fun w => by
    obtain ⟨y, hy⟩ := w.2
    exact ⟨y, Subtype.ext hy⟩
  refine ⟨fun S => ?_⟩
  let Z : Submodule ℂ (WT (m := m) ψ) :=
    { carrier := {y | Phi hψ hI hB y ∈ S.toSubmodule}
      zero_mem' := by
        show Phi hψ hI hB 0 ∈ S.toSubmodule
        have : Phi hψ hI hB 0 = 0 := by rw [← zero_smul ℂ (0 : WT (m := m) ψ), hPsmul, map_zero, zero_smul]
        rw [this]; exact S.toSubmodule.zero_mem
      add_mem' := fun {a b} ha hb => by
        show Phi hψ hI hB (a + b) ∈ S.toSubmodule
        rw [hPadd]; exact S.toSubmodule.add_mem ha hb
      smul_mem' := fun c a ha => by
        show Phi hψ hI hB (c • a) ∈ S.toSubmodule
        rw [hPsmul]; exact S.toSubmodule.smul_mem _ ha }
  have hinv : ∀ g, ∀ z ∈ Z, rhoW ψ g z ∈ Z := fun g z hz => by
    show Phi hψ hI hB (rhoW ψ g z) ∈ S.toSubmodule
    rw [← tauRep_Phi]; exact S.2 g hz
  rcases hZ Z hinv with h | h
  · refine Or.inl (Subrepresentation.toSubmodule_injective ?_)
    show S.toSubmodule = ⊥
    refine (Submodule.eq_bot_iff _).2 fun w hw => ?_
    obtain ⟨y, rfl⟩ := hPof w
    exact Subtype.ext (Wf_eq_zero hψ hI hB (h y hw))
  · refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
    show S.toSubmodule = ⊤
    refine Submodule.eq_top_iff'.2 fun w => ?_
    obtain ⟨x, rfl⟩ := hPof w
    obtain ⟨z, hz, h0⟩ := h x
    have e : Phi hψ hI hB x = Phi hψ hI hB (x - z) + Phi hψ hI hB z := by rw [← hPadd, sub_add_cancel]
    rw [e, show Phi hψ hI hB (x - z) = 0 from Subtype.ext (Wf_eq_zero hψ hI hB h0), zero_add]
    exact hz

end DiscreteGroups.sglob.LConv

end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.MulRowOfGood
section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConvGenM

variable {k : Type} [Field k] {n : ℕ}

def Nset (m : ℕ) : Set (GL (Fin n) k) :=
  {g | ∀ i l : Fin n, (l ≤ i ∨ l.val < m) → (g : Matrix (Fin n) (Fin n) k) i l = (1 : Matrix (Fin n) (Fin n) k) i l}

def sdS (m : ℕ) (M : Matrix (Fin n) (Fin n) k) : k :=
  ∑ i : Fin n, ∑ l : Fin n, if l.val = i.val + 1 ∧ m ≤ l.val then M i l else 0

def Good (j : ℕ) (x : Matrix (Fin n) (Fin n) k) : Prop :=
  ∀ i l : Fin n, (j ≤ i.val ∨ j + 1 ≤ l.val) → x i l = (1 : Matrix (Fin n) (Fin n) k) i l

theorem mul_col_of_good {j : ℕ} {Y : Matrix (Fin n) (Fin n) k} (hY : Good j Y) (M : Matrix (Fin n) (Fin n) k)
    {i l : Fin n} (hl : j + 1 ≤ l.val) : (M * Y) i l = M i l := by
  rw [Matrix.mul_apply, Finset.sum_eq_single l]
  · rw [hY l l (Or.inr hl), one_apply_eq, mul_one]
  · intro b _ hb; rw [hY b l (Or.inr hl), one_apply_ne hb, mul_zero]
  · simp

theorem mul_row_of_good {j : ℕ} {X : Matrix (Fin n) (Fin n) k} (hX : Good j X) (M : Matrix (Fin n) (Fin n) k)
    {i l : Fin n} (hi : j ≤ i.val) : (X * M) i l = M i l := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hX i i (Or.inl hi), one_apply_eq, one_mul]
  · intro b _ hb; rw [hX i b (Or.inl hi), one_apply_ne (Ne.symm hb), zero_mul]
  · simp

theorem good_conj {j : ℕ} (x : GL (Fin n) k) (hx : Good j (x : Matrix (Fin n) (Fin n) k))
    (hy : Good j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) {g : GL (Fin n) k} (hg : g ∈ Nset (j + 1)) :
    x * g * x⁻¹ ∈ Nset (j + 1) ∧ sdS (j + 1) ((x * g * x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      sdS (j + 1) (g : Matrix (Fin n) (Fin n) k) := by
  set X := (x : Matrix (Fin n) (Fin n) k)
  set Y := ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
  set G := (g : Matrix (Fin n) (Fin n) k)
  have hXY : X * Y = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hval : ((x * g * x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = X * G * Y := by
    simp only [Units.val_mul, X, Y, G]

  have hA : ∀ i l : Fin n, l.val < j + 1 → (X * G * Y) i l = (1 : Matrix (Fin n) (Fin n) k) i l := by
    intro i l hl
    have hGY : ∀ a, (G * Y) a l = Y a l := by
      intro a
      rw [Matrix.mul_apply, ← one_mul Y, Matrix.mul_apply, one_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hb : b.val < j + 1
      · exact congrArg (· * Y b l) (hg a b (Or.inr hb))
      · have h1 : Y b l = 0 := by
          rw [hy b l (Or.inl (by omega)), one_apply_ne]; intro h; rw [h] at hb; omega
        rw [h1, mul_zero, mul_zero]
    rw [Matrix.mul_assoc, Matrix.mul_apply, ← hXY, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ => by rw [hGY]

  have hB : ∀ i l : Fin n, j ≤ i.val → j + 1 ≤ l.val → (X * G * Y) i l = G i l := by
    intro i l hi hl
    rw [mul_col_of_good hy _ hl, mul_row_of_good hx _ hi]
  refine ⟨fun i l hil => ?_, ?_⟩
  · rw [hval]
    by_cases hl : l.val < j + 1
    · exact hA i l hl
    · have hli : l ≤ i := hil.resolve_right hl
      rw [hB i l (by rw [Fin.le_iff_val_le_val] at hli; omega) (by omega)]
      exact hg i l (Or.inl hli)
  · rw [hval, sdS, sdS]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    split_ifs with h
    · exact hB i l (by omega) h.2
    · rfl

end DiscreteGroups.sglob.LConvGenM
end
end

