module

public import Mathlib
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsStableSubmoduleTopWeightLine
section
open Formalism.REAL

namespace GlobalTheory

inductive LoweringWord {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) : ℕ → V → Prop
  | base : LoweringWord E v 0 v
  | step {N : ℕ} {x : V} (a b : Fin n) (h : b < a) :
      LoweringWord E v N x → LoweringWord E v (N + (a.val - b.val)) (E a b x)

section
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
  {E : Fin n → Fin n → Module.End ℂ V} {ν : Fin n → ℂ} {v : V}

theorem glRel_apply_comm (hE : GlRel E) (a b c d : Fin n) (y : V) :
    E a b (E c d y) = E c d (E a b y) + (if b = c then E a d y else 0)
      - (if d = a then E c b y else 0) := by
  have h := congrArg (fun f : Module.End ℂ V => f y) (hE a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  have h1 : (if b = c then E a d else 0) y = if b = c then E a d y else 0 := by
    split_ifs <;> simp
  have h2 : (if d = a then E c b else 0) y = if d = a then E c b y else 0 := by
    split_ifs <;> simp
  rw [h1, h2] at h
  rw [add_sub_assoc, ← h]
  abel

theorem loweringWord_span_lower (a b : Fin n) (hab : b < a) :
    ∀ x ∈ Submodule.span ℂ {x | ∃ N, LoweringWord E v N x},
      E a b x ∈ Submodule.span ℂ {x | ∃ N, LoweringWord E v N x} := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨N, hN⟩ := hx
    exact Submodule.subset_span ⟨_, hN.step a b hab⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem loweringWord_apply_mem (hE : GlRel E) (hv : IsHW E ν v) {N : ℕ} {x : V}
    (hx : LoweringWord E v N x) :
    ∀ a b, E a b x ∈ Submodule.span ℂ {x | ∃ N, LoweringWord E v N x} := by
  induction hx with
  | base =>
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · rw [hv.2 a b h]; exact Submodule.zero_mem _
    · subst h
      rw [hv.1 a]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, LoweringWord.base⟩)
    · exact Submodule.subset_span ⟨_, LoweringWord.base.step a b h⟩
  | step c d h _ ih =>
    intro a b
    rw [glRel_apply_comm hE]
    refine Submodule.sub_mem _ (Submodule.add_mem _ (loweringWord_span_lower c d h _ (ih a b)) ?_) ?_
    · split_ifs
      · exact ih _ _
      · exact Submodule.zero_mem _
    · split_ifs
      · exact ih _ _
      · exact Submodule.zero_mem _

theorem loweringWord_height (hE : GlRel E) (hv : IsHW E ν v) {N : ℕ} {x : V}
    (hx : LoweringWord E v N x) :
    (∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a) x
      = ((∑ a : Fin n, ((a.val : ℕ) : ℂ) * ν a) + (N : ℂ)) • x := by
  induction hx with
  | base =>
    simp [LinearMap.sum_apply, hv.1, Finset.sum_smul, mul_smul]
  | @step N y c d h _ ih =>
    have key : (∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a) (E c d y)
        = E c d ((∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a) y)
          + ((c.val : ℕ) : ℂ) • E c d y - ((d.val : ℕ) : ℂ) • E c d y := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
      simp only [glRel_apply_comm hE _ _ c d y, smul_sub, smul_add, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    rw [key, ih, map_smul]
    have hle : d.val ≤ c.val := le_of_lt h
    push_cast [Nat.cast_sub hle]
    module

theorem loweringWord_zero_or_pos {N : ℕ} {x : V} (hx : LoweringWord E v N x) :
    x = v ∨ 0 < N := by
  cases hx with
  | base => exact Or.inl rfl
  | step c d h _ =>
    right
    have : d.val < c.val := h
    omega

end

theorem exists_stable_submodule_topWeight_line :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
      (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
      ∃ S : Submodule ℂ V, (∀ a b, ∀ x ∈ S, E a b x ∈ S) ∧ v ∈ S ∧
        ∀ x ∈ S, (∀ a, E a a x = ν a • x) → ∃ c : ℂ, x = c • v := by
  intro V _ _ n E ν v hE hv
  refine ⟨Submodule.span ℂ {x | ∃ N, LoweringWord E v N x}, ?_,
    Submodule.subset_span ⟨0, LoweringWord.base⟩, ?_⟩
  · intro a b x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨N, hN⟩ := hx
      exact loweringWord_apply_mem hE hv hN a b
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  · intro x hx hw
    set H : Module.End ℂ V := ∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a with hH
    set h : ℂ := ∑ a : Fin n, ((a.val : ℕ) : ℂ) * ν a with hh
    have hle : Submodule.span ℂ {x | ∃ N, LoweringWord E v N x}
        ≤ Submodule.span ℂ {v} ⊔ ⨆ (μ : ℂ) (_ : μ ≠ h), H.eigenspace μ := by
      rw [Submodule.span_le]
      rintro y ⟨N, hN⟩
      rcases loweringWord_zero_or_pos hN with rfl | hpos
      · exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
      · refine Submodule.mem_sup_right ?_
        have hne : h + (N : ℂ) ≠ h := by
          have : (N : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
          simpa using this
        refine Submodule.mem_iSup_of_mem (h + (N : ℂ)) (Submodule.mem_iSup_of_mem hne ?_)
        rw [Module.End.mem_eigenspace_iff]
        exact loweringWord_height hE hv hN
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hle hx)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hxe : x ∈ H.eigenspace h := by
      rw [Module.End.mem_eigenspace_iff]
      simp [hH, hh, LinearMap.sum_apply, hw, Finset.sum_smul, mul_smul]
    have hve : v ∈ H.eigenspace h := by
      rw [Module.End.mem_eigenspace_iff]
      simp [hH, hh, LinearMap.sum_apply, hv.1, Finset.sum_smul, mul_smul]
    have hze : z ∈ H.eigenspace h := by
      have : z = x - c • v := by rw [← hyz]; abel
      rw [this]
      exact Submodule.sub_mem _ hxe (Submodule.smul_mem _ _ hve)
    have hd := Module.End.eigenspaces_iSupIndep H h
    have hz0 : z = 0 := (Submodule.disjoint_def.1 hd) z hze hz
    exact ⟨c, by rw [← hyz, hz0, add_zero]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GramBlockDiagonalEnergyBound
section
open Formalism.REAL Finset

namespace GlobalTheory

theorem abs_list_prod_map_le_of_abs_le {α : Type} (L : List α) (f n : α → ℝ)
    (h : ∀ a ∈ L, |f a| ≤ n a) : |(L.map f).prod| ≤ (L.map n).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, abs_mul]
    have h1 := h a (by simp)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)

theorem sum_weight_blockDiagonal_eq {ι κ : Type} [Fintype ι] [DecidableEq κ] (B : ι → ι → ℂ)
    (k : ι → κ) (hB : ∀ i j, k i ≠ k j → B i j = 0) (f : κ → ℝ) :
    (∑ i, ∑ j, ((f (k i) : ℝ) : ℂ) * B i j).re =
      ∑ t ∈ Finset.univ.image k, f t *
        (∑ i ∈ Finset.univ.filter (fun i => k i = t),
          ∑ j ∈ Finset.univ.filter (fun j => k j = t), B i j).re := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image k) (g := k)
    (fun i _ => Finset.mem_image_of_mem k (Finset.mem_univ i)), Complex.re_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [← Complex.re_ofReal_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : k i = t := (Finset.mem_filter.mp hi).2
  rw [← Finset.mul_sum, hi', Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs with h
  · rfl
  · exact hB i j (fun e => h (e ▸ hi'))

theorem gram_blockDiagonal_energy_bound :
    ∀ (ι α : Type) [Fintype ι] (B : ι → ι → ℂ) (c : ι → α → ℝ) (L : List α) (n : α → ℝ), (∀ S : Finset ι, 0 ≤ (∑ i ∈ S, ∑ j ∈ S, B i j).re) → (∀ i j, ∀ a ∈ L, c i a ≠ c j a → B i j = 0) → (∀ i, ∀ a ∈ L, |c i a| ≤ n a) → (∑ i, ∑ j, (((L.map (c i)).prod : ℝ) : ℂ) * B i j).re ≤ (L.map n).prod * (∑ i, ∑ j, B i j).re := by
  intro ι α _ B c L n hpos hzero hbd
  classical
  have hB : ∀ i j, L.map (c i) ≠ L.map (c j) → B i j = 0 := by
    intro i j hij
    by_contra hne
    apply hij
    refine List.map_congr_left (fun a ha => ?_)
    by_contra h
    exact hne (hzero i j a ha h)
  have e1 := sum_weight_blockDiagonal_eq B (fun i => L.map (c i)) hB List.prod
  have e2 := sum_weight_blockDiagonal_eq B (fun i => L.map (c i)) hB (fun _ => 1)
  simp only [Complex.ofReal_one, one_mul] at e2
  rw [e1, e2, Finset.mul_sum]
  refine Finset.sum_le_sum (fun t ht => ?_)
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
  exact mul_le_mul_of_nonneg_right
    ((le_abs_self _).trans (abs_list_prod_map_le_of_abs_le L (c i) n (hbd i))) (hpos _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HighestWeightTensorStandard
section
open Formalism.REAL

namespace GlobalTheory

theorem highestWeight_tensor_standard : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (θ : Fin (n + 1) → ℂ) (lam : ℂ) (y : (PiLp 2 (fun _ : Fin (n + 1) => V))), (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → y ≠ 0 → IsHW Et θ y → Om y = lam • y → ∃ c, y c ≠ 0 ∧ IsHW E (fun a => θ a - if a = c then 1 else 0) (y c) ∧ lam = θ c - 1 - ((c : ℕ) : ℂ) := by
  classical
  intro V _ _ _ n E Et Om θ lam y hEt hOm hy hw hlam
  obtain ⟨h1, h2⟩ := hw
  have hne : (Finset.univ.filter (fun c => y c ≠ 0)).Nonempty := by
    by_contra h
    apply hy
    ext c
    by_contra hc
    exact h ⟨c, by simpa using hc⟩
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image _ id hne
  have hc0 : y c ≠ 0 := by simpa using hc
  have hz : ∀ d, c < d → y d = 0 := by
    intro d hd
    by_contra h
    exact absurd (hmax d (by simpa using h)) (not_le.mpr hd)
  have hup : ∀ a b, a < b → ∀ e, E a b (y e) = - if e = a then y b else 0 := by
    intro a b hab e
    have h := hEt a b y e
    have h0 : Et a b y = 0 := h2 a b hab
    rw [h0] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have hdiag : ∀ a, E a a (y c) = (θ a - if a = c then 1 else 0) • y c := by
    intro a
    have h := hEt a a y c
    have h0 : Et a a y = θ a • y := h1 a
    rw [h0] at h
    have h' : E a a (y c) = θ a • y c - if c = a then y a else 0 := by
      rw [eq_sub_iff_add_eq, ← h]; rfl
    rw [h']
    by_cases hca : c = a
    · subst hca; simp [sub_smul]
    · simp [hca, Ne.symm hca]
  have hraise : ∀ a b, a < b → E a b (y c) = 0 := by
    intro a b hab
    rw [hup a b hab c]
    by_cases hca : c = a
    · subst hca; simp [hz b hab]
    · simp [hca]
  refine ⟨c, hc0, ⟨hdiag, hraise⟩, ?_⟩
  have hterm : ∀ d, E d c (y d) =
      ((if d = c then θ c - 1 else 0) - if d < c then 1 else 0 : ℂ) • y c := by
    intro d
    rcases lt_trichotomy d c with h | h | h
    · rw [hup d c h d]; simp [h, h.ne]
    · subst h; rw [hdiag]; simp
    · simp [hz d h, h.ne', not_lt.mpr h.le]
  have hsum : lam • y c = (θ c - 1 - ((c : ℕ) : ℂ)) • y c := by
    have h := hOm y c
    rw [hlam] at h
    have h' : lam • y c = ∑ d, E d c (y d) := h
    rw [h', Finset.sum_congr rfl (fun d _ => hterm d), ← Finset.sum_smul,
      Finset.sum_sub_distrib]
    congr 2
    · simp
    · rw [Finset.sum_boole]
      have : Finset.univ.filter (fun d => d < c) = Finset.Iio c := by ext d; simp
      rw [this, Fin.card_Iio]
  exact smul_left_injective ℂ hc0 hsum

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HwComponentTensorDualStandard
section
open Formalism.REAL
namespace GlobalTheory

theorem hw_component_tensor_dual_standard (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (θ : Fin (n + 1) → ℂ) (lam : ℂ) (y : (PiLp 2 (fun _ : Fin (n + 1) => V))) (hEt : ∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) (hOm : ∀ y a, Om y a = ∑ c, E a c (y c)) (hy : y ≠ 0) (hw : IsHW Et θ y) (hl : Om y = lam • y) : ∃ c, y c ≠ 0 ∧ IsHW E (fun a => θ a + if a = c then 1 else 0) (y c) ∧ lam = θ c + 1 - ((c : ℕ) : ℂ) + (n : ℂ) := by
  classical
  have hex : ∃ c, y c ≠ 0 := by
    by_contra h
    push_neg at h
    exact hy (by ext c; simpa using h c)
  obtain ⟨c, hc, hmin⟩ := (wellFounded_lt (α := Fin (n + 1))).has_min {c | y c ≠ 0} hex
  have hlt : ∀ d, d < c → y d = 0 := fun d hd => by
    by_contra h
    exact hmin d h hd
  unfold IsHW at hw ⊢
  obtain ⟨hd, hu⟩ := hw
  have hc' : y c ≠ 0 := hc
  have hdiag : ∀ a, E a a (y c) = (θ a + if a = c then 1 else 0) • y c := by
    intro a
    have h := hEt a a y c
    rw [hd a, PiLp.smul_apply] at h
    by_cases hac : a = c
    · subst hac
      simp only [if_true] at h ⊢
      rw [add_smul, one_smul, h, sub_add_cancel]
    · have hca : ¬ c = a := fun e => hac e.symm
      simp only [hac, hca, if_false, sub_zero, add_zero] at h ⊢
      exact h.symm
  refine ⟨c, hc', ⟨hdiag, ?_⟩, ?_⟩
  · intro a b hab
    have h := hEt a b y c
    rw [hu a b hab, PiLp.zero_apply] at h
    by_cases hcb : c = b
    · subst hcb
      simp only [if_true, hlt a hab, sub_zero] at h
      exact h.symm
    · simp only [hcb, if_false, sub_zero] at h
      exact h.symm
  · have h := hOm y c
    rw [hl, PiLp.smul_apply] at h
    have hterm : ∀ d, E c d (y d) =
        ((if d = c then θ c + 1 else 0) + (if c < d then (1 : ℂ) else 0)) • y c := by
      intro d
      rcases lt_trichotomy d c with hdc | hdc | hdc
      · simp [hlt d hdc, hdc.ne, hdc.not_gt]
      · subst hdc
        simp [hdiag d]
      · have h2 := hEt c d y d
        rw [hu c d hdc, PiLp.zero_apply] at h2
        simp only [if_true] at h2
        have h3 := (sub_eq_zero.mp h2.symm)
        simp [h3, hdc, hdc.ne']
    simp_rw [hterm] at h
    rw [← Finset.sum_smul] at h
    have h4 := smul_left_injective ℂ hc' h
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_boole] at h4
    have h5 : (Finset.univ.filter (fun d : Fin (n + 1) => c < d)).card = n - c := by
      have : Finset.univ.filter (fun d : Fin (n + 1) => c < d) = Finset.Ioi c := by
        ext d; simp
      rw [this, Fin.card_Ioi]; omega
    rw [h5, Nat.cast_sub (Nat.lt_succ_iff.mp c.2)] at h4
    rw [h4]; ring
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LastComatrixRowInvertsDual
section
open Formalism.REAL

namespace GlobalTheory

theorem _root_.GlobalTheory.lastComatrixRow_inverts_dual : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (m : Fin (n + 1) → ℂ), _root_.Formalism.REAL.GlRel E → (∀ w v, _root_.Formalism.REAL.qdet E w v = (∏ j, (w + m j)) • v) → (∀ y a, Om y a = ∑ c, E a c (y c)) → ∃ K : ℂ → ((PiLp 2 (fun _ : Fin (n + 1) => V)) →ₗ[ℂ] V), (∀ u x, K u ((u - (n : ℂ)) • x + Om x) = (∏ j, (u + m j)) • x (Fin.last n)) ∧ ∀ u v, K u (PiLp.single 2 (Fin.last n) v) = _root_.Formalism.REAL.qdet (fun a b : Fin n => E a.castSucc b.castSucc) u v := by
  intro V _ _ _ n E Om m hE hdet hOm
  let c : ℂ → Fin (n + 1) → Module.End ℂ V := fun u j =>
    ((((-1 : ℤ) ^ ((Fin.last n : ℕ) + (j : ℕ)) : ℤ) : Module.End ℂ V)) * _root_.Formalism.REAL.qminor E j.succAbove (Fin.last n).succAbove u
  refine ⟨fun u => ∑ j, (c u j) ∘ₗ ((LinearMap.proj j).comp (WithLp.linearEquiv 2 ℂ (Fin (n + 1) → V)).toLinearMap), ?_, ?_⟩
  · intro u x
    have hproj : ∀ (y : PiLp 2 (fun _ : Fin (n + 1) => V)) j, (WithLp.addEquiv 2 (Fin (n + 1) → V)).toFun y j = y.ofLp j := fun _ _ => rfl
    have hcom := _root_.Formalism.REAL.qComatrix (Module.End ℂ V) n E hE u (Fin.last n)
    have hT : ∀ j, (u - (n : ℂ)) • x j + Om x j = ∑ l, _root_.Formalism.REAL.Tm E (u - (n : ℂ)) j l (x l) := by
      intro j
      have hite : ∀ l, (if j = l then (u - (n : ℂ)) • (1 : Module.End ℂ V) else 0) (x l) = if j = l then (u - (n : ℂ)) • x l else 0 := by
        intro l; split_ifs <;> simp
      simp only [_root_.Formalism.REAL.shiftedGenerator_eq_ite_smul_add, LinearMap.add_apply, Finset.sum_add_distrib, hOm, ite_smul, zero_smul, hite, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [LinearMap.sum_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, WithLp.linearEquiv_apply, LinearMap.proj_apply, hproj, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, hT, map_sum]
    rw [Finset.sum_comm]
    simp only [← Module.End.mul_apply, ← LinearMap.sum_apply]
    have hite : ∀ l, (if Fin.last n = l then _root_.Formalism.REAL.qdet E u else 0) (x l) = if Fin.last n = l then _root_.Formalism.REAL.qdet E u (x l) else 0 := by
      intro l; split_ifs <;> simp
    simp only [c, hcom, hite, Finset.sum_ite_eq, Finset.mem_univ, if_true, hdet]
  · intro u v
    have hproj : ∀ (y : PiLp 2 (fun _ : Fin (n + 1) => V)) j, (WithLp.addEquiv 2 (Fin (n + 1) → V)).toFun y j = y.ofLp j := fun _ _ => rfl
    rw [LinearMap.sum_apply, Finset.sum_eq_single (Fin.last n)]
    · simp only [c, LinearMap.comp_apply, LinearEquiv.coe_coe, WithLp.linearEquiv_apply, LinearMap.proj_apply, hproj, PiLp.ofLp_single, Pi.single_eq_same, Fin.succAbove_last, Module.End.mul_apply]
      have hsign : ((-1 : ℤ) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ))) = 1 := by
        rw [← two_mul, pow_mul]; simp
      rw [hsign, Int.cast_one, Module.End.one_apply]
      unfold _root_.Formalism.REAL.qdet
      rw [_root_.Formalism.REAL.quantumMinor_eq_sum_term, _root_.Formalism.REAL.quantumMinor_eq_sum_term]
      unfold _root_.Formalism.REAL.exchangeTwo_self_eq_one
      simp only [_root_.Formalism.REAL.shiftedGenerator_eq_ite_smul_add, Fin.castSucc_inj, id]
    · intro j _ hj
      simp [LinearMap.comp_apply, hproj, PiLp.ofLp_single, Pi.single_eq_of_ne hj]
    · simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevZeroOfKHighest
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem lev_zero_of_kHighest : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (w : M), GlRel E → IsUnitary ε E → KHighest ε E (lowK ε μ) w → FiniteDimensional ℂ (kSpan ε E w) → Lev ε E μ 0 w := by
  intro M _ _ n ε E μ w hrel _ hhi hfin
  have hk : KRel ε E := glRel_kRel ε E hrel
  have hsq : ckv ε (lowK ε μ) ≤ (Real.sqrt (ckv ε (lowK ε μ)) + 4 * (n : ℝ) * ((0 : ℕ) : ℝ)) ^ 2 := by
    rcases le_total 0 (ckv ε (lowK ε μ)) with h | h
    · simp [Real.sq_sqrt h]
    · simp [Real.sqrt_eq_zero'.mpr h, h]
  refine ⟨⟨kSpan ε E w, hfin, ?_, mem_compact_span_self w, ?_⟩, ?_⟩
  · intro a b hab x hx
    exact compact_span_stable w a b hab x hx
  · intro x hx
    rw [compact_casimir_span_holds M n ε E (lowK ε μ) w hk hhi x hx, inner_smul_right,
      inner_self_eq_norm_sq_to_K]
    have hx2 : (0 : ℝ) ≤ ‖x‖ ^ 2 := by positivity
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right hsq hx2)
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    congr 1
    norm_cast
  · apply Submodule.subset_span
    exact ⟨lowK ε μ, by simp, hhi.1⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorCommOfCommColumns
section
open Formalism.REAL Finset

namespace GlobalTheory

theorem qminor_comm_of_comm_columns (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ)
    (E : Fin n → Fin n → A) (x : A) (a b : Fin t → Fin n) (u : ℂ)
    (h : ∀ (c : Fin n) (i : Fin t), E c (b i) * x = x * E c (b i)) :
    qminor E a b u * x = x * qminor E a b u := by
  have hT : ∀ (v : ℂ) (c : Fin n) (i : Fin t), Commute (Tm E v c (b i)) x := by
    intro v c i
    have h1 : Commute (E c (b i)) x := h c i
    unfold Tm
    refine Commute.add_left ?_ h1
    split_ifs
    · exact Algebra.commutes v x
    · exact Commute.zero_left x
  change Commute (qminor E a b u) x
  unfold qminor
  refine Commute.sum_left _ _ _ fun σ _ => ?_
  have hp : ∀ f : Fin t → A, (∀ i, Commute (f i) x) → Commute (List.ofFn f).prod x := by
    intro f hf
    refine Commute.list_prod_left _ _ fun y hy => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    exact hf i
  exact (Int.cast_commute _ x).mul_left (hp _ fun i => hT _ _ i)

end GlobalTheory
end

