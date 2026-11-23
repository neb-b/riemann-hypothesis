module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.KhwWeightEqOfIrr
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section KIrr

variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X} {Λ : Fin n → ℝ} {V : Submodule ℂ X}

def kirrWord (A : Fin n → Fin n → Module.End ℂ X) (u : X) : List (Fin n × Fin n) → X
  | [] => u
  | p :: l => A p.1 p.2 (kirrWord A u l)

def kirrWt (ν : Fin n → ℝ) : List (Fin n × Fin n) → Fin n → ℝ
  | [] => ν
  | p :: l => kirrWt ν l + root p.1 p.2

def KirrLow (ε : Fin n → Bool) (l : List (Fin n × Fin n)) : Prop :=
  ∀ p ∈ l, p.2 < p.1 ∧ ε p.1 = ε p.2

def kirrSpan (ε : Fin n → Bool) (A : Fin n → Fin n → Module.End ℂ X) (u : X) : Submodule ℂ X :=
  Submodule.span ℂ {x | ∃ l, KirrLow ε l ∧ x = kirrWord A u l}

def kirrPs (k : ℕ) (μ : Fin n → ℝ) : ℝ := ∑ a ∈ univ.filter (fun a : Fin n => a.val < k), μ a

def kirrH (A : Fin n → Fin n → Module.End ℂ X) (k : ℕ) : Module.End ℂ X :=
  ∑ a ∈ univ.filter (fun a : Fin n => a.val < k), A a a

private theorem glRep_apply_commutator (hA : IsGlRep A) (a b c d : Fin n) (v : X) :
    A a b (A c d v) = A c d (A a b v) + ((if b = c then A a d else 0) - if d = a then A c b else 0) v :=
  eq_add_of_sub_eq' (by
    have h := LinearMap.congr_fun (hA a b c d) v
    rw [LinearMap.sub_apply] at h
    exact h)

theorem kirrWord_wt (hA : IsGlRep A) {ν : Fin n → ℝ} {u : X} (hu : ∀ a, A a a u = (ν a : ℂ) • u) :
    ∀ l a, A a a (kirrWord A u l) = (kirrWt ν l a : ℂ) • kirrWord A u l
  | [], a => by simpa [kirrWord, kirrWt] using hu a
  | p :: l, a => by
    obtain ⟨b, c⟩ := p
    have ih := kirrWord_wt hA hu l a
    have key := LinearMap.congr_fun (hA a a b c) (kirrWord A u l)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at key
    simp only [kirrWord, kirrWt]
    rw [sub_eq_iff_eq_add, ih, map_smul] at key
    rw [key]
    by_cases h1 : a = b <;> by_cases h2 : c = a
    · subst h1; subst h2; simp [root]
    · subst h1; (simp [root, h2, Ne.symm h2, add_smul]; abel)
    · subst h2; (simp [root, h1, add_smul]; abel)
    · simp [root, h1, h2, Ne.symm h2]

theorem kirrWord_mem (u : X) {l : List (Fin n × Fin n)} (hl : KirrLow ε l) :
    kirrWord A u l ∈ kirrSpan ε A u := Submodule.subset_span ⟨l, hl, rfl⟩

theorem kirr_low_mem {u : X} {a b : Fin n} (hba : b < a) (hab : ε a = ε b) {x : X}
    (hx : x ∈ kirrSpan ε A u) : A a b x ∈ kirrSpan ε A u := by
  have h : kirrSpan ε A u ≤ (kirrSpan ε A u).comap (A a b) := Submodule.span_le.2 (by
    rintro _ ⟨l, hl, rfl⟩
    exact Submodule.subset_span ⟨(a, b) :: l, fun p hp => by
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hba, hab⟩
      · exact hl p hp, rfl⟩)
  exact h hx

theorem kirr_compact_word (hA : IsGlRep A) {ν : Fin n → ℝ} {u : X} (hu : IsKHWVec ε A ν u) :
    ∀ l, KirrLow ε l → ∀ a b, ε a = ε b → A a b (kirrWord A u l) ∈ kirrSpan ε A u := by
  intro l
  induction l with
  | nil =>
    intro _ a b hab
    rcases lt_trichotomy a b with h | rfl | h
    · show A a b u ∈ _
      rw [hu.2 a b h hab]; exact Submodule.zero_mem _
    · show A a a u ∈ _
      rw [hu.1 a]
      exact Submodule.smul_mem _ _ (kirrWord_mem (l := []) u (fun p hp => by simp at hp))
    · exact kirrWord_mem (l := [(a, b)]) u (fun p hp => by
        rw [List.mem_singleton] at hp; subst hp; exact ⟨h, hab⟩)
  | cons p l ih =>
    intro hl a b hab
    obtain ⟨x, y⟩ := p
    have hl' : KirrLow ε l := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hxy : y < x ∧ ε x = ε y := hl (x, y) (by simp)
    have hw := ih hl'
    show A a b (A x y (kirrWord A u l)) ∈ _
    rw [glRep_apply_commutator hA]
    refine Submodule.add_mem _ (kirr_low_mem hxy.1 hxy.2 (hw a b hab)) ?_
    rw [LinearMap.sub_apply]
    refine Submodule.sub_mem _ ?_ ?_
    · split_ifs with h
      · subst h; exact hw _ _ (hab.trans hxy.2)
      · rw [LinearMap.zero_apply]; exact Submodule.zero_mem _
    · split_ifs with h
      · subst h; exact hw _ _ (hxy.2.trans hab)
      · rw [LinearMap.zero_apply]; exact Submodule.zero_mem _

theorem kirrSpan_kStable (hA : IsGlRep A) {ν : Fin n → ℝ} {u : X} (hu : IsKHWVec ε A ν u) :
    IsKStableSub ε A (kirrSpan ε A u) := by
  intro a b hab v hv
  have h : kirrSpan ε A u ≤ (kirrSpan ε A u).comap (A a b) := Submodule.span_le.2 (by
    rintro _ ⟨l, hl, rfl⟩
    exact kirr_compact_word hA hu l hl a b hab)
  exact h hv

theorem kirrSpan_le (hV : IsKStableSub ε A V) {u : X} (hu : u ∈ V) : kirrSpan ε A u ≤ V := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨l, hl, rfl⟩
  induction l with
  | nil => exact hu
  | cons p l ih =>
    exact hV p.1 p.2 (hl p (by simp)).2 _ (ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)))

theorem kirrPs_wt (k : ℕ) (ν : Fin n → ℝ) :
    ∀ l, KirrLow ε l → kirrPs k (kirrWt ν l) ≤ kirrPs k ν
  | [], _ => le_rfl
  | p :: l, hl => by
    have ih := kirrPs_wt k ν l fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp := hl p List.mem_cons_self
    have hr : kirrPs k (root p.1 p.2) ≤ 0 := by
      unfold kirrPs root
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_pi_single', Finset.mem_filter,
        Finset.mem_univ, true_and]
      have h3 : (p.2 : ℕ) < p.1 := hp.1
      split_ifs with h1 h2 <;> first | (exfalso; omega) | norm_num
    have hadd : kirrPs k (kirrWt ν (p :: l)) = kirrPs k (kirrWt ν l) + kirrPs k (root p.1 p.2) := by
      simp [kirrPs, kirrWt, Finset.sum_add_distrib]
    linarith

theorem kirrH_apply (k : ℕ) {μ : Fin n → ℝ} {x : X} (hx : ∀ a, A a a x = (μ a : ℂ) • x) :
    kirrH A k x = (kirrPs k μ : ℂ) • x := by
  rw [kirrH, LinearMap.sum_apply]
  simp only [hx, kirrPs, Complex.ofReal_sum, Finset.sum_smul]

theorem kirrPs_le (hA : IsGlRep A) (hV : IsKIrrHW ε A Λ V) {u : X} (hu : u ∈ V) (hu0 : u ≠ 0)
    {ν : Fin n → ℝ} (hν : IsKHWVec ε A ν u) {w : X} (hw : w ∈ V) (hw0 : w ≠ 0) {μ : Fin n → ℝ}
    (hμ : ∀ a, A a a w = (μ a : ℂ) • w) (k : ℕ) : kirrPs k μ ≤ kirrPs k ν := by
  classical
  obtain ⟨-, hVs, hirr, -⟩ := id hV
  have hspan : kirrSpan ε A u = V := by
    rcases hirr _ (kirrSpan_le hVs hu) (kirrSpan_kStable hA hν) with h | h
    · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ kirrWord_mem (l := []) u (fun p hp => by simp at hp))) hu0
    · exact h
  have hle : kirrSpan ε A u ≤
      ⨆ z ∈ {z : ℂ | ∃ r : ℝ, r ≤ kirrPs k ν ∧ z = r}, Module.End.eigenspace (kirrH A k) z :=
    Submodule.span_le.2 (by
      rintro _ ⟨l, hl, rfl⟩
      refine Submodule.mem_iSup_of_mem ((kirrPs k (kirrWt ν l) : ℝ) : ℂ)
        (Submodule.mem_iSup_of_mem (Set.mem_setOf.2 ⟨_, kirrPs_wt k ν l hl, rfl⟩) ?_)
      rw [Module.End.mem_eigenspace_iff]
      exact kirrH_apply k (kirrWord_wt hA hν.1 l))
  have hwS := hle (by rw [hspan]; exact hw)
  by_contra hlt
  push_neg at hlt
  have hwE : w ∈ Module.End.eigenspace (kirrH A k) ((kirrPs k μ : ℝ) : ℂ) := by
    rw [Module.End.mem_eigenspace_iff]; exact kirrH_apply k hμ
  have hx : ((kirrPs k μ : ℝ) : ℂ) ∉ {z : ℂ | ∃ r : ℝ, r ≤ kirrPs k ν ∧ z = r} := by
    rintro ⟨r, hr, he⟩
    have := Complex.ofReal_injective he
    linarith
  have hd : Disjoint (Module.End.eigenspace (kirrH A k) ((kirrPs k μ : ℝ) : ℂ))
      (⨆ z ∈ {z : ℂ | ∃ r : ℝ, r ≤ kirrPs k ν ∧ z = r}, Module.End.eigenspace (kirrH A k) z) := by
    first
      | exact (Module.End.eigenspaces_iSupIndep (kirrH A k)).disjoint_biSup hx
      | exact (Module.End.eigenspaces_independent (kirrH A k)).disjoint_biSup hx
  exact hw0 (Submodule.disjoint_def.1 hd w hwE hwS)

private theorem kirrPs_succ (μ : Fin n → ℝ) (a : Fin n) : kirrPs (a.val + 1) μ = kirrPs a.val μ + μ a := by
  simp only [kirrPs]
  rw [show univ.filter (fun b : Fin n => b.val < a.val + 1) = insert a (univ.filter (fun b : Fin n => b.val < a.val)) by
    ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]; omega]
  rw [Finset.sum_insert (by simp), add_comm]

theorem kirr_eq_of_ps {μ ν : Fin n → ℝ} (h : ∀ k, kirrPs k μ = kirrPs k ν) : μ = ν := by
  funext a
  have h1 := h (a.val + 1)
  rw [kirrPs_succ, kirrPs_succ, h a.val] at h1
  linarith

theorem khw_weight_eq_of_irr (hA : IsGlRep A) (hV : IsKIrrHW ε A Λ V) {u : X} (hu : u ∈ V)
    (hu0 : u ≠ 0) {ν : Fin n → ℝ} (hν : IsKHWVec ε A ν u) : ν = Λ := by
  obtain ⟨-, -, -, w, hw, hw0, hwΛ⟩ := id hV
  exact kirr_eq_of_ps fun k =>
    le_antisymm (kirrPs_le hA hV hw hw0 hwΛ hu hu0 hν.1 k) (kirrPs_le hA hV hu hu0 hν hw hw0 hwΛ.1 k)

theorem casimirK_irr (hA : IsGlRep A) (hV : IsKIrrHW ε A Λ V) :
    ∀ v ∈ V, casimirK ε A v = (casValK ε Λ : ℂ) • v := by
  obtain ⟨-, hst, hirr, w, hwV, hw0, hwK⟩ := hV
  let S : Submodule ℂ X := V ⊓ (casimirK ε A).eigenspace (casValK ε Λ : ℂ)
  have hS : IsKStableSub ε A S := by
    intro a b hab v hv
    have hv2 := Module.End.mem_eigenspace_iff.1 hv.2
    refine ⟨hst a b hab v hv.1, Module.End.mem_eigenspace_iff.2 ?_⟩
    have := LinearMap.congr_fun (casimirK_comm ε hA a b hab) v
    simp only [Module.End.mul_apply] at this
    rw [this, hv2, map_smul]
  rcases hirr S inf_le_left hS with h | h
  · exfalso
    have hwS : w ∈ S := ⟨hwV, Module.End.mem_eigenspace_iff.2 (casimirK_khwVec ε hA hwK)⟩
    rw [h] at hwS
    exact hw0 ((Submodule.mem_bot ℂ).1 hwS)
  · intro v hv
    rw [← h] at hv
    exact Module.End.mem_eigenspace_iff.1 hv.2

end KIrr

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Layers

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem layer_le_succ (k : ℕ) : layer ε E V k ≤ layer ε E V (k + 1) := by
  show layer ε E V k ≤ layer ε E V k ⊔ _
  exact le_sup_left

theorem layer_mono {k l : ℕ} (hkl : k ≤ l) : layer ε E V k ≤ layer ε E V l := by
  exact monotone_nat_of_le_succ (fun k => layer_le_succ (ε := ε) (E := E) (V := V) k) hkl

theorem apply_mem_layer_succ_nc {a b : Fin n} (hab : ε a ≠ ε b) {k : ℕ} {v : M}
    (hv : v ∈ layer ε E V k) : E a b v ∈ layer ε E V (k + 1) := by
  have h1 : (layer ε E V k).map (E a b) ≤ layer ε E V (k + 1) := by
    show _ ≤ layer ε E V k ⊔ ⨆ (a : Fin n) (b : Fin n) (_ : ε a ≠ ε b), (layer ε E V k).map (E a b)
    exact le_sup_of_le_right (le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le hab le_rfl)))
  exact h1 (Submodule.mem_map_of_mem hv)

theorem layer_le_of_stable {T : Submodule ℂ M} (hVT : V ≤ T)
    (hT : ∀ a b, ∀ v ∈ T, E a b v ∈ T) (k : ℕ) : layer ε E V k ≤ T := by
  induction k with
  | zero => exact hVT
  | succ k ih =>
    show layer ε E V k ⊔ _ ≤ T
    refine sup_le ih (iSup_le fun a => iSup_le fun b => iSup_le fun _ => ?_)
    rw [Submodule.map_le_iff_le_comap]
    intro v hv
    exact hT a b v (ih hv)

theorem layer_le_genSub (k : ℕ) : layer ε E V k ≤ genSub E V := by
  have hVT : V ≤ genSub E V := by
    unfold genSub
    apply le_sInf
    intro T hT
    exact hT.1
  have hStable : ∀ a b, ∀ v ∈ genSub E V, E a b v ∈ genSub E V := by
    intro a b v hv
    unfold genSub at hv ⊢
    simp only [Submodule.mem_sInf, Set.mem_setOf_eq] at hv ⊢
    intro T hT
    exact hT.2 a b v (hv T hT)
  exact layer_le_of_stable hVT hStable k

theorem layer_kStable (hE : IsGlRep E) (hV : IsKStableSub ε E V) (k : ℕ) :
    IsKStableSub ε E (layer ε E V k) := by
  induction k with
  | zero => exact hV
  | succ k ih =>
    intro a b hab
    have key : layer ε E V (k + 1) ≤ (layer ε E V (k + 1)).comap (E a b) := by
      show layer ε E V k ⊔ _ ≤ _
      refine sup_le (fun v hv => layer_le_succ k (ih a b hab v hv))
        (iSup_le fun c => iSup_le fun d => iSup_le fun hcd => ?_)
      rw [Submodule.map_le_iff_le_comap]
      intro v hv
      rw [Submodule.mem_comap, Submodule.mem_comap]
      have h := congrArg (fun f : Module.End ℂ M => f v) (hE a b c d)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
      have h2 : E a b (E c d v) = E c d (E a b v) +
          ((if b = c then E a d else 0) v - (if d = a then E c b else 0) v) := by
        rw [← h]
        abel
      rw [h2]
      refine Submodule.add_mem _ (apply_mem_layer_succ_nc hcd (ih a b hab v hv))
        (Submodule.sub_mem _ ?_ ?_)
      · split_ifs with hbc
        · exact apply_mem_layer_succ_nc (fun h' => hcd (by rw [← hbc, ← hab, h'])) hv
        · simp
      · split_ifs with hda
        · exact apply_mem_layer_succ_nc (fun h' => hcd (by rw [hda, hab]; exact h')) hv
        · simp
    intro v hv
    exact key hv

theorem apply_mem_layer_succ (hE : IsGlRep E) (hV : IsKStableSub ε E V) (a b : Fin n) {k : ℕ}
    {v : M} (hv : v ∈ layer ε E V k) : E a b v ∈ layer ε E V (k + 1) := by
  by_cases hab : ε a = ε b
  · exact layer_le_succ k (layer_kStable hE hV k a b hab v hv)
  · exact apply_mem_layer_succ_nc hab hv

theorem genSub_eq_iSup_layer (hE : IsGlRep E) (hV : IsKStableSub ε E V) :
    genSub E V = ⨆ k, layer ε E V k := by
  have hmono : Monotone (layer ε E V) := monotone_nat_of_le_succ fun k => layer_le_succ k
  refine le_antisymm (sInf_le ⟨le_iSup_of_le 0 le_rfl, fun a b v hv => ?_⟩) (iSup_le layer_le_genSub)
  obtain ⟨k, hk⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hv
  exact (le_iSup (layer ε E V) (k + 1)) (apply_mem_layer_succ hE hV a b hk)

theorem finiteDimensional_layer (hV : FiniteDimensional ℂ V) (k : ℕ) :
    FiniteDimensional ℂ (layer ε E V k) := by
  induction k with
  | zero => exact hV
  | succ k ih =>
    show FiniteDimensional ℂ ↥(layer ε E V k ⊔
      ⨆ (a : Fin n) (b : Fin n) (_ : ε a ≠ ε b), (layer ε E V k).map (E a b))
    infer_instance

theorem casimir_genSub (hE : IsGlRep E) {c : ℂ} (hc : ∀ v ∈ V, casimir E v = c • v) :
    ∀ v ∈ genSub E V, casimir E v = c • v := by
  intro v hv
  have hle : genSub E V ≤ LinearMap.ker (casimir E - c • LinearMap.id) := by
    refine sInf_le ⟨fun w hw => ?_, fun a b w hw => ?_⟩
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        hc w hw, sub_self]
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero] at hw ⊢
      have h := congrArg (fun f : Module.End ℂ M => f w) (casimir_comm hE a b)
      simp only [Module.End.mul_apply] at h
      rw [h, hw, map_smul]
  have h := hle hv
  rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero] at h

end Layers

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Permute
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Defs

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

abbrev Big (n k : ℕ) (M : Type*) := PiLp 2 (fun _ : Fin k → Fin n × Fin n => M)

def coord (k : ℕ) (κ : Fin k → Fin n × Fin n) : Big n k M →ₗ[ℂ] M :=
  LinearMap.proj (R := ℂ) (φ := fun _ : Fin k → Fin n × Fin n => M) κ ∘ₗ
    (WithLp.linearEquiv 2 ℂ ((Fin k → Fin n × Fin n) → M)).toLinearMap

def ofCoords {X : Type*} [AddCommGroup X] [Module ℂ X] (k : ℕ)
    (f : (Fin k → Fin n × Fin n) → (X →ₗ[ℂ] M)) : X →ₗ[ℂ] Big n k M :=
  (WithLp.linearEquiv 2 ℂ ((Fin k → Fin n × Fin n) → M)).symm.toLinearMap ∘ₗ LinearMap.pi f

def mAct (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) (a b : Fin n) : Module.End ℂ (Big n k M) :=
  ofCoords k fun κ => E a b ∘ₗ coord k κ

def factorAd (k : ℕ) (i : Fin k) (a b : Fin n) : Module.End ℂ (Big n k M) :=
  ofCoords k fun κ =>
    (if (κ i).1 = a then coord k (Function.update κ i (b, (κ i).2)) else 0) -
      (if (κ i).2 = b then coord k (Function.update κ i ((κ i).1, a)) else 0)

def bAct (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) (a b : Fin n) : Module.End ℂ (Big n k M) :=
  mAct E k a b + ∑ i, factorAd k i a b

def factorCasimir (ε : Fin n → Bool) (k : ℕ) : Module.End ℂ (Big n k M) :=
  casimirK ε (fun a b => ∑ i, factorAd (M := M) k i a b)

def crossOp (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) (i : Fin k) :
    Module.End ℂ (Big n k M) :=
  ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), factorAd k i a b * mAct E k b a

def ncV (ε : Fin n → Bool) (V : Submodule ℂ M) (k : ℕ) : Submodule ℂ (Big n k M) :=
  ⨅ κ : Fin k → Fin n × Fin n,
    (if ∀ i, ε (κ i).1 ≠ ε (κ i).2 then V else ⊥).comap (coord k κ)

def word (E : Fin n → Fin n → Module.End ℂ M) {k : ℕ} (κ : Fin k → Fin n × Fin n) :
    Module.End ℂ M :=
  (List.ofFn fun i => E (κ i).1 (κ i).2).prod

def phi (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) : Big n k M →ₗ[ℂ] M :=
  ∑ κ, word E κ ∘ₗ coord k κ

def slice {k : ℕ} (i : Fin k) (κ : Fin k → Fin n × Fin n) (F : Big n k M) : Big n 1 M :=
  WithLp.toLp 2 (fun ι : Fin 1 → Fin n × Fin n => F (Function.update κ i (ι 0)))

def permute {k : ℕ} (σ : Equiv.Perm (Fin k)) (F : Big n k M) : Big n k M :=
  WithLp.toLp 2 (fun κ => F (κ ∘ σ))

def Wm (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) :
    Submodule ℂ (Big n 1 M) :=
  ⨆ (θ : ℝ) (_ : θ < 0), Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1

def Wp (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) :
    Submodule ℂ (Big n 1 M) :=
  ⨆ (θ : ℝ) (_ : 0 < θ), Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1

end Defs

end ReciprocityTheory.ChartRestriction.DS
end
end

