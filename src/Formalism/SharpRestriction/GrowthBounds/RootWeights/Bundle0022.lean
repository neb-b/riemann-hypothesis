module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.CasimirIsotypicNoHigherWeight
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantProjectionRangeTrivial
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.TraceProjectionIsInvProj

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.CrLift
section
noncomputable section

open Finset Polynomial

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem cr_lift [CharZero K] (E : GLOps n K V) (hT : (⨆ ν, weightSp E ν) = ⊤) (W Z : Submodule K V)
    (hW : IsStableUnderOperators E W) (hZ : IsStableUnderOperators E Z) (mu : Fin n → ℤ) (x0 : V) (hx0 : x0 ∈ W)
    (hq : Z.mkQ x0 ∈ weightSp (cr_quot E Z hZ) mu) :
    ∃ x ∈ W, x ∈ weightSp E mu ∧ Z.mkQ x = Z.mkQ x0 := by
  classical
  have hg := v2rep_graded E W (fun a x hx => hW a a x hx) x0 hx0 (by rw [hT]; trivial)
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hg
  have hm : ∑ ν ∈ f.support, Z.mkQ (f ν) = Z.mkQ x0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hsum, Finsupp.sum, map_sum]
  have hc := v2rep_comp_mem (cr_quot E Z hZ) (weightSp (cr_quot E Z hZ) mu)
    (fun a x hx => cr_wt_diag_stable _ mu a x hx) f.support (fun ν => Z.mkQ (f ν))
    (fun ν _ => cr_quot_wt E Z hZ ν _ (hf ν).1) (by rw [hm]; exact hq)
  refine ⟨f mu, (hf mu).2, (hf mu).1, ?_⟩
  rw [← hm]
  symm
  refine Finset.sum_eq_single mu (fun ν hν hne => ?_) (fun hn => ?_)
  · exact cr_wt_disj _ hne (cr_quot_wt E Z hZ ν _ (hf ν).1) (hc ν hν)
  · rw [Finsupp.notMem_support_iff.1 hn, map_zero]

theorem cr_CR [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (hR : SatisfiesGLRelations E)
    (hT : (⨆ ν, weightSp E ν) = ⊤) (W : Submodule K V) (hW : IsStableUnderOperators E W) :
    W ≤ ⨆ mu, isotypicPartIn E W mu := by
  classical
  set W2 : Submodule K V := ⨆ mu, isotypicPartIn E W mu with hW2
  have hW2st : IsStableUnderOperators E W2 := v2rep_iSup_stable E _ fun mu => v2rep_isoIn_stable E W mu
  by_contra hnot
  have hZne : W.map W2.mkQ ≠ ⊥ := by
    intro h
    apply hnot
    have := (LinearMap.le_ker_iff_map (f := W2.mkQ) (p := W)).2 h
    rwa [Submodule.ker_mkQ] at this
  have hZst : IsStableUnderOperators (cr_quot E W2 hW2st) (W.map W2.mkQ) := by
    rintro a b y ⟨x, hx, rfl⟩
    exact ⟨E a b x, hW a b x hx, rfl⟩
  have hRq := cr_quot_rel E hR W2 hW2st
  obtain ⟨mu, xb, hxbZ, hxb⟩ := v2rep_exists_hwv (cr_quot E W2 hW2st) hRq (W.map W2.mkQ) hZst
    (le_top.trans (cr_quot_top E W2 hW2st hT)) hZne
  obtain ⟨x0, hx0W, rfl⟩ := hxbZ
  obtain ⟨x, hxW, hxwt, hxq⟩ := cr_lift E hT W W2 hW hW2st mu x0 hx0W hxb.2.1
  rw [← hxq] at hxb
  have hdom : Dominant mu := cr_hwv_dom _ hRq hxb
  have hxn : x ∉ W2 := fun h => hxb.1 ((Submodule.Quotient.mk_eq_zero W2).2 h)
  have hup : ∀ a b : Fin n, a < b → E a b x ∈ W2 := by
    intro a b hab
    have := hxb.2.2 a b hab
    rw [cr_quot_mk] at this
    exact (Submodule.Quotient.mk_eq_zero W2).1 this
  set T := cr_C E with hTdef
  have hTW2 : ∀ z ∈ W2, T z ∈ W2 := cr_C_stable E W2 hW2st
  have hy : T x - ((cr_c mu : ℤ) : K) • x ∈ W2 := by
    rw [hTdef, cr_C_wt E hR mu x hxwt, add_sub_cancel_left]
    refine W2.smul_mem _ (Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_)
    split_ifs with h
    · exact hW2st b a _ (hup a b h)
    · exact zero_mem _
  obtain ⟨q, hq1, hq2⟩ := casimir_polynomial_isolates_level E hR (fun _ => W) _ hy (cr_c mu)
  set x' := aeval T q x with hx'
  have h1 : x' - x ∈ W2 := by
    have := cr_aeval_mod T W2 hTW2 _ x hy q
    rwa [hq1, one_smul] at this
  have h2 : x' ∈ W := cr_aeval_stable T W (cr_C_stable E W hW) x hxW q
  have h3 : x' ∈ weightSp E mu := cr_aeval_stable T _ (cr_C_weightSp E hR mu) x hxwt q
  have h4 : x' ∉ W2 := by
    intro h
    apply hxn
    have : x = x' - (x' - x) := by abel
    rw [this]; exact W2.sub_mem h h1

  have hy0 : T x' - ((cr_c mu : ℤ) : K) • x' = aeval T q (T x - ((cr_c mu : ℤ) : K) • x) := by
    rw [map_sub, map_smul, cr_aeval_comm T T rfl q x]
  have hy0e : T (T x' - ((cr_c mu : ℤ) : K) • x') = ((cr_c mu : ℤ) : K) • (T x' - ((cr_c mu : ℤ) : K) • x') := by
    rw [hy0]
    exact casimir_acts_scalar_on_level E hR (fun _ => W) (cr_c mu) _ hq2
  have hzero : ∀ a b : Fin n, a < b → E a b x' = 0 := by
    intro a b hab
    set z := E a b x' with hz
    have hzW2 : z ∈ W2 := by
      have : z = E a b x + E a b (x' - x) := by rw [hz, ← map_add (f := _)]; congr 1; abel
      rw [this]; exact W2.add_mem (hup a b hab) (hW2st a b _ h1)
    have hzwt : z ∈ weightSp E (mu + rootW a b) := v2rep_shift E hR a b mu x' h3
    set w1 := T z - ((cr_c mu : ℤ) : K) • z with hw1
    have hw1' : w1 = E a b (T x' - ((cr_c mu : ℤ) : K) • x') := by
      rw [hw1, hz, map_sub, map_smul, hTdef, cr_C_comm_apply E hR]
    have hw1e : T w1 = ((cr_c mu : ℤ) : K) • w1 := by
      rw [hw1', hTdef, cr_C_comm_apply E hR, ← hTdef, hy0e, map_smul]
    obtain ⟨r, hr1, hr2⟩ := casimir_polynomial_isolates_level E hR (fun _ => W) z hzW2 (cr_c mu)
    have hz0 : aeval T r z = 0 := by
      refine casimir_isotypic_no_higher_weight E hR (fun _ => W) mu hdom (mu + rootW a b) ?_ ?_ _ hr2
        (cr_aeval_stable T _ (cr_C_weightSp E hR _) z hzwt r)
      · rw [add_sub_cancel_left]; exact cr_root_mem a b hab
      · rw [add_sub_cancel_left]; exact cr_ht_root a b hab
    have hspan : aeval T r z - r.eval (((cr_c mu : ℤ) : K)) • z ∈ Submodule.span K {w1} := by
      refine cr_aeval_mod T (Submodule.span K {w1}) ?_ _ z (Submodule.mem_span_singleton_self w1) r
      intro y hy
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [map_smul, hw1e, smul_comm]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w1))
    rw [hz0, hr1, one_smul, zero_sub] at hspan
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hspan
    have hzt : z = (-t) • w1 := by rw [neg_smul, ht, neg_neg]
    have hw0 : w1 = 0 := by
      have : T z = ((cr_c mu : ℤ) : K) • z := by rw [hzt, map_smul, hw1e, smul_comm]
      rw [hw1, this, sub_self]
    rw [hzt, hw0, smul_zero]
  apply h4
  have hne : x' ≠ 0 := fun h => h4 (by rw [h]; exact zero_mem _)
  exact Submodule.mem_iSup_of_mem mu (Submodule.subset_span ⟨1, one_mem _, x', h2, ⟨hne, h3, hzero⟩, rfl⟩)

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.EquivariantKillsCyclicOfZero
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section
variable {n : ℕ} {K V V' : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

def weightHeightRootWeights (nu : Fin n → ℤ) : ℤ := ∑ c : Fin n, ((c : ℕ) : ℤ) * nu c

theorem weight_height_root_weights_add_root (nu : Fin n → ℤ) (a b : Fin n) :
    weightHeightRootWeights (nu + rootW a b) = weightHeightRootWeights nu + (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) := by
  unfold weightHeightRootWeights rootW
  simp only [Pi.add_apply, Pi.sub_apply, mul_add, Finset.sum_add_distrib, mul_sub, Finset.sum_sub_distrib]
  simp [Pi.single_apply]

theorem lowering_monomial_raises_height {E : GLOps n K V} (hs : OperatorsShiftWeightsByRoots E) {mu : Fin n → ℤ} {v : V}
    (hv : v ∈ weightSp E mu) {u : Module.End K V} (hu : u ∈ loweringWordMonoid E) :
    ∃ nu, u v ∈ weightSp E nu ∧ ((u v = v ∧ nu = mu) ∨ weightHeightRootWeights mu < weightHeightRootWeights nu) := by
  induction hu using Submonoid.closure_induction generalizing mu v with
  | mem x hx =>
    obtain ⟨a, b, hba, rfl⟩ := hx
    refine ⟨mu + rootW a b, hs a b mu v hv, Or.inr ?_⟩
    rw [weight_height_root_weights_add_root]
    have : (b : ℕ) < (a : ℕ) := hba
    omega
  | one => exact ⟨mu, by simpa using hv, Or.inl ⟨by simp, rfl⟩⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨nu2, h2, hc2⟩ := ihy hv
    obtain ⟨nu1, h1, hc1⟩ := ihx h2
    refine ⟨nu1, by simpa [Module.End.mul_apply] using h1, ?_⟩
    rcases hc2 with ⟨e2, rfl⟩ | lt2
    · rcases hc1 with ⟨e1, rfl⟩ | lt1
      · left; exact ⟨by rw [Module.End.mul_apply, e1, e2], rfl⟩
      · right; exact lt1
    · right
      rcases hc1 with ⟨_, rfl⟩ | lt1
      · exact lt2
      · exact lt2.trans lt1

theorem self_mem_cyclicSubmodule (E : GLOps n K V) (v : V) : v ∈ cyclicSubmodule E v := Submodule.subset_span ⟨1, (Umon E).one_mem, by simp⟩

theorem cyclic_highest_weightSpace_line [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) (mu : Fin n → ℤ) (v : V)
    (hv : IsHWV E mu v) (x : V) (hx : x ∈ cyclicSubmodule E v) (hxw : x ∈ weightSp E mu) : ∃ c : K, x = c • v := by
  classical
  have hs : OperatorsShiftWeightsByRoots E := gl_rep_shifts_weights hE

  set Hh : Module.End K V := ∑ c : Fin n, (((c : ℕ) : ℤ) : K) • E c c with hHh
  have hH : ∀ nu (w : V), w ∈ weightSp E nu → Hh w = ((weightHeightRootWeights nu : ℤ) : K) • w := by
    intro nu w hw
    rw [mem_weightSpace_iff_diag_eigen] at hw
    rw [hHh, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, hw, smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    simp [weightHeightRootWeights]

  have hvY : v ∈ loweringWordSpan E v := Submodule.subset_span ⟨1, (loweringWordMonoid E).one_mem, by simp⟩
  have hcY : cyclicSubmodule E v ≤ loweringWordSpan E v := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨u, hu, rfl⟩
    exact lowering_word_span_enveloping_stable hE hv hu v hvY
  set S : Submodule K V := Submodule.span K
    {y | ∃ nu, y ∈ weightSp E nu ∧ weightHeightRootWeights mu < weightHeightRootWeights nu} with hS
  have hYS : loweringWordSpan E v ≤ K ∙ v ⊔ S := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨u, hu, rfl⟩
    obtain ⟨nu, hnu, hc⟩ := lowering_monomial_raises_height hs hv.2.1 hu
    rcases hc with ⟨he, -⟩ | hlt
    · rw [he]; exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨nu, hnu, hlt⟩)
  obtain ⟨y, hy, s, hsS, hys⟩ := Submodule.mem_sup.1 (hYS (hcY hx))
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  refine ⟨c, ?_⟩
  have hsx : s = x - c • v := by rw [← hys]; abel
  have hs1 : s ∈ Hh.eigenspace ((weightHeightRootWeights mu : ℤ) : K) := by
    rw [Module.End.mem_eigenspace_iff, hsx, map_sub, map_smul, hH mu x hxw, hH mu v hv.2.1, smul_sub,
      smul_comm]
  have hs2 : s ∈ ⨆ (l : K) (_ : l ≠ ((weightHeightRootWeights mu : ℤ) : K)), Hh.eigenspace l := by
    refine (Submodule.span_le.2 ?_) hsS
    rintro w ⟨nu, hnu, hlt⟩
    have hne : ((weightHeightRootWeights nu : ℤ) : K) ≠ ((weightHeightRootWeights mu : ℤ) : K) := by
      exact_mod_cast hlt.ne'
    refine Submodule.mem_iSup_of_mem ((weightHeightRootWeights nu : ℤ) : K) (Submodule.mem_iSup_of_mem hne ?_)
    rw [Module.End.mem_eigenspace_iff]
    exact hH nu w hnu
  have h0 : s = 0 :=
    (Submodule.disjoint_def.1 (Module.End.eigenspaces_iSupIndep Hh ((weightHeightRootWeights mu : ℤ) : K))) s hs1 hs2
  rw [← hys, h0, add_zero]

theorem equivariant_kills_cyclic_of_zero (E : GLOps n K V) (E' : GLOps n K V') (T : V →ₗ[K] V') (hT : IsEquivariantMap E E' T) (v : V)
    (h0 : T v = 0) : ∀ x ∈ cyclicSubmodule E v, T x = 0 := by
  intro x hx
  have hle : cyclicSubmodule E v ≤ LinearMap.ker T := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨u, hu, rfl⟩
    obtain ⟨u', -, hu'⟩ := equivariant_intertwines_monoid E E' T hT hu
    show T (u v) = 0
    rw [hu' v, h0, map_zero]
  exact hle hx

theorem envelopingMonoid_restrict (E : GLOps n K V) (L : Submodule K V) (hL : IsSubrepresentation E L) {u : Module.End K V} (hu : u ∈ Umon E) :
    ∃ uL ∈ Umon (restrictRepresentation E L hL), ∀ y : L, ((uL y : L) : V) = u (y : V) := by
  induction hu using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    exact ⟨restrictRepresentation E L hL a b, Submonoid.subset_closure ⟨(a, b), rfl⟩, fun y => rfl⟩
  | one => exact ⟨1, (Umon _).one_mem, fun y => rfl⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨ux, hux, hx⟩ := ihx
    obtain ⟨uy, huy, hy⟩ := ihy
    refine ⟨ux * uy, (Umon _).mul_mem hux huy, fun z => ?_⟩
    simp only [Module.End.mul_apply, hx, hy]

theorem cyclicSubmodule_restrict_eq_top (E : GLOps n K V) (v : V) (hL : IsSubrepresentation E (cyclicSubmodule E v)) :
    cyclicSubmodule (restrictRepresentation E _ hL) (⟨v, self_mem_cyclicSubmodule E v⟩ : cyclicSubmodule E v) = ⊤ := by
  refine eq_top_iff.2 ?_
  rintro ⟨x, hx⟩ -
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, rfl⟩ := hy
    obtain ⟨uL, huL, hL'⟩ := envelopingMonoid_restrict E _ hL hu
    have heq : (⟨u v, Submodule.subset_span ⟨u, hu, rfl⟩⟩ : cyclicSubmodule E v) = uL ⟨v, self_mem_cyclicSubmodule E v⟩ :=
      Subtype.ext (hL' ⟨v, self_mem_cyclicSubmodule E v⟩).symm
    rw [heq]
    exact Submodule.subset_span ⟨uL, huL, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add y z hy hz ihy ihz =>
    have := Submodule.add_mem _ ihy ihz
    exact this
  | smul c y hy ihy =>
    have := Submodule.smul_mem _ c ihy
    exact this

theorem highest_vector_restrict (E : GLOps n K V) (L : Submodule K V) (hL : IsSubrepresentation E L) (mu : Fin n → ℤ) (v : V) (hvL : v ∈ L)
    (hv : IsHWV E mu v) : IsHWV (restrictRepresentation E L hL) mu ⟨v, hvL⟩ := by
  obtain ⟨h0, hw, hl⟩ := hv
  refine ⟨fun h => h0 (congrArg Subtype.val h), ?_, fun a b hab => Subtype.ext (hl a b hab)⟩
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker] at hw ⊢
  intro a
  apply Subtype.ext
  have := hw a
  simpa using this

end

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightEntriesBetweenExtremeHighest
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem rootWeight_apply_first {n : ℕ} {a c : Fin n} (h : a ≠ c) : rootW a c a = 1 := by
  simp [rootW, Pi.single_apply, h]

theorem rootWeight_apply_second {n : ℕ} {a c : Fin n} (h : a ≠ c) : rootW a c c = -1 := by
  simp [rootW, Pi.single_apply, h.symm]

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem integral_operator_pow_shifts_weight {E : GLOps n (KK O) V} (hE : IsGLRep E) {nu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E nu)
    (a c : Fin n) (j : ℕ) : ((E a c) ^ j) x ∈ weightSp E (nu + (j : ℤ) • rootW a c) := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := gl_rep_operator_weight_shift hE ih a c
    have e : nu + ((j + 1 : ℕ) : ℤ) • rootW a c = nu + (j : ℤ) • rootW a c + rootW a c := by
      push_cast; rw [add_smul, one_smul, add_assoc]
    rw [e]; exact h

theorem offdiag_operator_nilpotent_on_weight [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V} (hE : IsGLRep E)
    {nu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E nu) {a c : Fin n} (hac : a ≠ c) :
    ∃ j : ℕ, ((E a c) ^ j) x = 0 := by
  obtain ⟨F, hF⟩ := findim_exists_finite_weights E hE.2.2
  by_contra hcon
  push Not at hcon
  have hin : ∀ j : ℕ, nu + (j : ℤ) • rootW a c ∈ F := by
    intro j
    by_contra hj
    exact hcon j (weight_support_sum_eq_zero (O := O) E (fun mu => mu ∈ F) (integral_operator_pow_shifts_weight hE hx a c j) (hF Submodule.mem_top) hj)
  have hinj : Function.Injective (fun j : ℕ => (⟨nu + (j : ℤ) • rootW a c, hin j⟩ : F)) := by
    intro i j hij
    have h1 := congrFun (congrArg Subtype.val hij) a
    simp only [Pi.add_apply, Pi.smul_apply, rootWeight_apply_first hac, smul_eq_mul, mul_one] at h1
    omega
  exact not_injective_infinite_finite _ hinj

theorem offdiag_string_reaches_top_nonzero [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V} (hE : IsGLRep E)
    {nu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E nu) (h0 : x ≠ 0) {a c : Fin n} (hac : a ≠ c) :
    ∃ j : ℕ, ((E a c) ^ j) x ≠ 0 ∧ E a c (((E a c) ^ j) x) = 0 := by
  obtain ⟨j, h1, h2⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists (p := fun j => ((E a c) ^ j) x = 0)
    (by simpa using h0) (offdiag_operator_nilpotent_on_weight hE hx hac)
  refine ⟨j, h1, ?_⟩
  rw [pow_succ', Module.End.mul_apply] at h2
  exact h2

theorem weight_entries_between_extreme_highest [NeZero n] [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V}
    {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) {nu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E nu)
    (h0 : x ≠ 0) (a : Fin n) : lam (lastIdx n) ≤ nu a ∧ nu a ≤ lam 0 := by
  constructor
  · by_cases ha : a = lastIdx n
    · subst ha; exact (irreducible_weight_end_bounds hI hx h0).2
    · have hla : lastIdx n ≠ a := fun e => ha e.symm
      obtain ⟨j, h1, h2⟩ := offdiag_string_reaches_top_nonzero hI.1 hx h0 hla
      have hw := integral_operator_pow_shifts_weight hI.1 hx (lastIdx n) a j
      obtain ⟨m, hm, h3, -⟩ := sl2_string_nonvanishing hI.1.1 hla h1 hw h2
      have hz := (irreducible_weight_end_bounds hI (integral_operator_pow_shifts_weight hI.1 hw a (lastIdx n) m) h3).2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, rootWeight_apply_first hla, rootWeight_apply_second hla, rootWeight_apply_second ha] at hm hz
      omega
  · by_cases ha : a = 0
    · subst ha; exact (irreducible_weight_end_bounds hI hx h0).1
    · obtain ⟨j, h1, h2⟩ := offdiag_string_reaches_top_nonzero hI.1 hx h0 ha
      have hw := integral_operator_pow_shifts_weight hI.1 hx a 0 j
      obtain ⟨m, hm, h3, -⟩ := sl2_string_nonvanishing hI.1.1 ha h1 hw h2
      have h0a : (0 : Fin n) ≠ a := fun e => ha e.symm
      have hz := (irreducible_weight_end_bounds hI (integral_operator_pow_shifts_weight hI.1 hw 0 a m) h3).1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, rootWeight_apply_first ha, rootWeight_apply_second ha, rootWeight_apply_first h0a] at hm hz
      omega

end hw

end Formalism.MainNotions.G.GLWeightTheory
end
end

