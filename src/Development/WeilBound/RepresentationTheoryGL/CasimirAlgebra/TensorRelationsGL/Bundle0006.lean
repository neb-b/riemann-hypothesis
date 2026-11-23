module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PSWStartA
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace SWS

variable {n : ℕ} {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ]

def mono (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) {m : ℕ} (lab : Fin m → ι) (c : ι → ℤ) (I K : Fin m → Fin n) :
    Γ → ℂ :=
  fun k => (∏ τ, (κ τ k).det ^ c τ) * ∏ p, κ (lab p) k (I p) (K p)

def Mono (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (H : Set ι) : Set (Γ → ℂ) :=
  {g | ∃ (m : ℕ) (lab : Fin m → ι) (c : ι → ℤ) (I K : Fin m → Fin n), (∀ p, lab p ∈ H) ∧ g = mono κ lab c I K}

theorem exists_half (bar : ι → ι) (h1 : ∀ τ, bar (bar τ) = τ) (h2 : ∀ τ, bar τ ≠ τ) :
    ∃ H : Set ι, ∀ τ, τ ∈ H ↔ bar τ ∉ H := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨{τ | e τ < e (bar τ)}, fun τ => ?_⟩
  simp only [Set.mem_setOf_eq, h1, not_lt]
  have hne : e τ ≠ e (bar τ) := fun h => h2 τ (e.injective h).symm
  constructor
  · intro h
    exact h.le
  · intro h
    exact lt_of_le_of_ne h hne

variable {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ}

theorem det_ne (hK : IsKD bar κ) (τ : ι) (γ : Γ) : (κ τ γ).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (hK.unit τ γ)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem mono_cont (hK : IsKD bar κ) {m : ℕ} (lab : Fin m → ι) (c : ι → ℤ) (I K : Fin m → Fin n) :
    Continuous (mono κ lab c I K) := by
  have hent : ∀ τ, Continuous fun k => κ τ k :=
    fun τ => continuous_pi fun i => continuous_pi fun j => hK.cont τ i j
  unfold mono
  refine Continuous.mul ?_ ?_
  · refine continuous_finsetProd _ fun τ _ => ?_
    exact ((hent τ).matrix_det).zpow₀ (c τ) fun k => Or.inl (det_ne hK τ k)
  · exact continuous_finsetProd _ fun p _ => hK.cont (lab p) (I p) (K p)

theorem one_mem_Mono (H : Set ι) : (1 : Γ → ℂ) ∈ Mono κ H := by
  refine ⟨0, Fin.elim0, 0, Fin.elim0, Fin.elim0, fun p => p.elim0, ?_⟩
  funext k
  simp [mono]

theorem mul_mem_Mono (hK : IsKD bar κ) (H : Set ι) {g g' : Γ → ℂ} (hg : g ∈ Mono κ H) (hg' : g' ∈ Mono κ H) :
    g * g' ∈ Mono κ H := by
  obtain ⟨m1, l1, c1, I1, K1, hl1, rfl⟩ := hg
  obtain ⟨m2, l2, c2, I2, K2, hl2, rfl⟩ := hg'
  refine ⟨m1 + m2, Fin.append l1 l2, c1 + c2, Fin.append I1 I2, Fin.append K1 K2, ?_, ?_⟩
  · intro p
    refine Fin.addCases (fun i => ?_) (fun i => ?_) p
    · simpa [Fin.append_left] using hl1 i
    · simpa [Fin.append_right] using hl2 i
  · funext k
    simp only [mono, Pi.mul_apply, Fin.prod_univ_add, Fin.append_left, Fin.append_right, Pi.add_apply]
    rw [show (∏ τ, (κ τ k).det ^ (c1 τ + c2 τ)) =
        (∏ τ, (κ τ k).det ^ c1 τ) * ∏ τ, (κ τ k).det ^ c2 τ by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun τ _ => zpow_add₀ (det_ne hK τ k) _ _]
    ring

def monoAlg (hK : IsKD bar κ) (H : Set ι) : Subalgebra ℂ (Γ → ℂ) :=
  (Submodule.span ℂ (Mono κ H)).toSubalgebra (Submodule.subset_span (one_mem_Mono H)) (by
    intro x y hx hy
    have := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at this
    refine Submodule.span_le.2 ?_ this
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact Submodule.subset_span (mul_mem_Mono hK H ha hb))

theorem integrable_of_cont [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ] (μ : MeasureTheory.Measure Γ)
    [MeasureTheory.IsFiniteMeasure μ] {f : Γ → ℂ} (hf : Continuous f) : MeasureTheory.Integrable f μ := by
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem entry_mem (hK : IsKD bar κ) {H : Set ι} (hH : ∀ τ, τ ∈ H ↔ bar τ ∉ H) (τ : ι) (i j : Fin n) :
    (fun k => κ τ k i j) ∈ Submodule.span ℂ (Mono κ H) := by
  classical
  change (fun k => κ τ k i j) ∈ monoAlg hK H
  have hent : ∀ σ ∈ H, ∀ a b : Fin n, (fun k => κ σ k a b) ∈ monoAlg hK H := by
    intro σ hσ a b
    apply Submodule.subset_span
    refine ⟨1, fun _ => σ, 0, fun _ => a, fun _ => b, fun _ => hσ, ?_⟩
    funext k
    simp [mono]
  by_cases hτ : τ ∈ H
  · exact hent τ hτ i j
  · have hσ : bar τ ∈ H := by
      by_contra h
      exact hτ ((hH τ).2 h)
    have hinv : ∀ z : ℤ, (fun k => (κ (bar τ) k).det ^ z) ∈ monoAlg hK H := by
      intro z
      apply Submodule.subset_span
      refine ⟨0, Fin.elim0, Pi.single (bar τ) z, Fin.elim0, Fin.elim0, fun p => p.elim0, ?_⟩
      funext k
      symm
      simp only [mono, Fin.prod_univ_zero, mul_one]
      rw [Finset.prod_eq_single (bar τ)]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hadj : (fun k => (κ (bar τ) k).adjugate j i) ∈ monoAlg hK H := by
      have hfun : (fun k => (κ (bar τ) k).adjugate j i) = ∑ p : Equiv.Perm (Fin n),
          (Equiv.Perm.sign p : ℤ) • ∏ r, (fun k => ((κ (bar τ) k).updateRow i (Pi.single j 1)) (p r) r) := by
        funext k
        simp [Matrix.adjugate_apply, Matrix.det_apply, Finset.sum_apply, Finset.prod_apply, Units.smul_def]
      rw [hfun]
      refine Subalgebra.sum_mem _ fun p _ => zsmul_mem (Subalgebra.prod_mem _ fun r _ => ?_) _
      by_cases h : p r = i
      · simp only [h, Matrix.updateRow_self]
        exact Subalgebra.algebraMap_mem (monoAlg hK H) ((Pi.single j (1 : ℂ) : Fin n → ℂ) r)
      · simp only [Matrix.updateRow_ne h]
        exact hent _ hσ _ _
    have hkey : (fun k => κ τ k i j) =
        (fun k => (κ (bar τ) k).det ^ (-1 : ℤ)) * (fun k => (κ (bar τ) k).adjugate j i) := by
      funext k
      have hinvM : (κ (bar τ) k)⁻¹ = (κ (bar τ) k)ᴴ := Matrix.inv_eq_right_inv (hK.unit (bar τ) k)
      have e1 : κ τ k i j = star (κ (bar τ) k i j) := by
        have := hK.conj (bar τ) k i j
        rwa [hK.invol] at this
      have e2 : star (κ (bar τ) k i j) = ((κ (bar τ) k)ᴴ) j i := by
        simp [Matrix.conjTranspose_apply]
      rw [Pi.mul_apply, e1, e2, ← hinvM]
      simp [Matrix.inv_def, Ring.inverse_eq_inv', _root_.zpow_neg_one]
    rw [hkey]
    exact Subalgebra.mul_mem _ (hinv (-1)) hadj

end SWS

end PositivityTheory.Rg.Cz

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PStepFormulaA
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace PStepFormula

theorem qdet_map {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (E : Fin n → Fin n → A) (u : ℂ) : f (qdet E u) = qdet (fun a b => f (E a b)) u := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [qdet, qminor, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn, Function.comp_def, Tm,
    map_add, apply_ite f, AlgHom.commutes, map_zero]

theorem glRel_map {A B : Type*} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    {E : Fin n → Fin n → A} (h : GlRel E) : GlRel (fun a b => f (E a b)) := by
  intro a b c d
  have := congrArg f (h a b c d)
  simpa only [map_sub, map_mul, apply_ite f, map_zero] using this

section
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem conj_eq (e : V ≃ₗ[ℂ] W) {T : Module.End ℂ V} {T' : Module.End ℂ W}
    (h : ∀ x, e (T x) = T' (e x)) : e.conjAlgEquiv ℂ T = T' := by
  ext x
  simp [LinearEquiv.conjAlgEquiv_apply, h]
end

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem liftA_apply {P : Type} (B : Module.End ℂ M) : liftA n M P B = lift B := rfl

theorem lift_PiJ {m : ℕ} {P : Type} (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) :
    (lift (PiJ m E u) : Module.End ℂ (TV n (TV n M (Fin m)) P)) =
      (List.ofFn fun i => algebraMap ℂ _ u + lift (xJ E i)).prod := by
  rw [← liftA_apply]
  simp only [PiJ, map_list_prod, List.map_ofFn, Function.comp_def, map_add (f := _), AlgHom.commutes, liftA_apply]

theorem PiJ_one (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) :
    (PiJ 1 E u : Module.End ℂ (TV n M (Fin 1))) = algebraMap ℂ _ u + Om E 0 := by
  have : (Finset.univ.filter fun i : Fin 1 => i < 0) = ∅ := by
    ext i; simp
  simp [PiJ, xJ]

theorem app_upd_r {α : Type} {m k : ℕ} (I : Fin m → α) (J : Fin k → α) (j : Fin k) (a : α) :
    Function.update (Fin.append I J) (Fin.natAdd m j) a = Fin.append I (Function.update J j a) := by
  funext x
  refine Fin.addCases (fun i => ?_) (fun i => ?_) x
  · rw [Fin.append_left, Function.update_of_ne, Fin.append_left]
    intro h; have := congrArg Fin.val h; simp at this; omega
  · by_cases h : i = j
    · subst h; simp
    · rw [Function.update_of_ne, Fin.append_right, Fin.append_right, Function.update_of_ne h]
      intro h'; exact h (Fin.ext (by have := congrArg Fin.val h'; simp at this; omega))

theorem app_upd_l {α : Type} {m k : ℕ} (I : Fin m → α) (J : Fin k → α) (i : Fin m) (a : α) :
    Function.update (Fin.append I J) (Fin.castAdd k i) a = Fin.append (Function.update I i a) J := by
  funext x
  refine Fin.addCases (fun i' => ?_) (fun j => ?_) x
  · by_cases h : i' = i
    · subst h; simp
    · rw [Function.update_of_ne, Fin.append_left, Fin.append_left, Function.update_of_ne h]
      intro h'; exact h (Fin.ext (by have := congrArg Fin.val h'; simp at this; omega))
  · rw [Fin.append_right, Function.update_of_ne, Fin.append_right]
    intro h; have := congrArg Fin.val h; simp at this; omega

theorem curF_Om_r {m k : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (j : Fin k) (f : TV n M (Fin (m + k))) :
    curF n M m k (Om E (Fin.natAdd m j) f) = Om (fun a b => lift (E a b)) j (curF n M m k f) := by
  funext J I
  simp only [curF_apply, Om_apply, Fin.append_right, app_upd_r]
  rw [Finset.sum_apply]
  simp [curF_apply]

theorem curF_Om_l {m k : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (i : Fin m) (f : TV n M (Fin (m + k))) :
    curF n M m k (Om E (Fin.castAdd k i) f) = lift (Om E i) (curF n M m k f) := by
  funext J I
  simp only [curF_apply, Om_apply, Fin.append_left, app_upd_l, lift_apply]

theorem eq_zero_of_eq_neg' {X : Type} [AddCommGroup X] [Module ℂ X] {x : X} (h : x = -x) : x = 0 := by
  have h2 : (2 : ℂ) • x = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    exact add_neg_cancel x
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

theorem alt_swap {X : Type} [AddCommGroup X] [Module ℂ X] (g : TV n X (Fin n)) (J : Fin n → Fin n) (a b : Fin n)
    (h : a ≠ b) : alt Finset.univ g (J ∘ Equiv.swap a b) = -alt Finset.univ g J := by
  rw [alt_apply, alt_apply, ← Finset.sum_neg_distrib]
  refine Fintype.sum_equiv (Equiv.mulLeft (Equiv.swap a b)) _ _ fun σ => ?_
  have h1 : J ∘ ⇑(Equiv.swap a b * σ) = (J ∘ Equiv.swap a b) ∘ σ := by
    funext x; simp
  simp only [Equiv.coe_mulLeft, h1, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap h]
  push_cast
  rw [neg_one_mul, neg_smul, neg_neg]

theorem sum_swap {X : Type} [AddCommGroup X] [Module ℂ X] (h : (Fin n → Fin n) → (Fin 1 → Fin n) → X)
    (hanti : ∀ J a b, a ≠ b → h (J ∘ Equiv.swap a b) = -h J) (J : Fin n → Fin n) (I : Fin 1 → Fin n) :
    ∑ j, h (Function.update J j (I 0)) (Function.update I 0 (J j)) = h J I := by
  classical
  have hz : ∀ K : Fin n → Fin n, ∀ a b, a ≠ b → K a = K b → h K = 0 := by
    intro K a b hab hK
    have hc : K ∘ Equiv.swap a b = K := by
      funext x
      simp only [Function.comp_apply, Equiv.swap_apply_def]
      split_ifs with h1 h2
      · rw [h1, hK]
      · rw [h2, hK]
      · rfl
    have := hanti K a b hab
    rw [hc] at this
    funext I
    exact eq_zero_of_eq_neg' (congrFun this I)
  by_cases hJ : Function.Injective J
  · obtain ⟨p, hp⟩ := (Finite.injective_iff_surjective.mp hJ) (I 0)
    rw [Finset.sum_eq_single p]
    · rw [← hp, Function.update_eq_self, hp, Function.update_eq_self]
    · intro j _ hj
      rw [hz (Function.update J j (I 0)) j p hj (by simp [Function.update_of_ne (Ne.symm hj), hp]), Pi.zero_apply]
    · simp
  · obtain ⟨a, b, hab, hne⟩ : ∃ a b, J a = J b ∧ a ≠ b := by
      simp only [Function.Injective, not_forall] at hJ
      obtain ⟨a, b, h1, h2⟩ := hJ
      exact ⟨a, b, h1, h2⟩
    rw [hz J a b hne hab, Pi.zero_apply, Fintype.sum_eq_add a b hne]
    · have hc : Function.update J b (I 0) = Function.update J a (I 0) ∘ Equiv.swap a b := by
        funext x
        simp only [Function.comp_apply, Equiv.swap_apply_def]
        by_cases h1 : x = a
        · subst h1
          rw [if_pos rfl, Function.update_of_ne hne, Function.update_of_ne (Ne.symm hne), hab]
        · rw [if_neg h1]
          by_cases h2 : x = b
          · subst h2
            rw [if_pos rfl, Function.update_self, Function.update_self]
          · rw [if_neg h2, Function.update_of_ne h2, Function.update_of_ne h1]
      rw [hc, hanti _ a b hne, hab]
      simp
    · rintro c ⟨hca, hcb⟩
      rw [hz _ a b hne (by simp [Function.update_of_ne (Ne.symm hca), Function.update_of_ne (Ne.symm hcb), hab]),
        Pi.zero_apply]

def rot (n : ℕ) : Equiv.Perm (Fin (1 + n)) where
  toFun k := if h : (k : ℕ) < n then ⟨k + 1, by omega⟩ else ⟨0, by omega⟩
  invFun k := if h : (k : ℕ) = 0 then ⟨n, by omega⟩ else ⟨k - 1, by omega⟩
  left_inv k := by
    apply Fin.ext; by_cases h : (k : ℕ) < n <;> simp [h] <;> omega
  right_inv k := by
    apply Fin.ext
    by_cases h : (k : ℕ) = 0
    · simp [h]
    · have h' : (k : ℕ) - 1 < n := by omega
      simp [h, h']; omega

theorem rot_nat (i : Fin n) (h : (i : ℕ) < 1 + n) : rot n ⟨i, h⟩ = Fin.natAdd 1 i := by
  apply Fin.ext; simp [rot, i.2]; omega

theorem rot_last (k : Fin (1 + n)) (h : (k : ℕ) = n) : rot n k = Fin.castAdd n 0 := by
  apply Fin.ext; simp [rot, h]

theorem sum_lt_cast {X : Type} [AddCommMonoid X] (k : Fin (1 + n)) (hk : (k : ℕ) ≤ n) (f : Fin (1 + n) → X) :
    ∑ i ∈ Finset.univ.filter (· < k), f i =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), f ⟨i, by omega⟩ := by
  refine Finset.sum_bij' (fun a ha => ⟨a, ?_⟩) (fun b _ => ⟨b, by omega⟩) ?_ ?_ ?_ ?_ ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at ha; omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact hb
  · intro a ha; rfl
  · intro b hb; rfl
  · intro a ha; rfl

theorem app_swap (I : Fin 1 → Fin n) (J : Fin n → Fin n) (j : Fin n) :
    Fin.append I J ∘ Equiv.swap (Fin.natAdd 1 j) (Fin.castAdd n 0) =
      Fin.append (Function.update I 0 (J j)) (Function.update J j (I 0)) := by
  funext x
  refine Fin.addCases (fun i => ?_) (fun i => ?_) x
  · have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp [Equiv.swap_apply_right, Fin.append_left, Fin.append_right]
  · by_cases h : i = j
    · subst h; simp [Fin.append_left, Fin.append_right]
    · have h1 : Fin.natAdd 1 i ≠ Fin.natAdd 1 j := fun h' => h (Fin.ext (by
        have := congrArg Fin.val h'; simp at this; omega))
      have h2 : Fin.natAdd 1 i ≠ Fin.castAdd n 0 := fun h' => by
        have := congrArg Fin.val h'; simp at this
      rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_right, Fin.append_right,
        Function.update_of_ne h]

theorem conj_xJ {N : ℕ} (hT : TensorGl) (E : Fin n → Fin n → Module.End ℂ M) (hE : GlRel E)
    (σ : Equiv.Perm (Fin N)) (k : Fin N) :
    (pm σ * xJ E k * pm σ⁻¹ : Module.End ℂ (TV n M (Fin N))) =
      Om E (σ k) + ∑ i ∈ Finset.univ.filter (· < k), pm (Equiv.swap (σ i) (σ k)) := by
  have h4 := (hT n M (Fin N) E hE Finset.univ).2.2.2
  have hinv : (pm σ * pm σ⁻¹ : Module.End ℂ (TV n M (Fin N))) = 1 := by rw [← pm_mul, mul_inv_cancel, pm_one]
  rw [xJ, mul_add, add_mul, h4, mul_assoc, hinv, mul_one, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← pm_mul, ← pm_mul, Equiv.swap_apply_apply]

theorem ext_of_alt {W : Type} [AddCommGroup W] [Module ℂ W] {X Y : Module.End ℂ W}
    (h : (lift X : Module.End ℂ (TV n W (Fin n))) * alt Finset.univ = lift Y * alt Finset.univ) : X = Y := by
  classical
  ext w
  let g : TV n W (Fin n) := fun J => if J = id then w else 0
  have hg : alt Finset.univ g id = w := by
    rw [alt_apply, Finset.sum_eq_single 1]
    · simp [g]
    · intro σ _ hσ
      have hs : (id ∘ ⇑σ) ≠ id := fun h' => hσ (Equiv.ext fun x => congrFun h' x)
      simp only [g, if_neg hs, smul_zero]
    · simp
  have := congrArg (fun T : Module.End ℂ (TV n W (Fin n)) => T g id) h
  simpa only [Module.End.mul_apply, lift_apply, hg] using this

end PStepFormula

end PositivityTheory.Rg.Cz

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransAllA
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.TA

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem qdet_map' {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {m : ℕ} (φ : A →ₐ[ℂ] B)
    (E : Fin m → Fin m → A) (u : ℂ) : φ (qdet E u) = qdet (fun a b => φ (E a b)) u := by
  simp [qdet, qminor, Tm, map_list_prod, List.map_ofFn, Function.comp_def, apply_ite φ]

theorem qdet_commute {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (u : ℂ) (Z : A)
    (h : ∀ a b, Commute (E a b) Z) : Commute (qdet E u) Z := by
  unfold qdet qminor
  refine Commute.sum_left _ _ _ fun σ _ => ?_
  refine Commute.mul_left (Int.cast_commute _ _) (Commute.list_prod_left _ _ ?_)
  intro x hx
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
  unfold Tm
  refine Commute.add_left ?_ (h _ _)
  split_ifs
  · exact Algebra.commute_algebraMap_left _ _
  · exact Commute.zero_left _

theorem glRel_map {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {m : ℕ} (φ : A →ₐ[ℂ] B)
    (E : Fin m → Fin m → A) (h : GlRel E) : GlRel fun a b => φ (E a b) := by
  intro a b c d
  dsimp only
  rw [← map_mul, ← map_mul, ← map_sub, h a b c d]
  split_ifs <;> simp

theorem comm_of_mem_adjoin {A : Type*} [Ring A] [Algebra ℂ A] {s : Set A} {X Z : A}
    (hX : X ∈ Algebra.adjoin ℂ s) (h : ∀ T ∈ s, Commute T Z) : Commute X Z := by
  have hs : s ⊆ Subalgebra.centralizer ℂ {Z} := fun T hT => by
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact (h T hT).symm.eq
  have hX' := Algebra.adjoin_le hs hX
  rw [Subalgebra.mem_centralizer_iff] at hX'
  exact (hX' Z rfl).symm

variable {P : Type} [Fintype P] [DecidableEq P]

omit [Fintype P] [DecidableEq P] in
@[simp] theorem liftA_apply (B : Module.End ℂ M) : liftA n M P B = lift B := rfl

omit [Fintype P] [DecidableEq P] in
theorem qdet_lift (F : Fin n → Fin n → Module.End ℂ M) (l : Fin n → ℂ) (h : HasChar F l) :
    HasChar (fun a b => (lift (F a b) : Module.End ℂ (TV n M P))) l := by
  intro u
  have e : (fun a b => (lift (F a b) : Module.End ℂ (TV n M P))) = fun a b => liftA n M P (F a b) := by
    funext a b
    rw [liftA_apply]
  rw [e, ← qdet_map', h u, AlgHom.commutes]

omit [Fintype P] in
theorem tE_empty (F : Fin n → Fin n → Module.End ℂ M) :
    (tE (∅ : Finset P) F : Fin n → Fin n → Module.End ℂ (TV n M P)) = fun a b => lift (F a b) := by
  funext a b
  simp [tE]

omit [Fintype P] in
theorem tE_comm_lift (S : Finset P) (F : Fin n → Fin n → Module.End ℂ M) (B : Module.End ℂ M)
    (h : ∀ c d, Commute (F c d) B) (a b : Fin n) :
    Commute (tE S F a b : Module.End ℂ (TV n M P)) (lift B) := by
  unfold tE
  refine Commute.add_left ?_ (Commute.sum_left _ _ _ fun p _ => ?_)
  · have hc := (h a b).map (liftA n M P)
    simpa only [liftA_apply] using hc
  · unfold Commute SemiconjBy
    refine LinearMap.ext fun x => funext fun I => ?_
    simp only [Module.End.mul_apply, eAt, lift, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval]
    split_ifs <;> simp

theorem cA_lift {C : Type} [DecidableEq C] (col : P → C) (b : P → Fin n) (B : Module.End ℂ M) :
    cA col b ∘ₗ lift B = B ∘ₗ (cA col b : TV n M P →ₗ[ℂ] M) := by
  refine LinearMap.ext fun x => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp [cA, alt, pm, lift, LinearMap.sum_apply, map_sum, map_zsmul]

def cj {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W) :
    Module.End ℂ W →ₐ[ℂ] Module.End ℂ V where
  toFun X := e.symm.toLinearMap ∘ₗ X ∘ₗ e.toLinearMap
  map_one' := LinearMap.ext fun v => by simp
  map_mul' X Y := LinearMap.ext fun v => by simp
  map_zero' := LinearMap.ext fun v => by simp
  map_add' X Y := LinearMap.ext fun v => by simp
  commutes' r := LinearMap.ext fun v => by simp

theorem cj_apply {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    (X : Module.End ℂ W) (v : V) : cj e X v = e.symm (X (e v)) := rfl

end PositivityTheory.Rg.Cz.TA

end
end

