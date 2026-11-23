module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.QdetFacts

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]

omit [Fintype P] [DecidableEq P] in
@[simp] theorem lift_apply (B : Module.End ℂ M) (f : TV n M P) (I : P → Fin n) : lift B f I = B (f I) := rfl

omit [Fintype P] in
theorem eAt_apply (p : P) (a b : Fin n) (f : TV n M P) (I : P → Fin n) :
    eAt p a b f I = if I p = a then f (Function.update I p b) else 0 := by
  simp only [eAt, LinearMap.pi_apply]
  split_ifs <;> simp

omit [Fintype P] [DecidableEq P] in
@[simp] theorem pm_apply (σ : Equiv.Perm P) (f : TV n M P) (I : P → Fin n) : pm σ f I = f (I ∘ σ) := rfl

omit [Fintype P] in
theorem tE_apply (S : Finset P) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : TV n M P) (I : P → Fin n) :
    tE S E a b f I = E a b (f I) + ∑ p ∈ S, if I p = a then f (Function.update I p b) else 0 := by
  simp only [tE, LinearMap.add_apply, Pi.add_apply, lift_apply, LinearMap.sum_apply, Finset.sum_apply, eAt_apply]

omit [Fintype P] in
theorem Om_apply (E : Fin n → Fin n → Module.End ℂ M) (p : P) (f : TV n M P) (I : P → Fin n) :
    Om E p f I = ∑ a, E a (I p) (f (Function.update I p a)) := by
  simp only [Om, LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, lift_apply, eAt_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (I p)]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb), map_zero]
  · simp

omit [Fintype P] [DecidableEq P] in
theorem pm_mul (σ τ : Equiv.Perm P) : (pm (σ * τ) : Module.End ℂ (TV n M P)) = pm σ * pm τ := rfl

omit [Fintype P] [DecidableEq P] in
@[simp] theorem pm_one : (pm 1 : Module.End ℂ (TV n M P)) = 1 := rfl

omit [Fintype P] [DecidableEq P] in
theorem lift_mul (B B' : Module.End ℂ M) : (lift (B * B') : Module.End ℂ (TV n M P)) = lift B * lift B' := rfl

omit [Fintype P] [DecidableEq P] in
theorem lift_comm_pm (B : Module.End ℂ M) (σ : Equiv.Perm P) : Commute (lift B : Module.End ℂ (TV n M P)) (pm σ) := rfl

def liftA (n : ℕ) (M P : Type) [AddCommGroup M] [Module ℂ M] : Module.End ℂ M →ₐ[ℂ] Module.End ℂ (TV n M P) where
  toFun := lift
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

omit [Fintype P] in
theorem lift_comm_eAt (B : Module.End ℂ M) (p : P) (a b : Fin n) : Commute (lift B) (eAt p a b) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Module.End.mul_apply, lift_apply, eAt_apply]
  split_ifs <;> simp

theorem alt_apply (G : Finset (Equiv.Perm P)) (f : TV n M P) (I : P → Fin n) :
    alt G f I = ∑ σ ∈ G, ((Equiv.Perm.sign σ : ℤ) : ℂ) • f (I ∘ σ) := by
  simp only [alt, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, pm_apply]

theorem cA_apply {C : Type} [DecidableEq C] (col : P → C) (b : P → Fin n) (f : TV n M P) :
    cA col b f = alt (colG col) f b := rfl

theorem actT_apply {ι Γ : Type} (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M) (γ : Γ)
    (f : TV n M P) (I : P → Fin n) :
    actT lab κ ρ γ f I = ∑ J : P → Fin n, (∏ p, κ (lab p) γ (I p) (J p)) • ρ γ (f J) := by
  simp only [actT, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]

theorem curF_apply {m k : ℕ} (f : TV n M (Fin (m + k))) (J : Fin k → Fin n) (I : Fin m → Fin n) :
    curF n M m k f J I = f (Fin.append I J) := rfl

end PositivityTheory.Rg.Cz

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PWallQuot
section
noncomputable section

open Formalism.REAL

namespace PositivityTheory.Rg.Cz

namespace WQ

section Alg

variable {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]

theorem qdet_map (f : A →ₐ[ℂ] B) {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) :
    f (qdet E u) = qdet (fun a b => f (E a b)) u := by
  unfold qdet qminor
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 1
  refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
  simp only [Function.comp, Tm, map_add (f := _), apply_ite f, map_zero, AlgHom.commutes]

theorem glRel_map (f : A →ₐ[ℂ] B) {n : ℕ} {E : Fin n → Fin n → A} (h : GlRel E) : GlRel fun a b => f (E a b) := by
  intro a b c d
  have := congrArg f (h a b c d)
  simpa [map_sub, map_mul, apply_ite f] using this

theorem glRel_of_inj (f : A →ₐ[ℂ] B) (hf : Function.Injective f) {n : ℕ} {E : Fin n → Fin n → A}
    (h : GlRel fun a b => f (E a b)) : GlRel E := by
  intro a b c d
  apply hf
  simpa [map_sub, map_mul, apply_ite f] using h a b c d

theorem comm_qdet {n : ℕ} (E : Fin n → Fin n → A) (x : A) (h : ∀ a b, Commute x (E a b)) (u : ℂ) :
    Commute x (qdet E u) := by
  unfold qdet qminor
  refine Commute.sum_right _ _ _ fun σ _ => ?_
  refine Commute.mul_right (Int.cast_commute _ _).symm ?_
  refine Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hy
  unfold Tm
  refine Commute.add_right ?_ (h _ _)
  split_ifs
  · exact Algebra.commute_algebraMap_right _ _
  · exact Commute.zero_right _

end Alg

section Quot

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def stab (N : Submodule ℂ M) : Subalgebra ℂ (Module.End ℂ M) where
  carrier := {X | ∀ y ∈ N, X y ∈ N}
  mul_mem' hX hY y hy := hX _ (hY y hy)
  add_mem' hX hY y hy := N.add_mem (hX y hy) (hY y hy)
  algebraMap_mem' c y hy := by simpa [Module.algebraMap_end_apply] using N.smul_mem c hy

def qmap (N : Submodule ℂ M) : stab N →ₐ[ℂ] Module.End ℂ (M ⧸ N) where
  toFun X := N.mapQ N X.1 (fun y hy => X.2 y hy)
  map_one' := by ext y; simp
  map_mul' X Y := by ext y; simp
  map_zero' := by ext y; simp
  map_add' X Y := by ext y; simp
  commutes' c := by ext y; simp [Module.algebraMap_end_apply]

end Quot

end WQ

open WQ

theorem wallQuot_of (hQ : QdetFacts) : WallQuot := by
  intro n M _ _ ι E hgl hcomm l φ hφ
  let N : Submodule ℂ M :=
    { carrier := {y | ∀ w ∈ envAlg E, φ (w y) = 0}
      add_mem' := fun {x y} hx hy w hw => by
        show φ (w (x + y)) = 0
        rw [map_add (f := _), map_add (f := _), hx w hw, hy w hw, add_zero]
      zero_mem' := fun w _ => by simp
      smul_mem' := fun c y hy w hw => by
        show φ (w (c • y)) = 0
        rw [map_smul, map_smul, hy w hw, smul_zero] }
  have hgen : ∀ τ a b, E τ a b ∈ envAlg E := fun τ a b => Algebra.subset_adjoin ⟨τ, a, b, rfl⟩
  have hstab : ∀ τ a b, E τ a b ∈ stab N := fun τ a b y hy w hw =>
    hy (w * E τ a b) (Subalgebra.mul_mem _ hw (hgen τ a b))
  let E' : ι → Fin n → Fin n → stab N := fun τ a b => ⟨E τ a b, hstab τ a b⟩
  let F : ι → Fin n → Fin n → Module.End ℂ (M ⧸ N) := fun τ a b => qmap N (E' τ a b)
  have hgl' : ∀ τ, GlRel (E' τ) := fun τ => glRel_of_inj (stab N).val Subtype.val_injective (hgl τ)
  have hcent : ∀ τ (u : ℂ), ∀ w ∈ envAlg E, Commute w (qdet (E τ) u) := by
    intro τ u w hw
    induction hw using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨τ', a, b, rfl⟩ := hx
      by_cases h : τ' = τ
      · subst h
        exact ((hQ n M (E τ') (hgl τ')).1 u a b).symm
      · exact comm_qdet _ _ (fun c d => hcomm τ' τ h a b c d) u
    | algebraMap c => exact Algebra.commute_algebraMap_left _ _
    | add x y _ _ hx hy => exact hx.add_left hy
    | mul x y _ _ hx hy => exact hx.mul_left hy
  have hq : ∀ τ (u : ℂ) y, qdet (F τ) u (N.mkQ y) = N.mkQ (qdet (E τ) u y) := by
    intro τ u y
    rw [show qdet (F τ) u = qmap N (qdet (E' τ) u) from (qdet_map _ _ _).symm,
      show qdet (E τ) u = (stab N).val (qdet (E' τ) u) from (qdet_map (stab N).val (E' τ) u).symm]
    rfl
  refine ⟨N, F, fun τ => glRel_map (qmap N) (hgl' τ), fun τ τ' h a b c d => ?_, fun τ u => ?_,
    fun τ a b => LinearMap.ext fun y => rfl, fun y => Iff.rfl⟩
  · exact (show Commute (E' τ a b) (E' τ' c d) from Subtype.ext (hcomm τ τ' h a b c d).eq).map (qmap N)
  · refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hq, Module.algebraMap_end_apply, ← N.mkQ.map_smul,
      Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    intro w hw
    show φ (w (qdet (E τ) u y - (∏ k, (u + l τ k)) • y)) = 0
    have hc := congrArg (fun T : Module.End ℂ M => φ (T y)) (hcent τ u w hw).eq
    simp only [Module.End.mul_apply] at hc
    have h2 := LinearMap.congr_fun (hφ τ u) (w y)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h2
    rw [map_sub, map_sub, map_smul, map_smul, hc, h2, sub_self]

end PositivityTheory.Rg.Cz

end
end

