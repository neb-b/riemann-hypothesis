module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0504
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianModelOfDivisorOfConstants
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0506
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0508

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesOfCharacterTw
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

noncomputable def twistAlg {K Γ : Type} [Field K] [Group Γ] (H : Subgroup Γ) (χ : Γ →* Kˣ) :
    MonoidAlgebra K H →ₐ[K] MonoidAlgebra K H :=
  MonoidAlgebra.lift K (MonoidAlgebra K H) H
    { toFun := fun h => MonoidAlgebra.single h (((χ (h : Γ))⁻¹ : Kˣ) : K)
      map_one' := by simp [MonoidAlgebra.one_def]
      map_mul' := by
        intro a b
        simp [MonoidAlgebra.single_mul_single, mul_comm] }

theorem twistAlg_single {K Γ : Type} [Field K] [Group Γ] (H : Subgroup Γ) (χ : Γ →* Kˣ) (h : H) (c : K) :
    twistAlg H χ (MonoidAlgebra.single h c) = MonoidAlgebra.single h (c * (((χ (h : Γ))⁻¹ : Kˣ) : K)) := by
  simp [twistAlg, MonoidAlgebra.lift_single, MonoidAlgebra.smul_single]

theorem twistAlg_inv_twistAlg {K Γ : Type} [Field K] [Group Γ] (H : Subgroup Γ) (χ : Γ →* Kˣ)
    (x : MonoidAlgebra K H) : twistAlg H χ⁻¹ (twistAlg H χ x) = x := by
  induction x using MonoidAlgebra.induction_on with
  | of m =>
    simp only [MonoidAlgebra.of_apply, twistAlg_single]
    congr 1
    simp
  | add x y hx hy => simp [map_add (f := _), hx, hy]
  | smul r x hx => simp [map_smul, hx]

theorem twistAlg_injective {K Γ : Type} [Field K] [Group Γ] (H : Subgroup Γ) (χ : Γ →* Kˣ) :
    Function.Injective (twistAlg H χ) := fun x y hxy => by
  rw [← twistAlg_inv_twistAlg H χ x, ← twistAlg_inv_twistAlg H χ y, hxy]

theorem embReg_twist : ∀ (K Γ V : Type) [Field K] [Group Γ] [AddCommGroup V] [Module K V] (ρ ρ' : Representation K Γ V)
    (χ : Γ →* Kˣ), (∀ g v, ρ' g v = ((χ g : Kˣ) : K) • ρ g v) → ∀ (H : Subgroup Γ) (n : ℕ), EmbReg ρ H n → EmbReg ρ' H n := by
  intro K Γ V _ _ _ _ ρ ρ' χ hρ H n ⟨j, hj, hjeq⟩
  refine ⟨LinearMap.pi fun i => (twistAlg H χ).toLinearMap.comp ((LinearMap.proj i).comp j), ?_, ?_⟩
  · intro v w hvw
    apply hj
    funext i
    have := congrFun hvw i
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.coe_proj, Function.eval,
      AlgHom.toLinearMap_apply] at this
    exact twistAlg_injective H χ this
  · intro h v i
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.coe_proj, Function.eval,
      AlgHom.toLinearMap_apply]
    rw [hρ, map_smul, Pi.smul_apply, hjeq, map_smul, map_mul, twistAlg_single, ← smul_mul_assoc,
      MonoidAlgebra.smul_single]
    congr 2
    simp

end GlobalTheory.BadCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesOfFreePermute
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem embReg_of_free_permuted_summands : ∀ (K Γ V X : Type) [Field K] [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype X] [DecidableEq X] (ρ : Representation K Γ V) (H : Subgroup Γ) [MulAction H X], (∀ (h : H) (x : X), h • x = x → h = 1) → ∀ (A : X → Submodule K V), DirectSum.IsInternal A → (∀ (h : H) (x : X), ∀ v ∈ A x, ρ h v ∈ A (h • x)) → ∃ n : ℕ, EmbReg ρ H n ∧ n * Nat.card H = finrank K V := by
  intro K Γ V X _ _ _ _ _ _ _ _ ρ H _ hfree A hA hmap
  classical
  haveI : Fintype H := Fintype.ofFinite H
  have hinv : ∀ (g : Γ) (v : V), ρ g⁻¹ (ρ g v) = v := by
    intro g v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  let E := LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hA
  let comp : ∀ x : X, V →ₗ[K] A x := fun x =>
    (DirectSum.component K X (fun y => A y) x) ∘ₗ E.symm.toLinearMap
  have comp_apply : ∀ x v, comp x v = E.symm v x := fun x v => rfl

  have htr : ∀ (h : H) (x : X) (v : V), (comp (h • x) (ρ h v) : V) = ρ h (comp x v) := by
    intro h x v
    obtain ⟨w, rfl⟩ : ∃ w, v = E w := ⟨E.symm v, (E.apply_symm_apply v).symm⟩
    rw [comp_apply, comp_apply, E.symm_apply_apply]
    induction w using DirectSum.induction_on with
    | zero => simp
    | of y a =>
      have hE : E (DirectSum.of (fun y => A y) y a) = (a : V) := DirectSum.coeLinearMap_of A y a
      rw [hE]
      by_cases hxy : y = x
      · subst hxy
        rw [DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem hA (hmap h y a a.2), DirectSum.of_eq_same]
      · have hne : h • y ≠ h • x := fun he => hxy (smul_left_cancel h he)
        rw [DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem_ne hA hne (hmap h y a a.2),
          DirectSum.of_eq_of_ne (β := fun i => A i) y x a (Ne.symm hxy)]
        simp
    | add w₁ w₂ h₁ h₂ =>
      rw [map_add (f := _), map_add (f := _), map_add (f := _), DirectSum.add_apply, Submodule.coe_add, h₁, h₂,
        DirectSum.add_apply, Submodule.coe_add, map_add]
  have hzero : ∀ v : V, (∀ x, comp x v = 0) → v = 0 := by
    intro v hv
    have : E.symm v = 0 := DFinsupp.ext fun x => by rw [← comp_apply, hv]; rfl
    rw [← E.apply_symm_apply v, this, map_zero]

  let d : X → ℕ := fun x => finrank K (A x)
  have hdle : ∀ (h : H) (x : X), d x ≤ d (h • x) := by
    intro h x
    let φ : A x →ₗ[K] A (h • x) :=
      LinearMap.codRestrict (A (h • x)) ((ρ h).comp (A x).subtype) (fun a => hmap h x a a.2)
    refine LinearMap.finrank_le_finrank_of_injective (f := φ) fun a b hab => ?_
    have := congrArg (fun c : A (h • x) => ρ (h : Γ)⁻¹ (c : V)) hab
    have ha : ((φ a : A (h • x)) : V) = ρ h a := rfl
    have hb : ((φ b : A (h • x)) : V) = ρ h b := rfl
    simp only [ha, hb, hinv] at this
    exact Subtype.ext this
  have hdeq : ∀ (h : H) (x : X), d (h • x) = d x := by
    intro h x
    refine le_antisymm ?_ (hdle h x)
    have := hdle h⁻¹ (h • x)
    rwa [inv_smul_smul] at this

  let O := MulAction.orbitRel.Quotient H X
  haveI : Fintype O := Fintype.ofFinite O
  let β : H × O → X := fun p => p.1 • p.2.out
  have hβ : Function.Bijective β := by
    constructor
    · rintro ⟨h, o⟩ ⟨h', o'⟩ he
      simp only [β] at he
      have ho : o = o' := by
        have e1 : (Quotient.mk _ (h • o.out) : O) = o := by
          conv_rhs => rw [← Quotient.out_eq o]
          exact Quotient.sound (MulAction.mem_orbit _ h)
        have e2 : (Quotient.mk _ (h' • o'.out) : O) = o' := by
          conv_rhs => rw [← Quotient.out_eq o']
          exact Quotient.sound (MulAction.mem_orbit _ h')
        rw [← e1, ← e2, he]
      subst ho
      have : (h'⁻¹ * h) • o.out = o.out := by rw [mul_smul, he, inv_smul_smul]
      have := hfree _ _ this
      rw [inv_mul_eq_one] at this
      rw [this]
    · intro x
      let o : O := Quotient.mk _ x
      have hrel : o.out ∈ MulAction.orbit H x := by
        have := Quotient.exact (Quotient.out_eq o)
        exact this
      obtain ⟨g, hg⟩ := hrel
      exact ⟨(g⁻¹, o), by simp only [β, ← hg, inv_smul_smul]⟩

  let n : ℕ := ∑ o : O, d o.out
  have hdimV : finrank K V = ∑ x, d x := by
    rw [Module.finrank_eq_card_basis (hA.collectedBasis fun x => Module.finBasis K (A x)), Fintype.card_sigma]
    simp [d]
  have hcount : n * Nat.card H = finrank K V := by
    rw [hdimV, ← hβ.sum_comp d, Fintype.sum_prod_type_right]
    simp only [β, hdeq, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card, n, Finset.sum_mul]
    exact Finset.sum_congr rfl fun o _ => by ring

  let I := Σ o : O, Fin (d o.out)
  have hcard : Fintype.card I = n := by simp [I, Fintype.card_sigma, n]
  let e : Fin n ≃ I := (Fintype.equivFinOfCardEq hcard).symm
  let b : ∀ o : O, Basis (Fin (d o.out)) K (A o.out) := fun o => Module.finBasis K (A o.out)
  let fo : I → V →ₗ[K] K := fun p => (b p.1).coord p.2 ∘ₗ comp p.1.out
  let T : (V →ₗ[K] K) → V →ₗ[K] MonoidAlgebra K H := fun f =>
    ∑ h : H, (f ∘ₗ ρ (h : Γ)⁻¹).smulRight (MonoidAlgebra.single h (1 : K))
  have hT : ∀ f v, T f v = ∑ h : H, f (ρ (h : Γ)⁻¹ v) • MonoidAlgebra.single h (1 : K) := by
    intro f v; simp [T]
  have hTc : ∀ f v (h : H), (T f v).coeff h = f (ρ (h : Γ)⁻¹ v) := by
    intro f v h
    rw [hT, MonoidAlgebra.coeff_sum]
    simp [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  have hTeq : ∀ f (g : H) v, T f (ρ g v) = MonoidAlgebra.single g 1 * T f v := by
    intro f g v
    rw [hT, hT, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ fun h => ?_
    simp only [Equiv.coe_mulLeft]
    rw [mul_smul_comm, MonoidAlgebra.single_mul_single, one_mul, mul_inv_cancel_left]
    have hc : ρ (h : Γ)⁻¹ (ρ g v) = ρ ((g⁻¹ * h : H) : Γ)⁻¹ v := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp [mul_assoc]
    rw [hc]
  let j : V →ₗ[K] (Fin n → MonoidAlgebra K H) := LinearMap.pi fun k => T (fo (e k))
  refine ⟨n, ⟨j, ?_, ?_⟩, hcount⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply hzero
    intro x
    obtain ⟨⟨h, o⟩, rfl⟩ := hβ.2 x
    have h1 : comp o.out (ρ (h : Γ)⁻¹ v) = 0 := by
      rw [← (b o).forall_coord_eq_zero_iff]
      intro i
      have hk : e (e.symm ⟨o, i⟩) = ⟨o, i⟩ := e.apply_symm_apply _
      have h5 : T (fo (e (e.symm ⟨o, i⟩))) v = 0 := congrFun hv (e.symm ⟨o, i⟩)
      rw [hk] at h5
      have h6 := congrArg (fun a => MonoidAlgebra.coeff a h) h5
      simp only [hTc] at h6
      simpa [fo] using h6
    have h2 := htr h⁻¹ (h • o.out) v
    rw [inv_smul_smul] at h2
    simp only [Subgroup.coe_inv] at h2
    rw [h1, Submodule.coe_zero] at h2
    have h3 := congrArg (ρ (h : Γ)) h2
    have h4 := hinv ((h : Γ)⁻¹) (comp (h • o.out) v : V)
    rw [inv_inv] at h4
    rw [map_zero, h4] at h3
    exact Subtype.ext h3.symm
  · intro h v i
    simp only [j, LinearMap.pi_apply]
    exact hTeq _ h v

end GlobalTheory.BadCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesOfGroupDeterm
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

noncomputable section

namespace GlobalTheory.RegEmbed

variable {K Γ R : Type} [Field K] [Group Γ] [CommRing R] [Algebra K R]
  (act : Γ →* (R →ₐ[K] R)) (H : Subgroup Γ) [Fintype H]

theorem act_mul_apply (a b : Γ) (x : R) : act (a * b) x = act a (act b x) := by
  rw [map_mul]; rfl

theorem act_one_apply (x : R) : act 1 x = x := by
  rw [map_one]; rfl

theorem sum_act_act (x : R) (g : H) : ∑ k : H, act k (act g x) = ∑ k : H, act k x := by
  rw [← Equiv.sum_comp (Equiv.mulRight g⁻¹)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [← act_mul_apply]

theorem act_sum_act (x : R) (g : H) : act g (∑ k : H, act k x) = ∑ k : H, act k x := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  rw [← Equiv.sum_comp (Equiv.mulLeft g⁻¹)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Equiv.coe_mulLeft, ← act_mul_apply, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]

def invIn (V₁ : Submodule K R) : Submodule K R where
  carrier := {x | x ∈ V₁ ∧ ∀ h : H, act h x = x}
  add_mem' := fun ha hb => ⟨V₁.add_mem ha.1 hb.1, fun h => by rw [map_add (f := _), ha.2, hb.2]⟩
  zero_mem' := ⟨V₁.zero_mem, fun h => map_zero _⟩
  smul_mem' := fun c x hx => ⟨V₁.smul_mem c hx.1, fun h => by rw [map_smul, hx.2]⟩

def trL : R →ₗ[K] R := ∑ g : H, (act g).toLinearMap

theorem trL_apply (x : R) : trL act H x = ∑ g : H, act g x := by
  simp [trL]

theorem trL_mem (V₁ : Submodule K R) (hV₁ : ∀ h : H, ∀ x ∈ V₁, act h x ∈ V₁) (x : R) (hx : x ∈ V₁) :
    trL act H x ∈ invIn act H V₁ := by
  rw [trL_apply]
  exact ⟨V₁.sum_mem fun g _ => hV₁ g x hx, fun g => act_sum_act act H x g⟩

theorem eq_zero_of_traces [DecidableEq H] (u : R)
    (hdet : (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R) (v : R)
    (hv : ∀ h : H, ∑ g : H, act g (v * act h u) = 0) : v = 0 := by
  have h0 := GlobalTheory.mulVec_eq_zero_of_det_nonZeroDivisor (Matrix.transpose (Matrix.of fun h g : H => act ((h : Γ) * g) u))
    (by rwa [Matrix.det_transpose]) (fun g : H => act g v) (by
      funext h
      rw [Pi.zero_apply, ← hv h]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_mul (act (g : Γ)), act_mul_apply, mul_comm])
  simpa [act_one_apply] using congrFun h0 1

theorem eq_zero_of_sum [DecidableEq H] (u : R)
    (hdet : (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R) (F : H → R)
    (hF : ∀ g h : H, act g (F h) = F h) (h0 : ∑ h : H, F h * act h u = 0) : F = 0 := by
  refine GlobalTheory.mulVec_eq_zero_of_det_nonZeroDivisor _ hdet F ?_
  funext g
  have h2 := congrArg (fun x => act (g : Γ) x) h0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zero] at h2
  rw [Pi.zero_apply, ← h2]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_mul (act (g : Γ)), hF, act_mul_apply, mul_comm]

end GlobalTheory.RegEmbed

namespace GlobalTheory.BadCount


open GlobalTheory.RegEmbed in
theorem embReg_of_groupDet : ∀ (K Γ R : Type) [Field K] [Group Γ] [Finite Γ] [CommRing R] [Algebra K R] (act : Γ →* (R →ₐ[K] R)) (H : Subgroup Γ) [Fintype H] [DecidableEq H] (u : R), (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R → ∀ (V V₁ V₂ : Submodule K R) [FiniteDimensional K V₂] (ρ : Representation K Γ V), (∀ g x, (ρ g x : R) = act g x) → (∀ h : H, ∀ x ∈ V, x * act h u ∈ V₁) → (∀ h : H, ∀ x ∈ V₁, act h x ∈ V₁) → (∀ h : H, ∀ x ∈ V₁, x * act h u ∈ V₂) → ∃ n : ℕ, EmbReg ρ H n ∧ n * Nat.card H ≤ finrank K V₂ := by
  intro K Γ R _ _ _ _ _ act H _ _ u hdet V V₁ V₂ _ ρ hρ hV hV₁ hV₁₂
  let I := invIn act H V₁
  let T : H → (V →ₗ[K] I) := fun h =>
    ((trL act H).comp ((LinearMap.mulRight K (act h u)).comp V.subtype)).codRestrict I
      (fun v => trL_mem act H V₁ hV₁ _ (hV h v v.2))
  have hT : ∀ h v, ((T h v : I) : R) = ∑ g : H, act g (v * act h u) := fun h v => by
    simp [T, trL_apply]
  let Ψ : (H → I) →ₗ[K] V₂ :=
    (∑ h : H, (LinearMap.mulRight K (act h u)).comp (I.subtype.comp (LinearMap.proj h))).codRestrict V₂
      (fun F => by
        simp only [LinearMap.sum_apply, LinearMap.comp_apply]
        exact V₂.sum_mem fun h _ => hV₁₂ h _ (F h).2.1)
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro F hF
    have h0 := eq_zero_of_sum act H u hdet (fun h => (F h : R)) (fun g h => (F h).2.2 g) (by
      have := congrArg Subtype.val hF
      simpa [Ψ] using this)
    funext h
    exact Subtype.ext (congrFun h0 h)
  haveI : Module.Finite K (H → I) := Module.Finite.of_injective Ψ hΨ
  haveI : Module.Finite K I :=
    Module.Finite.of_surjective (LinearMap.proj (R := K) (φ := fun _ : H => I) 1) (fun x => ⟨fun _ => x, rfl⟩)
  have hle := LinearMap.finrank_le_finrank_of_injective hΨ
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
  let b := Module.finBasis K I
  let j : V →ₗ[K] (Fin (finrank K I) → MonoidAlgebra K H) := LinearMap.pi fun i =>
    (MonoidAlgebra.coeffLinearEquiv K).symm.toLinearMap ∘ₗ (Finsupp.linearEquivFunOnFinite K K H).symm.toLinearMap ∘ₗ
      LinearMap.pi (fun h => (LinearMap.proj i ∘ₗ b.equivFun.toLinearMap) ∘ₗ T h)
  have hj : ∀ v i h, (j v i).coeff h = b.equivFun (T h v) i := fun v i h => by
    simp [j]
  refine ⟨finrank K I, ⟨j, ?_, ?_⟩, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hTv : ∀ h, T h v = 0 := fun h => by
      apply b.equivFun.injective
      funext i
      rw [← hj, hv]
      simp
    apply Subtype.ext
    refine eq_zero_of_traces act H u hdet (v : R) fun h => ?_
    rw [← hT, hTv]
    rfl
  · intro h v i
    apply MonoidAlgebra.ext
    ext k
    rw [MonoidAlgebra.single_mul_apply, one_mul, hj, hj]
    have : T k (ρ h v) = T (h⁻¹ * k) v := by
      apply Subtype.ext
      rw [hT, hT, hρ]
      conv_rhs => rw [← sum_act_act act H _ h]
      refine Finset.sum_congr rfl fun g _ => ?_
      congr 1
      rw [map_mul (act (h : Γ)), Subgroup.coe_mul, Subgroup.coe_inv, ← act_mul_apply act (h : Γ) ((h : Γ)⁻¹ * k),
        mul_inv_cancel_left]
    rw [this]
  · rw [Nat.card_eq_fintype_card, mul_comm]
    exact hle

end GlobalTheory.BadCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegralClosurePiOfEtaleStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_integralClosure_pi_of_etale : ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] (E : ι → Type) [∀ i, CommRing (E i)]
    [∀ i, Algebra R (E i)], (∀ i, Algebra.Etale R (integralClosure R (E i))) →
    Algebra.Etale R (integralClosure R (∀ i, E i)) := by
  first | (exact @GlobalTheory.PiClosure.etale_integralClosure_pi) | (exact GlobalTheory.PiClosure.etale_integralClosure_pi) | (intros; apply GlobalTheory.PiClosure.etale_integralClosure_pi  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClopenIntegralOfSmoothOverField
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem exists_clopen_integral_of_smooth_over_field :
    ∀ (F : Type) [Field F] (Z : Scheme.{0}) (q : Z ⟶ Sp F), Smooth q → ∀ z : Z,
      ∃ (W' : Scheme.{0}) (j : W' ⟶ Z), IsClosedImmersion j ∧ IsOpenImmersion j ∧ IsIntegral W' ∧
        z ∈ Set.range j := by
  intro F _ Z q hq z
  obtain ⟨hR, hN, hL⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F Z q hq
  have : GlobalTheory.IsNormalScheme Z := by first | exact hN | exact IsNormalScheme.of_pred hN
  have hC : irreducibleComponent z ∈ irreducibleComponents Z := irreducibleComponent_mem_irreducibleComponents z
  let C : Z.Opens := ⟨irreducibleComponent z, IsNormalScheme.isOpen_of_mem_irreducibleComponents hC⟩
  have hzC : z ∈ C := mem_irreducibleComponent
  have hrange : Set.range C.ι = (C : Set Z) := Scheme.Opens.range_ι C
  refine ⟨C.toScheme, C.ι, ?_, inferInstance, ?_, by rw [hrange]; exact hzC⟩
  · apply IsClosedImmersion.of_isPreimmersion
    rw [hrange]
    exact isClosed_of_mem_irreducibleComponents _ hC
  · have : IrreducibleSpace C := Subtype.irreducibleSpace isIrreducible_irreducibleComponent
    have : Nonempty C := ⟨⟨z, hzC⟩⟩
    exact isIntegral_of_irreducibleSpace_of_isReduced C.toScheme

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveCochainModelTrivialProjectiveBundStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_cochainModel_trivialProjectiveBundle : ∀ (q : ℕ) [NeZero q] (N : ℕ) (i : ℤ), ∃ (J : Cx (ZMod q)) (ψ : ∀ j : Fin N, Cocycle (res (ZMod q) (tw q (i - (j : ℕ)))) J (2 * (j : ℕ))), J.IsStrictlyGE 0 ∧ (∀ n, CategoryTheory.Injective (J.X n)) ∧ ∀ F : PSh, Inv q (disc.obj F) → ∀ n : ℤ, ∃ e : CohomologyClass ((chains (ZMod q)).obj (disc.obj F)) J n ≃+ Ht q (pullback (trivV N (disc.obj F)) (PGL.pr N)) n i, ∀ a : ∀ j : Fin N, Ht q (disc.obj F) (n - 2 * (j : ℕ)) (i - (j : ℕ)), e (∑ j, cpost _ (ψ j) (n - 2 * (j : ℕ)) n (by omega) (a j)) = pbfMap q (trivV N (disc.obj F)) n i a := by
  first | (exact @GlobalTheory.EtC.pbf_disc_model) | (exact GlobalTheory.EtC.pbf_disc_model) | (intros; apply GlobalTheory.EtC.pbf_disc_model  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianModelOfDivisorOfConstantsStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_noetherian_model_of_divisor_of_constants : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E] [Algebra T E]
      [IsScalarTower T (Polynomial T) E] [Algebra.Etale (Polynomial T) E]
      (Q : Ideal E) [Q.IsPrime],
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (j : Localization.AtPrime Q →+* O),
      j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O →
    ∀ (b₁ c₁ : Localization.AtPrime Q) (s : T), s ≠ 0 →
      b₁ * c₁ = algebraMap T (Localization.AtPrime Q) s →
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A) (_ : IsNoetherianRing A)
      (_ : IsIntegrallyClosed A) (_ : Algebra.EssFiniteType ℤ A) (i : A →+* T),
      Function.Injective i ∧ IsLocalHom i ∧
      ∃ (EA : Type) (_ : CommRing EA) (_ : Algebra (Polynomial A) EA) (_ : Algebra A EA)
        (_ : IsScalarTower A (Polynomial A) EA) (_ : Algebra.Etale (Polynomial A) EA)
        (QA : Ideal EA) (_ : QA.IsPrime),
        QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A ∧
      ∃ (jA : Localization.AtPrime QA →+* O),
        jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
          (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) ∧
      ∃ (bA cA : Localization.AtPrime QA) (sA : A), sA ≠ 0 ∧ i sA = s ∧
        bA * cA = algebraMap A (Localization.AtPrime QA) sA ∧ jA bA = j b₁ := by
  first | (exact @GlobalTheory.VertUnitsNoeth.exists_noetherian_model_of_mul_eq) | (exact GlobalTheory.VertUnitsNoeth.exists_noetherian_model_of_mul_eq) | (intros; apply GlobalTheory.VertUnitsNoeth.exists_noetherian_model_of_mul_eq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalLocalDomainOverHenselianPrimeStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_local_domain_over_henselian_prime : ∀ (A : Type) [CommRing A] [HenselianLocalRing A] (𝔭 : Ideal A) [𝔭.IsPrime],
    ∃ (S : Type) (_ : CommRing S) (_ : IsDomain S) (_ : IsIntegrallyClosed S) (_ : IsLocalRing S) (f : A →+* S), f.IsIntegral ∧ RingHom.ker f = 𝔭 := by
  first | (exact @GlobalTheory.NormalLocal.exists_normal_local) | (exact GlobalTheory.NormalLocal.exists_normal_local) | (intros; apply GlobalTheory.NormalLocal.exists_normal_local  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumSemidirectCosetPairingNeZeroStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_semidirect_coset_pairing_ne_zero : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∀ Y ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∀ z : ℤ, ∑ᶠ g, X (inl g) * star (Y (inl g)) = z * (Nat.card G : ℂ) → ¬ ((Nat.card Γ : ℤ) ∣ z) → ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) ≠ 0 := by
  first | (exact @GlobalTheory.Shin.finsum_coset_pair_ne_zero) | (exact GlobalTheory.Shin.finsum_coset_pair_ne_zero) | (intros; apply GlobalTheory.Shin.finsum_coset_pair_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftCharpolyRootPowerSumEqNormStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shintaniLift_charpoly_rootPowerSum_eq_norm : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ) (k n : ℕ) (δ : GL (Fin n) F'), shLift s (chG (rootSum (pullθ ι θ) k) n) δ = chG (rootSum θ k) n (nrm s δ) := by
  first | (exact @GlobalTheory.Shin.shLift_chG_rootSum) | (exact GlobalTheory.Shin.shLift_chG_rootSum) | (intros; apply GlobalTheory.Shin.shLift_chG_rootSum  <;> assumption)
end

