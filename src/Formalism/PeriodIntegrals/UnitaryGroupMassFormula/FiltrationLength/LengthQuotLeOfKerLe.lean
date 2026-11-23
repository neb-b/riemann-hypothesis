module

public import Mathlib

@[expose] public section

namespace PI.FiltrationLength

open Submodule

variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]

noncomputable def ell (B A : Submodule R W) : ℕ∞ :=
  Module.length R (↥B ⧸ A.comap B.subtype)

theorem ell_add {A B C : Submodule R W} (hAC : A ≤ C) (hCB : C ≤ B) :
    ell B A = ell C A + ell B C := by
  unfold ell
  let f : (↥C ⧸ A.comap C.subtype) →ₗ[R] (↥B ⧸ A.comap B.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hCB) (fun x hx => by simpa using hx)
  let g : (↥B ⧸ A.comap B.subtype) →ₗ[R] (↥B ⧸ C.comap B.subtype) :=
    Submodule.mapQ _ _ LinearMap.id (fun x hx => by simpa using hAC hx)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | _ c =>
      rw [LinearMap.mem_ker] at hy
      simp only [f, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
        Submodule.coe_subtype, Submodule.coe_inclusion] at hy
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact hy
  have hg : Function.Surjective g := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | _ b => exact ⟨Submodule.Quotient.mk b, by simp [g]⟩
  have H : Function.Exact f g := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | _ b =>
      constructor
      · intro hb
        simp only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
          Submodule.mem_comap, Submodule.coe_subtype] at hb
        exact ⟨Submodule.Quotient.mk ⟨b, hb⟩, by simp [f]; rfl⟩
      · rintro ⟨z, hz⟩
        induction z using Submodule.Quotient.induction_on with
        | _ c =>
          simp only [f, Submodule.mapQ_apply] at hz
          rw [Submodule.Quotient.eq] at hz
          simp only [Submodule.mem_comap, Submodule.coe_subtype, AddSubgroupClass.coe_sub,
            Submodule.coe_inclusion] at hz
          simp only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
            Submodule.mem_comap, Submodule.coe_subtype]
          have h1 : (c : W) ∈ C := c.2
          have h2 : (c : W) - (b : W) ∈ C := hAC hz
          have := C.sub_mem h1 h2
          simpa using this
  exact Module.length_eq_add_of_exact f g hf hg H

theorem ell_sup_le {A C D : Submodule R W} (hDA : D ≤ A) :
    ell (A ⊔ C) A ≤ ell C D := by
  unfold ell
  refine Module.length_le_of_surjective
    (Submodule.mapQ (D.comap C.subtype) (A.comap (A ⊔ C).subtype)
      (Submodule.inclusion (le_sup_right : C ≤ A ⊔ C)) (fun x hx => by simpa using hDA hx)) ?_
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ z =>
    obtain ⟨a, ha, c, hc, hz⟩ := Submodule.mem_sup.mp z.2
    refine ⟨Submodule.Quotient.mk ⟨c, hc⟩, ?_⟩
    simp only [Submodule.mapQ_apply]
    rw [Submodule.Quotient.eq]
    simp only [Submodule.mem_comap, Submodule.coe_subtype, AddSubgroupClass.coe_sub,
      Submodule.coe_inclusion]
    have : (c : W) - (z : W) = -a := by rw [← hz]; abel
    rw [this]
    exact A.neg_mem ha

end PI.FiltrationLength
