module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.Bundle0001

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Whittaker

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option linter.unusedSectionVars false

namespace WhittakerInverseTranspose

section Tilde

theorem invT_invT' {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    GlobalTheory.CuspRep.invT n R (GlobalTheory.CuspRep.invT n R g) = g := Units.ext rfl

theorem val_invT' {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    ((GlobalTheory.CuspRep.invT n R g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)ᵀ := rfl

theorem continuous_invT' (N : ℕ) : Continuous (GlobalTheory.CuspRep.invT N k) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem isSmooth_comp_invT {N : ℕ} {ρ : Representation ℂ (GL (Fin N) k) V} (h : IsSmooth ρ) :
    IsSmooth (ρ.comp (GlobalTheory.CuspRep.invT N k)) :=
  fun v => (h v).preimage (continuous_invT' N)

theorem isIrreducible_comp_invT {N : ℕ} {ρ : Representation ℂ (GL (Fin N) k) V} (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp (GlobalTheory.CuspRep.invT N k)) := by
  let Φ : Subrepresentation (ρ.comp (GlobalTheory.CuspRep.invT N k)) ≃o Subrepresentation ρ :=
    { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
        rw [← invT_invT' N g]
        exact U.apply_mem_toSubmodule (GlobalTheory.CuspRep.invT N k g) hv⟩
      invFun := fun U => ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule _ hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  have : IsSimpleOrder (Subrepresentation ρ) := h
  exact Φ.isSimpleOrder

theorem mem_unipRad_iff' {s N : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin N) (g : GL (Fin N) k) :
    g ∈ unipRad k e ↔ ∀ x y, ((e.symm y).1 < (e.symm x).1 → (g : Matrix (Fin N) (Fin N) k) x y = 0) ∧
      ((e.symm x).1 = (e.symm y).1 →
        (g : Matrix (Fin N) (Fin N) k) x y = (1 : Matrix (Fin N) (Fin N) k) x y) := by
  rw [mem_unipRad, mem_parab_iff]
  constructor
  · rintro ⟨h1, h2⟩ x y
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective x
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective y
    simp only [Equiv.symm_apply_apply]
    refine ⟨fun hab => h1 a b i j hab, fun hab => ?_⟩
    subst hab
    rw [h2 a i j]
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne]
      intro h; exact hij (eq_of_heq (Sigma.mk.inj_iff.1 (e.injective h)).2)
  · intro h
    refine ⟨fun a b i j hab => (h _ _).1 (by simpa using hab), fun a i j => ?_⟩
    rw [(h _ _).2 (by simp)]
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne]
      intro h'; exact hij (eq_of_heq (Sigma.mk.inj_iff.1 (e.injective h')).2)

theorem invT_mem_unipRad {s N : ℕ} {d d' : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin N)
    (e' : (Σ a, Fin (d' a)) ≃ Fin N) (he : ∀ x, (e'.symm x).1 = Fin.rev (e.symm x).1) {g : GL (Fin N) k}
    (hg : g ∈ unipRad k e) : GlobalTheory.CuspRep.invT N k g ∈ unipRad k e' := by
  have hi := (mem_unipRad_iff' e _).1 (inv_mem hg)
  refine (mem_unipRad_iff' e' _).2 fun x y => ⟨fun hxy => ?_, fun hxy => ?_⟩
  · rw [val_invT', Matrix.transpose_apply]
    refine (hi y x).1 ?_
    rw [he, he] at hxy
    exact Fin.rev_lt_rev.1 hxy
  · rw [val_invT', Matrix.transpose_apply, (hi y x).2 ?_]
    · by_cases hxy' : x = y
      · subst hxy'; rfl
      · rw [Matrix.one_apply_ne hxy', Matrix.one_apply_ne (Ne.symm hxy')]
    · rw [he, he] at hxy; exact (Fin.rev_injective hxy).symm

theorem isCuspidal_comp_invT {N : ℕ} {ρ : Representation ℂ (GL (Fin N) k) V} (h : IsCuspidal ρ) :
    IsCuspidal (ρ.comp (GlobalTheory.CuspRep.invT N k)) := by
  refine ⟨isSmooth_comp_invT h.1, fun s d e hne => ?_⟩
  let e' : (Σ a, Fin (d (Fin.revPerm a))) ≃ Fin N :=
    (Equiv.sigmaCongrLeft (β := fun a => Fin (d a)) Fin.revPerm).trans e
  have he : ∀ x, (e'.symm x).1 = Fin.rev (e.symm x).1 := fun x => by
    have h1 : e'.symm x = (Equiv.sigmaCongrLeft (β := fun a => Fin (d a)) Fin.revPerm).symm (e.symm x) := rfl
    obtain ⟨⟨a, i⟩, hq⟩ : ∃ q, (Equiv.sigmaCongrLeft (β := fun a => Fin (d a)) Fin.revPerm).symm (e.symm x) = q :=
      ⟨_, rfl⟩
    have h2 := congrArg (Equiv.sigmaCongrLeft (β := fun a => Fin (d a)) Fin.revPerm) hq
    rw [Equiv.apply_symm_apply, Equiv.sigmaCongrLeft_apply] at h2
    rw [h1, hq, h2]
    simp
  have he' : ∀ x, (e.symm x).1 = Fin.rev (e'.symm x).1 := fun x => by rw [he, Fin.rev_rev]
  have hne' : unipRad k e' ≠ ⊥ := by
    obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨_, invT_mem_unipRad e e' he hg⟩, fun h1 => hg1 ?_⟩
    have h2 : GlobalTheory.CuspRep.invT N k g = 1 := congrArg Subtype.val h1
    refine Subtype.ext ?_
    show g = 1
    rw [← invT_invT' N g, h2, map_one]
  have hs := h.2 s (fun a => d (Fin.revPerm a)) e' hne'
  have htop : twKer ρ (unipRad k e') 1 = ⊤ := Submodule.Quotient.subsingleton_iff.1 hs
  show Subsingleton (V ⧸ twKer _ _ 1)
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff, ← htop]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨n, v, rfl⟩
  refine Submodule.subset_span ⟨⟨GlobalTheory.CuspRep.invT N k n, invT_mem_unipRad e' e he' n.2⟩, v, ?_⟩
  simp [invT_invT']

end Tilde

end WhittakerInverseTranspose

end PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing

end
