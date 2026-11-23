module

public import Formalism.LocalToGlobal.GlobalTheory.GL4.PFrCore
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel

@[expose] public section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions Formalism.L2.GlobalTheoryTheory.Comp

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F

variable (v : HeightOneSpectrum (𝓞 F))

abbrev lv (Λ : Submodule (𝓞 E) (n → E)) : Submodule (intV E v) (n → E ⊗[F] v.adicCompletion F) :=
  latS (F := F) (v.adicCompletion F) (intV E v) Λ

theorem prV_hat {Λ : Submodule (𝓞 E) (n → E)} (u : n → 𝒜) (hu : u ∈ hat F Λ) :
    (fun i => prV (E := E) v (u i)) ∈ lv v Λ := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero =>
    have : (fun i => prV (E := E) v ((0 : n → 𝒜) i)) = 0 := by funext i; simp
    rw [this]; exact zero_mem _
  | add u w _ _ hu hw =>
    have : (fun i => prV (E := E) v ((u + w) i)) =
        (fun i => prV (E := E) v (u i)) + (fun i => prV (E := E) v (w i)) := by funext i; simp
    rw [this]; exact add_mem hu hw
  | smul s u _ hu =>
    have hs := afsplit_prV_int (E := E) v (s : 𝒜) s.2
    have : (fun i => prV (E := E) v ((s • u) i)) =
        (⟨_, hs⟩ : intV E v) • (fun i => prV (E := E) v (u i)) := by
      funext i
      simp [Subring.smul_def, map_mul]
    rw [this]; exact Submodule.smul_mem _ _ hu

theorem bc_mulVec_vi (k : GL n 𝒜) (x : n → E) :
    ((bc (prV (E := E) v) k : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n _) *ᵥ
      (fun i => inclE (F := F) (v.adicCompletion F) (x i)) =
      fun i => prV (E := E) v (((k : Matrix n n 𝒜) *ᵥ vi F x) i) := by
  funext i
  rw [RingHom.map_mulVec]
  rfl

theorem loc_fwd {Λ Λ' : Submodule (𝓞 E) (n → E)} (k : GL n 𝒜) (hk : ∀ u ∈ hat F Λ, (k : Matrix n n 𝒜) *ᵥ u ∈ hat F Λ')
    (y : n → E ⊗[F] v.adicCompletion F) (hy : y ∈ lv v Λ) :
    ((bc (prV (E := E) v) k : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n _) *ᵥ y ∈ lv v Λ' := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [bc_mulVec_vi]
    exact prV_hat v _ (hk _ (vi_mem_hat hx))
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add y w _ _ hy hw => rw [mulVec_add]; exact add_mem hy hw
  | smul t y _ hy =>
    rw [Subring.smul_def, mulVec_smul]
    exact Submodule.smul_mem _ t hy

end Loc

section Lev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]



end Lev

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

end
