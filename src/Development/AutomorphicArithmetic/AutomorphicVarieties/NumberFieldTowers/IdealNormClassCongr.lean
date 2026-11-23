module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum
open scoped nonZeroDivisors

namespace UpperTheory.V.Tower

section Norm

variable (K : Type) {K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']

def idNorm : (Ideal (𝓞 K'))⁰ →* (Ideal (𝓞 K))⁰ where
  toFun I := ⟨Ideal.relNorm (𝓞 K) I.1, mem_nonZeroDivisors_of_ne_zero fun h =>
    nonZeroDivisors.ne_zero I.2 (Ideal.relNorm_eq_bot_iff.1 h)⟩
  map_one' := Subtype.ext (map_one (Ideal.relNorm (𝓞 K)))
  map_mul' I J := Subtype.ext (map_mul (Ideal.relNorm (𝓞 K)) I.1 J.1)

theorem ideal_norm_class_congr {I J : (Ideal (𝓞 K'))⁰} (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    ClassGroup.mk0 (idNorm K I) = ClassGroup.mk0 (idNorm K J) := by
  rw [ClassGroup.mk0_eq_mk0_iff] at h ⊢
  obtain ⟨x, y, hx, hy, h⟩ := h
  refine ⟨Algebra.intNorm (𝓞 K) (𝓞 K') x, Algebra.intNorm (𝓞 K) (𝓞 K') y, fun h => hx (Algebra.intNorm_eq_zero.1 h),
    fun h => hy (Algebra.intNorm_eq_zero.1 h), ?_⟩
  have := congrArg (Ideal.relNorm (𝓞 K)) h
  rw [map_mul, map_mul, Ideal.relNorm_singleton, Ideal.relNorm_singleton] at this
  exact this

def nFun (c : ClassGroup (𝓞 K')) : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 (idNorm K (ClassGroup.mk0_surjective c).choose)

private theorem norm_function_mk (I : (Ideal (𝓞 K'))⁰) : nFun K (ClassGroup.mk0 I) = ClassGroup.mk0 (idNorm K I) :=
  ideal_norm_class_congr K (ClassGroup.mk0_surjective _).choose_spec

def clNorm : ClassGroup (𝓞 K') →* ClassGroup (𝓞 K) :=
  MonoidHom.mk' (nFun K) fun a b => by
    obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective a
    obtain ⟨J, rfl⟩ := ClassGroup.mk0_surjective b
    rw [← map_mul, norm_function_mk, norm_function_mk, norm_function_mk, map_mul, map_mul]

end Norm

section Lim

variable (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]

omit [IsAlgClosure L Ω] in
theorem Fn_le_succ (n : ℕ) : Fn L Ω l n ≤ Fn L Ω l (n + 1) := by
  refine IntermediateField.adjoin.mono _ _ _ fun x hx => ?_
  have h0 : ∀ m : ℕ, (Polynomial.X ^ l ^ m - 1 : Polynomial L) ≠ 0 := fun m =>
    Polynomial.X_pow_sub_C_ne_zero (pow_pos (Fact.out : l.Prime).pos m) 1
  rw [Polynomial.mem_rootSet_of_ne (h0 _)] at hx ⊢
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, sub_eq_zero] at hx ⊢
  rw [pow_succ, pow_mul, hx, one_pow]

def normStep (n : ℕ) : ClassGroup (𝓞 (Fn L Ω l (n + 1))) →* ClassGroup (𝓞 (Fn L Ω l n)) :=
  letI : Algebra (Fn L Ω l n) (Fn L Ω l (n + 1)) := (IntermediateField.inclusion (Fn_le_succ l L Ω n)).toRingHom.toAlgebra
  clNorm (Fn L Ω l n)

variable (k : Type) [Field k] [NumberField k] [Algebra k Ω] [IsAlgClosure k Ω]

theorem galOf_Fn (n : ℕ) : galOf k (Fn L Ω l n) Ω = levU l (galOf k L Ω) n :=
  haveI := (fnCyc L Ω l n).1
  galOfCyc k Ω l n L (Fn L Ω l n)

theorem cycU_le_Fn (n : ℕ) : cycU l (galOf k L Ω) ≤ galOf k (Fn L Ω l n) Ω :=
  (galOf_Fn l L Ω k n).symm ▸ cycU_le_levU l _ n

abbrev pullN (n : ℕ) : (ClassGroup (𝓞 (Fn L Ω l n)) → QZ l) →ₗ[ℤ_[l]] (cycU l (galOf k L Ω) → QZ l) :=
  clPull (Fn L Ω l n) (cycU_le_Fn l L Ω k n) ℤ_[l] (QZ l)

end Lim

section Desc

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

variable (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra L Ω] [IsScalarTower k L Ω] [IsAlgClosure L Ω]

def IsDesc {l : ℕ} [Fact l.Prime] (D : LData L Ω l) (e : ℤ) (U : Subgroup (G k Ω)) [U.Normal]
    (Φ : Sha D e →ₗ[ℤ_[l]] ShaD l l U (galOf k L Ω) e) : Prop :=
  ∀ (x : Sha D e) (u : Uinf L Ω l) (u' : cycU l U), u'.1 = galEmb k L Ω u.1 → (Φ x).1.1 u' = resInf D e x.1 u

variable [Normal k L]

variable (k Ω) (l : ℕ) [Fact l.Prime] (N : ℕ)

end Desc

end UpperTheory.V.Tower

end
