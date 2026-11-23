module

public import Mathlib
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PlusPolynomialInclusion
section
noncomputable section

open Polynomial TensorProduct Matrix NumberField IsDedekindDomain Formalism.UG

namespace GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def sharp (c : E ≃ₐ[F] E) (r : ℕ) (P : E[X]) : E[X] :=
  C (c (P.coeff 0))⁻¹ * reflect r (P.map (c : E →+* E))

def IsPPol (c : E ≃ₐ[F] E) (r : ℕ) (P : E[X]) : Prop :=
  P.Monic ∧ Irreducible P ∧ P.natDegree = r ∧ P.coeff 0 ≠ 0 ∧ P = sharp c r P

variable {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}

theorem isUnit_root (hP : IsPPol c r P) : IsUnit (AdjoinRoot.root P) := by
  haveI : Fact (Irreducible P) := ⟨hP.2.1⟩
  refine Ne.isUnit fun h => hP.2.2.2.1 ?_
  have h1 := AdjoinRoot.eval₂_root P
  rw [h, eval₂_at_zero] at h1
  exact (map_eq_zero_iff _ (AdjoinRoot.of P).injective).1 h1

def alpha (hP : IsPPol c r P) : (AdjoinRoot P)ˣ := (isUnit_root hP).unit

theorem eval₂_conj_inv (hP : IsPPol c r P) :
    P.eval₂ ((AdjoinRoot.of P).comp (c : E →+* E)) ((alpha hP)⁻¹ : (AdjoinRoot P)ˣ) = 0 := by
  rw [← eval₂_map]
  letI : Invertible (((alpha hP)⁻¹ : (AdjoinRoot P)ˣ) : AdjoinRoot P) := Units.invertible _
  have hd : (P.map (c : E →+* E)).natDegree ≤ r := hP.2.2.1 ▸ natDegree_map_le
  rw [← eval₂_reflect_eq_zero_iff _ _ r _ hd]
  have h1 : ⅟(((alpha hP)⁻¹ : (AdjoinRoot P)ˣ) : AdjoinRoot P) = AdjoinRoot.root P := rfl
  have h2 : reflect r (P.map (c : E →+* E)) = C (c (P.coeff 0)) * P := by
    have hne : c (P.coeff 0) ≠ 0 := by simpa using hP.2.2.2.1
    conv_rhs => rw [hP.2.2.2.2]
    rw [← hP.2.2.2.2]
    conv_rhs => arg 2; rw [hP.2.2.2.2]
    rw [sharp, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hne, C_1, one_mul]
  rw [h1, h2, eval₂_mul, AdjoinRoot.eval₂_root, mul_zero]

def starL (hP : IsPPol c r P) : AdjoinRoot P →ₐ[F] AdjoinRoot P :=
  { AdjoinRoot.lift ((AdjoinRoot.of P).comp (c : E →+* E))
      (((alpha hP)⁻¹ : (AdjoinRoot P)ˣ) : AdjoinRoot P) (eval₂_conj_inv hP) with
    commutes' := fun a => by
      have h : algebraMap F (AdjoinRoot P) a = AdjoinRoot.of P (algebraMap F E a) := rfl
      rw [h]
      simp }

def Lplus (hP : IsPPol c r P) : Subalgebra F (AdjoinRoot P) :=
  AlgHom.equalizer (starL hP) (AlgHom.id F (AdjoinRoot P))

variable (k : Type) [Field k] [Algebra F k]

@[reducible] def algLk (P : E[X]) : Algebra (E ⊗[F] k) (AdjoinRoot P ⊗[F] k) :=
  (Algebra.TensorProduct.map (IsScalarTower.toAlgHom F E (AdjoinRoot P))
    (AlgHom.id F k)).toRingHom.toAlgebra

attribute [local instance] algLk

def starLk (hP : IsPPol c r P) : AdjoinRoot P ⊗[F] k →+* AdjoinRoot P ⊗[F] k :=
  sigR (starL hP) k

def inclPlus (hP : IsPPol c r P) : Lplus hP ⊗[F] k →+* AdjoinRoot P ⊗[F] k :=
  (Algebra.TensorProduct.map (Lplus hP).val (AlgHom.id F k)).toRingHom

def trLk (P : E[X]) : AdjoinRoot P ⊗[F] k →ₗ[F] E ⊗[F] k :=
  TensorProduct.map ((Algebra.trace E (AdjoinRoot P)).restrictScalars F) LinearMap.id

def hx (hP : IsPPol c r P) (x : (Lplus hP ⊗[F] k)ˣ) (y y' : AdjoinRoot P ⊗[F] k) : E ⊗[F] k :=
  trLk k P (inclPlus k hP x * y * starLk k hP y')

variable {k}

variable (k)

end GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SemilinearExtensionBases
section
noncomputable section

open scoped TensorProduct
open Module

namespace GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases

def IsForm (LL : Type) {Ks WL : Type} [Field Ks] [Field LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    (WK : Submodule Ks WL) : Prop :=
  ∃ (n : ℕ) (b : Fin n → WL), (∀ i, b i ∈ WK) ∧ LinearIndependent Ks b ∧
    Submodule.span Ks (Set.range b) = WK ∧ LinearIndependent LL b ∧ Submodule.span LL (Set.range b) = ⊤

section

variable {Ks LL WL : Type} [Field Ks] [Field LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
  {WK : Submodule Ks WL}
  (O : Type) {K K'' : Type} [CommRing O] [Field K] [Algebra Ks K] [Field K''] [Algebra O K'']
  {Fm : Type} [AddCommGroup Fm] [Module K Fm] [Module O Fm]

def IsExt (emb : LL →+* K'') (eF : Fm ≃ₗ[K] K ⊗[Ks] WK) (e : WL →ₛₗ[emb] K'' ⊗[O] Fm) : Prop :=
  ∀ (ι : Type) [Fintype ι] (a : ι → LL) (f : ι → WK),
    e (∑ k, a k • (f k : WL)) = ∑ k, emb (a k) ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] f k)

def CarriesBases {emb : LL →+* K''} (e : WL →ₛₗ[emb] K'' ⊗[O] Fm) : Prop :=
  ∀ (ι : Type) (b : Basis ι LL WL), ∃ b'' : Basis ι K'' (K'' ⊗[O] Fm), ∀ i, b'' i = e (b i)

end

def SemilinearExtension : Prop :=
  ∀ (Ks LL WL : Type) [Field Ks] [Field LL] [Algebra Ks LL]
    [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    (WK : Submodule Ks WL), IsForm LL WK →
  ∀ (O K K'' : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] [Algebra Ks K]
    [Field K''] [Algebra O K''] [Algebra K K''] [IsScalarTower O K K'']
    (emb : LL →+* K''), emb.comp (algebraMap Ks LL) = (algebraMap K K'').comp (algebraMap Ks K) →
  ∀ (Fm : Type) [AddCommGroup Fm] [Module K Fm] [Module O Fm] [IsScalarTower O K Fm]
    (eF : Fm ≃ₗ[K] K ⊗[Ks] WK),
    (∃! e : WL →ₛₗ[emb] K'' ⊗[O] Fm, IsExt O emb eF e) ∧
    (∀ e : WL →ₛₗ[emb] K'' ⊗[O] Fm, IsExt O emb eF e → CarriesBases O e) ∧
    (∀ (a : Ks) (m : Fm),
      emb (algebraMap Ks LL a) ⊗ₜ[O] m = (1 : K'') ⊗ₜ[O] (algebraMap Ks K a • m))

theorem IsExt.apply_coe {Ks LL WL : Type} [Field Ks] [Field LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    {WK : Submodule Ks WL} {O K K'' : Type} [CommRing O] [Field K] [Algebra Ks K] [Field K''] [Algebra O K'']
    {Fm : Type} [AddCommGroup Fm] [Module K Fm] [Module O Fm]
    {emb : LL →+* K''} {eF : Fm ≃ₗ[K] K ⊗[Ks] WK} {e : WL →ₛₗ[emb] K'' ⊗[O] Fm} (h : IsExt O emb eF e) (f : WK) :
    e f = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] f) := by
  simpa using h Unit (fun _ => 1) (fun _ => f)

end GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases
end
end

