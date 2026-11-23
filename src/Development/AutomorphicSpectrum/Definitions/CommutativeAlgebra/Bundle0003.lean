module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OmStable
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

structure HTPoint (C O : Type) [Field C] [CommRing O] [Algebra O C] {E : Type} [Field E] [NumberField E]
    (c : E ≃+* E) (κ : O) (N : ℕ)
    (V Ω : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
    [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω] where

  T : Submodule O V

  ρ : 𝓞 E →+* Module.End C V

  t : Fin N → V
  free : IsFreeOn ρ T t

  e : V →ₗ[C] V →ₗ[C] C
  alt : ∀ x, e x x = 0
  nondeg : ∀ y, (∀ x, e x y = 0) → y = 0
  perfect : dualLat e T = T
  adj : ∀ (a : 𝓞 E) (x y : V), e (ρ a x) y = e x (ρ (RingOfIntegers.mapRingEquiv c a) y)

  om : Submodule O Ω
  om_lat : om.IsFullLattice C

  ρΩ : 𝓞 E →+* Module.End C Ω
  om_stable : ∀ (a : 𝓞 E), ∀ x ∈ om, ρΩ a x ∈ om

  ht : V →ₗ[C] Ω
  ht_lin : ∀ (a : 𝓞 E) (x : V), ht (ρ a x) = ρΩ a (ht x)
  ht_mem : ∀ x ∈ T, ht x ∈ om
  κ_ne : algebraMap O C κ ≠ 0
  κ_mem : ∀ y ∈ om, ∃ x ∈ T, ht x = κ • y
  lagr : ∀ x, ht x = 0 ↔ ∀ y, ht y = 0 → e x y = 0

namespace HTPoint

variable {C O : Type} [Field C] [CommRing O] [Algebra O C] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {κ : O} {N : ℕ}
  {V Ω : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω]
  (P : HTPoint C O c κ N V Ω)

def W : Submodule C V := LinearMap.ker P.ht

def om' : Submodule O Ω := P.T.map (P.ht.restrictScalars O)

def Wsp (σ : E →+* C) : Submodule C V := P.W ⊓ eigSp P.ρ σ

def Ωsp (σ : E →+* C) : Submodule C Ω := eigSp P.ρΩ σ

def W' (σ : E →+* C) : Submodule O V := P.W.restrictScalars O ⊓ eigSub P.ρ σ P.T

def omHT (σ : E →+* C) : Submodule O Ω := eigQuot P.ρΩ σ P.om'

def omRec (σ : E →+* C) : Submodule O Ω := eigQuot P.ρΩ σ P.om

def tate (x : Fin N → 𝓞 E) : V := ∑ i, P.ρ (x i) (P.t i)

end HTPoint

end GlobalTheory.CompanionTheory.Ar.HT
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
  {F : Type} [Field F] {N : Type} [AddCommGroup N] [Module F N]

def IsFund (p : ℕ) (σ : MulChar F R) : Prop :=
  ∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}


variable (F) in
def FStable (M : Submodule R (N → C)) : Prop :=
  ∀ a : F, ∀ g ∈ M, (fun x => g (a • x)) ∈ M

def eig (M : Submodule R (N → C)) (χ : MulChar F R) : Submodule R (N → C) where
  carrier := {g | g ∈ M ∧ ∀ (a : F) x, g (a • x) = algebraMap R C (χ a) * g x}
  add_mem' := by
    intro f g hf hg
    exact ⟨M.add_mem hf.1 hg.1, fun a x => by simp [hf.2 a x, hg.2 a x, mul_add]⟩
  zero_mem' := ⟨M.zero_mem, fun _ _ => by simp⟩
  smul_mem' := by
    intro c f hf
    refine ⟨M.smul_mem c hf.1, fun a x => ?_⟩
    simp only [Pi.smul_apply, hf.2 a x, Algebra.smul_def]; ring

abbrev OmType (M : Submodule R (N → C)) (χ : MulChar F R) :=
  eig M χ ⧸ (sqIdeal (augIdeal M)).comap (eig M χ).subtype

def proj [Fintype F] [DecidableEq F] (χ : MulChar F R) (g : N → C) : N → C :=
  fun x => (Fintype.card Fˣ : C)⁻¹ * ∑ a : Fˣ, algebraMap R C (χ⁻¹ (a : F)) * g ((a : F) • x)

def xIdeal (M : Submodule R (F → C)) (χ : MulChar F R) : Ideal R :=
  M.comap (LinearMap.toSpanSingleton R (F → C) fun a => algebraMap R C (χ a))

def stepOrder (M : Submodule R (N → C)) (K : Submodule F N) (t : N) : Submodule R (F → C) :=
  (invFun M K.toAddSubgroup).map (LinearMap.funLeft R C fun a : F => a • t)

def stepOrderRes (M : Submodule R (N → C)) (K : Submodule F N) (t : N) : Submodule R (F → C) where
  carrier := {h | ∃ g ∈ M, ∀ a : F, ∀ k ∈ K, g (a • t + k) = h a}
  add_mem' := by
    rintro h h' ⟨g, hg, e⟩ ⟨g', hg', e'⟩
    exact ⟨g + g', M.add_mem hg hg', fun a k hk => by simp [e a k hk, e' a k hk]⟩
  zero_mem' := ⟨0, M.zero_mem, fun _ _ _ => rfl⟩
  smul_mem' := by
    rintro c h ⟨g, hg, e⟩
    exact ⟨c • g, M.smul_mem c hg, fun a k hk => by simp [e a k hk]⟩

def idealX (M : Submodule R (N → C)) (K : Submodule F N) (t : N) (χ : MulChar F R) : Ideal R :=
  xIdeal (stepOrder M K t) χ

def idealD (p : ℕ) (M : Submodule R (N → C)) (K : Submodule F N) (t : N) (χ : MulChar F R) :
    Ideal R where
  carrier := {c | ∃ g ∈ afFun p M,
    (∀ (a : F) x, g (a • x) - algebraMap R C (χ a) * g x ∈ pInt (C := C) R p) ∧
    (∀ k ∈ K, g k ∈ pInt (C := C) R p) ∧ g t - algebraMap R C c ∈ pInt (C := C) R p}
  add_mem' := by
    rintro c c' ⟨g, hg, h1, h2, h3⟩ ⟨g', hg', h1', h2', h3'⟩
    refine ⟨g + g', Submodule.add_mem _ hg hg', fun a x => ?_, fun k hk => ?_, ?_⟩
    · convert Submodule.add_mem _ (h1 a x) (h1' a x) using 1
      simp only [Pi.add_apply]; ring
    · exact Submodule.add_mem _ (h2 k hk) (h2' k hk)
    · convert Submodule.add_mem _ h3 h3' using 1
      simp only [Pi.add_apply, map_add (f := _)]; ring
  zero_mem' := ⟨0, Submodule.zero_mem _, fun _ _ => by simp, fun _ _ => by simp, by simp⟩
  smul_mem' := by
    rintro r c ⟨g, hg, h1, h2, h3⟩
    refine ⟨r • g, Submodule.smul_mem _ r hg, fun a x => ?_, fun k hk => ?_, ?_⟩
    · convert Submodule.smul_mem _ r (h1 a x) using 1
      simp only [Pi.smul_apply, Algebra.smul_def]; ring
    · exact Submodule.smul_mem _ r (h2 k hk)
    · convert Submodule.smul_mem _ r h3 using 1
      simp only [Pi.smul_apply, Algebra.smul_def, smul_eq_mul, map_mul, Algebra.algebraMap_self,
        RingHom.id_apply]; ring

def flagSub {n : ℕ} (b : Module.Basis (Fin n) F N) (i : ℕ) : Submodule F N :=
  Submodule.span F (b '' {j | (j : ℕ) < i})

def afLatT (p f : ℕ) {n : ℕ} (b : Module.Basis (Fin n) F N) (σ : MulChar F R)
    (M : Submodule R (N → C)) : Submodule R (Fin n × Fin f → R) :=
  (M ⊔ pFun R p N).comap (Fintype.linearCombination R
    fun (j : Fin n × Fin f) (x : N) => algebraMap R C ((σ ^ p ^ (j.2 : ℕ)) (b.repr x j.1)))

end GlobalTheory.CompanionTheory.Ar.GR
end
end

