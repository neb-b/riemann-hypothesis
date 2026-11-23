module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.SafeUGap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.IsAutQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CongruenceNumberRankThree
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.GalOfCusp
open scoped Matrix

namespace UpperTheory.V.Af

section admitted

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def AttR [IsTotallyReal F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) (π : TR.CuspSub F n) : Prop :=
  AttachedSys ι r π.HasSat

def IsAutR [IsTotallyReal F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ π : TR.CuspSub F n, π.IsRegAlg ∧ AttR ι r π

def DualTw {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin n) k) (θ : Γ →* kˣ) : Prop :=
  ∃ P : GL (Fin n) k, ∀ s, (r s : Matrix (Fin n) (Fin n) k)ᵀ * (P : Matrix (Fin n) (Fin n) k) * (r s : Matrix (Fin n) (Fin n) k) =
    (θ s : k) • (P : Matrix (Fin n) (Fin n) k)


omit [NumberField F] in
variable (l) in
def IsCycWt (wt : ℤ) (θ : G F Ω →* (Qbar l)ˣ) : Prop :=
  ∃ (M : ℕ) (χ : G F Ω →* (Qbar l)ˣ), 1 ≤ M ∧ KillsMu M χ ∧ θ = cycBar F Ω l ^ wt * χ


variable (l) in
structure LevelO (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop extends Level l M m r where
  odd : Odd n

structure AdmK [IsCMField F] (ι : Qbar l ≃+* ℂ) (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop where
  irr : IsIrr r
  aut : IsAutCsd ι r
  level : LevelO l M m r

structure AdmR [IsTotallyReal F] (ι : Qbar l ≃+* ℂ) (M : ℕ) (m : Fin n → ℤ) (wt : ℤ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop where
  irr : IsIrr r
  aut : IsAutQ ι r
  level : Level l M m r
  dual : ∃ θ, IsCycWt l wt θ ∧ DualTw r θ
  safe : Keep.SafeU l M m r

end admitted

structure EigData (n q : ℕ) (m : Fin n → ℤ) (wt : ℤ) where

  S : Type
  fin : Finite S

  β : S → Multiset ℂ
  card : ∀ s, (β s).card = n
  conj : ∀ σ : ℂ ≃+* ℂ, ∃ e : S ≃ S, ∀ s, β (e s) = (β s).map σ
  pure : ∀ s, ∀ b ∈ β s, ‖b‖ = (q : ℝ) ^ ((wt : ℝ) / 2)
  int : ∀ a : ℤ, (∀ i, -a ≤ m i) → ∀ s, ∀ b ∈ β s, IsIntegral ℤ ((q : ℂ) ^ a * b)
  intInv : ∀ a : ℤ, (∀ i, m i ≤ a) → ∀ s, ∀ b ∈ β s, IsIntegral ℤ ((q : ℂ) ^ a * b⁻¹)

def EigData.Classifies {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n q : ℕ}
    {m : Fin n → ℤ} {wt : ℤ} (D : EigData n q m wt) (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F))
    (admitted : (G F Ω →* GL (Fin n) (Qbar l)) → Prop) : Prop :=
  ∃ cl : {r // admitted r} → D.S, (∀ r r', cl r = cl r' → RepIso r.1 r'.1) ∧
    ∀ r, FrobEig ι r.1 w ((D.β (cl r)).map (·⁻¹))

def CountK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
    ∀ (m : Fin n → ℤ), StrictAnti m → (∀ i, m i + m i.rev = 1 - n) → ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ M → ¬ (p : ℤ) ∣ discr K →
      ∃ D : EigData n (normV w) m (1 - n), Nat.card D.S ≤ c * (M * (H + 1)) ^ A ∧
        ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ),
          D.Classifies (Ω := Ω) ι w (AdmK ι M m)

def CountQ : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
    ∀ (m : Fin n → ℤ) (wt : ℤ), StrictAnti m → (∀ i, m i + m i.rev = wt) → ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 ℚ)), p.Prime → (p : 𝓞 ℚ) ∈ w.asIdeal → ¬ p ∣ M →
      ∃ D : EigData n p m wt, Nat.card D.S ≤ c * (M * (H + 1)) ^ A ∧
        ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ),
          D.Classifies (Ω := Ω) ι w (AdmR ι M m wt)

def NewformAutR : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (f : Newform k) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (j : ℤ), f.Att ι (tw W (cycBar ℚ Ω l ^ j)) → IsAutR ι W

section U3

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
  {l : ℕ} [Fact l.Prime]

structure Adm3 [IsCMField K] (ι : Qbar l ≃+* ℂ) (e N : ℕ) (ρ : G K Ω →* GL (Fin 3) (Qbar l)) : Prop where
  irr : IsIrr ρ
  aut : IsAutCsd ι (tw ρ (cycBar K Ω l)⁻¹)
  level : Level l N ![(e : ℤ), 0, -(e : ℤ)] ρ

def Adm2 (ι : Qbar l ≃+* ℂ) (e M : ℕ) (ρ : G K Ω →* GL (Fin 3) (Qbar l)) : Prop :=
  ∃ W : G ℚ Ω →* GL (Fin 2) (Qbar l), IsIrr W ∧ (∃ f : Newform (2 * e + 1), f.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧
    Level l M ![(e : ℤ), -(e : ℤ)] W ∧ IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W) ∧
    ∃ g : GL (Fin 3) (Qbar l), ∀ s : G K Ω, ((g * ρ s * g⁻¹ : GL (Fin 3) (Qbar l)) : Matrix (Fin 3) (Fin 3) (Qbar l)) =
      !![W (s.restrictScalars ℚ) 0 0, 0, W (s.restrictScalars ℚ) 0 1; 0, 1, 0;
         W (s.restrictScalars ℚ) 1 0, 0, W (s.restrictScalars ℚ) 1 1]

end U3

def eis3 (q e : ℕ) (z : ℂ) : ℂ := ((q : ℂ) ^ e)⁻¹ * z + 1 + (q : ℂ) ^ e * z⁻¹

def eis4 (p e : ℕ) (z₁ z₂ z₃ : ℂ) : ℂ := (p : ℂ) ^ (e + 1) * z₁ + (p : ℂ) ^ e * z₂ + (p : ℂ) * z₃ + 1

def NumberSp4 : Prop :=
  ∃ c A : ℕ, ∀ e : ℕ, 2 ≤ e → ∀ M : ℕ, 1 ≤ M → ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 ℚ)), p.Prime → (p : 𝓞 ℚ) ∈ w.asIdeal →
    5 ≤ p → ¬ p ∣ M → ∀ k : ℕ, 0 < k → ∀ z₁ z₂ z₃ : ℂ, z₁ ^ k = 1 → z₂ ^ k = 1 → z₃ ^ k = 1 →
    ∃ NN : ℤ, NN ≠ 0 ∧ Real.log |(NN : ℝ)| ≤ c * Nat.totient k * ((M : ℝ) * (e + 1)) ^ A * Real.log p ∧
      ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ)
        (B : ValuationSubring Ω), IsPlaceOver B w → ∀ σ : G ℚ Ω, IsFrob B p σ →
        ∀ X : Finset (G ℚ Ω →* GL (Fin 4) (Qbar l)),
          (∀ r ∈ X, AdmR ι M ![(e : ℤ) + 1, e, 1, 0] (e + 1) r) → (∀ r ∈ X, ∀ r' ∈ X, RepIso r r' → r = r') →
          (∀ r ∈ X, (r σ : Matrix (Fin 4) (Fin 4) (Qbar l)).trace ≠ ι.symm (eis4 p e z₁ z₂ z₃)) ∧
          ‖((NN : ℤ) : Qbar l)‖ ≤ ∏ r ∈ X, ‖(r σ : Matrix (Fin 4) (Fin 4) (Qbar l)).trace - ι.symm (eis4 p e z₁ z₂ z₃)‖

section Ad

variable {F₀ F Ω : Type} [Field F₀] [Field F] [Field Ω] [Algebra F₀ F] [Algebra F₀ Ω] [Algebra F Ω] [IsScalarTower F₀ F Ω]
  {k : Type} [Field k] {n : ℕ}

def IsAdOf (r : G F Ω →* GL (Fin n) k) (μ : G F Ω →* kˣ) (ρ : Representation k (G F₀ Ω) (Matrix (Fin n) (Fin n) k)) : Prop :=
  ∃ (c : G F₀ Ω) (P : GL (Fin n) k), (∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)) ∧
    (∀ s s' : G F Ω, s'.restrictScalars F₀ = c * s.restrictScalars F₀ * c⁻¹ →
      (r s : Matrix (Fin n) (Fin n) k)ᵀ * (P : Matrix (Fin n) (Fin n) k) * (r s' : Matrix (Fin n) (Fin n) k) =
        (μ s : k) • (P : Matrix (Fin n) (Fin n) k)) ∧
    (∀ (s : G F Ω) (X : Matrix (Fin n) (Fin n) k), ρ (s.restrictScalars F₀) X =
      (r s : Matrix (Fin n) (Fin n) k) * X * ((r s)⁻¹ : GL (Fin n) k)) ∧
    ∀ X : Matrix (Fin n) (Fin n) k, ρ c X = -((P⁻¹ : GL (Fin n) k) * Xᵀ * (P : Matrix (Fin n) (Fin n) k))

end Ad

def AdVanishK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 2 ≤ n →
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω]
      (ι : Qbar l ≃+* ℂ) (r : G K Ω →* GL (Fin n) (Qbar l)), Continuous r → IsAutCsd ι r →
      IsIrr (r.comp (cycBar K Ω l).ker.subtype) →
      ∀ ρ : Representation (Qbar l) (G ℚ Ω) (Matrix (Fin n) (Fin n) (Qbar l)),
        IsAdOf r (cycBar K Ω l ^ (1 - (n : ℤ))) ρ → BlochKatoSelmerVanishes l ρ

def AdVanishQ : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 2 ≤ n →
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω]
      (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (wt : ℤ) (θ : G ℚ Ω →* (Qbar l)ˣ), Continuous r → IsAutQ ι r →
      IsCycWt l wt θ → DualTw r θ →
      IsIrr ((r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)).comp (cycBar K Ω l).ker.subtype) →
      ∀ ρ : Representation (Qbar l) (G ℚ Ω) (Matrix (Fin n) (Fin n) (Qbar l)),
        IsAdOf (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) (θ.comp (AlgEquiv.restrictScalarsHom ℚ)) ρ →
        BlochKatoSelmerVanishes l ρ

end UpperTheory.V.Af
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ConjSep
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.LFun

namespace UpperTheory.V.Af

section Sep

variable {G H V V' V'' : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup V''] [Module ℂ V'']

def Sep (σ : ℂ ≃+* ℂ) (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') : Prop :=
  ∀ x : V, x ≠ 0 → ∃ p : V →+ V', (∀ (c : ℂ) v, p (c • v) = σ c • p v) ∧ (∀ g v, p (ρ g v) = ρ' g (p v)) ∧ p x ≠ 0

variable {σ σ' : ℂ ≃+* ℂ} {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'} {ρ'' : Representation ℂ G V''}

theorem Sep.trans (h : Sep σ ρ ρ') (h' : Sep σ' ρ' ρ'') : Sep (σ.trans σ') ρ ρ'' := fun x hx => by
  obtain ⟨p, h1, h2, h3⟩ := h x hx
  obtain ⟨q, k1, k2, k3⟩ := h' _ h3
  exact ⟨q.comp p, fun c v => by simp [h1, k1], fun g v => by simp [h2, k2], k3⟩

theorem Sep.comp (h : Sep σ ρ ρ') (e : H →* G) : Sep σ (ρ.comp e) (ρ'.comp e) := fun x hx => by
  obtain ⟨p, h1, h2, h3⟩ := h x hx
  exact ⟨p, h1, fun g v => h2 _ v, h3⟩

theorem Sep.of_injective (f : V →ₗ[ℂ] V') (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (hi : Function.Injective f) :
    Sep (RingEquiv.refl ℂ) ρ ρ' := fun x hx =>
  ⟨f.toAddMonoidHom, fun c v => map_smul f c v, hf, (map_ne_zero_iff f hi).2 hx⟩

theorem Sep.of_equiv (T : V ≃ₗ[ℂ] V') (hT : ∀ g v, T (ρ g v) = ρ' g (T v)) :
    Sep (RingEquiv.refl ℂ) ρ ρ' ∧ Sep (RingEquiv.refl ℂ) ρ' ρ :=
  ⟨.of_injective T.toLinearMap hT T.injective, .of_injective T.symm.toLinearMap (fun g v => T.injective (by
    change T (T.symm _) = T (ρ g (T.symm v))
    rw [hT, T.apply_symm_apply, T.apply_symm_apply])) T.symm.injective⟩

theorem Sep.of_irred (hρ : ρ.IsIrreducible) (f : V →ₗ[ℂ] V') (h0 : f ≠ 0) (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) :
    Sep (RingEquiv.refl ℂ) ρ ρ' := by
  refine .of_injective f hf (LinearMap.ker_eq_bot.1 ?_)
  refine (((isIrreducible_iff ρ).1 hρ).2 (LinearMap.ker f) fun g v hv => ?_).resolve_right
    fun e => h0 (LinearMap.ker_eq_top.1 e)
  rw [LinearMap.mem_ker, hf, LinearMap.mem_ker.1 hv, map_zero]

private theorem exists_sep_module {R M S ι : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup S] [Module R S]
    [IsSimpleModule R S] (Φ : (ι →₀ S) →ₗ[R] M) (hs : Function.Surjective Φ) (x : M) (hx : x ≠ 0) :
    ∃ p : M →ₗ[R] S, p x ≠ 0 := by
  obtain ⟨s, hs'⟩ := IsSemisimpleModule.lifting_property Φ hs (LinearMap.id : M →ₗ[R] M)
  have h0 : s x ≠ 0 := fun e => hx (by rw [← LinearMap.id_apply (R := R) x, ← hs', LinearMap.comp_apply, e, map_zero])
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 h0
  exact ⟨Finsupp.lapply i ∘ₗ s, hi⟩

theorem Sep.of_isotypic (hρ : ρ'.IsIrreducible)
    (h : ⨆ f : {f : V' →ₗ[ℂ] V // ∀ g v, f (ρ' g v) = ρ g (f v)}, LinearMap.range f.1 = ⊤) :
    Sep (RingEquiv.refl ℂ) ρ ρ' := by
  classical
  intro x hx
  let F : {f : V' →ₗ[ℂ] V // ∀ g v, f (ρ' g v) = ρ g (f v)} → ρ'.asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule := fun f =>
    Representation.IntertwiningMap.equivLinearMapAsModule ρ' ρ ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩
  let Φ := Finsupp.lsum ℕ F
  have hs : Function.Surjective Φ := fun y => by
    have hy : (y : V) ∈ ⨆ f : {f : V' →ₗ[ℂ] V // ∀ g v, f (ρ' g v) = ρ g (f v)}, LinearMap.range f.1 := by
      rw [h]; exact @Submodule.mem_top _ V _ _ _ y
    refine Submodule.iSup_induction _ (motive := fun y : V => ∃ z, Φ z = y) hy ?_ ⟨0, map_zero Φ⟩ ?_
    · rintro f _ ⟨v, rfl⟩
      exact ⟨Finsupp.single f v, Finsupp.lsum_single _ _ _ _⟩
    · rintro _ _ ⟨z, rfl⟩ ⟨z', rfl⟩
      exact ⟨z + z', map_add Φ z z'⟩
  obtain ⟨p, hp⟩ := exists_sep_module Φ hs x hx
  let q := (Representation.IntertwiningMap.equivLinearMapAsModule ρ ρ').symm p
  exact ⟨q.toLinearMap.toAddMonoidHom, fun c v => map_smul q.toLinearMap c v, fun g v => q.isIntertwining _ _ g v, hp⟩

theorem Sep.hasFixed (h : Sep σ ρ ρ') {U : Subgroup G} (hU : HasFixed ρ U) : HasFixed ρ' U := by
  obtain ⟨x, hx, hU⟩ := hU
  obtain ⟨p, -, h2, h3⟩ := h x hx
  exact ⟨p x, h3, fun u hu => by rw [← h2, hU u hu]⟩

end Sep

theorem IsConjBy.sep {E : Type} [Field E] [NumberField E] {a : ℕ} {σ : ℂ ≃+* ℂ} {τ τ' : SmIrr (GL (Fin a) (Af E))}
    (h : IsConjBy σ τ τ') : Sep σ τ.ρ τ'.ρ ∧ Sep σ.symm τ'.ρ τ.ρ := by
  obtain ⟨T, h1, h2⟩ := h
  refine ⟨fun x hx => ⟨T.toAddMonoidHom, h1, h2, (map_ne_zero_iff T T.injective).2 hx⟩,
    fun x hx => ⟨T.symm.toAddMonoidHom, fun c v => T.injective ?_, fun g v => T.injective ?_,
      (map_ne_zero_iff T.symm T.symm.injective).2 hx⟩⟩
  · change T (T.symm _) = T (_ • T.symm v)
    rw [h1]; simp
  · change T (T.symm _) = T (τ.ρ g (T.symm v))
    rw [h2]; simp

section Sat

private theorem algSat_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat]

theorem satEig_eq_algSat {q : ℕ} (hq : q ≠ 0) (n : ℕ) (B : Multiset ℂˣ) (j : ℕ) :
    satEig q n B j = ((q : ℂ) ^ j.choose 2)⁻¹ * (algSat n q B).esymm j := by
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have e : algSat n q B = (B.map fun b : ℂˣ => (b : ℂ)).map fun x => ((q : ℂ) ^ (((n : ℂ) - 1) / 2)) • x := by
    rw [algSat, Multiset.map_map, Complex.ofReal_cpow (Nat.cast_nonneg q)]
    simp
  rw [e, ← Multiset.pow_smul_esymm, satEig, smul_eq_mul, ← mul_assoc, ← Complex.cpow_nat_mul, ← Complex.cpow_natCast,
    ← Complex.cpow_neg, ← Complex.cpow_add _ _ hq', Nat.cast_choose_two]
  congr 2
  ring

theorem esymm_map_ringEquiv (σ : ℂ ≃+* ℂ) (A : Multiset ℂ) (j : ℕ) : (A.map σ).esymm j = σ (A.esymm j) := by
  simp only [Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map, map_multiset_sum, Function.comp_def,
    map_multiset_prod]

theorem satEig_conj {q : ℕ} (hq : q ≠ 0) {n : ℕ} {σ : ℂ ≃+* ℂ} {B B' : Multiset ℂˣ}
    (h : algSat n q B' = (algSat n q B).map σ) (j : ℕ) : satEig q n B' j = σ (satEig q n B j) := by
  rw [satEig_eq_algSat hq, satEig_eq_algSat hq, h, esymm_map_ringEquiv, map_mul, map_inv₀, map_pow, map_natCast]

theorem exists_algSat_conj {q : ℕ} (hq : q ≠ 0) (n : ℕ) (σ : ℂ ≃+* ℂ) (B : Multiset ℂˣ) :
    ∃ B' : Multiset ℂˣ, algSat n q B' = (algSat n q B).map σ := by
  have h0 : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (by positivity) _).ne'
  refine ⟨B.map fun α => (Units.mk0 _ h0)⁻¹ * Units.map σ.toMonoidHom (Units.mk0 _ h0 * α), ?_⟩
  simp only [algSat_eq, Multiset.map_map]
  refine Multiset.map_congr rfl fun α _ => ?_
  simp [h0]

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
  {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {ρ' : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V'}

private theorem map_heckeTj {σ : ℂ ≃+* ℂ} (p : V →+ V') (h1 : ∀ (c : ℂ) v, p (c • v) = σ c • p v)
    (h2 : ∀ g v, p (ρ g v) = ρ' g (p v)) {ϖ : w.adicCompletion E} (hϖ : Formalism.UG.IsUnifV E w ϖ) (j : ℕ) (x : V) :
    p (heckeVec ρ (KGL w (n := n)) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j) x) =
      heckeVec ρ' (KGL w (n := n)) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j) (p x) := by
  refine (p.map_finsum (finite_heckeVec (Formalism.UG.Final.GLintComm E w n) (Tj_mem_hecke hϖ j) ρ x)).trans
    (finsum_congr fun c => ?_)
  rw [h1, h2]
  congr 1
  simp only [Formalism.UG.Tj, Formalism.UG.dosetInd, Set.indicator]
  split_ifs <;> simp

theorem Sep.hasSatGL {σ : ℂ ≃+* ℂ} (h : Sep σ ρ ρ') (h' : Sep σ.symm ρ' ρ) {B B' : Multiset ℂˣ} (hB : HasSatGL w ρ B)
    (e : algSat n (normV w) B' = (algSat n (normV w) B).map σ) : HasSatGL w ρ' B' := by
  have hc : B'.card = n := by simpa [algSat, hB.card] using congrArg Multiset.card e
  constructor
  · obtain ⟨x, hx⟩ := hB.exists_vec
    obtain ⟨y, h0, hy⟩ := h.hasFixed ⟨x, hx.1, GlobalTheory.LGrp.mem_fixed.1 hx.2.1⟩
    exact (Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.LGrp.mem_fixed.2 hy, h0⟩
  · refine fun y hy h0 => ⟨h0, hy, hc, fun ϖ hϖ j hj => ?_⟩
    by_contra hne
    obtain ⟨p, h1, h2, h3⟩ := h' _ (sub_ne_zero.2 hne)
    refine h3 ?_
    have hq : Formalism.UG.qV E w = normV w := by
      simp [normV, Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have e2 : satEig (Formalism.UG.qV E w) n B' j = σ (satEig (Formalism.UG.qV E w) n B j) :=
      satEig_conj (qV_ne_zero w) (by rw [hq]; exact e) j
    rw [map_sub, map_heckeTj p h1 h2 hϖ, h1, e2, σ.symm_apply_apply, sub_eq_zero]
    by_cases hp : p y = 0
    · simp [hp, heckeVec]
    · exact (hB.2 _ (GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [← h2, GlobalTheory.LGrp.mem_fixed.1 hy k hk]) hp).2.2.2 ϖ hϖ j hj

theorem Sep.exists_hasSatGL {σ : ℂ ≃+* ℂ} (h : Sep σ ρ ρ') (h' : Sep σ.symm ρ' ρ) {B : Multiset ℂˣ} (hB : HasSatGL w ρ B) :
    ∃ B', HasSatGL w ρ' B' ∧ algSat n (normV w) B' = (algSat n (normV w) B).map σ := by
  have hq : Formalism.UG.qV E w = normV w := by
    simp [normV, Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  obtain ⟨B', e⟩ := exists_algSat_conj (q := normV w) (hq ▸ qV_ne_zero w) n σ B
  exact ⟨B', h.hasSatGL h' hB e, e⟩

theorem Sep.hasSatGL_refl (h : Sep (RingEquiv.refl ℂ) ρ ρ') (h' : Sep (RingEquiv.refl ℂ) ρ' ρ) {B : Multiset ℂˣ}
    (hB : HasSatGL w ρ B) : HasSatGL w ρ' B := h.hasSatGL h' hB (by simp)

end Sat

section Fin

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem act_fin_comm (k : GL (Fin a) (Af E)) (o : Op E a) (ho : ∀ k', o ≠ .fin k') :
    act o * act (.fin k) = act (.fin k) * act o := by
  cases o with
  | fin k' => exact (ho k' rfl).elim
  | cpt u =>
    change rt E a _ * rt E a _ = rt E a _ * rt E a _
    rw [← map_mul, ← map_mul]
    exact congrArg _ (infGL_comm _ _)
  | lie X => exact lie_rt_fin X k

theorem IsFinComp.iSup_range {π : CuspSub E a} {τ : SmIrr (GL (Fin a) (Af E))} (h : IsFinComp π τ) :
    ⨆ f : {f : τ.V →ₗ[ℂ] π.V // ∀ g v, f (τ.ρ g v) = π.finPart g (f v)}, LinearMap.range f.1 = ⊤ := by
  obtain ⟨f, h0, hf⟩ := h
  set W := ⨆ f : {f : τ.V →ₗ[ℂ] π.V // ∀ g v, f (τ.ρ g v) = π.finPart g (f v)}, LinearMap.range f.1 with hW
  have hs : ∀ o, W ≤ W.comap (π.op o) := fun o => iSup_le fun f => by
    rintro _ ⟨v, rfl⟩
    by_cases ho : ∀ k', o ≠ .fin k'
    · exact Submodule.mem_iSup_of_mem ⟨π.op o ∘ₗ f.1, fun g v => by
        rw [LinearMap.comp_apply, f.2]
        exact Subtype.ext (LinearMap.congr_fun (act_fin_comm g o ho) (f.1 v).1)⟩ ⟨v, rfl⟩
    · push Not at ho
      obtain ⟨k, rfl⟩ := ho
      exact Submodule.mem_iSup_of_mem f ⟨τ.ρ k v, f.2 k v⟩
  rcases π.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hs o hx, rfl⟩) with e | e
  · refine (h0 (LinearMap.range_eq_bot.1 (le_bot_iff.1 ?_))).elim
    rw [← Submodule.map_bot π.V.subtype] at e
    rw [← Submodule.map_injective_of_injective π.V.subtype_injective e]
    exact le_iSup (fun f : {f : τ.V →ₗ[ℂ] π.V // ∀ g v, f (τ.ρ g v) = π.finPart g (f v)} => LinearMap.range f.1) ⟨f, hf⟩
  · exact Submodule.map_injective_of_injective π.V.subtype_injective (e.trans (Submodule.map_subtype_top _).symm)

theorem IsFinComp.sep {π : CuspSub E a} {τ : SmIrr (GL (Fin a) (Af E))} (h : IsFinComp π τ) :
    Sep (RingEquiv.refl ℂ) π.finPart τ.ρ ∧ Sep (RingEquiv.refl ℂ) τ.ρ π.finPart :=
  ⟨.of_isotypic τ.irred h.iSup_range, by
    obtain ⟨f, h0, hf⟩ := h
    exact .of_irred τ.irred f h0 hf⟩

theorem sep_of_conj {π π' : CuspSub E a} {τ τ' : SmIrr (GL (Fin a) (Af E))} {σ : ℂ ≃+* ℂ} (h : IsFinComp π τ)
    (h' : IsFinComp π' τ') (hc : IsConjBy σ τ τ') : Sep σ π.finPart π'.finPart ∧ Sep σ.symm π'.finPart π.finPart :=
  ⟨(h.sep.1.trans hc.sep.1).trans h'.sep.2, (h'.sep.1.trans hc.sep.2).trans h.sep.2⟩

end Fin

end UpperTheory.V.Af
end
end

