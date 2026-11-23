module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FiniteRankZero
section
noncomputable section

open NumberField GlobalTheory.CuspRep Formalism.L2.Host

namespace GlobalTheory.Published.AutFinGL.Model

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def kerL (a : ℕ) (χ : HChar E) : Subgroup (GL (Fin a) (Af E)) := ((chiDet a χ).comp (finGL E a)).ker

theorem isOpen_kerL (χ : HChar E) : IsOpen (kerL a χ : Set (GL (Fin a) (Af E))) := isOpen_ker_chiDet χ

end GlobalTheory.Published.AutFinGL.Model

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.Whittaker

namespace GlobalTheory.LocLanglands

section Tate

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


variable (k) in
def unitFilt (a : ℕ) : Set kˣ :=
  {x | valuation k (x : k) = 1 ∧ valuation k ((x : k) - 1) ≤ uniformizer k ^ a}

def HasExponent (χ : kˣ →* ℂˣ) (a : ℕ) : Prop :=
  (∀ x ∈ unitFilt k a, χ x = 1) ∧ ∀ b < a, ∃ x ∈ unitFilt k b, χ x ≠ 1

def IsShellReps (c : kˣ) (a : ℕ) (R : Finset kˣ) : Prop :=
  (∀ r ∈ R, ord k r = ord k c - a) ∧
    ∀ y : kˣ, ord k y = ord k c - a → ∃! r : kˣ, r ∈ R ∧ valuation k ((y : k) - r) ≤ valuation k (c : k)

def IsTateEps (ψ : AddChar k Circle) (χ : kˣ →* ℂˣ) (e : ℂ) : Prop :=
  ∃ (c : kˣ) (a : ℕ) (R : Finset kˣ), HasConductor ψ c ∧ HasExponent χ a ∧ IsShellReps c a R ∧
    e = (resCard k : ℂ) ^ (-(a : ℂ) / 2) * ∑ r ∈ R, (((χ r)⁻¹ : ℂˣ) : ℂ) * (ψ (r : k) : ℂ)

theorem HasExponent.unique {χ : kˣ →* ℂˣ} {a b : ℕ} (ha : HasExponent χ a) (hb : HasExponent χ b) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · obtain ⟨x, hx, hx'⟩ := hb.2 a h
    exact absurd (ha.1 x hx) hx'
  · exact h
  · obtain ⟨x, hx, hx'⟩ := ha.2 b h
    exact absurd (hb.1 x hx) hx'

end Tate

section Pairs

theorem antidiag_mul_self (n : ℕ) (R : Type) [CommRing R] :
    (Matrix.of fun i j : Fin n => if j = i.rev then (1 : R) else 0) *
      (Matrix.of fun i j : Fin n => if j = i.rev then (1 : R) else 0) = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev (fun b _ hb => by simp [hb]) (by simp)]
  simp [Matrix.one_apply, eq_comm]

def longElt (n : ℕ) (R : Type) [CommRing R] : GL (Fin n) R :=
  ⟨Matrix.of fun i j => if j = i.rev then 1 else 0, Matrix.of fun i j => if j = i.rev then 1 else 0,
    antidiag_mul_self n R, antidiag_mul_self n R⟩

def tilde {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) : GL (Fin n) R :=
  longElt n R * GlobalTheory.CuspRep.invT n R g

def corner {m : ℕ} {R : Type} [CommRing R] (g : GL (Fin m) R) : GL (Fin (m + 1)) R :=
  emb₂ R (stdSum (rfl : m + 1 = m + 1)) (g, 1)

variable {k : Type} [Field k] [TopologicalSpace k] {m : ℕ}

def IsTestFun (f : GL (Fin m) k → ℂ) : Prop :=
  (∀ u ∈ unipB k (Fin m), ∀ g, f (u * g) = f g) ∧ IsLocallyConstant f ∧
    ∃ C : Set (GL (Fin m) k), IsCompact C ∧ ∀ g, f g ≠ 0 → ∃ u ∈ unipB k (Fin m), ∃ c ∈ C, g = u * c

def IsInvIntegral (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ f, IsTestFun f → ∀ x, I (fun g => f (g * x)) = I f

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

def HasPairEps (ψ : AddChar k Circle) (π : Representation ℂ (GL (Fin (m + 1)) k) V)
    (τ : Representation ℂ (GL (Fin m) k) V') (e : ℂ) : Prop :=
  ∀ ω : kˣ →* ℂˣ, HasCentralChar τ ω →
    ∀ (l : Module.Dual ℂ V) (l' : Module.Dual ℂ V'), IsFunctional ψ π l → IsFunctional ψ⁻¹ τ l' →
      ∀ I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ, IsInvIntegral I → ∀ (v : V) (v' : V'),
        I (fun g => l (π (tilde (corner g)) v) * l' (τ (tilde g) v')) =
          (ω (-1) : ℂ) ^ m * e * I (fun g => l (π (corner g) v) * l' (τ g v'))

end Pairs

section Galois

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.HeckeGal ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}

structure IsLocalArtin {E : Type} [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω]
    {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) : Prop where
  surj : Function.Surjective a
  cont : Continuous fun σ : Ine (F := E) A => a (ineIncl h σ)
  ord_eq : ∀ σ, ord (w.adicCompletion E) (a σ) = -deg σ
  factor : ∀ ξ : Weil h →* ℂˣ, WeilDeligne.IsSmooth ξ → ∃ χ, IsSmoothChar χ ∧ ξ = χ.comp a
  glob : ∀ art : Ideles E →* Gab E Ω, IsGlobalArtin art →
    ∀ σ : Weil h, art (localIdele E w (a σ)) = toAb E Ω σ

theorem IsLocalArtin.smooth {E : Type} [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω]
    {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion E)ˣ}
    (ha : IsLocalArtin h a) {χ : (w.adicCompletion E)ˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    WeilDeligne.IsSmooth (χ.comp a) :=
  IsOpen.preimage ha.cont hχ

section Ind

variable {K L : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}


variable (L) in
def IsLocalExt (h : IsPlaceOver A v) : Prop :=
  ∀ σ : G K Ω, ∃ τ : Weil h, ∀ x : L, (τ : G K Ω) (algebraMap L Ω x) = σ (algebraMap L Ω x)

def Induces {h' : IsPlaceOver A v'} {h : IsPlaceOver A v} (x : WD h') (y : WD h) : Prop :=
  ∃ (m n : ℕ) (a : WDRep h' (Fin m → ℂ)) (b : WDRep h (Fin n → ℂ)) (j : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ)),
    WD.mk a = x ∧ WD.mk b = y ∧ n = Module.finrank K L * m ∧
    (∀ (σ' : Weil h') (σ : Weil h), (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) → ∀ u, j (a.ρ σ' u) = b.ρ σ (j u)) ∧
    Submodule.span ℂ (Set.range fun p : Weil h × (Fin m → ℂ) => b.ρ p.1 (j p.2)) = ⊤


omit [IsAlgClosure K Ω] in
theorem isLocalExt_self (h : IsPlaceOver A v) : IsLocalExt K h := fun σ => ⟨1, fun x => by simp⟩

theorem induces_self {h : IsPlaceOver A v} (x : WD h) : Induces x x := by
  obtain ⟨n, a, rfl⟩ := x.exists_rep
  refine ⟨n, n, a, a, LinearMap.id, rfl, rfl, by simp, fun σ' σ hσ u => ?_, ?_⟩
  · rw [show σ = σ' from Subtype.ext (AlgEquiv.ext hσ)]; rfl
  · exact eq_top_iff.2 fun u _ => Submodule.subset_span ⟨(1, u), by simp⟩

end Ind


variable (A) in
abbrev EpsFamily : Type 1 :=
  ∀ (L : Type) [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] (v : HeightOneSpectrum (𝓞 L))
    (h : IsPlaceOver A v), AddChar (v.adicCompletion L) Circle → WD h → ℂˣ

structure IsDeligneEps (ε : EpsFamily A) : Prop where
  add : ∀ (L : Type) [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] (v : HeightOneSpectrum (𝓞 L))
    (h : IsPlaceOver A v) (ψ : AddChar (v.adicCompletion L) Circle), Continuous ψ → ψ ≠ 1 →
    ∀ x y : WD h, ε L v h ψ (x.lpSum y) = ε L v h ψ x * ε L v h ψ y
  char : ∀ (L : Type) [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] (v : HeightOneSpectrum (𝓞 L))
    (h : IsPlaceOver A v) (ψ : AddChar (v.adicCompletion L) Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (a : Weil h →* (v.adicCompletion L)ˣ) (ha : IsLocalArtin h a) (χ : (v.adicCompletion L)ˣ →* ℂˣ)
      (hχ : IsSmoothChar χ), IsTateEps ψ χ (ε L v h ψ (WD.lpOfChar h (χ.comp a) (ha.smooth hχ)))
  ind : ∀ (K L : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]
    (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v'),
    IsLocalExt L h →
    ∀ (ψ : AddChar (v.adicCompletion K) Circle) (ψ' : AddChar (v'.adicCompletion L) Circle),
      Continuous ψ → ψ ≠ 1 → Continuous ψ' →
      (∀ z : L, ψ' (algebraMap L _ z) = ψ (algebraMap K _ (Algebra.trace K L z))) →
      ∀ (x₁ x₂ : WD h') (y₁ y₂ : WD h), Induces x₁ y₁ → Induces x₂ y₂ → x₁.lpDim = x₂.lpDim →
        ε K v h ψ y₁ * ε L v' h' ψ' x₂ = ε K v h ψ y₂ * ε L v' h' ψ' x₁

end Galois

end GlobalTheory.LocLanglands
end
end

