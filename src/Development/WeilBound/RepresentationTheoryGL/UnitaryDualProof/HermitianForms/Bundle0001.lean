module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.GlCongr

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.AvgData
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


variable (k) in
def colEl (m N : ℕ) (h : m + 2 ≤ N) (x : Fin (m + 1) → k) : GL (Fin N) k :=
  blkAt k (m + 2) N h (unip k (m + 1) (Multiplicative.ofAdd x))


variable (k) in
def xi0 (m : ℕ) : Fin (m + 1) → k := Pi.single (Fin.last m) 1

def AvgData (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (ξ : Fin (m + 1) → k) (A : AddSubgroup (Fin (m + 1) → k)) (v : V)
    (p : AddSubgroup (Fin (m + 1) → k) × Finset (Fin (m + 1) → k)) : Prop :=
  p.1 ≤ A ∧ IsOpen (p.1 : Set (Fin (m + 1) → k)) ∧ (∀ a ∈ p.1, π (colEl k m N h a) v = v) ∧ (∀ a ∈ p.1, ψ (ξ ⬝ᵥ a) = 1) ∧
    (∀ t ∈ p.2, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ p.2 ∧ a - t ∈ p.1


open Classical in
def avg (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (ξ : Fin (m + 1) → k) (A : AddSubgroup (Fin (m + 1) → k)) (v : V) : V :=
  if hd : ∃ p, AvgData ψ h π ξ A v p then
    ((hd.choose.2.card : ℂ)⁻¹) • ∑ t ∈ hd.choose.2, (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) v
  else 0

def IsLat {m : ℕ} (A : AddSubgroup (Fin (m + 1) → k)) : Prop :=
  IsCompact (A : Set (Fin (m + 1) → k)) ∧ IsOpen (A : Set (Fin (m + 1) → k))

def IsDens (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (A₀ : AddSubgroup (Fin (m + 1) → k)) (B B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : Prop :=
  ∀ v w, ∃ A₁, IsLat A₁ ∧ A₀ ≤ A₁ ∧ ∀ A, IsLat A → A₁ ≤ A →
    B' v w = ((A₀.relIndex A : ℕ) : ℂ) * B (avg ψ h π (xi0 k m) A v) w

def IsAtom {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (B B₀ : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : Prop :=
  ∀ v w, Filter.Tendsto (fun A : {A : AddSubgroup (Fin (m + 1) → k) // IsLat A} =>
      B (avg (1 : AddChar k Circle) h π 0 A.1 v) w) Filter.atTop (nhds (B₀ v w))

end PositivityTheory.RgUd.Form
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.StepForm
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def StepForm : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m N : ℕ) (hN : m + 2 ≤ N) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ (s : ℝ) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), IsPsd B →
    Kills ψ π (m + 2) B → MirEq π (m + 1) hN s B →
    ∃ B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ, IsPsd B' ∧ Kills ψ π (m + 1) B' ∧
      (∀ v, B' v v = 0 → v ∈ twKer π (derUnip k N (m + 1)) (lvlChar k ψ N (m + 1)) ⊔ LinearMap.ker B) ∧
      MirEq π m (by omega) (s + 1) B' ∧
      (∀ K : Subgroup (GL (Fin (m + 1)) k), IsOpen (K : Set (GL (Fin (m + 1)) k)) → ∃ C : ℝ, ∀ v,
        (∀ g ∈ K, π (blkAt k (m + 1) N (by omega) g) v = v) → (B' v v).re ≤ C * (B v v).re) ∧
      ∀ z : kˣ, nabs k z < 1 → ∀ v, Summable fun i : ℕ =>
        nabs k z ^ (-((i : ℝ) * (m + 1) * s)) *
          (B' (π (scalAt k (m + 1) N (by omega) (z ^ i)) v) (π (scalAt k (m + 1) N (by omega) (z ^ i)) v)).re

def AsmForm : Prop := StepForm k → PositivityTheory.RgUd.BesselSum k

end PositivityTheory.RgUd.Form
end
end

