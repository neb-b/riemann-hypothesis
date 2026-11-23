module

public import Mathlib
public import Formalism.PieriBlockIdeals.PieriColumnMinors.RowGenDerivative
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0553
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCapFBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0540

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur
section
open MvPolynomial Formalism.GradedWeylDivisibility TensorProduct

noncomputable section

namespace GlobalTheory.LeviCut

def GlRel (N : ℕ) {A : Type} [Ring A] (e : ℕ → ℕ → A) : Prop :=
  ∀ a b c d : ℕ, a < N → b < N → c < N → d < N →
    e a b * e c d - e c d * e a b = (if b = c then e a d else 0) - (if d = a then e c b else 0)

def coef (j k : ℕ) : ℚ := (-1) ^ k * (j.factorial : ℚ) / ((k.factorial : ℚ) * ((k + j + 1).factorial : ℚ))

def proj {A : Type} [Ring A] [Algebra ℚ A] (K j : ℕ) (X Y : A) : A :=
  ∑ k ∈ Finset.range (K + 1), coef j k • (Y ^ k * X ^ k)

def rootP {A : Type} [Ring A] [Algebra ℚ A] (D : ℕ → ℕ → A) (K i j : ℕ) : A :=
  proj K (j - i - 1) (D i j) (D j i)

def rowP {A : Type} [Ring A] [Algebra ℚ A] (D : ℕ → ℕ → A) (K i s n : ℕ) : A :=
  ((List.range' s n).map (rootP D K i)).prod

def gridP {A : Type} [Ring A] [Algebra ℚ A] (D : ℕ → ℕ → A) (K a b t : ℕ) : A :=
  ((List.range t).reverse.map fun i => rowP D K i a b).prod

def adj {A : Type} [Ring A] [Algebra ℚ A] (x : A) : Module.End ℚ A :=
  LinearMap.mulLeft ℚ x - LinearMap.mulRight ℚ x

def IsWt (N : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (e : ℕ → ℕ → Module.End ℚ V) (μ : ℕ → ℤ) (x : V) : Prop :=
  ∀ c < N, e c c x = (μ c : ℚ) • x

def Bdd (N K : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (e : ℕ → ℕ → Module.End ℚ V) : Prop :=
  ∀ a < N, ∀ b < N, ∀ (n : ℤ) (x : V), e a a x - e b b x = (n : ℚ) • x → (K : ℤ) < n → x = 0

def Dom (N : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (e : ℕ → ℕ → Module.End ℚ V) (lam : ℕ → ℤ) : Prop :=
  ∀ (μ : ℕ → ℤ) (x : V), IsWt N e μ x → x ≠ 0 →
    (∀ k ≤ N, ∑ c ∈ Finset.range k, μ c ≤ ∑ c ∈ Finset.range k, lam c) ∧
      ∑ c ∈ Finset.range N, μ c = ∑ c ∈ Finset.range N, lam c

def WtSpan (N : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (e : ℕ → ℕ → Module.End ℚ V) : Prop :=
  Submodule.span ℚ {x : V | ∃ μ : ℕ → ℤ, IsWt N e μ x} = ⊤

def DivStable (N : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (e : ℕ → ℕ → Module.End ℚ V)
    (L : Submodule ℤ V) : Prop :=
  ∀ i < N, ∀ j < N, i ≠ j → ∀ k : ℕ, ∀ x ∈ L, ((k.factorial : ℚ)⁻¹) • (e i j ^ k) x ∈ L

def RankOne : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℚ W] (N K : ℕ) (D : ℕ → ℕ → Module.End ℚ W), GlRel N D → Bdd N (2 * K) D →
    ∀ o q : ℕ, o < N → q < N → o ≠ q → ∀ T : W, D o o T = 0 → D q q T = 0 →
      D o q (proj K 0 (D o q) (D q o) T) = 0 ∧ (D o q T = 0 → D q o T = 0)

def RankTwo : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℚ W] (N K : ℕ) (D : ℕ → ℕ → Module.End ℚ W), GlRel N D → Bdd N (2 * K) D →
    ∀ o p q : ℕ, o < N → p < N → q < N → o ≠ p → o ≠ q → p ≠ q → ∀ (j : ℕ) (T : W),
      D o o T = 0 → D p p T = 0 → D q q T = 0 → D p q T = 0 →
      D p q (proj K j (D o p) (D p o) (proj K (j + 1) (D o q) (D q o) T)) = 0

def GridInv : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℚ W] (a b K : ℕ) (D : ℕ → ℕ → Module.End ℚ W), GlRel (a + b) D →
    Bdd (a + b) (2 * K) D → ∀ T : W, (∀ c < a + b, ∀ d < a + b, (c < a ↔ d < a) → D c d T = 0) →
      ∀ c < a + b, ∀ d < a + b, D c d (gridP D K a b a T) = 0

def AdjBdd : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] (N K : ℕ) (e : ℕ → ℕ → Module.End ℚ V), GlRel N e → Bdd N K e →
    WtSpan N e → GlRel N (fun a b => adj (e a b)) ∧ Bdd N (2 * K) (fun a b => adj (e a b))

def StepScalar : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] (E F H T : Module.End ℚ V) (v : V) (φ : V →ₗ[ℚ] ℚ) (n K j : ℕ),
    E * F - F * E = H → H * F - F * H = -(F + F) → E v = 0 → H v = (n : ℚ) • v → n ≤ K → (∀ x, φ (F x) = 0) →
    (∀ k : ℕ, 0 < k → T ((F ^ k) v) = 0) →
      φ (proj K j (adj E) (adj F) T v) * ((n : ℚ) + j + 1) = φ (T v)

def GridScalar : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] (a b K : ℕ) (e : ℕ → ℕ → Module.End ℚ V) (lam : ℕ → ℤ) (v : V)
    (φ : V →ₗ[ℚ] ℚ) (T : Module.End ℚ V), GlRel (a + b) e → Dom (a + b) e lam → IsWt (a + b) e lam v →
    (∀ i j : ℕ, i < j → j < a + b → e i j v = 0 ∧ (∀ x, φ (e j i x) = 0) ∧ lam j ≤ lam i ∧ lam i ≤ lam j + K) →
    (∀ (μ : ℕ → ℤ) (x : V), IsWt (a + b) e μ x → ∑ c ∈ Finset.range a, μ c < ∑ c ∈ Finset.range a, lam c → T x = 0) →
      φ (gridP (fun c d => adj (e c d)) K a b a T v) *
        ((∏ i ∈ Finset.range a, ∏ j ∈ Finset.Ico a (a + b), (lam i - lam j + (j : ℤ) - (i : ℤ)) : ℤ) : ℚ) = φ (T v)

def GridInt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] (a b K w Λ : ℕ) (e : ℕ → ℕ → Module.End ℚ V) (L M : Submodule ℤ V),
    DivStable (a + b) e L → DivStable (a + b) e M → K + (a + b) ≤ w + 1 →
    (∀ j k : ℕ, j + k + 1 ≤ w → (j + k + 1).factorial ∣ Λ * (j.factorial * k.factorial)) →
    ∀ (c : ℕ) (T : Module.End ℚ V), (∀ x ∈ L, (c : ℤ) • T x ∈ M) →
      ∀ x ∈ L, ((c * Λ ^ (a * b) : ℕ) : ℤ) • gridP (fun c d => adj (e c d)) K a b a T x ∈ M

def BetaDen : Prop :=
  ∀ l w : ℕ, l.Prime → ∃ m : ℕ, ¬ l ∣ m ∧
    ∀ j k : ℕ, j + k + 1 ≤ w → (j + k + 1).factorial ∣ (m * l ^ Nat.log l w) * (j.factorial * k.factorial)

def eV (N : ℕ) (ν : Fin N → ℕ) (a b : ℕ) : Module.End ℚ (dualWeyl ℚ N N ν) :=
  if h : a < N ∧ b < N then
    LinearMap.restrict (Formalism.CohomologicalDescent.LR.der N N ⟨a, h.1⟩ ⟨b, h.2⟩ : Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ))
      (fun f hf => Formalism.CohomologicalDescent.LR.der_mem ν _ _ f hf)
  else 0

def latV (N : ℕ) (ν : Fin N → ℕ) (M : Submodule ℤ (MvPolynomial (Fin N × Fin N) ℤ)) : Submodule ℤ (dualWeyl ℚ N N ν) :=
  (M.map (intQ N N)).comap ((dualWeyl ℚ N N ν).subtype.restrictScalars ℤ)

def wtZ {N : ℕ} (ν : Fin N → ℕ) (c : ℕ) : ℤ := if h : c < N then (ν ⟨c, h⟩ : ℤ) else 0

def resVarT (R : Type) [CommRing R] (p q : ℕ) (v : Fin (p + q) × Fin (p + q)) :
    MvPolynomial (Fin p × Fin p) R ⊗[R] MvPolynomial (Fin q × Fin q) R :=
  Fin.addCases (motive := fun _ => MvPolynomial (Fin p × Fin p) R ⊗[R] MvPolynomial (Fin q × Fin q) R)
    (fun a => Fin.addCases (motive := fun _ => MvPolynomial (Fin p × Fin p) R ⊗[R] MvPolynomial (Fin q × Fin q) R)
      (fun s => X (a, s) ⊗ₜ[R] 1) (fun _ => 0) v.2)
    (fun b => Fin.addCases (motive := fun _ => MvPolynomial (Fin p × Fin p) R ⊗[R] MvPolynomial (Fin q × Fin q) R)
      (fun _ => 0) (fun t => 1 ⊗ₜ[R] X (b, t)) v.2) v.1

def resT (R : Type) [CommRing R] (p q : ℕ) : MvPolynomial (Fin (p + q) × Fin (p + q)) R →ₐ[R]
    MvPolynomial (Fin p × Fin p) R ⊗[R] MvPolynomial (Fin q × Fin q) R :=
  aeval (resVarT R p q)

def NablaGl : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν →
    GlRel N (eV N ν) ∧ WtSpan N (eV N ν) ∧ Dom N (eV N ν) (wtZ ν) ∧
      DivStable N (eV N ν) (latV N ν (dualWeyl ℤ N N ν)) ∧ DivStable N (eV N ν) (latV N ν (weyl ℤ N N le_rfl ν))

def NablaBdd : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∀ K : ℕ, (∀ i j, ν i ≤ ν j + K) → Bdd N K (eV N ν)

def NablaSchur : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ) (hν : Antitone ν) (S : Module.End ℚ (dualWeyl ℚ N N ν)),
    (∀ c < N, ∀ d < N, eV N ν c d * S = S * eV N ν c d) →
    fockQ (hw ℚ le_rfl ν) (S ⟨hw ℚ le_rfl ν, hwMem ℚ N N le_rfl ν hν⟩ : dualWeyl ℚ N N ν) =
      fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) → S = 1

def SubstMem : Prop :=
  ∀ (R : Type) [CommRing R] (k N : ℕ) (τ : Fin k → Fin N), StrictMono τ →
    ∀ ψ : Fin N × Fin N → MvPolynomial (Fin k × Fin k) R,
      (∀ a s, ψ (τ a, τ s) = X (a, s)) → (∀ x s, x ∉ Set.range τ → ψ (x, τ s) = 0) →
      (∀ x y, y ∉ Set.range τ → ∃ c : R, ψ (x, y) = C c) →
      ∀ (ν : Fin N → ℕ), ∀ f ∈ dualWeyl R N N ν, aeval ψ f ∈ dualWeyl R k k (fun s => ν (τ s))

def ResLat : Prop :=
  ∀ (p q : ℕ) (ν : Fin (p + q) → ℕ), ∀ f ∈ dualWeyl ℤ (p + q) (p + q) ν,
    resT ℚ p q (intQ (p + q) (p + q) f) ∈ Submodule.span ℤ
      {z | ∃ f₁ ∈ dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i)), ∃ f₂ ∈ dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j)),
        z = intQ p p f₁ ⊗ₜ[ℚ] intQ q q f₂}

def ResHw : Prop :=
  ∀ (p q : ℕ) (ν : Fin (p + q) → ℕ), Antitone ν →
    resT ℚ p q (hw ℚ le_rfl ν) =
      hw ℚ le_rfl (fun i => ν (Fin.castAdd q i)) ⊗ₜ[ℚ] hw ℚ le_rfl (fun j => ν (Fin.natAdd p j))

def ResDer : Prop :=
  ∀ (p q : ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ),
    (∀ c d : Fin p, resT ℚ p q (Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.castAdd q c) (Fin.castAdd q d) f) =
      LinearMap.rTensor _ (Formalism.CohomologicalDescent.LR.der p p c d : Module.End ℚ (MvPolynomial (Fin p × Fin p) ℚ)) (resT ℚ p q f)) ∧
    (∀ c d : Fin q, resT ℚ p q (Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.natAdd p c) (Fin.natAdd p d) f) =
      LinearMap.lTensor _ (Formalism.CohomologicalDescent.LR.der q q c d : Module.End ℚ (MvPolynomial (Fin q × Fin q) ℚ)) (resT ℚ p q f)) ∧
    ∀ (ν : Fin (p + q) → ℕ) (t : ℚ), IsWeightedHomogeneous (colW (p + q) (p + q)) f ν →
      ∑ c : Fin p, Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.castAdd q c) (Fin.castAdd q c) f = t • f →
      t ≠ ∑ c : Fin p, (ν (Fin.castAdd q c) : ℚ) → resT ℚ p q f = 0

def LeviProj : Prop :=
  ∀ (p q : ℕ) (ν : Fin (p + q) → ℕ) (hν : Antitone ν) (c₁ c₂ : ℕ),
    (∀ x ∈ dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i)), (c₁ : ℤ) • x ∈ weyl ℤ p p le_rfl (fun i => ν (Fin.castAdd q i))) →
    (∀ x ∈ dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j)), (c₂ : ℤ) • x ∈ weyl ℤ q q le_rfl (fun j => ν (Fin.natAdd p j))) →
    ∃ T : Module.End ℚ (dualWeyl ℚ (p + q) (p + q) ν),
      (∀ c < p + q, ∀ d < p + q, (c < p ↔ d < p) → eV (p + q) ν c d * T = T * eV (p + q) ν c d) ∧
      (∀ x ∈ latV (p + q) ν (dualWeyl ℤ (p + q) (p + q) ν),
        ((c₁ * c₂ : ℕ) : ℤ) • T x ∈ latV (p + q) ν (weyl ℤ (p + q) (p + q) le_rfl ν)) ∧
      (∀ (μ : ℕ → ℤ) (x : dualWeyl ℚ (p + q) (p + q) ν), IsWt (p + q) (eV (p + q) ν) μ x →
        ∑ c ∈ Finset.range p, μ c < ∑ c ∈ Finset.range p, wtZ ν c → T x = 0) ∧
      fockQ (hw ℚ le_rfl ν) (T ⟨hw ℚ le_rfl ν, hwMem ℚ (p + q) (p + q) le_rfl ν hν⟩ : dualWeyl ℚ (p + q) (p + q) ν) =
        fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν)

end GlobalTheory.LeviCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairFstPreimageRestrictionBijectiveClosedImmersi
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

private theorem exAff (Z : Scheme.{0}) {O : Z.Opens} {z : Z} (hz : z ∈ O) :
    ∃ V : Z.affineOpens, z ∈ V.1 ∧ V.1 ≤ O := by
  obtain ⟨V, hV, hzV, hVO⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens hz
  exact ⟨⟨V, hV⟩, hzV, hVO⟩

theorem pair_pre_bijective : ∀ (R' : Type) [CommRing R'] (X Y Y' : Scheme.{0}) (ψ : Y ⟶ X) (χ : Y' ⟶ Y) [IsClosedImmersion χ] (q' : Y' ⟶ Sp R'), Function.Bijective (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull1 ∧ Function.Bijective (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull2 ∧ (CohomZeroIsConstants (OAff q') → CohomZeroIsConstants (pairFst ψ ⋙ OPre χ q')) := by
  intro R' _ X Y Y' ψ χ _ q'
  have hG : Monotone (fun p : Pair ψ ↦ preU χ p.1.1) := fun _ _ h ↦ preU_mono χ (Pair.le_fst h)
  have hF : pairFst ψ ⋙ preAff χ = hG.functor.op := rfl
  have key := _root_.GlobalTheory.AbCoh.cohO_basis_bijective R' Y' q' (Pair ψ) (fun p ↦ preU χ p.1.1) hG ?cov ?dir
  · rw [hF]
    exact key
  case cov =>
    intro U x hx
    obtain ⟨t, ht, hte⟩ := χ.isClosedEmbedding.isInducing.isOpen_iff.1 U.1.2
    have hxt : χ x ∈ (⟨t, ht⟩ : Y.Opens) := by
      show χ x ∈ t
      rw [← Set.mem_preimage, hte]; exact hx
    obtain ⟨W, hW, -⟩ := exAff X (show ψ (χ x) ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨V, hV, hVle⟩ := exAff Y (show χ x ∈ (⟨t, ht⟩ : Y.Opens) ⊓ ψ ⁻¹ᵁ W.1 from ⟨hxt, hW⟩)
    refine ⟨⟨(V, W), fun y hy ↦ (hVle hy).2⟩, hV, ?_⟩
    intro y hy
    have : χ y ∈ t := (hVle hy).1
    rw [← Set.mem_preimage, hte] at this
    exact this
  case dir =>
    intro a b x ha hb
    have hya : ψ (χ x) ∈ a.1.2.1 := a.2 ha
    have hyb : ψ (χ x) ∈ b.1.2.1 := b.2 hb
    obtain ⟨W, hW, hWle⟩ := exAff X (show ψ (χ x) ∈ a.1.2.1 ⊓ b.1.2.1 from ⟨hya, hyb⟩)
    obtain ⟨V, hV, hVle⟩ := exAff Y
      (show χ x ∈ (a.1.1.1 ⊓ b.1.1.1) ⊓ ψ ⁻¹ᵁ W.1 from ⟨⟨ha, hb⟩, hW⟩)
    refine ⟨⟨(V, W), fun y hy ↦ (hVle hy).2⟩, ?_, ?_, hV⟩
    · exact ⟨fun y hy ↦ (hVle hy).1.1, fun y hy ↦ (hWle hy).1⟩
    · exact ⟨fun y hy ↦ (hVle hy).1.2, fun y hy ↦ (hWle hy).2⟩

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerfectProjectionNaturalIdempotentReduced
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PerfectProj

theorem exists_pow_prime_pow_kill (p : ℕ) (hp : 1 < p) (k B : Type) [Field k] [CommRing B]
    [Algebra k B] [Module.Finite k B] :
    ∃ r : ℕ, ∀ x : B, IsNilpotent x → x ^ (p ^ r) = 0 := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_nilradical (R := B)
  refine ⟨n, fun x hx => ?_⟩
  have hmem : x ^ n ∈ (nilradical B) ^ n := Ideal.pow_mem_pow (mem_nilradical.mpr hx) n
  rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hmem
  exact pow_eq_zero_of_le (Nat.lt_pow_self hp).le hmem

theorem exists_eq_pow_prime_pow (p : ℕ) {A : Type} [CommRing A] (π : A → A)
    (h : ∀ a, ∃ b, π a = π b ^ p) : ∀ (m : ℕ) (a : A), ∃ b, π a = π b ^ (p ^ m) := by
  intro m
  induction m with
  | zero => intro a; exact ⟨a, by simp⟩
  | succ m ih =>
    intro a
    obtain ⟨b, hb⟩ := ih a
    obtain ⟨c, hc⟩ := h b
    exact ⟨c, by rw [hb, hc, ← pow_mul, pow_succ']⟩

theorem natural_idempotent_reduced : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (A B : Type) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [Module.Finite k B] (π : A →ₐ[k] A) (π' : B →ₐ[k] B), ((∀ a : A, IsNilpotent (a - π a)) ∧ ∀ a : A, ∃ b : A, π a = π b ^ p) → ((∀ a : B, IsNilpotent (a - π' a)) ∧ ∀ a : B, ∃ b : B, π' a = π' b ^ p) → (∀ (f : A →ₐ[k] B) (a : A), f (π a) = π' (f a)) ∧ (∀ b, π' (π' b) = π' b) ∧ ∀ b, IsNilpotent (π' b) → π' b = 0 := by
  intro p _ k _ _ A B _ _ _ _ _ π π' hA hB
  rcases subsingleton_or_nontrivial B with hs | hs
  · exact ⟨fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _,
      fun _ _ => Subsingleton.elim _ _⟩
  haveI : CharP B p := charP_of_injective_algebraMap (algebraMap k B).injective p
  obtain ⟨r, hr⟩ := exists_pow_prime_pow_kill p (Fact.out : p.Prime).one_lt k B
  have iA := exists_eq_pow_prime_pow p π hA.2 r
  have iB := exists_eq_pow_prime_pow p π' hB.2 r
  have h3 : ∀ b, IsNilpotent (π' b) → π' b = 0 := by
    intro b hb
    obtain ⟨c, hc⟩ := iB b
    rw [hc] at hb ⊢
    exact hr _ hb.of_pow
  refine ⟨fun f a => ?_, fun y => ?_, h3⟩
  · obtain ⟨b, hb⟩ := iA a
    obtain ⟨c, hc⟩ := iB (f a)
    have hd : IsNilpotent (f (π a) - π' (f a)) := by
      have h1 : IsNilpotent (f (a - π a)) := (hA.1 a).map f
      have h2 := hB.1 (f a)
      have e : f (π a) - π' (f a) = (f a - π' (f a)) - f (a - π a) := by rw [map_sub]; ring
      rw [e]
      exact (Commute.all _ _).isNilpotent_sub h2 h1
    have he : f (π a) - π' (f a) = (f (π b) - π' c) ^ (p ^ r) := by
      rw [sub_pow_char_pow, hb, hc, map_pow]
    rw [he] at hd
    exact sub_eq_zero.mp (he.trans (hr _ hd.of_pow))
  · obtain ⟨c, hc⟩ := iB y
    have he : π' (π' y) - π' y = (π' (π' c) - π' c) ^ (p ^ r) := by
      rw [sub_pow_char_pow, hc, map_pow]
    have hn : IsNilpotent (π' (π' c) - π' c) := by
      rw [← neg_sub]; exact (hB.1 (π' c)).neg
    exact sub_eq_zero.mp (he.trans (hr _ hn))

end GlobalTheory.PerfectProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosetOneCochainToCechCochainCoboundary
section
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

noncomputable section

namespace GlobalTheory.CechCmp

theorem posetOneCochainToCechCochain_coboundary : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ g : C0 (capF s U hU hinf), IsCob U (toCech s U hU hinf (d0 (capF s U hU hinf) g)) := by
  intro I _ X R _ s U hU hinf g
  refine ⟨fun i => rsT (cv s U hU hinf (op (NE.single i)) (g (op (NE.single i)))) (U i), fun i j => ?_⟩
  have hp : U i ⊓ U j ≤ cap U (NE.pair i j) := (cap_pair U i j).ge
  have key : ∀ k, k ∈ ({i, j} : Set I) →
      rsT (rsT (cv s U hU hinf (op (NE.single k)) (g (op (NE.single k)))) (cap U (NE.pair i j))) (U i ⊓ U j) =
        rsT (rsT (cv s U hU hinf (op (NE.single k)) (g (op (NE.single k)))) (U k)) (U i ⊓ U j) := by
    intro k hk
    have hk' : U i ⊓ U j ≤ U k := by
      rcases hk with rfl | hk
      · exact inf_le_left
      · rw [Set.mem_singleton_iff.1 hk]; exact inf_le_right
    rw [GlobalTheory.KS.rsT_rsT (cap_mono U (a := NE.pair i j) (b := NE.single k) (NE.le_iff.2 (by rw [NE.set_single, NE.set_pair]; exact Set.singleton_subset_iff.2 hk))) hp,
      GlobalTheory.KS.rsT_rsT (cap_single U k).ge hk']
  rw [toCech_apply, amitsur_d0_apply, amitsur_d0_apply, map_sub, map_sub, cv_mp, cv_mp, GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_sub]
  have e1 := key i (Set.mem_insert i {j})
  have e2 := key j (Set.mem_insert_of_mem i rfl)
  simp only [unop_op] at e1 e2 ⊢
  rw [e1, e2]
  abel

end GlobalTheory.CechCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosetToCechCechToPosetCocycleEq
section
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

set_option autoImplicit false

namespace GlobalTheory.CechCmp

theorem toCech_toPos : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ c : GlobalTheory.KS.C1 U, IsCoc U c → toCech s U hU hinf (toPos s U hU hinf c) = c := by
  intro I _ X R _ s U hU hinf c hc
  funext i j
  rw [toCech_apply, cv_toPos, cv_toPos]
  simp only [unop_op]
  rw [NE.pt_single, NE.pt_single]
  have hk : (NE.pair i j).pt = i ∨ (NE.pair i j).pt = j := by
    have := NE.pt_mem (NE.pair i j)
    rw [NE.set_pair] at this
    simpa using this
  have hi : i ∈ (NE.pair i j).set := by simp [NE.set_pair]
  have hj : j ∈ (NE.pair i j).set := by simp [NE.set_pair]
  have hcap : U i ⊓ U j ≤ cap U (NE.pair i j) := (cap_pair U i j).ge
  rw [GlobalTheory.KS.rsT_rsT (le_inf (cap_le U hi) (cap_le U (NE.pt_mem _))) hcap,
    GlobalTheory.KS.rsT_rsT (le_inf (cap_le U hj) (cap_le U (NE.pt_mem _))) hcap]
  generalize (NE.pair i j).pt = k at hk ⊢
  have hle : U i ⊓ U j ≤ U i ⊓ U j ⊓ U k := by
    refine le_inf le_rfl ?_
    rcases hk with h | h <;> subst h
    exacts [inf_le_left, inf_le_right]
  have h := congrArg (fun t => rsT t (U i ⊓ U j)) (hc i j k)
  simp only [GlobalTheory.KS.rsT_add] at h
  have e₁ : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k := inf_le_inf_right _ inf_le_right
  have e₂ : U i ⊓ U j ⊓ U k ≤ U i ⊓ U k := inf_le_inf_right _ inf_le_left
  rw [GlobalTheory.KS.rsT_rsT inf_le_left hle, GlobalTheory.KS.rsT_self, GlobalTheory.KS.rsT_rsT e₁ hle, GlobalTheory.KS.rsT_rsT e₂ hle] at h
  rw [← h]
  abel

end GlobalTheory.CechCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageCochainRestrictionBijectiveClosedImmersi
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem preRes_bijective : ∀ (R' : Type) [CommRing R'] (X X' : Scheme.{0}) (φ : X' ⟶ X) [IsClosedImmersion φ] (s' : X' ⟶ Sp R'), Function.Bijective (preRes φ s').pull1 ∧ Function.Bijective (preRes φ s').pull2 ∧ (CohomZeroIsConstants (OAff s') → CohomZeroIsConstants (OPre φ s')) := by
  intro R' _ X X' φ _ s'
  have hB : ∀ {U : TopologicalSpace.Opens X} {x : X}, x ∈ U → ∃ U' ∈ X.affineOpens, x ∈ U' ∧ U' ≤ U :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
  refine _root_.GlobalTheory.AbCoh.cohO_basis_bijective R' X' s' X.affineOpens (preU φ) (preU_mono φ) ?_ ?_
  · intro U x hx
    obtain ⟨W, hW, hWU⟩ := (φ.isClosedEmbedding).isInducing.isOpen_iff.mp U.1.2
    have hxW : φ.base x ∈ W := by
      have : x ∈ φ.base ⁻¹' W := by rw [hWU]; exact hx
      exact this
    obtain ⟨V, hV, hxV, hVW⟩ := hB (U := ⟨W, hW⟩) hxW
    refine ⟨⟨V, hV⟩, hxV, ?_⟩
    intro y hy
    have : y ∈ φ.base ⁻¹' W := hVW hy
    rw [hWU] at this
    exact this
  · intro a b x ha hb
    obtain ⟨V, hV, hxV, hVW⟩ := hB (U := a.1 ⊓ b.1) ⟨ha, hb⟩
    exact ⟨⟨V, hV⟩, fun y hy ↦ (hVW hy).1, fun y hy ↦ (hVW hy).2, hxV⟩

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCohomologyComplexContinuousFilteredColimitStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringCohomologyComplex_continuous_filtered_colimit : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X n, (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).X n) (y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X (n - 1)), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).d n (n + 1) w = 0 ∧ (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (c.ι.app j)).f n w = z + (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).X n), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X (n - 1), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (c.ι.app j)).f n w = (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj k)).X (n - 1)), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (D.map f)).f n w = (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj k)).d (n - 1) n y) := by
  first
  | exact @GlobalTheory.EtC.RingCont.main
  | exact GlobalTheory.EtC.RingCont.main
  | (intros; apply GlobalTheory.EtC.RingCont.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallExtensionElementMulZeroClassEqZero
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem tMul_zero_eq_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ y : HO1 s, TMul h₀.w t 0 y → y = 0 := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hE hF y hy
  have iφ : IsClosedImmersion φ :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip
      (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom σ) hE.1)
  have iφ₀ : IsClosedImmersion φ₀ :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h₀.flip
      (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom σ₀) hE.2.2.1)
  obtain ⟨f, c, hc, rfl, hred⟩ := hy
  obtain ⟨c₀, hc₀, hcl⟩ := ((GlobalTheory.AbCoh.red_iff_pre R R₀ X X₀ s s₀ σ₀ φ₀ h₀.w).1 f 0).1 hred
  rw [map_zero, CatCoh.H1.mk_eq_zero] at hcl
  obtain ⟨g₀, hg₀⟩ := hcl
  have hS := GlobalTheory.AbCoh.preα_surjective_and_ker R R' R₀ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hE hF
  choose g hg using fun U => (hS U).2.2.1 (g₀ U)
  have key : ∀ U V (a : U ⟶ V), t • (f U V a - d0 (OAff s) g U V a) = 0 := by
    intro U V a
    rw [← (hS V).2.2.2]
    have hn := (preCoef h₀.w).naturality a (g U)
    have e := congrFun (congrFun (congrFun hg₀ U) V) a
    change preα φ₀ s s₀ V (mp (OAff s) a (g U)) = mp (OPre φ₀ s₀) a (preα φ₀ s s₀ U (g U)) at hn
    rw [amitsur_d0_apply, hc₀] at e
    rw [amitsur_d0_apply, map_sub, map_sub, hn, hg, hg, ← e]
    ring
  refine CatCoh.H1.mk_eq_zero.2 ⟨t • g, ?_⟩
  rw [hc, map_smul]
  funext U V a
  have := key U V a
  simp only [Pi.smul_apply]
  rw [smul_sub, sub_eq_zero] at this
  exact this.symm

end GlobalTheory.AbCoh
end

