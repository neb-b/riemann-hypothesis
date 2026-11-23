module

public import Formalism.HermitianCurvature.StatementB

@[expose] public section

open Matrix MeasureTheory
open scoped ComplexConjugate ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.C2

open Formalism.QuantumDeterminants

def mx {α β : Type*} [Fintype α] [Fintype β] (M : Matrix α β ℂ) : ℝ := ‖Matrix.of.symm M‖

def UTset (m : ℕ) : Set (Matrix (Fin m) (Fin m) ℂ) := {u | (∀ i j, j < i → u i j = 0) ∧ ∀ i, u i i = 1}

def LTset (m : ℕ) : Set (Matrix (Fin m) (Fin m) ℂ) := {l | (∀ i j, i < j → l i j = 0) ∧ ∀ i, l i i = 1}

def monoP {m : ℕ} (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i a => if i = w a then d a else 0

def IsMonomial {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∃ (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ), (∀ a, d a ≠ 0) ∧ P = monoP w d

def simpleUp {m : ℕ} (u : Matrix (Fin m) (Fin m) ℂ) : ℂ :=
  ∑ a : Fin m, if h : a.val + 1 < m then u a ⟨a.val + 1, h⟩ else 0

def psiC (c x : ℂ) : ℂ := Complex.exp (Complex.I * ((c * x).re : ℂ))

def LPg {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) : Set (Matrix (Fin m) (Fin m) ℂ) :=
  {l | l ∈ LTset m ∧ P⁻¹ * l * P ∈ LTset m}

def Lstg {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) : Set (Matrix (Fin m) (Fin m) ℂ) :=
  {l | l ∈ LTset m ∧ P⁻¹ * l * P ∈ UTset m}

def lowOf {m : ℕ} {ι : Type*} [Fintype ι] (pos : ι → Fin m × Fin m) (v : ι → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  1 + Matrix.of fun i j => ∑ q, if pos q = (i, j) then v q else 0

abbrev Lidx (m : ℕ) : Type := {q : Fin m × Fin m // q.2 < q.1}

abbrev LPidx {m : ℕ} (w : Equiv.Perm (Fin m)) : Type := {q : Fin m × Fin m // q.2 < q.1 ∧ w.symm q.2 < w.symm q.1}

abbrev Lstidx {m : ℕ} (w : Equiv.Perm (Fin m)) : Type := {q : Fin m × Fin m // q.2 < q.1 ∧ w.symm q.1 < w.symm q.2}

def IsPolyDeg {n : ℕ} (D : ℕ) (P : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∃ q : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ, q.totalDegree ≤ D ∧
    ∀ g, P g = MvPolynomial.eval (Sum.elim (fun p => g p.1 p.2) (fun p => conj (g p.1 p.2))) q

def StdZ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Prop := inWb k r z ∧ 0 < Tz k r z

def Std (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Prop := 1 ≤ k ∧ StdZ k r z ∧ StdZ k r z'

def uMap (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (s : B.Mat k r) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  fun a b => if h : a.val < r then herm (Hpk k r) (s *ᵥ fvec k r z b) (bvec (esI k r ⟨a.val, h⟩))
    else herm (Hpk k r) (s *ᵥ fvec k r z b) z / herm (Hpk k r) z z

def flagSpan (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
  Submodule.span ℂ (Set.range fun b : {b : Fin (r + 1) // b < a} => fvec k r z b.1)

def FlagStab (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Set (B.Mat k r) :=
  {s | s ∈ B.GV k r ∧ ∀ a, s *ᵥ fvec k r z a - fvec k r z a ∈ flagSpan k r z a}

def CurvatureSupportSet (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Set (B.Mat k r) := {s | s ∈ Sset k r z ∧ uMap k r z s = 1}

def N0set (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Set (B.Mat k r) := {n | n ∈ Nset k r ∧ uMap k r z n = 1}

def FixSet (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Set (B.Mat k r) :=
  {g | g ∈ B.GV k r ∧ ∀ a, g *ᵥ fvec k r z a = fvec k r z a}

def Adiag (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Matrix.diagonal fun a => if a = Fin.last r then -((Tz k r z : ℝ) : ℂ) else 0

def SFlag : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), StdZ k r z → FlagStab k r z = Sset k r z

def UMapFrame : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), StdZ k r z →
    (∀ s ∈ Sset k r z, (∀ b, s *ᵥ fvec k r z b = ∑ a, uMap k r z s a b • fvec k r z a) ∧
      uMap k r z s ∈ UTset (r + 1) ∧
      ∀ t ∈ Sset k r z, uMap k r z (s * t) = uMap k r z s * uMap k r z t) ∧
    ∀ h ∈ UWset k r z, uMap k r z h = 1

def ZhatEquiv : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), StdZ k r z → StdZ k r z' →
    ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z', ∀ g : B.Mat k r,
      Zhat k r z z' (s⁻¹ * g * s') = (uMap k r z s)ᴴ * Zhat k r z z' g * uMap k r z' s'

def GramBlocks : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), StdZ k r z → StdZ k r z' → ∀ g ∈ B.GV k r,
    gramM k r z z' g = Matrix.fromBlocks (Adiag k r z) (Zhat k r z z' g) (Zhat k r z z' g)ᴴ (Adiag k r z')

def DetNonzero : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), StdZ k r z → StdZ k r z' → ∀ g : B.Mat k r,
    0 < Gf k r z z' g → (Zhat k r z z' g).det ≠ 0

def Majorant : Prop :=
  ∀ k r : ℕ, Hpk k r ∈ B.GV k r ∧ Hpk k r * Hpk k r = 1 ∧
    ∀ v : Fin (2 * r + k + 1) → ℂ, herm (Hpk k r) v (Hpk k r *ᵥ v) = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) ∧
      (herm (Hpk k r) v v).re ≤ ∑ i, Complex.normSq (v i)

def NormInv : Prop := ∀ (k r : ℕ), ∀ g ∈ B.GV k r, B.gN g⁻¹ = B.gN g ∧ 1 ≤ B.gN g

def TwoSided : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (m : ℕ) (F : B.Mat k r → E) (c : ℝ),
    B.CkOn (m : ℕ∞) (B.GV k r) F →
    (∀ v : List (B.Mat k r), (∀ X ∈ v, B.unitLie k r X) → v.length ≤ m →
      ∀ g ∈ B.GV k r, B.gN g ^ A * ‖B.Rw v F g‖ ≤ c) →
    B.InCC (A - 2 * m) m F

def Uperp (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
  LinearMap.ker (Matrix.mulVecLin ((Matrix.of fun i j => star (gramVec k r z z' γ i j)) * Hpk k r))

def KU (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) : Set (B.Mat k r) :=
  {g | g ∈ B.GV k r ∧ ∀ i, g *ᵥ gramVec k r z z' γ i = gramVec k r z z' γ i}

def Hst (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) : Set (B.Mat k r) :=
  {g | g ∈ Sset k r z ∧ ∃ s' ∈ Sset k r z', g = γ * s' * γ⁻¹}

def Rst (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) : Set (B.Mat k r) :=
  {g | g ∈ Hst k r z z' γ ∧ ∀ v ∈ Uperp k r z z' γ, g *ᵥ v = v}

def PosPt (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) : Prop :=
  γ ∈ B.GV k r ∧ 0 < Gf k r z z' γ

def GramIndependentSignature : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    LinearIndependent ℂ (gramVec k r z z' γ) ∧
    (∃ Q : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ, IsUnit Q.det ∧
      Qᴴ * gramM k r z z' γ * Q = Matrix.fromBlocks 1 0 0 (-1)) ∧
    (∀ v ∈ Uperp k r z z' γ, v ≠ 0 → 0 < (herm (Hpk k r) v v).re) ∧
    Module.finrank ℂ (Uperp k r z z' γ) = k - 1

def C1ii : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    KU k r z z' γ ⊆ Hst k r z z' γ ∧
    Rst k r z z' γ = {g | g ∈ Nset k r ∧ ∃ n ∈ Nset k r, g = γ * n * γ⁻¹} ∧
    (∀ h ∈ Hst k r z z' γ, ∃! p : B.Mat k r × B.Mat k r,
      p.1 ∈ Rst k r z z' γ ∧ p.2 ∈ KU k r z z' γ ∧ h = p.1 * p.2) ∧
    (∀ ρ ∈ Rst k r z z' γ, ∀ κ ∈ KU k r z z' γ, ρ * κ = κ * ρ) ∧
    ∀ ρ ∈ Rst k r z z' γ, (ρ - 1) ^ (2 * r + k + 1) = 0

def CurvatureConditionOneClauseThree : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    Set.BijOn (fun ρ => (uMap k r z ρ, uMap k r z' (γ⁻¹ * ρ * γ))) (Rst k r z z' γ)
      {p | p.1 ∈ UTset (r + 1) ∧ p.2 ∈ UTset (r + 1) ∧ p.1ᴴ * Zhat k r z z' γ * p.2 = Zhat k r z z' γ} ∧
    Set.InjOn (uMap k r z) (Rst k r z z' γ) ∧
    Set.InjOn (fun ρ => uMap k r z' (γ⁻¹ * ρ * γ)) (Rst k r z z' γ)

def LowSplit : Prop :=
  ∀ (m : ℕ) (P : Matrix (Fin m) (Fin m) ℂ), IsMonomial P → ∀ l ∈ LTset m,
    ∃! p : Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ, p.1 ∈ LPg P ∧ p.2 ∈ Lstg P ∧ l = p.1 * p.2

def LPCoords : Prop :=
  ∀ (m : ℕ) (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ), (∀ a, d a ≠ 0) →
    (Set.range (lowOf (fun q : LPidx w => q.1)) = LPg (monoP w d)) ∧
    (Set.range (lowOf (fun q : Lstidx w => q.1)) = Lstg (monoP w d))

def LowSplitMeas : Prop :=
  ∀ (m : ℕ) (w : Equiv.Perm (Fin m)),
    MeasurePreserving (fun p : (LPidx w → ℂ) × (Lstidx w → ℂ) => fun q : Lidx m =>
        (lowOf (fun q : LPidx w => q.1) p.1 * lowOf (fun q : Lstidx w => q.1) p.2) q.1.1 q.1.2)
      volume volume

def URImage : Prop :=
  ∀ (m : ℕ) (P : Matrix (Fin m) (Fin m) ℂ), IsMonomial P →
    {u | u ∈ UTset m ∧ ∃ u' ∈ UTset m, uᴴ * P * u' = P} = {u | u ∈ UTset m ∧ uᴴ ∈ Lstg P}

def UpSplit : Prop :=
  ∀ (m : ℕ) (P : Matrix (Fin m) (Fin m) ℂ), IsMonomial P → ∀ u ∈ UTset m,
    ∃! p : Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ,
      p.1 ∈ UTset m ∧ p.2 ∈ UTset m ∧ p.1ᴴ ∈ Lstg P ∧ p.2ᴴ ∈ LPg P ∧ u = p.1 * p.2

def MonomialFactorizationBound : Prop :=
  ∀ (m : ℕ) (P : Matrix (Fin m) (Fin m) ℂ), IsMonomial P → ∃ C : ℝ, ∀ l ∈ LPg P, ∀ u' ∈ UTset m,
    mx l ≤ C * (1 + mx (l * P * u')) ^ m ∧ mx u' ≤ C * (1 + mx (l * P * u')) ^ m ∧
    mx l⁻¹ ≤ C * (1 + mx (l * P * u')) ^ ((m - 1) * m) ∧ mx u'⁻¹ ≤ C * (1 + mx (l * P * u')) ^ ((m - 1) * m)

def xiV (k r : ℕ) (ξ : Fin r → ℂ) : Fin (2 * r + k + 1) → ℂ := fun i => if h : i.val < r then ξ ⟨i.val, h⟩ else 0

def nEich (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (ξ : Fin r → ℂ) : B.Mat k r :=
  1 + ((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) •
    (-(vecMulVec (xiV k r ξ) (star (Hpk k r *ᵥ z))) + vecMulVec z (star (Hpk k r *ᵥ xiV k r ξ)) +
      (1 / 2 : ℂ) • vecMulVec (xiV k r ξ) (star (Hpk k r *ᵥ xiV k r ξ)))

def mX (k r : ℕ) (vX : Matrix (Fin r) (Fin r) ℂ) : B.Mat k r := fun i j =>
  if hi : i.val < r then (if hj : j.val < r then vX ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0)
  else if hi' : r + k < i.val then
    (if hj' : r + k < j.val then (vXᴴ)⁻¹ ⟨2 * r + k - i.val, by omega⟩ ⟨2 * r + k - j.val, by omega⟩ else 0)
  else if i = j then 1 else 0

def tauM (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (v : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : B.Mat k r :=
  nEich k r z (fun a => v a.castSucc (Fin.last r)) * mX k r (v.submatrix Fin.castSucc Fin.castSucc)

def TauMem : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), StdZ k r z → ∀ v ∈ UTset (r + 1),
    tauM k r z v ∈ Nset k r ∧ (∀ b, tauM k r z v *ᵥ fvec k r z b = ∑ a, v a b • fvec k r z a) ∧
    uMap k r z (tauM k r z v) = v

def Sg (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) : Set (B.Mat k r) :=
  {σ | ∃ n0 ∈ N0set k r z, ∃ v ∈ UTset (r + 1), vᴴ ∈ LPg (Zhat k r z z' γ) ∧ ∃ h ∈ UWset k r z,
    σ = n0 * tauM k r z v * h}

def Sg' (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) : Set (B.Mat k r) :=
  {σ | ∃ n0 ∈ N0set k r z', ∃ v ∈ UTset (r + 1),
    Zhat k r z z' γ * v * (Zhat k r z z' γ)⁻¹ ∈ UTset (r + 1) ∧ ∃ h ∈ UWset k r z', σ = n0 * tauM k r z' v * h}

def SectionDecomp : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    IsMonomial (Zhat k r z z' γ) → ∀ s ∈ Sset k r z,
      ∃! p : B.Mat k r × B.Mat k r, p.1 ∈ Rst k r z z' γ ∧ p.2 ∈ Sg k r z z' γ ∧ s = p.1 * p.2

def SectionDecompOfParts : Prop :=
  C1ii → CurvatureConditionOneClauseThree → URImage → UpSplit → SFlag → UMapFrame → ZhatEquiv → TauMem → SectionDecomp

def ZhatBound : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), ∃ C : ℝ, ∀ g : B.Mat k r, mx (Zhat k r z z' g) ≤ C * B.gN g

def PolyProper : Prop :=
  ∃ c₁ : ℕ, ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    IsMonomial (Zhat k r z z' γ) → ∃ C : ℝ,
      (∀ σ ∈ Sg k r z z' γ, ∀ s' ∈ Sset k r z',
        B.gN σ + B.gN s' ≤ C * B.gN (σ⁻¹ * γ * s') ^ (c₁ * (r + 1) ^ 2)) ∧
      (∀ s ∈ Sset k r z, ∀ σ' ∈ Sg' k r z z' γ,
        B.gN s + B.gN σ' ≤ C * B.gN (s⁻¹ * γ * σ') ^ (c₁ * (r + 1) ^ 2))

def FixFrame : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), StdZ k r z → FixSet k r z = CurvatureSupportSet k r z

def FibreOrbit : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), Std k r z z' → ∀ g₁ ∈ B.GV k r, ∀ g₂ ∈ B.GV k r,
    0 < Gf k r z z' g₁ → Zhat k r z z' g₁ = Zhat k r z z' g₂ →
      ∃ s ∈ CurvatureSupportSet k r z, ∃ s' ∈ CurvatureSupportSet k r z', g₂ = s⁻¹ * g₁ * s'

end Formalism.FourierDecayAlt.C2
