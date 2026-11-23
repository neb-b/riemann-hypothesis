module

public import Development.AutomorphicArithmetic.CoprimeRanks.SecondSetNoRelation
public import Development.AutomorphicArithmetic.CharacterBoxes.PairGood

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CharacterBoxes.Imports
section
noncomputable section

namespace UpperTheory.Top

open Formalism.BasicNotions Formalism.HC HostParam.Seam

def admitted (R : Ranks) (H0 : HostAx R.toFrame) : Prop :=
  ∀ (b : ℕ) (c : Choices R.toFrame H0.toHostRaw), FieldRows H0.toHostRaw b →
    (4 * R.t * R.r + 1 < H0.q ∧ 4 * R.t * R.r + 1 < H0.d) →
    ∃ D : Host R, D.toHostAx = H0 ∧ D.splitBound = b ∧ HEq (HostNF.ofHost D).ch c

end UpperTheory.Top

end
end

-- bundled from Development.AutomorphicArithmetic.CharacterBoxes.TwistForm
section
noncomputable section

namespace UpperTheory.Top

open Formalism.HC

def KerChi (ψ : PChar) {φ : Frame} (H : HostRaw φ) : Prop :=
  ψ.N ∣ H.QS ∧ ∀ (a : ℕ) (h : a.Coprime H.condN), H.art (ZMod.unitOfCoprime a h) = 1 ↔
    (a ≡ 1 [MOD 2 ^ (φ.e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (φ.e + 2)]) ∧ ψ.val a = 1 ∧
      jacobiSym (a : ℤ) H.q = 1 ∧ jacobiSym (a : ℤ) H.d = 1

def TwistForm (ψ : PChar) {φ : Frame} (H : HostRaw φ) : Prop :=
  ∀ θ : φ.Char, Frame.TrivialOnFirstFactor θ → ∃ ξ ∈ Subgroup.zpowers ψ.χ, ∃ i j : Fin 2,
    θ φ.iod = (-1) ^ (j : ℕ) ∧
      ∀ a : ℕ, a.Coprime H.condN → H.dirAt θ a = tw (fun b => ξ (b : ZMod ψ.N)) H.q H.d i j a

structure WinDatum (ψ : PChar) (eps J c x Y : ℝ) (q d e : ℕ) : Prop where
  lo : x ^ (1 / J) ≤ Y
  up : Y ≤ x
  good : PairGood ψ.N eps Y x q d
  n_lo : x ^ (2 + 8 * eps) ≤ c * 2 ^ e
  n_up : c * 2 ^ e ≤ 2 * x ^ (2 + 8 * eps)
  bound : ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ e q d E →
    VVle E ⌊x ^ (400 : ℝ)⌋₊ (Real.sqrt (Real.exp (x ^ eps)))

end UpperTheory.Top

end
end

