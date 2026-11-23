module

public import Formalism.DoubleCosetMeasures.Statement
public import Formalism.HermitianCurvature.Bundle0002

@[expose] public section

namespace Formalism.FourierDecayAlt.S3

open Matrix Finset MeasureTheory
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni upUniG)
open scoped ENNReal

abbrev Mid (k : ℕ) : Type := Fin k ⊕ Unit

abbrev Idx (r k : ℕ) : Type := Fin r ⊕ Mid k ⊕ Fin r

section Blocks

variable {A : Type} {r k : ℕ}

def b11 (x : Matrix (Idx r k) (Idx r k) A) : Matrix (Fin r) (Fin r) A :=
  Matrix.of fun a b => x (Sum.inl a) (Sum.inl b)

def b12 (x : Matrix (Idx r k) (Idx r k) A) : Matrix (Fin r) (Mid k) A :=
  Matrix.of fun a b => x (Sum.inl a) (Sum.inr (Sum.inl b))

def b13 (x : Matrix (Idx r k) (Idx r k) A) : Matrix (Fin r) (Fin r) A :=
  Matrix.of fun a b => x (Sum.inl a) (Sum.inr (Sum.inr b))

def b21 (x : Matrix (Idx r k) (Idx r k) A) : Matrix (Mid k) (Fin r) A :=
  Matrix.of fun a b => x (Sum.inr (Sum.inl a)) (Sum.inl b)

def b22 (x : Matrix (Idx r k) (Idx r k) A) : Matrix (Mid k) (Mid k) A :=
  Matrix.of fun a b => x (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl b))

def b23 (x : Matrix (Idx r k) (Idx r k) A) : Matrix (Mid k) (Fin r) A :=
  Matrix.of fun a b => x (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr b))

def b31 (x : Matrix (Idx r k) (Idx r k) A) : Matrix (Fin r) (Fin r) A :=
  Matrix.of fun a b => x (Sum.inr (Sum.inr a)) (Sum.inl b)

def b32 (x : Matrix (Idx r k) (Idx r k) A) : Matrix (Fin r) (Mid k) A :=
  Matrix.of fun a b => x (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inl b))

def b33 (x : Matrix (Idx r k) (Idx r k) A) : Matrix (Fin r) (Fin r) A :=
  Matrix.of fun a b => x (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inr b))

variable [CommRing A]

def IsN (x : Matrix (Idx r k) (Idx r k) A) : Prop :=
  IsUpUni (b11 x) ∧ IsUpUni (b33 x) ∧ b22 x = 1 ∧ b21 x = 0 ∧ b31 x = 0 ∧ b32 x = 0

def midEmb (h : Matrix (Fin k) (Fin k) A) : Matrix (Mid k) (Mid k) A := Matrix.fromBlocks h 0 0 1

def hEmb (r : ℕ) (h : Matrix (Fin k) (Fin k) A) : Matrix (Idx r k) (Idx r k) A :=
  Matrix.fromBlocks 1 0 0 (Matrix.fromBlocks (midEmb h) 0 0 1)

end Blocks

def GammaProduct : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (k : ℕ),
    Nat.card (GL (Fin k) K) = Nat.card (upUniG K k) * ∏ i ∈ Icc 1 k, (Fintype.card K ^ i - 1)

def PrimeTail : Prop :=
  ∀ (s N : ℕ), 2 ≤ s → ∑ l ∈ Icc 2 N, ((l : ℝ) ^ s)⁻¹ ≤ 3 * ((2 : ℝ) ^ s)⁻¹

def lead {A : Type} [CommRing A] {r : ℕ} (M : Matrix (Fin r) (Fin r) A) (l : ℕ) (hl : l ≤ r) : A :=
  (M.submatrix (Fin.castLE hl) (Fin.castLE hl)).det

def LDUExists : Prop :=
  ∀ (A : Type) [CommRing A] (r : ℕ) (M : Matrix (Fin r) (Fin r) A),
    (∀ (l : ℕ) (hl : l < r), IsUnit (lead M l hl.le)) →
    ∃ (L U : Matrix (Fin r) (Fin r) A) (d : Fin r → A), IsLowUni L ∧ IsUpUni U ∧
      M = L * Matrix.diagonal d * U ∧
      ∀ (l : ℕ) (hl : l < r), lead M (l + 1) hl = d ⟨l, hl⟩ * lead M l hl.le

structure MassData (P : Type) where

  g : P → ℝ

  glk : P → ℝ

  uk : P → ℝ

  nn : P → ℝ

  gg : P → ℝ

  μKp : P → ℝ

  μKnatp : P → ℝ

  μKppp : P → ℝ

  μSp : P → ℝ

  μSp' : P → ℝ

  μSppp : P → ℝ

  μSppp' : P → ℝ

  Mp : P → ℝ

  localVolumeAtPlace : P → ℝ

  μKo : ℝ

  μSo : ℝ

  μSo' : ℝ

  Mo : ℝ

  localVolumeArchimedean : ℝ

  μH : ℝ

  μH' : ℝ

  μHpp : ℝ

  μHpp' : ℝ

  μN : ℝ

  μN' : ℝ

  volZZ : ℝ

  volPP : ℝ

  al : ℝ

  volG : ℝ

  volHa : ℝ

  volHa' : ℝ

  volNa : ℝ

  volNa' : ℝ

  volB : ℝ

  volH : ℝ

  volH' : ℝ

  volN : ℝ

  volN' : ℝ

  Coo : ℝ

  deg : ℝ

  dimπ : ℝ

  dimπ' : ℝ

  ρ0 : ℝ

  ρ0' : ℝ

  d : ℝ

  d' : ℝ

  n0c : ℝ

  supdens : ℝ

  e1 : ℝ

  δ : ℝ

  Kgs2 : ℝ

  KV : ℝ

  Sig : ℝ

  KtopV : ℝ

  IntN : ℝ

  IntC : ℝ

  IntOO : ℝ

namespace MassData

variable {P : Type} [Fintype P] (B : MassData P)

noncomputable def ga (p : P) : ℝ := B.glk p / B.uk p

noncomputable def Gam1 : ℝ := ∏ p, B.ga p

noncomputable def tt : ℝ := ∏ p, (1 + 3 / B.g p)

noncomputable def μK : ℝ := B.μKo * ∏ p, B.μKp p

noncomputable def μKnat : ℝ := B.μKo * ∏ p, B.μKnatp p

noncomputable def μKpp : ℝ := B.μKo * ∏ p, B.μKppp p

noncomputable def μS : ℝ := B.μSo * ∏ p, B.μSp p

noncomputable def μS' : ℝ := B.μSo' * ∏ p, B.μSp' p

noncomputable def μSpp : ℝ := B.μSo * ∏ p, B.μSppp p

noncomputable def μSpp' : ℝ := B.μSo' * ∏ p, B.μSppp' p

noncomputable def MM : ℝ := B.Mo * ∏ p, B.Mp p

noncomputable def unitLevelVolume : ℝ := B.localVolumeArchimedean * ∏ p, B.localVolumeAtPlace p

noncomputable def c0 : ℝ := B.volN * B.volH / B.dimπ

noncomputable def c0' : ℝ := B.volN' * B.volH' / B.dimπ'

noncomputable def Dstar : ℝ := B.deg * (B.volG / B.μKpp)

noncomputable def AA : ℝ := B.volB * B.Coo * (B.MM / B.volZZ) / B.μK

noncomputable def GS : ℝ := B.tt * (B.d / B.dimπ) * B.KV

noncomputable def Smod : ℝ := B.c0 * B.c0' * B.KtopV

def Pos : Prop :=
  (∀ p, 0 < B.g p ∧ 0 < B.glk p ∧ 0 < B.uk p ∧ 0 < B.nn p ∧ 0 < B.gg p ∧ 0 < B.μKp p ∧
    0 < B.μKnatp p ∧ 0 < B.μKppp p ∧ 0 < B.μSp p ∧ 0 < B.μSp' p ∧ 0 < B.μSppp p ∧ 0 < B.μSppp' p ∧
    0 < B.Mp p ∧ 0 < B.localVolumeAtPlace p) ∧
  0 < B.μKo ∧ 0 < B.μSo ∧ 0 < B.μSo' ∧ 0 < B.Mo ∧ 0 < B.localVolumeArchimedean ∧ 0 < B.μH ∧ 0 < B.μH' ∧
  0 < B.μHpp ∧ 0 < B.μHpp' ∧ 0 < B.μN ∧ 0 < B.μN' ∧ 0 < B.volZZ ∧ 0 < B.volPP ∧ 0 < B.al ∧ 0 < B.volG ∧
  0 < B.volHa ∧ 0 < B.volHa' ∧ 0 < B.volNa ∧ 0 < B.volNa' ∧ 0 < B.volB ∧ 0 < B.volH ∧
  0 < B.volH' ∧ 0 < B.volN ∧ 0 < B.volN' ∧ 0 < B.Coo ∧ 0 < B.deg ∧ 0 < B.dimπ ∧ 0 < B.dimπ' ∧
  0 < B.ρ0 ∧ 0 < B.ρ0' ∧ 0 < B.d ∧ 0 < B.d' ∧ 0 < B.n0c ∧ 0 ≤ B.supdens ∧ 0 ≤ B.δ

def InTwoA : Prop := B.Kgs2 ≤ B.tt * B.Gam1 * B.Sig

def InForm : Prop := B.Sig = B.ρ0 * B.KV

def InKernel : Prop := B.KV ≤ B.supdens * B.n0c * B.KtopV ∧ 0 ≤ B.KtopV

def InMass : Prop := B.n0c * B.ρ0 = B.AA

def InDens : Prop := B.supdens ≤ B.e1

def InTheoremA : Prop := B.Smod ≤ (1 + B.δ) * B.IntN

def InJacMod : Prop := B.IntN = B.volZZ / (B.unitLevelVolume * B.volPP) * (B.volPP * B.IntC)

def InNu : Prop := B.IntOO = B.Coo * B.IntC

def InInfinity : Prop := B.IntOO ≤ 1 / B.deg

def InVolumes : Prop := B.volB * B.volG = B.volHa * B.volHa' ∧ B.volNa = 1 ∧ B.volNa' = 1

def InLevelS : Prop :=
  B.μS = B.μN * B.μH ∧ B.μSpp = B.μN * B.μHpp ∧ B.μS' = B.μN' * B.μH' ∧ B.μSpp' = B.μN' * B.μHpp'

def InMasses : Prop :=
  B.ρ0 = B.volHa / (B.volH * B.μH) ∧ B.volNa = B.volN * B.μN ∧
  B.ρ0' = B.volHa' / (B.volH' * B.μH') ∧ B.volNa' = B.volN' * B.μN'

def InColumns : Prop :=
  B.d = B.dimπ * (B.volHa / (B.volH * B.μHpp)) ∧ B.μH / B.μHpp = B.Gam1 ∧
  B.d' = B.dimπ' * (B.volHa' / (B.volH' * B.μHpp')) ∧ B.μH' / B.μHpp' = B.Gam1

def InOrdinary : Prop := B.Mo / B.localVolumeArchimedean = B.μKo ^ 2 / (B.μSo * B.μSo')

def InTyped : Prop :=
  ∀ p, B.Mp p / B.localVolumeAtPlace p = B.μKp p * B.μKnatp p / (B.μSp p * B.μSp' p) ∧
    B.μSp p = B.ga p * B.μSppp p ∧ B.μSp' p = B.ga p * B.μSppp' p

def InIndices : Prop :=
  ∀ p, B.μKp p = B.gg p / (B.nn p * B.uk p) * B.μKppp p ∧
    B.μKnatp p / B.μKp p = B.glk p * B.nn p / B.gg p

end MassData

def Columns : Prop :=
  ∀ (P : Type) [Fintype P] (B : MassData P), B.Pos → B.InVolumes → B.InLevelS → B.InMasses →
    B.InColumns →
    B.ρ0 * B.volN * B.volH = B.volHa / B.μS ∧ B.d = B.Gam1 * B.ρ0 * B.dimπ ∧
    1 / B.c0 = B.d * B.μSpp / B.volHa ∧
    B.ρ0' * B.volN' * B.volH' = B.volHa' / B.μS' ∧ B.d' = B.Gam1 * B.ρ0' * B.dimπ' ∧
    1 / B.c0' = B.d' * B.μSpp' / B.volHa'

def KnatGamma : Prop :=
  ∀ (P : Type) [Fintype P] (B : MassData P), B.Pos → B.InIndices →
    ∀ p, B.μKnatp p = B.ga p * B.μKppp p

def LocalProduct : Prop :=
  ∀ (P : Type) [Fintype P] (B : MassData P), B.Pos → B.InOrdinary → B.InTyped → B.InIndices →
    B.MM / B.unitLevelVolume / B.μK = B.μKpp / (B.Gam1 * B.μSpp * B.μSpp') ∧
    B.MM / B.unitLevelVolume / B.μK = B.μKnat / (B.μS * B.μS')

def JacobianConstant : Prop :=
  ∀ (P : Type) [Fintype P] (B : MassData P), B.Pos → B.InJacMod → B.InNu →
    B.IntN = B.volZZ / B.unitLevelVolume * B.Coo⁻¹ * B.IntOO

def SigBound : Prop :=
  ∀ (P : Type) [Fintype P] (B : MassData P), B.Pos → B.InForm → B.InKernel → B.InMass → B.InDens →
    B.InTheoremA → B.InJacMod → B.InNu → B.InInfinity →
    B.Sig ≤ (1 + B.δ) * B.e1 * (B.c0 * B.c0')⁻¹ * B.volB * (B.MM / B.unitLevelVolume) / (B.μK * B.deg)

def MainTheorem : Prop :=
  ∀ (P : Type) [Fintype P] (B : MassData P), B.Pos → B.InTwoA → B.InForm → B.InKernel → B.InMass →
    B.InDens → B.InTheoremA → B.InJacMod → B.InNu → B.InInfinity → B.InVolumes → B.InLevelS →
    B.InMasses → B.InColumns → B.InOrdinary → B.InTyped → B.InIndices →
    B.GS = B.tt * B.Gam1 * B.Sig ∧
    B.GS ≤ (1 + B.δ) * B.e1 * B.tt * (B.d * B.d' / B.Dstar) ∧
    B.Kgs2 ≤ (1 + B.δ) * B.e1 * B.tt * (B.d * B.d' / B.Dstar)

end Formalism.FourierDecayAlt.S3
