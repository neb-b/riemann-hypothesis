module

public import Mathlib
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0029
public import Formalism.LocalRingCardinality.FactDelDualNabla
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0010
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0012
public import Formalism.GradedWeylDivisibility.FinalC
public import Formalism.LocalToGlobal.Divisibility.LinkDef
public import Formalism.AdicCompletionExports.NonnegativeDivisors.Imports
public import Formalism.SharpRestriction.Bundle0002
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0005
public import Formalism.LocalToGlobal.Divisibility.NumbersLink

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Divisibility.BrJoint
section
noncomputable section

namespace Formalism.L2.DIV.BrJ

open Formalism.BasicNotions Formalism.MainNotions

theorem branching_interlacing_pairs : PrimeDegreeVariant.Conclusion6 := by
  intro n N h lam sg hI
  exact _root_.gTLower_of Formalism.BasicNotions.factDelDualNabla n N h lam sg hI

variable {D : D7} {u : D.what₂.Word}

variable {D : D7} {u : D.what₂.Word}

end Formalism.L2.DIV.BrJ
end
end

-- bundled from Formalism.LocalToGlobal.Divisibility.LinkDefN
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.BasicNotions Formalism.MainNotions Formalism.AdicCompletionExports.NonnegativeDivisors

section Rec

variable {D : D7}

theorem zero_le_logWeight (w : D.what₂.places.Pl) : 0 ≤ SizeData₂.lwP w := by
  unfold SizeData₂.lwP Formalism.BasicNotions.lw
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

def TieTwRec (L : SizeData₂ D) (Tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) : Prop :=
  ∀ y ∈ Tw, D.plEq.symm y ∈ L.supp ∧ D.what₂.muAt (D.plEq.symm y) ≠ D.what₂.mu0

end Rec

section Ties

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
  (F : DefFam D.what₂.LL G Pl0 T (Fin D.R.m)) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub F.amb)
  (μ : HeightOneSpectrum (𝓞 D.what₂.LL) → T) (Tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL)))

end Ties

section Inputs

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

variable {A : FamIn K G Pl0 T m} {s : ℕ} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G}
  {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)}
  {Zsc : DefSub A.fam.amb → IndefScale A.fam.base} {C CH : ℝ} {Pk : IndefPkg A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) C CH}
  {Pl : Type} [Fintype Pl] [DecidableEq Pl] {R : RecNums A.fam.base.J Pl} {u : (Dc Pk.Zs).Mem}
  {Nu : Submodule (𝓞 K) (Fin ((Dc Pk.Zs).a u) → K)} {sg : HeightOneSpectrum (𝓞 K) → ℝ} {bd : A.fam.base.J → ℝ}

end Inputs

end Formalism.L2.DIV
end
end

-- bundled from Formalism.LocalToGlobal.Divisibility.ZscOfNum
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.BasicNotions

def NumDatum.unitE (Nd : NumDatum) (Nc : ℝ) : ℝ := Nd.sc.x ^ Nd.sc.eps * (Nd.B0 + Nc)

theorem NumDatum.logLog_le (Nd : NumDatum) (h : Real.log Nd.sc.x ≤ Nd.sc.L) :
    Real.log (Real.log Nd.sc.x) ≤ Nd.sc.x ^ Nd.sc.eps := by
  have hl : 0 < Real.log Nd.sc.x := Real.log_pos Nd.sc.one_lt_alt
  have h1 := Real.log_le_sub_one_of_pos hl
  have h2 : Nd.sc.L = Nd.sc.x ^ Nd.sc.eps := rfl
  linarith

theorem NumDatum.loss_bound_nonneg (Nd : NumDatum) : 0 ≤ Nd.B0 := by
  unfold NumDatum.B0
  have := Nd.b_pos
  have := Real.rpow_nonneg Nd.x_pos.le Nd.sc.eps
  positivity

theorem NumDatum.one_le_B0 (Nd : NumDatum) : 1 ≤ Nd.B0 := by
  unfold NumDatum.B0
  have hf : (1 : ℝ) ≤ Nd.R.f := by
    have : 1 ≤ Nd.R.f := by
      have h1 : Nd.R.f = 2 * Nd.R.ord := rfl
      have h2 := Nd.R.ord_pos
      omega
    exact_mod_cast this
  have hm : (1 : ℝ) ≤ Nd.R.m := by
    have := Nd.R.two_le_m
    exact_mod_cast (show 1 ≤ Nd.R.m by omega)
  have hb := Nd.one_le_b
  have hx : 1 ≤ Nd.sc.x ^ Nd.sc.eps := Real.one_le_rpow Nd.sc.one_lt_alt.le Nd.sc.eps_pos.le
  have h1 := one_le_mul_of_one_le_of_one_le hf hm
  have h2 := one_le_mul_of_one_le_of_one_le h1 hb
  exact one_le_mul_of_one_le_of_one_le h2 hx

theorem NumDatum.one_le_m_unitE (Nd : NumDatum) {Nc : ℝ} (hNc : 0 ≤ Nc) : 1 ≤ (Nd.R.m : ℝ) * Nd.unitE Nc := by
  unfold NumDatum.unitE
  have hm : (1 : ℝ) ≤ Nd.R.m := by
    have := Nd.R.two_le_m
    exact_mod_cast (show 1 ≤ Nd.R.m by omega)
  have hx : 1 ≤ Nd.sc.x ^ Nd.sc.eps := Real.one_le_rpow Nd.sc.one_lt_alt.le Nd.sc.eps_pos.le
  have hB : 1 ≤ Nd.B0 + Nc := by linarith [Nd.one_le_B0]
  exact one_le_mul_of_one_le_of_one_le hm (one_le_mul_of_one_le_of_one_le hx hB)

section Scale

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

def ZscOfNum (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (Nd : NumDatum) (eJ : A.fam.base.J ≃ Fin Nd.R.m)
    (Nc : ℝ) (Zs : DefSub A.fam.amb) : IndefScale A.fam.base where
  F0 y j := Nd.Fj ((eJ j).1 + 1) y
  J0 t y j := ((A.fam.JJ P0 ψ0 Zs j t y : ℚ) : ℝ)
  E1u := Nd.unitE Nc
  l3m j := ∑ ρ : RPl Nd.R, (((Nd.R.k : ℝ) + (((eJ j).1 + 1 : ℕ) : ℝ) - 1) - ((Nd.R.m : ℝ) - (((eJ j).1 + 1 : ℕ) : ℝ))) *
    Nd.w ((eJ j).1 + 1) ρ * Nd.logOm
  l3u := Nd.B0 * Real.log (Real.log Nd.sc.x)
  l6m j := ∑ ρ : RPl Nd.R, Nd.logHook ((eJ j).1 + 1) ρ
  l6u := (Nd.R.f : ℝ) * (Nd.R.nV : ℝ) ^ 2 * Nd.Lp
  x := Nd.sc.x
  b := Nd.sc.b
  la := Real.log (Fintype.card G)
  de := 8 * (Nd.R.f : ℝ) * (Nd.R.r : ℝ) / ((min (Nd.g 0) (Nd.g 1) : ℕ) : ℝ)

variable (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (Nd : NumDatum) (eJ : A.fam.base.J ≃ Fin Nd.R.m) (Nc : ℝ)

def dgOf (hT : Finite T) : ℕ :=
  letI := Fintype.ofFinite T
  Finset.univ.lcm fun p : Fin m × T => (A.fam.L p.1 p.2).DG (A.fam.lvlA P0 ψ0)

theorem dgOf_dvd (hT : Finite T) (j : Fin m) (t : T) : (A.fam.L j t).DG (A.fam.lvlA P0 ψ0) ∣ dgOf A P0 ψ0 hT := by
  letI := Fintype.ofFinite T
  exact Finset.dvd_lcm (f := fun p : Fin m × T => (A.fam.L p.1 p.2).DG (A.fam.lvlA P0 ψ0)) (Finset.mem_univ (j, t))

theorem dgOf_pos (hT : Finite T) : 0 < dgOf A P0 ψ0 hT := by
  letI := Fintype.ofFinite T
  have hpos : ∀ j t, 0 < (A.fam.L j t).DG (A.fam.lvlA P0 ψ0) := by
    intro j t
    unfold BlockDat.DG
    refine Nat.mul_pos Nat.card_pos (Nat.pos_of_ne_zero ?_)
    unfold CSD.DGam
    rw [Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨c, -, hc⟩
    exact (Fintype.card_pos (α := ((A.fam.L j t).S.Gam c))).ne' hc
  refine Nat.pos_of_ne_zero ?_
  unfold dgOf
  rw [Ne, Finset.lcm_eq_zero_iff]
  rintro ⟨p, -, hp⟩
  exact (hpos p.1 p.2).ne' hp

end Scale

section Q

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1}
  {Sp : SPer Dc} {N : IndefNum Bs}

def QOf (P : IndefCore Df0 Df1 Dc Sp N) (LG E3 : ℝ) (E2 : Bs.J → ℝ) : ℝ :=
  max 1 (boundB P LG E3 E2 + N.hh + 28 * N.la)

end Q

section Sizes

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
variable (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (Nd : NumDatum) (eJ : A.fam.base.J ≃ Fin Nd.R.m) (Nc : ℝ)

def LamSizeAt (s : ℕ) (cG : ℝ) : Prop :=
  Real.log (Fintype.card G) + Real.log (s : ℝ) ≤ cG * ((Nd.R.m : ℝ) * Nd.unitE Nc)

def DGamSize (hT : Finite T) (s : ℕ) (cD : ℝ) : Prop :=
  Real.log (dgOf A P0 ψ0 hT : ℝ) + Real.log (s : ℝ) ≤ cD * Nd.unitE Nc

end Sizes

section Assemble

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

end Assemble

end Formalism.L2.DIV
end
end

