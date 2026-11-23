module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LatIndexEqOneOfMem
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift.Model

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem coef_one (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (h : VecNe R i t) (μ) (𝓕)
    (hμ : IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕) : coef R i t μ 𝓕 1 = 1 := by
  unfold coef
  have : R.ωP i t (1, 1) = 1 := map_one _
  rw [this]
  exact div_self (h μ 𝓕 hμ).1

theorem pureTensor_one (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : R.ptP i t 1 = R.vP i t := by
  unfold RealDat.ptP pureTensorO pureTensorL
  have : (1 : MvPolynomial (FVar D (Wc D i).rank (Vc D i).rank) ℂ) = MvPolynomial.basisMonomials _ ℂ 0 := by
    simp
  rw [this, Module.Basis.constr_basis]
  simp [opPow]

theorem coef_mul_lev (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (h : LevFix R i t) (μ) (𝓕) (g k : GA D (Wc D i))
    (hk : k ∈ levW R i) : coef R i t μ 𝓕 (g * k) = coef R i t μ 𝓕 g := by
  unfold coef
  have e : R.ωP i t (1, g * k) = R.ωP i t (1, g) * R.ωP i t (1, k) := by rw [← map_mul]; simp
  have hv := h k hk 1
  rw [pureTensor_one] at hv
  rw [e, Module.End.mul_apply, hv]

theorem trivAt_one (V : HSp D) (f : AE D) : TrivAt V f 1 ∧ SuppF V f 1 := by
  have : Formalism.L2.Theta.mt V 1 = 1 := rfl
  constructor <;> intro a b <;> simp [this]

end GlobalTheory.RawLift.Model

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NegOneNotMemNatLat
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.RSJ.Model

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def eLast (R : Type*) [CommRing R] (a : ℕ) : Fin a → R := fun i => if (i : ℕ) + 1 = a then 1 else 0

theorem secRow_eLast {R : Type*} [CommRing R] : secRow (eLast R a) = 1 := by
  ext i j
  simp only [secRow, eLast, Matrix.of_apply, Matrix.one_apply]
  by_cases h : (i : ℕ) + 1 = a
  · rw [if_pos h]
    by_cases h2 : (j : ℕ) + 1 = a
    · rw [if_pos h2, if_pos (Fin.ext (by omega))]
    · rw [if_neg h2, if_neg (fun e : i = j => h2 (e ▸ h))]
  · rw [if_neg h]



omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem secInv_eLast : secInv (eLast (Cinf E) a) = 1 := by
  unfold secInv
  split_ifs with h
  · rw [inv_eq_one]; exact Units.ext secRow_eLast
  · rfl


omit [_root_.NumberField.IsTotallyComplex E] in
theorem detPow_mul (x : ℝ) (g h : GA E a) : detPow E a x (g * h) = detPow E a x g * detPow E a x h := by
  simp [detPow]



omit [_root_.NumberField.IsTotallyComplex E] in
theorem detPow_ratGL (x : ℝ) (γ : GL (Fin a) E) : detPow E a x (ratGL E a γ) = 1 := by
  have h : Matrix.GeneralLinearGroup.det (ratGL E a γ) = diagUnits E (Matrix.GeneralLinearGroup.det γ) :=
    Units.ext (det_map (algebraMap E (Ad E)) γ)
  have h2 := (GlobalTheory.HeckeGal.Model.absPow E x).2.2 (Matrix.GeneralLinearGroup.det γ)
  unfold detPow chiDet
  rw [MonoidHom.comp_apply, h, h2]; simp








end GlobalTheory.RSJ.Model
end
end

