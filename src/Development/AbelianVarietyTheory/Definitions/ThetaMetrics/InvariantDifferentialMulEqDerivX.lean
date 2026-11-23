module

public import Mathlib
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0005

@[expose] public section

noncomputable section

open Formalism.L2.Th1.A ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

universe u v

namespace GlobalTheory.WeierstrassFormal

section Series

open PowerSeries

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

theorem w_eq : wSer W = X ^ 3 + C W.a₁ * X * wSer W + C W.a₂ * X ^ 2 * wSer W + C W.a₃ * wSer W ^ 2
    + C W.a₄ * X * wSer W ^ 2 + C W.a₆ * wSer W ^ 3 := (wSerSpec R W).1.2

theorem w_eq_X_pow_mul : wSer W = X ^ 3 * wU W ∧ constantCoeff (wU W) = 1 :=
  ⟨(wSerFactor R W).1, (wSerFactor R W).2.1⟩

theorem wU_eq : wU W = 1 + C W.a₁ * X * wU W + C W.a₂ * X ^ 2 * wU W + C W.a₃ * X ^ 3 * wU W ^ 2
    + C W.a₄ * X ^ 4 * wU W ^ 2 + C W.a₆ * X ^ 6 * wU W ^ 3 := by
  have h := w_eq W
  rw [(w_eq_X_pow_mul W).1] at h
  refine X_pow_mul_cancel (k := 3) ?_
  linear_combination h

theorem coeff_one_wU : coeff 1 (wU W) = W.a₁ := by
  have h : wU W = 1 + X * (C W.a₁ * wU W + X * (C W.a₂ * wU W + C W.a₃ * X * wU W ^ 2
      + C W.a₄ * X ^ 2 * wU W ^ 2 + C W.a₆ * X ^ 4 * wU W ^ 3)) := by
    linear_combination wU_eq W
  rw [h, map_add (f := _), coeff_succ_X_mul]
  simp [(w_eq_X_pow_mul W).2, coeff_one]

variable (φ : R →+* S)

end Series

section Group

open MvPowerSeries

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

def formalGroup : FormalGroup R where
  toPowerSeries := fgl W
  zero_constantCoeff := (fglChord R W).2.2.2.2.1
  lin_coeff_X := (fglChord R W).2.2.2.2.2.1
  lin_coeff_Y := (fglChord R W).2.2.2.2.2.2
  assoc := by
    obtain ⟨F, hF, -⟩ := fglGroup R W
    rw [← hF]
    exact F.assoc

@[simp] theorem formalGroup_toPowerSeries : (formalGroup W).toPowerSeries = fgl W := rfl

theorem chord (i : Fin 2) : (wSer W).subst (X i : MvPowerSeries (Fin 2) R) = lam W * X i + nu W := by
  have := Fgl2.nu_eq W i
  change _ = (wSer W).subst (X i : MvPowerSeries (Fin 2) R) - _ at this
  linear_combination -this

theorem third_point : constantCoeff (uThird W) = 0 ∧
    (wSer W).subst (uThird W) = lam W * uThird W + nu W ∧
    cThree W * (X 0 + X 1 + uThird W) + cTwo W = 0 ∧
    (formalGroup W).toPowerSeries = (iSer W).subst (uThird W) :=
  ⟨(fglChord R W).2.1, (fglChord R W).2.2.1.symm, Fgl2.third_rel W 0 1 (by decide),
    (fglChord R W).2.2.2.1⟩

variable {σ : Type*}

theorem map_zsmul (φ : R →+* S) (n : ℤ) : PowerSeries.map φ (zSer W n) = zSer (W.map φ) n :=
  zSerMap R S φ W n

end Group

section Law

open MvPowerSeries

variable {R S : Type} [CommRing R] [CommRing S]

variable (W : WeierstrassCurve R)

end Law

section Points

open MvPowerSeries WeierstrassCurve WeierstrassCurve.Projective GlobalTheory.AddLaw

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) {σ : Type*}

abbrev seriesCurve (σ : Type*) : WeierstrassCurve.Projective (MvPowerSeries σ R) :=
  W.map (C : R →+* MvPowerSeries σ R)

def point (s : MvPowerSeries σ R) : Fin 3 → MvPowerSeries σ R := ![s, -1, (wSer W).subst s]

theorem equation_point {s : MvPowerSeries σ R} (hs : PowerSeries.HasSubst s) :
    (seriesCurve W σ).Equation (point W s) := by
  have h := congrArg (PowerSeries.substAlgHom (R := R) hs) (w_eq W)
  simp only [map_add (f := _), map_mul, map_pow, PowerSeries.substAlgHom_X] at h
  simp only [PowerSeries.coe_substAlgHom, PowerSeries.subst_C] at h
  rw [equation_iff]
  simp only [point, fin3_def_ext, WeierstrassCurve.map]
  linear_combination h

variable {K : Type v} [Field K] (φ : MvPowerSeries σ R →+* K)

end Points

section Examples

open MvPowerSeries

variable {R : Type u} [CommRing R]

theorem formalGroup_singular (a : R) :
    (formalGroup (⟨a, 0, 0, 0, 0⟩ : WeierstrassCurve R)).toPowerSeries =
      X 0 + X 1 - C a * X 0 * X 1 := by
  set W : WeierstrassCurve R := ⟨a, 0, 0, 0, 0⟩ with hW
  have hw : ∀ i : Fin 2, (lam W * X i + nu W) * (1 - C a * X i) = X i ^ 3 := fun i => by
    have h := (WeierstrassCurve.Projective.equation_iff _).mp
      (equation_point W (s := (X i : MvPowerSeries (Fin 2) R)) (.of_constantCoeff_zero (by simp)))
    simp only [point, WeierstrassCurve.Projective.fin3_def_ext, WeierstrassCurve.map, chord W i] at h
    simp only [hW, map_zero] at h ⊢
    linear_combination h
  have hl : lam W * ((1 - C a * X 0) * (1 - C a * X 1)) =
      X 0 ^ 2 + X 0 * X 1 + X 1 ^ 2 - C a * X 0 * X 1 * (X 0 + X 1) :=
    sub_eq_zero.mp (Fgl1.sub_cancel (by
      linear_combination (1 - C a * X 1) * hw 0 - (1 - C a * X 0) * hw 1))
  have h3 : X 0 + X 1 + uThird W + C a * lam W = 0 := by
    simpa [cThree, cTwo, hW] using (third_point W).2.2.1
  have hd : Fgl1.dd W * invOfUnit (Fgl1.dd W) (-1) = 1 :=
    mul_invOfUnit _ _ (by
      have hc := (third_point W).1
      simp only [hW] at hc ⊢
      simp [Fgl1.dd, hc])
  have hd' : Fgl1.dd W = -1 + C a * uThird W := by simp [Fgl1.dd, hW]
  have key : uThird W = (X 0 + X 1 - C a * X 0 * X 1) * Fgl1.dd W := by
    rw [hd']
    linear_combination (1 - C a * X 0) * (1 - C a * X 1) * h3 - C a * hl
  change uThird W * invOfUnit (Fgl1.dd W) (-1) = _
  linear_combination invOfUnit (Fgl1.dd W) (-1) * key + (X 0 + X 1 - C a * X 0 * X 1) * hd

end Examples

end GlobalTheory.WeierstrassFormal
