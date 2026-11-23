module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0087
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerDefectPadicOfComplex
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

namespace GlobalTheory.FrobStickMap

theorem hasSubst_of_cc {R : Type*} [CommRing R] (a : MvPowerSeries (Fin 3) R)
    (ha : MvPowerSeries.constantCoeff a = 0) : PowerSeries.HasSubst a :=
  PowerSeries.HasSubst.of_constantCoeff_zero ha

theorem map_defect {R S : Type*} [CommRing R] [CommRing S] (h : R →+* S)
    (f : Fin 3 → R⟦X⟧) (s : R⟦X⟧) :
    MvPowerSeries.map h (GlobalTheory.FrobStick.defect f s)
      = GlobalTheory.FrobStick.defect (fun j => PowerSeries.map h (f j)) (PowerSeries.map h s) := by
  have hs : ∀ (a : MvPowerSeries (Fin 3) R), MvPowerSeries.constantCoeff a = 0 → ∀ g : R⟦X⟧,
      MvPowerSeries.map h (subst a g) = subst (MvPowerSeries.map h a) (PowerSeries.map h g) :=
    fun a ha g => PowerSeries.map_subst (hasSubst_of_cc a ha) g
  unfold GlobalTheory.FrobStick.defect
  rw [map_sub, map_mul, map_mul, map_mul, map_mul, map_ofNat]
  rw [RingHom.map_det]
  congr 1
  · congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    rw [hs _ (by simp) _]
    simp
  · rw [hs _ (by simp), hs _ (by simp), hs _ (by simp), hs _ (by simp)]
    simp [map_add (f := _), map_sub]

end GlobalTheory.FrobStickMap

namespace GlobalTheory.FrobStickMap

noncomputable def tq (F : ℂ → ℂ) : (↥Qbar)⟦X⟧ :=
  PowerSeries.mk (fun n => if h : coef1 F n ∈ Qbar then ⟨_, h⟩ else 0)

theorem map_tq_of_algEnt (F : ℂ → ℂ) (hF : AlgEnt F) :
    PowerSeries.map (algebraMap (↥Qbar) ℂ) (tq F) = GlobalTheory.FrobStick.tay F := by
  ext n
  simp only [tq, GlobalTheory.FrobStick.tay, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  rw [dite_eq_left (hF.2 n)]
  rfl

theorem mvmap_injective {R S : Type*} [CommRing R] [CommRing S] (h : R →+* S)
    (hi : Function.Injective h) :
    Function.Injective (MvPowerSeries.map (σ := Fin 3) h) := by
  intro a b hab
  ext n
  apply hi
  have := congrArg (MvPowerSeries.coeff n) hab
  simpa [MvPowerSeries.coeff_map] using this

theorem defect_ser1_eq_zero_of_defect_tay_eq_zero (p : ℕ) [Fact p.Prime] (lam : (↥Qbar) →+* ℂ_[p]) (f : Fin 3 → ℂ → ℂ)
    (s : ℂ → ℂ) (hf : ∀ j, AlgEnt (f j)) (hs : AlgEnt s)
    (h0 : GlobalTheory.FrobStick.defect (fun j => GlobalTheory.FrobStick.tay (f j)) (GlobalTheory.FrobStick.tay s) = 0) :
    GlobalTheory.FrobStick.defect (fun j => GL3Theta.ser1 lam (f j)) (GL3Theta.ser1 lam s) = 0 := by
  have hq : GlobalTheory.FrobStick.defect (fun j => tq (f j)) (tq s) = 0 := by
    apply mvmap_injective (algebraMap (↥Qbar) ℂ) (FaithfulSMul.algebraMap_injective _ _)
    rw [map_defect, map_zero]
    simp only [map_tq_of_algEnt _ (hf _), map_tq_of_algEnt _ hs]
    exact h0
  have hser : ∀ F : ℂ → ℂ, AlgEnt F → GL3Theta.ser1 lam F = PowerSeries.map lam (tq F) := fun F hF =>
    GlobalTheory.EvenTheta.Param.theta_series_map_coefficients lam F (tq F) (map_tq_of_algEnt F hF).symm
  simp only [hser _ (hf _), hser _ hs]
  rw [← map_defect, hq, map_zero]

end GlobalTheory.FrobStickMap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerDefectSubstFormalGroupLog
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

noncomputable section

namespace GlobalTheory.FrobStick.SubstLog

variable {p : ℕ} [Fact p.Prime]

theorem cc_lg (g : GL3Theta.G1 p) {x : MvPowerSeries (Fin 3) ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0) :
    MvPowerSeries.constantCoeff (g.lg x) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hx _ (GlobalTheory.SerTransport.const_l g)

theorem cc_pt {g : GL3Theta.G1 p} (hg : g.Ok) {x : MvPowerSeries (Fin 3) ℂ_[p]}
    (hx : MvPowerSeries.constantCoeff x = 0) : MvPowerSeries.constantCoeff (g.pt x) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hx _ hg.2.2.1

theorem lg_pt {g : GL3Theta.G1 p} (hg : g.Ok) {x : MvPowerSeries (Fin 3) ℂ_[p]}
    (hx : MvPowerSeries.constantCoeff x = 0) : g.lg (g.pt x) = x := by
  have hx' : PowerSeries.HasSubst x := PowerSeries.HasSubst.of_constantCoeff_zero hx
  have he : PowerSeries.HasSubst g.ex := PowerSeries.HasSubst.of_constantCoeff_zero' hg.2.2.1
  unfold GL3Theta.G1.lg GL3Theta.G1.pt
  rw [← PowerSeries.subst_comp_subst_apply he hx', hg.2.2.2, PowerSeries.subst_X hx']

theorem cc_sum (g : GL3Theta.G1 p) {x y : MvPowerSeries (Fin 3) ℂ_[p]}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.constantCoeff (g.lg x + g.lg y) = 0 := by
  rw [map_add (f := _), cc_lg g hx, cc_lg g hy, add_zero]

theorem cc_diff (g : GL3Theta.G1 p) {x y : MvPowerSeries (Fin 3) ℂ_[p]}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.constantCoeff (g.lg x - g.lg y) = 0 := by
  rw [map_sub, cc_lg g hx, cc_lg g hy, sub_zero]

theorem cc_Cl (g : GL3Theta.G1 p) (c : ℂ_[p]) : PowerSeries.constantCoeff (PowerSeries.C c * g.l) = 0 := by
  rw [map_mul, GlobalTheory.SerTransport.const_l, mul_zero]

theorem subst_Cl (g : GL3Theta.G1 p) (c : ℂ_[p]) {w : MvPowerSeries (Fin 3) ℂ_[p]}
    (hw : MvPowerSeries.constantCoeff w = 0) (h : PowerSeries ℂ_[p]) :
    (PowerSeries.subst w (PowerSeries.subst (PowerSeries.C c * g.l) h : PowerSeries ℂ_[p]) :
        MvPowerSeries (Fin 3) ℂ_[p]) =
      PowerSeries.subst (MvPowerSeries.C c * g.lg w) h := by
  have hw' : PowerSeries.HasSubst w := PowerSeries.HasSubst.of_constantCoeff_zero hw
  rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' (cc_Cl g c)) hw',
    PowerSeries.subst_mul hw', PowerSeries.subst_C]
  rfl

theorem hom_subst {a : Fin 3 → MvPowerSeries (Fin 3) ℂ_[p]} (ha : MvPowerSeries.HasSubst a)
    {y : MvPowerSeries (Fin 3) ℂ_[p]} (hy : MvPowerSeries.constantCoeff y = 0) (h : PowerSeries ℂ_[p]) :
    MvPowerSeries.substAlgHom (R := ℂ_[p]) ha (PowerSeries.subst y h) =
      PowerSeries.subst (MvPowerSeries.substAlgHom (R := ℂ_[p]) ha y) h := by
  rw [MvPowerSeries.coe_substAlgHom]
  exact MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hy).const ha h

theorem formula_at {a : Fin 3 → MvPowerSeries (Fin 3) ℂ_[p]}
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (f : Fin 3 → PowerSeries ℂ_[p]) (s : PowerSeries ℂ_[p])
    (h : GlobalTheory.FrobStick.defect f s = 0) :
    Matrix.det (Matrix.of fun i j => (PowerSeries.subst (a i) (f j) : MvPowerSeries (Fin 3) ℂ_[p])) =
      2 * PowerSeries.subst (a 0 + a 1 + a 2) s * PowerSeries.subst (a 0 - a 1) s *
        PowerSeries.subst (a 1 - a 2) s * PowerSeries.subst (a 2 - a 0) s := by
  have ha : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hX : ∀ i, MvPowerSeries.substAlgHom (R := ℂ_[p]) ha (MvPowerSeries.X i) = a i := fun i => by
    rw [MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X ha]
  have h1 := congrArg (MvPowerSeries.substAlgHom (R := ℂ_[p]) ha) (sub_eq_zero.mp h)
  rw [AlgHom.map_det, map_mul, map_mul, map_mul, map_mul, map_ofNat, hom_subst ha (by simp),
    hom_subst ha (by simp), hom_subst ha (by simp), hom_subst ha (by simp)] at h1
  simp only [map_add (f := _), map_sub, hX] at h1
  rw [← h1]
  congr 1
  ext1 i j
  simp only [Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply]
  rw [hom_subst ha (by simp), hX]

theorem subst_log_formula : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → MvPowerSeries.constantCoeff (g.add (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1)) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ MvPowerSeries.constantCoeff (g.sub (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ MvPowerSeries.constantCoeff (g.sub (GL3Theta.Xv 1) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ MvPowerSeries.constantCoeff (g.sub (GL3Theta.Xv 2) (GL3Theta.Xv 0) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ ∀ (c : ℂ_[p]) (f : Fin 3 → PowerSeries ℂ_[p]) (s : PowerSeries ℂ_[p]), GlobalTheory.FrobStick.defect f s = 0 → Matrix.det (Matrix.of fun i j => (PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) (f j) : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 3) ℂ_[p])) = 2 * PowerSeries.subst (g.add (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1)) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) * PowerSeries.subst (g.sub (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) * PowerSeries.subst (g.sub (GL3Theta.Xv 1) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) * PowerSeries.subst (g.sub (GL3Theta.Xv 2) (GL3Theta.Xv 0) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) := by
  intro p _ g hg
  have hX : ∀ i : Fin 3, MvPowerSeries.constantCoeff (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have h01 : MvPowerSeries.constantCoeff
      (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := cc_pt hg (cc_sum g (hX 0) (hX 1))
  have hs : MvPowerSeries.constantCoeff
      (g.add (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1)) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    cc_pt hg (cc_sum g h01 (hX 2))
  have hd : ∀ i j : Fin 3, MvPowerSeries.constantCoeff
      (g.sub (GL3Theta.Xv i) (GL3Theta.Xv j) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    fun i j => cc_pt hg (cc_diff g (hX i) (hX j))
  refine ⟨hs, hd 0 1, hd 1 2, hd 2 0, fun c f s h => ?_⟩
  have ld : ∀ i j : Fin 3, g.lg (g.sub (GL3Theta.Xv i) (GL3Theta.Xv j) : MvPowerSeries (Fin 3) ℂ_[p]) =
      g.lg (GL3Theta.Xv i) - g.lg (GL3Theta.Xv j) := fun i j => lg_pt hg (cc_diff g (hX i) (hX j))
  have l01 : g.lg (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 3) ℂ_[p]) =
      g.lg (GL3Theta.Xv 0) + g.lg (GL3Theta.Xv 1) := lg_pt hg (cc_sum g (hX 0) (hX 1))
  have ls : g.lg (g.add (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1)) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) =
      g.lg (GL3Theta.Xv 0) + g.lg (GL3Theta.Xv 1) + g.lg (GL3Theta.Xv 2) := by
    rw [← l01]; exact lg_pt hg (cc_sum g h01 (hX 2))
  have key := formula_at (a := fun i => MvPowerSeries.C c * g.lg (GL3Theta.Xv i))
    (fun i => by rw [map_mul, cc_lg g (hX i), mul_zero]) f s h
  simp only [subst_Cl g c (hX _), subst_Cl g c hs, subst_Cl g c (hd _ _), ld, ls, mul_add, mul_sub]
  exact key

end GlobalTheory.FrobStick.SubstLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerDeterminantDefectOnLine
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

namespace GlobalTheory.FrobStick

theorem hasSubst_line {R : Type} [CommRing R] (t : Fin 3 → R) :
    MvPowerSeries.HasSubst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
    rw [map_mul]; exact mul_eq_zero_of_right _ (PowerSeries.constantCoeff_X (R := R))

theorem subst_line_subst {R : Type} [CommRing R] (t : Fin 3 → R) (a : MvPowerSeries (Fin 3) R)
    (ha : MvPowerSeries.constantCoeff a = 0) (f : PowerSeries R) :
    (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R))
      (PowerSeries.subst a f : MvPowerSeries (Fin 3) R) : PowerSeries R) =
      PowerSeries.subst (MvPowerSeries.subst
        (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R)) a : PowerSeries R) f := by
  have has : MvPowerSeries.HasSubst (fun _ : Unit => a) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => ha
  rw [PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply has (hasSubst_line t)]
  rfl

theorem subst_C_mul_X {R : Type} [CommRing R] (c : R) (f : PowerSeries R) :
    PowerSeries.subst (PowerSeries.C c * PowerSeries.X : PowerSeries R) f = PowerSeries.rescale c f := by
  rw [PowerSeries.rescale_eq_subst, PowerSeries.smul_eq_C_mul]

end GlobalTheory.FrobStick

namespace GlobalTheory.FrobStick

theorem defect_line (R : Type) [CommRing R] (f : Fin 3 → PowerSeries R) (s : PowerSeries R)
    (t : Fin 3 → R) :
    (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R))
      (GlobalTheory.FrobStick.defect f s) : PowerSeries R) =
      Matrix.det (Matrix.of fun i j => PowerSeries.rescale (t i) (f j)) -
        2 * PowerSeries.rescale (t 0 + t 1 + t 2) s * PowerSeries.rescale (t 0 - t 1) s *
          PowerSeries.rescale (t 1 - t 2) s * PowerSeries.rescale (t 2 - t 0) s := by
  have hb := hasSubst_line t
  have hlin : ∀ (a : MvPowerSeries (Fin 3) R) (c : R), MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R)) a =
        (PowerSeries.C c * PowerSeries.X : PowerSeries R) → ∀ g : PowerSeries R,
      (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R))
        (PowerSeries.subst a g : MvPowerSeries (Fin 3) R) : PowerSeries R) = PowerSeries.rescale c g := by
    intro a c ha h g
    rw [subst_line_subst t a ha, h, subst_C_mul_X]
  have hX : ∀ i, MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R))
      (MvPowerSeries.X i : MvPowerSeries (Fin 3) R) = (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R) :=
    fun i => MvPowerSeries.subst_X hb i
  unfold defect
  rw [← MvPowerSeries.coe_substAlgHom hb]
  simp only [map_sub, map_mul, AlgHom.map_det]

  have hmat : (MvPowerSeries.substAlgHom hb).mapMatrix
      (Matrix.of fun i j => (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) R) (f j) :
        MvPowerSeries (Fin 3) R)) = Matrix.of fun i j => PowerSeries.rescale (t i) (f j) := by
    refine Matrix.ext fun i j => ?_
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPowerSeries.coe_substAlgHom]
    exact hlin _ _ (MvPowerSeries.constantCoeff_X i) (hX i) _
  rw [hmat, map_ofNat]
  simp only [MvPowerSeries.coe_substAlgHom]
  have h3 : MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R))
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2 : MvPowerSeries (Fin 3) R) =
      (PowerSeries.C (t 0 + t 1 + t 2) * PowerSeries.X : PowerSeries R) := by
    rw [MvPowerSeries.subst_add hb, MvPowerSeries.subst_add hb, hX, hX, hX, map_add (f := _), map_add (f := _), add_mul, add_mul]
  have hd : ∀ i j : Fin 3, MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R))
      (MvPowerSeries.X i - MvPowerSeries.X j : MvPowerSeries (Fin 3) R) =
      (PowerSeries.C (t i - t j) * PowerSeries.X : PowerSeries R) := by
    intro i j
    rw [MvPowerSeries.subst_sub hb, hX, hX, map_sub, sub_mul]
  have c3 : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2 : MvPowerSeries (Fin 3) R) = 0 := by
    simp
  have cd : ∀ i j : Fin 3, MvPowerSeries.constantCoeff
      (MvPowerSeries.X i - MvPowerSeries.X j : MvPowerSeries (Fin 3) R) = 0 := by
    intro i j; simp
  rw [hlin _ _ c3 h3, hlin _ _ (cd 0 1) (hd 0 1), hlin _ _ (cd 1 2) (hd 1 2), hlin _ _ (cd 2 0) (hd 2 0)]

end GlobalTheory.FrobStick
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerSigmaStarDetComplex
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

noncomputable section

namespace GlobalTheory.FrobStick

theorem sgStar_cube_det_cplx : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ v : ℂ, v ∉ Λ → ∀ z : Fin 3 → ℂ, Matrix.det (Matrix.of fun i j => ![GlobalTheory.FrobStick.colA Λ, GlobalTheory.FrobStick.colB Λ v, GlobalTheory.FrobStick.colC Λ v] j (z i)) = 2 * sgStar Λ (z 0 + z 1 + z 2) * sgStar Λ (z 0 - z 1) * sgStar Λ (z 1 - z 2) * sgStar Λ (z 2 - z 0) := by
  intro Λ hΛ v hv z
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hΛ
  have hΛL : Λ = L.lattice.toAddSubgroup := AddSubgroup.ext hL
  have hσ : sgStar Λ = Formalism.L2.Th1.F.sgStar L := by rw [hΛL]; exact GlobalTheory.JetsGenusOne.sgStar_eq L
  have hwp : wpF Λ = L.weierstrassP := funext (GlobalTheory.OddTheta.wpF_eq L Λ hL)
  have hsd : Differentiable ℂ (sgStar Λ) := hΛ.differentiable
  have hopen : IsOpen ((Λ : Set ℂ)ᶜ) := by
    have : (Λ : Set ℂ) = (L.lattice : Set ℂ) := Set.ext fun w => hL w
    rw [this]; exact L.isClosed_lattice.isOpen_compl
  have hB : ∀ w, w ∉ Λ → colB Λ v w = sgStar Λ w ^ 3 * L.weierstrassP w := by
    intro w hw
    rw [colB, hΛ.sqTh_eq hv hw, ← hwp]
    ring
  have hC : ∀ w, w ∉ Λ → colC Λ v w = sgStar Λ w ^ 3 * L.derivWeierstrassP w := by
    intro w hw
    have hwL : w ∉ L.lattice := fun h => hw ((hL w).2 h)
    have hpd : HasDerivAt L.weierstrassP (L.derivWeierstrassP w) w := by
      have h1 : DifferentiableAt ℂ L.weierstrassP w :=
        L.differentiableOn_weierstrassP.differentiableAt (L.isClosed_lattice.isOpen_compl.mem_nhds hwL)
      have h2 := h1.hasDerivAt
      rwa [L.deriv_weierstrassP] at h2
    have hev : sqTh Λ v =ᶠ[nhds w] fun u => sgStar Λ u ^ 2 * (L.weierstrassP u - wpF Λ v) := by
      filter_upwards [hopen.mem_nhds hw] with u hu
      rw [hΛ.sqTh_eq hv hu, hwp]
    have hd : HasDerivAt (fun u => sgStar Λ u ^ 2 * (L.weierstrassP u - wpF Λ v))
        ((2 : ℕ) * sgStar Λ w ^ (2 - 1) * deriv (sgStar Λ) w * (L.weierstrassP w - wpF Λ v) +
          sgStar Λ w ^ 2 * L.derivWeierstrassP w) w :=
      ((hsd w).hasDerivAt.pow 2).mul (hpd.sub_const _)
    rw [colC, hev.deriv_eq, hd.deriv, hΛ.sqTh_eq hv hw, hwp]
    push_cast
    ring
  have hoff : ∀ y : Fin 3 → ℂ, (∀ i, y i ∉ Λ) →
      Matrix.det (Matrix.of fun i j => ![colA Λ, colB Λ v, colC Λ v] j (y i)) =
        2 * sgStar Λ (y 0 + y 1 + y 2) * sgStar Λ (y 0 - y 1) * sgStar Λ (y 1 - y 2) * sgStar Λ (y 2 - y 0) := by
    intro y hy
    have h := Formalism.L2.Th1.F.sgStarThree L (y 0) (y 1) (y 2)
      (fun h => hy 0 ((hL _).2 h)) (fun h => hy 1 ((hL _).2 h)) (fun h => hy 2 ((hL _).2 h))
    rw [← hσ] at h
    rw [Matrix.det_fin_three] at h ⊢
    simp [Matrix.vecHead, Matrix.vecTail] at h ⊢
    rw [hB _ (hy 0), hB _ (hy 1), hB _ (hy 2), hC _ (hy 0), hC _ (hy 1), hC _ (hy 2)]
    simp only [colA]
    linear_combination h
  have hcA : Continuous (colA Λ) := by
    have := hsd.continuous
    unfold colA; fun_prop
  have hcB : Continuous (colB Λ v) := by
    have := (hΛ.differentiable_sqTh v).continuous
    have := hsd.continuous
    unfold colB; fun_prop
  have hcC : Continuous (colC Λ v) := by
    have h1 : Continuous (deriv (sqTh Λ v)) :=
      ((hΛ.differentiable_sqTh v).contDiff (n := 1)).continuous_deriv le_rfl
    have h2 : Continuous (deriv (sgStar Λ)) := (hsd.contDiff (n := 1)).continuous_deriv le_rfl
    have := (hΛ.differentiable_sqTh v).continuous
    have := hsd.continuous
    unfold colC; fun_prop
  have hcL : Continuous fun y : Fin 3 → ℂ =>
      Matrix.det (Matrix.of fun i j => ![colA Λ, colB Λ v, colC Λ v] j (y i)) := by
    refine Continuous.matrix_det ?_
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.of_apply]
    fin_cases j
    · exact hcA.comp (continuous_apply i)
    · exact hcB.comp (continuous_apply i)
    · exact hcC.comp (continuous_apply i)
  have hcR : Continuous fun y : Fin 3 → ℂ =>
      2 * sgStar Λ (y 0 + y 1 + y 2) * sgStar Λ (y 0 - y 1) * sgStar Λ (y 1 - y 2) * sgStar Λ (y 2 - y 0) := by
    have := hsd.continuous
    fun_prop
  have hdense : Dense {y : Fin 3 → ℂ | ∀ i, y i ∉ Λ} := by
    have := dense_pi (Set.univ : Set (Fin 3)) (s := fun _ => ((Λ : Set ℂ)ᶜ)) fun _ _ => hΛ.dense_compl
    convert this using 1
    ext y; simp
  exact congrFun (Continuous.ext_on hdense hcL hcR fun y hy => hoff y hy) z

end GlobalTheory.FrobStick
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterPowEqOneFiniteIdelesOfOrderDvd
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharOrderFin

theorem locK_pow_eq_one {L : Type} [Field L] [NumberField L] {χ : HChar L} {n : ℕ}
    (h : χ.OrderDvd n) (P : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : χ.locK P k ^ n = 1 := by
  have h1 : (χ.1 : _ →* ℂˣ) ^ n = 1 := by
    have := congrArg Subtype.val h
    simpa using this
  have h2 : ∀ y, χ.1 y ^ n = 1 := fun y => by
    have := DFunLike.congr_fun h1 y
    simpa [MonoidHom.pow_apply] using this
  exact h2 _

theorem char_pow_eq_one_of_orderDvd : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E),
    ChrEq c χ → ∀ n : ℕ, χ.OrderDvd n → ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → c x ^ n = 1 := by
  intro D c χ hc n hn x hx
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h4 := _root_.GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 h4 c χ hc
  let y : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ :=
    ⟨ι (finPart D (x : AE D)), ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)),
      by rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one],
      by rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]⟩
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN y
  have h5 := hprod x hx S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS'
  apply Circle.ext
  have h6 : ((c x ^ n : Circle) : ℂ) = ((c x : Circle) : ℂ) ^ n :=
    map_pow Circle.coeHom (c x) n
  rw [h6, h5, ← Finset.prod_pow, Circle.coe_one]
  refine Finset.prod_eq_one fun P _ => ?_
  rw [← Units.val_pow_eq_pow_val, locK_pow_eq_one hn, Units.val_one]

end GlobalTheory.CharOrderFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelLocallyFiniteContinuous
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary Topology

namespace GlobalTheory.AutomorphicL2KernelContinuous

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  {Γ : Subgroup G} [DiscreteTopology Γ] {f : G → ℂ}

theorem finite_contributing (hc : HasCompactSupport f) {C C' : Set G} (hC : IsCompact C) (hC' : IsCompact C') :
    {γ : Γ | ∃ x ∈ C, ∃ y ∈ C', f (x⁻¹ * γ * y) ≠ 0}.Finite := by
  have hK := (hC.prod (hc.isCompact.prod hC')).image (f := fun p : G × G × G => p.1 * p.2.1 * p.2.2⁻¹) (by fun_prop)
  refine (finite_mem_compact (Γ := Γ) hK).subset ?_
  rintro γ ⟨x, hx, y, hy, h⟩
  exact ⟨(x, x⁻¹ * γ * y, y), ⟨hx, subset_tsupport f h, hy⟩, by simp [mul_assoc]⟩

theorem locallyFinite_support [LocallyCompactSpace G] (hc : HasCompactSupport f) :
    LocallyFinite fun γ : Γ => Function.support fun p : G × G => f (p.1⁻¹ * γ * p.2) := by
  rintro ⟨x, y⟩
  obtain ⟨C, hC, hx⟩ := exists_compact_mem_nhds x
  obtain ⟨C', hC', hy⟩ := exists_compact_mem_nhds y
  refine ⟨C ×ˢ C', prod_mem_nhds hx hy, (finite_contributing hc hC hC').subset ?_⟩
  rintro γ ⟨p, h, h1, h2⟩
  exact ⟨p.1, h1, p.2, h2, h⟩

theorem continuous_kernel [LocallyCompactSpace G] (hf : Continuous f) (hc : HasCompactSupport f) :
    Continuous fun p : G × G => kernel Γ f p.1 p.2 := by
  have h : Continuous fun p : G × G => ∑ᶠ γ : Γ, f (p.1⁻¹ * γ * p.2) :=
    continuous_finsum (fun γ => by fun_prop) (locallyFinite_support hc)
  refine h.congr fun p => ?_
  exact (tsum_eq_finsum (finite_support_kernel hc p.1 p.2)).symm

end GlobalTheory.AutomorphicL2KernelContinuous
end

