module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CayleyTransformTrivialPhaseSkewHermitian
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0122
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DeterminantCharacterUnitaryApply
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitary
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormProdCmEmbeddingsEqOneOfInert
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThIndep
public import Formalism.LocalToGlobal.KernelLattices.KerStd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KappaOnNonsplitPrimes
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BarKHomSurjective
section
noncomputable section

open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.IdemAdj

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
def barKHom : Kinf E a →* Kinf E a where
  toFun := barK
  map_one' := Subtype.ext (by ext i j : 1; simp [barK, Matrix.one_apply])
  map_mul' k k' := Subtype.ext (by
    change Matrix.transpose (star (k.1 * k'.1)) = Matrix.transpose (star k.1) * Matrix.transpose (star k'.1)
    ext i j
    simp [Matrix.mul_apply, Matrix.star_apply, mul_comm])



omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem barK_barK (k : Kinf E a) : barK (barK k) = k := Subtype.ext (by
  ext i j
  simp [barK, Matrix.star_apply])


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem barKHom_surjective : Function.Surjective (barKHom E a) := fun k => ⟨barK k, barK_barK k⟩

def cptOn (π : CuspSub E a) : Representation ℂ (Kinf E a) π.V where
  toFun k := π.op (.cpt k)
  map_one' := by
    ext φ
    simp [CuspSub.op, act]
  map_mul' k k' := by
    ext φ
    simp [CuspSub.op, act, map_mul]

@[simp] theorem cptOn_val (π : CuspSub E a) (k : Kinf E a) (φ : π.V) :
    (cptOn π k φ).1 = cptRep E a k φ.1 := rfl

end GlobalTheory.IdemAdj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CayleyTransformIntegralUnitaryCongruentOne
section
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.CayleyCong

open GlobalTheory.Hk3.CayleyPhase GlobalTheory.Hk3.IntWitt

theorem cayley_cong : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ C : Matrix (Fin n') (Fin n') L, (∀ r s, σ (C r s) = - C s r) → (∀ r s, C r s ∈ Formalism.UG.intL L) →
    ∀ k : ℕ, 1 ≤ k →
    ∃ g : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (g : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      (∀ r s, GlobalTheory.Hk3.IntWitt.DvdPow ϖ k ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) r s - (1 : Matrix (Fin n') (Fin n') L) r s)) ∧
      ∀ r s, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) r s - (1 : Matrix (Fin n') (Fin n') L) r s -
        (ϖ ^ k • (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * C)) r s) := by
  intro L _ _ ϖ σ q hU hq n' JT hJT hermT C hskew hCI k hk
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hq
  have hσv := hU.2.1
  have hσϖ : σ ϖ = ϖ := hU.2.2.1
  have hvϖ : Valued.v ϖ < 1 := by
    rw [hU.2.2.2.1]; exact_mod_cast (show (Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) < 1 by decide)
  have hϖI : ϖ ∈ Formalism.UG.intL L := le_of_lt hvϖ
  have hvϖk : Valued.v (ϖ ^ k) < 1 := by
    rw [map_pow]; exact pow_lt_one₀ zero_le' hvϖ (by omega)
  have hhalf : Valued.v ((2 : L)⁻¹) ≤ 1 := by rw [map_inv₀, h2, inv_one]
  have hσhalf : σ ((2 : L)⁻¹) = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  set Jt : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJt
  set Jti : Matrix (Fin n') (Fin n') L := ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) with hJti
  have hJtiI : IsIntM Jti := GlobalTheory.Hk3.HoweDuality.entry_mem_of_mem_GLint (inv_mem hJT)
  have hJJi : Jt * Jti = 1 := by rw [hJt, hJti, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcJt : Formalism.UG.cT σ Jt = Jt := cT_herm σ hermT
  have hcC : Formalism.UG.cT σ C = -C := cT_skew σ hskew
  have hcJti : Formalism.UG.cT σ Jti * Jt = 1 := by
    calc Formalism.UG.cT σ Jti * Jt = Formalism.UG.cT σ Jti * Formalism.UG.cT σ Jt := by rw [hcJt]
      _ = Formalism.UG.cT σ (Jt * Jti) := (Formalism.UG.cT_mul σ _ _).symm
      _ = 1 := by rw [hJJi, Formalism.UG.cT_one]
  set M : Matrix (Fin n') (Fin n') L := Jti * C with hMdef
  have hMI : IsIntM M := isIntM_mul hJtiI hCI
  set Y : Matrix (Fin n') (Fin n') L := ϖ ^ k • M with hYdef
  have hσϖk : σ (ϖ ^ k) = ϖ ^ k := by rw [map_pow, hσϖ]
  have hY : Formalism.UG.cT σ Y * Jt = -(ϖ ^ k • C) := by
    rw [hYdef, cT_smul, hσϖk, Matrix.smul_mul, hMdef, Formalism.UG.cT_mul, hcC, Matrix.mul_assoc, hcJti, Matrix.mul_one,
      smul_neg]
  have hJY : Jt * Y = ϖ ^ k • C := by
    rw [hYdef, Matrix.mul_smul, hMdef, ← Matrix.mul_assoc, hJJi, Matrix.one_mul]
  set Z : Matrix (Fin n') (Fin n') L := (2⁻¹ : L) • Y with hZdef
  have hZZ : Z + Z = Y := by
    rw [hZdef, ← add_smul]
    have : (2⁻¹ + 2⁻¹ : L) = 1 := by
      have h2ne : (2 : L) ≠ 0 := fun h => by rw [h, map_zero] at h2; exact zero_ne_one h2
      field_simp; norm_num
    rw [this, one_smul]
  have hZ : Formalism.UG.cT σ Z * Jt = -(Jt * Z) := by
    rw [hZdef, cT_smul, hσhalf, Matrix.smul_mul, hY, Matrix.mul_smul, hJY, smul_neg]
  have hYsmall : IsSmallM Y := fun i j => by
    rw [hYdef, Matrix.smul_apply, smul_eq_mul]; exact lt_one_mul hvϖk (hMI i j)
  have hZsmall : IsSmallM Z := small_smul hhalf hYsmall
  obtain ⟨hPdet, hPiI⟩ := inv_one_sub hZsmall
  obtain ⟨hQdet, hQiI⟩ := inv_one_add hZsmall
  set Pi := (1 - Z)⁻¹ with hPi
  set Qi := (1 + Z)⁻¹ with hQi
  have hP1 : Pi * (1 - Z) = 1 := Matrix.nonsing_inv_mul _ hPdet
  have hP2 : (1 - Z) * Pi = 1 := Matrix.mul_nonsing_inv _ hPdet
  have hQ1 : Qi * (1 + Z) = 1 := Matrix.nonsing_inv_mul _ hQdet
  have hQ2 : (1 + Z) * Qi = 1 := Matrix.mul_nonsing_inv _ hQdet
  have hPs : Formalism.UG.cT σ Pi * (1 - Formalism.UG.cT σ Z) = 1 := by
    rw [← Formalism.UG.cT_one σ, ← cT_sub, ← Formalism.UG.cT_mul, hP2]
  let g : GL (Fin n') L := ⟨Pi * (1 + Z), Qi * (1 - Z), by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 + Z), hQ2, Matrix.one_mul, hP1], by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 - Z), hP2, Matrix.one_mul, hQ1]⟩
  have hgU : g ∈ Formalism.UG.UJ σ Jt := by
    show Formalism.UG.cT σ (Pi * (1 + Z)) * Jt * (Pi * (1 + Z)) = Jt
    rw [Formalism.UG.cT_mul, cT_add, Formalism.UG.cT_one]
    exact cayley_unitary_ring hZ hP1 hP2 hQ1 hQ2 hPs
  have hone : IsIntM (1 : Matrix (Fin n') (Fin n') L) := fun i j => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hIZ : IsIntM (1 + Z) := isIntM_add hone (isIntM_of_small hZsmall)
  have hIZ' : IsIntM (1 - Z) := by
    rw [sub_eq_add_neg]; exact isIntM_add hone (isIntM_neg (isIntM_of_small hZsmall))
  have hgI : g ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) :=
    mem_GLint_of_int (isIntM_mul hPiI hIZ) (isIntM_mul hQiI hIZ')
  obtain ⟨hr1, hr2⟩ := cayley_ring hP1 hP2
  have hg1 : Pi * (1 + Z) - 1 = ϖ ^ k • (M * Pi) := by
    rw [hr1, hZZ, hYdef, Matrix.smul_mul]
  have hg2 : Pi * (1 + Z) - 1 - Y = (ϖ ^ (k + 1) * (ϖ ^ (k - 1) * 2⁻¹)) • (M * Pi * M) := by
    have e : ϖ ^ (k + 1) * (ϖ ^ (k - 1) * 2⁻¹) = ϖ ^ k * (2⁻¹ * ϖ ^ k) := by
      have : k + 1 + (k - 1) = k + k := by omega
      rw [← mul_assoc, ← pow_add, this, pow_add]; ring
    rw [e, hr1, hZZ]
    have e2 : Y * Pi - Y = Y * (Pi - 1) := by rw [Matrix.mul_sub, Matrix.mul_one]
    rw [e2, hr2, hZdef, hYdef]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc]
    congr 1; ring
  refine ⟨⟨g, hgU⟩, hgI, fun r s => ?_, fun r s => ?_⟩
  · have : ((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) r s - (1 : Matrix (Fin n') (Fin n') L) r s =
        (Pi * (1 + Z) - 1) r s := by rw [Matrix.sub_apply]
    rw [this, hg1, Matrix.smul_apply, smul_eq_mul]
    exact ⟨_, isIntM_mul hMI hPiI r s, rfl⟩
  · have : ((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) r s - (1 : Matrix (Fin n') (Fin n') L) r s -
        (ϖ ^ k • (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * C)) r s =
        (Pi * (1 + Z) - 1 - Y) r s := by rw [Matrix.sub_apply, Matrix.sub_apply]
    rw [this, hg2, Matrix.smul_apply, smul_eq_mul, mul_assoc]
    refine ⟨_, mul_mem (mul_mem (pow_mem hϖI _) hhalf) (isIntM_mul (isIntM_mul hMI hPiI) hMI r s), rfl⟩

end GlobalTheory.Hk3.CayleyCong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainLocalDataIntegralOffLevelsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chain_local_data_integral_off_levels : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ (P : HeightOneSpectrum (𝓞 t.X.E)), (∀ (i : ℕ) x, IntOff (t.O u μ).S (t.seam.σ₀ (PhiAt (R := D.R) t.Ch (t.tup μ) (t.cst μ).sharp i P x))) ∧ ∀ x, IntOff (t.O u μ).S (t.seam.σ₀ (PhiTop (R := D.R) t.Ch (t.tup μ) (t.cst μ).sharp t.m2 P x)) := by
  first | exact @GlobalTheory.PhiRootVal.phi_intOff | exact GlobalTheory.PhiRootVal.phi_intOff | (intros; apply GlobalTheory.PhiRootVal.phi_intOff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacterCmInfinityType
section
noncomputable section

namespace GlobalTheory.KerJ.RatPts

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Host NumberField IsDedekindDomain Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.Mem.Chr (finPartI)

theorem isFin_finPart {L : Type} [Field L] [NumberField L] (a : Ideles L) : Formalism.L2.Host.IsFinIdele (finPartI L a) := fun _ => rfl

end GlobalTheory.KerJ.RatPts

namespace GlobalTheory.KerJ

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.Host NumberField Classical Formalism.FrobeniusOrbits GlobalTheory.KerJ.RatPts

end GlobalTheory.KerJ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChiAlgUnitInert
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

theorem ringHom_mem_qbar {A : Type} [Field A] [NumberField A] (f : A →+* ℂ) (x : A) : f x ∈ TaylorLogMetric.Qbar := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral (R := ℚ) x).map f.toRatAlgHom

theorem lamC_eq_of_mem {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam s = lam ⟨s, hs⟩ := by
  unfold TaylorLogMetric.lamC
  rw [dite_eq_left hs]

theorem chi_alg_unit_inert : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (χ : TaylorLogMetric.IdE D → ℂ),
    TaylorLogMetric.IsChi D χ → p ≠ 2 → GL3Theta.InertK D p → ∀ 𝔞 : TaylorLogMetric.IdE D, TaylorLogMetric.N1 D 𝔞 →
      χ 𝔞 ∈ TaylorLogMetric.Qbar ∧ χ 𝔞 ≠ 0 ∧ ‖TaylorLogMetric.lamC lam (χ 𝔞)‖ = 1 := by
  intro D p _ lam χ hχ hp2 hin 𝔞 ha
  letI := D.host.cmStar
  obtain ⟨k, hk, z, hz, hspan⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.pow_unitary D ha
  have hzu : z ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.star_conj]
    exact ⟨by rw [mul_comm]; exact hz, hz⟩
  set P : ℂ := ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z with hPdef
  have hpow : χ 𝔞 ^ k = P⁻¹ := by
    have h := hχ.2 ⟨z, hzu⟩
    simp only at h
    rw [← hspan, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.chi_pow D χ hχ ha k hk] at h
    rw [h, hPdef, Finset.prod_inv_distrib]
  have hz0 : z ≠ 0 := by
    rintro rfl; simp at hz
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun τ _ => (map_ne_zero _).mpr hz0
  have hP : P ∈ TaylorLogMetric.Qbar := prod_mem fun τ _ => ringHom_mem_qbar _ z
  have hk0 : k ≠ 0 := by omega
  have halg : χ 𝔞 ∈ TaylorLogMetric.Qbar := by
    rw [mem_algebraicClosure_iff] at hP ⊢
    have h2 : IsAlgebraic ℚ (χ 𝔞 ^ k) := by rw [hpow]; exact hP.inv
    exact IsAlgebraic.of_pow (Nat.pos_of_ne_zero hk0) h2
  have hne : χ 𝔞 ≠ 0 := by
    intro h0
    rw [h0, zero_pow hk0] at hpow
    exact hP0 (inv_eq_zero.mp hpow.symm)
  refine ⟨halg, hne, ?_⟩
  have hnu := _root_.GlobalTheory.normUnit_of_inert D p lam hp2 hin z hz
  rw [← hPdef, lamC_eq_of_mem lam hP] at hnu
  have hsub : (⟨χ 𝔞, halg⟩ : TaylorLogMetric.Qbar) ^ k = (⟨P, hP⟩ : TaylorLogMetric.Qbar)⁻¹ := by
    apply Subtype.ext
    simp [hpow]
  have e1 : ‖lam ⟨χ 𝔞, halg⟩‖ ^ k = 1 := by
    rw [← norm_pow, ← map_pow, hsub, map_inv₀, norm_inv, hnu, inv_one]
  rw [lamC_eq_of_mem lam halg]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk0).mp e1

end GlobalTheory.TwV.Xc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CurveIdealBaseThetaVectorNormalisedEveryPlace
section
noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity
open Formalism.L2.Th1.F (cmTheta)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace GlobalTheory.ThLoc.LocMM

theorem cmTheta_odd (b : ℤ) (hb : Odd b) (d : ℕ) : ∃ k : ℤ, cmTheta b d = cmTheta 1 d + (k : ℂ) := by
  obtain ⟨k, rfl⟩ := hb
  refine ⟨k, ?_⟩
  simp only [cmTheta]
  push_cast
  ring

theorem stable_of_one {V : Type*} [AddCommGroup V] [Module ℂ V] (Λ : AddSubgroup V) (d : ℕ)
    (h : ∀ x ∈ Λ, cmTheta 1 d • x ∈ Λ) (b : ℤ) (hb : Odd b) : ∀ x ∈ Λ, cmTheta b d • x ∈ Λ := by
  intro x hx
  obtain ⟨k, hk⟩ := cmTheta_odd b hb d
  rw [hk, add_smul]
  refine Λ.add_mem (h x hx) ?_
  rw [Int.cast_smul_eq_zsmul]
  exact Λ.zsmul_mem hx k

theorem odd_of_cmOK {a : ℕ} {b c : ℤ} {d : ℕ} (h : CmOK a b c d) : Odd b := by
  by_contra hb
  obtain ⟨k, rfl⟩ := Int.not_odd_iff_even.1 hb
  have h1 := h.1
  have h8 := h.2.2.1
  have h2 : (d : ℤ) = 4 * ((a : ℤ) * c - k * k) := by
    have : (k + k) ^ 2 = 4 * (k * k) := by ring
    rw [this] at h1
    linarith
  generalize (a : ℤ) * c - k * k = t at h2
  omega

theorem hermitianSelfDual_of_fourfoldBlock {n : Type} [Fintype n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (hsd : IsSelfDual (matH (blk4 h)) (pow4 Λ)) : IsSelfDual (matH h) Λ := by
  have key : ∀ (x : n → ℂ) (y : Fin 4 × n → ℂ), altE (matH (blk4 h)) (CmData.embA 0 x) y = altE (matH h) x (slice 0 y) := by
    intro x y
    simp only [altE, matrixForm_fourfoldBlock, CmData.slice_embA]
    rw [Finset.sum_eq_single (0 : Fin 4)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  ext x
  constructor
  · intro hx
    have h1 : CmData.embA 0 x ∈ dualLat (matH (blk4 h)) (pow4 Λ) := by
      intro y hy
      obtain ⟨m, hm⟩ := hx (slice 0 y) (hy 0)
      exact ⟨m, by rw [key, hm]⟩
    rw [hsd] at h1
    have h2 := h1 0
    rwa [CmData.slice_embA, if_pos rfl] at h2
  · intro hx y hy
    have h1 : CmData.embA 0 x ∈ dualLat (matH (blk4 h)) (pow4 Λ) := by
      rw [hsd]
      exact CmData.embA_mem Λ 0 hx
    obtain ⟨m, hm⟩ := h1 _ (CmData.embA_mem Λ 0 hy)
    refine ⟨m, ?_⟩
    rw [key, CmData.slice_embA, if_pos rfl] at hm
    exact hm

section Base

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem selfDual_fourfold_curveIdeal_lattice (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    IsSelfDual (matH (blk4 (hOne B.L D.what₂.Tau))) (pow4 B.lamM) := by
  have h := ((B.latAll hcc hδ (base_linkage_nonempty D cc δ B)).1 2 2 _ _
    (Formalism.MainNotions.GlobalTheoryTheory.Inhab.Adm_std D 2 2 even_two even_two)).1
  rw [show TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = _ from B.areaOK, show TaylorLogMetric.La D B.tor _ _ = _ from B.lat0OK 2 2] at h
  have h2 := SO.selfDual_img _ _ (SO.reix D.what₂.Tau) (SO.reix_isom B.L D.what₂.Tau) _ h
  rw [SO.reix_pow] at h2
  exact h2

theorem selfDual_lamM (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    IsSelfDual (matH (hOne B.L D.what₂.Tau)) B.lamM :=
  hermitianSelfDual_of_fourfoldBlock _ _ (selfDual_fourfold_curveIdeal_lattice B hcc hδ)

theorem stable_lamM (b : ℤ) (hb : Odd b) : ∀ x ∈ B.lamM, cmTheta b D.host.d • x ∈ B.lamM := by
  refine stable_of_one _ _ (fun x hx => ?_) b hb
  have := SO.lamMM_smul (AR.om D) hx
  rw [← SO.theta_eq] at this
  exact this

end Base

theorem kappaAt {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) : B.KappaAt p ι := by
  by_cases hs : SplitK D p
  · exact _root_.GlobalTheory.kappaSplit_all D cc δ B hcc hδ p ι hs
  · exact _root_.GlobalTheory.ThLoc.kappaNonSplit D cc δ B hcc hδ p ι hs

theorem locNormMM : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (B : Base D cc δ) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0),
    CmOK a₀ b₀ c₀ D.host.d → B.IsCm a₀ b₀ ha hd lam hlam →
    ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), B.LocNormMM a₀ b₀ ha hd lam hlam p ι := by
  intro D cc δ hcc hδ B a₀ b₀ c₀ ha hd lam hlam hcm hB l _ ι
  have hK : B.KappaAt l ι := kappaAt B hcc hδ l ι
  obtain ⟨hL, hω⟩ := hB
  have hS : StdData B.L B.ω₀ (hOne B.L D.what₂.Tau) B.lamM (alphaQ B.cq (matH (hOne B.L D.what₂.Tau)))
    (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) B.gC := B.stdOK hcc hδ
  have hsd := selfDual_lamM B hcc hδ
  have hst := stable_lamM B b₀ (odd_of_cmOK hcm)
  have hspec := B.thMM_spec (B.stdOK hcc hδ)
  have h2 : tens4 B.thMM = B.kappa • kernel4 B.L B.ω₀ B.lamM
      (alphaQ (Real.sqrt D.host.d / 2) (stdH B.L (Fin 4 × D.what₂.Tau))) B.gC := hspec.2
  have iso := hS.isom
  have i1 := hS.idx₁
  have i2 := hS.idx₂
  unfold Base.KappaAt Base.latA at hK
  unfold Base.LocNormMM LocNorm
  rw [hω] at h2
  rw [hL] at h2 hK iso i1 i2 hsd ⊢
  have hsda := CmData.selfDual_img _ _ B.gC iso _ (CmData.isSelfDual_matH_blk4_pow4 _ B.lamM hsd)
  have hsta : ∀ x ∈ imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM),
      cmTheta b₀ D.host.d • x ∈ imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM) := by
    rintro x ⟨x', hx', rfl⟩
    refine ⟨cmTheta b₀ D.host.d • x', fun a' => hst _ (hx' a'), ?_⟩
    simp
  obtain ⟨u, huiso, hufix, j1, jl, j2⟩ := localStandard a₀ b₀ c₀ D.host.d ha hd lam hlam hcm (Fin 4 × D.what₂.Tau) _
    hsda hsta i1 i2 l Fact.out
  have hκu := hK u huiso j1 jl j2
  rw [← KR.imgLat_trans] at j1 jl j2
  have hg₁ : IsIsom (matH (blk4 (hOne (cmL a₀ b₀ D.host.d ha hd lam hlam) D.what₂.Tau)))
      (stdH (cmL a₀ b₀ D.host.d ha hd lam hlam) (Fin 4 × D.what₂.Tau))
      ((B.gC.trans u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) :
        (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) := by
    intro x y
    have h1 := huiso (B.gC x) (B.gC y)
    have h0 := iso x y
    simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply] at h0 h1 ⊢
    rw [h1, h0]
  have D0 := stdDataCm a₀ b₀ c₀ D.host.d ha hd lam hlam hcm.1 hcm.2.1 hcm.2.2.1 D.what₂.Tau _ B.lamM B.gC iso hsd hst i1 i2
  have D1 := stdDataCm a₀ b₀ c₀ D.host.d ha hd lam hlam hcm.1 hcm.2.1 hcm.2.2.1 D.what₂.Tau _ B.lamM (B.gC.trans u) hg₁
    hsd hst j1 j2
  have hcomp : B.gC.symm.trans (B.gC.trans u) = u := by
    ext x
    simp
  have hfix : ∀ x, (B.gC.trans u) x = B.gC x → x = 0 := by
    intro x hx
    have h1 : B.gC x = 0 := hufix _ hx
    simpa using congrArg B.gC.symm h1
  rw [← hcomp] at hκu
  obtain ⟨c, hc8, hc⟩ := kernelRatio _ _ D.what₂.Tau _ B.lamM _ _ B.gC (B.gC.trans u) D0 D1 hfix
  refine ⟨B.gC.trans u, B.kappa * c, hg₁, jl, j2, (KR.norm_mul_eq_one ι B.kappa c _ hc8 hκu).le, ?_⟩
  rw [h2, hc, smul_smul]

end GlobalTheory.ThLoc.LocMM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerTieEntire
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerTieEntire

theorem kerTie_entire : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ, ∀ i < D.R.m, ∀ c c', Differentiable ℂ ((t.O u μ).Th i c c') := by
  intro D L hT Gi Gl K Y cX ex t u μ i _ c c'
  have hEven : ∀ j, Even (D.R.N j) := fun j => D.R.k_even.add (D.R.t_odd.add_one.mul_left j)
  have hAdm : TaylorLogMetric.admitted D _ _ ((t.O u μ).lat i c).1 ((t.O u μ).lat (i + 1) c').1 :=
    ⟨hEven i, hEven (i + 1), ((t.O u μ).lat i c).2, ((t.O u μ).lat (i + 1) c').2⟩
  rw [t.O_lat u μ i c, t.O_lat u μ (i + 1) c'] at hAdm
  rw [t.O_Th u μ i c c']
  have hF := GlobalTheory.KerFinEntire.kerFin_entire D t.X t.seam t.cc t.δ t.B t.χ t.cD t.seam_ok t.cc_ok t.δ_ok t.χ_ok _ _
    ((t.rd u μ).N i c) ((t.rd u μ).N (i + 1) c') hAdm (t.rd u μ).SS (t.rd u μ).lev ((t.rd u μ).Xi i c c')
  let T : TaylorLogMetric.VC D (D.R.N i) (D.R.N (i + 1)) →L[ℂ] VCx t.X.Tau (D.R.N i) (D.R.N (i + 1)) :=
    ContinuousLinearMap.pi fun τ => ContinuousLinearMap.proj (t.seam.iT τ)
  exact hF.comp T.differentiable

end GlobalTheory.KerTieEntire
end
end

