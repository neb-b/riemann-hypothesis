module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0080
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0007
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AdditionIdentityOfSigmaFormulaUnit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeTeichmuller.NormLeOneOfIntegralInt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryThetaConstantEqInverseDeterminantPhase

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PhAtMulByNorm
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section
namespace GlobalTheory.CMNormPhi

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem intSer_iff' {f : PowerSeries ℂ_[p]} : IntegralMv f ↔ IntSer f := by
  constructor
  · intro h n; exact h (Finsupp.single () n)
  · intro h n
    have := h (n ())
    rwa [PowerSeries.coeff_def (s := n) rfl] at this

theorem intSer_sq_of_eq (h F f L : PowerSeries ℂ_[p]) (τ : ℂ_[p]) (n : ℕ) (hh : IntSer h)
    (hh0 : constantCoeff h = 0) (hh1 : coeff 1 h = τ) (hτ : ‖τ‖ = 1) (hF : constantCoeff F = 1)
    (hL : IntSer L) (hL0 : constantCoeff L = 1)
    (e : h ^ 2 * F ^ 2 = C (τ ^ 2) * X ^ 2 * (f ^ n) ^ 2 * L) : IntSer ((F⁻¹ * f ^ n) ^ 2) := by
  obtain ⟨v, rfl⟩ := (PowerSeries.X_dvd_iff).2 hh0
  have hv : IntSer v := fun m => by simpa [PowerSeries.coeff_succ_X_mul] using hh (m + 1)
  have e' : v ^ 2 * F ^ 2 = C (τ ^ 2) * (f ^ n) ^ 2 * L := by
    have hX : (X : PowerSeries ℂ_[p]) ^ 2 ≠ 0 := pow_ne_zero _ X_ne_zero
    apply mul_left_cancel₀ hX
    linear_combination e
  have hτ0 : τ ≠ 0 := by rintro rfl; simp at hτ
  have hFi : F⁻¹ * F = 1 := PowerSeries.inv_mul_cancel _ (by rw [hF]; exact one_ne_zero)
  have hLi : L * L⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rw [hL0]; exact one_ne_zero)
  have hc : C (τ⁻¹ ^ 2) * C (τ ^ 2) = (1 : PowerSeries ℂ_[p]) := by
    rw [← map_mul, ← mul_pow, inv_mul_cancel₀ hτ0, one_pow, map_one]
  have key : (F⁻¹ * f ^ n) ^ 2 = C (τ⁻¹ ^ 2) * v ^ 2 * L⁻¹ := by
    linear_combination (-(C (τ⁻¹ ^ 2)) * F⁻¹ ^ 2 * L⁻¹) * e' +
      (C (τ⁻¹ ^ 2) * v ^ 2 * L⁻¹ * (F⁻¹ * F + 1)) * hFi -
      (F⁻¹ ^ 2 * (f ^ n) ^ 2 * L * L⁻¹) * hc - (F⁻¹ ^ 2 * (f ^ n) ^ 2) * hLi
  obtain ⟨hr, -, hC, -, hinv, -⟩ := GlobalTheory.EvenTheta.SerRing.series_ring_laws p
  rw [key]
  refine (hr _ _ (hr _ _ ((hC _).2 ?_) (by rw [sq]; exact (hr _ _ hv hv).2.2)).2.2
    (hinv L hL (by rw [hL0, norm_one]))).2.2
  rw [norm_pow, norm_inv, hτ]; simp

theorem atU_prod' (g : GL3Theta.G1 p) {ι : Type} (s : Finset ι) {F : ι → ℂ → ℂ} (hF : ∀ i, AlgEnt (F i)) :
    AlgEnt (fun z => ∏ i ∈ s, F i z) ∧ g.atU (fun z => ∏ i ∈ s, F i z) = ∏ i ∈ s, g.atU (F i) := by
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨h1, h2⟩ := (GlobalTheory.SerTransport.transport p g).2.1 1 (one_mem _)
    simp only [Finset.prod_empty]
    refine ⟨h1, ?_⟩
    rw [h2, lamC, dite_eq_left (one_mem _)]
    exact congrArg C (map_one g.lam)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    rw [← ih.2]
    exact ((GlobalTheory.SerTransport.transport p g).1 _ _ (hF a) ih.1).1

theorem phAt_mulBy_norm : ∀ (D : D7), GL3Theta.endInt D → GL3Theta.addInt D → ∀ (p : ℕ) [Fact p.Prime]
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p), GL3Theta.At D cc δ g → p ≠ 2 →
    ∀ a : 𝓞 D.host.K, Nat.Coprime (Algebra.norm ℤ a).natAbs p →
    GL3Theta.Simeq (g.phAt (g.mulBy (GL3Theta.tauK D g.lam (a : D.host.K)) (GL3Theta.Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (GL3Theta.tauK D g.lam (a : D.host.K) * GL3Theta.tauKc D g.lam (a : D.host.K)) *
        g.phAt (GL3Theta.Xv ())) := by
  intro D hend _ p _ cc δ g hg hp a hcop
  have hg' := hg
  obtain ⟨hcc, -, hδ, hΛ, hok⟩ := hg
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -, hdisc, -, hst⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  obtain ⟨⟨-, h2, h3⟩, hwp⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  simp only [tor0] at h2 h3
  rw [← hΛ] at hlat hdisc hst h2 h3 hwp huse
  have hlat' : IsLat g.abelian₂ := hlat
  have halgσ : AlgEnt (sgStar g.abelian₂) := by
    have e : U1 g.abelian₂ 0 (sgStar g.abelian₂) = sgStar g.abelian₂ := by funext z; simp [U1]
    have := huse 0 ⟨1, one_pos, by simp⟩
    rw [e] at this
    exact ⟨hlat'.differentiable, this⟩

  set β : ℂ := D.host.φ₀ ((a : D.host.K) : D.host.E) with hβdef
  have hβQ : β ∈ Qbar := Formalism.MainNotions.Ext.test_vector_mem_schwartz_bruhat D _
  have hβst : ∀ ω ∈ g.abelian₂, β * ω ∈ g.abelian₂ := hst a
  let a' : 𝓞 D.host.K := ⟨Formalism.MainNotions.Ext.conjK D (a : D.host.K),
    (RingOfIntegers.isIntegral_coe a).map (Formalism.MainNotions.Ext.conjK D).toIntAlgHom⟩
  have hconj : D.host.φ₀ ((a' : D.host.K) : D.host.E) = starRingEnd ℂ β := by
    show D.host.φ₀ ((Formalism.MainNotions.Ext.conjK D (a : D.host.K) : D.host.K) : D.host.E) = _
    rw [Formalism.MainNotions.Ext.conjK_coe]
    exact D.host.conjE_apply D.host.φ₀ _
  have hN : β * starRingEnd ℂ β = ((Algebra.norm ℤ a : ℤ) : ℂ) := by
    have h := Formalism.MainNotions.UnusedSlot33.HK.norm_int D.host a
    rw [Algebra.intNorm_eq_norm] at h
    have h' := congrArg D.host.φ₀ h
    have hc : D.host.φ₀ (D.host.conj ((a : D.host.K) : D.host.E)) = starRingEnd ℂ β :=
      D.host.conjE_apply D.host.φ₀ _
    rw [map_intCast, map_mul, hc] at h'
    exact h'.symm
  have hnn : 0 ≤ (Algebra.norm ℤ a : ℤ) := by
    have e1 : ((Algebra.norm ℤ a : ℤ) : ℂ) = ((Complex.normSq β : ℝ) : ℂ) := by
      rw [← hN, Complex.mul_conj]
    have e2 : ((Algebra.norm ℤ a : ℤ) : ℝ) = Complex.normSq β := by exact_mod_cast e1
    have := Complex.normSq_nonneg β
    rw [← e2] at this
    exact_mod_cast this
  have hn0 : (Algebra.norm ℤ a).natAbs ≠ 0 := by
    intro h0
    rw [h0, Nat.coprime_zero_left] at hcop
    exact (Fact.out : p.Prime).one_lt.ne' hcop
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hnk : (Algebra.norm ℤ a : ℤ) = ((k + 1 : ℕ) : ℤ) := by
    have := Int.natAbs_of_nonneg hnn
    rw [hk] at this
    exact this.symm
  have hβN : β * starRingEnd ℂ β = ((k + 1 : ℕ) : ℂ) := by rw [hN, hnk]; push_cast; ring
  have hcop' : Nat.Coprime (k + 1) p := by
    have := hcop
    rwa [hk] at this

  set τ := GL3Theta.tauK D g.lam (a : D.host.K) with hτdef
  have hτβ : τ = lamC g.lam β := rfl
  have htn : τ * GL3Theta.tauKc D g.lam (a : D.host.K) = ((k + 1 : ℕ) : ℂ_[p]) := by
    rw [hτdef, Formalism.MainNotions.Ext.CutA.tau_norm, hnk]; push_cast; ring
  have hτ1 : ‖τ‖ ≤ 1 := by
    rw [hτβ, hβdef, ← Formalism.MainNotions.Ext.tauKp_apply]; exact PI.OkpW.norm_tau_le _ a
  have hτc1 : ‖GL3Theta.tauKc D g.lam (a : D.host.K)‖ ≤ 1 := by
    have e : GL3Theta.tauKc D g.lam (a : D.host.K) = Formalism.MainNotions.Ext.tauKp D g.lam (a' : D.host.K) := by
      rw [Formalism.MainNotions.Ext.tauKp_apply]
      show _ = lamC g.lam (D.host.φ₀ ((Formalism.MainNotions.Ext.conjK D (a : D.host.K) : D.host.K) : D.host.E))
      rw [Formalism.MainNotions.Ext.conjK_coe]; rfl
    rw [e]; exact PI.OkpW.norm_tau_le _ a'
  have hn1 : ‖((k + 1 : ℕ) : ℂ_[p])‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap']
    exact Padic.norm_natCast_eq_one_iff.2 hcop'.symm
  have hτu : ‖τ‖ = 1 := by
    have := congrArg norm htn
    rw [norm_mul, hn1] at this
    nlinarith [norm_nonneg τ, norm_nonneg (GL3Theta.tauKc D g.lam (a : D.host.K))]

  obtain ⟨hmul, hconst, -, hscale⟩ := GlobalTheory.SerTransport.transport p g
  obtain ⟨h, hh, hh0, hh1, hsub⟩ := hscale hok β hβQ
  obtain ⟨hu, hw, hw0, hE, hσ⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat' h2 h3 hdisc
  have hhI : IntSer h := by
    have := hend p cc δ g hg' (τ, GL3Theta.tauKc D g.lam (a : D.host.K)) (subset_closure ⟨a, rfl⟩)
    have h' : IntegralMv (h : MvPowerSeries Unit ℂ_[p]) := by rw [hh]; exact this
    exact intSer_iff'.1 h'

  set f := ePhi1 g.lam g.abelian₂ g.C g.wq with hfdef
  have hε0 : ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ≠ 0 := Units.ne_zero _
  obtain ⟨Q, hQ, hfac⟩ := GlobalTheory.T.sigmaStar_mul_sq_eq_prod_kernel_quotients g.abelian₂ hlat' β k hβst hβN
  have hLaQ : ∀ i, ((k + 1 : ℕ) : ℂ) * Q i ∈ g.abelian₂ := fun i => by
    have e : ((k + 1 : ℕ) : ℂ) * Q i = D.host.φ₀ ((a' : D.host.K) : D.host.E) * (β * Q i) := by
      rw [hconj, ← hβN]; ring
    rw [e]; exact hst a' _ (hQ i).2
  have hsq : ∀ i, AlgEnt (sqTh g.abelian₂ (Q i)) ∧
      g.atU (sqTh g.abelian₂ (Q i)) = f ^ 2 * lineSer g.wq⁻¹ (xAt g (Q i)) :=
    fun i => GlobalTheory.EvenTheta.Param.sqTh_atU p g hok.2.1 hlat' h2 h3 halgσ (Q i) (hQ i).1
      (hwp _ ⟨k + 1, Nat.succ_pos k, hLaQ i⟩ (hQ i).1).1
  have hx : ∀ i, ‖xAt g (Q i)‖ ≤ 1 := fun i =>
    _root_.GlobalTheory.TorsionAbscissa.norm_xAt_le_of_mul D p cc δ g hg' (k + 1) (Q i) (Nat.succ_pos k) hcop' (hLaQ i) (hQ i).1
  obtain ⟨hr, -, hC, hXI, -, -⟩ := GlobalTheory.EvenTheta.SerRing.series_ring_laws p
  have hlineI : ∀ x : ℂ_[p], ‖x‖ ≤ 1 → IntSer (lineSer g.wq⁻¹ x) := fun x hx =>
    (hr _ _ hw ((hr _ _ ((hC x).2 hx) (by rw [sq]; exact (hr _ _ hXI hXI).2.2)).2.2)).2.1
  have hLI : IntSer (∏ i, lineSer g.wq⁻¹ (xAt g (Q i))) :=
    Finset.prod_induction _ IntSer (fun _ _ h1 h2 => (hr _ _ h1 h2).2.2)
      (fun n => by rw [coeff_one]; split_ifs <;> simp) (fun i _ => hlineI _ (hx i))
  have hL0 : constantCoeff (∏ i, lineSer g.wq⁻¹ (xAt g (Q i))) = 1 := by
    rw [map_prod]; refine Finset.prod_eq_one fun i _ => ?_
    simp only [lineSer, map_sub, map_mul, map_pow, constantCoeff_X, hw0, constantCoeff_C]; simp

  have hA := hsub _ halgσ
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' hh0
  have lhs : g.atU (fun z => sgStar g.abelian₂ (β * z) ^ 2) =
      (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * h * subst h f) ^ 2 := by
    have e := (hmul _ _ hA.1 hA.1).1.2
    have e2 : (fun z => sgStar g.abelian₂ (β * z) ^ 2) = fun z => sgStar g.abelian₂ (β * z) * sgStar g.abelian₂ (β * z) := by
      funext z; ring
    rw [e2, e, hA.2, hσ, subst_mul hs, subst_mul hs, subst_C, subst_X hs, sq]
    rfl
  have hτ2 : lamC g.lam (β ^ 2) = τ ^ 2 := by
    have e : β ^ 2 = D.host.φ₀ (((a : D.host.K) * (a : D.host.K) : D.host.K) : D.host.E) := by
      rw [IntermediateField.coe_mul, map_mul, sq]
    rw [e, sq]
    exact Formalism.MainNotions.Ext.CutA.tauK_mul D g.lam _ _
  have hG2 : AlgEnt (fun z => sgStar g.abelian₂ z ^ 2) ∧
      g.atU (fun z => sgStar g.abelian₂ z ^ 2) = g.atU (sgStar g.abelian₂) ^ 2 := by
    have e2 : (fun z => sgStar g.abelian₂ z ^ 2) = fun z => sgStar g.abelian₂ z * sgStar g.abelian₂ z := by funext z; ring
    rw [e2, sq]; exact (hmul _ _ halgσ halgσ).1
  have hP := atU_prod' g Finset.univ (fun i => (hsq i).1)
  have hGP := (hmul _ _ hG2.1 hP.1).1
  have hc := hconst (β ^ 2) (pow_mem hβQ 2)
  have hcGP := (hmul _ _ hc.1 hGP.1).1
  have rhs : g.atU (fun z => β ^ 2 * sgStar g.abelian₂ z ^ 2 * ∏ i, sqTh g.abelian₂ (Q i) z) =
      C (τ ^ 2) * ((C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * X * f) ^ 2 *
        ∏ i, (f ^ 2 * lineSer g.wq⁻¹ (xAt g (Q i)))) := by
    have e2 : (fun z => β ^ 2 * sgStar g.abelian₂ z ^ 2 * ∏ i, sqTh g.abelian₂ (Q i) z) =
        fun z => β ^ 2 * (sgStar g.abelian₂ z ^ 2 * ∏ i, sqTh g.abelian₂ (Q i) z) := by funext z; ring
    rw [e2, hcGP.2, hc.2, hGP.2, hG2.2, hP.2, hσ, hτ2, Finset.prod_congr rfl fun i _ => (hsq i).2]
  have E1 := congrArg g.atU (funext hfac : (fun z => sgStar g.abelian₂ (β * z) ^ 2) =
    fun z => β ^ 2 * sgStar g.abelian₂ z ^ 2 * ∏ i, sqTh g.abelian₂ (Q i) z)
  rw [lhs, rhs, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at E1
  have e : h ^ 2 * (subst h f : PowerSeries ℂ_[p]) ^ 2 =
      C (τ ^ 2) * X ^ 2 * (f ^ (k + 1)) ^ 2 * ∏ i, lineSer g.wq⁻¹ (xAt g (Q i)) := by
    have hε2 : (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) : PowerSeries ℂ_[p]) ^ 2 ≠ 0 :=
      pow_ne_zero _ fun h0 => hε0 (by simpa using congrArg constantCoeff h0)
    apply mul_left_cancel₀ hε2
    linear_combination E1
  have hF0 : constantCoeff (subst h f : PowerSeries ℂ_[p]) = 1 := by
    rw [GlobalTheory.SerTransport.const_subst hh0, hE]
  have hI2 := intSer_sq_of_eq h (subst h f) f _ τ (k + 1) hhI hh0 hh1 hτu hF0 hLI hL0 e
  have hH0 : constantCoeff ((subst h f : PowerSeries ℂ_[p])⁻¹ * f ^ (k + 1)) = 1 := by
    rw [map_mul, PowerSeries.constantCoeff_inv, hF0, map_pow, hE]; simp
  have hI := _root_.GlobalTheory.EvenTheta.intSer_of_sq_main p hp _ hH0 hI2
  obtain ⟨c0, ex⟩ := _root_.GlobalTheory.ExpLogShift.expMv_phAt_sub_nsmul p g h (k + 1) hE hh0
  have hmb : (g.mulBy τ (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) = h := hh.symm
  rw [hmb, htn]
  refine ⟨c0, ?_⟩
  rw [ex]
  exact intSer_iff'.2 hI
end GlobalTheory.CMNormPhi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackFirstGroupRationalPointEqSmul
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui
open scoped BigOperators

noncomputable section

namespace GlobalTheory.RatRow

variable {D : D7} {N N' : ℕ}

theorem conj_conj (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  have h : ∀ y, D.host.φ₀ (D.host.conj y) = (starRingEnd ℂ) (D.host.φ₀ y) := fun y =>
    D.host.conjE_apply _ y
  rw [h, h, Complex.conj_conj]

theorem adj_adj {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) : adj D (adj D M) = M := by
  refine Matrix.ext fun i j => ?_
  simp [adj, conj_conj]

theorem moves_one (D : D7) (N : ℕ) : Moves D ((1 : GA D N) : GL (Fin N) (AE D)) (stdL D N) := by
  obtain ⟨Lt, h1, h2, -⟩ := exists_lattice_of_adelic_point D N
  rw [← h2]; exact (h1 _).1

theorem sd_of_moves {g : GA D N} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (h : Moves D (g : GL (Fin N) (AE D)) L) : SD D L := by
  obtain ⟨Lt, h1, -⟩ := exists_lattice_of_adelic_point D N
  have : L = Lt g := by
    ext x; rw [h x, (h1 g).1 x]
  rw [this]; exact (h1 g).2

theorem klat (T : Tor D) {g : GA D N} {g' : GA D N'} {L₁ L₁'}
    (h : Moves D (g : GL (Fin N) (AE D)) L₁) (h' : Moves D (g' : GL (Fin N') (AE D)) L₁') :
    KLat D T (La D T L₁ L₁') := Or.inr ⟨_, _, sd_of_moves h, sd_of_moves h', rfl⟩

theorem isRat_one (D : D7) (N : ℕ) : IsRat D ((1 : GA D N) : GL (Fin N) (AE D)) 1 := by
  unfold IsRat
  rw [Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

theorem hf_unitary (T : Tor D) {M' : Matrix (Fin N') (Fin N') D.host.E} {M : Matrix (Fin N) (Fin N) D.host.E}
    (h' : adj D M' * M' = 1) (h : M * adj D M = 1) (z w : VC D N N') :
    Hf D T (mulV D M' M z) (mulV D M' M w) = Hf D T z w := by
  rw [Hf_mulV, mulV_mulV, h', h, mulV_one]

theorem mulV_comm (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E) (z : VC D N N') :
    mulV D M' 1 (mulV D 1 M z) = mulV D 1 M (mulV D M' 1 z) := by
  simp only [mulV_mulV, Matrix.mul_one, Matrix.one_mul]

theorem mulV_scalar (a : D.host.E) (z : VC D N N') (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) :
    mulV D (Matrix.diagonal fun _ => a) 1 z τ i j = embT D τ a * z τ i j := by
  rw [mulV_apply, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
    Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul]
  rfl

def revM (D : D7) (n : ℕ) : Matrix (Fin n) (Fin n) D.host.E := Matrix.of fun i j => if j = i.rev then 1 else 0

def halfM (D : D7) (n : ℕ) : Matrix (Fin n) (Fin n) D.host.E :=
  Matrix.diagonal fun i => if i < i.rev then 1 else 0

theorem revM_mul_self (n : ℕ) : revM D n * revM D n = 1 := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev (fun k _ hk => by simp [revM, hk]) (by simp)]
  simp [revM, Matrix.one_apply, eq_comm]

theorem adj_revM (n : ℕ) : adj D (revM D n) = revM D n := by
  refine Matrix.ext fun i j => ?_
  have : i = j.rev ↔ j = i.rev := by
    constructor <;> rintro rfl <;> simp
  simp only [adj, revM, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, this]
  split_ifs <;> simp

theorem halfM_mul_self (n : ℕ) : halfM D n * halfM D n = halfM D n := by
  rw [halfM, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem adj_halfM (n : ℕ) : adj D (halfM D n) = halfM D n := by
  rw [adj, halfM, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
  congr 1
  funext i
  split_ifs <;> simp

theorem revM_mul_halfM {n : ℕ} (hn : Even n) : revM D n * halfM D n = revM D n - halfM D n * revM D n := by
  refine Matrix.ext fun i j => ?_
  obtain ⟨k, rfl⟩ := hn
  simp only [halfM, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.sub_apply, revM, Matrix.of_apply]
  by_cases h : j = i.rev
  · subst h
    have hi := i.2
    by_cases h1 : i < i.rev
    · have h2 : ¬ i.rev < i := not_lt.2 h1.le
      simp [h1, h2]
    · have h2 : i.rev < i := by
        rw [Fin.lt_def, Fin.val_rev] at *
        omega
      simp [h1, h2]
  · simp [h]

theorem integral_diagonal {n : ℕ} {d : Fin n → D.host.E} (hd : ∀ i, IsIntegral ℤ (d i)) (i j : Fin n) :
    IsIntegral ℤ (Matrix.diagonal d i j) := by
  rw [Matrix.diagonal_apply]
  split_ifs
  · exact hd i
  · exact isIntegral_zero

theorem integral_one {n : ℕ} (i j : Fin n) : IsIntegral ℤ ((1 : Matrix (Fin n) (Fin n) D.host.E) i j) :=
  integral_diagonal (fun _ => isIntegral_one) i j

theorem det_adj {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) : (adj D M).det = D.host.conj M.det := by
  rw [adj, Matrix.det_transpose]
  exact ((D.host.conj : D.host.E →+* D.host.E).map_det M).symm

theorem adj_one_sub {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) : adj D (1 - M) = 1 - adj D M := by
  refine Matrix.ext fun i j => ?_
  simp [adj, Matrix.one_apply, eq_comm]

theorem det_mul_conj (hN : Even N) {γ : Matrix (Fin N) (Fin N) D.host.E} (h : γ * adj D γ = 1) :
    γ.det * D.host.conj (1 - γ).det = (1 - γ).det := by
  rw [← det_adj, adj_one_sub, ← Matrix.det_mul, Matrix.mul_sub, h, Matrix.mul_one, ← neg_sub, Matrix.det_neg,
    Fintype.card_fin, hN.neg_one_pow, one_mul]

theorem phase {g w : ℂ} (hw : w ≠ 0) (h : g * (starRingEnd ℂ) w = w) (k : ℕ) :
    ((‖w ^ (k + k)‖ : ℝ) : ℂ) / w ^ (k + k) = g ^ (-(k : ℤ)) := by
  have hg : g ≠ 0 := by rintro rfl; exact hw (by simpa using h.symm)
  have h1 : ((‖w ^ (k + k)‖ : ℝ) : ℂ) = (w * (starRingEnd ℂ) w) ^ k := by
    rw [Complex.mul_conj', norm_pow, ← two_mul, pow_mul]; push_cast; rfl
  rw [h1, zpow_neg, zpow_natCast, div_eq_iff (pow_ne_zero _ hw), eq_inv_mul_iff_mul_eq₀ (pow_ne_zero _ hg), ← mul_pow,
    mul_left_comm, h, mul_pow, pow_add]

theorem pull_eq_smul_iop : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), Even N → Even N' → ∀ th ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), ∀ (γA : GA D N) (γ : Matrix (Fin N) (Fin N) D.host.E) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), IsRat D (γA : GL (Fin N) (AE D)) γ → (1 - γ).det ≠ 0 → Moves D (γA : GL (Fin N) (AE D)) L₁ → pull D (tor0 D cc δ) γ 1 th = (∏ τ, embT D τ γ.det ^ (-((N' / 2 : ℕ) : ℤ))) • Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ (stdL D N')) th := by
  intro D cc δ hc N N' hN hN' th hth γA γ L₁ hr hdet hm
  have hu : γ * adj D γ = 1 := (mem_ratG_intG D N).2.2.2.1 γA γ hr
  have hu' : adj D γ * γ = 1 := mul_eq_one_comm.1 hu
  obtain ⟨hint, hden, hmov⟩ := _root_.GlobalTheory.ThetaStab.mulV_theta_lattices D cc δ hc N N'
  let u : VC D N N' ≃ₗ[ℂ] VC D N N' := LinearEquiv.ofLinear (mulV D 1 (adj D γ)) (mulV D 1 γ)
    (LinearMap.ext fun z => by simp [mulV_mulV, hu, mulV_one])
    (LinearMap.ext fun z => by simp [mulV_mulV, hu', mulV_one])
  have ua : ∀ z, u z = mulV D 1 (adj D γ) z := fun _ => rfl
  have us : ∀ z, u.symm z = mulV D 1 γ z := fun _ => rfl
  have hid : LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N') = mulV D 1 (1 - γ) :=
    LinearMap.ext fun z => by rw [mulV_sub_right, mulV_one]; rfl
  have hd : LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) =
      ∏ τ, embT D τ (1 - γ).det ^ N' := by
    rw [hid, _root_.GlobalTheory.TwoSidedDet.det_mulV]; simp
  have hw : ∀ τ, embT D τ (1 - γ).det ≠ 0 := fun τ => (map_ne_zero _).2 hdet
  have key := _root_.GlobalTheory.SymConst.const_of_symm D cc δ hc N N' (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ (stdL D N'))
    (klat _ (moves_one D N) (moves_one D N')) (klat _ hm (moves_one D N')) u
    (hf_unitary _ (by rw [adj_one, Matrix.one_mul]) (by rw [adj_adj, hu']))
    (hmov γA 1 γ 1 L₁ _ hr (isRat_one D N') hm (moves_one D N'))
    (by rw [hd]; exact Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (hw τ)) ?_
    (mulV D (halfM D N') 1) (mulV D (revM D N') 1) ?_
    (fun x => by rw [mulV_mulV, halfM_mul_self, Matrix.one_mul])
    (fun x y => by rw [Hf_mulV, adj_halfM, adj_one])
    (fun x => by rw [mulV_mulV, revM_mul_self, Matrix.one_mul, mulV_one])
    (hf_unitary _ (by rw [adj_revM, revM_mul_self]) (by rw [adj_one, Matrix.one_mul]))
    (fun x => by rw [mulV_mulV, mulV_mulV, revM_mul_halfM hN', Matrix.one_mul, mulV_sub_left])
    (fun x => mulV_comm _ _ x) (fun x => mulV_comm _ _ x) ?_ th hth
  · rw [pull_eq, adj_one]
    refine key.trans ?_
    congr 1
    obtain ⟨k, rfl⟩ := hN'
    rw [hd, norm_prod, Complex.ofReal_prod, ← Finset.prod_div_distrib, show (k + k) / 2 = k by omega]
    refine Finset.prod_congr rfl fun τ _ => phase (hw τ) ?_ k
    rw [← embT_conj, ← map_mul, det_mul_conj hN hu]
  · obtain ⟨m₁, h₁, g₁⟩ := hden 1 (1 - γ)⁻¹
    obtain ⟨m₂, h₂, g₂⟩ := hden 1 ((1 - γ)⁻¹ * γ)
    have e : ∀ x : VC D N N', u.symm ((m₁ * m₂) • mulV D 1 (1 - γ)⁻¹ x) = (m₁ * m₂) • mulV D 1 ((1 - γ)⁻¹ * γ) x := by
      intro x
      rw [map_nsmul, us, mulV_mulV, Matrix.one_mul]
    refine ⟨m₁ * m₂, Nat.mul_pos h₁ h₂, fun x hx => ⟨(m₁ * m₂) • mulV D 1 (1 - γ)⁻¹ x, ?_, ?_, ?_⟩⟩
    · rw [mul_comm, mul_smul]; exact nsmul_mem (g₁ x hx) _
    · rw [e, mul_smul]; exact nsmul_mem (g₂ x hx) _
    · have h1 : (1 - γ)⁻¹ - (1 - γ)⁻¹ * γ = 1 := by
        have := Matrix.nonsing_inv_mul (1 - γ) (Ne.isUnit hdet)
        rwa [Matrix.mul_sub, Matrix.mul_one] at this
      rw [e, ← smul_sub, ← mulV_sub_right, h1, mulV_one]
  · refine fun x hx => ⟨hint _ _ (integral_diagonal fun i => ?_) integral_one x hx,
      hint _ _ (fun i j => ?_) integral_one x hx⟩
    · split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
    · rw [revM, Matrix.of_apply]
      split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
  · intro M hM
    obtain ⟨l, b, hlb⟩ := GlobalTheory.NegOneNorm.exists_norm_eq_neg_one D M hM
    have hM' : (M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
    have hb : D.host.conj (b : D.host.E) = b := by
      have := congrArg D.host.conj hlb
      rw [map_mul, conj_conj, mul_comm, hlb, map_add (f := _), map_neg, map_one, map_mul, map_natCast] at this
      exact (mul_left_cancel₀ hM' (add_left_cancel this)).symm
    refine ⟨mulV D (Matrix.diagonal fun _ => (l : D.host.E)) 1, mulV D (Matrix.diagonal fun _ => (b : D.host.E)) 1,
      fun x hx => ⟨hint _ _ (integral_diagonal fun _ => l.2) integral_one x hx,
        hint _ _ (integral_diagonal fun _ => b.2) integral_one x hx⟩,
      fun x => mulV_comm _ _ x, fun x => mulV_comm _ _ x, fun x => ?_, fun x y => ?_, fun x y => ?_⟩
    · rw [mulV_mulV, mulV_mulV, halfM, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      simp only [mul_comm]
    · rw [Hf_mulV, adj_one, adj, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
      simp only [hb]
    · have h : ∀ τ, embT D τ l * (starRingEnd ℂ) (embT D τ l) = -1 + M * embT D τ b := by
        intro τ
        rw [← embT_conj, ← map_mul, hlb]; simp
      simp only [Hf, mulV_scalar, ← neg_div, ← mul_div_assoc, ← add_div, Finset.mul_sum, ← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib, map_mul]
      congr 1
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      linear_combination (x τ i j * (starRingEnd ℂ) (y τ i j)) * h τ

end GlobalTheory.RatRow
end
end

