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
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0267
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddnessConditionHolds
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationVacuumSignInertPlaces
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0274

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeWpDerivModelParameterSeries
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.FrobStick

open PowerSeries

theorem omegaW_mul_inv {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p])
    (hwq : IsWq W wq) :
    omegaW W wq * (wq⁻¹ * (C W.a₁ * X + C W.a₃ * X ^ 3 * wq - 2)) =
      X * derivative (R := ℂ_[p]) wq⁻¹ - 2 * wq⁻¹ ∧ omegaW W wq ≠ 0 := by
  have hw1 := GlobalTheory.GenusOneDatum.constantCoeff_of_isWq hwq
  have he : wq * wq⁻¹ = 1 := PowerSeries.mul_inv_cancel wq (by rw [hw1]; exact one_ne_zero)
  have he1 : constantCoeff wq⁻¹ = 1 := by simp [PowerSeries.constantCoeff_inv, hw1]
  set e := wq⁻¹ with hedef
  set N : PowerSeries ℂ_[p] := C W.a₁ * X + C W.a₃ * X ^ 3 * wq - 2 with hN
  have h2 : constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := map_ofNat _ 2
  have hω : omegaW W wq * (wq * N) = -2 * wq - X * derivative (R := ℂ_[p]) wq := by
    have hu : (wq * N)⁻¹ * (wq * N) = 1 :=
      PowerSeries.inv_mul_cancel _ (by simp [hN, hw1, h2])
    have : omegaW W wq = (-2 * wq - X * derivative (R := ℂ_[p]) wq) * (wq * N)⁻¹ := by
      have hd : dX wq = derivative (R := ℂ_[p]) wq := by
        ext n
        simp [dX, coeff_derivative, mul_comm]
      unfold omegaW
      rw [hd]
      rfl
    rw [this, mul_assoc, hu, mul_one]
  have hde : wq * derivative (R := ℂ_[p]) e + e * derivative (R := ℂ_[p]) wq = 0 := by
    have := congrArg (derivative (R := ℂ_[p])) he
    rw [Derivation.leibniz] at this
    simpa using this
  have key : omegaW W wq * (e * N) = X * derivative (R := ℂ_[p]) e - 2 * e := by
    linear_combination e ^ 2 * hω - X * e * hde -
      (omegaW W wq * N * e + 2 * e - X * derivative (R := ℂ_[p]) e) * he
  refine ⟨key, fun h => ?_⟩
  rw [h, zero_mul] at key
  have := congrArg constantCoeff key
  simp [he1, h2] at this

theorem atU_sgStar_eq {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (hL : IsLat g.abelian₂) :
    g.atU (sgStar g.abelian₂) =
      C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (X * ePhi1 g.lam g.abelian₂ g.C g.wq) := by
  have h0 : constantCoeff (GL3Theta.ser1 g.lam (sgStar g.abelian₂)) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, GlobalTheory.SerTransport.coeff_padicTransportSeries, GlobalTheory.SerTransport.taylorCoeff_zero_eq_value,
      (hL.sg_eq_zero 0).2 (zero_mem _)]
    exact (GlobalTheory.SerTransport.lamC_coe g.lam 0).trans (map_zero g.lam)
  obtain ⟨S, hS⟩ := X_dvd_iff.2 h0
  have hs := HasSubst.of_constantCoeff_zero' (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  rw [GlobalTheory.EvenTheta.Param.X_mul_ePhi1 g S hS, GlobalTheory.SerTransport.atU_eq, hS, subst_mul hs, subst_X hs,
    mul_assoc]

theorem colC_atU : (∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (F : ℂ → ℂ), AlgEnt F → AlgEnt (deriv F) ∧ PowerSeries.derivative (R := ℂ_[p]) (g.atU F) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * omegaW g.W g.wq * g.atU (deriv F)) → ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsWq g.W g.wq → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → AlgEnt (GlobalTheory.FrobStick.colC g.abelian₂ v) ∧ g.atU (GlobalTheory.FrobStick.colC g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 * g.wq⁻¹ * (PowerSeries.C g.W.a₁ * PowerSeries.X + PowerSeries.C g.W.a₃ * PowerSeries.X ^ 3 * g.wq - 2) := by
  intro hD p _ g hq hL h2 h3 hσ v hv hw
  obtain ⟨hQ, eQ⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hq hL h2 h3 hσ v hv hw
  obtain ⟨hσ', dσ⟩ := hD p g _ hσ
  obtain ⟨hQ', dQ⟩ := hD p g _ hQ
  obtain ⟨hT, hc, -⟩ := GlobalTheory.SerTransport.transport p g
  have hm : (-2 : ℂ) ∈ Qbar := neg_mem (ofNat_mem _ 2)
  obtain ⟨c1, c2⟩ := hc _ hm
  have c3 : lamC g.lam (-2) = -2 := by
    have : (-2 : ℂ) = ((-2 : Qbar) : ℂ) := by push_cast; rfl
    rw [this, GlobalTheory.SerTransport.lamC_coe, map_neg, map_ofNat]
  obtain ⟨a1, a2⟩ := (hT _ _ hσ hQ').1
  obtain ⟨b1, b2⟩ := (hT _ _ c1 hσ').1
  obtain ⟨d1, d2⟩ := (hT _ _ b1 hQ).1
  obtain ⟨f1, f2⟩ := (hT _ _ a1 d1).2
  have e : colC g.abelian₂ v = fun z => sgStar g.abelian₂ z * deriv (sqTh g.abelian₂ v) z +
      (-2 * deriv (sgStar g.abelian₂) z) * sqTh g.abelian₂ v z := by
    funext z
    rw [colC]; ring
  rw [e]
  refine ⟨f1, ?_⟩
  rw [f2, a2, d2, b2, c2, c3, map_neg, map_ofNat]
  obtain ⟨hω, hω0⟩ := omegaW_mul_inv g.W g.wq hq
  have eS := atU_sgStar_eq g hL
  have hε : (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) : PowerSeries ℂ_[p]) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    rw [constantCoeff_C, map_zero] at this
    exact Units.ne_zero _ this
  apply mul_left_cancel₀ (mul_ne_zero hε hω0)
  rw [eQ, lineSer] at dQ
  rw [eS] at dσ
  rw [eQ, eS, lineSer]
  generalize ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) = ε at *
  generalize ePhi1 g.lam g.abelian₂ g.C g.wq = E at *
  generalize g.wq⁻¹ = q at *
  generalize xAt g v = x at *
  have k1 : derivative (R := ℂ_[p]) (C ε * (X * E)) = C ε * (E + X * derivative (R := ℂ_[p]) E) := by
    rw [Derivation.leibniz, Derivation.leibniz]; simp [add_comm]
  have k2 : derivative (R := ℂ_[p]) (E ^ 2 * (q - C x * X ^ 2)) =
      E ^ 2 * (derivative (R := ℂ_[p]) q - C x * (2 * X)) + (q - C x * X ^ 2) * (2 * E * derivative (R := ℂ_[p]) E) := by
    rw [Derivation.leibniz, map_sub, Derivation.leibniz (a := C x), Derivation.leibniz_pow, Derivation.leibniz_pow]
    simp only [derivative_C, derivative_X, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
    ring
  rw [k1] at dσ
  rw [k2] at dQ
  linear_combination -(C ε * (X * E)) * dQ + 2 * (E ^ 2 * (q - C x * X ^ 2)) * dσ - C ε * E ^ 3 * hω

end GlobalTheory.FrobStick
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameHeckeCharTrivialOnFiniteUnitsCongOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem valued_natCast_le_of_mem_asIdeal {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (m : ℕ)
    (hm : (m : 𝓞 L) ∈ P.asIdeal) : Valued.v ((m : P.adicCompletion L)) ≤ WithZero.exp (-1 : ℤ) := by
  have h1 : ((m : P.adicCompletion L)) = ((algebraMap (𝓞 L) L (m : 𝓞 L) : L) : P.adicCompletion L) := by
    rw [map_natCast]
    exact (map_natCast (algebraMap L (P.adicCompletion L)) m).symm
  rw [h1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  have := (P.intValuation_le_pow_iff_mem (m : 𝓞 L) 1).2 (by simpa using hm)
  simpa using this

theorem finiteAdele_apply_sub_one_of_eq {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (m : ℕ)
    (a b : FiniteAdeleRing (𝓞 L) L) (e : a - 1 = (m : FiniteAdeleRing (𝓞 L) L) * b) :
    a P - 1 = (m : P.adicCompletion L) * b P := by
  let ev : FiniteAdeleRing (𝓞 L) L →+* P.adicCompletion L :=
    RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L) P
  have e3 : ev (a - 1) = ev ((m : FiniteAdeleRing (𝓞 L) L) * b) := congrArg ev e
  rw [ev.map_sub, ev.map_mul, ev.map_one, map_natCast ev m] at e3
  exact e3

theorem tame_heckeChar_eq_one_of_finUnit : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → (∀ P, χ.TameAt P) → ∀ m : ℕ, (∀ P : HeightOneSpectrum (𝓞 D.host.E), (m : 𝓞 D.host.E) ∉ P.asIdeal → χ.UnrAt P) → ∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = m • y) → c x = 1 := by
  intro D c χ hc ht m hu x hx ⟨y, hy, hxy⟩
  obtain ⟨ι, h1, h2, h3⟩ := _root_.GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := _root_.GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 (_root_.GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  obtain ⟨S, k, hS, hS'⟩ := _root_.GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  obtain ⟨hx1, hx2, hx3⟩ := hx
  have hv : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (x : AE D)) P) = 1 := by
    intro P
    have a := (h2 _).1 hx2 P
    have b := (h2 _).1 hx3 P
    have e : ι (finPart D (x : AE D)) * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have e' : Valued.v (ι (finPart D (x : AE D)) P) * Valued.v (ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P) = 1 := by
      rw [← map_mul]
      have : ι (finPart D (x : AE D)) P * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P = 1 :=
        congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z P) e
      rw [this, map_one]
    refine le_antisymm a ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := e'.symm
      _ ≤ Valued.v (ι (finPart D (x : AE D)) P) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _
  have key := hprod x hx1 S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS'
  apply Subtype.ext
  refine key.trans (Finset.prod_eq_one fun P hP => ?_)
  obtain ⟨a, -, b⟩ := hS P hP
  have a' : Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) := a
  have b' : Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k P : D.host.E)) ≤
      WithZero.exp (-1 : ℤ) * P.valuation D.host.E (k P : D.host.E) := b
  rw [hv P] at a'
  rw [← a', mul_one] at b'
  have hun : IsUnitAt P (atFin P (k P)) := by
    show Valued.v (((k P : D.host.E)) : P.adicCompletion D.host.E) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← a']
  have : χ.loc P (atFin P (k P)) = 1 := by
    by_cases hm : (m : 𝓞 D.host.E) ∈ P.asIdeal
    · refine ht P _ hun ?_
      have e : ι (finPart D (x : AE D)) - 1 = (m : FiniteAdeleRing (𝓞 D.host.E) D.host.E) * ι y := by
        rw [← map_one ι, ← map_sub, hxy, map_nsmul, nsmul_eq_mul]
      have e2 : ι (finPart D (x : AE D)) P - 1 = (m : P.adicCompletion D.host.E) * ι y P :=
        finiteAdele_apply_sub_one_of_eq P m _ _ e
      have c1 : Valued.v (ι (finPart D (x : AE D)) P - 1) ≤ WithZero.exp (-1 : ℤ) := by
        rw [e2, map_mul]
        calc _ ≤ WithZero.exp (-1 : ℤ) * 1 :=
              mul_le_mul' (valued_natCast_le_of_mem_asIdeal P m hm) ((h2 _).1 hy P)
          _ = _ := mul_one _
      have e4 : ((atFin P (k P) : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) - 1 =
          (ι (finPart D (x : AE D)) P - 1) - (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k P : D.host.E)) := by
        show algebraMap D.host.E _ (k P : D.host.E) - 1 = _
        ring
      rw [e4]
      exact Valuation.map_sub_le _ c1 b'
    · exact hu P hm _ hun
  show ((χ.loc P (atFin P (k P)) : ℂˣ) : ℂ) = 1
  rw [this, Units.val_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairUnitModulusFactor
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.NormSum.VacMove
open scoped BigOperators Pointwise

namespace GlobalTheory.ArchFree.weilc

theorem exists_scalar {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {N N' : ℕ}
    {e0 : VC D N N' → ℂ} (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (W : WeilO D cc δ N N' e0)
    (g : GA D N) (g' : GA D N') {L₁ L₁'} (h : Moves D (g : GL (Fin N) (AE D)) L₁)
    (h' : Moves D (g' : GL (Fin N') (AE D)) L₁') :
    ∃ c : ℂ, W.Om g g' e0 = fun z => c *
      Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 z := by
  have hcc : cc ≠ ⊥ := hc.1.1
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := klat _ (moves_one D N) (moves_one D N')
  have k1 := klat (tor0 D cc δ) h h'
  have hT := vac_TT (_root_.GlobalTheory.InducedType.induced_type D).1 hc he
  obtain ⟨-, hF, -, hinv⟩ := _root_.GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc N N' _ _ k0 k1 e0 he
  have hF0 : Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 ≠ 0 := by
    intro h0
    rw [h0, iop_zero] at hinv
    exact W.nz hinv.symm
  obtain ⟨hline, hW, -⟩ := _root_.GlobalTheory.ThetaLine.theta_line D (_root_.GlobalTheory.InducedType.induced_type D).1 cc δ hc N N' _ k1
  suffices hG : W.Om g g' e0 ∈ ThSp D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') from hline _ hG _ hF hF0
  refine ⟨(W.maps g g' e0 hT).1, fun x hx => ?_⟩
  suffices hs : Wd D (tor0 D cc δ) x (W.Om g g' e0) = W.Om g g' e0 by
    rw [hW x hx] at hs; exact congrFun hs
  have hmul : ∀ a ∈ La D (tor0 D cc δ) L₁ L₁', ∀ b ∈ La D (tor0 D cc δ) L₁ L₁', ∀ F,
      Wd D (tor0 D cc δ) a (Wd D (tor0 D cc δ) b F) = Wd D (tor0 D cc δ) (a + b) F := by
    intro a ha b hb F
    obtain ⟨φ, hφ⟩ := wd_wd D (tor0 D cc δ) a b
    have h2 := hφ (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0)
    rw [wd_fix (_root_.GlobalTheory.InducedType.induced_type D).1 hc k1 hF hb, wd_fix (_root_.GlobalTheory.InducedType.induced_type D).1 hc k1 hF ha, wd_fix (_root_.GlobalTheory.InducedType.induced_type D).1 hc k1 hF (add_mem ha hb)] at h2
    have h3 : φ = 1 := by
      by_contra hne
      apply hF0
      have : (φ - 1) • Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 = 0 := by
        rw [sub_smul, one_smul, ← h2, sub_self]
      exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
    rw [hφ, h3, one_smul]
  obtain ⟨z', rfl, hz'⟩ := _root_.GlobalTheory.NormSum.exists_pt_of_mem_La_moved D (_root_.GlobalTheory.InducedType.induced_type D).1 cc δ hcc N N' g g' L₁ L₁' h h' x hx
  have hlatb := _root_.GlobalTheory.NormSum.pt_mem_La_of_adelic D (_root_.GlobalTheory.InducedType.induced_type D).1 cc δ hcc N N' g g' L₁ L₁' h h'
  have hlat0 := _root_.GlobalTheory.NormSum.pt_mem_La_of_adelic D (_root_.GlobalTheory.InducedType.induced_type D).1 cc δ hcc N N' 1 1 _ _ (moves_one D N) (moves_one D N')
  simp only [OneMemClass.coe_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one] at hlat0
  simp only [← MI_one] at hz' hlatb hlat0
  obtain ⟨m0, hm0, hl0⟩ := W.lift g g' 0 e0 hT
  rw [VacMove.pt_zero, VacMove.wd_zero] at hl0
  set P : Matrix (Fin N') (Fin N') (AE D) := ((g' : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) with hP
  set P' : Matrix (Fin N') (Fin N') (AE D) :=
    (((g' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) with hP'
  set Q : Matrix (Fin N) (Fin N) (AE D) := ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) with hQ
  set Q' : Matrix (Fin N) (Fin N) (AE D) :=
    (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) with hQ'
  have ePP : P * P' = 1 := Units.mul_inv _
  have eP'P : P' * P = 1 := Units.inv_mul _
  have eQQ : Q * Q' = 1 := Units.mul_inv _
  have eQ'Q : Q' * Q = 1 := Units.inv_mul _
  have e1 : ∀ M : Matrix (Fin N') (Fin N) (AE D), P * (P' * M * Q) * Q' = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ePP, Matrix.one_mul, Matrix.mul_assoc, eQQ, Matrix.mul_one]
  have e2 : ∀ M : Matrix (Fin N') (Fin N) (AE D), P' * (P * M * Q') * Q = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, eP'P, Matrix.one_mul, Matrix.mul_assoc, eQ'Q, Matrix.mul_one]
  obtain ⟨n, hn, hb⟩ := MI_bound hcc P Q'
  obtain ⟨n', hn', hb'⟩ := MI_bound hcc P' Q
  obtain ⟨z, hz⟩ := MI_approx hcc (P' * z'.map (inc D) * Q) (n * m0) (Nat.mul_pos hn hm0)
  have hz0 : MI D cc 1 (z.map (inc D)) := by
    simpa using (hz.of_dvd (one_dvd _)).add hz'
  obtain ⟨m, hm, hl⟩ := W.lift g g' z e0 hT
  rw [wd_fix (_root_.GlobalTheory.InducedType.induced_type D).1 hc k0 he (hlat0 z hz0)] at hl
  obtain ⟨w, hw⟩ := MI_approx hcc (P * z.map (inc D) * Q') (n' * (m * m0)) (by positivity)
  have hw1 : MI D cc 1 (P' * w.map (inc D) * Q) := by
    have := ((hb' _ _ hw).of_dvd (one_dvd _)).add hz0
    rwa [Matrix.mul_sub, Matrix.sub_mul, e2, sub_add_cancel] at this
  have hd : (w - z').map (inc D) = w.map (inc D) - z'.map (inc D) := by
    ext i j; simp
  have hd' : (z' - w).map (inc D) = z'.map (inc D) - w.map (inc D) := by
    ext i j; simp
  have hdiff : MI D cc m0 ((z' - w).map (inc D)) := by
    have h1 := hb _ _ hz
    rw [Matrix.mul_sub, Matrix.sub_mul, e1] at h1
    have h2 : MI D cc m0 (0 : Matrix (Fin N') (Fin N) (AE D)) := fun i j => ⟨0, zero_mem _, by simp⟩
    have := (h2.sub h1).sub (hw.of_dvd (m := m0) ⟨n' * m, by ring⟩)
    rw [hd']
    convert this using 1
    abel
  have f1 := hl w (hw.of_dvd (m := m) ⟨n' * m0, by ring⟩)
  have f2 := hl0 (z' - w) (by
    intro i j
    have h0 : (0 : Matrix (Fin N') (Fin N) D.host.E).map (inc D) = 0 := by ext; simp
    rw [h0, Matrix.mul_zero, Matrix.zero_mul, sub_zero]
    exact hdiff i j)
  have hdl : MI D cc 1 (P' * (z' - w).map (inc D) * Q) := by
    rw [hd', Matrix.mul_sub, Matrix.sub_mul]
    exact hz'.sub hw1
  have := hmul _ (hlatb w hw1) _ (hlatb _ hdl) (W.Om g g' e0)
  rw [← f2, ← f1, ← pt_add, add_sub_cancel] at this
  exact this.symm

theorem vacuum_under_adelic_pair : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), Even (N * N') → ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), ∀ (W : WeilO D cc δ N N' e0) (g : GA D N) (g' : GA D N') L₁ L₁', Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → ∃ c : ℂ, Mod1All c ∧ (W.Om g g' e0 = fun z => c * Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 z) ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (k' : GA D N'), k' ∈ intG D N' → TrivAt D p (g : GL (Fin N) (AE D)) → TrivAt D p ((g' * k' : GA D N') : GL (Fin N') (AE D)) → ‖lamC lam c‖ = 1 := by
  intro D cc δ hc N N' hev e0 he W g g' L₁ L₁' h h'
  obtain ⟨c, hce⟩ := exists_scalar hc he W g g' h h'
  have hmod : Mod1All c := by
    obtain ⟨z, x, hz, hx, -⟩ := exists_splitComp D _ (det_norm D g)
    obtain ⟨z', x', hz', hx', -⟩ := exists_splitComp D _ (det_norm D g')
    obtain ⟨sg, hsg, hc2⟩ := (_root_.GlobalTheory.VacuumScalar.vacuum_scalar D cc δ hc N N' hev e0 he W.nz W g g' L₁ L₁' c h h' hce).1 z z' x x' hz hz' hx hx'
    refine modulusOneAllEmbeddings_of_pow (k := 2 * 2) (by norm_num) ?_
    have hs : sg ^ 2 = 1 := by rcases hsg with rfl | rfl <;> norm_num
    have h4 : c ^ (2 * 2) = ((W.chV.f x' : ℂˣ) : ℂ) ^ (4 * W.ep) * ((W.chV'.f x : ℂˣ) : ℂ) ^ (4 * W.ep') := by
      rw [pow_mul, hc2, mul_pow, hs, one_mul, ← Units.val_pow_eq_pow_val, ← Units.val_zpow_eq_zpow_val,
        ← Units.val_zpow_eq_zpow_val, ← Units.val_mul, mul_pow]
      congr 2 <;> (rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]; congr 1; push_cast; ring)
    rw [h4]
    exact algebraicModulusOneAll_mul (algebraicModulusOneAll_zpow (_root_.GlobalTheory.HeckeVal.hecke_values D N W.chV x').1 _) (algebraicModulusOneAll_zpow (_root_.GlobalTheory.HeckeVal.hecke_values D N' W.chV' x).1 _)
  refine ⟨c, hmod, hce, fun p _ lam k' hk' ht ht' => ?_⟩
  have hm1 : Moves D (k' : GL (Fin N') (AE D)) (stdL D N') := by
    simpa using moves_mul_int hk' (moves_one D N')
  obtain ⟨a, hae⟩ := exists_scalar hc he W 1 k' (moves_one D N) hm1
  obtain ⟨k, hk, hak⟩ : ∃ k : ℕ, 0 < k ∧ a ^ k = 1 := by
    obtain ⟨z, x, hz, hx, hxi⟩ := exists_splitComp D _ (det_norm D (1 : GA D N))
    obtain ⟨z', x', hz', hx', hxi'⟩ := exists_splitComp D _ (det_norm D k')
    obtain ⟨sg, hsg, hc2⟩ := (_root_.GlobalTheory.VacuumScalar.vacuum_scalar D cc δ hc N N' hev e0 he W.nz W 1 k' _ _ a (moves_one D N) hm1 hae).1
      z z' x x' hz hz' hx hx'
    obtain ⟨m, hm, hxm⟩ := (_root_.GlobalTheory.HeckeVal.hecke_values D N' W.chV' x).2.1
      (hxi (det_int D _ (((mem_ratG_intG D N).2.1 1).1 (one_mem _))))
    obtain ⟨m', hm', hxm'⟩ := (_root_.GlobalTheory.HeckeVal.hecke_values D N W.chV x').2.1
      (hxi' (det_int D _ (((mem_ratG_intG D N').2.1 k').1 hk')))
    refine ⟨2 * (2 * (m * m')), by positivity, ?_⟩
    have hs : sg ^ 2 = 1 := by rcases hsg with rfl | rfl <;> norm_num
    have key : ∀ (u : ℂˣ) (e : ℤ) (r s : ℕ), u ^ r = 1 → r ∣ s → ((u ^ 2) ^ e) ^ s = 1 := by
      rintro u e r _ hu ⟨t, rfl⟩
      rw [← zpow_natCast, ← zpow_mul, mul_comm e, zpow_mul, zpow_natCast, ← pow_mul, mul_comm 2, mul_assoc,
        pow_mul, hu, one_pow, one_zpow]
    rw [pow_mul, hc2, mul_pow, pow_mul sg, hs, one_pow, one_mul, ← Units.val_pow_eq_pow_val, mul_pow,
      key _ _ m' _ hxm' ⟨2 * m, by ring⟩, key _ _ m _ hxm ⟨2 * m', by ring⟩, one_mul, Units.val_one]
  have hT := vac_TT (_root_.GlobalTheory.InducedType.induced_type D).1 hc he
  have hae' : W.Om 1 k' e0 = a • e0 := by
    rw [hae, show La D (tor0 D cc δ) (stdL D N) (stdL D N') = La0 D (tor0 D cc δ) N N' from rfl,
      iop_self D _ (La0 D (tor0 D cc δ) N N') he]
    rfl
  have hprod : W.Om g (g' * k') e0 = fun z => (a * c) *
      Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 z := by
    have := W.mul g 1 g' k' e0 hT
    rw [mul_one, hae', W.smul _ _ _ _ hT, hce] at this
    rw [this]
    funext z
    simp [mul_assoc]
  exact norm_lamC_of_root lam hk hak hmod.1
    ((_root_.GlobalTheory.VacuumScalar.vacuum_scalar D cc δ hc N N' hev e0 he W.nz W g (g' * k') L₁ L₁' _ h (moves_mul_int hk' h') hprod).2 p lam ht ht').2

end GlobalTheory.ArchFree.weilc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorVacuumExactConstantEvenRank
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.VacuumScalar
open scoped BigOperators

namespace GlobalTheory.VacuumExact

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem exists_scalar (hc : Crv D cc δ) {e0 : VC D N N' → ℂ}
    (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (W : WeilO D cc δ N N' e0) {g : GA D N} {g' : GA D N'}
    {L L'} (hL : Moves D (g : GL (Fin N) (AE D)) L) (hL' : Moves D (g' : GL (Fin N') (AE D)) L') :
    ∃ c : ℂ, W.Om g g' e0 = c • Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') e0 := by
  have hg1 := (GlobalTheory.InducedType.induced_type D).1
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') :=
    Or.inr ⟨_, _, sd_of_moves (moves_one D N), sd_of_moves (moves_one D N'), rfl⟩
  have k1 : KLat D (tor0 D cc δ) (La D (tor0 D cc δ) L L') := Or.inr ⟨_, _, sd_of_moves hL, sd_of_moves hL', rfl⟩
  obtain ⟨-, hTh, -, -⟩ := _root_.GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc N N' _ _ k0 k1 e0 he
  obtain ⟨hline, w1, -⟩ := _root_.GlobalTheory.ThetaLine.theta_line D hg1 cc δ hc N N' _ k1
  obtain ⟨a1, -, a3, a4, -, a6, -⟩ := lattice_facts hc he W.nz hL hL'
  have heT : e0 ∈ TT D (tor0 D cc δ) N N' := ⟨he.1, 1, one_pos, fun y hy => by rw [one_smul]; exact a6 y hy⟩
  have hGT := W.maps g g' e0 heT
  have hinv : ∀ F ∈ TT D (tor0 D cc δ) N N', W.Om g g' (W.Om g⁻¹ g'⁻¹ F) = F := by
    intro F hF
    rw [← W.mul _ _ _ _ _ hF, mul_inv_cancel, mul_inv_cancel, W.one F hF]
  have hinv' : W.Om g⁻¹ g'⁻¹ (W.Om g g' e0) = e0 := by
    rw [← W.mul _ _ _ _ _ heT, inv_mul_cancel, inv_mul_cancel, W.one e0 heT]
  refine hline _ ⟨hGT.1, fun x hx z => ?_⟩ _ hTh a1
  have hWT : Wd D (tor0 D cc δ) x (W.Om g g' e0) ∈ TT D (tor0 D cc δ) N N' := by
    obtain ⟨hd, m, hm, hfix⟩ := hGT
    refine ⟨Wd_differentiable _ hd, (La D (tor0 D cc δ) L L').relIndex (La0 D (tor0 D cc δ) N N') * m,
      Nat.mul_pos (Nat.pos_of_ne_zero a4) hm, fun y hy => ?_⟩
    have h1 := AddSubgroup.nsmul_relIndex_mem (La D (tor0 D cc δ) L L') hy
    have h2 := (La D (tor0 D cc δ) L L').nsmul_mem h1 m
    have h3 := hfix _ ((La0 D (tor0 D cc δ) N N').nsmul_mem hy
      ((La D (tor0 D cc δ) L L').relIndex (La0 D (tor0 D cc δ) N N')))
    rw [smul_smul, mul_comm] at h2 h3
    rw [← Wl_apply, ← Wl_apply, ← Module.End.mul_apply, ← a3 _ h2 _ hx, add_comm, a3 _ hx _ h2,
      Module.End.mul_apply, Wl_apply _ (W.Om g g' e0), h3]
  obtain ⟨x0, hx0, hW⟩ := _root_.GlobalTheory.WeilEquiv.om_wd_moved D hg1 cc δ hc.1.1 N N' e0 W g⁻¹ g g'⁻¹ g' L _ L' _ hL hL'
    (by rw [inv_mul_cancel]; exact moves_one D N) (by rw [inv_mul_cancel]; exact moves_one D N') x hx _ hGT
  rw [hinv', ← Wl_apply x0, a6 x0 hx0] at hW
  have h := hinv _ hWT
  rw [hW, w1 x hx] at h
  exact (congrFun h z).symm

theorem split_part {e : AE D} (h1 : e * e = e) (h2 : sgA D e = e)
    (h3 : ∀ q : ℕ, q.Prime → (InertQ D q → ZeroAt D q e) ∧ (¬ InertQ D q → ZeroAt D q (1 - e)))
    (g : GA D N) {x : (AE D)ˣ} (hx : x = Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) * sgU D x) :
    ∃ y : (AE D)ˣ, (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((y : AE D) - 1)) ∧
      y = Matrix.GeneralLinearGroup.det ((cutG e h1 h2 g : GA D N) : GL (Fin N) (AE D)) * sgU D y ∧
      ∀ {n : ℕ} (χ : HeckeU D n), Even n → χ.f y = χ.f x := by
  set d : AE D := ((Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) with hdef
  have hxv : (x : AE D) = d * sgA D x := congrArg Units.val hx
  refine ⟨Units.map (cut e h1) x, fun q hq hi => ?_, Units.ext ?_, fun χ hn => ?_⟩
  · convert VacMove.zeroAt_mul D hq ((h3 q hq).1 hi) (x - 1) using 1
    change e * x + (1 - e) * 1 - 1 = _
    ring
  · rw [Units.val_mul, det_cutG, ← hdef]
    change e * x + (1 - e) * 1 = _ * sgA D (e * x + (1 - e) * 1)
    rw [map_add (f := _), map_mul, map_mul, map_sub, map_one, h2]
    linear_combination e * hxv + ((d - 1) * (1 - sgA D x)) * h1
  · have hsplit : x = Units.map (cut e h1) x * Units.map (cut (1 - e) (compl_idem h1)) x :=
      Units.ext (cut_mul_cut e h1 (x : AE D)).1.symm
    have htriv : χ.f (Units.map (cut (1 - e) (compl_idem h1)) x) = 1 := by
      refine GlobalTheory.T.hecke_character_trivial_near_one D _ hn χ _ fun q hq hi => ?_
      convert VacMove.zeroAt_mul D hq ((h3 q hq).2 hi) (x - 1) using 1
      change (1 - e) * x + (1 - (1 - e)) * 1 - 1 = _
      ring
    conv_rhs => rw [hsplit, map_mul, htriv, mul_one]

theorem vacuum_exact : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), Even N → Even N' → ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), ∀ (W : WeilO D cc δ N N' e0) (g : GA D N) (g' : GA D N') (x x' : (AE D)ˣ) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), x = Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) * sgU D x → x' = Matrix.GeneralLinearGroup.det (g' : GL (Fin N') (AE D)) * sgU D x' → Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → W.Om g g' e0 = fun z => ((W.chV.f x' ^ W.ep * W.chV'.f x ^ W.ep' : ℂˣ) : ℂ) * Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 z := by
  intro D cc δ hc N N' hN hN' e0 he W g g' x x' L L' hx hx' hL hL'
  obtain ⟨ε, -, a1, a2, h3⟩ := VacMove.exists_half_idem D
  have h1 : (ε + sgA D ε) * (ε + sgA D ε) = ε + sgA D ε := by
    have a3 : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, a1]
    linear_combination a1 + a3 + 2 * a2
  have h2 : sgA D (ε + sgA D ε) = ε + sgA D ε := by rw [map_add (f := _), VacMove.sgA_sgA, add_comm]
  generalize ε + sgA D ε = e at h1 h2 h3
  obtain ⟨y, b1, b2, b3⟩ := split_part h1 h2 h3 g hx
  obtain ⟨y', c1, c2, c3⟩ := split_part h1 h2 h3 g' hx'
  obtain ⟨c, hO⟩ := exists_scalar hc he W hL hL'
  obtain ⟨Ls, hLs⟩ := exists_moves (cutG e h1 h2 g)
  obtain ⟨Ls', hLs'⟩ := exists_moves (cutG e h1 h2 g')
  obtain ⟨Li, hLi⟩ := exists_moves (cutG (1 - e) (compl_idem h1) (compl_fixed h2) g)
  obtain ⟨Li', hLi'⟩ := exists_moves (cutG (1 - e) (compl_idem h1) (compl_fixed h2) g')
  have hs : ∀ {n : ℕ} (k : GA D n), SuppSplit D ((cutG e h1 h2 k : GA D n) : GL (Fin n) (AE D)) :=
    fun k q hq hi => trivAt_cutG hq _ _ _ k ((h3 q hq).1 hi)
  have hi : ∀ {n : ℕ} (k : GA D n),
      SuppInert D ((cutG (1 - e) (compl_idem h1) (compl_fixed h2) k : GA D n) : GL (Fin n) (AE D)) :=
    fun k q hq hi => trivAt_cutG hq _ _ _ k ((h3 q hq).2 hi)
  have hcc := scalar_mul hc he W (cutG_mul e h1 h2 g).1 (cutG_mul e h1 h2 g).2 (cutG_mul e h1 h2 g').1
    (cutG_mul e h1 h2 g').2 (hs g) (hs g') (hi g) (hi g') hL hL' hLs hLs' hLi hLi' hO
    (W.split _ _ y y' Ls Ls' (hs g) (hs g') (fun q hq h => ⟨b1 q hq h, c1 q hq h⟩) b2 c2 hLs hLs')
    (_root_.GlobalTheory.InertSign.vacuum_inert D cc δ hc N N' (hN.mul_right N') e0 he W _ _ Li Li' (hi g) (hi g') hLi hLi')
  rw [Even.neg_one_pow ((hN.mul_right _).add (hN'.mul_right _)), one_mul, b3 _ hN', c3 _ hN] at hcc
  rw [hO, hcc]
  rfl

end GlobalTheory.VacuumExact
end
end

