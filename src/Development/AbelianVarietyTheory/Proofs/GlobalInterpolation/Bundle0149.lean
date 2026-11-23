module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0148
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.FinalEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FourthTensorThetaEqKernel
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bundle0002
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.TorsValsFinite
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicIsogenyConstantOfIsogenyFormula
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0122
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0135
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsVolumeTransportOfLatticeIsometry
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AutFormDefiniteUnitaryEqSumPolynomialMulAutFormStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.autFormDefiniteUnitary_eq_sum_polynomial_mul_autForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (φ : UA E n → ℂ), IsAutFormU φ → ∃ (m : ℕ) (p : Fin m → infU E n → ℂ) (e : Fin m → UA E n → ℂ), (∀ i, p i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j} ∧ IsAutFormU (e i)) ∧ ∀ (k : infU E n) (g : UA E n), φ (g * k) = ∑ i, p i k * e i g := by
  first | exact @GlobalTheory.UnitaryDecomp.exists_poly_mul_autForm | exact GlobalTheory.UnitaryDecomp.exists_poly_mul_autForm | (intros; apply GlobalTheory.UnitaryDecomp.exists_poly_mul_autForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqAndAlg
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomEq

theorem eq_and_alg : (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ) ∧ (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ t : VC D N N', (∃ a : ℕ, 0 < a ∧ a • t ∈ La D B.tor L L') → ∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D (U D B.tor t (B.eNat χ N N' L L')) α ∈ Qbar) :=
  ⟨fun _ _ _ B χ hcc hδ hχ => Formalism.L2.PairingIndexBounds.Eq.SqG.eulerProduct_eq_of_curve_ideal B hcc hδ χ hχ,
   fun D cc δ B χ hcc hδ hχ => GlobalTheory.ThLoc.algTAll D cc δ B χ hcc hδ hχ⟩

end GlobalTheory.MomEq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EvenThetaIteratedDerivZeroAlgebraic
section
noncomputable section

namespace GlobalTheory.ThetaZeroAlg

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker
open GlobalTheory.IsogConst

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem omegaK_eq (d : ℕ) : Formalism.L2.Th1.CM.omegaK d = Formalism.L2.Th1.F.cmTheta 1 d := by
  unfold Formalism.L2.Th1.CM.omegaK Formalism.L2.Th1.F.cmTheta; push_cast; ring

theorem hasCMBy (B : Base D cc δ) : Formalism.L2.Th1.CM.HasCMBy D.host.d B.L := by
  intro ω hω
  rw [omegaK_eq]
  exact Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hst B ω hω

theorem disc_one (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    B.L.g₂ ^ 3 - 27 * B.L.g₃ ^ 2 = 1 := by
  have hL' : (B.L.lattice : Set ℂ) = TaylorLogMetric.lamOf D cc δ := by rw [← B.lat]; rfl
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ B.L hL'
  have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  rw [← e2, ← e3]
  exact h

theorem d_sq (D : D7) : Squarefree D.host.d := (D.host.hyp.2.1 : D.host.d.Prime).squarefree

theorem host_imagQuadratic_discriminant_mod_four (D : D7) : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega

theorem g₂_g₃_mem_Qbar (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    B.L.g₂ ∈ TaylorLogMetric.Qbar ∧ B.L.g₃ ∈ TaylorLogMetric.Qbar := by
  have hdisc := disc_one B hcc hδ
  have hj : IsIntegral ℤ (Formalism.L2.Th1.CM.jInv B.L) := GlobalTheory.ThLoc.cm1 D.host.d B.L (d_sq D) (host_imagQuadratic_discriminant_mod_four D) (hasCMBy B)
  have hjQ : Formalism.L2.Th1.CM.jInv B.L ∈ TaylorLogMetric.Qbar :=
    (qbar_iff _).2 (hj.tower_top (A := ℚ)).isAlgebraic
  have hg2c : B.L.g₂ ^ 3 = Formalism.L2.Th1.CM.jInv B.L / 1728 := by
    unfold Formalism.L2.Th1.CM.jInv; rw [hdisc]; ring
  have h2 : B.L.g₂ ∈ TaylorLogMetric.Qbar := by
    refine qbar_of_pow (n := 3) (by norm_num) ?_
    rw [hg2c]; exact div_mem hjQ (nat_mem 1728)
  have h3sq : B.L.g₃ ^ 2 = (B.L.g₂ ^ 3 - 1) / 27 := by rw [← hdisc]; ring
  have h3 : B.L.g₃ ∈ TaylorLogMetric.Qbar := by
    refine qbar_of_pow (n := 2) (by norm_num) ?_
    rw [h3sq]
    exact div_mem (sub_mem (pow_mem h2 3) (one_mem _)) (nat_mem 27)
  exact ⟨h2, h3⟩

theorem kernelBase_periodLattice_sigmaTwo_algebraic (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    Formalism.L2.Th1.F.s2 B.L ∈ TaylorLogMetric.Qbar := by
  obtain ⟨h2, h3⟩ := g₂_g₃_mem_Qbar B hcc hδ
  have hd0 : 0 < D.host.d := (D.host.hyp.2.1 : D.host.d.Prime).pos
  obtain ⟨S, -, -, hIso, -⟩ := Formalism.L2.Th1.F.hasCMByIsogeny D.host.d B.L (hasCMBy B) (-1) 2 (by simp) hd0
  have hαsq := alpha_sq D.host.d
  have hα : ((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d ∈ TaylorLogMetric.Qbar :=
    qbar_of_pow (n := 2) (by norm_num) (by rw [hαsq]; exact neg_mem (natCast_mem _ _))
  have hα0 : ((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d ≠ 0 := by
    intro h0
    rw [h0] at hαsq
    have : (D.host.d : ℂ) = 0 := by linear_combination hαsq
    have : D.host.d = 0 := by exact_mod_cast this
    omega
  have he : InQ (Formalism.L2.Th1.F.pSeries B.L) := by
    intro k
    rw [Formalism.L2.KerInert.AlgP.pSeries_eq_map TaylorLogMetric.Qbar B.L h2 h3, PowerSeries.coeff_map]
    exact SetLike.coe_mem _
  have hc := algebraic_isogenyConstant_of_isogenyFormula _ he _ _ hα hα0 _ hIso
  rw [hαsq] at hc
  have hN : (((Fintype.card S + 1 : ℕ) : ℂ) - -(D.host.d : ℂ)) = ((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) := by
    push_cast; ring
  rw [hN] at hc
  have hN0 : ((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : Fintype.card S + 1 + D.host.d ≠ 0)
  have e : Formalism.L2.Th1.F.s2 B.L = (((Fintype.card S + 1 + D.host.d : ℕ) : ℂ))⁻¹ *
      (((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) * Formalism.L2.Th1.F.s2 B.L) := by
    rw [← mul_assoc, inv_mul_cancel₀ hN0, one_mul]
  rw [e]
  exact mul_mem (inv_mem (natCast_mem _ _)) hc

theorem weierstrassP_halfPeriod_algebraic (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    B.L.weierstrassP (B.ω₀ / 2) ∈ TaylorLogMetric.Qbar := by
  obtain ⟨h2, h3⟩ := g₂_g₃_mem_Qbar B hcc hδ
  haveI : Algebra.IsAlgebraic ℚ TaylorLogMetric.Qbar :=
    ⟨fun x => IntermediateField.isAlgebraic_iff.2 (mem_algebraicClosure_iff.1 x.2)⟩
  have hN : ((2 : ℕ) : ℂ) * (B.ω₀ / 2) ∈ B.L.lattice := by
    have e : ((2 : ℕ) : ℂ) * (B.ω₀ / 2) = B.ω₀ := by push_cast; ring
    rw [e]; exact B.omega_mem
  have hx : IsAlgebraic ℚ (B.L.weierstrassP (B.ω₀ / 2)) :=
    (PI.GalTorsConj.W.wp_isAlgebraic B.L TaylorLogMetric.Qbar h2 h3 2 (B.ω₀ / 2) (by norm_num) hN
      (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.half B)).restrictScalars ℚ
  exact mem_algebraicClosure_iff.2 hx

theorem evenTheta_iteratedDeriv_zero_algebraic : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.IsCurveIdeal D cc →
    TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ k : ℕ, iteratedDeriv k B.th0 0 ∈ TaylorLogMetric.Qbar := by
  intro D cc δ B hcc hδ k
  obtain ⟨h2, h3⟩ := g₂_g₃_mem_Qbar B hcc hδ
  have hc := Formalism.L2.KerInert.AlgP.theta_null_coefficients B.L B.ω₀ B.omega_mem (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.half B) TaylorLogMetric.Qbar h2 h3
    (kernelBase_periodLattice_sigmaTwo_algebraic B hcc hδ) (weierstrassP_halfPeriod_algebraic B hcc hδ) k
  unfold Formalism.L2.Th1.F.taylor0 at hc
  rw [PowerSeries.coeff_mk] at hc
  have hf : ((k.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have e : iteratedDeriv k B.th0 0 = ((k.factorial : ℕ) : ℂ) *
      (iteratedDeriv k (Formalism.L2.Th1.F.th0 B.L (B.ω₀ / 2)) 0 / ((k.factorial : ℕ) : ℂ)) := by
    rw [mul_div_cancel₀ _ hf]; rfl
  rw [e]
  exact mul_mem (natCast_mem _ _) hc

end GlobalTheory.ThetaZeroAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDefiniteUnitaryFunctionPolynomialMulSmooth
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryBC

theorem continuous_of_right_invariant_open {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (e : G → ℂ) (V : Subgroup G) (hV : IsOpen (V : Set G)) (h : ∀ u ∈ V, ∀ g, e (g * u) = e g) :
    Continuous e := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open e).2 fun x => ?_)
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (V : Set G), hV.preimage (by fun_prop), by simp, fun y hy => ?_⟩
  rw [← h _ hy x, mul_inv_cancel_left]

theorem exists_fun_of_poly_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (m : ℕ) (p : Fin m → infU E n → ℂ) (e : Fin m → finU (E := E) (n := n) → ℂ), (∀ i, p i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) → (∀ i, ∃ V : Subgroup (finU (E := E) (n := n)), IsOpen (V : Set (finU (E := E) (n := n))) ∧ ∀ u ∈ V, ∀ g, e i (g * u) = e i g) → ∃ φ : UA E n → ℂ, Continuous φ ∧ IsOpen {k : finU (E := E) (n := n) | RU E n k φ = φ} ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)) ∧ ∀ (g : finU (E := E) (n := n)) (k : infU E n), φ (g.1 * k.1) = ∑ i, p i k * e i g := by
  intro E _ _ _ n m p e hp he
  obtain ⟨-, -, -, a, b, ha, hb, -, hab⟩ := GlobalTheory.T.definiteUnitary_realApprox_and_finite_infinite_split E n
  obtain ⟨hcont, -, -, -, hco⟩ := _root_.GlobalTheory.PolyRealU.poly_infU E n
  choose V hVo hV using he
  have haf : ∀ g : finU (E := E) (n := n), a g.1 = g := fun g => by simpa using (hab g 1).1
  have hbf : ∀ g : finU (E := E) (n := n), b g.1 = 1 := fun g => by simpa using (hab g 1).2
  have hai : ∀ k : infU E n, a k.1 = 1 := fun k => by simpa using (hab 1 k).1
  have hbi : ∀ k : infU E n, b k.1 = k := fun k => by simpa using (hab 1 k).2
  have hR : ∀ (x : UA E n) (φ : UA E n → ℂ) (g : UA E n), RU E n x φ g = φ (g * x) := fun _ _ _ => rfl
  refine ⟨fun x => ∑ i, p i (b x) * e i (a x), ?_, ?_, ?_, fun g k => ?_⟩
  · exact continuous_finsetSum _ fun i _ => ((hcont _ (hp i)).comp hb).mul
      ((continuous_of_right_invariant_open _ _ (hVo i) (hV i)).comp ha)
  · set φ : UA E n → ℂ := fun x => ∑ i, p i (b x) * e i (a x) with hφ
    let S : Subgroup (finU (E := E) (n := n)) :=
      { carrier := {k : finU (E := E) (n := n) | RU E n k φ = φ}
        one_mem' := by
          change RU E n ((1 : finU (E := E) (n := n)) : UA E n) φ = φ
          funext g
          rw [hR]
          simp
        mul_mem' := fun {x y} hx hy => by
          change RU E n ((x * y : finU (E := E) (n := n)) : UA E n) φ = φ
          funext g
          have h1 := congrFun (show RU E n x φ = φ from hx) g
          have h2 := congrFun (show RU E n y φ = φ from hy) (g * x)
          rw [hR] at h1 h2 ⊢
          rw [Subgroup.coe_mul, ← mul_assoc, h2, h1]
        inv_mem' := fun {x} hx => by
          change RU E n ((x⁻¹ : finU (E := E) (n := n)) : UA E n) φ = φ
          funext g
          have h1 := congrFun (show RU E n x φ = φ from hx) (g * (x : UA E n)⁻¹)
          rw [hR] at h1 ⊢
          rw [Subgroup.coe_inv, ← h1, inv_mul_cancel_right] }
    have hle : (⨅ i, V i) ≤ S := fun u hu => by
      change RU E n (u : UA E n) φ = φ
      funext g
      rw [hR]
      simp only [hφ, map_mul, haf, hbf, mul_one]
      exact Finset.sum_congr rfl fun i _ => by rw [hV i u (Subgroup.mem_iInf.1 hu i)]
    refine Subgroup.isOpen_mono hle ?_
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite hVo
  · choose N c d _ hcd using fun i => hco _ (hp i)
    let f : (Σ i, Fin (N i)) → UA E n → ℂ := fun s x => c s.1 s.2 (b x) * e s.1 (a x)
    haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range f)) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range f)
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range f)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    have : RU E n k (fun x => ∑ i, p i (b x) * e i (a x)) = ∑ s : Σ i, Fin (N i), d s.1 s.2 k • f s := by
      funext g
      rw [hR]
      simp only [map_mul, hai, hbi, mul_one, hcd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, f,
        Fintype.sum_sigma, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    change RU E n k _ ∈ _
    rw [this]
    exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  · simp only [(hab g k).1, (hab g k).2]

end GlobalTheory.UnitaryBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIntegralCoordinatesTwistedTrueChainStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralCoordinates_twistedTrueChain : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι), ∃ P : GlobalTheory.PerQ.PendTw (I.rec7 l Z) (I.tw l l0 Z) u a, ∀ τ, P.br τ = brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ (I.rec7 l Z).R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ) (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ) := by
  first | exact @GlobalTheory.PerQ.Co.pendTw_exists | exact GlobalTheory.PerQ.Co.pendTw_exists | (intros; apply GlobalTheory.PerQ.Co.pendTw_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GenusMassAtTwo
section
namespace GlobalTheory

theorem genusMassAt_two : ∀ D : Formalism.BasicNotions.D7, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.GenusMassAt D 2 :=
  fun D => Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.genusMassAt_of D (genusMassStd_all D) 2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianClassNumberItemsAllRanks
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem classItemsAt_all : ∀ (D : D7) (n : ℕ), ClassItemsAt D n := fun D n =>
  have h := _root_.GlobalTheory.ClassNumberMass.classFin_and_classMass D
  ⟨genusMassAt_of D (GlobalTheory.genusMassStd_all D) n, classFinAt_of D h.1 n, classMassAt_of D h.2 n⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFundamentalDomainMap
section
noncomputable section

namespace GlobalTheory.VolumeIndep

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open GlobalTheory.VolTransport GlobalTheory.IndefiniteRowSideFullHecke.SignatureLatticeIndependence
open scoped TensorProduct Matrix ENNReal

theorem isFundamentalDomain_map {G H : Type} [Group G] [Group H] [MeasurableSpace G] [MeasurableSpace H]
    (φ : G ≃* H) (hc : Measurable φ) (hc' : Measurable φ.symm) (Γ : Subgroup G) (Γ' : Subgroup H)
    (hQ : ∀ g, g ∈ Γ ↔ φ g ∈ Γ') (μ : Measure G) (𝓕 : Set G) :
    IsFundamentalDomain Γ 𝓕 μ ↔ IsFundamentalDomain Γ' (φ '' 𝓕) (μ.map φ) := by
  let ψ : G ≃ᵐ H := ⟨φ.toEquiv, hc, hc'⟩
  have hψ : MeasurePreserving ψ μ (μ.map φ) := ⟨ψ.measurable, rfl⟩
  constructor
  · intro h
    have e : φ '' 𝓕 = φ.symm ⁻¹' 𝓕 := φ.toEquiv.image_eq_preimage_symm 𝓕
    rw [e]
    exact h.preimage_of_equiv (f := φ.symm) (MeasurePreserving.symm ψ hψ).quasiMeasurePreserving
      (e := fun γ => ⟨φ γ, (hQ γ).1 γ.2⟩)
      ⟨fun a b hab => Subtype.ext (φ.injective (congrArg Subtype.val hab)),
        fun b => ⟨⟨φ.symm b, (hQ _).2 (by simp)⟩, Subtype.ext (by simp)⟩⟩
      fun γ y => by
        show φ.symm (φ γ * y) = γ * φ.symm y
        rw [map_mul, φ.symm_apply_apply]
  · intro h
    have e : 𝓕 = φ ⁻¹' (φ '' 𝓕) := (φ.injective.preimage_image 𝓕).symm
    rw [e]
    exact h.preimage_of_equiv (f := φ) hψ.quasiMeasurePreserving
      (e := fun γ => ⟨φ.symm γ, (hQ _).2 (by simp)⟩)
      ⟨fun a b hab => Subtype.ext (φ.symm.injective (congrArg Subtype.val hab)),
        fun b => ⟨⟨φ b, (hQ b).1 b.2⟩, Subtype.ext (by simp)⟩⟩
      fun γ y => by
        show φ (φ.symm γ * y) = γ * φ y
        rw [map_mul, φ.apply_symm_apply]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isoPair_of_isometry (V V' : HSp D) (e : V.V ≃ₗ[D.host.E] V'.V)
    (he : ∀ x y, V'.hT (e x) (e y) = V.hT x y) :
    IsoPair (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram V'.gram
      (LinearMap.toMatrix V.frame V'.frame e.toLinearMap)
      (LinearMap.toMatrix V'.frame V.frame e.symm.toLinearMap) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix_comp]; simp
  · rw [← LinearMap.toMatrix_comp]; simp
  · exact GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embMat_isom D.sp.cm V V' e.toLinearMap he
  · exact GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embMat_isom D.sp.cm V' V e.symm.toLinearMap (fun x y => by
      have := he (e.symm x) (e.symm y)
      rw [e.apply_symm_apply, e.apply_symm_apply] at this
      exact this.symm)

theorem isVolMeas_map (V V' : HSp D) {T : Matrix (Fin V'.rank) (Fin V.rank) D.host.E}
    {T' : Matrix (Fin V.rank) (Fin V'.rank) D.host.E}
    (h : IsoPair (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram V'.gram T T')
    (hL : ∀ x ∈ L0c D V, T *ᵥ x ∈ L0c D V') (hL' : ∀ x ∈ L0c D V', T' *ᵥ x ∈ L0c D V)
    (P Q : ℕ) (μ : Measure (GA D V)) (hμ : IsVolMeas D V P Q μ) : IsVolMeas D V' P Q (μ.map (conjA h)) := by
  have c1 := conjA_continuous h
  have c2 : Continuous (conjA h).symm := conjA_continuous h.symm
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V'.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V'.gram
  have := hμ.1
  have hτ : ∀ (ρ : D.what₂.Tau) a, embOf D ρ ((D.sp.cm.sig : D.host.E →+* D.host.E) a) =
      starRingEnd ℂ (embOf D ρ a) := fun ρ a => D.sp.cm.cmUnram.2.1 _ a
  refine ⟨MulEquiv.isHaarMeasure_map μ (conjA h) c1 c2, hμ.2.1, fun θ hθ => ⟨?_, ?_⟩⟩
  · obtain ⟨A, hA⟩ := (hμ.2.2 θ hθ).1
    exact ⟨_, fun ρ => frame_transport h.symm (embOf D ρ) (hτ ρ) _ (A ρ) (hA ρ)⟩
  · intro A hA B hB
    have key := (hμ.2.2 θ hθ).2 _
      (fun ρ => frame_transport h (embOf D ρ) (hτ ρ) _ (A ρ) (hA ρ)) B hB
    let H : GA D V ≃ₜ GA D V' := ⟨(conjA h).toEquiv, c1, c2⟩
    refine Eq.trans (H.toMeasurableEquiv.map_apply _) ?_
    refine Eq.trans (congrArg μ ?_) key
    ext g
    refine and_congr (stab_transport h hL hL' g) ?_
    refine forall_congr' fun ρ => exists_congr fun b => and_congr Iff.rfl ?_
    refine Iff.trans ?_ (frame_iff h (embOf D ρ) _ (A ρ) _)
    rw [← conjA_infMat h g (hθ ρ)]
    rfl

theorem latticeIndependence (D : D7) : LatticeIndependence D := by
  intro W P Q _ L L' hL hU hL' hU' μ
  exact ⟨fun h => GlobalTheory.VolumeRatioTypings.isVolMeas_reLat (withLattice W L hL hU) L' hL' hU' h
      (GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D W μ h.1),
    fun h => GlobalTheory.VolumeRatioTypings.isVolMeas_reLat (withLattice W L' hL' hU') L hL hU h
      (GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D W μ h.1)⟩

theorem isometryTransport (D : D7) : IsometryTransport D := by
  intro V V' P Q _ _ e he hL
  have h := isoPair_of_isometry V V' e he
  have c1 := conjA_continuous h
  have c2 : Continuous (conjA h).symm := conjA_continuous h.symm
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V'.gram
  have l1 := mem_std_lattice_iff_integral_coords D V V' e.toLinearMap fun x => (hL x).1
  have l2 := mem_std_lattice_iff_integral_coords D V' V e.symm.toLinearMap fun x hx => (hL _).2 (by simpa using hx)
  have hQ : ∀ g, g ∈ GQ V ↔ conjA h g ∈ GQ V' := fun g => ⟨conjA_rat h g, fun hg => by
    have := conjA_rat h.symm _ hg
    rwa [← conjA_symm h, MulEquiv.symm_apply_apply] at this⟩
  refine ⟨⟨conjA h, c1, c2⟩, fun g => ?_, hQ, fun μ => ⟨isVolMeas_map V V' h l1 l2 P Q μ, fun hμ => ?_⟩,
    fun μ _ 𝓕 => isFundamentalDomain_map (conjA h) c1.measurable c2.measurable (GQ V) (GQ V') hQ μ 𝓕⟩
  · have e1 := conjA_mat h g
    have e2 := h.adelic.2.1
    unfold Intertwines pointMatrix baseChange frameMatrix
    refine (congrArg (· * _) e1).trans ?_
    show _ * _ * _ * _ = _
    rw [Matrix.mul_assoc, e2, Matrix.mul_one]
  · have k := isVolMeas_map V' V h.symm l2 l1 P Q _ hμ
    have e3 : Measure.map (conjA h.symm) (Measure.map (conjA h) μ) = μ := by
      refine (Measure.map_map c2.measurable c1.measurable).trans ?_
      rw [show ((conjA h).symm : _ → _) ∘ (conjA h) = id from funext (conjA h).symm_apply_apply, Measure.map_id]
    exact e3 ▸ k

theorem volumeInvariance (D : D7) : VolumeInvariance D := by
  intro hT V V' P Q hV hV' ⟨e, he⟩
  have pos : ∀ W : HSp D, HasSignatureEverywhere W P Q → 0 < D.vol W := fun W hW => by
    obtain ⟨⟨μ, hμ⟩, hall⟩ := hT W P Q hW.1 hW.2
    obtain ⟨⟨𝓕, h𝓕⟩, hv⟩ := hall μ hμ
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig W.gram
    have := hμ.1
    have : Countable (GQ W) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ W)
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ W) μ
    have h𝓕' : IsFundamentalDomain (GQ W) 𝓕 μ := h𝓕
    have := h𝓕'.measure_ne_zero (NeZero.ne μ)
    rw [hv 𝓕 h𝓕] at this
    exact ENNReal.ofReal_pos.1 (pos_iff_ne_zero.2 this)
  have h1 : GlobalTheory.IndefiniteRowSideFullHecke.VolumePerpendicular.IsVol D V P Q (D.vol V) := ⟨pos V hV, hT V P Q hV.1 hV.2⟩
  have h2 := GlobalTheory.VolumeRatioTypings.isVol_of_isometry V V' e he h1
  obtain ⟨⟨μ, hμ⟩, hall⟩ := hT V' P Q hV'.1 hV'.2
  obtain ⟨⟨𝓕, h𝓕⟩, hv⟩ := hall μ hμ
  exact (ENNReal.ofReal_eq_ofReal_iff (pos V hV).le (pos V' hV').le).1
    (((h2.2.2 μ hμ).2 𝓕 h𝓕).symm.trans (hv 𝓕 h𝓕))

theorem volumeIndependence (D : D7) : VolumeIndependence D :=
  ⟨latticeIndependence D, isometryTransport D, volumeInvariance D⟩

end GlobalTheory.VolumeIndep
end
end

