module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1334
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1208
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0898
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298
public import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasOrbIntTensorOfHasOrbInt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightedOrbitalIntegralTypeTestVanish
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
public import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0424
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemValuationEq
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA (Dinv xi_mem_Dinv int_of_xi)
open GlobalTheory.FunObj.Good (char_int mem_Dinv atPl_mul inc_mul_inc mem_intAE exists_pole isEquiv_Kw valued_alg psiAt_eq_one
  trace_inc_pair cpt_pair)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7}

namespace CondAA

theorem valued_genAt (w : Pl D.host.E) (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
    Valued.v ((genAt w 𝔞 : (Kw w)ˣ) : Kw w) = WithZero.exp (-FractionalIdeal.count D.host.E w 𝔞) := by
  have hu : Valued.v (unifAt w : Kw w) = WithZero.exp (-1 : ℤ) := unif_spec w
  rw [genAt, Units.val_zpow_eq_zpow_val, map_zpow₀, hu, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one]

theorem exists_mem_valuation_eq (w : Pl D.host.E) {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hI : I ≠ 0) :
    ∃ c ∈ I, w.valuation D.host.E c = WithZero.exp (-FractionalIdeal.count D.host.E w I) := by
  have hw0 : (w.asIdeal : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 w.ne_bot
  have hIw : I * w.asIdeal ≠ 0 := mul_ne_zero hI hw0
  have hne : ¬ I ≤ I * w.asIdeal := fun h => by
    have := FractionalIdeal.count_mono D.host.E w hI h
    rw [FractionalIdeal.count_mul D.host.E w hI hw0, FractionalIdeal.count_self] at this
    omega
  obtain ⟨c, hc, hc'⟩ := SetLike.not_le_iff_exists.1 hne
  refine ⟨c, hc, le_antisymm ((GlobalTheory.Idele.mem_iff_valuation_le hI c).1 hc w) ?_⟩
  by_contra hlt
  push_neg at hlt
  refine hc' ((GlobalTheory.Idele.mem_iff_valuation_le hIw c).2 fun Q => ?_)
  rw [FractionalIdeal.count_mul D.host.E Q hI hw0]
  by_cases hQ : w = Q
  · subst hQ
    rw [FractionalIdeal.count_self]
    rcases eq_or_ne (w.valuation D.host.E c) 0 with h0 | h0
    · rw [h0]; exact zero_le'
    · rw [← WithZero.exp_log h0, WithZero.exp_lt_exp] at hlt
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
      omega
  · rw [FractionalIdeal.count_maximal_coprime D.host.E Q hQ, add_zero]
    exact (GlobalTheory.Idele.mem_iff_valuation_le hI c).1 hc Q

end CondAA


open CondAA in
theorem hasConductor_psiAt_AA {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (w : Pl D.host.E) :
    HasConductor (psiAt W w) (genAt w D.host.AA * genAt w D.host.AAbar) := by
  classical
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have e := isEquiv_Kw w
  have hA : D.host.AA ≠ 0 := Formalism.L2.Pj.AA_ne_zero hP D
  have hB : D.host.AAbar ≠ 0 := fun h => by
    have h1 := hP D.R D.host
    rw [h, mul_zero, zero_mul] at h1
    exact zero_ne_one h1
  have hI : D.host.AA * D.host.AAbar ≠ 0 := mul_ne_zero hA hB
  set n := FractionalIdeal.count D.host.E w (D.host.AA * D.host.AAbar) with hn
  have hv : Valued.v (((genAt w D.host.AA * genAt w D.host.AAbar : (Kw w)ˣ)) : Kw w) = WithZero.exp (-n) := by
    rw [Units.val_mul, map_mul, valued_genAt, valued_genAt, ← WithZero.exp_add, hn,
      FractionalIdeal.count_mul D.host.E w hA hB, neg_add]
  have hint : ∀ y : Kw w, Valued.v y ≤ 1 → finPart D (atPl w y) ∈ intAE D := fun y hy => mem_intAE fun Q => by
    rw [(atPl_spec w y).2]
    by_cases h : Q = w
    · subst h; simpa using hy
    · simp [h]
  intro x
  rw [e x, hv]
  refine ⟨fun h => ?_, fun hx y hy => ?_⟩
  · by_contra hx
    obtain ⟨u, hu, hu1, hu2⟩ := exists_pole w
    refine hu (int_of_xi hP D fun a ha j hj => mem_Dinv.2 fun c => ?_)
    have hx1 : WithZero.exp (-n + 1) ≤ Valued.v x := by
      have h0 : Valued.v x ≠ 0 := fun h0 => hx (h0 ▸ zero_le')
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp] at hx
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
      omega
    have haj : w.valuation D.host.E (a * j) ≤ WithZero.exp (-n) :=
      (GlobalTheory.Idele.mem_iff_valuation_le hI (a * j)).1 (FractionalIdeal.mul_mem_mul ha hj) w
    have hn' : D.host.xi0 * (a * j) * c ∈ Dinv D := by
      rw [mul_comm]
      exact (Dinv D).coeToSubmodule.smul_mem c (xi_mem_Dinv hP D ha hj)
    have h1 := (psiAt_eq_one W w _).1 (h (algebraMap D.host.E (Kw w) (a * j * c) * algebraMap D.host.E (Kw w) u) (by
      rw [e, map_mul, valued_alg, valued_alg, map_mul]
      refine le_trans ?_ hx1
      calc _ ≤ WithZero.exp (-n) * 1 * WithZero.exp (1 : ℤ) :=
            mul_le_mul' (mul_le_mul' haj (w.valuation_le_one c)) hu1
        _ = _ := by rw [mul_one, ← WithZero.exp_add]))
    rw [atPl_mul, inc_mul_inc] at h1
    have h2 := char_int W.ψ_std hn' (z := pairA D.host.F 0 1 ⊗ₜ[D.host.F] u - atPl w (algebraMap D.host.E (Kw w) u))
      (by rw [RingHom.map_sub, GlobalTheory.LatVac.infPart_pair, (atPl_spec w _).1, sub_zero]) (mem_intAE fun Q => by
        rw [RingHom.map_sub, RingHom.map_sub, cpt_pair, (atPl_spec w _).2]
        by_cases hQ : Q = w
        · subst hQ; simp
        · rw [Pi.single_eq_of_ne hQ, sub_zero, valued_alg]
          exact hu2 Q hQ)
    rw [← mul_assoc D.host.xi0, ← mul_assoc D.host.xi0] at h1
    rw [← mul_assoc D.host.xi0] at h2
    have h3 : W.ψ (Algebra.trace (AF D.host.F) (AE D)
        (incA D (D.host.xi0 * a * j * c) * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] u))) = 1 := by
      rw [← sub_add_cancel (pairA D.host.F 0 1 ⊗ₜ[D.host.F] u : AE D) (atPl w (algebraMap D.host.E (Kw w) u)), mul_add,
        map_add, W.ψ.map_add_eq_mul, h1, h2, one_mul]
    rw [trace_inc_pair, one_mul, GlobalTheory.LatVac.char_rat W.ψ_std] at h3
    rwa [show D.host.xi0 * (a * (j * u)) * c = D.host.xi0 * a * j * c * u by ring]
  · obtain ⟨c, hc, hcv⟩ := exists_mem_valuation_eq w hI
    have hy1 : Valued.v y ≤ WithZero.exp (-n) := ((e y x).1 hy).trans hx
    have hξc : D.host.xi0 * c ∈ Dinv D := by
      rw [show Dinv D = _ from (Formalism.L2.Pj.dual_eq hP D).symm, mul_assoc]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hc
    have hvc : Valued.v (algebraMap D.host.E (Kw w) c) = WithZero.exp (-n) := by rw [valued_alg, hcv]
    have h0 : algebraMap D.host.E (Kw w) c ≠ 0 := fun h => by
      rw [h, map_zero] at hvc
      exact WithZero.exp_ne_zero hvc.symm
    rw [psiAt_eq_one, ← mul_inv_cancel_left₀ h0 y, atPl_mul, inc_mul_inc]
    refine char_int W.ψ_std hξc (atPl_spec w _).1 (hint _ ?_)
    rw [map_mul, map_inv₀, hvc]
    calc _ ≤ (WithZero.exp (-n))⁻¹ * WithZero.exp (-n) := mul_le_mul' le_rfl hy1
      _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero

end GlobalTheory.FunObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthonormalBasisSplitSupportedAdelicPoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FunObj.StdVertex


set_option maxHeartbeats 6000000 in
theorem exists_std_vertex : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), V.SigOK →
    (∀ τ, V.sig τ = (V.rank, 0)) → IsSelfDualC V Λ → ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) →
    ∃ (fr : GL (Fin V.rank) D.host.E) (u : GfC V),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V u.1 ∧ ∀ w ∈ P, Off S w) ∧
      ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE V u.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  intro D V Λ hsig hpos hΛ S hS
  obtain ⟨fr0, hfr0⟩ := _root_.GlobalTheory.DefiniteFrame.exists_unitary_frame D V hsig hpos
  obtain ⟨x, hxx⟩ := GlobalTheory.T.exists_finiteAdelicUnitary_moves_selfDualLattice D V fr0 Λ hfr0 hΛ
  have hx : x ∈ GfC V := hxx.1
  have hxL := hxx.2
  obtain ⟨γ, h, k, hr⟩ := GlobalTheory.T.idempotent_support_hermitian_decomposition D V fr0 S hS x hx
  have hγ := hr.1
  have hh := hr.2.1
  have hsupp := hr.2.2.1
  have hkL := hr.2.2.2.2.1
  have hxe := hr.2.2.2.2.2
  obtain ⟨u, hur⟩ := _root_.GlobalTheory.ConjSplit.conj_supp D V S γ h hγ hh hsupp
  have hu : u ∈ GfC V := hur.1
  have hue := hur.2.2
  refine ⟨γ * fr0, ⟨u, hu⟩, ?_, hur.2.1, ?_⟩
  · have e1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (γ * fr0).1 =
        Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr0.1 * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 := by
      simp only [Formalism.UG.cT, Units.val_mul, Matrix.map_mul, Matrix.transpose_mul]
    rw [e1, Units.val_mul]
    calc _ = Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr0.1 *
          (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 * V.gram * γ.1) * fr0.1 := by
            simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hγ, hfr0]
  · intro v
    have hγγ : γ.1.map (eToEAf D) * (γ⁻¹).1.map (eToEAf D) = 1 := by
      rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    have hKK : (Formalism.IndefR.Lev.finE V k).1 * ((Formalism.IndefR.Lev.finE V k)⁻¹).1 = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h1 : ∀ w, w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr0) ↔
        ((Formalism.IndefR.Lev.finE V k)⁻¹).1 *ᵥ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr0) := fun w => by
      rw [hkL (((Formalism.IndefR.Lev.finE V k)⁻¹).1 *ᵥ w), Matrix.mulVec_mulVec, hKK, Matrix.one_mulVec]
    have key : (Formalism.IndefR.Lev.finE V x).1 *ᵥ (((Formalism.IndefR.Lev.finE V k)⁻¹).1 *ᵥ ((γ⁻¹).1.map (eToEAf D) *ᵥ v)) =
        (Formalism.IndefR.Lev.finE V u).1 *ᵥ v := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hxe, hue]
      congr 1
      calc _ = γ.1.map (eToEAf D) * (Formalism.IndefR.Lev.finE V h).1 *
            ((Formalism.IndefR.Lev.finE V k).1 * ((Formalism.IndefR.Lev.finE V k)⁻¹).1) * (γ⁻¹).1.map (eToEAf D) := by
              simp only [Matrix.mul_assoc]
        _ = _ := by rw [hKK, Matrix.mul_one]
    have s1 := GlobalTheory.T.mem_completedLattice_columnLattice_mul_iff D γ fr0 v
    have s2 := h1 ((γ⁻¹).1.map (eToEAf D) *ᵥ v)
    have s3 := hxL (((Formalism.IndefR.Lev.finE V k)⁻¹).1 *ᵥ ((γ⁻¹).1.map (eToEAf D) *ᵥ v))
    rw [key] at s3
    exact s1.trans (s2.trans s3)

end GlobalTheory.FunObj.StdVertex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatRepr
section
open GlobalTheory.SqTop

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.CMVal
open Formalism.L2.Host (HChar)

namespace GlobalTheory.ToricExist

theorem exists_rat_repr (D : D7) {w : D.host.E} (hw : w ^ 2 = -(D.host.d : D.host.E)) (hd : 0 < D.host.d)
    (σ : D.host.E →+* ℂ) (hσ : σ w = Complex.I * (Real.sqrt D.host.d : ℝ)) :
    w ∈ D.host.K ∧ ∀ y : D.host.K, ∃ a b : ℚ, (y : D.host.E) = (a : D.host.E) + (b : D.host.E) * w := by
  set bb : D.host.E := D.host.sqd with hbb
  have hb : bb ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  have hbK : bb ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ _
  have hwb : w = bb ∨ w = -bb := by
    have h0 : (w - bb) * (w + bb) = 0 := by
      have : (w - bb) * (w + bb) = w ^ 2 - bb ^ 2 := by ring
      rw [this, hw, hb, sub_self]
    rcases mul_eq_zero.1 h0 with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hwK : w ∈ D.host.K := by
    rcases hwb with h | h
    · rw [h]; exact hbK
    · rw [h]; exact neg_mem hbK
  refine ⟨hwK, fun y => ?_⟩
  let wK : D.host.K := ⟨w, hwK⟩
  have hli : LinearIndependent ℚ ![(1 : D.host.K), wK] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h0 : (s : D.host.E) + (t : D.host.E) * w = 0 := by
      have := congrArg Subtype.val hst
      simpa [Rat.smul_def, wK] using this
    have h1 := congrArg σ h0
    simp only [map_add (f := _), map_mul, map_ratCast, map_zero, hσ] at h1
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    simp at hre him
    refine ⟨by exact_mod_cast hre, ?_⟩
    rcases him with h | h
    · exact_mod_cast h
    · exact absurd h hd.ne'
  have hcard : Fintype.card (Fin 2) = Module.finrank ℚ D.host.K := by
    rw [GlobalTheory.CurveLattice.finrank_hostK]; rfl
  let B := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hB : ∀ i, B i = ![(1 : D.host.K), wK] i := fun i => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]
  refine ⟨B.repr y 0, B.repr y 1, ?_⟩
  have e := B.sum_repr y
  rw [Fin.sum_univ_two, hB, hB] at e
  have e2 := congrArg (fun z : D.host.K => (z : D.host.E)) e
  simp only [IntermediateField.coe_add, IntermediateField.coe_smul, Matrix.cons_val_zero, Matrix.cons_val_one,
    IntermediateField.coe_one, Rat.smul_def, mul_one] at e2
  rw [← e2]
  rfl

theorem exists_phiK (D : D7) (hFD : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (cmPhi D)) :
    ∃ φK : D.host.K →+* ℂ, (∀ τ, (cmPhi D τ).comp (algebraMap D.host.K D.host.E) = φK) ∧
      ∀ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf φK 1 Λ := by
  obtain ⟨-, hd4, -, -, -, hcard, -, w, hw, hwφ⟩ := hFD
  have hne : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨τ₀⟩ := hne
  obtain ⟨hwK, hrep⟩ := exists_rat_repr D hw (by omega) (cmPhi D τ₀) (hwφ τ₀)
  let φK : D.host.K →+* ℂ := (cmPhi D τ₀).comp (algebraMap D.host.K D.host.E)
  have hval : ∀ (τ : D.what₂.Tau) (y : D.host.K) (a b : ℚ), (y : D.host.E) = (a : D.host.E) + (b : D.host.E) * w →
      cmPhi D τ (y : D.host.E) = (a : ℂ) + (b : ℂ) * (Complex.I * (Real.sqrt D.host.d : ℝ)) := by
    intro τ y a b h
    rw [h, map_add (f := _), map_mul, map_ratCast, map_ratCast, hwφ τ]
  have hcomp : ∀ τ, (cmPhi D τ).comp (algebraMap D.host.K D.host.E) = φK := fun τ => by
    ext y
    obtain ⟨a, b, h⟩ := hrep y
    show cmPhi D τ (y : D.host.E) = cmPhi D τ₀ (y : D.host.E)
    rw [hval τ y a b h, hval τ₀ y a b h]
  refine ⟨φK, hcomp, fun Λ hΛ => ?_⟩
  have hinj : Function.Injective φK := φK.injective
  ext x
  simp only [Set.mem_image, SetLike.mem_coe]
  constructor
  · intro hx
    obtain ⟨hint, a, b, rfl⟩ := (hΛ x).1 hx
    let y : D.host.K := (a : D.host.K) + (b : D.host.K) * ⟨w, hwK⟩
    have hy : φK y = (a : ℂ) + (b : ℂ) * (Complex.I * (Real.sqrt D.host.d : ℝ)) := by
      show cmPhi D τ₀ (y : D.host.E) = _
      exact hval τ₀ y a b (by simp [y])
    refine ⟨y, ?_, hy⟩
    have hyi : IsIntegral ℤ y := (isIntegral_algHom_iff φK.toIntAlgHom hinj).1 (by rw [← hy] at hint; exact hint)
    exact (FractionalIdeal.mem_one_iff _).2 ⟨⟨y, hyi⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨y', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hy
    obtain ⟨a, b, h⟩ := hrep (algebraMap (𝓞 D.host.K) D.host.K y')
    refine (hΛ _).2 ⟨?_, a, b, hval τ₀ _ a b h⟩
    exact (RingOfIntegers.isIntegral_coe y').map φK.toIntAlgHom

theorem gBig_of {P R : GP} (hP : GBig P)
    (h : ∀ {D : D7} {T : Type} {Lc : Formalism.IndefR.Links.LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Lc.Is μ₀ → P G μ₀ C x b → R G μ₀ C x b) : GBig R := by
  obtain ⟨CF0, h1⟩ := hP
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h2⟩ := h1 ε CF hCF
  exact ⟨C0, x0, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => h G μ₀ _ _ _ hμ (h2 C hC D large₂ he hx hr T Lc μ₀ hμ G)⟩

theorem gBig_and {P Q : GP} (hP : GBig P) (hQ : GBig Q) :
    GBig fun {_ _ _ _} G μ₀ C x b => P G μ₀ C x b ∧ Q G μ₀ C x b := by
  obtain ⟨CF1, h1⟩ := hP
  obtain ⟨CF2, h2⟩ := hQ
  refine ⟨max CF1 CF2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, k1⟩ := h1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, x2, k2⟩ := h2 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => ⟨?_, ?_⟩⟩
  · exact k1 C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hr T Lc μ₀ hμ G
  · exact k2 C (le_trans (le_max_right _ _) hC) D large₂ he (le_trans (le_max_right _ _) hx) hr T Lc μ₀ hμ G

theorem exists_prime {E : Type} [Field E] [NumberField E] {𝔣 : Ideal (OF E)} (h : IsBaseCond 𝔣) :
    Nonempty (HeightOneSpectrum (𝓞 E)) := by
  obtain ⟨M, hM, hfM⟩ := Ideal.exists_le_maximal 𝔣 h.2.1
  let v : HeightOneSpectrum (OF E) := ⟨M, hM.isPrime, fun e => h.1 (eq_bot_iff.2 (e ▸ hfM))⟩
  obtain ⟨P, -⟩ := (h.2.2 v (Ideal.dvd_iff_le.2 hfM)).1
  exact ⟨P⟩

theorem torEx : GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport → FieldDat → LNe → TorEx := by
  intro hT hF hL
  refine gBig_of (gBig_and hF hL) ?_
  intro D T Lc sc G μ₀ C x b hμ ⟨hf, hl⟩ i j s hs1 hs2 c
  obtain ⟨hCM, hAb, hFD, hBC, -⟩ := hf
  have hFD' := hFD
  obtain ⟨-, hd4, hU, -, -, hcard, hφ, -⟩ := hFD
  have hV : IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) ∅ (fam G μ₀ i j c) := by
    cases c with
    | none => exact (GlobalTheory.FunObj.SqNum.Model.isValChar_nu hμ G i j hs2).1
    | some c => exact (GlobalTheory.FunObj.SqNum.Model.isValChar_nu hμ G i j hs2).2 c
  obtain ⟨P⟩ := exists_prime hBC
  have hAux : IsFinSetSplitPlacesCoprimeConductor (condF G.pl) ∅ := fun q hq => absurd hq (Finset.notMem_empty q)
  have hTS : ∀ Λ, IsHeckeL (fam G μ₀ i j c) Λ →
      IsToricSum (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) (fam G μ₀ i j c) (Λ s) := fun Λ hΛ => by
    have := GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.Published.HeckeEntire_holds D.host.E D.what₂.Tau (cmPhi D) hφ s
      (kap D sc.cGap i j s) (condF G.pl) ∅ (fam G μ₀ i j c) (fun _ => P) Λ hU hs1 hBC hAux hV
      (fun q hq => absurd hq (Finset.notMem_empty q)) hΛ
    simpa [condQ] using this
  obtain ⟨Λ, hΛ, hne⟩ := (hl i j).2 c
  refine ⟨Λ s, ⟨hV, hTS Λ hΛ⟩, hne s hs1, fun Λ' h => by rw [hΛ.unique h], fun Λ₁ hΛ₁ => ?_⟩
  obtain ⟨φK, hcomp, hlat⟩ := exists_phiK D hFD'
  haveI := hCM
  haveI := hAb
  obtain ⟨t, 𝔞, Λσ, -, -, hTr⟩ := hT D.host.K D.host.d hd4 (GlobalTheory.CurveLattice.finrank_hostK D)
    (GlobalTheory.CurveLattice.discr_hostK D) φK Λ₁ (hlat Λ₁ hΛ₁)
  have hk := hTr D.host.E hU D.what₂.Tau (cmPhi D) hcard hφ hcomp s (kap D sc.cGap i j s) (condF G.pl) hs1
    (fun τ => (GlobalTheory.FunObj.SqNum.Model.kap_add D sc.cGap i j τ hs2).2) hBC
  exact (hk.1 ∅ _ _ ⟨hAux, hV, by simpa [condQ] using hTS Λ hΛ⟩).1

end GlobalTheory.ToricExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryCarryHyperbolicFamilyWittFrame
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.WittCarry

theorem exists_GF_carry_hyperbolic : ∀ {D : D7} {V : HSp D} (Φ : WittFrame V) {a : ℕ} (ha : a ≤ wittIndex V) (x x' : Fin a → V.V), LinearIndependent D.host.E (Sum.elim x x') → (∀ i j, V.hD (x i) (x j) = 0) → (∀ i j, V.hD (x' i) (x' j) = 0) → (∀ i j, V.hD (x i) (x' j) = if i = j then 1 else 0) → ∃ g : GF V, ∀ i, GlobalTheory.Cusp.ratAct D.sp.cm V g (x i) = Φ.e (Fin.castLE ha i) ∧ GlobalTheory.Cusp.ratAct D.sp.cm V g (x' i) = Φ.f (Fin.castLE ha i) := by
  intro D V Φ a ha x x' hli h1 h2 h3
  classical
  have hs : ∀ u w, star (V.hT u w) = V.hT w u := fun u w => V.herm.eq u w
  have hn : ∀ u, (∀ w, V.hT u w = 0) → u = 0 := fun u hu => V.nondeg.1 u hu
  have sw : ∀ u w, V.hD u w = star (V.hD w u) := fun u w => (hs u w).symm
  have hcast : ∀ i j : Fin a, (Fin.castLE ha i = Fin.castLE ha j) ↔ i = j :=
    fun i j => (Fin.castLE_injective ha).eq_iff
  let e' : Fin a → V.V := fun i => Φ.e (Fin.castLE ha i)
  let f' : Fin a → V.V := fun i => Φ.f (Fin.castLE ha i)
  have hli' : LinearIndependent D.host.E (Sum.elim e' f') := by
    refine LinearIndependent.of_pairwise_dual_eq_zero_one _
      (Sum.elim (fun i => V.hT (f' i)) (fun i => V.hT (e' i))) ?_ ?_
    · rintro (i | i) (j | j) hij
      · have : Fin.castLE ha j ≠ Fin.castLE ha i := fun h => hij (congrArg Sum.inl ((hcast j i).1 h).symm)
        exact (Φ.ef _ _).trans (if_neg this)
      · exact Φ.ff _ _
      · exact Φ.ee _ _
      · have : Fin.castLE ha i ≠ Fin.castLE ha j := fun h => hij (congrArg Sum.inr ((hcast i j).1 h))
        show V.hD (f' j) (e' i) = 0
        rw [sw]; show star (V.hD (Φ.e (Fin.castLE ha i)) (Φ.f (Fin.castLE ha j))) = 0
        rw [Φ.ef, if_neg this, star_zero]
    · rintro (i | i)
      · exact (Φ.ef _ _).trans (if_pos rfl)
      · show V.hD (f' i) (e' i) = 1
        rw [sw]; show star (V.hD (Φ.e (Fin.castLE ha i)) (Φ.f (Fin.castLE ha i))) = 1
        rw [Φ.ef, if_pos rfl, star_one]
  have hg : ∀ p q, V.hT (Sum.elim x x' p) (Sum.elim x x' q) = V.hT (Sum.elim e' f' p) (Sum.elim e' f' q) := by
    rintro (i | i) (j | j)
    · show V.hD (x j) (x i) = V.hD (e' j) (e' i)
      rw [h1, Φ.ee]
    · show V.hD (x' j) (x i) = V.hD (f' j) (e' i)
      rw [sw, sw (f' j)]
      show star (V.hD (x i) (x' j)) = star (V.hD (Φ.e (Fin.castLE ha i)) (Φ.f (Fin.castLE ha j)))
      rw [h3, Φ.ef]; simp only [hcast]
    · show V.hD (x j) (x' i) = V.hD (e' j) (f' i)
      show _ = V.hD (Φ.e (Fin.castLE ha j)) (Φ.f (Fin.castLE ha i))
      rw [h3, Φ.ef]; simp only [hcast]
    · show V.hD (x' j) (x' i) = V.hD (f' j) (f' i)
      rw [h2, Φ.ff]
  obtain ⟨g, hgB, hgv⟩ := GlobalTheory.LocOver.WittFrames.exists_isom_of_gram witt_extension_theorem V.hT hs hn _ _ hli hli' hg
  let M : Matrix (Fin V.rank) (Fin V.rank) D.host.E := LinearMap.toMatrix V.frame V.frame g.toLinearMap
  let N : Matrix (Fin V.rank) (Fin V.rank) D.host.E := LinearMap.toMatrix V.frame V.frame g.symm.toLinearMap
  have hMN : M * N = 1 := by
    rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_one V.frame]; congr 1; ext y; simp
  have hNM : N * M = 1 := by
    rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_one V.frame]; congr 1; ext y; simp
  let U : GL (Fin V.rank) D.host.E := ⟨M, N, hMN, hNM⟩
  have hrat : ∀ γ : GF V, γ.1 = U → GlobalTheory.Cusp.ratAct D.sp.cm V γ = g.toLinearMap := fun γ h => by
    show Matrix.toLin V.frame V.frame γ.1.1 = _
    rw [h]; exact Matrix.toLin_toMatrix _ _ _
  refine ⟨⟨U, ?_⟩, fun i => ?_⟩
  · show Formalism.UG.cT _ M * V.gram * M = V.gram
    funext i j
    have hexp : ∀ k, g (V.frame k) = ∑ l, M l k • V.frame l := fun k => by
      conv_lhs => rw [← V.frame.sum_repr (g (V.frame k))]
      simp [M, LinearMap.toMatrix_apply]
    rw [show V.gram i j = V.hT (V.frame i) (V.frame j) from rfl, ← hgB, hexp, hexp]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, map_sum, map_smulₛₗ,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    have hσ : ∀ z, (D.sp.cm.sig : D.host.E →+* D.host.E) z = star z := fun z => rfl
    simp only [hσ, starRingEnd_apply, HSpace.gram, RingHom.id_apply]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  · rw [hrat _ rfl]
    exact ⟨hgv (Sum.inl i), hgv (Sum.inr i)⟩

end GlobalTheory.WittCarry
end

