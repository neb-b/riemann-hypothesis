module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModelKSN
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0024
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0040
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0020

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModelKSD
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.FourierDecayAlt Formalism.L2.SG.DataInst
open Classical ValuativeRel
open scoped nonZeroDivisors

namespace Formalism.L2.SG.Pf.LMK

variable {D : Formalism.BasicNotions.D7}

theorem modK_alg (Z : Formalism.L2.SG.TermLoc.LocDat D) (p : PlF D) [IsNonarchimedeanLocalField (D.s.atP p).Fp]
    {z : (D.s.atP p).Fp} (hz : z ≠ 0) :
    A5.modK (Z.M p).R (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep z) = PI.ProdFormulaE.modF (D.s.atP p).Fp z ^ 2 := by
  have := (D.s.atP p).borel
  have := (D.s.atP p).free
  have : Module.Finite (D.s.atP p).Fp (D.s.atP p).Ep :=
    Module.finite_of_finrank_pos (by rw [(D.s.atP p).rank]; norm_num)
  have := (D.s.atP p).top
  have hOK := (Z.agree p).1
  have := hOK.haar.haar
  have hu : IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep z) := (isUnit_iff_ne_zero.2 hz).map _
  have h1 := Formalism.MainNotions.LocalModelPeriodLattices.modK_of_OK (Z.M p) hOK hu.unit
  rw [IsUnit.unit_spec] at h1
  rw [← h1]
  unfold Loc.Model.modK
  rw [PI.ProdFormulaE.HaarAlgP.haarScaling (D.s.atP p).Fp (D.s.atP p).Ep (Z.M p).mu _ hu _, hOK.haar.volR, mul_one,
    Algebra.norm_algebraMap, (D.s.atP p).rank, ENNReal.toReal_ofReal (PI.ProdFormulaE.HaarBox.modF_nonneg' _), pow_two,
    PI.ProdFormulaE.modF_mul]
  ring

theorem delta_unit (Z : Formalism.L2.SG.TermLoc.LocDat D) (p : PlF D) (x0 : 𝓞 D.host.F)
    (hx0 : x0 ∈ differentIdeal ℤ (𝓞 D.host.F))
    (hv : p.intValuation x0 = WithZero.exp (-(Formalism.L2.SG.Pf.NcVal.mDiff D.host.F p : ℤ))) :
    (D.s.atP p).ιF (x0 : D.host.F) ≠ 0 ∧
      Z.δ p * ((D.s.atP p).ιF (x0 : D.host.F))⁻¹ ∈ 𝒪[(D.s.atP p).Fp] ∧
      (Z.δ p * ((D.s.atP p).ιF (x0 : D.host.F))⁻¹)⁻¹ ∈ 𝒪[(D.s.atP p).Fp] := by
  set A := D.s.atP p with hAdef
  have hδ : Z.δ p ≠ 0 := (Z.agree p).2.1
  have hx0ne : x0 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hι0 : A.ιF (x0 : D.host.F) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ A.ιF.injective]
    exact_mod_cast hx0ne
  have hvx0 : p.valuation D.host.F (x0 : D.host.F) = WithZero.exp (-(Formalism.L2.SG.Pf.NcVal.mDiff D.host.F p : ℤ)) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]; exact hv

  set J : FractionalIdeal (𝓞 D.host.F)⁰ D.host.F := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 D.host.F)⁰ D.host.F)
    with hJ
  have hJ0 : J ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  have hdd : ((differentIdeal ℤ (𝓞 D.host.F) : Ideal (𝓞 D.host.F)) : FractionalIdeal (𝓞 D.host.F)⁰ D.host.F) = J⁻¹ :=
    coeIdeal_differentIdeal ℤ ℚ D.host.F (𝓞 D.host.F)
  have hmemJ : ∀ y : D.host.F, y ∈ J ↔ ∀ a : 𝓞 D.host.F, ∃ n : ℤ, Algebra.trace ℚ D.host.F (y * a) = n := by
    intro y
    rw [hJ, FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 D.host.F)⁰ D.host.F) ≠ 0)]
    constructor
    · intro h a
      obtain ⟨n, hn⟩ := h (algebraMap _ _ a) ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
      exact ⟨n, by rw [Algebra.traceForm_apply] at hn; rw [← hn]; rfl⟩
    · intro h b hb
      obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hb
      obtain ⟨n, hn⟩ := h a
      exact ⟨n, by rw [Algebra.traceForm_apply, hn]; rfl⟩
  have hx0J : (x0 : D.host.F) ∈ J⁻¹ := by
    rw [← hdd]; exact (FractionalIdeal.mem_coeIdeal _).2 ⟨x0, hx0, rfl⟩
  have hmulO : ∀ y ∈ J, ∀ b ∈ J⁻¹, p.valuation D.host.F (y * b) ≤ 1 := by
    intro y hy b hb
    have h1 : y * b ∈ J * J⁻¹ := FractionalIdeal.mul_mem_mul hy hb
    rw [mul_inv_cancel₀ hJ0] at h1
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [← ho]
    exact p.valuation_le_one o

  obtain ⟨t, htr, hne, hu1, hu2⟩ := PI.CntNotIntW.locDiff_of PI.CntNotIntW.trace_dual_lattice
    (PI.CntNotIntW.dualApprox_of PI.CntNotIntW.small_powers_bound PI.CntNotIntW.tensorLiftSurjective)
    PI.CntNotIntW.small_powers_bound D Z.δ Z.M Z.agree p
  have htJ : t ∈ J := (hmemJ t).2 htr
  have ht0 : A.ιF t ≠ 0 := right_ne_zero_of_mul hne
  have htx0 : A.ιF (t * (x0 : D.host.F)) ∈ 𝒪[A.Fp] := by
    rw [Formalism.MainNotions.BridgeLemma.mem_OF_iff]
    exact hmulO t htJ _ hx0J

  obtain ⟨y, hy, a, ha, hya⟩ : ∃ y ∈ J, ∃ b ∈ J⁻¹, ¬ valuation A.Fp (A.ιF (y * b)) < 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : (1 : D.host.F) ∈ J * J⁻¹ := by
      rw [mul_inv_cancel₀ hJ0]; exact FractionalIdeal.one_mem_one _
    have h2 : valuation A.Fp (A.ιF 1) < 1 := by
      refine FractionalIdeal.mul_induction_on h1 (fun y hy b hb => hcon y hy b hb) ?_
      intro u v hu hv
      rw [map_add (f := _)]
      exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hu hv)
    rw [map_one, map_one] at h2
    exact lt_irrefl _ h2

  have hyδ : A.ιF y * Z.δ p ∈ 𝒪[A.Fp] := by
    have := A.lf
    have := A.ellPrime
    have hz := Formalism.L2.SG.Pf.dualLoc_holds D.host.F p A.Fp A.qlCont A.qlFin A.ιF A.dense A.val y ((hmemJ y).1 hy)
    exact Formalism.L2.SG.Pf.LocFacts.lf_dual_le p Z _ hz

  have ha0 : valuation A.Fp (A.ιF a) ≤ valuation A.Fp (A.ιF (x0 : D.host.F)) := by
    rw [Formalism.MainNotions.BridgeLemma.val_iff, hvx0]
    rw [← hdd] at ha
    obtain ⟨a', ha', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact Formalism.L2.SG.Pf.NcVal.intValuation_le_of_mem_different p ha'
  have hyx0 : 1 ≤ valuation A.Fp (A.ιF (y * (x0 : D.host.F))) := by
    have h1 : 1 ≤ valuation A.Fp (A.ιF (y * a)) := not_lt.1 hya
    rw [map_mul, map_mul] at h1 ⊢
    exact le_trans h1 (mul_le_mul' le_rfl ha0)
  have hyx0ne : A.ιF (y * (x0 : D.host.F)) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hyx0; exact absurd hyx0 (not_le.2 zero_lt_one)
  refine ⟨hι0, ?_, ?_⟩
  · have e : Z.δ p * (A.ιF (x0 : D.host.F))⁻¹ = (A.ιF y * Z.δ p) * (A.ιF (y * (x0 : D.host.F)))⁻¹ := by
      rw [map_mul]
      have hy0 : A.ιF y ≠ 0 := by intro h0; rw [map_mul, h0, zero_mul] at hyx0ne; exact hyx0ne rfl
      field_simp
    rw [e]
    refine mul_mem hyδ ?_
    rw [Valuation.mem_integer_iff, map_inv₀]
    exact inv_le_one_of_one_le₀ hyx0
  · have e : (Z.δ p * (A.ιF (x0 : D.host.F))⁻¹)⁻¹ = A.ιF (t * (x0 : D.host.F)) * (Z.δ p * A.ιF t)⁻¹ := by
      rw [map_mul]
      field_simp
    rw [e]
    exact mul_mem htx0 hu2

theorem modK_delta (Z : Formalism.L2.SG.TermLoc.LocDat D) (p : PlF D) :
    A5.modK (Z.M p).R (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)) =
      (((Ideal.absNorm (p.maxPowDividing (differentIdeal ℤ (𝓞 D.host.F))) : ℕ) : ℝ)⁻¹) ^ 2 := by
  have := (D.s.atP p).lf
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (Z.M p) (Z.agree p).1
  have hd := Formalism.MainNotions.LocalModelPeriodLattices.datum_of_OK (Z.M p) (Z.agree p).1
  obtain ⟨x0, hx0, hv⟩ := Formalism.L2.SG.Pf.NcVal.exists_mem_different_intValuation_eq (F := D.host.F) p
  obtain ⟨hι0, hu1, hu2⟩ := delta_unit Z p x0 hx0 hv
  set u := Z.δ p * ((D.s.atP p).ιF (x0 : D.host.F))⁻¹ with hudef
  have hu0 : u ≠ 0 := mul_ne_zero (Z.agree p).2.1 (inv_ne_zero hι0)
  have hmu : A5.modK (Z.M p).R (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep u) = 1 :=
    Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.modK_unitR (alg_mem_R (M := Z.M) p hu1) (alg_mem_R (M := Z.M) p hu2)
      (by rw [← map_mul, mul_inv_cancel₀ hu0, map_one])
  have e : Z.δ p = u * (D.s.atP p).ιF (x0 : D.host.F) := by rw [hudef, mul_assoc, inv_mul_cancel₀ hι0, mul_one]
  have hx0ne : x0 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  rw [e, map_mul, Formalism.FourierDecayAlt.P.A5x5.modK_mul' hd ((isUnit_iff_ne_zero.2 hu0).map _) ((isUnit_iff_ne_zero.2 hι0).map _),
    hmu, one_mul, modK_alg Z p hι0, PI.ProdFormulaE.modF_localization_eq_adicAbv]

  have h3 := NumberField.HeightOneSpectrum.embedding_mul_absNorm D.host.F p hx0ne
  rw [NumberField.FinitePlace.norm_embedding] at h3
  have hcount : (Associates.mk p.asIdeal).count (Associates.mk (Ideal.span {x0})).factors =
      Formalism.L2.SG.Pf.NcVal.mDiff D.host.F p := by
    rw [HeightOneSpectrum.intValuation_if_neg p hx0ne] at hv
    have := WithZero.exp_injective hv
    omega
  have hmp : p.maxPowDividing (Ideal.span {x0}) = p.maxPowDividing (differentIdeal ℤ (𝓞 D.host.F)) := by
    unfold HeightOneSpectrum.maxPowDividing
    rw [hcount]
  rw [hmp] at h3
  have hN : ((Ideal.absNorm (p.maxPowDividing (differentIdeal ℤ (𝓞 D.host.F))) : ℕ) : ℝ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h3; exact zero_ne_one h3
  have h4 : (NumberField.HeightOneSpectrum.adicAbv D.host.F p) (x0 : D.host.F) =
      ((Ideal.absNorm (p.maxPowDividing (differentIdeal ℤ (𝓞 D.host.F))) : ℕ) : ℝ)⁻¹ :=
    eq_inv_of_mul_eq_one_left h3
  rw [show ((x0 : D.host.F)) = algebraMap (𝓞 D.host.F) D.host.F x0 from rfl] at h4 ⊢
  rw [h4]

theorem prod_maxPow (I : Ideal (𝓞 D.host.F)) (hI : I ≠ 0) :
    (Function.mulSupport fun p : PlF D =>
      (((Ideal.absNorm (p.maxPowDividing I) : ℕ) : ℝ)⁻¹) ^ 2).Finite ∧
    ∏ᶠ p : PlF D, (((Ideal.absNorm (p.maxPowDividing I) : ℕ) : ℝ)⁻¹) ^ 2 = (((Ideal.absNorm I : ℕ) : ℝ)⁻¹) ^ 2 := by
  let φ : Ideal (𝓞 D.host.F) →* ℝ := (powMonoidHom 2).comp (invMonoidHom.comp
    ((Nat.castRingHom ℝ).toMonoidHom.comp (Ideal.absNorm : Ideal (𝓞 D.host.F) →*₀ ℕ).toMonoidHom))
  have hφ : ∀ J, φ J = (((Ideal.absNorm J : ℕ) : ℝ)⁻¹) ^ 2 := fun J => rfl
  have hfin := Ideal.hasFiniteMulSupport hI
  have hsub : (Function.mulSupport fun p : PlF D => φ (p.maxPowDividing I)) ⊆
      Function.mulSupport fun p : PlF D => p.maxPowDividing I :=
    Function.mulSupport_comp_subset (map_one φ) _
  refine ⟨?_, ?_⟩
  · simpa only [hφ] using hfin.subset hsub
  · have h1 := (MonoidHom.map_finprod φ hfin).symm
    simp only [hφ] at h1
    rw [h1, Ideal.finprod_heightOneSpectrum_factorization hI]

theorem deltaProd_holds (D : Formalism.BasicNotions.D7) : DeltaProd D := by
  intro δ M hA
  let Z : Formalism.L2.SG.TermLoc.LocDat D := ⟨δ, M, hA⟩
  have hI : differentIdeal ℤ (𝓞 D.host.F) ≠ 0 := differentIdeal_ne_bot
  have hfun : (fun p => A5.modK (M p).R (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p))) =
      fun p : PlF D => (((Ideal.absNorm (p.maxPowDividing (differentIdeal ℤ (𝓞 D.host.F))) : ℕ) : ℝ)⁻¹) ^ 2 :=
    funext fun p => modK_delta Z p
  obtain ⟨hfin, hval⟩ := prod_maxPow (D := D) _ hI
  rw [hfun]
  refine ⟨hfin, ?_⟩
  rw [hval, absNorm_differentIdeal D.host.F (𝓞 D.host.F)]
  have hf : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    have := Formalism.MainNotions.LocalModelPeriodLattices.cmE D
    rw [(Formalism.FourierDecayAlt.P.degreeFacts_statement D.host.E).1, Formalism.MainNotions.LocalModelPeriodLattices.deg_eq]
  have hrd : D.host.rdE ^ (2 * D.R.f) = |(NumberField.discr D.host.E : ℝ)| := by
    unfold Formalism.BasicNotions.Host.rdE
    rw [← hf, one_div]
    exact Real.rpow_inv_natCast_pow (abs_nonneg _) Module.finrank_pos.ne'
  rw [hrd, Formalism.L2.SG.NGCut.LeadingMinorIntegrality.discr_sq, Nat.cast_natAbs, Int.cast_abs]
  push_cast
  rw [abs_pow, inv_pow]

end Formalism.L2.SG.Pf.LMK

namespace Formalism.L2.SG.Pf

theorem localModelS_holds (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.DataCut.LocalModelS D := localModelS_of_delta (LMK.deltaProd_holds D)

theorem localModelAt_holds (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.DataInst.LocalModelAt D :=
  Formalism.L2.SG.DataCut.localModelAt_of_KS (localModelK_holds D) (localModelS_holds D)

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqSteps
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.Pf.MainEqCut

set_option linter.dupNamespace false

namespace Formalism.L2.SG.Pf.MainEqSteps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abs

variable {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]

def ScalEquivOn (X : PB.Terms τ Rw I H H₁) : Prop :=
  (∀ t ∈ X.genSet, X.s0 t t = 1 ∧ X.scal t t) ∧
  (∀ t ∈ X.genSet, ∀ t' ∈ X.genSet, X.rowOf t = X.rowOf t' → X.s0 t t' = 1 → X.scal t t' →
    X.s0 t' t = 1 ∧ X.scal t' t) ∧
  (∀ t ∈ X.genSet, ∀ t' ∈ X.genSet, ∀ t'' ∈ X.genSet, X.rowOf t = X.rowOf t' → X.rowOf t' = X.rowOf t'' →
    X.s0 t t' = 1 → X.scal t t' → X.s0 t' t'' = 1 → X.scal t' t'' → X.s0 t t'' = 1 ∧ X.scal t t'')

end Abs

section Conc

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)

theorem classInputG_of (h : ScalEquivOn (Y.tO u u)) (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf)
    (ng : PN.Pts D.host.E D.R.rS → ℝ) : PN.ClassInput (genT (Y.tO u u)) (NOfG Y u νL νB ng) := by
  obtain ⟨hrefl, hsymm, htrans⟩ := h
  have hset : ∀ t, t ∈ (genT (Y.tO u u)).ngSet ↔ t ∈ (Y.tO u u).genSet := fun t => by
    simp [PB.Terms.ngSet, PB.Terms.genSet, genT]
  have hs0 : ∀ t t', (genT (Y.tO u u)).s0 t t' = 1 ↔
      (Y.tO u u).s0 t t' = 1 ∧ (Y.tO u u).scal t t' := fun t t' => by
    simp only [genT]
    split_ifs with hc <;> simp [hc]
  intro t ht t' ht'
  rw [hset] at ht ht'
  change ((Y.tO u u).rowOf t = (Y.tO u u).rowOf t' ∧ (genT (Y.tO u u)).s0 t t' = 1) ↔
    clsG Y u t = clsG Y u t'
  rw [hs0]
  constructor
  · rintro ⟨hrow, hs, hsc⟩
    obtain ⟨hs', hsc'⟩ := hsymm t ht t' ht' hrow hs hsc
    ext t''
    simp only [clsG, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hg, hr, h1, h2⟩
      exact ⟨hg, hr.trans hrow, htrans t' ht' t ht t'' hg hrow.symm hr.symm hs' hsc' h1 h2⟩
    · rintro ⟨hg, hr, h1, h2⟩
      exact ⟨hg, hr.trans hrow.symm, htrans t ht t' ht' t'' hg hrow hr.symm hs hsc h1 h2⟩
  · intro hcl
    have hmem : t' ∈ clsG Y u t' := ⟨ht', rfl, (hrefl t' ht').1, (hrefl t' ht').2⟩
    rw [← hcl] at hmem
    simp only [clsG, Set.mem_setOf_eq] at hmem
    obtain ⟨-, hr, h1, h2⟩ := hmem
    exact ⟨hr.symm, h1, h2⟩

def AmpVanishG (νL : X.B.I.Ginf → Measure X.B.I.Ginf) : Prop :=
  ∀ c γ ν, J2of Y u u νL γ = 0 → grpGC Y u c γ ν = 0

theorem ampInputG_of_vanish (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ)
    (h : AmpVanishG Y u νL) : PN.AmpInput (genT (Y.tO u u)) (NOfG Y u νL νB ng) := by
  have hJ : ∀ γ, 0 ≤ J2of Y u u νL γ := fun γ => by
    unfold J2of
    split_ifs <;> positivity
  refine ⟨fun c γ ν => div_nonneg (sq_nonneg _) (hJ γ), fun γ => hJ γ, fun c γ ν => ?_⟩
  have hset : (genT (Y.tO u u)).ngSet = (Y.tO u u).genSet := by
    ext t
    simp [PB.Terms.ngSet, PB.Terms.genSet, genT]
  have hg : PN.grp (genT (Y.tO u u)) (NOfG Y u νL νB ng) c γ ν = grpGC Y u c γ ν := by
    unfold PN.grp grpGC
    rw [hset]
    rfl
  rw [hg]
  change ‖grpGC Y u c γ ν‖ ^ 2 ≤ a2GC Y u νL c γ ν * J2of Y u u νL γ
  unfold a2GC
  rcases (hJ γ).eq_or_lt with h0 | hpos
  · rw [h c γ ν h0.symm, norm_zero]
    simp
  · rw [div_mul_cancel₀ _ hpos.ne']

end Conc

def StepClassG : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), (∀ i, 3 ≤ D.host.g i) → ConcTie X Y →
    ScalEquivOn (Y.tO u u)

def StepNormalsG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.L2.SG.NGCut.Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ),
        PN.NormalsInput (genT (Y.tO u u)) (NOfG Y u νL νB ng)
          ((2 * D.host.v) ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
            (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) ^ (6 * D.R.f))

def StepPointsG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.L2.SG.NGCut.Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ),
        PN.PointsInput (genT (Y.tO u u)) (NOfG Y u νL νB ng)

def StepHeightG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.L2.SG.NGCut.Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ),
        PN.HeightInput (genT (Y.tO u u)) (NOfG Y u νL νB ng) ((X.B.g : ℝ) ^ D.R.f)

def StepNormOneG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.L2.SG.NGCut.Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ) (γ : PN.Pts D.host.E D.R.rS),
        PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ →
        1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ∧ 1 ≤ NDPt D.host.rdE γ

theorem stepHeightG_of_normOne (h : StepNormOneG) : StepHeightG := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C'₀, Cl₀, hC⟩ := h Cg cb Cw cT CT C0
  refine ⟨C'₀, Cl₀, fun C' Cl h1 h2 D large₂ X Y u hc νL νB ng γ hγ => ?_⟩
  obtain ⟨hG, hD⟩ := hC C' Cl h1 h2 D large₂ X Y u hc νL νB ng γ hγ
  refine ⟨hG, hD, ?_⟩
  have key : ((X.B.g : ℝ) ^ ((2 * D.R.rS + 1) * Fintype.card (InfinitePlace D.host.E)))⁻¹ ≤
      (X.B.g : ℝ) ^ D.R.f := by
    rcases Nat.eq_zero_or_pos X.B.g with h0 | hpos
    · have hN : 0 < (2 * D.R.rS + 1) * Fintype.card (InfinitePlace D.host.E) :=
        Nat.mul_pos (by omega) Fintype.card_pos
      rw [h0, Nat.cast_zero, zero_pow hN.ne', inv_zero]
      positivity
    · have hg : (1 : ℝ) ≤ X.B.g := by exact_mod_cast hpos
      exact (inv_le_one_of_one_le₀ (one_le_pow₀ hg)).trans (one_le_pow₀ hg)
  change HPt D.host.rdE (X.B.g : ℝ) ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ≤
    (X.B.g : ℝ) ^ D.R.f * NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u : ℕ)) γ * NDPt D.host.rdE γ
  unfold HPt
  have hGD : 0 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u : ℕ)) γ * NDPt D.host.rdE γ := by
    have := mul_le_mul hG hD zero_le_one (zero_le_one.trans hG)
    linarith
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_right key hGD

theorem g_ge_three {Cg cb Cw cT CT C0 C' Cl : ℝ} {D : D7} {large₂ : SizeData₂ D} {X : HidaSetting D} {Y : Full X}
    {u u' : D.what₂.Word} (hc : Formalism.L2.SG.NGCut.Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u') :
    ∀ i, 3 ≤ D.host.g i := by
  obtain ⟨⟨hH, _, _⟩, _, _⟩ := hc
  unfold Formalism.MainNotions.S.StandingHypotheses at hH
  dsimp only at hH
  obtain ⟨-, -, h3, h4, -, -, -, -, -, -, h11, h12, h13, h14, h15, h16, -, -, h19, -, -, -, h23, -, h25⟩ := hH
  have hm2 := D.R.two_le_m
  have hk16 : (16 : ℝ) ≤ D.R.k := by
    have : 2 ^ 4 ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm2 4
    have : 16 ≤ D.R.k := by omega
    exact_mod_cast this
  have hL : 0 < large₂.sc.L := by
    unfold Formalism.BasicNotions.Scale.L
    exact Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _
  have hb : 1 < large₂.sc.b := by
    unfold Formalism.BasicNotions.Scale.b
    have := Real.add_one_lt_exp (ne_of_gt hL); linarith
  have hkb : (3 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := by
    have : (16 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := by nlinarith
    exact le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) this 8)
  intro i
  fin_cases i
  · exact_mod_cast hkb.trans h12
  · exact_mod_cast hkb.trans h14

end Formalism.L2.SG.Pf.MainEqSteps

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.MainEqSteps

end Formalism.L2.SG.Pf
end
end

