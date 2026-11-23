module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0491
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicChartLiftHolomorphicPeriodMaps
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option autoImplicit false

theorem GlobalTheory.ShFam.chart_lift_periods_of_openPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∃ (i : Fin Fu.n) (B : Set (ReciprocityTheory.L2DbarEstimates.V X.dim)) (P : ReciprocityTheory.L2DbarEstimates.V X.dim → ((Fu.Di i).La →+ (Fin g → ℂ))), IsOpen B ∧ c'.e y ∈ B ∧ B ⊆ c'.e.target ∧ (∀ b ∈ B, IsPeriod (Fu.Di i) ty (P b)) ∧ (∀ x, DifferentiableOn ℂ (fun b => P b x) B) ∧ ∀ b ∈ B, ∃ q : FrPt Xo c (Formalism.L2.Pj.CAt σ), cxPt T.Z q = cxOf e σ hj (c'.e.symm b) ∧ Fu.u i (P b) = q.x := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ g ty Fu X j hj hjo y hy c' hyc
  have := T.Z.jQ_open
  have : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  let L := EuclideanSpace.equiv (Fin X.dim) ℂ
  have hsy := GlobalTheory.TrueCx.TorHolo.isHolTo_symm c'
  have hsj := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hsy j
  have hB₀ := (hsj T.Z.jQ.opensRange 0).1
  set B₀ := {b ∈ c'.e.target | ⊤ ≤ ((c'.e.symm b).1 ≫ j) ⁻¹ᵁ T.Z.jQ.opensRange} with hB₀def
  have hb₀ : c'.e y ∈ B₀ := by
    refine ⟨c'.e.map_source hyc, ?_⟩
    rw [c'.e.left_inv hyc]
    intro s _
    have h1 : y.1 s ∈ openPart j := hy (Set.mem_univ s)
    exact not_not.1 h1
  have hw : ∀ b ∈ B₀, ∃ w : Sp ℂ ⟶ Xo.XF c, w ≫ T.Z.jQ = (c'.e.symm b).1 ≫ j := fun b hb =>
    ⟨IsOpenImmersion.lift T.Z.jQ _ (by rintro _ ⟨s, rfl⟩; exact hb.2 (Set.mem_univ s)), IsOpenImmersion.lift_fac _ _ _⟩
  have : Nonempty (Sp ℂ ⟶ Xo.XF c) := ⟨(hw _ hb₀).choose⟩
  choose! w hw using hw
  have hwh : IsHolTo B₀ w := GlobalTheory.TrueCx.TorHolo.isHolTo_of_openImmersion T.Z.jQ
    (LocLift.isHolTo_congr (LocLift.isHolTo_mono hsj hB₀ fun b hb => hb.1) hw)
  have hyh := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hwh (Limits.pullback.fst _ _)
  have hsnd : ∀ b ∈ B₀, w b ≫ Limits.pullback.snd _ _ = spMap σ := fun b hb => by
    rw [← T.Z.jQ_over, ← Category.assoc, hw b hb]
    exact (Category.assoc _ _ _).trans (cxOf e σ hj (c'.e.symm b)).2
  have hB₁ : IsOpen (L.symm ⁻¹' B₀) := hB₀.preimage L.symm.continuous
  obtain ⟨B', i, P, hB', hb', hsub, hP, hu⟩ := Fu.lift X.dim (L.symm ⁻¹' B₀) (fun x => w (L.symm x) ≫ Limits.pullback.fst _ _) hB₁
    (fun x hx => by
      rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hsnd _ hx, ← Spec.map_comp]
      rfl)
    (LocLift.isHolTo_comp hyh hB₁ L.symm.differentiableOn fun x hx => hx) (L (c'.e y))
    (by simpa only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hb₀)
  refine ⟨i, L ⁻¹' B', fun v => P (L v), hB'.preimage L.continuous, hb', fun v hv => ?_, fun v hv => hP.1 _ hv,
    fun x => (hP.2 x).comp L.differentiableOn fun v hv => hv, fun b hb => ?_⟩
  · have := hsub hv
    simp only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] at this
    exact this.1
  · have hb1 := hsub hb
    simp only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] at hb1
    have h2 := hu _ hb
    simp only [ContinuousLinearEquiv.symm_apply_apply] at h2
    have ho : (w b ≫ Limits.pullback.fst _ _) ≫ Xo.s = sOf c (CAt σ) := by
      rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hsnd b hb1]
      exact OpenReg.spMap_comp _ _
    obtain ⟨q, hq⟩ : ∃ q : FrPt Xo c (CAt σ), q.x = w b ≫ Limits.pullback.fst _ _ := GlobalTheory.FlagTan.exists_frPt _ ho
    refine ⟨q, Subtype.ext ?_, h2.trans hq.symm⟩
    have h3 : GlobalTheory.AllWt.ptF (S := CAt σ) q = w b :=
      Limits.pullback.hom_ext ((ptF_fst q).trans hq) ((ptF_snd q).trans (hsnd b hb1).symm)
    exact (congrArg (· ≫ T.Z.jQ) h3).trans (hw b hb1)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesSplit
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.HeightCounting.Up

theorem isSplitPl_of_mem_levelPrimes {R : Ranks} (H : Host R)
    (hc : ∀ p ∈ H.levelPrimes, p.Prime ∧ p % (H.QS * H.q * H.d) = 1) {p : ℕ} (hp : p ∈ H.levelPrimes)
    (v : HeightOneSpectrum (𝓞 H.E)) (hv : v ∈ placesOver H.E p) : IsSplitPl H v := by
  obtain ⟨hpr, hm⟩ := hc p hp
  have h := (GlobalTheory.HostSplit.split_of_one_mod R H p hpr hm).1
  obtain ⟨-, he, hf⟩ := GlobalTheory.unramified_degree_one_of_ncard_placesOver H.E p hpr h v hv
  exact GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSplitPl_of_degree_one H v hf he

end GlobalTheory.HeightCounting.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesSplitAll
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.SplitPrimeAuxiliary

open scoped Pointwise

theorem eq_one_of_smul_eq (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] {p : ℕ} (hp : p.Prime)
    (h : ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E)).ncard = Module.finrank ℚ E)
    (P : Ideal (𝓞 E)) [P.IsPrime] (hP : (p : 𝓞 E) ∈ P) (σ : Gal(E/ℚ)) (hσ : σ • P = P) : σ = 1 := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpz.ne_zero).2 hpz).isMaximal (by simpa using hp.ne_zero)
  have hlo : P.LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ P).ne_top ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
    simpa using hP
  have horb := Algebra.IsInvariant.orbit_eq_primesOver ℤ (𝓞 E) Gal(E/ℚ) (Ideal.span {(p : ℤ)}) P
  have hidx := MulAction.index_stabilizer Gal(E/ℚ) P
  rw [horb, h, ← IsGalois.card_aut_eq_finrank] at hidx
  have hmul := (MulAction.stabilizer Gal(E/ℚ) P).card_mul_index
  rw [hidx] at hmul
  have h1 : Nat.card (MulAction.stabilizer Gal(E/ℚ) P) = 1 :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [hmul, one_mul])
  have hb := Subgroup.card_eq_one.1 h1
  have hm : σ ∈ MulAction.stabilizer Gal(E/ℚ) P := hσ
  rwa [hb, Subgroup.mem_bot] at hm

theorem conj_ne_one {R : Ranks} (H : Host R) : H.conj ≠ 1 := by
  have : IsCMField H.E := H.isCMField_hostE
  intro h
  apply IsCMField.complexConj_ne_one H.E
  ext z
  have : IsCMField.complexConj H.E z = H.conj z := by
    apply H.φ₀.injective
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
  rw [this, h]
  rfl

theorem isSplitPl_of_split {R : Ranks} (H : Host R) {p : ℕ} (hp : p.Prime)
    (h : ((Ideal.span {(p : ℤ)}).primesOver (𝓞 H.E)).ncard = Module.finrank ℚ H.E)
    (v : HeightOneSpectrum (𝓞 H.E)) (hv : v ∈ placesOver H.E p) : IsSplitPl H v := by
  have : IsGalois ℚ H.E := H.hostE_isGalois
  have := v.isPrime
  by_contra hs
  apply conj_ne_one H
  rw [← inv_eq_one]
  refine eq_one_of_smul_eq H.E hp h v.asIdeal hv _ (Eq.symm ?_)
  refine v.isMaximal.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_
  intro x hx
  rw [Ideal.mem_inv_pointwise_smul_iff]
  by_contra hx'
  refine hs ⟨x, hx, fun y hy => ?_⟩
  have : y = H.conj • x := RingOfIntegers.ext hy
  rwa [this]

end GlobalTheory.SplitPrimeAuxiliary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedFormCellMultiplicityPos
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem cellMult_pos {O : Type} [CommRing O] [Module.Finite ℤ O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} (δ : Fin m → balForms bar X) : 0 < cellMult bar δ := by
  haveI : Module.Finite ℤ X := Module.Finite.trans O X
  unfold cellMult
  set M := balForms bar X ⧸ Submodule.span ℤ (Set.range δ)
  set T := Submodule.torsion ℤ M
  haveI : IsNoetherian ℤ (LinearMap.BilinForm ℤ X) := inferInstance
  haveI : Module.Finite ℤ M := inferInstance
  haveI : IsNoetherian ℤ M := inferInstance
  haveI : IsNoetherian ℤ T := isNoetherian_of_submodule_of_noetherian ℤ M T inferInstance
  haveI : Module.Finite ℤ T := ⟨IsNoetherian.noetherian ⊤⟩
  haveI : AddGroup.FG T := by
    rw [← Module.Finite.iff_addGroup_fg]; infer_instance
  haveI : Finite T := by
    apply AddCommGroup.finite_of_fg_torsion
    rintro ⟨x, hx⟩
    obtain ⟨⟨a, ha⟩, hax⟩ := hx
    refine (isOfFinAddOrder_iff_zsmul_eq_zero).2 ⟨a, nonZeroDivisors.ne_zero ha, ?_⟩
    ext
    exact hax
  exact Nat.card_pos

end GlobalTheory.PolFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelCharacterEqProdSuperdiagonalSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace GlobalTheory.HeightCounting.ThetaSt

section Gen

variable {D : D7}

theorem baseLevelCharacter_eq_prod_superdiagonalSum {Pg : Finset (Pl D.host.E)} {r : ℕ} (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL)
    (y : (Formalism.L2.DIV.P0 Pg r ψ).H) :
    (((Formalism.L2.DIV.P0 Pg r ψ).chi y : D.what₂.LLˣ) : D.what₂.LL) =
      ∏ PP : ↥Pg, ψ PP.1 (edgeSum supEdge ((y : G0 Pg r) PP)) := by
  change ↥(Subgroup.pi Set.univ fun PP : ↥Pg => unip (kP PP.1) r) at y
  change (((∏ PP : ↥Pg, (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp
    (LevelP.prj (fun PP : ↥Pg => unip (kP PP.1) r) PP)) y : D.what₂.LLˣ) : D.what₂.LL) = _
  letI : IsOneApply (↥(Subgroup.pi Set.univ fun PP : ↥Pg => unip (kP PP.1) r) →* D.what₂.LLˣ) := ⟨fun _ => rfl⟩
  letI : IsMulApply (↥(Subgroup.pi Set.univ fun PP : ↥Pg => unip (kP PP.1) r) →* D.what₂.LLˣ) := ⟨fun _ _ _ => rfl⟩
  rw [prod_apply, Units.coe_prod]
  rfl

theorem supSum_map {κ : Type} [CommRing κ] {n : ℕ} (e : κ →+* ZMod n) {r : ℕ} (g : GL (Fin r) κ) :
    Formalism.L2.NX.supSum r ((Matrix.GeneralLinearGroup.map e g : GL (Fin r) (ZMod n)) : Matrix (Fin r) (Fin r) (ZMod n)) =
      e (edgeSum supEdge g) := by
  unfold Formalism.L2.NX.supSum edgeSum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : (b : ℕ) = a + 1
  · have h' : supEdge a b := h
    rw [if_pos h, if_pos h']
    rfl
  · have h' : ¬ supEdge a b := h
    rw [if_neg h, if_neg h', map_zero]

def thOf (ζ : Fin 2 → ↥D.LL0) (hp : ∀ k, ζ k ^ D.host.g k = 1) (k : Fin 2) :
    Multiplicative (ZMod (D.host.g k)) →* (↥D.LL0)ˣ :=
  ((AddChar.zmodChar (D.host.g k) (hp k)).toMonoidHom.toHomUnits)⁻¹

theorem thOf_val (ζ : Fin 2 → ↥D.LL0) (hp : ∀ k, ζ k ^ D.host.g k = 1) (k : Fin 2) (z : ZMod (D.host.g k)) :
    (((thOf ζ hp k (Multiplicative.ofAdd z) : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) = ((ζ k : D.what₂.LL) ^ z.val)⁻¹ := by
  simp [thOf, MonoidHom.inv_apply, AddChar.toMonoidHom_apply, AddChar.zmodChar_apply]

theorem pow_of_emb (ζ : Fin 2 → ↥D.LL0)
    (hζ : ∀ k, D.what₂.embLL (ζ k : D.what₂.LL) = Complex.exp (2 * Real.pi * Complex.I / (D.host.g k : ℂ))) (k : Fin 2) :
    ζ k ^ D.host.g k = 1 := by
  have hg : (D.host.g k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (D.host.g_prime k).ne_zero
  apply Subtype.ext
  apply D.what₂.embLL.injective
  have e1 : ((ζ k ^ D.host.g k : ↥D.LL0) : D.what₂.LL) = (ζ k : D.what₂.LL) ^ D.host.g k := rfl
  rw [e1, map_pow, hζ, ← Complex.exp_nat_mul]
  have e2 : ((D.host.g k : ℕ) : ℂ) * (2 * Real.pi * Complex.I / (D.host.g k : ℂ)) = 2 * Real.pi * Complex.I := by
    field_simp
  rw [e2, Complex.exp_two_pi_mul_I]
  simp

end Gen

section State

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

theorem roots_g (x : St P) (k : Fin 2) : ∃ ζ : ↥(Dof x).LL0,
    (Dof x).what₂.embLL (ζ : (Dof x).what₂.LL) = Complex.exp (2 * Real.pi * Complex.I / ((Dof x).host.g k : ℂ)) := by
  have hmem : (w.st x.o.Z).B.host.g k * ((w.st x.o.Z).B.host.g k - 1) ∈ [(w.st x.o.Z).B.restRowsFiniteGroupCard,
      (w.st x.o.Z).B.host.g 0 * ((w.st x.o.Z).B.host.g 0 - 1), (w.st x.o.Z).B.host.g 1 * ((w.st x.o.Z).B.host.g 1 - 1), 3 ^ 4,
      5 ^ 4] := by
    fin_cases k <;> simp
  obtain ⟨z, hz, hz'⟩ := (w.st x.o.Z).B.roots_Ks _ hmem
  have hg1 : 1 < (Dof x).host.g k := ((Dof x).host.g_prime k).one_lt
  refine ⟨⟨z ^ ((Dof x).host.g k - 1), (w.st x.o.Z).B.Ks_le (pow_mem hz _)⟩, ?_⟩
  show (w.st x.o.Z).B.embLL (z ^ ((Dof x).host.g k - 1)) = _
  rw [map_pow, hz', ← Complex.exp_nat_mul]
  congr 1
  have hc : (((Dof x).host.g k - 1 : ℕ) : ℂ) = ((Dof x).host.g k : ℂ) - 1 := by
    rw [Nat.cast_sub hg1.le, Nat.cast_one]
  have hg0 : ((Dof x).host.g k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hg1' : ((Dof x).host.g k : ℂ) - 1 ≠ 0 := by
    rw [← hc]; exact Nat.cast_ne_zero.2 (by omega)
  change (((Dof x).host.g k - 1 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / (((Dof x).host.g k * ((Dof x).host.g k - 1) : ℕ) : ℂ)) = _
  rw [Nat.cast_mul, hc]
  field_simp

end State

section Gen

end Gen

end GlobalTheory.HeightCounting.ThetaSt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BilinFormExistsPrimitiveOfNeZero
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory

theorem bilinForm_exists_primitive_of_ne_zero (X : Type) [AddCommGroup X]
    (σ : LinearMap.BilinForm ℤ X) (hσ : σ ≠ 0) :
    ∃ (g : ℕ) (β₀ : LinearMap.BilinForm ℤ X), 0 < g ∧ (g : ℤ) • β₀ = σ ∧
      ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β₀ → k = 1 := by
  classical
  obtain ⟨a, b, hab⟩ : ∃ a b, σ a b ≠ 0 := by
    by_contra h
    apply hσ
    ext a b
    by_contra h'
    exact h ⟨a, b, by simpa using h'⟩
  have hbound : ∀ k : ℕ, (∃ β' : LinearMap.BilinForm ℤ X, (k : ℤ) • β' = σ) →
      k ≤ (σ a b).natAbs := by
    rintro k ⟨β', hβ'⟩
    have h1 : σ a b = (k : ℤ) * β' a b := by
      rw [← hβ']
      simp
    have h2 : k ∣ (σ a b).natAbs := Int.natCast_dvd.mp ⟨β' a b, h1⟩
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr hab) h2
  let P : ℕ → Prop := fun k => ∃ β' : LinearMap.BilinForm ℤ X, (k : ℤ) • β' = σ
  have hP1 : P 1 := ⟨σ, by simp⟩
  have h1le : 1 ≤ (σ a b).natAbs := hbound 1 hP1
  have hg : P (Nat.findGreatest P (σ a b).natAbs) := Nat.findGreatest_spec h1le hP1
  have hg1 : 1 ≤ Nat.findGreatest P (σ a b).natAbs := Nat.le_findGreatest h1le hP1
  have hmax : ∀ k, P k → k ≤ Nat.findGreatest P (σ a b).natAbs :=
    fun k hk => Nat.le_findGreatest (hbound k hk) hk
  generalize Nat.findGreatest P (σ a b).natAbs = g at hg hg1 hmax
  obtain ⟨β₀, hβ₀⟩ := hg
  refine ⟨g, β₀, hg1, hβ₀, ?_⟩
  intro k β' hk
  have hgk : P (g * k) := ⟨β', by rw [Nat.cast_mul, mul_smul, hk, hβ₀]⟩
  have hle := hmax _ hgk
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hσ
    rw [← hβ₀, ← hk]
    simp
  have hk1 : k ≤ 1 := by
    have : g * k ≤ g * 1 := by simpa using hle
    exact Nat.le_of_mul_le_mul_left this hg1
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedDomainModelGramContDiffIsUnit
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.PointChern

open GlobalTheory.HermFrame Matrix
open scoped ComplexOrder

theorem mContDiffAt_coordOf {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {n : ℕ}
    (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (σ : GlobalTheory.AllWt.Psi H) (w : ReciprocityTheory.L2DbarEstimates.V n) :
    MContDiffAt 2 (fun u => coordOf ix u σ) w := fun a b => by
  have : (fun u : ReciprocityTheory.L2DbarEstimates.V n => coordOf ix u σ a b) =
      ((EuclideanSpace.proj (𝕜 := ℂ) (ix.symm (σ, a, b))).restrictScalars ℝ) := by
    funext u; rfl
  rw [this]
  exact ContinuousLinearMap.contDiff _ |>.contDiffAt

theorem one_sub_map_conj_mul_transpose {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) :
    (1 - z.map (starRingEnd ℂ) * zᵀ) = (1 - z * zᴴ)ᵀ := by
  ext a b
  simp [Matrix.mul_apply, Matrix.one_apply, Matrix.sub_apply, eq_comm, mul_comm]

theorem isUnit_det_one_sub_map_conj {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) (h : (1 - zᴴ * z).PosDef) :
    IsUnit (1 - z.map (starRingEnd ℂ) * zᵀ).det := by
  rw [one_sub_map_conj_mul_transpose, det_transpose, det_one_sub_mul_comm]
  exact (h.det_pos.ne').isUnit

theorem isUnit_det_one_sub_conjTranspose {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) (h : (1 - zᴴ * z).PosDef) :
    IsUnit (1 - zᴴ * z).det :=
  (h.det_pos.ne').isUnit

theorem MContDiffAt.map_conj {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {m n : Type*} {k : WithTop ℕ∞}
    {A : V → Matrix m n ℂ} {z : V} (h : MContDiffAt k A z) :
    MContDiffAt k (fun x => (A x).map (starRingEnd ℂ)) z :=
  fun a b => Complex.conjCLE.contDiff.contDiffAt.comp z (h a b)

end GlobalTheory.PointChern

namespace GlobalTheory.PointChern
open GlobalTheory.HermFrame Matrix
open scoped ComplexOrder

theorem modelGram_smooth_isUnit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (w : ReciprocityTheory.L2DbarEstimates.V n), InDom (coordOf ix w) → ∀ τ, MContDiffAt 2 (fun u => modelGram H Dw (coordOf ix u) τ) w ∧ IsUnit (modelGram H Dw (coordOf ix w) τ).det := by
  intro E _ _ _ H Dw n ix w hw τ
  by_cases h : τ (H.rt : E) = H.rt0
  · have hZ := mContDiffAt_coordOf ix ⟨τ, h⟩ w
    have hA : MContDiffAt 2 (fun u => 1 - (coordOf ix u ⟨τ, h⟩).map (starRingEnd ℂ) * (coordOf ix u ⟨τ, h⟩)ᵀ) w :=
      (mContDiffAt_const 1).sub ((GlobalTheory.PointChern.MContDiffAt.map_conj hZ).mul hZ.transpose)
    have hu := isUnit_det_one_sub_map_conj _ (hw ⟨τ, h⟩)
    simp only [modelGram, dif_pos h]
    refine ⟨?_, ?_⟩
    · simp only [reindex_apply]
      exact (hA.inv hu).submatrix _ _
    · rw [det_reindex_self]
      exact isUnit_nonsing_inv_det_iff.mpr hu
  · by_cases h' : conjEmb τ (H.rt : E) = H.rt0
    · have hZ := mContDiffAt_coordOf ix ⟨conjEmb τ, h'⟩ w
      have hA : MContDiffAt 2 (fun u => 1 - (coordOf ix u ⟨conjEmb τ, h'⟩)ᴴ * coordOf ix u ⟨conjEmb τ, h'⟩) w :=
        (mContDiffAt_const 1).sub (hZ.conjTranspose.mul hZ)
      have hu := isUnit_det_one_sub_conjTranspose _ (hw ⟨conjEmb τ, h'⟩)
      simp only [modelGram, dif_neg h, dif_pos h']
      refine ⟨?_, ?_⟩
      · simp only [reindex_apply]
        exact (hA.inv hu).submatrix _ _
      · rw [det_reindex_self]
        exact isUnit_nonsing_inv_det_iff.mpr hu
    · simp only [modelGram, dif_neg h, dif_neg h']
      exact ⟨mContDiffAt_const 1, by simp⟩

end GlobalTheory.PointChern
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriesExistsMarkedFormInCone
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem carries_exists_marked : ∀ {O : Type} [CommRing O] (bar : O → O) (w0 : O) (c : FormFamily O) {X₀ : Type} [AddCommGroup X₀] [Module O X₀] [Module.Finite O X₀] {m : ℕ} (δ₀ : Fin m → LinearMap.BilinForm ℤ X₀) (v : LinearMap.BilinForm ℤ X₀) (t : Fin m → ℝ),
  v ∈ balForms bar X₀ → v ≠ 0 → (∀ y, 0 ≤ v y y) → c.Carries δ₀ → (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ X), c.Carries δ →
    ∃ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) ∧ (OrbMark.orbFun O w0 v).evalZ β = 1 ∧ InRCone δ β := by
  intro O _ bar w0 c X₀ _ _ _ m δ₀ v t hbal hv hpos hc₀ ht hsum X _ _ _ m' δ hc
  obtain ⟨e₀, s₀, hδ₀⟩ := hc₀
  obtain ⟨e, s, hδ⟩ := hc
  set g : X ≃ₗ[O] X₀ := e.trans e₀.symm with hg
  refine ⟨pull g.toLinearMap v, pull_mem _ hbal, fun y => by simpa using hpos (g y), ?_, ?_⟩
  · rw [evalZ_pull _ g.surjective]
    exact OrbMark.orbFun_evalZ_self w0 hv hbal.1
  · refine ⟨fun j => t (s₀.symm (s j)), fun j => ht _, LinearMap.ext₂ fun a b => ?_⟩
    have h1 := LinearMap.congr_fun₂ hsum (g a) (g b)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul] at h1 ⊢
    show ((v (g a) (g b) : ℤ) : ℝ) = _
    rw [h1]
    have key : ∀ i, (δ₀ i (g a) (g b) : ℝ) = (c.δ (s₀ i) (e a) (e b) : ℝ) := fun i => by
      rw [hδ₀ i, pull_apply]; simp [hg]
    have key' : ∀ j, (δ j a b : ℝ) = (c.δ (s j) (e a) (e b) : ℝ) := fun j => by
      rw [hδ j, pull_apply]; rfl
    simp only [key, key']
    rw [← (s.trans s₀.symm).sum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp

end GlobalTheory.PolFan
end
end

