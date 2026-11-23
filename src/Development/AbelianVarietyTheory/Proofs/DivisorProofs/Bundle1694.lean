module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CoverFourierCoeffEqFiniteFourierSum
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HalvesFreeAndAdjoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDataLevelForms
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1673
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledDarbouxCoordsCompat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1379
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0439
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHalfOfSmul
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.CoverTransform

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem qRep_sub_mem {K : Submodule (𝓞 E) Dw.La} (a : Dw.La) :
    qRep (Submodule.Quotient.mk a : Dw.La ⧸ K) - a ∈ K :=
  (Submodule.Quotient.eq _).1 (GlobalTheory.HalfPairing.qRep_mk _)

theorem pd_mem_half (d : DeltaDat Xo c n) (h : d.IsLev) :
    (d.pd : 𝓞 E) ∈ d.I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  have h1 : (d.pd : 𝓞 E) ∈ d.I * d.I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [GlobalTheory.LevelCoverDatum.half_mul_conj d h]; exact Ideal.mem_span_singleton_self _
  exact Ideal.mul_le_right h1

theorem mfr_cover (d : DeltaDat Xo c n) (h : d.IsLev) :
    Mfr d.l₂ = Mfr l * d.I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  unfold Mfr; rw [h.2.2.2.1, Ideal.map_mul]

theorem finite_laJ (d : DeltaDat Xo c n) (h : d.IsLev) : Finite (LaJ Xo c d) := by
  have hp := GlobalTheory.LevelCoverDatum.pd_pos d h
  have hb : d.I.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ ⊥ := by
    intro e
    have := pd_mem_half d h
    rw [e, Ideal.mem_bot] at this
    exact hp.ne' (by exact_mod_cast this)
  have := (d.I.map (H.bar : 𝓞 E →+* 𝓞 E)).finiteQuotientOfFreeOfNeBot hb
  have := Dw.fin
  exact Submodule.finite_quotient_smul _ (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem exists_bezout (d : DeltaDat Xo c n) (h : d.IsLev) :
    ∃ α β : 𝓞 E, α * d.pd + β * l.M = 1 := Nat.Coprime.cast (R := 𝓞 E) h.2.2.1

theorem mem_half_of_smul (d : DeltaDat Xo c n) (h : d.IsLev) {u : Dw.La}
    (hu : l.M • u ∈ (Mfr d.l₂ • ⊤ : Submodule (𝓞 E) Dw.La)) :
    u ∈ (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La) := by
  obtain ⟨α, β, e⟩ := exists_bezout d h
  have h1 : l.M • u ∈ (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La) :=
    Submodule.smul_mono_left (by rw [mfr_cover d h]; exact Ideal.mul_le_right) hu
  have h2 : u = (α * d.pd) • u + β • l.M • u := by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), smul_smul, ← add_smul, e, one_smul]
  rw [h2]
  exact add_mem (Submodule.smul_mem_smul (Ideal.mul_mem_left _ _ (pd_mem_half d h)) trivial) (Submodule.smul_mem _ _ h1)

theorem exists_class (d : DeltaDat Xo c n) (h : d.IsLev) {x u : Dw.La}
    (hu : u - d.pd • x ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)) :
    ∃ z : LaJ Xo c d, (Submodule.Quotient.mk (d.pd • x + l.M • qRep z) : LevQc Dw d.l₂) = Submodule.Quotient.mk u := by
  obtain ⟨α, β, e⟩ := exists_bezout d h
  refine ⟨Submodule.Quotient.mk (β • (u - d.pd • x)), (Submodule.Quotient.eq _).2 ?_⟩
  have h1 := qRep_sub_mem (K := (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La)) (β • (u - d.pd • x))
  generalize qRep (Submodule.Quotient.mk (β • (u - d.pd • x)) : LaJ Xo c d) = r at h1 ⊢
  have h2 : d.pd • x + l.M • r - u =
      (l.M : 𝓞 E) • (r - β • (u - d.pd • x)) - (α * d.pd) • (u - d.pd • x) := by
    have e' : α * (d.pd : 𝓞 E) = 1 - l.M * β := by linear_combination e
    rw [e', ← Nat.cast_smul_eq_nsmul (𝓞 E) l.M]
    generalize d.pd • x = v
    module
  rw [h2, mfr_cover d h]
  refine sub_mem ?_ ?_
  · rw [Submodule.mul_smul]
    exact Submodule.smul_mem_smul (GlobalTheory.Dict.CoverFourier.natCast_mem l).2 h1
  · rw [mul_comm (Mfr l), Submodule.mul_smul]
    exact Submodule.smul_mem_smul (Ideal.mul_mem_left _ _ (pd_mem_half d h)) hu

theorem dvd_pairing (d : DeltaDat Xo c n) (h : d.IsLev) (x z y : Dw.La) :
    (d.l₂.M : ℤ) ∣ Dw.EF (qRep (Submodule.Quotient.mk (d.pd • x + l.M • z) : LevQc Dw d.l₂)) (cSep d.l₂ • y) -
      (d.pd * Dw.EF x (cSep l • y) + l.M * Dw.EF z (cHalf H d.I • y)) := by
  have h1 := GlobalTheory.LevelPairing.dvd_left (l := d.l₂) y
    (qRep_sub_mem (K := (Mfr d.l₂ • ⊤ : Submodule (𝓞 E) Dw.La)) (d.pd • x + l.M • z))
  obtain ⟨a1, a2⟩ := GlobalTheory.LevelPairing.cSep_spec d.l₂
  obtain ⟨b1, b2⟩ := GlobalTheory.LevelPairing.cSep_spec l
  have h2 : (l.M : ℤ) ∣ Dw.EF x ((cSep d.l₂ - cSep l) • y) := by
    refine GlobalTheory.HalfPairing.dvd_of_mem _ _ _ ?_
    rw [← l.prod, Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.2 l.coprime)]
    refine ⟨?_, sub_mem ?_ b1⟩
    · simpa using sub_mem (h.1.2.1 a2) b2
    · rw [mfr_cover d h] at a1
      exact Ideal.mul_le_left a1
  have h3 := GlobalTheory.Dict.CoverFourier.pd_dvd d h (by rw [mfr_cover d h]; exact Ideal.mul_le_right) z
    (a := y) (a' := y) (by rw [sub_self]; exact zero_mem _)
  have hM : (d.l₂.M : ℤ) = l.M * d.pd := by rw [h.2.1]; push_cast; rfl
  have h4 : (d.l₂.M : ℤ) ∣ _ := hM ▸ mul_dvd_mul_right h2 (d.pd : ℤ)
  have h5 : (d.l₂.M : ℤ) ∣ _ := hM ▸ mul_dvd_mul_left (l.M : ℤ) h3
  have h6 := dvd_add (dvd_add h1 h4) h5
  simp only [map_sub, map_add (f := _), map_nsmul, sub_smul, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    nsmul_eq_mul] at h6
  refine h6.trans (dvd_of_eq ?_)
  ring

end

theorem hatC_eq_datum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (xJ : Fin n → LaJ Xo c d), d.PhiPin ph ψ xJ → ∀ (x₀ : Fin n → Dw.La) (ζ : ℂ) (φc : (Fin n → LevQc Dw d.l₂) → ℂ), (∀ z : Fin n → Dw.La, φc (fun b => Submodule.Quotient.mk (d.pd • x₀ b + l.M • z b)) = ζ * ((ph (fun b => Submodule.Quotient.mk (z b)) : c.F) : ℂ)) → (∀ x : Fin n → Dw.La, φc (fun b => Submodule.Quotient.mk (x b)) ≠ 0 → ∀ b, x b - d.pd • x₀ b ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)) → GlobalTheory.AdTh.hatC d.l₂ φc = fun q => ζ * ((d.eF.symm (d.w x₀ q) : c.F) : ℂ) := by
  intro E _ _ _ H Dw l Xo c n d hd ph ψ xJ hpin x₀ ζ φc hval hsupp
  funext q
  haveI := finite_laJ d hd
  haveI := GlobalTheory.AdTh.PairModel.finite_levQc Dw d.l₂
  haveI := Fintype.ofFinite (Fin n → LaJ Xo c d)
  haveI := Fintype.ofFinite (Fin n → LevQc Dw d.l₂)
  have hM₂ : d.l₂.M ≠ 0 := by have := d.l₂.three_le; omega
  have he : zeta d.l₂.M ^ d.l₂.M = 1 := (Complex.isPrimitiveRoot_exp _ hM₂).pow_eq_one
  have he0 : zeta d.l₂.M ≠ 0 := Complex.exp_ne_zero _
  have hz : d.c₂.F.val (zetaM d.c₂) = zeta d.l₂.M := GlobalTheory.LevelPairing.zetaM_coe d.c₂
  have hz1 : c.F.val (zetaM c) = zeta d.l₂.M ^ d.pd := by
    rw [← hz, ← map_pow, GlobalTheory.LevelCoverDatum.zetaM_cover d hd.2.1]; rfl
  have hφ : c.F.val (d.φδ q) = ∑ z : Fin n → LaJ Xo c d, ((ph z : c.F) : ℂ) * (zeta d.l₂.M ^ l.M) ^
      (∑ b, Dw.EF (qRep (z b)) (cHalf H d.I • levRep (q b))) := by
    change d.c₂.F.val (d.eF (d.φδ q)) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hpin.2.2.2.2.2 q, finsum_eq_sum_of_fintype, map_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [map_mul, map_zpow₀, ← GlobalTheory.Dict.CoverFourier.zetaM_pow d hd, map_pow, hz]
    rfl
  rw [DeltaDat.w, AlgEquiv.symm_apply_apply]
  change _ = ζ * c.F.val (zetaM c ^ pairL (l := l) x₀ (fun b => levRep (q b)) * d.φδ q)
  rw [map_mul, map_zpow₀, hz1, hφ, Finset.mul_sum, Finset.mul_sum, GlobalTheory.AdTh.hatC, finsum_eq_sum_of_fintype]
  symm
  refine Fintype.sum_of_injective
    (fun (z : Fin n → LaJ Xo c d) b => (Submodule.Quotient.mk (d.pd • x₀ b + l.M • qRep (z b)) : LevQc Dw d.l₂))
    (fun z z' e => funext fun b => ?_) _ _ (fun x hx => ?_) (fun z => ?_)
  · have h1 := (Submodule.Quotient.eq _).1 (congrFun e b)
    rw [add_sub_add_left_eq_sub, ← smul_sub] at h1
    rw [← GlobalTheory.HalfPairing.qRep_mk (z b), ← GlobalTheory.HalfPairing.qRep_mk (z' b)]
    exact (Submodule.Quotient.eq _).2 (mem_half_of_smul d hd h1)
  · refine mul_eq_zero_of_left ?_ _
    by_contra hne
    have hx' : (fun b => (Submodule.Quotient.mk (qRep (x b)) : LevQc Dw d.l₂)) = x :=
      funext fun b => GlobalTheory.HalfPairing.qRep_mk _
    choose z hz' using fun b => exists_class d hd (hsupp (fun b => qRep (x b)) (by rwa [hx']) b)
    exact hx ⟨z, (funext hz').trans hx'⟩
  · have hz' : (fun b => (Submodule.Quotient.mk (qRep (z b)) : LaJ Xo c d)) = z :=
      funext fun b => GlobalTheory.HalfPairing.qRep_mk _
    rw [hval (fun b => qRep (z b)), hz', mul_left_comm, ← mul_assoc ζ, mul_left_comm]
    congr 1
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ he0]
    symm
    refine GlobalTheory.Dict.CoverFourier.zpow_congr' hM₂ he ?_
    rw [pairL, pairL, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.dvd_sum fun b _ => dvd_pairing d hd _ _ _

end GlobalTheory.CoverTransform
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumOfFjEqOfRecord
section
open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn

theorem numOf_eq_ofRecord (D : D7) (L : SizeData₂ D) (Del h0 : ℕ) (h1 : D.s.Del = (Del : ℚ))
    (h2 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ)) : GlobalTheory.RunDepth.numOf D L = ofRecord D L Del h0 := by
  have hm : (D.R.m : ℝ) ≠ 0 := by
    intro h
    have := L.etaSz_pos
    rw [h2, h, zero_mul] at this
    exact lt_irrefl _ this
  have e1 : ⌊((D.s.Del : ℚ) : ℝ)⌋₊ = Del := by
    rw [h1, Rat.cast_natCast, Nat.floor_natCast]
  have e2 : ⌊LevelStarExponents.h0 L⌋₊ = h0 := by
    have : LevelStarExponents.h0 L = (h0 : ℝ) := by
      unfold LevelStarExponents.h0
      rw [h2, mul_div_cancel_left₀ _ hm]
    rw [this, Nat.floor_natCast]
  have e3 : (fun z => D.hc (GlobalTheory.RunDepth.plOf D z)) = fun z => D.hc (Formalism.BasicNotions.tauPl D z) := by
    funext z
    obtain ⟨b, t⟩ := z
    cases b <;> rfl
  unfold GlobalTheory.RunDepth.numOf ofRecord
  simp only [e1, e2, e3]

theorem numOf_Fj_eq_ofRecord :
    ∀ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ), D.s.Del = (Del : ℚ) → L.etaSz = (D.R.m : ℝ) * (h0 : ℝ) → ∀ (j : ℕ) (w : HeightOneSpectrum (𝓞 D.what₂.LL)), (GlobalTheory.RunDepth.numOf D L).Fj j w = (ofRecord D L Del h0).Fj j w := by
  intro D L Del h0 h1 h2 j w
  rw [numOf_eq_ofRecord D L Del h0 h1 h2]

end GlobalTheory.BigOn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapRowOfBaseTupleIdentityRowSpanStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneMapRow_of_baseTuple_identityRow_span : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ) (i : Fin D.R.m), R.toLevCh.Is A.μ0 → R.grp_chiW → R.IsFam → R.IsModels → OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → OneMapRow0 T R κ v₀ O i → GlobalTheory.OneMapAll.PinnedDataExist T R κ v₀ i → GlobalTheory.OneMapAll.IdentityRow T R κ v₀ i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → OneMapRowR T R κ v₀ O ph i := by
  first | exact @GlobalTheory.OneMapAll.oneMapRowR_of_clauses | exact GlobalTheory.OneMapAll.oneMapRowR_of_clauses | (intros; apply GlobalTheory.OneMapAll.oneMapRowR_of_clauses <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedProjectionExists
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.DblSiegelChar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hTens_vecMulVec_split {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
    {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (a a' : α → A) (x x' : β → A) :
    hTens c JA JB (Matrix.vecMulVec a x) (Matrix.vecMulVec a' x') =
      (∑ i, ∑ k, a i * JA i k * c (a' k)) * ∑ j, ∑ l, x j * JB j l * c (x' l) := by
  simp only [hTens, Matrix.vecMulVec_apply, map_mul]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

theorem form_swap {σ : E →ₐ[F] E} (hσ : ∀ z, σ (σ z) = z) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) : form σ J y x = σ (form σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, dotProduct, Matrix.mulVec, Finset.mul_sum, map_sum, map_mul, hσ, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem form_inc {σ : E →ₐ[F] E} {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    ∑ j, ∑ l, incV F x j * incM F J j l * cA σ (incV F y l) = inclR (F := F) (AF F) (form σ J x y) := by
  have hc : ∀ x : E, cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun x => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, incV, incM, Matrix.map_apply, hc, dotProduct, Matrix.mulVec, Finset.mul_sum, map_sum, map_mul, mul_assoc]

theorem trace_one_tmul (e : E) : Algebra.trace (AF F) (AE F E) ((1 : AF F) ⊗ₜ[F] e) = algebraMap F (AF F) (Algebra.trace F E e) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  rw [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange, ← Algebra.trace_apply]

theorem eq_zero_of_psi_trace {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (a : AE F E)
    (h : ∀ t : AE F E, ψ (Algebra.trace (AF F) (AE F E) (a * t)) = 1) : a = 0 := by
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  let bb : Module.Basis _ (AF F) (AE F E) := Algebra.TensorProduct.basis (AF F) b
  have hco : ∀ i, ∀ x : AE F E, Algebra.trace (AF F) (AE F E) (x * ((1 : AF F) ⊗ₜ[F] b.traceDual i)) = bb.repr x i := by
    intro i x
    conv_lhs => rw [← bb.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, map_sum]
    simp only [smul_mul_assoc, map_smul, bb, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, trace_one_tmul, mul_comm (b _) (b.traceDual i), Module.Basis.trace_traceDual_mul]
    simp
  refine bb.ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  apply GlobalTheory.DiagNonvan.eq_zero_of_psi_mul hψ
  intro y
  have := h (y • ((1 : AF F) ⊗ₜ[F] b.traceDual i))
  rwa [mul_smul_comm, map_smul, hco, smul_eq_mul, mul_comm] at this

end GlobalTheory.DblSiegelChar

namespace GlobalTheory.DblSiegelChar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def vdiff (σ : E →ₐ[F] E) {d : ℕ} (c : Fin d ⊕ Fin d → AE F E) : Fin d → AE F E :=
  fun l => cA σ (c (Sum.inl l)) - cA σ (c (Sum.inr l))

theorem vdiff_add (σ : E →ₐ[F] E) {d : ℕ} (a b : Fin d ⊕ Fin d → AE F E) :
    vdiff σ (a + b) = vdiff σ a + vdiff σ b := by
  funext l
  simp only [vdiff, Pi.add_apply, map_add (f := _)]
  ring

def pairL (σ : E →ₐ[F] E) {d : ℕ} (JW : Matrix (Fin d) (Fin d) (AE F E)) (c : Fin d ⊕ Fin d → AE F E) :
    (Fin d → AE F E) →ₗ[AF F] AF F where
  toFun u := Algebra.trace (AF F) (AE F E) (-1 * (u ⬝ᵥ (JW *ᵥ vdiff σ c)))
  map_add' u u' := by simp only [add_dotProduct, mul_add, map_add (f := _)]
  map_smul' r u := by simp only [smul_dotProduct, mul_smul_comm, map_smul, RingHom.id_apply]

theorem pairL_apply (σ : E →ₐ[F] E) {d : ℕ} (JW : Matrix (Fin d) (Fin d) (AE F E)) (c : Fin d ⊕ Fin d → AE F E)
    (u : Fin d → AE F E) : pairL σ JW c u = Algebra.trace (AF F) (AE F E) (-1 * (u ⬝ᵥ (JW *ᵥ vdiff σ c))) := rfl

theorem pairL_add (σ : E →ₐ[F] E) {d : ℕ} (JW : Matrix (Fin d) (Fin d) (AE F E)) (a b : Fin d ⊕ Fin d → AE F E) :
    pairL σ JW (a + b) = pairL σ JW a + pairL σ JW b := by
  refine LinearMap.ext fun u => ?_
  simp only [pairL_apply, LinearMap.add_apply, vdiff_add, Matrix.mulVec_add, dotProduct_add, mul_add, map_add (f := _)]

theorem symp_eq (σ : E →ₐ[F] E) {n n₁ d : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (H : Plane E n n₁) (hf : ∑ i, ∑ k, incV F H.y i * incM F JX i k * cA σ (incV F H.x k) = 1)
    (c : Fin d ⊕ Fin d → AE F E) (u : Fin d → AE F E) :
    symp (cA σ) (-1) (incM F JX) (dbl (incM F JW)) (GlobalTheory.DblSiegelX.zs H u) (Matrix.vecMulVec (incV F H.x) c) =
      pairL σ (incM F JW) c u := by
  rw [symp, GlobalTheory.DblSiegelX.zs, hTens_vecMulVec_split, hf, one_mul, pairL_apply]
  congr 2
  have e1 : ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) *ᵥ u) = Sum.elim u u := by
    rw [diagCols, Matrix.fromRows_mulVec, Matrix.one_mulVec]
  have e2 : ∀ U : Fin d ⊕ Fin d → AE F E, ∑ j, ∑ l, U j * dbl (incM F JW) j l * cA σ (c l) =
      U ⬝ᵥ (dbl (incM F JW) *ᵥ fun l => cA σ (c l)) := by
    intro U
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have e3 : vdiff σ c = (fun l => cA σ (c (Sum.inl l))) - fun l => cA σ (c (Sum.inr l)) := rfl
  rw [e1, e2, dbl, Matrix.fromBlocks_mulVec, e3, Matrix.mulVec_sub]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec, add_zero, zero_add,
    Matrix.neg_mulVec, Pi.neg_apply, Pi.sub_apply, Pi.add_apply, mul_neg, mul_sub, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, sub_eq_add_neg]
  simp only [mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rfl

theorem sep (σ : E →ₐ[F] E) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {d : ℕ} (JW : Matrix (Fin d) (Fin d) (AE F E))
    (hdet : IsUnit JW.det) (u : Fin d → AE F E) (h : ∀ c, ψ (pairL σ JW c u) = 1) : u = 0 := by
  classical
  funext j
  refine eq_zero_of_psi_trace hψ (u j) fun t => ?_
  have := h (Sum.elim (fun l => GlobalTheory.ArchTraceNondeg.cAinv σ ((JW⁻¹ *ᵥ Pi.single j (-t)) l)) 0)
  have hv : vdiff σ (Sum.elim (fun l => GlobalTheory.ArchTraceNondeg.cAinv σ ((JW⁻¹ *ᵥ Pi.single j (-t)) l)) 0) =
      JW⁻¹ *ᵥ Pi.single j (-t) := by
    funext l
    simp [vdiff, GlobalTheory.ArchTraceNondeg.cA_cAinv]
  rw [pairL_apply, hv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec, dotProduct_single] at this
  simpa [neg_mul, mul_neg] using this

end GlobalTheory.DblSiegelChar

namespace GlobalTheory.DblSiegelChar

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ), H.IsAdapted σ B X X₁ j₀ j₁ →
    ∃ p : (Fin d ⊕ Fin d → AE F E) → (Fin d → AE F E) →ₗ[AF F] AF F, (∀ a b, p (a + b) = p a + p b) ∧
      (∀ c u, p c u = symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J)) (GlobalTheory.DblSiegelX.zs H u) (Matrix.vecMulVec (incV F H.x) c)) ∧
      ∀ u, (∀ c, B.ψ (p c u) = 1) → u = 0 := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ hH
  have hcm : IsCMExt F E σ := hP.base.cm
  have hψ : IsStd B.ψ := hP.base.std
  have hf : ∑ i, ∑ k, incV F H.y i * incM F X.J i k * cA σ (incV F H.x k) = 1 := by
    rw [form_inc, form_swap (invol hcm) hP.herm.herm, hH.xy, map_one, map_one]
  have hdet : IsUnit (incM F W.J).det := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have h1 := GlobalTheory.ArchTraceNondeg.det_ne_zero_of_hasSig (hP.skew.sig w)
    rw [Matrix.det_smul] at h1
    have h2 : (W.J.map (B.emb w).1).det ≠ 0 := right_ne_zero_of_mul h1
    have h3 : W.J.det ≠ 0 := fun h0 => h2 (by
      have := RingHom.map_det (B.emb w).1 W.J
      rw [h0, map_zero] at this
      exact this.symm)
    have h : (incM F W.J).det = inclR (F := F) (AF F) W.J.det := by rw [RingHom.map_det]; rfl
    rw [h]
    exact (isUnit_iff_ne_zero.2 h3).map _
  exact ⟨pairL σ (incM F W.J), pairL_add σ _, fun c u => (symp_eq σ X.J W.J H hf c u).symm,
    fun u hu => sep σ hψ _ hdet u hu⟩

end GlobalTheory.DblSiegelChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaValuesAtNegIntUnique
section
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.ZetaValUnique

theorem classZeta_eqOn {E : Type} [Field E] [NumberField E] {C : ClassGroup (GlobalTheory.CMVal.OF E)} {Z Z' : ℂ → ℂ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZeta C Z) (h' : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZeta C Z') :
    Set.EqOn Z Z' {1}ᶜ := by
  have ho : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  refine (h.1.analyticOnNhd ho).eqOn_of_preconnected_of_eventuallyEq (h'.1.analyticOnNhd ho) hc
    (z₀ := 2) (by norm_num) ?_
  have hh : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hh.mem_nhds (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by simp)] with s hs
  exact (h.2 s hs).unique (h'.2 s hs)

theorem classZetaVals_unique : ∀ {E : Type} [Field E] [NumberField E] {k : ℕ}, 2 ≤ k →
    ∀ {z z' : ClassGroup (GlobalTheory.CMVal.OF E) → ℚ}, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZetaVals k z →
      GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZetaVals k z' → z = z' := by
  intro E _ _ k hk z z' hz hz'
  funext C
  obtain ⟨Z, hZ, hZv⟩ := hz C
  obtain ⟨Z', hZ', hZv'⟩ := hz' C
  have hne : (1 - (k : ℂ)) ∈ ({1}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, sub_eq_self, Nat.cast_eq_zero]
    omega
  have := classZeta_eqOn hZ hZ' hne
  rw [hZv, hZv'] at this
  exact_mod_cast this

end GlobalTheory.ZetaValUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnramifiedAwayDifferentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_unramified_away_different : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → PsiUnr ψ v := by
  first | exact @GlobalTheory.StdCharUnrF.psiUnr_of_not_le | exact GlobalTheory.StdCharUnrF.psiUnr_of_not_le | (intros; apply GlobalTheory.StdCharUnrF.psiUnr_of_not_le <;> assumption)
end
end

