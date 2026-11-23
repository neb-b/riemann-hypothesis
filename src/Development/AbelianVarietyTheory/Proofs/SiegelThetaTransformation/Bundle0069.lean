module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelMulSplit
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0003
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsVanishingOffFramesLeSpanShortTheta
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0064

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CoverProductIndepOfLift
section
open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.EquivariantLiftInvariance

theorem cover_product_indep_of_lift : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → d.l₂.A = l.A → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → ∀ (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ), d.PsiTie ψ → ∀ w : (Fin n → LevQ Dw d.l₂) → c.F, DatEq d ψ w → ∀ (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) d.c₂.F), P ∈ HHa Dw.mult n d.c₂.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (β : d.c₂.F) (r' : d.Xo₂.X ⟶ Xo.X) (m' : SABMap d.Xo₂.univ.t Xo.univ.t r'), DeltaDat.EtaOK { d with r := r', m := m' } → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k], (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) → ∀ (y : FrPt Xo c k) (y₂ y₂' : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y → FrOver { d with r := r', m := m' } y₂' y → ∀ v v', ShortValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w q)) Λ β N P y₂ v → ShortValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w q)) Λ β N P y₂' v' → evR d.Xo₂ d.c₂ d.cδ y₂ * v = evR d.Xo₂ d.c₂ d.cδ y₂' * v' := by
  intro hC E _ _ _ H Dw l Xo c n d hLev hA hnab ψ htie w hw Λ N hU hT hOK a P hP β r' m' hE' k _ _ _ _
    hk y y₂ y₂' ho ho' v v' hv hv'
  obtain ⟨_, hnab⟩ := hnab
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hN := GlobalTheory.LevelMapsAnyRank.levelMaps Dw
  obtain ⟨hdvd, hM, hcop, hb, hI, hE, -⟩ := hLev
  obtain ⟨g, ρ, ν, hg, hρ, hmv, hfr⟩ := GlobalTheory.exists_levMove_of_frOver hL E H Dw l Xo c n d hN hdvd hM hE
    r' m' hE' k hk y y₂ y₂' ho ho'
  have hM₂ : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  have hbI : d.l₂.Mb ≤ d.I := hb ▸ (Ideal.mul_le_inf.trans inf_le_right)
  have hmb : ((d.l₂.M : ℕ) : 𝓞 E) ∈ d.l₂.Mb := by
    refine (Ideal.mul_le_inf.trans inf_le_left : d.l₂.Mb * d.l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ _) ?_
    rw [d.l₂.prod]; exact Ideal.mem_span_singleton_self _
  obtain ⟨g', hg'⟩ := g.inv d.l₂.M hM₂
  obtain ⟨kI, hkI⟩ := GlobalTheory.DatumInverseCharacter.exists_quot_equiv Dw (hbI hmb) _ g' hg'
  obtain ⟨σ, hσ⟩ := GlobalTheory.DatumInverseCharacter.exists_quot_equiv Dw hmb _ g' hg'
  have hw' := hw g hg kI σ.toEquiv (fun a => (hkI a).symm) hσ
  have hgA : ∀ a, Dw.ModN d.l₂.A (g.f d.l₂.A a - a) := by rw [hA]; exact hg.2.2
  have hc := htie kI g ρ hg hgA hρ (fun a => (hkI a).symm) k y₂ y₂' hfr.1
  have h1 := GlobalTheory.ShortValMove.shortValAt_move hL hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab k ρ.hom ν _ _ y₂ y₂' hmv hfr
    σ.toEquiv hσ n a P hP (fun q => d.eF (w q)) Λ β N v' hv'
  have h2 := GlobalTheory.ShortLiftInvariance.shortValAt_smul d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w q))
    (fun q => d.eF (w (fun b => σ.toEquiv.symm (q b)))) (d.eF (((ψ kI)⁻¹ : c.Fˣ) : c.F))
    (fun q => by rw [hw', map_mul]) Λ β N P y₂ v hv
  have h3 := ((GlobalTheory.shortThetaValue_existsUnique_natural hL hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab n Λ N hU hT hOK a P
    hP _ β).1 k y₂).unique h1 h2
  rw [hc, h3, _root_.mul_mul_mul_comm, ← map_mul, ← map_mul]
  simp

end GlobalTheory.EquivariantLiftInvariance
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSpanningHypotheses
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.SpanInhab

theorem exists_imag_neg {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    ∃ ξ : E, cc ξ = -ξ ∧ ξ ≠ 0 ∧ ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ).im < 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have key : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → z.re = 0 ∧ z.im ≠ 0 := by
    intro z hz
    have h1 := congrArg Complex.re hz
    have h2 := congrArg Complex.im hz
    simp [sq] at h1 h2
    have him : z.im ≠ 0 := by
      intro h; rw [h] at h1; nlinarith [mul_self_nonneg z.re]
    refine ⟨?_, him⟩
    have : z.re * z.im = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right him
  have hE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
    simpa using this
  have hcc : cc (H.rt : E) = -(H.rt : E) := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    have hk := key (τ (H.rt : E)) (by rw [← map_pow, hE, map_neg, map_natCast])
    have : τ (cc (H.rt : E)) = starRingEnd ℂ (τ (H.rt : E)) := IsCMField.complexEmbedding_complexConj E τ _
    rw [this, map_neg]
    apply Complex.ext <;> simp [hk.1]
  have h0 : (H.rt : E) ≠ 0 := by
    intro h
    rw [h] at hE
    have : (H.d : E) = 0 := by linear_combination hE
    exact H.d_prime.ne_zero (by exact_mod_cast this)
  rcases lt_or_gt_of_ne (key _ H.sqrt_neg_disc_sq).2 with h | h
  · exact ⟨H.rt, hcc, h0, fun τ hτ => hτ ▸ h⟩
  · refine ⟨-(H.rt : E), ?_, neg_ne_zero.2 h0, fun τ hτ => by rw [map_neg, hτ]; simpa using h⟩
    have : cc (-(H.rt : E)) = -cc (H.rt : E) := by simp [cc]
    rw [this, hcc]

end GlobalTheory.SpanInhab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatAtAndSpanAtOfHypC
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps GlobalTheory

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.RunLat

theorem thc_le_shortTh {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j)
    (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) : X.Thc s w ≤ X.shortTh w := by
  intro x hx
  simp only [PJ.Thc, PJ.scaled, Submodule.mem_map, LinearMap.smul_apply, LinearMap.id_apply] at hx
  obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := hx
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hz)

theorem spanAt_of_shortG {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j)
    (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) (β : ℝ) (h : WeightAlgebra.ShortG X w (X.Thc s w) β) : PullbackSections.SpanAt X w := by

  obtain ⟨Sh, hSh, hspan, -⟩ := h
  show Submodule.span _ _ = ⊤
  rw [eq_top_iff, ← hspan]
  exact Submodule.span_mono fun x hx => thc_le_shortTh X s w (hSh hx)

end GlobalTheory.RunLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnfoldingConstantTermsAgreeAtGoodEmbeddings
section
open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.Dict


set_option maxHeartbeats 1000000 in
theorem holSub0_le_span_cusp : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), 1 ≤ r → l.A = 1 → (∀ σ, GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ σ, GoodEmb c σ → (∀ k k', ((U σ).X k).Gm = ((U σ).X k').Gm ∧ ((U σ).X k).ξ0 = ((U σ).X k').ξ0) → (∀ k, HasPrinc ((U σ).X k) l.M) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → LastPos Dw a → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → (∀ k, ChiOne ((U σ).X k) (Formalism.L2.PjFree.laU (U σ) a n k)) → GlobalTheory.Dict.holSub0 (U σ).X (Formalism.L2.PjFree.laU (U σ) a n) ≤ Submodule.span ℂ (Formalism.L2.PjFree.rdU (U σ) '' (Formalism.L2.PjFree.cusp Xo c U a n : Set (Rul Xo c))) := by
  intro hC E _ _ _ H Dw l Xo c r U hr hA hU σ hσ hG hP a n hdom hlast hn hχ
  have hrk : r = Dw.p + Dw.q := (hU σ hσ).1
  have h1 : 1 ≤ Dw.p + Dw.q := hrk ▸ hr
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hB : Out.SecBaseChangeSt := hL.secBaseChange
  have hnr : Dw.p + Dw.q ≤ n := by
    have h0 : 0 < Module.finrank ℚ E := Module.finrank_pos
    have : r ≤ Module.finrank ℚ E * r := Nat.le_mul_of_pos_left r h0
    omega
  have hd : ∃ d : DeltaDat Xo c n, d.IsLev ∧ (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) ∧ d.cδ = 1 ∧
      d.pd = 1 ∧ d.l₂.A = l.A ∧ ∃ ph x₀, d.PhiPin ph 1 x₀ := by
    obtain ⟨d, e1, -, e2, -, -, hδ, hlev, hnab⟩ :=
      GlobalTheory.LevelCover.exists_deltaDat_isLev E H Dw l Xo c h1 n 1 ⊤ l Xo c rfl
        ⟨dvd_rfl, le_rfl, dvd_rfl⟩ (Nat.mul_one _).symm (Nat.coprime_one_left _) (Ideal.mul_top _).symm
        (top_sup_eq _)
    obtain ⟨f, ph, x₀, hpin⟩ := GlobalTheory.exists_phiPin_of_character E H Dw l Xo c n d hlev hnr 1
    exact ⟨{ d with φδ := f }, hlev, hnab, hδ, e1, congrArg (·.A) e2, ph, x₀, hpin⟩
  obtain ⟨d, hlev, hnab, hδ, hpe, hAe, ph, x₀, hpin⟩ := hd
  have hT : AllTest d.Xo₂ d.c₂ := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw d.l₂ d.Xo₂ d.c₂
  obtain ⟨_, nab, -⟩ := GlobalTheory.CanonConn.exists_isNab hL E H Dw l Xo c
  have hunit : UnitC d := fun A y => by
    have : evR d.Xo₂ d.c₂ d.cδ y = 1 := by
      rw [hδ]
      exact evalAt_one _ _ _ (hT _ _)
    rw [this, norm_one]
  have h3 : ¬ 3 ∣ d.pd := by rw [hpe]; decide
  have htie : d.PsiTie 1 := by
    intro k g ρ _ _ _ _ K _ _ _ y y' _
    have h : ∀ z : FrPt d.Xo₂ d.c₂ K, evR d.Xo₂ d.c₂ d.cδ z = 1 := fun z => by
      rw [hδ]
      exact evalAt_one _ _ _ (hT _ _)
    change evR d.Xo₂ d.c₂ d.cδ y' =
      algebraMap d.c₂.F K (d.eF ((1 : c.Fˣ) : c.F)) * evR d.Xo₂ d.c₂ d.cδ y
    rw [h y, h y']
    simp
  have htot : ShortValTot Xo c nab 1 0 a n d :=
    GlobalTheory.shortValTot_of_pinned hL hC E H Dw l Xo c n d (GlobalTheory.levelMaps_closed hL E H Dw h1)
      (GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c).2.2.1 (GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c)
      (GlobalTheory.Frames.algebraic_laws hB E H Dw _ _ _).2.2.1 hT hlev hAe hnab (fun _ => ⟨ph, 1, x₀, hpin, htie⟩)
      nab 1 0 a
  refine (_root_.GlobalTheory.Dict.holSub0_le_span_shortGen hC E H Dw l Xo c n d σ r (U σ) hσ (hU σ hσ) hr hA hG hP hlev hnab hunit h3
    (fun _ => ⟨ph, 1, x₀, hpin⟩) nab 1 0 a Nat.one_pos hdom hn hχ htot).trans
    (Submodule.span_mono (Set.image_mono ?_))
  exact _root_.GlobalTheory.Dict.shortInCusp_cusp hC E H Dw l Xo c n d r U hr hU hlev hnab hunit (fun _ => ⟨ph, 1, x₀, hpin⟩) nab 1 0 a hdom hlast

end GlobalTheory.Dict
end

