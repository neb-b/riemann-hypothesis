module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0491
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0623
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticFrameFamilyOfHolomorphicPeriodMaps
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0519
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsOkPins
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0406
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0354
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrderThree
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0475
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0196
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0005
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0379
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticFlagDomainFrameLiftAlgebraicChart
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase

theorem exists_analytic_frame_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∃ (k' : U.Comp) (s : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q)), AnalyticAt ℂ s (c'.e y) ∧ ∀ᶠ w in 𝓝 (c'.e y), ∃ hs : s w ∈ (U.X k').dom, cxPt T.Z (U.un k' ⟨s w, hs⟩) = cxOf e σ hj (c'.e.symm w) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU X j hj hjo y hy c' hyc
  rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with hr | hr
  · obtain ⟨W⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf _ _ _ _ _ _ _ _ U hU
    obtain ⟨i, B, P, hB, hb₀, -, hper, -, hq⟩ := _root_.GlobalTheory.ShFam.chart_lift_periods_of_openPart E H Dw l Xo c O β Y T F e σ W.g _ W.F X j hj hjo y hy c' hyc
    obtain ⟨q₀, hq₀, hu₀⟩ := hq _ hb₀
    have hne : ¬ LiesIn (cxOf e σ hj y) (genBd T.Z) := by
      rw [← c'.e.left_inv hyc, ← hq₀]; exact not_liesIn_cxPt q₀
    obtain ⟨k, x, -, hkx⟩ := GlobalTheory.HodgeSmooth.exists_orth (Z := T.Z) hσ hU hne
    have hg : IsEmpty (Fin W.g) := by
      refine ⟨fun a => ?_⟩
      have := (W.e a).2.2
      simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult] at this
      split_ifs at this <;> omega
    refine ⟨k, fun _ => x.1, analyticAt_const, Filter.mem_of_superset (hB.mem_nhds hb₀) fun w hw => ⟨x.2, ?_⟩⟩
    obtain ⟨q, hq1, hq2⟩ := hq w hw
    have hfib : W.F.u i (P (c'.e y)) = W.F.u i (P w) :=
      (W.F.fibre i _ _ (hper _ hb₀) (hper w hw)).2 ⟨LinearEquiv.refl _ _, LinearEquiv.refl _ _, fun _ _ => rfl,
        fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, fun a => funext fun t => (hg.false t).elim⟩
    have e1 : cxPt T.Z q₀ = cxPt T.Z q := cxPt_congr (hu₀.symm.trans (hfib.trans hq2))
    rw [← hq1, ← e1, hq₀, c'.e.left_inv hyc]
    exact hkx
  · obtain ⟨W, hinj⟩ := GlobalTheory.HodgeSmooth.exists_unfWit_inj hσ hU hr
    obtain ⟨i, B, P, hB, hb₀, -, hper, hdiff, hq⟩ := _root_.GlobalTheory.ShFam.chart_lift_periods_of_openPart E H Dw l Xo c O β Y T F e σ W.g _ W.F X j hj hjo y hy c' hyc
    obtain ⟨q₀, -, hu₀⟩ := hq _ hb₀
    obtain ⟨k, x₁, t, hbor⟩ := hU.2.2.1 q₀
    have hk : W.ik k = i := W.F.disj _ _ _ _ (W.period k x₁) (hper _ hb₀)
      (((W.lie k x₁).1.symm.trans hbor.1.symm).trans hu₀.symm)
    subst hk
    obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
    obtain ⟨hp0, hty⟩ := hU.2.1 k
    have hmult : ∀ τ : E →+* ℂ, Formalism.L2.PjFree.relab c σ τ ∉ (U.X k).Ψ → Dw.mult τ = (U.X k).p0 := by
      intro τ hτ
      rw [hp0]
      exact if_neg fun h => hτ ((hty _).2 ((hrt τ).2 h))
    have hrep : ∀ b ∈ B, ∀ q : FrPt Xo c (Formalism.L2.Pj.CAt σ), W.F.u (W.ik k) (P b) = q.x →
        ∃ x' : (U.X k).dom, (U.un k x').x = q.x ∧ ∃ h : (Fin W.g → ℂ) ≃ₗ[ℂ] (Fin W.g → ℂ), ∀ v, P b v =
          h (fun j => Formalism.L2.PjFree.perFr (U.X k) x'.1 (W.φ k v : Fin (Dw.p + Dw.q) → E)
            (Formalism.L2.PjFree.relab c σ (W.e j).1) ((W.e j).2 : ℕ)) := by
      intro b hb q hqu
      obtain ⟨x', hx', h, hh⟩ := _root_.GlobalTheory.PointLift.pm_lift_pointwise E H Dw l Xo c σ _ U W hσ hU hinj k (P b) (hper b hb) q hqu
      exact ⟨x', hx', h, fun v => (hh v).trans (congrArg h (funext fun j => W.Pm_eq k x' v j))⟩
    obtain ⟨s, hs, hev⟩ := _root_.GlobalTheory.PeriodFamFrame.lift_frame E (Dw.p + Dw.q) (U.X k) _ (W.φ k) W.g (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1)
      (fun j => ((W.e j).2 : ℕ)) X.dim B P (c'.e y) hB hb₀ (fun b hb => (hper b hb).1) hdiff
      (fun ρ hρ m hm => by
        obtain ⟨τ', hτ'⟩ := hbij.2 (conjEmb ρ)
        have hn : Formalism.L2.PjFree.relab c σ τ' ∉ (U.X k).Ψ := by
          rw [hτ']
          exact ((U.X k).cmType ρ).1 hρ
        have hm' : m < Dw.mult τ' := by rw [hmult τ' hn]; exact hm
        exact ⟨W.e.symm ⟨τ', ⟨m, hm'⟩⟩, by rw [Equiv.apply_symm_apply]; exact hτ', by rw [Equiv.apply_symm_apply]⟩)
      (fun j j' h1 h2 => by
        have h1' := hbij.1 h1
        exact W.e.injective (Sigma.ext h1' ((Fin.heq_ext_iff (by rw [h1'])).2 h2)))
      (fun j hj' => by
        exact lt_of_lt_of_eq (W.e j).2.2 (hmult _ hj'))
      (fun b hb => by
        obtain ⟨q, -, hqu⟩ := hq b hb
        obtain ⟨x', -, h, hh⟩ := hrep b hb q hqu
        exact ⟨x'.1, x'.2, h, hh⟩)
    refine ⟨k, s, hs, (hev.and (hB.mem_nhds hb₀)).mono fun w hw => ⟨hw.1.1, ?_⟩⟩
    obtain ⟨q, hq1, hqu⟩ := hq w hw.2
    obtain ⟨x', hx', h, hh⟩ := hrep w hw.2 q hqu
    obtain ⟨h1, h2⟩ := hw.1.2 x'.1 x'.2 ⟨h, hh⟩
    rw [← hq1]
    exact cxPt_congr ((GlobalTheory.TrueCx.PointWell.pt_eq_of_block hU hσ k ⟨s w, hw.1.1⟩ x' h1 h2).trans hx')

end GlobalTheory.LieBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonDenominatorRatMatrices
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem rat_matrix_common_denom : ∀ (a g : ℕ) (b : Fin a → Matrix (Fin g) (Fin g) ℚ), ∃ (D : ℕ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < D ∧ ∀ k i j, (B k i j : ℚ) = D * b k i j := by
  intro a g b
  classical
  let D : ℕ := ∏ k, ∏ i, ∏ j, (b k i j).den
  have hdvd : ∀ k i j, (b k i j).den ∣ D := fun k i j =>
    dvd_trans (Finset.dvd_prod_of_mem (fun j => (b k i j).den) (Finset.mem_univ j))
      (dvd_trans (Finset.dvd_prod_of_mem (fun i => ∏ j, (b k i j).den) (Finset.mem_univ i))
        (Finset.dvd_prod_of_mem (fun k => ∏ i, ∏ j, (b k i j).den) (Finset.mem_univ k)))
  refine ⟨D, fun k i j => ((D / (b k i j).den : ℕ) : ℤ) * (b k i j).num, ?_, ?_⟩
  · exact Finset.prod_pos fun k _ => Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => (b k i j).den_pos
  · intro k i j
    obtain ⟨m, hm⟩ := hdvd k i j
    have hD : D = (b k i j).den * m := hm
    simp only
    rw [hD, Nat.mul_div_cancel_left _ (b k i j).den_pos]
    push_cast
    rw [mul_comm ((b k i j).den : ℚ) (m : ℚ), _root_.mul_assoc, Rat.den_mul_eq_num]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonIntKernelPsdBlockNotPosDef
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem intPsd_common_kernel_of_sum_not_posDef : ∀ (a g rk : ℕ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), (∀ k, ((B k).map (Int.cast : ℤ → ℝ)).PosSemidef) → (∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → B k j l = 0) → ¬ (((∑ k, B k).map (Int.cast : ℤ → ℝ)).submatrix (Subtype.val : {j : Fin g // j.val < rk} → Fin g) Subtype.val).PosDef → ∃ v : Fin g → ℤ, v ≠ 0 ∧ (∀ j : Fin g, rk ≤ j.val → v j = 0) ∧ ∀ k, (B k).mulVec v = 0 := by
  intro a g rk B hpsd hsupp hnot
  set S : Matrix (Fin g) (Fin g) ℤ := ∑ k, B k with hS
  let e : {j : Fin g // j.val < rk} → Fin g := Subtype.val
  have hcast : ∀ (M : Matrix (Fin g) (Fin g) ℤ) (u : Fin g → ℤ) (i : Fin g),
      ((M.map (Int.cast : ℤ → ℝ)) *ᵥ (fun j => (u j : ℝ))) i = (((M *ᵥ u) i : ℤ) : ℝ) := by
    intro M u i
    simp [mulVec, dotProduct]
  have hSmap : S.map (Int.cast : ℤ → ℝ) = ∑ k, (B k).map (Int.cast : ℤ → ℝ) := by
    ext i j; simp [hS, Matrix.sum_apply]
  have hSR : ((S.map (Int.cast : ℤ → ℝ)).submatrix e e).PosSemidef := by
    rw [hSmap]
    exact (posSemidef_sum _ (fun k _ => hpsd k)).submatrix e
  have hdetR : ((S.map (Int.cast : ℤ → ℝ)).submatrix e e).det = 0 := by
    by_contra hdet
    apply hnot
    rw [posDef_iff_dotProduct_mulVec]
    refine ⟨hSR.isHermitian, fun x hx => ?_⟩
    have hnn := (posSemidef_iff_dotProduct_mulVec.1 hSR).2 x
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exfalso
      have hk := hSR.dotProduct_mulVec_zero_iff.1 h.symm
      exact hdet (exists_mulVec_eq_zero_iff.1 ⟨x, hx, hk⟩)
  have hdetZ : (S.submatrix e e).det = 0 := by
    have h := (Int.castRingHom ℝ).map_det (S.submatrix e e)
    have h2 : (Int.castRingHom ℝ).mapMatrix (S.submatrix e e)
        = (S.map (Int.cast : ℤ → ℝ)).submatrix e e := rfl
    rw [h2, hdetR, eq_intCast] at h
    exact_mod_cast h
  obtain ⟨w, hw0, hw⟩ := exists_mulVec_eq_zero_iff.2 hdetZ
  let v : Fin g → ℤ := fun j => if h : j.val < rk then w ⟨j, h⟩ else 0
  have hSi : ∀ i j : Fin g, rk ≤ i.val → S i j = 0 := by
    intro i j hi
    simp [hS, Matrix.sum_apply, hsupp _ i j (Or.inl hi)]
  have hsplit : ∀ i : Fin g, (S *ᵥ v) i = ∑ j : {j : Fin g // j.val < rk}, S i j * w j := by
    intro i
    simp only [mulVec, dotProduct]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun j : Fin g => j.val < rk)]
    have h2 : ∑ j : {j : Fin g // ¬ j.val < rk}, S i j * v j = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [v, j.2]
    rw [h2, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [v, j.2]
  have hSv : S *ᵥ v = 0 := by
    funext i
    rw [hsplit]
    by_cases hi : i.val < rk
    · have := congrFun hw ⟨i, hi⟩
      simpa [mulVec, dotProduct, e] using this
    · push_neg at hi
      simp [hSi i _ hi]
  refine ⟨v, ?_, ?_, ?_⟩
  · intro hv
    apply hw0
    funext j
    have := congrFun hv j.val
    simpa [v, j.2] using this
  · intro j hj
    simp [v, not_lt.2 hj]
  · intro k
    let vR : Fin g → ℝ := fun j => (v j : ℝ)
    have hQnn : ∀ k, 0 ≤ star vR ⬝ᵥ (((B k).map (Int.cast : ℤ → ℝ)) *ᵥ vR) := fun k =>
      (posSemidef_iff_dotProduct_mulVec.1 (hpsd k)).2 vR
    have hsum : ∑ k, star vR ⬝ᵥ (((B k).map (Int.cast : ℤ → ℝ)) *ᵥ vR) = 0 := by
      rw [← dotProduct_sum, ← sum_mulVec, ← hSmap]
      have : (S.map (Int.cast : ℤ → ℝ)) *ᵥ vR = 0 := by
        funext i; rw [hcast, hSv]; simp
      rw [this, dotProduct_zero]
    have hk0 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hQnn k)).1 hsum k (Finset.mem_univ _)
    have hker := (hpsd k).dotProduct_mulVec_zero_iff.1 hk0
    funext i
    have := congrFun hker i
    rw [hcast] at this
    simpa using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGIs
section
noncomputable section

namespace GlobalTheory.Mem.Top.Bl.TrueLocal

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.Mem.Per GlobalTheory.Glob GlobalTheory.Mem.TruePeriods GlobalTheory.Mem.PeriodTie

theorem omTied_retie_of_cube {D : D7} (hF : FieldOK D.host D.what₂.embLL D.embE) (h3 : ∀ z : ℂ, z ^ 3 = 1 → z ∈ coefM D) {δ : ℂ}
    (h : IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ) : Formalism.L2.GlobalTheoryTheory.OmegaCompatible (retie D) δ := by
  obtain ⟨δ', h', m2, m3⟩ := exists_delta_data D hF
  have h0 := delta_ne_zero h'
  have hu0 : δ / δ' ≠ 0 := div_ne_zero (delta_ne_zero h) h0
  have hu : (δ / δ') ^ 12 = 1 := by
    unfold IsDiscriminantTwelfthRootOfIdealLattice at h h'
    rw [div_pow, h, ← h', div_self (pow_ne_zero _ h0)]
  have hmap : lamOf D D.host.ccK δ = (lamOf D D.host.ccK δ').map (AddMonoidHom.mulLeft (δ / δ')) := by
    rw [lamOf_eq_map, lamOf_eq_map, AddSubgroup.map_map]
    congr 1
    ext; simp [← mul_assoc, div_mul_cancel₀ _ h0]
  generalize δ / δ' = u at hu0 hu hmap
  refine (ties_of_data hF h ?_ ?_).1
  · have e : g2 (lamOf D D.host.ccK δ) = (u ^ 4)⁻¹ * g2 (lamOf D D.host.ccK δ') := by
      unfold g2
      rw [hmap, Model.eisG_map _ _ hu0]; ring
    rw [e]
    exact mul_mem (inv_mem (h3 _ (by rw [← pow_mul, hu]))) m2
  · have e : g3 (lamOf D D.host.ccK δ) = (u ^ 6)⁻¹ * g3 (lamOf D D.host.ccK δ') := by
      unfold g3
      rw [hmap, Model.eisG_map _ _ hu0]; ring
    rw [e]
    refine mul_mem (inv_mem ?_) m3
    rcases sq_eq_one_iff.1 (show (u ^ 6) ^ 2 = 1 by rw [← pow_mul, hu]) with e | e <;> rw [e]
    · exact one_mem _
    · exact neg_mem (one_mem _)

open GlobalTheory.Mem.Top.ColOwe GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC in
set_option maxHeartbeats 1000000 in
theorem omTied_withTrue {B : Base} {C : Cols B} (hF : FieldOK B.host B.embLL B.embE) (hc : B.host.ccK = ⊤) {δ : ℂ}
    (h : Th.IsDiscriminantTwelfthRootOfIdealLattice B.host ⊤ δ) (Z : Later B C) (hZ : Z.G.gx = Per.trueGx B.host B.embLL B.embE (Equiv.refl _)) :
    Formalism.L2.GlobalTheoryTheory.OmegaCompatible (recOf Z) δ := by
  have h1 : IsDiscriminantTwelfthRootOfIdealLattice (recOf Z) (recOf Z).host.ccK δ := by
    have : (recOf Z).host.ccK = ⊤ := hc
    rw [this]; exact h
  have h2 := omTied_retie_of_cube (D := recOf Z) hF (fun z hz => B.fixedField_le_coefficientField (B.KsC_le_LL0C (B.rootsField_le_KsC
    ((le_sup_right.trans le_sup_left : Fld.cycField (3 ^ 4) ≤ Fld.rootsField B.toPre)
      (Fld.mem_cycField (by norm_num) (by rw [show 3 ^ 4 = 3 * 27 by norm_num, pow_mul, hz, one_pow])))))) h1
  obtain ⟨W, V, S, N, G⟩ := Z
  obtain ⟨M, i, e, a, b, c⟩ := h2
  refine ⟨M, i, e, a, b, fun τ => ?_⟩
  obtain ⟨d, hd, hs⟩ := c τ
  refine ⟨d, hd, fun s => ?_⟩
  have : (recOf (⟨W, V, S, N, G⟩ : Later B C)).gx = G.gx := rfl
  rw [this, show G.gx = _ from hZ]
  exact hs s

section Stages

open Formalism.MainNotions.G Formalism.L2.G IsDedekindDomain Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.ConcreteRecord GlobalTheory.Mem.Top.ColOwe GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B}


set_option maxHeartbeats 4000000 in
theorem isLocalFamily_stages (sc : Scale) (Z Z' : Later B C) (L0 : LevelData (recOf Z)) (T : ∀ u, Forms0 (recOf Z) u) (g)
    (h : IsLocalFamily sc (recOf Z) L0 T g) : IsLocalFamily sc (recOf Z') L0 (fun u => forms0Re Z' (T u)) g := by
  run_tac do
    let m ← Lean.Elab.Tactic.getMainGoal
    m.withContext do m.assign (← Lean.Meta.getFVarFromUserName `h)

end Stages

section Main

open Formalism.MainNotions.G Formalism.L2.G IsDedekindDomain Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.ConcreteRecord GlobalTheory.Mem.Top.ColOwe GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC
open Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top.GroupRetwisting

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

theorem companion_of_colsHermS {D : D7} (H : Formalism.L2.Herm.ColsHermS D) : Companion D H.base.lev0 := fun u =>
  have hi : IsIntegral ℤ (D.host.conj ((H.atT u).piU : D.host.E)) :=
    map_isIntegral_int D.host.conj (RingOfIntegers.isIntegral_coe _)
  ⟨Ideal.span {(⟨_, hi⟩ : 𝓞 D.host.E)}, (H.baseL u ⟨_, hi⟩ rfl).1⟩

theorem exists_gTiedS_heq {D : D7} (H : Formalism.L2.Herm.HermColsCh D) (H0 : Formalism.L2.Herm.Herm0 D) (h : H0.lev0 = H.lev0) :
    ∃ g : Formalism.L2.Herm.SymmetricGroupCompatibility D H, HEq g H0.g := by
  obtain ⟨l, g⟩ := H0
  dsimp only at h
  subst h
  exact ⟨g, HEq.rfl⟩

theorem herm0_eq_to0 {D : D7} (X : Formalism.L2.Herm.FullTiedS D) (H0 : Formalism.L2.Herm.Herm0 D) (h : X.base.lev0 = H0.lev0)
    (hg : HEq X.g H0.g) : H0 = X.to0 := by
  obtain ⟨l, g⟩ := H0
  dsimp only at h hg
  subst h
  obtain rfl := eq_of_heq hg
  rfl

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

theorem columnLocalData_of_levelZero_concreteData (w : ColW B f T) (Z : w.Lt) (C : ColsTiedSym (w.D Z)) (hC : TC.StdC w.I w.l Z C)
    (hL : ∀ u, TC.StdLvC w.I w.l Z u (C.forms u)) (hV : Formalism.L2.Herm.VolumeCompatible (w.D Z)) (hO : Formalism.L2.GlobalTheoryTheory.OmegaCompatible (w.D Z) w.I.J.δ)
    (Gt : GatTies (w.D Z)) (c : LatCmp (w.D Z)) (G : GroupCompatibilityAll (w.D Z) Gt c) (hR : IsRecG K.s (w.D Z) Gt c G.herm G.forms)
    (hl : G.herm.lev0 = C.herm.base.lev0) (hf : G.forms = fun u => (C.forms u).to0)
    (hpl : ∀ u v hg (a : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' a)) (x : 𝓞 (w.D Z).host.F),
      x ∈ ((G.herm.g u v hg).pl a).1.asIdeal ↔ (0 : WithTop ℤ) < (w.D Z).what₂.places.val v
        (tauLL (w.D Z) (Gt.gat_pos u v hg ⟨a, s⟩) (algebraMap (w.D Z).host.F (w.D Z).host.E (x : (w.D Z).host.F)))) :
    Nonempty (ColumnDataSplitPrimes K w Z) := by
  obtain ⟨g, hg⟩ := exists_gTiedS_heq C.herm.base G.herm hl
  obtain ⟨Fu, h1, h2⟩ := _root_.GlobalTheory.Mem.Col2.FullDt.exists_colsFullS w.I w.ok w.pins w.l Z C g hC hV
  have e : Fu.1.base.lev0 = G.herm.lev0 :=
    (congrArg (fun H : Formalism.L2.Herm.ColsHermS (w.D Z) => H.base.lev0) Fu.2).trans hl.symm
  exact ⟨⟨⟨C, hC, hL, Fu, h2, Gt, c, G, herm0_eq_to0 Fu.1 G.herm e (h1.trans hg), hf,
    gPlTiedS_of G.herm hpl _ _ e (h1.trans hg)⟩, hR, hO⟩⟩


set_option maxHeartbeats 8000000 in
theorem nonempty_columnLocalData_of_standardConcreteFamily (w : ColW B f T) (Z : w.Lt) (C : ColsTiedSym (w.D Z)) (hC : TC.StdC w.I w.l Z C)
    (hL : ∀ u, TC.StdLvC w.I w.l Z u (C.forms u)) (g) (hd)
    (h : IsLocalFamily K.s (w.D Z) C.herm.base.lev0 (fun u => (C.forms u).to0) g)
    (hV : Formalism.L2.Herm.VolumeCompatible (w.D { Z with G := { Z.G with gat := g, gat_d := hd } }))
    (hO : Formalism.L2.GlobalTheoryTheory.OmegaCompatible (w.D { Z with G := { Z.G with gat := g, gat_d := hd } }) w.I.J.δ) :
    Nonempty (ColumnDataSplitPrimes K w { Z with G := { Z.G with gat := g, gat_d := hd } }) := by
  obtain ⟨Gt, c, G, hR, hl, hf, hpl⟩ := isRecG_of_isLocalFamily C.joint0
    (fun u => _root_.GlobalTheory.Mem.Col2.TC.additiveCharacter_typePrimes_values_coefficientField w.I w.ok w.pins w.l Z (C.forms u).gl (hC u).gl) hd h
  exact columnLocalData_of_levelZero_concreteData w _ (colsRe _ C) (stdC_colsRe w.I w.l _ C hC) (fun u => stdLvC_colsRe w.I w.l _ C u (hL u)) hV hO Gt c G hR
    (funext hl) (funext fun u => (hf u).trans ((forms0Re_setGat g hd _).symm.trans (columnFormsAlongLaterStages_stageZero_eq _ C u).symm)) hpl


set_option maxHeartbeats 8000000 in
theorem exists_trueVolume_stage_of_any_column_choice (p : WP) : StepW p fun K B f T w => ∃ G : GJStage B w.C, GIs2 K w G := by
  refine StepW.of_all fun K B f T w hO _ _ => ?_
  obtain ⟨Z₀⟩ := TrueColsTest.later w.l (JetEx.hasLetters_of_over hO)
  obtain ⟨C, hC, hL⟩ := _root_.GlobalTheory.Mem.Col2.TC.colsTiedSym_std w.I w.ok w.pins w.l Z₀
  obtain ⟨g, hd, h⟩ := exists_isLocalFamily K.s (D := w.D Z₀) (fun u => (C.forms u).to0) C.herm.std (companion_of_colsHermS C.herm)
    C.joint0 fun u => _root_.GlobalTheory.Mem.Col2.TC.additiveCharacter_typePrimes_values_coefficientField w.I w.ok w.pins w.l Z₀ (C.forms u).gl (hC u).gl
  refine ⟨{ Z₀.G.withTrue with gat := g, gat_d := hd }, (LayerTwoModel.gIs2_iff w _).2 fun W V S N => ?_⟩
  have hV : Formalism.L2.Theta.VolTieG (w.D ⟨W, V, S, N, { Z₀.G.withTrue with gat := g, gat_d := hd }⟩) :=
    GlobalTheory.T.volumesAgreeAdelic_of_trueVolume _ fun _ => rfl
  refine ⟨hV, nonempty_columnLocalData_of_standardConcreteFamily w ⟨W, V, S, N, Z₀.G.withTrue⟩ (colsRe _ C) (stdC_colsRe w.I w.l _ C hC)
    (fun u => stdLvC_colsRe w.I w.l _ C u (hL u)) g hd ?_ hV.hermVolTied
    (omTied_withTrue w.fld w.px.ccK_top w.ok.amb_ok.delta _ rfl)⟩
  have h' := isLocalFamily_stages K.s Z₀ ⟨W, V, S, N, Z₀.G.withTrue⟩ _ _ g h
  exact (congrArg (fun F => IsLocalFamily K.s (recOf ⟨W, V, S, N, Z₀.G.withTrue⟩) C.herm.base.lev0 F g)
    (funext (columnFormsAlongLaterStages_stageZero_eq ⟨W, V, S, N, Z₀.G.withTrue⟩ C))).mpr h'

theorem exists_trueVolumeStage_columnChoiceStep : StepW Pinned fun K B f T w => ∃ G : GJStage B w.C, GIs2 K w G := exists_trueVolume_stage_of_any_column_choice Pinned

end Main

end GlobalTheory.Mem.Top.Bl.TrueLocal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGreenCuspidalLabellingSameGenerators
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.GreenSide

open Polynomial

theorem eSerC_eq_of_gen (hG : GlobalTheory.Published.GreenCuspidal) (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g)
    (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y)
    (z : ℕ → Formalism.CyclotomicNorms.Fbar g) (hz : IsGenSys z) (he : z = L.gen) (htL : t = L.teich)
    (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) (convC t ht z hz))
    (hO : ∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple τ →
      Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) τ → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (convC t ht z hz) τ (O.lab d τ))
    (r : ℕ) (f : (ZMod g)[X]) (hr : 1 ≤ r) : GlobalTheory.GLq.eSerC L r f = eSerO O r f := by
  subst he
  exact _root_.GlobalTheory.SerCmp.eSerC_eq_eSerO hG g L t ht hz htL O hO r f hr

theorem exists_greenLab : GlobalTheory.Published.GreenCuspidal → ∀ (D : D7) (cf : CharFrame D) (Γ : GrpSide D), TypesTrue D.ntypes cf.P cf.W → (∀ k, Γ.ζ k = @GlobalTheory.GLq.LabelDatum.gen _ ⟨D.host.g_prime k⟩ (@GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩)) → ∃ Γ' : GrpSide D, GlobalTheory.PendOf.GreenLab Γ' ∧ ∀ k, Γ'.ζ k = Γ.ζ k := by
  intro hG D cf Γ hT hζ
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  have key : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      ∃ O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k))
          (convC (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (Γ.ζ k) (Γ.ζ_gen k)),
        Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O ∧ LabTwLawO O ∧
        (∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) (ZMod (D.host.g k)))), 1 ≤ d → CategoryTheory.Simple τ →
          Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod (D.host.g k)) τ →
          Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (convC (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (Γ.ζ k) (Γ.ζ_gen k)) τ
            (O.lab d τ)) ∧
        ∀ f, D.ntypes.eSer k f = eSerO O D.R.r f := by
    intro k
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    obtain ⟨O, h1, h2, hO⟩ := GlobalTheory.CuspTwist.exists_labelMap_twist_cuspLabel (ZMod (D.host.g k)) _
      (_root_.GlobalTheory.GreenParam.cuspParam_of_green hG (D.host.g k) (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (Γ.ζ k) (Γ.ζ_gen k))
    exact ⟨O, h1, h2, hO, fun f => (hT.ser k f).trans
      (eSerC_eq_of_gen hG _ _ _ _ _ _ (hζ k) (hT.teich k) O hO D.R.r f hr)⟩
  refine ⟨{ Γ with
    O := fun k => (key k).choose
    eSer_def := fun k f => (key k).choose_spec.2.2.2 f
    O_equiv := fun k => (key k).choose_spec.1
    O_tw := fun k => (key k).choose_spec.2.1 }, ?_, fun _ => rfl⟩
  intro k d
  exact (key k).choose_spec.2.2.1 d

end GlobalTheory.GreenSide

end
end

