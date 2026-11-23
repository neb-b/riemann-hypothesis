module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CoeffMemOfLoc
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0002
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsComplexArcDatumCmFibre
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmNumbersOfGood
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM


open scoped nonZeroDivisors in
theorem exists_locGen_at {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K))
    (I : FractionalIdeal (𝓞 K)⁰ K) : ∃ c : K, IsLocGen p c I := by
  obtain ⟨c, hc⟩ := p.valuation_surjective K (WithZero.exp (-(FractionalIdeal.count K p I)))
  exact ⟨c, (isLocGen_iff_valuation_eq p c I).2 hc⟩

theorem cmNumbers_of_good : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) [StarRing (𝓞 E)] (l : Level H) (c : Coeff l) (nΨ n' f : ℕ) (o : LamObj c nΨ n') (La logOm : ℝ), (∀ a : 𝓞 E, star a = H.bar a) → LamObjGood o f La → ∀ L : LamLetters o, L.IsGood → 1 ≤ La → LamDegSt H logOm → CMNumbers0 o.LamL L.ℓ o.Tl.dual La logOm := by
  intro hK E _ _ _ H _ l c nΨ n' f o La logOm hbar hG L hL hLa hDeg
  have hdeg := hDeg l c hbar nΨ n' f o La hG
  have hdet := GlobalTheory.LamF.Ind.lamInd E H l c hbar nΨ n' f o La hG L hL
  choose Hm hH hn hsq using GlobalTheory.LamF.lamLen hK.theta hK.laws E H l c hbar nΨ n' f o La hG L hL
  have hloc := GlobalTheory.LamF.letters_det_valuation_le E H l c nΨ n' f o La hG L hL
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hvΨ, hv', hT, hLam, hkl, hka, -⟩ := hG
  obtain ⟨-, -, -, hℓ⟩ := hL
  have hlg : ∀ k, (L.ℓ k).Good := fun k => by
    have := hℓ k
    revert this
    cases L.src k with
    | inl q => intro h1; rw [h1]; exact (hvΨ q.2).1
    | inr q => intro h1; rw [h1]; exact (hv' q.2).1
  have hnd : ∀ k, (L.ℓ k).ndeg = logOm / 2 := fun k => by
    have := hℓ k
    revert this
    cases L.src k with
    | inl q => intro h1; rw [h1]; exact hdeg.1 q.2
    | inr q => intro h1; rw [h1]; exact hdeg.2 q.2
  have hkey := key_deg hK.key o.K₁ o.xB o.Tl o.LamL hT hLam hkl hka
  have hHad := hadamard_local_base o.K₁ o.xB.P.g o.LamL L.ℓ L.U Hm La hLam.1 hlg hdet (by linarith) hH hn
    (fun p => by
      obtain ⟨cd, hcd⟩ := exists_locGen_at p o.LamL.I
      choose cl hcl using fun j => exists_locGen_at p (L.ℓ j).I
      exact ⟨cd, cl, hcd, hcl, hloc p cd cl hcd hcl⟩) hsq
  have hTd : o.Tl.dual.Good := (degree_algebraic o.K₁ o.Tl o.Tl hT hT).2.2.1
  have hd := finrank_pos_real o.K₁
  refine ⟨hLam, hlg, hTd, hLa, hHad, hnd, le_of_eq ?_⟩
  simp only [MLine.ndeg]
  rw [hkey]
  field_simp

end GlobalTheory.ArcCM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsComplexArcDatumCmFibreStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complexArcDatum_cmFibre : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (B : GlobalTheory.CM.PAT H (Sp R)) (σR : R →+* ℂ), Formalism.L2.PjFree.GoodEmb c σ → IsUnf U → l.A = 1 → letI := H.starRing; ∀ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂) (ex : (Fin A.gB → ℂ) → (Over.mk (spMap σR) ⟶ B.t.G)), OnOrbit Uw k ξ' x A gam ξ → Module.finrank (𝓞 E) A.X = 1 → (∀ y y', (2 * l.M' : ℤ) ∣ A.be y y') → PrimAn H A → AbDat H A DB tyB eB → DB.p = Dw.p - 1 → DB.q = Dw.q - 1 → 1 ≤ Dw.p → 1 ≤ Dw.q → GlobalTheory.CM.IsExp B σR DB tyB (A.abelian₂.subtype.toAddMonoidHom.comp eB.toAddMonoidHom) ex → ∃ (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (Λ : GtAn aC) (hA : Λ.A = A) (φ : aC.D₀.P.A.left ⟶ B.pol.A.left), IsPolFibre σR B.pol aC.D₀.P φ ∧ (∀ a, (aC.oa.onB.act a).left ≫ φ = φ ≫ (B.t.act.act a).left) ∧ ∀ v, Λ.toGtAn₀.Lifts (aC.eta v) (cast (congrArg AnArc.La hA.symm) (gam (Uw.F.t (Uw.ik k) v))) := by
  first | exact @GlobalTheory.ArcCM.CxFibre.exists_arcIn_fibre | exact GlobalTheory.ArcCM.CxFibre.exists_arcIn_fibre | (intros; apply GlobalTheory.ArcCM.CxFibre.exists_arcIn_fibre <;> assumption)
end

