module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0259
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0261
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0170
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.UnfSectionNormBoundAtHeight
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlatOnModelExistsRulSections
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LineFunctionPlaceValuation
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LocalValuationLogNormsExistence
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0169
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0173
public import Development.WeilBound.CoreStatements.LocalModelCharts.ExistsLocalModelDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchIntegrableIffOverIntegers
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0153
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0152

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsConstSectionKroneckerChar
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br.CovEx

theorem exists_padic_emb (K : Type) [Field K] [NumberField K] (p : Nat.Primes) : Nonempty (K →+* ℂ_[p]) := by
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  exact ⟨(IsAlgClosed.lift (R := ℚ) (S := K) (M := ℂ_[p]) : K →ₐ[ℚ] ℂ_[p]).toRingHom⟩

theorem goodOf_or {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (σ : c.F →+* ℂ) : Formalism.L2.Pj.goodOf c σ = σ ∨ (starRingEnd ℂ).comp (Formalism.L2.Pj.goodOf c σ) = σ := by
  unfold Formalism.L2.Pj.goodOf
  split_ifs
  · exact Or.inl rfl
  · right; ext x; simp

theorem exists_constSec : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (r : ℕ)
    (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r) (x : ℝ), GlobalTheory.FlatCore.Laws U x → ∀ [NeZero H.d]
    (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (Z : Formalism.L2.Pj.Comp Xo c) (τ : GlobalTheory.AllWt.Psi H),
    ∃ s : GlobalTheory.FlatLine.ConstSec U x Z (GlobalTheory.FlatLine.flatWt D τ) 0,
      s.deg = ((D.p : ℝ) - D.q) / 2 * (GlobalTheory.CM.logOm E χ).re := by
  intro hR hG E _ _ _ H D l Xo c r U x hL _ χ hχ Z τ
  have hpos := hL.pos
  obtain ⟨κ⟩ := exists_padic_emb c.F (⟨2, Nat.prime_two⟩ : Nat.Primes)
  obtain ⟨O, _, _, _, β, Y, hβ, -, -, -⟩ :=
    _root_.PositivityTheory.Ar2.exists_local_model_dvr E H D l Xo c ⟨2, Nat.prime_two⟩ κ hpos (hL.good 2 Nat.prime_two)
  obtain ⟨hclopen, hcpt, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Br.cptOver_any E H D l Xo c (Z : Set (Xo.XF c)) Z.2
  obtain ⟨Z'⟩ := hcpt O β Y hβ
  have hgeom : Z'.IsGeom := GlobalTheory.T.geometric_component_alg_closed E H D l Xo c O β Y Z Z' hβ hL.geo
  obtain ⟨φ, hline, hflat, -⟩ := GlobalTheory.T.flat_zero_from_resolution_and_gaga hR hG E H D l Xo c O β Y Z Z' τ.1 hβ hpos τ.2 hgeom
  obtain ⟨hnorm, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.FlatFirstTheorem.flat_first_of_resolution_gaga hR hG E H D l Xo c O β Y Z Z' τ.1 φ hβ hpos τ.2 hgeom hline hflat
  choose t ht ht' using fun σ => hnorm (Formalism.L2.Pj.goodOf c σ)
  have hInf : ∀ σ, HasInfNorm (Z : Set (Xo.XF c)) τ.1 φ σ (t σ) := fun σ => by
    rcases goodOf_or c σ with h | h
    · have := ht σ
      rwa [h] at this
    · have := ht' σ
      rwa [h] at this
  have hFinEx : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm (Z : Set (Xo.XF c)) τ.1 φ p κ t :=
    fun p κ => _root_.GlobalTheory.CompanionTheory.Ar.Br.FinGood.finGood hR hG E H D l Xo c O β Y Z Z' τ.1 φ p κ hβ hpos τ.2 Z.2 hgeom hflat (hL.good p p.2)
  obtain ⟨ρ, hρ⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Br.FinPlace.exists_rho E H D l Xo c Z τ.1 φ hFinEx
  obtain ⟨hex, ⟨N, hNinf, hNfin⟩, hdict⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Br.Dd.deg_dict c.F (fun σ => Real.exp (t σ)) ρ
  have hinfN : ∀ s, HasInfNorm (Z : Set (Xo.XF c)) τ.1 φ s (N.inf s) := fun s => by
    rw [hNinf s, Real.log_exp]
    exact hInf s
  have hfinN : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), HasFinNorm (Z : Set (Xo.XF c)) τ.1 φ p κ (N.fin p κ) :=
    fun p κ => by
      obtain ⟨la, π, h1, h2⟩ := hex p κ
      rw [hNfin p κ la π h1 h2]
      exact hρ p κ la π h1 h2
  obtain ⟨hadel, hdeg⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Br.degree_of_flatOnModel hR hG E H D l Xo c O β Y _ Z' τ.1 φ N χ hχ hβ hpos τ.2 hclopen hgeom hflat
    hinfN hfinN
  obtain ⟨hsupp, hline'⟩ := hdict N hNinf hNfin
  obtain ⟨s, s', hs, hs', hi, hi', hm, hread⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Br.exists_flat_sec E H D l Xo c O β Y Z Z' τ φ hflat
  have hval := _root_.PositivityTheory.Xgn.line_function_place_valuation E H D l Xo c Z τ s φ ρ hline hread hρ
  have hPts := GlobalTheory.FlatLine.hasPts U hpos hL.good hL.unf Z
  refine ⟨{ sig := s, inv := s', sig_mem := hs, inv_mem := hs', idem_sig := hi, idem_inv := hi', mul_inv := hm,
            cInf := fun σ => Real.exp (t σ), cInf_pos := fun σ => Real.exp_pos _,
            norm_inf := fun σ => GlobalTheory.FlatLine.image_eq_singleton_iff.2 ⟨(hPts.1 σ).1, fun z hz =>
              _root_.GlobalTheory.CompanionTheory.Ar.Br.homN_eq_exp_hodge E H D l Xo c r (Formalism.L2.Pj.goodOf c σ) (U (Formalism.L2.Pj.goodOf c σ)) x Z τ s φ (t σ)
                (Formalism.L2.Pj.goodEmb_goodOf c σ) (hL.unf _ (Formalism.L2.Pj.goodEmb_goodOf c σ))
                (hL.xi _ (Formalism.L2.Pj.goodEmb_goodOf c σ)) hs hline hread (ht σ) z hz ((hPts.1 σ).2 z hz)⟩,
            rho_vw := ρ,
            val_fin := fun w => GlobalTheory.FlatLine.image_eq_singleton_iff.2 ⟨hPts.2 w, fun v hv => by
              simpa using hval w v hv⟩,
            finite_rho := hsupp.1 hadel }, ?_⟩
  exact (hline' hadel).symm.trans hdeg

end GlobalTheory.CompanionTheory.Ar.Br.CovEx
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ToZIsArithHeightIff
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem curveDeg_toZ {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} (t : X ⟶ Sp ℤ) {D : ℕ}
    (hX : IsArithVar p D) (L : HermLB p) (hL : ∀ τ, (wZ L t τ).IsCInf) (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegral Z] [IsLocallyNoetherian Z] (hc : CharZero Γ(Z, ⊤)) (hd : topologicalKrullDim Z = 1)
    (r : (L.restr i).B.ι → Z.functionFieldˣ) (hr : IsRatSec (L.restr i).B r) :
    HermLB.curveDeg ((toZ L t hL).restr i) (r := r) hr = HermLB.curveDeg (L.restr i) hr := by
  have hv : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hc (by simpa using hd)
  have e := _root_.GlobalTheory.CompanionTheory.Ar.BaseZ.sum_logNorm_curve k Z (i ≫ p) (i ≫ t) (Int.castRingHom ℂ) hv (L.restr i)
    (((toZ L t hL).restr i).φ (Int.castRingHom ℂ))
    (wOver_restr_pow k X Z p t i L hL _).1 r hr
  unfold HermLB.curveDeg
  refine congrArg (_ - ·) ?_
  rw [finsum_eq_single _ (Int.castRingHom ℂ) fun τ h => absurd (RingHom.ext_int _ _) h]
  exact e

theorem arch_toZ {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} (t : X ⟶ Sp ℤ) {D : ℕ}
    (hX : IsArithVar p D) (L : HermLB p) (hL : ∀ τ, (wZ L t τ).IsCInf) (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegral Z] (hc : CharZero Γ(Z, ⊤)) (e : ℕ) (hd : topologicalKrullDim Z = (e + 1 : ℕ)) (m : ℕ)
    (r : ((L.restr i).pow m).B.ι → Z.functionFieldˣ) (hr : IsRatSec ((L.restr i).pow m).B r) :
    (HermLB.ArchIntegrable ((toZ L t hL).restr i) ((toZ L t hL).restr i |>.pow m) (r := r) e hr ↔
      HermLB.ArchIntegrable (L.restr i) ((L.restr i).pow m) e hr) ∧
    (HermLB.ArchIntegrable (L.restr i) ((L.restr i).pow m) e hr →
      HermLB.archInt ((toZ L t hL).restr i) ((toZ L t hL).restr i |>.pow m) (r := r) e hr =
        HermLB.archInt (L.restr i) ((L.restr i).pow m) e hr) := by
  have hv : IsArithVar (i ≫ p) e := hX.of_isClosedImmersion i hc hd
  have hw := wOver_restr_pow k X Z p t i L hL (Int.castRingHom ℂ)
  obtain ⟨e₁, e₂⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BaseZ.archInt_over_int k Z (i ≫ p) (i ≫ t) (Int.castRingHom ℂ) e hv (L.restr i)
    ((L.restr i).pow m) (((toZ L t hL).restr i).φ (Int.castRingHom ℂ))
    ((((toZ L t hL).restr i).pow m).φ (Int.castRingHom ℂ)) hw.1 (hw.2 m)
    (((toZ L t hL).restr i).cInf _) e r hr
  have hτ (τ : ℤ →+* ℂ) : τ = Int.castRingHom ℂ := RingHom.ext_int _ _
  refine ⟨⟨fun H => e₁.1 (H _), fun H τ => ?_⟩, fun H => ?_⟩
  · rw [hτ τ]
    exact e₁.2 H
  · unfold HermLB.archInt
    rw [finsum_eq_single _ (Int.castRingHom ℂ) fun τ h => absurd (hτ τ) h]
    exact e₂ H

theorem isArithHeight_toZ_iff : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (hL : ∀ τ, (wZ L t τ).IsCInf) (h : X → ℝ), (toZ L t hL).IsArithHeight h ↔ L.IsArithHeight h := by
  intro k _ X p t D hX L hL h
  refine ⟨fun H => ⟨H.vertical, ?_, ?_⟩, fun H => ⟨H.vertical, ?_, ?_⟩⟩
  · intro Z i _ _ _ hc hd r hr
    exact (H.point Z i hc hd r hr).trans (curveDeg_toZ t hX L hL i hc hd r hr)
  · intro Z i _ _ _ hc e he hd m r hr
    obtain ⟨e₁, e₂⟩ := arch_toZ t hX L hL i hc e hd m r hr
    obtain ⟨h₁, h₂⟩ := H.recursion Z i hc e he hd m r hr
    have h₃ := e₁.1 h₁
    exact ⟨h₃, h₂.trans (congrArg (_ - ·) (e₂ h₃))⟩
  · intro Z i _ _ _ hc hd r hr
    exact (H.point Z i hc hd r hr).trans (curveDeg_toZ t hX L hL i hc hd r hr).symm
  · intro Z i _ _ _ hc e he hd m r hr
    obtain ⟨e₁, e₂⟩ := arch_toZ t hX L hL i hc e hd m r hr
    obtain ⟨h₁, h₂⟩ := H.recursion Z i hc e he hd m r hr
    exact ⟨e₁.2 h₁, h₂.trans (congrArg (_ - ·) (e₂ h₁).symm)⟩

end GlobalTheory.CompanionTheory.Ar.BaseZ
end
end

