module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0253
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0155
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchIntToZEq
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0154
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0035

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArFormExistsOfInt
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem arFormExists_of_int :
    (∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℤ) (D : ℕ), IsArithVar p D →
      ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p), ∃ Φ, IsArFun L D Φ) → GlobalTheory.Published.ArFormExists := by
  intro H k _ X _ p D hX ι _ L
  let t : X ⟶ Sp ℤ := specZIsTerminal.from X
  haveI : Module.Finite ℤ k := hX.finite
  have hL : ∀ i τ, (wZ (L i) t τ).IsCInf := fun i τ => _root_.GlobalTheory.CompanionTheory.Ar.BaseZ.wZ_isCInf k X p t (L i) τ
  obtain ⟨Φ, hΦ⟩ := H X t D (GlobalTheory.CompanionTheory.Ar.BaseZ.isArithVar_int k X p t D hX) ι
    (fun i => GlobalTheory.CompanionTheory.Ar.BaseZ.toZ (L i) t (hL i))
  exact ⟨Φ, (_root_.GlobalTheory.CompanionTheory.Ar.BaseZ.isArFun_toZ_iff k X p t D hX ι L hL Φ).1 hΦ⟩

end GlobalTheory.CompanionTheory.Ar.BaseZ
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArMixOfBaseInt
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem arMix_of_base_int : (∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℤ) (D : ℕ), IsArithVar p D → ∀ (ι : Type) [Fintype ι] (M : HermLB p) (L : ι → HermLB p) (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ), IsArFun (fun o : Option ι => o.elim M L) D Φ → ∀ (n : ι → ℤ) (h : X → ℝ), (comb L n).IsArithHeight h → ∀ (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), (comb L n).ArchIntegrable M D hr ∧ Φ (MvPolynomial.X none * MvPolynomial.rename some (lin fun i => (n i : ℝ)) ^ D) = ∑ᶠ z, ((M.div hr).mult z : ℝ) * h z - (comb L n).archInt M D hr) → GlobalTheory.Published.ArMix := by
  intro H k _ X _ _ p D hX ι _ M L Φ hΦ n h hh r hr
  haveI := hX.finite
  let t : X ⟶ Sp ℤ := p ≫ spMap (Int.castRingHom k)
  have hX' : IsArithVar t D := isArithVar_int k X p t D hX
  have Hc : ∀ (N : HermLB p) (τ : ℤ →+* ℂ), (wZ N t τ).IsCInf := fun N τ => _root_.GlobalTheory.CompanionTheory.Ar.BaseZ.wZ_isCInf k X p t N τ
  have hΦ' : IsArFun (fun o : Option ι => o.elim (toZ M t (Hc M)) fun i => toZ (L i) t (Hc (L i))) D Φ := by
    have e := (_root_.GlobalTheory.CompanionTheory.Ar.BaseZ.isArFun_toZ_iff k X p t D hX (Option ι) (fun o : Option ι => o.elim M L)
      (fun o => Hc _) Φ).2 hΦ
    convert e using 2 with o
    cases o <;> rfl
  have iso : (toZ (comb L n) t (Hc _)).Isometric (comb (fun i => toZ (L i) t (Hc (L i))) n) :=
    (_root_.GlobalTheory.CompanionTheory.Ar.BaseZ.toZ_pow_comb k X p t Hc).2 ι L n
  have hh' : (comb (fun i => toZ (L i) t (Hc (L i))) n).IsArithHeight h :=
    iso.isArithHeight hX' ((_root_.GlobalTheory.CompanionTheory.Ar.BaseZ.isArithHeight_toZ_iff k X p t D hX (comb L n) (Hc _) h).2 hh)
  obtain ⟨h₁, h₂⟩ := H X t D hX' ι (toZ M t (Hc M)) (fun i => toZ (L i) t (Hc (L i))) Φ hΦ' n h hh' r hr
  have hA : (toZ (comb L n) t (Hc _)).ArchIntegrable (toZ M t (Hc M)) D hr := fun τ => by
    rw [iso.chernIntegrableOn_eq]
    exact h₁ τ
  have hI : (comb (fun i => toZ (L i) t (Hc (L i))) n).archInt (toZ M t (Hc M)) D hr =
      (toZ (comb L n) t (Hc _)).archInt (toZ M t (Hc M)) D hr := by
    simp only [HermLB.archInt, iso.chernInt_eq]
  obtain ⟨e₁, e₂⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BaseZ.archInt_toZ k X p t D hX (comb L n) M (Hc _) (Hc _) D r hr
  have hB := e₁.1 hA
  refine ⟨hB, h₂.trans ?_⟩
  rw [hI, e₂ hB]
  rfl

end GlobalTheory.CompanionTheory.Ar.BaseZ
end

