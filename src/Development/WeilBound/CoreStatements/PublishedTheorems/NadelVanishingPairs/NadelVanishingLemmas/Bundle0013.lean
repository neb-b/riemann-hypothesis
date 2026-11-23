module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfAcyclic
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SubsingletonOfSheafPullback
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0023
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0001
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechTwistNonzeroLocusMaps
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2080
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2112
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2073

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CohomologyVanishingNonzeroLocus
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false
noncomputable section
namespace GlobalTheory

theorem isZero_cechH_nonzeroLocus_of_eventually_twist : ∀ (X : Scheme.{0}) (F : X.Modules) [F.IsQuasicoherent] (L : LB X), L.IsLB → ∀ (σ : L.Sec)
    {ι : Type} [LinearOrder ι] [Fintype ι] (U : ι → X.Opens),
    (∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) → ∀ n : ℕ,
    (∀ᶠ c : ℕ in atTop, IsZero (cechH ℤ (twistZ F L c) ⊤ U n)) → IsZero (cechH ℤ F (nonzeroLocus σ) U n) := by
  intro X F _ L hL σ ι _ _ U hU n h
  obtain ⟨μ, ρ, h₁, h₂, h₃, h₄⟩ := GlobalTheory.T.cech_twist_nonzero_locus_maps X F L hL σ U hU
  exact GlobalTheory.T.cech_complex_direct_limit (fun c => cechCube ℤ (twistZ F L c) ⊤ U) (cechCube ℤ F (nonzeroLocus σ) U) μ ρ h₁ h₂ h₃ h₄ n h

theorem subsingleton_cohOn_nonzeroLocus_of_eventually_twist : ∀ (X : Scheme.{0}) [CompactSpace X] [X.IsSeparated] (F : X.Modules) [F.IsQuasicoherent] (L : LB X), L.IsLB → ∀ (σ : L.Sec) (i : ℕ), (∀ᶠ c : ℕ in atTop, Subsingleton (coh (twist F (lbPow L c)) i)) → Subsingleton (cohOn F (nonzeroLocus σ) i) := by
  intro X _ _ F _ L hL σ i h
  obtain ⟨κ, hκ, T, c, hT, -, hTc, hcov⟩ :=
    Twist.exists_finite_affine_chart_cover hL (W := ⊤) (isCompact_univ (X := X))
  letI : Fintype κ := Fintype.ofFinite κ
  letI : LinearOrder κ := LinearOrder.lift' (Fintype.equivFin κ) (Fintype.equivFin κ).injective
  have hsep : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ a ∈ s, T a) :=
    (cech_computes_coh_of_affine_cover.{0, 0, 0} X ℤ).1 (Or.inl inferInstance) κ T hT
  have hc : ⨆ a, T a = ⊤ := eq_top_iff.2 hcov
  have hV : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (cechOpen (nonzeroLocus σ) T s) := by
    rintro s ⟨a, ha⟩
    have hle : ⨅ b ∈ s, T b ≤ L.U (c a) := (biInf_le T ha).trans (hTc a)
    have e := Twist.basicOpen_resG_zfun (Twist.zofSec σ) (c a) hle
    rw [Twist.nonzeroLocus_zofSec hL] at e
    have e' : cechOpen (nonzeroLocus σ) T s = X.basicOpen (resG X hle (Twist.zfun (Twist.zofSec σ) (c a))) := by
      rw [e, cechOpen, inf_comm]
    rw [e']
    exact (hsep s ⟨a, ha⟩).basicOpen _
  have hVc : nonzeroLocus σ ≤ ⨆ a, T a := hc ▸ le_top
  have eV := cechHEquivCohOn ℤ hVc (cechAcyclicMod_of_isAffineOpen hV F) i
  have hZ : IsZero (cechH ℤ F (nonzeroLocus σ) T i) := by
    refine isZero_cechH_nonzeroLocus_of_eventually_twist X F L hL σ T hsep i (h.mono fun k hk => ?_)
    haveI hq : (twistZ F L k).IsQuasicoherent := Twist.isQuasicoherent_twist (Twist.isLB_lbZPow hL k)
    have e2 := cechHEquivCoh ℤ hc hsep (twistZ F L k) i
    haveI : Subsingleton (coh (twistZ F L k) i) := by rw [Twist.twistZ_natCast]; exact hk
    haveI : Subsingleton (cechH ℤ (twistZ F L k) ⊤ T i) := e2.injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  haveI : Subsingleton (cechH ℤ F (nonzeroLocus σ) T i) := ModuleCat.subsingleton_of_isZero hZ
  exact eV.symm.injective.subsingleton

end GlobalTheory
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FinrankKaehlerResidueField
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.finrank_kaehler_residue_field : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d f] (U : X.Opens) (x : X) (hxU : x ∈ U), IsAffineOpen U → letI : Algebra k Γ(X, U) := (cstOn f U).toAlgebra; letI : Algebra Γ(X, U) (IsLocalRing.ResidueField (X.presheaf.stalk x)) := ((IsLocalRing.residue (X.presheaf.stalk x)).comp (X.presheaf.germ U x hxU).hom).toAlgebra; Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x)) (IsLocalRing.ResidueField (X.presheaf.stalk x) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄k]) = d := by
  first | exact @_root_.GlobalTheory.SmoothStalk.finrank_residue_kaehler | exact _root_.GlobalTheory.SmoothStalk.finrank_residue_kaehler | (intros; apply _root_.GlobalTheory.SmoothStalk.finrank_residue_kaehler <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RootOfMonomialQuotientIntegral
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.root_of_monomial_quotient_integral : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ (P : Ideal A) [P.IsPrime] (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] (S : Finset (Fin n)) (g : L) (m : ℕ), 0 < m → (∃ a b : A, b ∉ P ∧ g ^ m / algebraMap A L (∏ j ∈ S, t j) * algebraMap A L b = algebraMap A L a) → ∃ a b : A, b ∉ P ∧ g / algebraMap A L (∏ j ∈ S, t j) * algebraMap A L b = algebraMap A L a := by
  first | exact @_root_.GlobalTheory.EtRoot.div_prod_coords_mem_of_pow | exact _root_.GlobalTheory.EtRoot.div_prod_coords_mem_of_pow | (intros; apply _root_.GlobalTheory.EtRoot.div_prod_coords_mem_of_pow <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutSmoothProper
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem exists_finiteType_subring_ge_finset {k : Type} [CommRing k] (R₀ : Subring k)
    (h : Algebra.FiniteType ℤ R₀) (F : Finset k) :
    ∃ R : Subring k, R₀ ≤ R ∧ (F : Set k) ⊆ R ∧ Algebra.FiniteType ℤ R := by
  have h0 : (subalgebraOfSubring R₀).FG := (Subalgebra.fg_iff_finiteType _).2 h
  have h1 : (subalgebraOfSubring R₀ ⊔ Algebra.adjoin ℤ (F : Set k)).FG :=
    h0.sup (Subalgebra.fg_adjoin_finset F)
  refine ⟨(subalgebraOfSubring R₀ ⊔ Algebra.adjoin ℤ (F : Set k)).toSubring, ?_, ?_,
    (Subalgebra.fg_iff_finiteType _).1 h1⟩
  · intro x hx
    exact (le_sup_left : subalgebraOfSubring R₀ ≤ _) hx
  · intro x hx
    exact (le_sup_right : Algebra.adjoin ℤ (F : Set k) ≤ _) (Algebra.subset_adjoin hx)

theorem exists_model_with_sections : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k), Smooth f → IsProper f → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : ∀ i, (L i).IsLB) (M : LB X) (hM : M.IsLB), ∃ (R : Subring k) (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R) (π : X ⟶ X₁) (L₁ : Fin s → LB X₁) (σ₁ : ∀ i, (L₁ i).Sec) (h₁ : ∀ i, (L₁ i).IsLB) (M₁ : LB X₁) (hM₁ : M₁.IsLB), Algebra.FiniteType ℤ R ∧ Smooth f₁ ∧ IsProper f₁ ∧ IsPullback π f f₁ (spMap R.subtype) ∧ (∀ i, cls (L i) (h i) = CechPic.pull π (cls (L₁ i) (h₁ i))) ∧ (∀ i, SameDiv (σ i) (Cartier.secPull (σ₁ i) π)) ∧ cls M hM = CechPic.pull π (cls M₁ hM₁) := by
  classical
  intro k _ X f hsm hpr s L σ h M hM
  obtain ⟨R₀, X₀, f₀, π₀, hft, hsm₀, hpr₀, hpb⟩ := _root_.GlobalTheory.SmoothProperModel.exists_smooth_proper_model k X f hsm hpr
  choose F hF using fun i => GlobalTheory.T.spread_out_line_bundle_section k R₀ X X₀ f f₀ π₀ (L i) (h i) (σ i) hpb
  obtain ⟨G, hG⟩ := GlobalTheory.T.spread_out_line_bundle_section k R₀ X X₀ f f₀ π₀ M hM 0 hpb
  obtain ⟨R, hR, hFR, hRft⟩ :=
    exists_finiteType_subring_ge_finset R₀ hft (G ∪ Finset.univ.biUnion F)
  have hsp : spMap R.subtype ≫ spMap (Subring.inclusion hR) = spMap R₀.subtype := by
    simp only [spMap]
    rw [← Spec.map_comp]
    rfl
  have P := IsPullback.of_hasPullback f₀ (spMap (Subring.inclusion hR))
  let j : X ⟶ pullback f₀ (spMap (Subring.inclusion hR)) :=
    pullback.lift π₀ (f ≫ spMap R.subtype) (by rw [Category.assoc, hsp, hpb.w])
  have hj1 : j ≫ pullback.fst _ _ = π₀ := pullback.lift_fst _ _ _
  have hj2 : j ≫ pullback.snd _ _ = f ≫ spMap R.subtype := pullback.lift_snd _ _ _
  have hGR : (G : Set k) ⊆ R := fun x hx => hFR (by
    simp only [Finset.coe_union, Set.mem_union]; exact Or.inl hx)
  have hFi : ∀ i, (F i : Set k) ⊆ R := fun i x hx => hFR (by
    rw [Finset.mem_coe, Finset.mem_union]
    exact Or.inr (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hx⟩))
  choose L₁ h₁ σ₁ hc hd using fun i => hF i R hR (hFi i) _ _ _ j P hj1 hj2
  obtain ⟨M₁, hM₁, -, hMc, -⟩ := hG R hR hGR _ _ _ j P hj1 hj2
  refine ⟨R, _, pullback.snd f₀ (spMap (Subring.inclusion hR)), j, L₁, σ₁, h₁, M₁, hM₁, hRft,
    inferInstance, inferInstance, ?_, hc, hd, hMc⟩
  exact IsPullback.of_right (by rw [hj1, hsp]; exact hpb) hj2 P

end GlobalTheory.LogPair
end

