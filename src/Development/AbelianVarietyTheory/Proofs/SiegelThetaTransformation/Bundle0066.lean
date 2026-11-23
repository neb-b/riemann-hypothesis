module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsVanishingOffFramesLeSpanShortTheta
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0061
public import Formalism.LocalToGlobal.ProjectiveLattices.HostSize

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsLeSpanShortThetaSeries
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory

theorem mem_span_of_map_mem_span_image {K : Type*} [Field K] {σ : K →+* ℂ} {C : Type*} [AddCommGroup C]
    [Module K C] {W : Type*} [AddCommGroup W] [Module ℂ W] (j : C →ₛₗ[σ] W) (V : Submodule K C)
    (hj : ∀ (m : ℕ) (b : Fin m → C), (∀ i, b i ∈ V) → LinearIndependent K b →
      LinearIndependent ℂ (fun i => j (b i)))
    (S : Set C) (hS : S ⊆ V) {f : C} (hf : f ∈ V) (hjf : j f ∈ Submodule.span ℂ (j '' S)) :
    f ∈ Submodule.span K S := by
  let V' : Submodule K C := V ⊓ (Submodule.span ℂ (j '' S)).comap j
  have hSV : S ⊆ V' := fun s hs => ⟨hS hs, Submodule.subset_span ⟨s, hs, rfl⟩⟩
  have hind : ReciprocityTheory.ChartRestriction.G.PullbackSections.IndepToC (j.domRestrict V') := by
    intro m b hb
    exact hj m (fun i => (b i : C)) (fun i => (b i).2.1) (hb.map' V'.subtype (Submodule.ker_subtype V'))
  have himg : (j.domRestrict V') '' (V'.subtype ⁻¹' S) = j '' S := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hSV hx⟩, hx, rfl⟩
  have htop := ReciprocityTheory.ChartRestriction.G.PullbackSections.span_eq_top_of_indepToC (j.domRestrict V') hind (V'.subtype ⁻¹' S)
    (fun g => by rw [himg]; exact g.2.2)
  have h1 : (⟨f, hf, hjf⟩ : V') ∈ Submodule.span K (V'.subtype ⁻¹' S) := by
    rw [htop]; exact Submodule.mem_top
  have h2 := Submodule.mem_map_of_mem (f := V'.subtype) h1
  rw [Submodule.map_span] at h2
  exact Submodule.span_mono (Set.image_preimage_subset _ _) h2

theorem cusp_le_span_shortGen : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (σ : c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ) → 1 ≤ r → l.A = 1 → (∀ k k', ((U σ).X k).Gm = ((U σ).X k').Gm ∧ ((U σ).X k).ξ0 = ((U σ).X k').ξ0) → (∀ k, HasPrinc ((U σ).X k) l.M) → (∀ a n, Dom a n → ∀ k, ChiOne ((U σ).X k) (Formalism.L2.PjFree.laU (U σ) a n k)) → ∀ (nab : NabV Xo c) (bad nV : ℕ) (dδ : ∀ n, DeltaDat Xo c n), 0 < bad → (∀ n, (dδ n).IsLev ∧ (∃ _ : StarRing (𝓞 E), IsNab (dδ n).Xo₂ (dδ n).c₂ (dδ n).nab₂) ∧ UnitC (dδ n) ∧ ¬ 3 ∣ (dδ n).pd ∧ (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, (dδ n).PhiPin ph ψ x₀) ∧ ∀ a, Dom a n → ShortValTot Xo c nab bad nV a n (dδ n)) → SpanningAtDominantWeight Xo c nab bad nV (Formalism.L2.PjFree.cusp Xo c U) dδ := by
  intro hC E _ _ _ H Dw l Xo c r U σ hσ hU hr hA hG hP hχ nab bad nV dδ hbad hd a n hDom _ hn f hf
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hd n
  have hrk : 4 * (Module.finrank ℚ E * r) + 4 ≤ n := by
    have he : Module.finrank ℚ E = 2 * NumberField.InfinitePlace.nrComplexPlaces E :=
      NumberField.IsTotallyComplex.finrank E
    have hr' : r = Dw.p + Dw.q := hU.1
    rw [he, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), ← hr'] at hn
    rw [he]
    calc 4 * (2 * NumberField.InfinitePlace.nrComplexPlaces E * r) + 4
        = 8 * NumberField.InfinitePlace.nrComplexPlaces E * r + 4 := by ring
      _ ≤ n := hn
  have hsp := GlobalTheory.Dict.holSub0_le_span_shortGen hC E H Dw l Xo c n (dδ n) σ r (U σ) hσ hU hr hA hG hP h1 h2 h3 h4 h5 nab bad nV a
    hbad hDom hrk (hχ a n hDom) (h6 a hDom)
  have hf' := (Formalism.L2.PjFree.mem_cusp Xo c U a n f).1 hf
  have hind := (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c σ r
    (U σ) hU a n).1
  refine mem_span_of_map_mem_span_image (Formalism.L2.PjFree.rdU (U σ)) (sec Xo c a n) hind (shortGen Xo c nab bad nV a n (dδ n)) (fun g hg => hg.1) hf'.1 (hsp ?_)
  refine ⟨hf'.2 σ hσ, fun k x hx => ?_⟩
  exact dif_neg hx

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HolomorphicCuspFormsFramesLeSpanShortThetaReadin
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.Dict

theorem sig_add_of_pins {D : D7} (Q : Par D) (h : Q.Pins) {j : ℕ} (hj : InR D j) :
    (Q.Dw j).p + (Q.Dw j).q = D.R.r := by
  obtain ⟨-, -, -, h4⟩ := h
  obtain ⟨hp, hq, -⟩ := h4 j hj
  rw [hp, hq]
  obtain ⟨h1, h2⟩ := hj
  simp only [Formalism.BasicNotions.Ranks.sigW, Formalism.BasicNotions.Ranks.r]
  omega

private theorem dom_wtA_of_wt {D : D7} {j : ℕ} (ka : WeightFamilies.Wt D j) : Dom (wtA ka) ka.n := by
  unfold Dom wtA
  refine ⟨fun τ => ?_, ka.n_even⟩
  intro a b hab
  apply Finset.sum_le_sum
  intro t _
  apply add_le_add
  · split_ifs with h
    · unfold Formalism.L2.Pj.ext0
      split_ifs with h1 h2 <;> first | omega | exact Nat.zero_le _ | exact le_refl _ | exact ka.aPlus_antitone t (Fin.mk_le_mk.2 hab)
    · exact le_refl _
  · split_ifs with h
    · unfold Formalism.L2.Pj.ext0
      split_ifs with h1 h2 <;> first | omega | exact Nat.zero_le _ | exact le_refl _ | exact ka.aM_anti t (Fin.mk_le_mk.2 hab)
    · exact le_refl _

private theorem par_l_A_eq_one_of_pins {D : D7} (Q : Par D) (h : Q.Pins) : Q.l.A = 1 := by
  obtain ⟨-, hL, -⟩ := h
  unfold Par.PinLevel at hL
  exact hL.2

theorem holSub0_le_span_short_rec : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D), LawsM T.toCore → LawsSh T → GamAt T.toCore → 0 < badN D → (∀ j, InR D j → ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧ ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0) → ∀ (j : ℕ) (_hj : InR D j) (ka : WeightFamilies.Wt D j), 8 * D.R.f * D.R.r + 4 ≤ ka.n → GlobalTheory.Dict.holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA ka) ka.n) ≤ Submodule.span ℂ (rdU (T.U j T.σ₀) '' T.sh j ka) := by
  intro hC D T hM hSh hG hb hX j hj ka hn
  obtain ⟨-, dLev, dNab, dPd, dPhi, dRoot, shTot, -, -⟩ := hSh
  have hgood : GoodEmb T.Q.c T.σ₀ := T.toCore.good_σ₀
  have hpq : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := sig_add_of_pins T.Q hM.pins hj
  have hr1 : 1 ≤ D.R.r := by
    have := D.R.m_add_three_le_k
    simp only [Formalism.BasicNotions.Ranks.r]
    omega
  have hDom : Dom (wtA ka) ka.n := dom_wtA_of_wt ka
  have hl : T.Q.l.A = 1 := par_l_A_eq_one_of_pins T.Q hM.pins
  have hn' : 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ ka.n := by
    rw [hostSize_finrank D]
    calc 4 * (2 * D.R.f * D.R.r) + 4 = 8 * D.R.f * D.R.r + 4 := by ring
      _ ≤ ka.n := hn
  have hP3 : ¬ 3 ∣ (T.dδ j ka.n).pd := by
    obtain ⟨p, hp, hpd⟩ := dPd
    rw [hpd j hj ka.n]
    have h15 := D.host.pde_mod
    rcases hp with rfl | rfl <;> omega
  have hUnit : UnitC (T.dδ j ka.n) := by
    obtain ⟨Cls, x, hF, δ, gdet, hCMP⟩ := dRoot j hj ka.n
    exact unitC_of_finite_character _ _ _ _ _ _ _ _ Cls δ gdet (by rw [hpq]; exact hr1) hCMP
  have hPhi : (T.Q.Dw j).p + (T.Q.Dw j).q ≤ ka.n → ∃ ph ψ x₀, (T.dδ j ka.n).PhiPin ph ψ x₀ := by
    intro h
    obtain ⟨ph, ψ, x₀, -, hph, -⟩ := dPhi j hj ka.n (hpq ▸ h)
    exact ⟨ph, ψ, x₀, hph⟩
  have hPr : ∀ k, HasPrinc ((T.U j T.σ₀).X k) T.Q.l.M := by
    intro k ga hga hcong
    apply hG j hj T.σ₀ hgood k ga hga
    intro x hx
    obtain ⟨u, hu, he⟩ := hcong x hx
    refine ⟨u, hu, ?_⟩
    rw [he, Nat.cast_smul_eq_nsmul]
    abel
  have hChi : ∀ k, ChiOne ((Formalism.L2.PjFree.Unf.ofPj (T.U j T.σ₀)).X k)
      (Formalism.L2.PjFree.laU (Formalism.L2.PjFree.Unf.ofPj (T.U j T.σ₀)) (wtA ka) ka.n k) := by
    intro k γ hγ
    erw [Formalism.L2.PjFree.laU_ofPj]
    exact hM.chiTriv j hj T.σ₀ hgood _ _ hDom k γ hγ
  have key := _root_.GlobalTheory.Dict.holSub0_le_span_shortGen hC _ _ _ _ (T.Q.Xo j) T.Q.c ka.n (T.dδ j ka.n) T.σ₀ D.R.r
    (Formalism.L2.PjFree.Unf.ofPj (T.U j T.σ₀)) ((Formalism.L2.PjFree.goodEmb_iff _).2 hgood)
    ((Formalism.L2.PjFree.isUnf_ofPj _).2 (hM.unf j hj _ hgood)) hr1 hl (hX j hj) hPr (dLev j hj ka.n)
    (dNab j hj ka.n) hUnit hP3 hPhi (T.nab j) (badN D) D.R.nV (wtA ka) hb hDom hn' hChi (shTot j hj _ _ hDom)
  convert key using 3 <;> rfl

end GlobalTheory.Dict
end

