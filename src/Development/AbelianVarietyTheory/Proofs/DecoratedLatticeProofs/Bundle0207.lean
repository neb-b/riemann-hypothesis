module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0090
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmZeroRat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LiftSumProof

variable {D : D7}

theorem om_zero_rat {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hω : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : GA D S} (hγ : γ ∈ GQ S)
    {γ' : GA D T} (hγ' : γ' ∈ GQ T) (g : GA D S) (h : GA D T) : om (γ * g, γ' * h) f 0 = om (g, h) f 0 := by
  have e : ((γ * g, γ' * h) : GA D S × GA D T) = (γ, γ') * (g, h) := rfl
  rw [e, map_mul, Module.End.mul_apply]
  exact hω.om_aut γ hγ γ' hγ' _ (hω.om_pres _ _ hf)

theorem liftSum : ∀ D : D7, LiftSum D := by
  intro D ψ θ hθ S T x y hx hy k hk P
  obtain ⟨χS, χT, hω⟩ := hk.weil
  have hψ : IsStdChar D ψ (-1) := hk.vac.1
  have hvac : IsThetaFunO ψ S T k.vac := hk.vac.2.theta
  have hcomb : IsThetaFunO ψ S T (comb ψ S T k.c k.vac) :=
    GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ.1 k.vac hvac (WO S T) k.c.support id k.c (fun u hu => hk.fin u hu)
  have hpt : IsThetaFunO ψ S T (k.pt ψ θ x y P) :=
    GlobalTheory.FockTheta.ptStable D ψ θ hψ hθ S T x.s y.s x.B y.B _ P hcomb

  have key : ∀ φ : GA D S → ℂ, IsContAut S φ →
      (∀ h, IntegrableOn (fun g => k.om (g, h) (k.pt ψ θ x y P) 0 * φ g) x.vol.𝓕 x.vol.μ) ∧
      Continuous fun h => ∫ g in x.vol.𝓕, k.om (g, h) (k.pt ψ θ x y P) 0 * φ g ∂x.vol.μ := by
    intro φ hφ
    have hc : Continuous (Function.uncurry fun (g : GA D S) (h : GA D T) => k.om (g, h) (k.pt ψ θ x y P) 0 * φ g) :=
      (hω.om_cont _ hpt 0).mul (hφ.2.comp continuous_fst)
    have hinv : ∀ γ ∈ GQ S, ∀ (g : GA D S) (h : GA D T),
        k.om (γ * g, h) (k.pt ψ θ x y P) 0 * φ (γ * g) = k.om (g, h) (k.pt ψ θ x y P) 0 * φ g := by
      intro γ hγ g h
      have e := om_zero_rat hω hpt hγ (one_mem (GQ T)) g h
      rw [one_mul] at e
      rw [e, hφ.1 γ hγ g]
    obtain ⟨h1, h2, -⟩ := _root_.GlobalTheory.CocompactParam.continuous_integral_param D S hx.cpt x.vol (GA D T) _ hc hinv
    exact ⟨h1, h2⟩
  refine ⟨hpt, fun φ hφ => ⟨fun γ' hγ' h => ?_, ?_⟩, fun I s a φ hφ => ?_⟩
  · show ∫ g in x.vol.𝓕, k.om (g, γ' * h) (k.pt ψ θ x y P) 0 * φ g ∂x.vol.μ =
      ∫ g in x.vol.𝓕, k.om (g, h) (k.pt ψ θ x y P) 0 * φ g ∂x.vol.μ
    congr 1
    funext g
    have e := om_zero_rat hω hpt (one_mem (GQ S)) hγ' g h
    rw [one_mul] at e
    rw [e]
  · exact (key φ hφ).2
  · funext h
    show ∫ g in x.vol.𝓕, k.om (g, h) (k.pt ψ θ x y P) 0 * (∑ i ∈ s, a i • φ i) g ∂x.vol.μ =
      (∑ i ∈ s, a i • fun h' => ∫ g in x.vol.𝓕, k.om (g, h') (k.pt ψ θ x y P) 0 * φ i g ∂x.vol.μ) h
    rw [Finset.sum_apply]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    have e : (fun g => ∑ i ∈ s, k.om (g, h) (k.pt ψ θ x y P) 0 * (a i * φ i g)) =
        fun g => ∑ i ∈ s, a i * (k.om (g, h) (k.pt ψ θ x y P) 0 * φ i g) := by
      funext g
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, integral_finsetSum s (fun i hi => ((key (φ i) (hφ i hi)).1 h).const_mul (a i))]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul (a i) _

end GlobalTheory.SeeSaw.LiftSumProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthAllHeisenbergTranslatesOfOrthRealLatticeVacu
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinOrth

variable {D : D7} {S T : HSp D}

theorem setIntegral_add_right {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure (WO S T))
    [μ.IsAddHaarMeasure] {𝓕 : Set (WO S T)} (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {g : WO S T → E}
    (hg : ∀ γ ∈ ratL T S, ∀ w, g (γ + w) = g w) (u : WO S T) :
    ∫ w in 𝓕, g (w + u) ∂μ = ∫ w in 𝓕, g w ∂μ := by
  have i6 : BorelSpace (WO S T) := ⟨rfl⟩
  have : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  have : Countable (Matrix (Fin T.rank) (Fin S.rank) D.host.E) :=
    inferInstanceAs (Countable (Fin T.rank → Fin S.rank → D.host.E))
  have : Countable (ratL T S) := (Set.countable_range _).to_subtype
  have : MeasurableConstVAdd (ratL T S) (WO S T) := ⟨fun c => (continuous_const.add continuous_id).measurable⟩
  have : VAddInvariantMeasure (ratL T S) (WO S T) μ := ⟨fun c s _ => measure_preimage_add μ (c : WO S T) s⟩
  have hmp : MeasurePreserving (fun w : WO S T => u + w) μ μ := measurePreserving_add_left μ u
  have hemb : MeasurableEmbedding (fun w : WO S T => u + w) := (MeasurableEquiv.addLeft u).measurableEmbedding
  have hpre : 𝓕 = (fun w : WO S T => u + w) ⁻¹' ((fun w : WO S T => -u + w) ⁻¹' 𝓕) := by
    ext w; simp
  have h𝓕' : IsAddFundamentalDomain (ratL T S) ((fun w : WO S T => -u + w) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv (measurePreserving_add_left μ (-u)).quasiMeasurePreserving
      (e := id) Function.bijective_id fun γ w => ?_
    simp only [id, AddSubgroup.vadd_def, vadd_eq_add]
    abel
  have e1 : ∫ w in 𝓕, g (w + u) ∂μ = ∫ w in (fun w : WO S T => u + w) ⁻¹' ((fun w : WO S T => -u + w) ⁻¹' 𝓕),
      g (u + w) ∂μ := by
    rw [← hpre]; simp_rw [add_comm _ u]
  rw [e1, hmp.setIntegral_preimage_emb hemb]
  exact h𝓕'.setIntegral_eq h𝓕 fun γ w => by rw [AddSubgroup.vadd_def, vadd_eq_add]; exact hg γ γ.2 w

theorem star_mul_self_psi {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1) (a : AF D.host.F) :
    star (ψ a) * ψ a = 1 := by
  rw [Complex.star_def, Complex.conj_mul', hn]; simp

theorem thPair_heisO {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1) (μ : Measure (WO S T))
    [μ.IsAddHaarMeasure] {𝓕 : Set (WO S T)} (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) (u : WO S T) :
    thPair μ 𝓕 (heisO ψ S T u f) (heisO ψ S T u g) = thPair μ 𝓕 f g := by
  have hs := star_mul_self_psi hn
  unfold thPair
  have e : ∀ w, heisO ψ S T u f w * star (heisO ψ S T u g w) = f (w + u) * star (g (w + u)) := by
    intro w
    simp only [heisO, star_mul']
    linear_combination (f (w + u) * star (g (w + u))) * hs (symplOH S T w u)
  simp_rw [e]
  refine setIntegral_add_right μ h𝓕 (g := fun w => f w * star (g w)) ?_ u
  rintro _ ⟨γ, rfl⟩ w
  change f (ratW T S γ + w) * star (g (ratW T S γ + w)) = f w * star (g w)
  rw [hf.quasi, hg.quasi, star_mul']
  linear_combination (f w * star (g w)) * hs (-(symplOH S T (ratW T S γ) w))

theorem thetaNormSq_heisenbergOp_invariant {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1) (μ : Measure (WO S T))
    [μ.IsAddHaarMeasure] {𝓕 : Set (WO S T)} (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (u : WO S T) : nrm2 μ 𝓕 (heisO ψ S T u f) = nrm2 μ 𝓕 f := by
  unfold nrm2
  have e : ∀ w, ‖heisO ψ S T u f w‖ ^ 2 = ‖f (w + u)‖ ^ 2 := fun w => by
    simp only [heisO, norm_mul, hn, one_mul]
  simp_rw [e]
  refine setIntegral_add_right μ h𝓕 (g := fun w => ‖f w‖ ^ 2) ?_ u
  rintro _ ⟨γ, rfl⟩ w
  change ‖f (ratW T S γ + w)‖ ^ 2 = ‖f w‖ ^ 2
  rw [hf.quasi, norm_mul, hn, one_mul]

theorem thPair_smul_right (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f g : WO S T → ℂ) (c : ℂ) :
    thPair μ 𝓕 f (c • g) = star c * thPair μ 𝓕 f g := by
  unfold thPair
  rw [← integral_const_mul]
  congr 1; funext w
  simp only [Pi.smul_apply, smul_eq_mul, star_mul']
  ring

theorem orth_all : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ vac, IsVacO ψ θ S T x.s y.s x.L y.L vac → ∀ (v : VolM D T.rank S.rank) f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T x.L y.L fun _ => True) f → (∀ u : WO S T, u.map (finPart D) = 0 → thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0) → ∀ u : WO S T, thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0 := by
  intro D ψ θ hθ S T x y hx hy vac hvac v f hf hlat hreal u
  have hψ := hvac.1
  have hn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  haveI : v.μ.IsAddHaarMeasure := v.covol.1
  have hF : IsAddFundamentalDomain (ratL T S) v.𝓕 v.μ := v.covol.2.1
  have hvt : IsThetaFunO ψ S T vac := hvac.2.theta
  have hvl := hvac.2.lat

  have key : ∀ g : WO S T, heisO ψ S T g f = f → heisO ψ S T g vac = vac → ψ (symplO S T g u) ≠ 1 →
      thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0 := by
    intro g hgf hgv hne
    have hc : heisO ψ S T g (heisO ψ S T u vac) = ψ (symplO S T g u) • heisO ψ S T u vac := by
      rw [GlobalTheory.SplitScalar.heisO_comm, hgv]
    have e := thPair_heisO hn v.μ hF hf (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hvt u) g
    rw [hgf, hc, thPair_smul_right] at e
    have hne' : star (ψ (symplO S T g u)) ≠ 1 := by
      intro h; apply hne; rw [← star_star (ψ _), h, star_one]
    have h2 : (1 - star (ψ (symplO S T g u))) * thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0 := by
      linear_combination e.symm
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm hne'))
  by_cases hA1 : ∀ g ∈ latO S T x.L y.L (fun _ => True), ψ (symplO S T (2 • g) u) = 1
  swap
  · push_neg at hA1
    obtain ⟨g, hg, hne⟩ := hA1
    exact key (2 • g) (hlat.1 g hg) (hvl.1 g hg) hne
  by_cases hA2 : ∀ e, IsSplitIdem D e → ∀ g ∈ latO S T x.L y.L (fun _ => True), IsHalf e g →
      ψ (symplO S T g u) = 1
  swap
  · push_neg at hA2
    obtain ⟨e, he, g, hg, hh, hne⟩ := hA2
    exact key g (hlat.2 e he g hg hh) (hvl.2 e he g hg hh) hne

  obtain ⟨ur, uf, hr, hfi, rfl⟩ : ∃ ur uf : WO S T, ur.map (finPart D) = 0 ∧ uf.map (infPart D) = 0 ∧
      u = ur + uf := by
    refine ⟨GlobalTheory.FinTranslate.eInf D • u, (1 - GlobalTheory.FinTranslate.eInf D) • u, ?_, ?_, ?_⟩
    · ext i j; exact GlobalTheory.ThetaClosed.finPart_eInf_smul (u i j)
    · ext i j; exact GlobalTheory.ThetaClosed.infPart_one_sub_eInf_smul (u i j)
    · rw [← add_smul, add_sub_cancel, one_smul]
  have hlf : ∀ g ∈ latO S T x.L y.L (fun _ => True), g.map (infPart D) = 0 := fun g hg =>
    GlobalTheory.SplitScalar.latO_fin hg
  have hsf : ∀ g : WO S T, g.map (infPart D) = 0 → symplO S T g (ur + uf) = symplO S T g uf := by
    intro g hg
    rw [GlobalTheory.LatVac.symplO_add_right, GlobalTheory.SplitScalar.symplO_skew S T ur g, GlobalTheory.SplitScalar.symplO_real_fin S T hr hg,
      neg_zero, zero_add]
  have hv' : IsVacO ψ θ S T x.s y.s x.L y.L (heisO ψ S T uf vac) := by
    have hv2 := hvac
    obtain ⟨-, hinf, hth, hl, hfock, hnorm⟩ := hv2
    refine ⟨hψ, hinf, GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hth uf, ⟨fun g hg => ?_, fun e he g hg hh => ?_⟩,
      fun τ z => ?_, hnorm.1, fun p hp => ?_⟩
    · rw [GlobalTheory.SplitScalar.heisO_comm, hl.1 g hg, ← hsf _ (hlf _ (AddSubgroup.nsmul_mem _ hg 2)), hA1 g hg, one_smul]
    · rw [GlobalTheory.SplitScalar.heisO_comm, hl.2 e he g hg hh, ← hsf _ (hlf g hg), hA2 e he g hg hh, one_smul]
    · have h0 := hfock τ z
      unfold annih at h0 ⊢
      rw [GlobalTheory.FinTranslate.dRho_heisO hinf hfi, GlobalTheory.FinTranslate.dRho_heisO hinf hfi]
      have h1 := congrArg (GlobalTheory.FinTranslate.heisL S T ψ uf) h0
      rw [map_add (f := _), map_smul, map_zero] at h1
      exact h1
    · show nrm2 p.1 p.2 (heisO ψ S T uf vac) = 1
      haveI := hp.1
      rw [thetaNormSq_heisenbergOp_invariant hn p.1 hp.2.1 hth uf]
      exact hnorm.2 p hp
  obtain ⟨c, -, hc⟩ := GlobalTheory.VacUnique.vacUniqueO D ψ θ hψ hθ S T x.s y.s hx.sig hy.sig hx.cart hy.cart x.L y.L
    hx.sd hy.sd vac _ hvac hv'
  have e : heisO ψ S T (ur + uf) vac = c • heisO ψ S T ur vac := by
    rw [GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (GlobalTheory.SplitScalar.symplO_real_fin S T hr hfi), hc,
      GlobalTheory.SplitScalar.heisO_smul]
  rw [e, thPair_smul_right, hreal ur hr, mul_zero]

end GlobalTheory.FinOrth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthRealHeisenbergTranslatesVacuumOfOrthFock
section
noncomputable section

namespace GlobalTheory.FockRealOrth

section Coord

open Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Size GlobalTheory.FockDensity
open scoped ENNReal ComplexOrder

theorem inner_coord {κ : Type} [Fintype κ] [DecidableEq κ] {Q s : Matrix κ κ ℂ} (hQ : Qᴴ = Q) (hs : s * s = 1)
    (hp : (Q * s).PosDef) {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    {ρ : (κ → ℂ) → B →L[ℂ] B} (h : IsHeis (fun x y => (star y ⬝ᵥ Q *ᵥ x).im) ρ) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (Φ : B →L[ℂ] H) (hΦ : ∀ v f, ‖Φ (ρ v f)‖ = ‖Φ f‖) {Y : Type}
    (T : Y → B →L[ℂ] B) (hT : ∀ y v f, T y (ρ v f) = ρ v (T y f)) (S F : Submodule ℂ B)
    (hS : ∀ f, f ∈ S ↔ Sm ρ f ∧ ∀ y, T y f = f)
    (hF : ∀ z, ∀ f ∈ S, f ∈ F → dH ρ z f - I • dH ρ (I • s *ᵥ z) f ∈ F) {v : B} (hvS : v ∈ S) (hvF : v ∈ F)
    (hv : ∀ z, dH ρ z v + I • dH ρ (I • s *ᵥ z) v = 0) {y : H} (hy : ∀ x ∈ F, inner ℂ y (Φ x) = 0) (w : κ → ℂ) :
    inner ℂ y (Φ (ρ w v)) = 0 := by
  obtain ⟨E, J, hJ, hE, hom⟩ := _root_.GlobalTheory.Twist.EuclidCoord.exists_coord κ Q s hQ hs hp
  have hρ : IsHeis (omJ J) fun v => ρ (E v) :=
    UnitaryOsc.isHeis_comp h (E : EuclideanSpace ℂ κ →L[ℝ] (κ → ℂ)) fun x y => hom x y
  have hm : ∀ G, G ∈ S ↔ Sm (fun v => ρ (E v)) G ∧ ∀ y, T y G = G :=
    fun G => (hS G).trans (and_congr_left' (UnitaryOsc.sm_comp_iff E _ G).symm)
  have hd : ∀ z, dH (fun v => ρ (E v)) z = dH ρ (E z) := fun z => funext fun G => by
    have := E.comp_right_fderiv (f := fun v => ρ v G) (x := 0)
    rw [map_zero] at this
    exact DFunLike.congr_fun this z
  have a1 : ∀ G ∈ S, Sm (fun v => ρ (E v)) G := fun G hG => ((hm G).1 hG).1
  have a2 : ∀ v, ∀ G ∈ S, dH (fun v => ρ (E v)) v G ∈ S := fun v G hG =>
    (hm _).2 ⟨VacBd.sm_dH hρ (a1 G hG) v, fun y => by
      rw [← (dH_comm (T y) (fun v => hT y (E v)) (a1 G hG)).2, ((hm G).1 hG).2]⟩
  have := inner_translate hJ hρ (fun v => hΦ (E v)) a1 a2 (F.comap S.subtype)
    (fun z x hx => by
      rw [Submodule.mem_comap, Submodule.subtype_apply, coe_cE, hd, hd, hE]
      exact hF (E z) x x.2 hx) (v := ⟨v, hvS⟩) hvF
    (fun z => (aE_eq_zero a1 a2 z _).2 (by rw [hd, hd, hE]; exact hv (E z))) (y := y)
    (fun x hx => hy x hx) (E.symm w)
  simpa only [E.apply_symm_apply] using this

end Coord

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isUnit_det_of_onb {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {p : ℕ} (h : IsONBasis G s B p) : IsUnit B.det := by
  obtain ⟨ε, h1, h2, -⟩ := h
  have h3 := congrArg Matrix.det h2
  rw [Matrix.det_mul, Matrix.det_diagonal] at h3
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  rw [h0, mul_zero] at h3
  obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.1 h3.symm
  rcases h1 a with ⟨e, -⟩ | ⟨e, -⟩ <;> simp [e] at ha

theorem cplxO_pm {m n : ℕ} {s : Matrix (Fin n) (Fin n) ℂ} {t : Matrix (Fin m) (Fin m) ℂ} (hs : s = 1 ∨ s = -1)
    (ht : t = 1 ∨ t = -1) : ∃ b : Bool, ∀ z, cplxO s t z = ((if b then 1 else -1 : ℂ) * Complex.I) • z := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · exact ⟨true, fun z => by simp [cplxO]⟩
  · exact ⟨false, fun z => by simp [cplxO]⟩
  · exact ⟨false, fun z => by simp [cplxO]⟩
  · exact ⟨true, fun z => by simp [cplxO]⟩

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem crea_fock (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {x : DefSp S} {y : DefSp T} (hx : x.Is) (hy : y.Is)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    ∃ Q, pureTensorO ψ θ S T x.s y.s x.B y.B f Q =
      crea (heisO ψ S T) θ τ (cplxO (x.s τ) (y.s τ)) z (pureTensorO ψ θ S T x.s y.s x.B y.B f P) := by
  have hadd : ∀ g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → IsThetaFunO ψ S T (g + g') :=
    fun _ _ => GlobalTheory.OrientedHeis.theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (a • g) :=
    fun a _ => GlobalTheory.OrientedHeis.theta_smul a
  have hth : ∀ v g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T
      (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B v g) :=
    fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h
  have hX : ∀ v Q,
      pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B) f (MvPolynomial.X v * Q) =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B v
        (pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B) f Q) := fun v Q => by
    refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) hadd hsm hth ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ i.1 _ hx.cart hy.cart j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  have hg : IsThetaFunO ψ S T (pureTensorO ψ θ S T x.s y.s x.B y.B f P) :=
    GlobalTheory.FockIndep.pure_mem (P := IsThetaFunO ψ S T) hadd hsm hth hf P
  obtain ⟨c, rfl⟩ : ∃ c : Fin T.rank → Fin S.rank → ℂ,
      z = ∑ i, ∑ j, c i j • Formalism.IndefR.Datum.unitMap (x.B τ) (y.B τ) i j :=
    ⟨_, GlobalTheory.FockCreaDir.eq_sum_unitMap (isUnit_det_of_onb (hy.onb τ).choose_spec)
      (isUnit_det_of_onb (hx.onb τ).choose_spec) z⟩
  obtain ⟨b, hb⟩ := cplxO_pm (hx.pm τ) (hy.pm τ)
  refine ⟨((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j, (if b then c i j else starRingEnd ℂ (c i j)) •
    (MvPolynomial.X (τ, i, j) * P), Eq.symm ?_⟩
  have h1 : ∀ (u : Matrix (Fin T.rank) (Fin S.rank) ℂ) g,
      crea (heisO ψ S T) θ τ (cplxO (x.s τ) (y.s τ)) u g =
        ((fockScale D τ : ℝ) : ℂ) • Formalism.IndefR.Datum.aPlus (heisO ψ S T) θ τ (cplxO (x.s τ) (y.s τ)) u g := fun u g => by
    rw [Formalism.IndefR.Datum.aPlus, smul_smul, mul_inv_cancel₀ (GlobalTheory.FockCreaDir.fockScale_ne_zero D τ), one_smul]
  rw [h1]
  have h2 : pureTensorO ψ θ S T x.s y.s x.B y.B f (((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j,
      (if b then c i j else starRingEnd ℂ (c i j)) • (MvPolynomial.X (τ, i, j) * P)) =
      ((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j, (if b then c i j else starRingEnd ℂ (c i j)) •
        Formalism.IndefR.Datum.aPlus (heisO ψ S T) θ τ (cplxO (x.s τ) (y.s τ))
          (Formalism.IndefR.Datum.unitMap (x.B τ) (y.B τ) i j) (pureTensorO ψ θ S T x.s y.s x.B y.B f P) := by
    unfold pureTensorO
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, map_sum, hX]
    rfl
  rw [h2]
  congr 1
  rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ _ _ hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ _ _ hg]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ τ _ _ hg b _ (hb _)


open GlobalTheory.RealWeil GlobalTheory.FockDensity in
theorem inner_toL2_eq_theta_pairing (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) [BorelSpace (WO S T)] [SecondCountableTopology (WO S T)]
    [IsFiniteMeasure (μ.restrict 𝓕)] (G G' : BB ψ S T) :
    inner ℂ (toL2 _ _ (μ.restrict 𝓕) G') (toL2 _ _ (μ.restrict 𝓕) G) = thPair μ 𝓕 (coeL ψ S T G) (coeL ψ S T G') :=
  BoundedContinuousFunction.inner_toLp (μ.restrict 𝓕) G'.1 G.1


open GlobalTheory.RealWeil GlobalTheory.FockDensity GlobalTheory.Mem.Lift GlobalTheory.ChainFr Classical in
theorem orth_real_translate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ vac, IsVacO ψ θ S T x.s y.s x.L y.L vac → ∀ (v : VolM D T.rank S.rank) f, IsThetaFunO ψ S T f → (∀ P, thPair v.μ v.𝓕 f (pureTensorO ψ θ S T x.s y.s x.B y.B vac P) = 0) → ∀ u : WO S T, u.map (finPart D) = 0 → thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0 := by
  intro D ψ θ hθ S T x y hx hy vac hvac v f hf ho u hu
  have hψ := hvac.1
  have hv := hvac.2.theta
  have hm := v.covol
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨U, hU, hl⟩ := hv.level
  obtain ⟨-, i2, i3, i4, i5, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : IsFiniteMeasure (v.μ.restrict v.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, hm.2.2]; exact ENNReal.one_lt_top⟩
  have e0 : coeL ψ S T (toB hψ vac hv) = vac := coe_toB hψ vac hv
  have e1 : coeL ψ S T (toB hψ f hf) = f := coe_toB hψ f hf
  have e2 : ∀ G : BB ψ S T, inner ℂ (toL2 _ _ (v.μ.restrict v.𝓕) (toB hψ f hf)) (toL2 _ _ (v.μ.restrict v.𝓕) G) = 0 ↔
      thPair v.μ v.𝓕 f (coeL ψ S T G) = 0 := fun G => by
    rw [inner_eq_zero_symm, inner_toL2_eq_theta_pairing, e1]
  have hF : toB hψ vac hv ∈ (GlobalTheory.Size.thetaLevel ψ S T U).comap (coeL ψ S T) := by
    rw [Submodule.mem_comap, e0]
    exact ⟨hv, hl⟩
  have hc := HM_cartan hx.cart hy.cart
  have key := inner_coord HM_herm hc.1 hc.2 (isHeis_rhoB h hψ) (toL2 _ _ (v.μ.restrict v.𝓕))
    (fun w G => by
      rw [← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2]
      exact lintegral_rhoB hψ v.μ v.𝓕 hm.1 hm.2.1 _ G)
    (fun u : {u : WO S T // u ∈ U ∧ u.map (infPart D) = 0} => rhoB hψ u.1) (fun u => rhoB_comm h hψ u.2.2) _
    ((LinearMap.range (pureTensorO ψ θ S T x.s y.s x.B y.B vac)).comap (coeL ψ S T))
    (fun G => (mem_level h hψ hU G).trans
      (and_congr_right' ⟨fun a u => a u.1 u.2.1 u.2.2, fun a u h1 h2 => a ⟨u, h1, h2⟩⟩))
    (fun z G hG hF => by
      have hs := ((mem_level h hψ hU G).1 hG).1
      rw [Submodule.mem_comap, map_sub, map_smul, coe_dH h hψ hs, coe_dH h hψ hs, Finset.smul_sum,
        ← Finset.sum_sub_distrib]
      refine sum_mem fun τ _ => ?_
      obtain ⟨P, hP⟩ := hF
      rw [cpt_cplx, ← hP]
      exact crea_fock hψ hθ hx hy hv τ _ P)
    hF ⟨1, (GlobalTheory.FockIndep.pure_one _).trans e0.symm⟩
    (fun z => fderiv_vac h hψ _ ((mem_level h hψ hU _).1 hF).1 x.s y.s
      (by rw [coe_toB]; exact hvac.2.fock) z)
    (y := toL2 _ _ (v.μ.restrict v.𝓕) (toB hψ f hf))
    (fun G hG => by
      obtain ⟨P, hP⟩ := hG
      rw [e2, ← hP]
      exact ho P) (vecL (GlobalTheory.FockCompare.piW θ T S u))
  rw [e2] at key
  have e3 : iotaV σ S T (vecL (GlobalTheory.FockCompare.piW θ T S u)) = u :=
    h.real_ext (V := T) (W := S) (real_iotaV h _) hu (h.pi_iota T S _)
  have e4 := coe_rhoV (σ := σ) hψ (vecL (GlobalTheory.FockCompare.piW θ T S u)) (toB hψ vac hv)
  rw [e3, coe_toB] at e4
  rw [← e4]
  exact key

end GlobalTheory.FockRealOrth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PhiQEqZeroOfNotMem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

noncomputable section

namespace GlobalTheory.NrmVol

def suppQ {D : D7} (v : FinPl D) {a b : ℕ} (r : ℕ) : Set (Matrix (Fin b) (Fin a) (Fv D.host.F v)) :=
  {x | IsUnit (topL r x).det ∧ Valued.v (topL r x).det = 1 ∧ (∀ i j, x i j ∈ v.adicCompletionIntegers D.host.F) ∧
      ∀ i j, r ≤ i.val → j.val < r → Valued.v (x i j) < 1}

theorem phiQ_eq_zero_of_not_mem {D : D7} (v : FinPl D) {a b : ℕ} (r : ℕ) (mu : (Fv D.host.F v)ˣ →* ℂˣ)
    (x : Matrix (Fin b) (Fin a) (Fv D.host.F v)) (hx : x ∉ suppQ v r) : phiQ v r mu x = 0 := by
  unfold phiQ
  rw [dite_eq_right]
  exact hx

end GlobalTheory.NrmVol
end
end

