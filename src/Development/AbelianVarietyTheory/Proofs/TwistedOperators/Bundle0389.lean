module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1366
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompAtOfFin
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0347
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskySegmentClassExistsForEveryPlacing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0373

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionProdConjEqOfHeisenbergFixed
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaFixedProd

theorem setIntegral_add_right {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] (Γ : AddSubgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsAddHaarMeasure] {𝓕 : Set G} (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (h : G → ℂ)
    (hper : ∀ γ ∈ Γ, ∀ x, h (γ + x) = h x) (l : G) :
    ∫ x in 𝓕, h (x + l) ∂μ = ∫ x in 𝓕, h x ∂μ := by
  have hs : IsAddFundamentalDomain Γ ((fun x => x - l) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv (measurePreserving_sub_right μ l).quasiMeasurePreserving (e := id) Function.bijective_id
      (fun g x => by
        show (g +ᵥ x) - l = g +ᵥ (x - l)
        simp only [AddSubgroup.vadd_def, vadd_eq_add]
        abel)
  have e1 : ∫ x in 𝓕, h (x + l) ∂μ = ∫ y in (fun x => x - l) ⁻¹' 𝓕, h y ∂μ := by
    rw [← (measurePreserving_add_right μ l).setIntegral_preimage_emb (measurableEmbedding_addRight l) h]
    congr 2
    ext x
    simp
  rw [e1]
  exact hs.setIntegral_eq h𝓕 fun g x => hper g g.2 x

theorem prod_eq_of_fixed : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (N : AddSubgroup (WO S T)) (M : Module.End ℂ (WO S T → ℂ)), (∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T (M f) ∧ ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u (M f) = M f) → (∀ w f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) → M (heisO ψ S T w f) = heisO ψ S T w (M f)) → (∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∀ f g, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → ∀ x, M f x * star (M g x) = f x * star (g x) := by
  intro D ψ S T hψ N M hMV hc hn f g hf hfN hg hgN x
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨μ, 𝓕, hμ, h𝓕, -⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hKc μ h𝓕⟩
  obtain ⟨l1, l2, -, l4, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have hcomp := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).2.1
  let Θ : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {f | IsThetaFunO ψ S T f ∧ ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f}
      add_mem' := fun {a b} ha hb => ⟨GlobalTheory.WeilVacMove.isTheta_add ha.1 hb.1, fun u hu h0 => by
        funext w
        have e1 := congrFun (ha.2 u hu h0) w
        have e2 := congrFun (hb.2 u hu h0) w
        simp only [heisO, Pi.add_apply] at e1 e2 ⊢
        rw [mul_add, e1, e2]⟩
      zero_mem' := ⟨GlobalTheory.WeilVacMove.isTheta_zero, fun u _ _ => by funext w; simp [heisO]⟩
      smul_mem' := fun c a ha => ⟨GlobalTheory.WeilVacMove.isTheta_smul c ha.1, fun u hu h0 => by
        funext w
        have e1 := congrFun (ha.2 u hu h0) w
        simp only [heisO, Pi.smul_apply, smul_eq_mul] at e1 ⊢
        rw [mul_left_comm, e1]⟩ }
  have hb : ∀ a ∈ Θ, ∃ C : ℝ, ∀ w, ‖a w‖ ≤ C := fun a ha => by
    have hp : ∀ γ ∈ ratL T S, ∀ w, ‖a (γ + w)‖ = ‖a w‖ := by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm (ha.1.quasi γ w)).trans (by rw [norm_mul, hψ.1.2.1, one_mul])
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ha.1.cont.continuousOn
    refine ⟨C, fun w => ?_⟩
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← hp γ hγ w]
    exact hC _ h
  have hMΘ : ∀ a ∈ Θ, M a ∈ Θ := fun a ha => hMV a ha.1 ha.2
  have hpol : ∀ a a', a ∈ Θ → a' ∈ Θ → ∫ w in 𝓕, M a w * star (M a' w) ∂μ = ∫ w in 𝓕, a w * star (a' w) ∂μ :=
    fun a a' ha ha' => GlobalTheory.Mem.LiftPolar.integral_mul_star_eq (μ.restrict 𝓕) Θ (fun b hb => hb.1.cont.measurable) hb M
      hMΘ (fun b hb => hn μ 𝓕 hμ h𝓕 b hb.1 hb.2) a a' ha ha'
  have hint : ∀ a a', IsThetaFunO ψ S T a → IsThetaFunO ψ S T a' →
      Integrable (fun w => a w * star (a' w)) (μ.restrict 𝓕) := fun a a' ha ha' => by
    have hcont : Continuous fun w => a w * star (a' w) := ha.cont.mul ha'.cont.star
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    refine Integrable.of_bound hcont.aestronglyMeasurable C (Filter.Eventually.of_forall fun w => ?_)
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← GlobalTheory.ThetaSchur.prod_periodic hψ ha ha' hγ w]
    exact hC _ h
  have hfix : ∀ a a', a ∈ Θ → a' ∈ Θ → ∀ l ∈ N, l.map (infPart D) = 0 → ∀ w,
      a (w + l) * star (a' (w + l)) = a w * star (a' w) := fun a a' ha ha' l hl h0 w => by
    have e1 := congrFun (ha.2 l hl h0) w
    have e2 := congrFun (ha'.2 l hl h0) w
    simp only [heisO] at e1 e2
    rw [← e1, ← e2, star_mul']
    linear_combination -(a (w + l) * star (a' (w + l))) * GlobalTheory.ThetaSchur.mul_star_psi hψ (symplOH S T w l)
  have hfΘ : f ∈ Θ := ⟨hf, hfN⟩
  have hgΘ : g ∈ Θ := ⟨hg, hgN⟩
  have hadd : ∀ y z γ : WO S T, ψ (symplO S T (y + z) γ) = ψ (symplO S T y γ) * ψ (symplO S T z γ) := fun y z γ => by
    simp only [← l4, l1, AddChar.map_add_eq_mul]
    ring
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (WO S T) (ratL T S) K hK hKc (ratL T S)
    (fun γ x => ψ (symplO S T x γ))
    (fun γ => by
      have : Continuous fun x : WO S T => symplOH S T x (γ : WO S T) :=
        GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_id' continuous_const
      simp only [← l4]
      exact hψ.1.1.comp (this.add this))
    (fun γ x y => hadd x y γ)
    (fun γ γ' x => by
      simp only [← l4, AddSubgroup.coe_add, l2, AddChar.map_add_eq_mul]
      ring)
    (fun x => by
      simp only [← l4, AddSubgroup.coe_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one])
    (fun γ x => hψ.1.2.1 _)
    (fun x => by
      rw [← GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T x]
      exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
    μ 𝓕 hμ h𝓕 (fun x => M f x * star (M g x) - f x * star (g x))
    (((hMΘ f hfΘ).1.cont.mul (hMΘ g hgΘ).1.cont.star).sub (hf.cont.mul hg.cont.star))
    (fun γ hγ x => by
      rw [GlobalTheory.ThetaSchur.prod_periodic hψ hf hg hγ,
        GlobalTheory.ThetaSchur.prod_periodic hψ (hMΘ f hfΘ).1 (hMΘ g hgΘ).1 hγ])
    (fun γ => by
      show ∫ x in 𝓕, ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x)) ∂μ = 0
      by_cases hγ : ∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T (γ : WO S T) l) = 1
      · have hγf : heisO ψ S T γ f ∈ Θ := ⟨hth _ f hf, fun u hu h0 => by
          funext w
          have a1 := congrFun (hcomp u γ f) w
          have a2 := congrFun (hcomp γ u f) w
          rw [hfN u hu h0, add_comm (γ : WO S T) u] at a2
          simp only [Pi.smul_apply, smul_eq_mul] at a1 a2
          rw [a1, a2]
          congr 1
          have h1 := hγ u hu h0
          rw [← l4, AddChar.map_add_eq_mul] at h1
          rw [GlobalTheory.WeilVacMove.symplOH_skew S T (γ : WO S T) u]
          have h2 : ψ (-symplOH S T (γ : WO S T) u) * ψ (symplOH S T (γ : WO S T) u) = 1 := by
            rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
          linear_combination (-ψ (-symplOH S T (γ : WO S T) u)) * h1 + ψ (symplOH S T (γ : WO S T) u) * h2⟩
        have e : (fun x => ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x))) = fun x =>
            M (heisO ψ S T γ f) x * star (M g x) - heisO ψ S T γ f x * star (g x) := by
          funext x
          rw [hc _ f hf hfN hγ, GlobalTheory.ThetaSchur.heisO_rat hf γ.2, GlobalTheory.ThetaSchur.heisO_rat (hMΘ f hfΘ).1 γ.2]
          ring
        rw [e, integral_sub (hint _ _ (hMΘ _ hγf).1 (hMΘ g hgΘ).1) (hint _ _ hγf.1 hg), hpol _ _ hγf hgΘ, sub_self]
      · push_neg at hγ
        obtain ⟨l, hl, h0, hne⟩ := hγ
        have hper : ∀ δ ∈ ratL T S, ∀ x, (fun x => ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x)))
            (δ + x) = (fun x => ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x))) x := by
          intro δ hδ x
          simp only
          rw [hadd, (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T δ).2 hδ γ γ.2, one_mul,
            GlobalTheory.ThetaSchur.prod_periodic hψ hf hg hδ,
            GlobalTheory.ThetaSchur.prod_periodic hψ (hMΘ f hfΘ).1 (hMΘ g hgΘ).1 hδ]
        have htr := GlobalTheory.ThetaFixedProd.setIntegral_add_right (G := WO S T) (ratL T S) μ h𝓕
          (fun x => ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x))) hper l
        simp only [hadd, hfix _ _ (hMΘ f hfΘ) (hMΘ g hgΘ) l hl h0, hfix _ _ hfΘ hgΘ l hl h0] at htr
        have hsk : symplO S T l γ = -symplO S T (γ : WO S T) l := by
          rw [← l4, ← l4, GlobalTheory.WeilVacMove.symplOH_skew S T (γ : WO S T) l]
          abel
        have hc1 : ψ (symplO S T l γ) ≠ 1 := fun h1 => by
          apply hne
          rw [hsk] at h1
          have h2 : ψ (symplO S T (γ : WO S T) l) * ψ (-symplO S T (γ : WO S T) l) = 1 := by
            rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
          rw [h1, mul_one] at h2
          exact h2
        have e2 : (fun x => ψ (symplO S T x γ) * ψ (symplO S T l γ) * (M f x * star (M g x) - f x * star (g x))) =
            fun x => ψ (symplO S T l γ) * (ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x))) := by
          funext x
          ring
        rw [e2, integral_const_mul] at htr
        have h3 : (ψ (symplO S T l γ) - 1) *
            ∫ x in 𝓕, ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x)) ∂μ = 0 := by
          linear_combination htr
        exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hc1))
  exact sub_eq_zero.1 (congrFun key x)

end GlobalTheory.ThetaFixedProd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesFockVectorInvariance
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.ThInv

theorem fvec_val_inv : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (h : GA D S) (B : C.Bas), C.IsB B → ∀ u : WO S T → ℂ, C.IsTh u → ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, (∀ γ ∈ GQ T, ∀ g, om (h, γ * g) (C.fvec B u Q) 0 = om (h, g) (C.fvec B u Q) 0) ∧ ((∀ k, C.LevK Lv k 1 → om (1, k) u = u) → ∀ k, C.LevK Lv k 1 → ∀ g, om (h, g * k) (C.fvec B u Q) 0 = om (h, g) (C.fvec B u Q) 0) := by
  intro D S T C om hW Lv h B hB u hu Q
  have hth : C.IsTh (C.fvec B u Q) := (_root_.GlobalTheory.Ker.FockAlg.fock_vec_laws D S T C B hB (fun _ => 1) u hu Q).1
  refine ⟨fun γ hγ g => ?_, fun hk k hkL g => ?_⟩
  · have p : ((h, γ * g) : GA D S × GA D T) = (1, γ) * (h, g) := by
      rw [Prod.mk_mul_mk, one_mul]
    rw [p, map_mul, Module.End.mul_apply]
    exact hW.om_aut 1 (one_mem _) γ hγ _ (hW.om_pres _ _ hth)
  · have p : ((h, g * k) : GA D S × GA D T) = (h, g) * (1, k) := by
      rw [Prod.mk_mul_mk, mul_one]
    have hmv := ((_root_.GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB).2.2.2.2.2 k
    rw [p, map_mul, Module.End.mul_apply, GlobalTheory.Ker.Red.om_fvec C om hW 1 (one_mem _) k u hu B hB Q,
      hmv.2.2.1 hkL.1, hk k hkL]

end GlobalTheory.Ker.ThInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTraceIsTranslSumStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pull_isTranslSum_of_isThetaTrace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x x' : Sp K ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (p : ℕ) (s : LB.Sec (PPx x)) (s₀ s' : LB.Sec (PPx x')) (a : K), IsPair (p ^ 2) f f' → (∀ i, s'.f i = scal x' a i * s₀.f i) → IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) p s s' → ∃ t, IsPullOf p f a s₀ t ∧ IsTranslSum p s t := by
  first | exact @GlobalTheory.HkIntegral.thetaTrace_isTranslSum | exact GlobalTheory.HkIntegral.thetaTrace_isTranslSum | (intros; apply GlobalTheory.HkIntegral.thetaTrace_isTranslSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersRealPlaces
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

namespace GlobalTheory.VacuumCharacter

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem signBlockDeterminant_diagonalPhases_zpow {n : ℕ} (ε : Fin n → Bool) (t : Fin n → ℝ) (x : Bool → ℤ) :
    signBlockDeterminant ε true (diagonal fun j => Complex.exp (Complex.I * t j)) ^ x true *
      signBlockDeterminant ε false (diagonal fun j => Complex.exp (Complex.I * t j)) ^ x false =
      Complex.exp (Complex.I * ∑ j, (x (ε j) : ℂ) * t j) := by
  have key : ∀ e : Bool, signBlockDeterminant ε e (diagonal fun j => Complex.exp (Complex.I * t j)) ^ x e =
      Complex.exp (Complex.I * ∑ j ∈ Finset.univ.filter (fun j => ε j = e), (x e : ℂ) * t j) := by
    intro e
    rw [signBlockDeterminant, submatrix_diagonal _ _ Subtype.val_injective, det_diagonal]
    simp only [Function.comp_apply]
    rw [← Complex.exp_sum,
      ← Complex.exp_int_mul,
      Finset.sum_subtype (Finset.univ.filter fun j => ε j = e) (p := fun j => ε j = e) (by simp)]
    congr 1
    try simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [key, key, ← Complex.exp_add, ← mul_add,
    ← Finset.sum_fiberwise (M := ℂ) (s := (Finset.univ : Finset (Fin n))) (g := ε)
      (f := fun j : Fin n => (x (ε j) : ℂ) * (t j : ℂ)), Fintype.sum_bool]
  congr 3 <;> refine Finset.sum_congr rfl fun j hj => ?_ <;> rw [(Finset.mem_filter.1 hj).2]

theorem diag_mem_Kset {n : ℕ} (ε : Fin n → Bool) (t : Fin n → ℝ) :
    (diagonal fun j => Complex.exp (Complex.I * t j)) ∈ Formalism.REAL.Kset ε := by
  have hu : ∀ j, star (Complex.exp (Complex.I * t j)) * Complex.exp (Complex.I * t j) = 1 := by
    intro j
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    simp
  simp only [Formalism.REAL.Kset, Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, diagonal_conjTranspose,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext j
    exact hu j
  · rw [Formalism.REAL.Jm, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext j
    ring

theorem torusVac_of_compactFock {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ)
    (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S') (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
    (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ) (h : CompactFock ψ θ M M' ω f τ aS aT) :
    TorusVac θ M M' ω f τ aS aT := by
  obtain ⟨x, y, hx, hy, hK⟩ := h
  intro t t'
  have hact := hK _ (diag_mem_Kset (M.ε τ) t) _ (diag_mem_Kset (M'.ε τ) t') 1
  rw [map_one, GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.ptOf_one] at hact
  rw [hact, signBlockDeterminant_diagonalPhases_zpow, signBlockDeterminant_diagonalPhases_zpow, ← Complex.exp_add, ← mul_add]
  have hx' : ∀ j, ((x (M.ε τ j) : ℤ) : ℂ) = ((wtS (M'.ε τ) aT (M.ε τ j) : ℚ) : ℂ) := fun j => by
    rw [← hx j]; push_cast; rfl
  have hy' : ∀ i, ((y (M'.ε τ i) : ℤ) : ℂ) = ((wtT (M.ε τ) aS (M'.ε τ i) : ℚ) : ℂ) := fun i => by
    rw [← hy i]; push_cast; rfl
  simp only [hx', hy']

theorem vacChar : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D := by
  intro D V W S S' M M' θ ψ χS χT ω f τ aS aT hθ hW hS hT hV
  have hF := GlobalTheory.ChainFr.isVacF_of_isVacVec hV
  have hK := _root_.GlobalTheory.CompactFockAction.compactFockAll D V W (GlobalTheory.ChainFr.Fr.ofModel M) (GlobalTheory.ChainFr.Fr.ofModel M') θ ψ χS χT ω f τ aS aT
    hθ hW hS hT hF hV.ne
  have hL := _root_.GlobalTheory.LieScalar.lieFockAll D V W (GlobalTheory.ChainFr.Fr.ofModel M) (GlobalTheory.ChainFr.Fr.ofModel M') θ ψ χS χT ω f τ aS aT
    hθ hW hS hT hF
  have hC : CompactFock ψ θ M M' ω f τ aS aT := by
    obtain ⟨x, y, hx, hy, hk⟩ := hK
    refine ⟨x, y, hx, hy, fun g hg k hk' P => ?_⟩
    have e := hk g hg k hk' P
    rwa [GlobalTheory.ChainFr.ptF_ofModel] at e
  refine ⟨torusVac_of_compactFock ψ θ M M' ω f τ aS aT hC, hC, ?_, ?_⟩
  · intro X hX P z
    have e := hL.1 X hX P z
    rw [GlobalTheory.ChainFr.ptF_ofModel] at e
    rw [sub_eq_add_neg, ← neg_smul]
    exact e
  · intro Y hY P z
    have e := hL.2 Y hY P z
    rw [GlobalTheory.ChainFr.ptF_ofModel] at e
    exact e

end GlobalTheory.VacuumCharacter

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TracePairingArchimedeanVarsNondegenerateRight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

namespace GlobalTheory.GaussLine

theorem pairInf_nondeg : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (q : κ → mixedEmbedding.mixedSpace F),
    (∀ x, GlobalTheory.GaussLine.pairInf F κ x q = 0) → q = 0 := by
  intro F _ _ κ _ q hq
  funext i
  refine GlobalTheory.ArchUniq.Coord.eq_zero_of_trace _ fun b => ?_
  have h := hq (Pi.single i b)
  rw [GlobalTheory.GaussLine.pairInf_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp),
    Pi.single_eq_same, mul_comm] at h
  simpa using h

end GlobalTheory.GaussLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskyGrothendieckPolynomialRingOfSegments
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult

namespace GlobalTheory

theorem zelevinskyPolynomialRing_of_parts :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.SegmentRepresentation →
      GlobalTheory.Published.GrothendieckRingPolynomial → GlobalTheory.Published.ZelevinskyPolynomialRing := by
  intro hBZ hSeg hRing k _ _ _ _
  obtain ⟨Z, hZ⟩ := _root_.GlobalTheory.segmentClass_exists hSeg k
  obtain ⟨Ψ, h1, hmul, hX⟩ := hRing k Z hZ
  refine ⟨Z, Ψ, hZ, ⟨h1, fun r t V W _ _ _ _ π₁ π₂ h₁ h₂ s₁ s₂ => ?_⟩, hX⟩
  have h := _root_.GlobalTheory.ProdLength.prod₂_hasFiniteLength hBZ k r t V W π₁ π₂ h₁ h₂ s₁ s₂
  exact ⟨h, hmul r t V W π₁ π₂ h₁ h₂ s₁ s₂ h⟩

end GlobalTheory
end

