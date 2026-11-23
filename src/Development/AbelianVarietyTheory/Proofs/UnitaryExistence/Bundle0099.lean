module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagDomainModelsOfFamilyUniformisation
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr
public import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0200
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsConjSplitPointLatticeLinearMap
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsWeightZeroSectionOfPeriodSpaceFunction

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoeffFieldAlgClosedInFunctionFieldOfAutFixPeriod
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat.FixedConstLevel

open Polynomial GlobalTheory.CompRat.FixedConst

theorem fnAlgClosed_of_permutes_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (∀ x : KA l, σ x = (x : ℂ)) → ∀ c : Coeff l, (∀ τ : ℂ ≃+* ℂ, (∀ x ∈ c.F, τ x = x) → ConjugationPermutesPeriods F τ id) → FnAlgClosed (Xo := Xo) (c := c) := by
  intro E _ _ _ H D l Xo σ g ty F h1 hσ hty hA c hperm Z a ha
  obtain ⟨r, rfl⟩ := GlobalTheory.GeomIrr.mem_range_of_isAlgebraic_ratFun a (ha.tower_top (kap Z))
  have hr : IsIntegral c.F r := (isIntegral_algebraMap_iff ).1 ha.isIntegral
  suffices h : r ∈ (algebraMap c.F (kap Z)).range by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by rw [← hk, ← IsScalarTower.algebraMap_apply]⟩
  have hfin : FiniteDimensional ℚ c.F := c.fin
  have hcF : Countable c.F := Cardinal.mk_le_aleph0_iff.1 (by
    simpa [Cardinal.mkRat] using Algebra.IsAlgebraic.cardinalMk_le_max ℚ c.F)
  have hk : Countable (kap Z) :=
    GlobalTheory.GenericReading.countable_of_fg_top ((GlobalTheory.Reg.kap_fg_trdeg E H D l Xo c).1 Z)
  obtain ⟨φ⟩ : Nonempty (kap Z →ₐ[c.F] ℂ) := GlobalTheory.nonempty_algHom_complex_of_countable c.F (kap Z)
  refine mem_range_of_fixed φ hr fun τ hτ => ?_
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have := CompFin.isNoetherian_XF Xo c
  have : GlobalTheory.IsNormalScheme (Xo.XF c) := (GlobalTheory.isNormalScheme_iff _).2
    (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (strK (Xo := Xo) (c := c))
      ((GlobalTheory.isNormalScheme_iff _).1 inferInstance))
  let κ : c.F →+* Γ(Xo.XF c, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv ≫ (strK (Xo := Xo) (c := c)).appTop).hom
  let j : c.F →+* ℂ := algebraMap c.F ℂ
  have hκ : ∀ (x : Sp ℂ ⟶ Xo.XF c) (i : c.F →+* ℂ), x ≫ strK = spMap i → (ev x).comp κ = i := by
    intro x i hx
    ext k
    change ev x ((strK (Xo := Xo) (c := c)).appTop.hom _) = _
    rw [← ev_comp, hx, ev_spec]
    exact congrArg i ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv_hom_id_apply k)
  let x : Sp ℂ ⟶ Xo.XF c := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ genSp Z
  have hx : x ≫ strK = spMap j := by
    rw [Category.assoc, ← Spec.map_preimage (genSp Z ≫ strK), ← Spec.map_comp]
    congr 1
    ext k
    exact φ.commutes k
  have hev : ∀ f, ev x f = φ (((Xo.XF c).evaluation ⊤ (genPt Z) trivial).hom f) := ev_residue _ φ.toRingHom
  have hm := minpoly.monic hr
  obtain ⟨f, hf, hf0⟩ := exists_section Z (genPt Z)
    ((Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents _ Z.2)) ((minpoly c.F r).map κ) (hm.map _) r (by
    apply φ.toRingHom.injective
    rw [hom_eval₂, ← (RingHom.ext hev : ev x = φ.toRingHom.comp _), eval₂_map, hκ x j hx, map_zero]
    exact (aeval_algHom_apply φ r _).trans (by rw [minpoly.aeval, map_zero]))
  have hS : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap j →
      valAt' y ⊤ f ∈ insert 0 ((minpoly c.F r).rootSet ℂ) := by
    intro y hy
    have h := congrArg (ev y) hf0
    rw [map_mul, ← eval₂_at_apply, eval₂_map, hκ y j hy, map_zero, mul_eq_zero] at h
    rw [valAt'_top]
    exact h.imp id fun h => mem_rootSet.2 ⟨hm.ne_zero, h⟩
  obtain ⟨i, P, hP, hu⟩ := F.onto (x ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx, (RingHom.ext hA : σ = algebraMap (KA l) ℂ), ← Spec.map_comp]
    rfl)
  obtain ⟨P', hP', hu'⟩ := hperm τ (fun z hz => hτ ⟨z, hz⟩) i P hP
  have key := _root_.GlobalTheory.CompRat.valAt_eq_of_finite_values_anyLevel E H D l Xo σ g ty F h1 hσ hty c j f _ ((rootSet_finite _ _).insert 0) hS i P' P hP' hP
    (spMap (τ : ℂ →+* ℂ) ≫ x) x (by rw [Category.assoc, ← hu]; exact hu') (by
      rw [Category.assoc, hx, ← Spec.map_comp]
      congr 1
      ext k
      exact hτ k) hu.symm hx
  rwa [valAt'_top, valAt'_top, ev_conj, hev, hf] at key

end GlobalTheory.CompRat.FixedConstLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefficientFieldAlgClosedInFunctionFieldsOfPerioStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficientField_algClosed_in_functionFields_of_periodSpaces : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ c : Coeff l, (∀ τ : ℂ ≃+* ℂ, (∀ x ∈ c.F, τ x = x) → ConjugationPermutesPeriods F τ id) → FnAlgClosed (Xo := Xo) (c := c) := by
  first | exact @GlobalTheory.CompRat.FixedConst.fnAlgClosed_of_permutes_id | exact GlobalTheory.CompRat.FixedConst.fnAlgClosed_of_permutes_id | (intros; apply GlobalTheory.CompRat.FixedConst.fnAlgClosed_of_permutes_id <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongrOfDvdModulus
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.FrameNorm
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem congr_of_dvd_modulus {E : Type} [Field E] [NumberField E] {r : ℕ} {L : Type} [AddCommGroup L] [Module (𝓞 E) L]
    (Λ : Submodule (𝓞 E) (Fin r → E)) (φ : L ≃ₗ[𝓞 E] Λ) (γ : Matrix (Fin r) (Fin r) E) {m N : ℕ} (hd : m ∣ N)
    (h : ∀ x ∈ Λ, ∃ y ∈ Λ, Matrix.mulVec γ x - x = (N : E) • y) (a : L) :
    ∃ b : L, γ.mulVec (φ a : Fin r → E) = (φ a : Fin r → E) + m • (φ b : Fin r → E) := by
  obtain ⟨d, rfl⟩ := hd
  obtain ⟨y, hy, e⟩ := h _ (φ a).2
  refine ⟨φ.symm (d • ⟨y, hy⟩), ?_⟩
  rw [LinearEquiv.apply_symm_apply, ← sub_eq_iff_eq_add', e, Nat.cast_smul_eq_nsmul, mul_smul]
  rfl

theorem exists_unf_hasPrinc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (σ : c.F →+* ℂ) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)), 1 ≤ Dw.p + Dw.q → GoodEmb c σ → cc ξ₀ = -ξ₀ → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ₀).im < 0) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ x) (φ y))) → ∃ U : Unf Xo c σ r, IsUnf U ∧ HasPrinc U l.M' ∧ Nonempty U.Comp ∧ (∀ k la γ, (U.X k).χ la γ = 1) ∧ (∀ k, (U.X k).Gm = Gm ∧ (U.X k).ξ0 = ξ₀) ∧ (∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x)) ∧ ∀ ρ, FJ.LatZ U.X ρ ∧ (l.A = 1 → FJ.ExpoMatch U.X 1 ρ l.M) := by
  intro E _ _ _ H Dw l Xo c σ r ξ₀ Gm φ hpq hσ hξ hneg hφ
  have hN : N1c := _root_.GlobalTheory.closing_of_abelianSchemeLaws
  have hH := _root_.GlobalTheory.QNorm.hasseNormSt
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hT : Out.SecTwistSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  classical
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨F⟩ := hN E H Dw l Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) _
    (fun j => relab c σ (e j).1) hpq hσ ((_root_.GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw _ e)
  obtain ⟨M, hM, hX, hG⟩ := _root_.GlobalTheory.ModelsExist.exists_modelsOf hH E H Dw l Xo _ _ _ F r ξ₀ Gm φ hξ hneg hφ
  obtain ⟨un, hun⟩ := _root_.GlobalTheory.FrameUnif.exists_framesOK hB hT E H Dw l Xo c σ _ e F r M hσ hM hX
  have hred : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  refine ⟨unfOf e F M un, _root_.GlobalTheory.FrameUnif.isUnf_built hB E H Dw l Xo c σ _ e F r M un hσ hM hX hun, fun k γ hγ h => ?_,
    ⟨⟨0, F.n_pos⟩⟩, hM.chi, hG,
    fun k x => _root_.GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c (CAt σ) _, fun ρ => ⟨_root_.GlobalTheory.CuspCentre.latZ E r ρ _ _, fun hA => ?_⟩⟩
  · exact (hM.gam k γ).2 ⟨hγ, fun a _ => congr_of_dvd_modulus _ (M.φ k) _ (Nat.dvd_lcm_left _ _) h a,
      fun a => congr_of_dvd_modulus _ (M.φ k) _ (Nat.dvd_lcm_right _ _) h a⟩
  · exact _root_.GlobalTheory.ExpoModels.expoMatch_models E H Dw l Xo _ _ _ F r M ρ hM hA

end GlobalTheory.FrameUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspSectionAdelicLeftInvariantContinuous
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem adel_leftInv_and_continuous : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ dict, C.IsDict dict → ∀ mu : GA D V → ℂ, (∀ g g', mu (g * g') = mu g * mu g') → (∀ γ ∈ GQ V, mu γ = 1) → Continuous mu → ∀ (la : ∀ k, Wt (C.M.X k).Ψ r) (P : FDSec C.M.X), IsHolCusp C.M.X la P → (∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g) ∧ Continuous (adel V dict mu P) := by
  intro D H Dw l Xo c σ V r C hC dict hd mu hmul hrat hm la P hP
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨⟨Kf, hKf⟩, hnb⟩ := _root_.GlobalTheory.Member.PrincLevel.exists_levelK_and_nhds D V l.M
  obtain ⟨h1, -, h3, -, h5⟩ := _root_.GlobalTheory.Member.dict_invariant D H Dw l Xo c σ V r C hC dict hd Kf hKf
  have hχ := hC.base.chi
  have hsec : ∀ k, (C.M.X k).IsSec (la k) (P k) := fun k => (hP k).1.1
  constructor
  · intro γ hγ g
    obtain ⟨γ', hγ', he⟩ := h1 γ hγ g
    show mu (γ * g) * P (dict (γ * g)).1 (dict (γ * g)).2 = mu g * P (dict g).1 (dict g).2
    rw [he, hmul, hrat γ hγ, one_mul]
    show mu g * P (dict g).1 (lact γ' (dict g).2) = _
    rw [(hsec _).2.2 γ' hγ' _ (h3 g), hχ, one_mul]
  · rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨γ, hmk, -⟩ := hd.1 g₀
    generalize (dict g₀).1 = k at hmk
    have hfr := fun h => _root_.GlobalTheory.Member.fr_orthonormal_unit D H Dw l Xo c σ V r C hC h k
    have hPc : ContinuousOn (P k) (C.M.X k).dom := (hsec k).1.continuousOn
    have hx : Continuous (fun g : GA D V => C.fr (γ * g) k) :=
      (hfr 1).2.2.2.1.comp (continuous_const.mul continuous_id)
    have hc : Continuous (fun g => mu g * P k (C.fr (γ * g) k)) :=
      hm.mul (hPc.comp_continuous hx fun g => (hfr _).2.1)
    have hN : {g : GA D V | FinCong V l.M (g₀⁻¹ * g)} ∈ 𝓝 g₀ := by
      have hcont : ContinuousAt (fun g : GA D V => g₀⁻¹ * g) g₀ :=
        (continuous_const.mul continuous_id).continuousAt
      have h0 := hnb hM
      rw [← inv_mul_cancel g₀] at h0
      exact hcont h0
    have heq : (fun g => mu g * P k (C.fr (γ * g) k)) =ᶠ[𝓝 g₀] adel V dict mu P := by
      filter_upwards [hN] with g hg
      have hmk' := (_root_.GlobalTheory.Member.mark_move D H Dw l Xo c σ V r C hC g₀ k γ hmk).2.1 _ hg
      rw [mul_inv_cancel_left] at hmk'
      obtain ⟨δ, hδ, he⟩ := h5 g k γ hmk'
      show mu g * P k (C.fr (γ * g) k) = mu g * P (dict g).1 (dict g).2
      rw [he]
      show _ = mu g * P k (lact δ (C.fr (γ * g) k))
      rw [(hsec k).2.2 δ hδ _ (hfr _).2.1, hχ, one_mul]
    exact hc.continuousAt.congr heq

end GlobalTheory.Member
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DictIsUnifOfMarkingRuleDictionary
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem dictIsUnif_of_isDict : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ dict, C.IsDict dict → ∀ Kf : Subgroup (GA D V), IsLevelK V l.M Kf → DictIsUnif V dict Kf C.th C.hr := by
  intro D H Dw l Xo c σ V r C hC dict hd Kf hK
  obtain ⟨h1, h2, h3, -, -⟩ := _root_.GlobalTheory.Member.dict_invariant D H Dw l Xo c σ V r C hC dict hd Kf hK
  obtain ⟨h4, h5⟩ := _root_.GlobalTheory.Member.dict_real_equivariant_onto D H Dw l Xo c σ V r C hC dict hd
  refine ⟨h1, h2, ⟨fun k => C.fr 1 k, fun k => ⟨(_root_.GlobalTheory.Member.fr_orthonormal_unit D H Dw l Xo c σ V r C hC 1 k).2.1, hd.2 k⟩, h4⟩,
    h3, h5, ?_⟩
  rintro g g' ⟨δ, hδ, he⟩
  obtain ⟨γ, hγ, hf⟩ := hd.1 g
  obtain ⟨γ', hγ', hf'⟩ := hd.1 g'
  rw [he] at hγ' hf'
  dsimp only at hγ' hf'
  obtain ⟨γ₁, hγ₁, hm, hfr⟩ := (_root_.GlobalTheory.Member.mark_move D H Dw l Xo c σ V r C hC g _ γ hγ).2.2.2 δ hδ
  have hk := _root_.GlobalTheory.Member.mem_level_of_mark_of_frame_eq D H Dw l Xo c σ V r C hC Kf hK g g' _ _ _ hm hγ' (by rw [hfr, ← hf, hf'])
  refine ⟨γ'⁻¹ * (γ₁ * γ), mul_mem (inv_mem hγ'.1) hm.1, _, hk, ?_⟩
  group

end GlobalTheory.Member
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFrameUniformisationPrescribedSpace
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem exists_unf_of_space : N1c → GlobalTheory.Published.HasseNormSt → Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)), 1 ≤ Dw.p + Dw.q → GoodEmb c σ → cc ξ₀ = -ξ₀ → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ₀).im < 0) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ x) (φ y))) → ∃ U : Unf Xo c σ r, IsUnf U ∧ Nonempty U.Comp ∧ (∀ k la γ, (U.X k).χ la γ = 1) ∧ (∀ k, (U.X k).Gm = Gm ∧ (U.X k).ξ0 = ξ₀) ∧ (∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x)) ∧ ∀ ρ, FJ.LatZ U.X ρ ∧ (l.A = 1 → FJ.ExpoMatch U.X 1 ρ l.M) := by
  intro hN hH hB hT E _ _ _ H Dw l Xo c σ r ξ₀ Gm φ hpq hσ hξ hneg hφ
  classical
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨F⟩ := hN E H Dw l Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) _
    (fun j => relab c σ (e j).1) hpq hσ ((_root_.GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw _ e)
  obtain ⟨M, hM, hX, hG⟩ := _root_.GlobalTheory.ModelsExist.exists_modelsOf hH E H Dw l Xo _ _ _ F r ξ₀ Gm φ hξ hneg hφ
  obtain ⟨un, hun⟩ := _root_.GlobalTheory.FrameUnif.exists_framesOK hB hT E H Dw l Xo c σ _ e F r M hσ hM hX
  have hred : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  refine ⟨unfOf e F M un, _root_.GlobalTheory.FrameUnif.isUnf_built hB E H Dw l Xo c σ _ e F r M un hσ hM hX hun, ⟨⟨0, F.n_pos⟩⟩, hM.chi, hG,
    fun k x => _root_.GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c (CAt σ) _, fun ρ => ⟨_root_.GlobalTheory.CuspCentre.latZ E r ρ _ _, fun hA => ?_⟩⟩
  exact _root_.GlobalTheory.ExpoModels.expoMatch_models E H Dw l Xo _ _ _ F r M ρ hM hA

end GlobalTheory.FrameUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeLinearMapConjugateSplitPoint
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
open GlobalTheory.ConjSplit hiding exists_lin exists_conj_lattice_map

namespace GlobalTheory.ConjSplitAnyLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Fam

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  (F : FamilyUnif Xo σ ty) {i : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di i) ty P)

theorem exists_lin (h₁ : 1 ≤ D.p + D.q) (h₂ : σ (baseKA l).ρ = H.rt0) (h₃ : IsTypeFn H D.p D.q ty)
    (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left) {i' : Fin F.n} {P' : (F.Di i').La →+ (Fin g → ℂ)}
    (hP' : IsPeriod (F.Di i') ty P') (U : Over.mk (F.u i' P') ⟶ Over.mk (F.u i P)) (f : ℂ → ℂ)
    (hadd : ∀ z w, ∃ a, f (z + w) - (f z + f w) = wC H a)
    (hw : ∀ z, ∃ a, f (wC H (0, 1) * z) - wC H (0, 1) * f z = wC H a)
    (hf : ∀ z, C.pt z ≫ io = U.left ≫ C.pt (f z)) (ε : ℤˣ) :
    ∃ Φ : lat hP (((ε : ℤ) : ℂ) * H.rt0) →ₗ[𝓞 E] (F.Di i').La,
      (∀ a, Φ a ∈ lat hP' (((ε : ℤ) : ℂ) * H.rt0)) ∧
      ∀ a (z : ℂ), F.ex i' P' (z • P' (Φ a)) = U ≫ F.ex i P (f z • P a) := by
  have key : ∀ a : lat hP (((ε : ℤ) : ℂ) * H.rt0), ∃ a' ∈ lat hP' (((ε : ℤ) : ℂ) * H.rt0),
      ∀ z : ℂ, U ≫ F.ex i P (f z • P a) = F.ex i' P' (z • P' a') := by
    rintro ⟨a, ha⟩
    obtain ⟨φ, -, hφ⟩ := _root_.GlobalTheory.CompRat.exists_hom_of_pureType_of_level E H D l Xo σ g ty F h₁ h₂ h₃ C i P hP ε a ha
    have hx : ∀ z w, F.ex i P (f (z + w) • P a) = F.ex i P (f z • P a) * F.ex i P (f w • P a) := fun z w => by
      rw [ex_congr_type F hP ε ha (hadd z w), add_smul, F.ex_add i P hP]
    refine _root_.GlobalTheory.CurveHomLiftAnyLevel.exists_pure_vector E H D l Xo σ g ty F h₁ h₂ h₃ C i' P' hP' (io ≫ φ) (fun z => U ≫ F.ex i P (f z • P a)) ε
      (fun z => ?_) (fun z w => ?_) (fun z => ?_)
    · rw [← Category.assoc, hf, Category.assoc, hφ]; rfl
    · show U ≫ _ = (U ≫ _) * (U ≫ _)
      rw [hx, MonObj.comp_mul]
    · show U ≫ _ = (U ≫ _) ≫ _
      rw [Category.assoc, ← ex_smul F hP, period_w0_smul hP ha, smul_smul]
      congr 1
      have e0 : wC H (0, 1) = (1 + H.rt0) / 2 := by simp [wC]
      rw [e0] at hw
      rcases Int.units_eq_one_or ε with rfl | rfl
      · refine ex_congr_type F hP 1 ha ?_
        simpa [mul_comm] using hw z
      · have e1 := hx ((1 + -H.rt0) / 2 * z) ((1 + H.rt0) / 2 * z)
        rw [ex_congr_type F hP _ ha (hw z), ← F.ex_add i P hP, ← add_smul,
          show (1 + -H.rt0) / 2 * z + (1 + H.rt0) / 2 * z = z by ring] at e1
        have e2 := (F.ex_ker i P hP ((f ((1 + -H.rt0) / 2 * z) + (1 + H.rt0) / 2 * f z - f z) • P a)).1 (by
          have e3 := F.ex_add i P hP ((f ((1 + -H.rt0) / 2 * z) + (1 + H.rt0) / 2 * f z - f z) • P a) (f z • P a)
          rw [← add_smul, sub_add_cancel, ← e1] at e3
          exact mul_eq_right.1 e3.symm)
        refine ex_congr F hP ?_
        rw [← sub_smul]
        convert e2 using 2
        simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul]
        ring
  choose Φ hΦ hex using key
  refine ⟨{ toFun := Φ, map_add' := fun a b => ?_, map_smul' := fun s a => ?_ }, hΦ, fun a z => (hex a z).symm⟩
  · refine eq_of_ex F hP' fun z => ?_
    rw [map_add (f := _), smul_add, F.ex_add i' P' hP', ← hex, ← hex, ← hex, Submodule.coe_add, map_add (f := _), smul_add,
      F.ex_add i P hP, MonObj.comp_mul]
  · refine eq_of_ex F hP' fun z => ?_
    rw [RingHom.id_apply, ex_smul F hP', ← hex, ← hex, Submodule.coe_smul, ex_smul F hP, Category.assoc]

end Fam

theorem exists_conj_lattice_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left), IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (i' : Fin F.n) (P' : (F.Di i').La →+ (Fin g → ℂ)) (hP' : IsPeriod (F.Di i') ty P'), IsSplit hP → spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P' → ∃ Φ : (F.Di i).La →ₗ[𝓞 E] (F.Di i').La, Function.Injective Φ ∧ (∀ a, Φ a ∈ lat hP' H.rt0 ↔ a ∈ lat hP H.rt0) ∧ (∀ a, Φ a ∈ lat hP' (-H.rt0) ↔ a ∈ lat hP (-H.rt0)) ∧ ∀ (n : ℕ) (s : ℤ × ℤ), 0 < n → C.ActsBy τ io n s → ∀ a ∈ lat hP H.rt0, ∀ b ∈ lat hP (-H.rt0), spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P (a + b))).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' (Φ (wE H s • a + H.bar (wE H s) • b)))).left := by
  intro E _ _ _ H D l Xo σ g ty F h₁ h₂ h₃ τ hτ C io hio i P hP i' P' hP' hsp hu
  obtain ⟨f, hadd, hw, hon, hact, hf⟩ := exists_param C τ hτ io hio
  let U : Over.mk (F.u i' P') ⟶ Over.mk (F.u i P) := Over.homMk (spMap (τ : ℂ →+* ℂ)) hu
  have hU : ∀ x y : Over.mk (F.u i P) ⟶ Xo.univ.t.G, U ≫ x = U ≫ y → x = y := fun x y h =>
    Over.OverMorphism.ext (spMap_cancel τ (congrArg (fun m => m.left) h))
  have key : ∀ (ε : ℤˣ) (ρ : ℂ), ((ε : ℤ) : ℂ) * H.rt0 = ρ → ∃ Φ : lat hP ρ →ₗ[𝓞 E] (F.Di i').La,
      (∀ a, Φ a ∈ lat hP' ρ) ∧ (∀ a, Φ a = 0 → a = 0) ∧ ∀ (n : ℕ) (s : ℤ × ℤ), C.ActsBy τ io n s → ∀ a : lat hP ρ,
        U ≫ F.ex i P ((n : ℂ)⁻¹ • P a) = F.ex i' P' ((n : ℂ)⁻¹ • wC H s • P' (Φ a)) := by
    rintro ε _ rfl
    obtain ⟨Φ, hΦ, hex⟩ := exists_lin F hP h₁ h₂ h₃ C io hP' U f hadd hw hf ε
    refine ⟨Φ, hΦ, fun a ha => Subtype.ext (eq_of_ex F hP fun z' => ?_), fun n s hA a => ?_⟩
    · obtain ⟨z, hz⟩ := hon z'
      rw [← ex_congr_type F hP ε a.2 hz, ← ex_congr_type F hP ε (Submodule.coe_mem 0) hz]
      apply hU
      rw [← hex, ← hex, ha, map_zero Φ]
    · rw [smul_smul, mul_comm (n : ℂ)⁻¹, ← div_eq_mul_inv, hex, ex_congr_type F hP ε a.2 (hact n s hA), one_div]
  obtain ⟨Φp, hp, ip, tp⟩ := key 1 H.rt0 (by simp)
  obtain ⟨Φm, hm, im, tm⟩ := key (-1) (-H.rt0) (by simp)
  have hc : IsCompl (lat hP H.rt0) (lat hP (-H.rt0)) := ⟨disjoint_lat hP rt0_ne_neg, codisjoint_iff.2 hsp⟩
  have hd := Submodule.disjoint_def.1 (disjoint_lat hP (rt0_ne_neg (H := H)))
  have hd' := Submodule.disjoint_def.1 (disjoint_lat hP' (rt0_ne_neg (H := H)))
  have hdec : ∀ x, ∃ (a : lat hP H.rt0) (b : lat hP (-H.rt0)), x = a.1 + b.1 := fun x => by
    obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 ((show lat hP H.rt0 ⊔ lat hP (-H.rt0) = ⊤ from hsp) ▸
      Submodule.mem_top (x := x))
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, e.symm⟩
  have hΦ : ∀ (a : lat hP H.rt0) (b : lat hP (-H.rt0)),
      LinearMap.ofIsCompl hc Φp Φm (a.1 + b.1) = Φp a + Φm b := fun a b => by
    rw [map_add (f := _), LinearMap.ofIsCompl_apply_left, LinearMap.ofIsCompl_apply_right]
  refine ⟨LinearMap.ofIsCompl hc Φp Φm, (injective_iff_map_eq_zero _).2 fun x hx => ?_, fun x => ?_, fun x => ?_,
    fun n s _ hA a ha b hb => ?_⟩
  · obtain ⟨a, b, rfl⟩ := hdec x
    rw [hΦ] at hx
    have e : Φp a = 0 := hd' _ (hp a) (by rw [eq_neg_of_add_eq_zero_left hx]; exact neg_mem (hm b))
    rw [e, zero_add] at hx
    rw [ip a e, im b hx]; simp
  · obtain ⟨a, b, rfl⟩ := hdec x
    rw [hΦ, Submodule.add_mem_iff_right _ (hp a), Submodule.add_mem_iff_right _ a.2]
    constructor
    · intro h
      rw [im b (hd' _ h (hm b))]; simp
    · intro h
      rw [show b = 0 from Subtype.ext (hd _ h b.2)]; simp
  · obtain ⟨a, b, rfl⟩ := hdec x
    rw [hΦ, Submodule.add_mem_iff_left _ (hm b), Submodule.add_mem_iff_left _ b.2]
    constructor
    · intro h
      rw [ip a (hd' _ (hp a) h)]; simp
    · intro h
      rw [show a = 0 from Subtype.ext (hd _ a.2 h)]; simp
  · have e := hΦ (wE H s • ⟨a, ha⟩) (H.bar (wE H s) • ⟨b, hb⟩)
    rw [map_smul, map_smul] at e
    have e' : LinearMap.ofIsCompl hc Φp Φm (wE H s • a + H.bar (wE H s) • b) = _ := e
    rw [e', map_add P', period_wE hP' (hp _), period_bar_wE hP' (hm _), smul_add, F.ex_add i' P' hP', ← tp n s hA,
      ← tm n s hA, ← MonObj.comp_mul, ← F.ex_add i P hP, ← smul_add, ← map_add]
    rfl

end GlobalTheory.ConjSplitAnyLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsWeightZeroSectionOfPeriodSpaceFunctionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weightZero_section_of_periodSpace_function : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), 1 ≤ D.p + D.q → (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → FnAlgClosed (Xo := Xo) (c := c) → ∀ v : Fin F.n → c.F, ∃ f ∈ sec Xo c 0 0, (∀ m : ℕ, (∀ i, v i ^ m = 1) → f ^ m = 1) ∧ ∀ (y : FrPt Xo c (CAt σ)) (i : Fin F.n) P, IsPeriod (F.Di i) ty P → y.x = F.u i P → Formalism.L2.PjFree.toC (evR Xo c f y) = σ (v i) := by
  first | exact @GlobalTheory.CompFun.exists_section_of_function | exact GlobalTheory.CompFun.exists_section_of_function | (intros; apply GlobalTheory.CompFun.exists_section_of_function <;> assumption)
end

