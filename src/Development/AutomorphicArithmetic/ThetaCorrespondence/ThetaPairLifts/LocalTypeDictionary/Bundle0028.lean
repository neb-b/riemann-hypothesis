module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorDualPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0545
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0570
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0012
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0022
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationDenominatorsAndHostFieldSizes
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0007
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.ImportsTer
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0008
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0004
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2121
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PureThetaIntegralContinuousOrthogonal
section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Filter Topology MeasureTheory
open GlobalTheory.WeilM
noncomputable section
namespace GlobalTheory.SoPureThetaCont
theorem continuous_pure_theta_integral : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → Decay B G om om' →
    ∀ φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
      (∀ᶠ v in cofinite, φ v = G.M'.vac v) → φ B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁ →
      ∀ h, Continuous fun f : SInf F (Fin a' × Fin (a + a')) => G.M'.I om' (pure f φ) h := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT hD φ hSB hev hSo h
  have hPair := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).2
  have hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    (hev.and hT.geo.hM'.std).mono fun v hv => hv.1.trans hv.2
  let A : (Fin a' × Fin (a + a') → Af F) → ℂ := fun z => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (z i)
  have hA : A ∈ SB (Fin a' × Fin (a + a') → Af F) := GlobalTheory.AdelicCoordSB.finprod_mem_SB F _ φ hSB hstd
  have heq : ∀ u : SInf F (Fin a' × Fin (a + a')), pure u φ = pureA F u A := fun _ => rfl
  have hso : ∀ u : SInf F (Fin a' × Fin (a + a')), pure u φ ∈ G.M'.So B.ψ B.τ₁ := fun u =>
    Submodule.subset_span ⟨u, φ, hSB, hev, hSo, rfl⟩
  have hsch : ∀ u : SInf F (Fin a' × Fin (a + a')), pure u φ ∈ schA F _ := fun u =>
    GlobalTheory.TensUniq.pure_mem_schA u φ hSB hstd
  have hpres : ∀ x, ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), om' x Φ ∈ schA F _ := fun x Φ hΦ =>
    hPair.weil.isUSplitting.pres x Φ hΦ
  have hconv : ∀ u : SInf F (Fin a' × Fin (a + a')), IntegrableOn (fun g => theta om' (pure u φ) g h) G.M'.dom G.M'.μ :=
    fun u => (hD.2 _ (hso u)).2.1 h
  have hadd : ∀ (u u' : SInf F (Fin a' × Fin (a + a'))) g,
      theta om' (pure (u + u') φ) g h = theta om' (pure u φ) g h + theta om' (pure u' φ) g h := by
    intro u u' g
    have e : pure (u + u') φ = pure u φ + pure u' φ := funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
    simp only [theta, e, map_add (f := _)]
    exact thetaSum_add F (hpres _ _ (hsch u)) (hpres _ _ (hsch u'))
  have hsmul : ∀ (c : ℂ) (u : SInf F (Fin a' × Fin (a + a'))) g,
      theta om' (pure (c • u) φ) g h = c * theta om' (pure u φ) g h := by
    intro c u g
    have e : pure (c • u) φ = c • pure u φ := funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
    simp only [theta, e, map_smul]
    exact thetaSum_smul F c _
  have hcontg : ∀ g, Continuous fun u : SInf F (Fin a' × Fin (a + a')) => theta om' (pure u φ) g h := fun g =>
    (_root_.GlobalTheory.ThKBasic.theta_kernel_basic_properties hP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hPair).2 A hA g h
  let μd := G.M'.μ.restrict G.M'.dom
  let T : SInf F (Fin a' × Fin (a + a')) → UA σ G.V'.J → ℂ := fun u g => theta om' (pure u φ) g h
  have hfin : ∀ u, (∫⁻ g, ‖T u g‖ₑ ∂μd) ≠ ⊤ := fun u => (hconv u).2.ne
  have hν : ∀ u, ∫ g, ‖T u g‖ ∂μd = (∫⁻ g, ‖T u g‖ₑ ∂μd).toReal := fun u =>
    integral_norm_eq_lintegral_enorm (hconv u).1
  let ν : Seminorm ℂ (SInf F (Fin a' × Fin (a + a'))) :=
    Seminorm.of (fun u => ∫ g, ‖T u g‖ ∂μd)
      (fun u u' => by
        calc ∫ g, ‖T (u + u') g‖ ∂μd ≤ ∫ g, (‖T u g‖ + ‖T u' g‖) ∂μd :=
              integral_mono (hconv (u + u')).norm ((hconv u).norm.add (hconv u').norm)
                fun g => by simp only [T]; rw [hadd]; exact norm_add_le _ _
          _ = _ := integral_add (hconv u).norm (hconv u').norm)
      (fun c u => by
        simp only [T, hsmul, norm_mul]
        exact integral_const_mul _ _)
  haveI : BarrelledSpace ℂ (SInf F (Fin a' × Fin (a + a'))) := by
    classical exact GlobalTheory.schwartzMap_barrelledSpace _
  have hN : LowerSemicontinuous fun u => ∫⁻ g, ‖T u g‖ₑ ∂μd := by
    rw [lowerSemicontinuous_iff_le_liminf]
    intro u
    calc ∫⁻ g, ‖T u g‖ₑ ∂μd ≤ ∫⁻ g, liminf (fun u' => ‖T u' g‖ₑ) (𝓝 u) ∂μd :=
          lintegral_mono fun g => (((hcontg g).tendsto u).enorm.liminf_eq).ge
      _ ≤ _ := lintegral_liminf_le' fun u' => (hconv u').1.enorm
  have hνc : Continuous ν := by
    refine Seminorm.continuous_of_lowerSemicontinuous ν fun u y hy => ?_
    by_cases hy0 : y < 0
    · exact Filter.Eventually.of_forall fun u' => hy0.trans_le (apply_nonneg ν u')
    · push_neg at hy0
      have hy' : y < (∫⁻ g, ‖T u g‖ₑ ∂μd).toReal := by rw [← hν]; exact hy
      have h1 : ENNReal.ofReal y < ∫⁻ g, ‖T u g‖ₑ ∂μd := (ENNReal.ofReal_lt_iff_lt_toReal hy0 (hfin _)).2 hy'
      filter_upwards [hN u _ h1] with u' hu'
      show y < ∫ g, ‖T u' g‖ ∂μd
      rw [hν]
      exact (ENNReal.ofReal_lt_iff_lt_toReal hy0 (hfin _)).1 hu'
  let L : SInf F (Fin a' × Fin (a + a')) →+ ℂ :=
    { toFun := fun u => G.M'.I om' (pure u φ) h
      map_zero' := by
        show ∫ g, T 0 g ∂μd = 0
        have : ∀ g, T 0 g = 0 := fun g => by
          simpa using hsmul 0 0 g
        simp [this]
      map_add' := fun u u' => by
        show ∫ g, T (u + u') g ∂μd = ∫ g, T u g ∂μd + ∫ g, T u' g ∂μd
        simp only [T, hadd]
        exact integral_add (hconv u) (hconv u') }
  have hLb : ∀ u, ‖L u‖ ≤ ν u := fun u => norm_integral_le_integral_norm _
  have hL : Continuous L := by
    refine continuous_of_continuousAt_zero L ?_
    rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun u => norm_nonneg _) hLb ?_
    simpa using hνc.tendsto (0 : SInf F (Fin a' × Fin (a + a')))
  exact hL
end GlobalTheory.SoPureThetaCont
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_theta_integral_continuous_orthogonal : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → Decay B G om om' →
    ∀ φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
      (∀ᶠ v in cofinite, φ v = G.M'.vac v) → φ B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁ →
      ∀ h, Continuous fun f : SInf F (Fin a' × Fin (a + a')) => G.M'.I om' (pure f φ) h := by
  first | exact @_root_.GlobalTheory.SoPureThetaCont.continuous_pure_theta_integral | exact _root_.GlobalTheory.SoPureThetaCont.continuous_pure_theta_integral | (intros; apply _root_.GlobalTheory.SoPureThetaCont.continuous_pure_theta_integral <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SplitLeftScalarFactorEqOne
section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
noncomputable section
namespace GlobalTheory.SplitScalarV
theorem scalar_eq_one_of_split_left : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, ∀ c : ℂ, Acts (evFin F v) (om' (k, 1)) (G.M'.vac v) (c • G.M'.vac v) → c = 1 := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hsp hT hψ h2 hvac k hk c hc
  obtain ⟨d', hd', -, dd, omd, hdc, hws, hres⟩ := hTr.weil'.2.1
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (Fin a' × Fin (a + a')) v
  have hV := hTr.geo.hM'.vac v
  have hSB : G.M'.vac v ∈ SB _ := hV.1
  have hne : G.M'.vac v ≠ 0 := hV.2.1
  have hRv := hR _ hSB
  set Ψ := tens (evFin F v) (G.M'.vac v) R with hΨdef
  have hΨ : Ψ ∈ schA F _ := hRv.2
  have hΨ' : (fun x => star (Ψ x)) ∈ schA F _ := GlobalTheory.SchAConj.star_mem_schA F _ Ψ hΨ
  let H : Subgroup (GlobalTheory.InertDbl.UD σ G.V') :=
    { carrier := {g | omd g (GlobalTheory.InertDbl.dblFun Ψ) = GlobalTheory.InertDbl.dblFun Ψ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hgen := (GlobalTheory.T.antidiagonalUnipotent_conj_siegel_square_split) F E σ B a a' G X om om' hTr v hsp hψ h2 k hk
  have hle : Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.V' v ∪ GlobalTheory.InertDbl.NabD σ G.V' v) ≤ H := by
    rw [Subgroup.closure_le]
    rintro g (hg | hg)
    · exact (_root_.GlobalTheory.T.split_parallel_derivative_left_fixed) hP F E σ B a a' G X om om' hTr v hsp hT hψ h2 hvac d' hd' dd omd hdc hws R hR0 hRv g hg
    · exact (_root_.GlobalTheory.T.nabla_fixed_split_subspace) hP F E σ B a a' G X om om' hTr v hsp hT hψ h2 hvac d' hd' dd omd hdc hws R hR0 hRv g hg
  have hfix : omd (GlobalTheory.InertDbl.inlD σ G.V' k) (GlobalTheory.InertDbl.dblFun Ψ) = GlobalTheory.InertDbl.dblFun Ψ := hle hgen
  have hact : om' (k, 1) Ψ = c • Ψ := by
    rw [hΨdef, hc R hRv]
    funext x
    simp [tens, mul_assoc]
  have hr := hres k (GlobalTheory.InertDbl.inlD σ G.V' k) rfl Ψ hΨ (fun x => star (Ψ x)) hΨ'
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply] at hr
  rw [hact] at hr
  have key : c • GlobalTheory.InertDbl.dblFun Ψ = GlobalTheory.InertDbl.dblFun Ψ := by
    have e1 : omd (GlobalTheory.InertDbl.inlD σ G.V' k) (GlobalTheory.InertDbl.dblFun Ψ) = c • GlobalTheory.InertDbl.dblFun Ψ := by
      unfold GlobalTheory.InertDbl.dblFun
      rw [hr]
      funext x
      simp only [boxFun, Pi.smul_apply, smul_eq_mul]
      ring
    rw [← e1, hfix]
  obtain ⟨y, hy⟩ : ∃ y, G.M'.vac v y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  let x : Fin a' × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
  have hRx : R x = R 0 := by
    have := hRv.1 0 x (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
    simpa using this
  have hΨx : Ψ x ≠ 0 := by
    simp only [hΨdef, tens, x, GlobalTheory.LatVac.evFin_liftV, hRx]
    exact mul_ne_zero hy hR0
  have h2' := congrFun key (Sum.elim x x)
  simp only [GlobalTheory.InertDbl.dblFun, boxFun, Pi.smul_apply, smul_eq_mul] at h2'
  have hz : Ψ x * star (Ψ x) ≠ 0 := mul_ne_zero hΨx (star_ne_zero.mpr hΨx)
  have h3 : (Sum.elim x x ∘ Sum.inl : Fin a' × Fin (a + a') → AF F) = x := rfl
  have h4 : (Sum.elim x x ∘ Sum.inr : Fin a' × Fin (a + a') → AF F) = x := rfl
  rw [h3, h4] at h2'
  exact (mul_eq_right₀ hz).mp h2'
end GlobalTheory.SplitScalarV
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_left_scalar_factor_eq_one : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E)
    (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, ∀ c : ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (k, 1)) (G.M'.vac v) (c • G.M'.vac v) → c = 1 := by
  first | exact @_root_.GlobalTheory.SplitScalarV.scalar_eq_one_of_split_left | exact _root_.GlobalTheory.SplitScalarV.scalar_eq_one_of_split_left | (intros; apply _root_.GlobalTheory.SplitScalarV.scalar_eq_one_of_split_left <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SumSizeBoundFinitePlaces
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open GlobalTheory.SumSize
namespace GlobalTheory.SumSize
theorem finite_place_sum_size_bound (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hI : ∀ D, GlobalTheory.NormSum.Inp D) (hD : DictK) (hd : DepthK) : FinRowK := by
  have hG : PairInt.PairIntRatK := _root_.GlobalTheory.T.pairIntRatK_of_thetaLocalInputs hP hI hD
  obtain ⟨CF0, h⟩ := BigC.and hG hd
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨C0, h⟩ := h CF hCF
  refine ⟨C0, fun ε C hC => ?_⟩
  obtain ⟨x0, h⟩ := h ε C hC
  refine ⟨x0, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch h1 h2 h3 => ?_⟩
  obtain ⟨⟨dl, hL, h⟩, hDe⟩ := h D large₂ he hx Γ Pl0 T A Ks R F hS ch h1 h2 h3
  refine ⟨dl, hL, ?_⟩
  intro t w hw Φ β d hO c i a v hv
  obtain ⟨hβ, τ, hτ, hdτ⟩ := hO
  have hrat := (h3.isRatAt hβ hτ hdτ c).2 i
  obtain ⟨hk, ⟨e, -, hPz, -⟩, hcos⟩ := hτ
  have hdep := (hDe t Φ β hβ).2
  exact h t (.chi i D.R.m) ⟨i.2, rfl⟩ w hw _ (d.2 i) hk ((hcos d hdτ).2 i) ((hPz d hdτ).2 i).2.2 ((hPz d hdτ).2 i).1
    (fun l hl hlw => hdep w l hl hlw hw) _ _ hrat a v hv
end GlobalTheory.SumSize
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_size_bound_finite_places : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → FinRowK := by
  first | exact @_root_.GlobalTheory.SumSize.finite_place_sum_size_bound | exact _root_.GlobalTheory.SumSize.finite_place_sum_size_bound | (intros; apply _root_.GlobalTheory.SumSize.finite_place_sum_size_bound <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaIntegralCompRightTranslate
section
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
noncomputable section
namespace GlobalTheory.ThetaRightTranslate
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem thetaIntegral_rightTranslate_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ g ∈ UAt σ X (evI F), ∀ (h : UA σ W.J) (Φ : (Fin n × Fin d → AF F) → ℂ),
      Φ ∈ schA F (Fin n × Fin d) → ∀ y, M.I om (om (g, h) Φ) y = M.I om Φ (y * h) := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp g _ h Φ hΦ y
  have hTB := _root_.GlobalTheory.T.theta_kernel_fundamental_properties hP F E σ B n d X W M χX χW om r s r' s' hp
  have hinv : ∀ γ ∈ ratU σ X.J, ∀ x, theta om Φ (γ * x) (y * h) = theta om Φ x (y * h) := by
    intro γ hγ x
    have := (hTB.1 Φ hΦ).2.1 γ hγ 1 (one_mem _) x (y * h)
    rwa [one_mul] at this
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI := hp.good.haar
  haveI : M.μ.IsMulRightInvariant := isMulRightInvariant σ hp.base.cm X.J hp.herm.herm
    (GlobalTheory.isUnit_det_of_isHerm F E σ B n X r s hp.herm) M.μ
  haveI := countable_ratU σ X.J
  haveI : MeasurableConstSMul (ratU σ X.J) (UA σ X.J) := ⟨fun c => measurable_const_mul (c : UA σ X.J)⟩
  haveI : SMulInvariantMeasure (ratU σ X.J) (UA σ X.J) M.μ :=
    ⟨fun c s _ => measure_preimage_mul M.μ (c : UA σ X.J) s⟩
  have hL : M.I om (om (g, h) Φ) y = ∫ x in M.dom, theta om Φ (x * g) (y * h) ∂M.μ := by
    unfold Model.I theta
    congr 1
    funext x
    rw [← Module.End.mul_apply, ← map_mul]
    rfl
  have hmp := measurePreserving_mul_right M.μ g
  have h1 := hmp.setIntegral_preimage_emb (measurableEmbedding_mulRight g) (fun x => theta om Φ x (y * h))
    ((fun x : UA σ X.J => x * g⁻¹) ⁻¹' M.dom)
  have hpre : (fun x : UA σ X.J => x * g) ⁻¹' ((fun x : UA σ X.J => x * g⁻¹) ⁻¹' M.dom) = M.dom := by
    ext x; simp
  rw [hpre] at h1
  have hfd' : IsFundamentalDomain (ratU σ X.J) ((fun x : UA σ X.J => x * g⁻¹) ⁻¹' M.dom) M.μ :=
    hp.good.dom.preimage_of_equiv (measurePreserving_mul_right M.μ g⁻¹).quasiMeasurePreserving
      (e := id) Function.bijective_id (fun γ x => by
        show (γ.1 * x) * g⁻¹ = γ.1 * (x * g⁻¹)
        exact mul_assoc _ _ _)
  have h2 := hfd'.setIntegral_eq hp.good.dom (f := fun x => theta om Φ x (y * h)) (fun γ x => hinv γ.1 γ.2 x)
  rw [hL, h1, h2]
  rfl
end GlobalTheory.ThetaRightTranslate
end
end

section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaIntegral_comp_rightTranslate : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ g ∈ UAt σ X (evI F), ∀ (h : UA σ W.J) (Φ : (Fin n × Fin d → AF F) → ℂ),
      Φ ∈ schA F (Fin n × Fin d) → ∀ y, M.I om (om (g, h) Φ) y = M.I om Φ (y * h) := by
  first | exact @_root_.GlobalTheory.ThetaRightTranslate.thetaIntegral_rightTranslate_eq | exact _root_.GlobalTheory.ThetaRightTranslate.thetaIntegral_rightTranslate_eq | (intros; apply _root_.GlobalTheory.ThetaRightTranslate.thetaIntegral_rightTranslate_eq <;> assumption)
end
end

