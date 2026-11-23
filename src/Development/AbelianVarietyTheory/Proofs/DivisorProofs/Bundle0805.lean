module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaComplexConjugationCompatible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatio
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0794
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0800
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPosDefHermFormNearZeroMatrix
section
open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)

namespace GlobalTheory.PosOpen

theorem hermForm_smul_real {g : ℕ} (N : Matrix (Fin g) (Fin g) ℂ) (r : ℝ) (z : Fin g → ℂ) :
    hermForm N ((r : ℂ) • z) ((r : ℂ) • z) = ((r * r : ℝ) : ℂ) * hermForm N z z := by
  simp only [hermForm, star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  simp [Complex.conj_ofReal]
  ring

theorem posopen : ∀ {g : ℕ} (M₀ : Matrix (Fin g) (Fin g) ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M₀ z z).re) →
    ∀ᶠ C in nhds (0 : Matrix (Fin g) (Fin g) ℂ), (1 - C.map star * C).det ≠ 0 ∧ (1 - C * C.map star).det ≠ 0 ∧
      ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm (M₀ * (1 - C.map star * C)⁻¹) z z).re := by
  intro g M₀ hM
  have cA : Continuous fun C : Matrix (Fin g) (Fin g) ℂ => 1 - C.map star * C :=
    continuous_const.sub ((continuous_id.matrix_map continuous_star).matrix_mul continuous_id)
  have cB : Continuous fun C : Matrix (Fin g) (Fin g) ℂ => 1 - C * C.map star :=
    continuous_const.sub (continuous_id.matrix_mul (continuous_id.matrix_map continuous_star))
  have dA : Continuous fun C : Matrix (Fin g) (Fin g) ℂ => (1 - C.map star * C).det := cA.matrix_det
  have dB : Continuous fun C : Matrix (Fin g) (Fin g) ℂ => (1 - C * C.map star).det := cB.matrix_det
  have dA0 : (1 - (0 : Matrix (Fin g) (Fin g) ℂ).map star * 0).det ≠ 0 := by simp
  have dB0 : (1 - (0 : Matrix (Fin g) (Fin g) ℂ) * (0 : Matrix (Fin g) (Fin g) ℂ).map star).det ≠ 0 := by simp
  have e1 := dA.continuousAt.eventually_ne dA0
  have e2 := dB.continuousAt.eventually_ne dB0

  have cInv : ContinuousAt (fun C : Matrix (Fin g) (Fin g) ℂ => M₀ * (1 - C.map star * C)⁻¹) 0 := by
    have h1 : (fun C : Matrix (Fin g) (Fin g) ℂ => M₀ * (1 - C.map star * C)⁻¹) =
        fun C => M₀ * (((1 - C.map star * C).det)⁻¹ • (1 - C.map star * C).adjugate) := by
      funext C
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [h1]
    refine continuousAt_const.mul (ContinuousAt.smul (dA.continuousAt.inv₀ dA0) cA.matrix_adjugate.continuousAt)
  have cH : Continuous fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) => (hermForm p.1 p.2 p.2).re :=
    Complex.continuous_re.comp (continuous_snd.dotProduct (continuous_fst.matrix_mulVec continuous_snd.star))
  have tube : ∀ᶠ C in nhds (0 : Matrix (Fin g) (Fin g) ℂ), ∀ y ∈ Metric.sphere (0 : Fin g → ℂ) 1,
      0 < (hermForm (M₀ * (1 - C.map star * C)⁻¹) y y).re := by
    refine (isCompact_sphere (0 : Fin g → ℂ) 1).eventually_forall_of_forall_eventually fun y hy => ?_
    have cF : ContinuousAt (fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) =>
        (hermForm (M₀ * (1 - p.1.map star * p.1)⁻¹) p.2 p.2).re) (0, y) := by
      have : ContinuousAt (fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) =>
          (M₀ * (1 - p.1.map star * p.1)⁻¹, p.2)) (0, y) :=
        (ContinuousAt.comp (x := ((0 : Matrix (Fin g) (Fin g) ℂ), y))
          (f := (Prod.fst : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) → Matrix (Fin g) (Fin g) ℂ)) cInv
          continuousAt_fst).prodMk continuousAt_snd
      exact ContinuousAt.comp (x := ((0 : Matrix (Fin g) (Fin g) ℂ), y))
        (g := fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) => (hermForm p.1 p.2 p.2).re)
        (f := fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) => (M₀ * (1 - p.1.map star * p.1)⁻¹, p.2))
        cH.continuousAt this
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    have v0 : 0 < (hermForm (M₀ * (1 - (0 : Matrix (Fin g) (Fin g) ℂ).map star * 0)⁻¹) y y).re := by
      simpa using hM y hy0
    exact cF.eventually (lt_mem_nhds v0)
  filter_upwards [e1, e2, tube] with C h1 h2 h3
  refine ⟨h1, h2, fun z hz => ?_⟩
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hu : ((‖z‖⁻¹ : ℝ) : ℂ) • z ∈ Metric.sphere (0 : Fin g → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have := h3 _ hu
  rw [hermForm_smul_real, Complex.re_ofReal_mul] at this
  exact pos_of_mul_pos_right this (by positivity)

end GlobalTheory.PosOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicNumbersExtensionConjVacuumNormSq
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ConjVacuumNorm

theorem area_lamConj_pos (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (hc : StandardLatticesGL3.Crv D cc dl)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (hD : TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D cc dl) M) :
    0 < TaylorLogMetric.area (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc dl)) := by
  have g1 := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hK | hK, hT, -⟩ := GlobalTheory.ThetaConj.useBar_holds D cc dl hc M ρ hD
  · obtain ⟨cc', δ', hc', -, hl⟩ :=
      GlobalTheory.ConjCurve.galCurve_holds D cc dl hc M ρ hK hD.2.1 hD.2.2 1 one_pos
    rw [hl]
    exact GlobalTheory.ConjJet.area_pos D g1 cc' δ' hc'
  · obtain ⟨cc', δ', hc', -, hl⟩ :=
      GlobalTheory.ConjCurve.galCurve_holds D cc dl hc M _ hK hD.2.1 hD.2.2 1 one_pos
    have hL : TaylorLogMetric.lamConj M (StandardLatticesGL3.rhoBar M ρ) (TaylorLogMetric.lamOf D cc dl) =
        (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc dl)).map (starRingEnd ℂ).toAddMonoidHom :=
      congrArg TaylorLogMetric.Tor.abelian₂ hT
    rw [← GlobalTheory.ConjJet.area_conj, ← hL, hl]
    exact GlobalTheory.ConjJet.area_pos D g1 cc' δ' hc'

theorem exists_extension_normSq_eq : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (t0 : ℂ), StandardLatticesGL3.Crv D cc dl → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0 → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (ρ : M →ₐ[ℚ] ℂ), TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D cc dl) M → ∃ ρ' : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, (∀ x ∈ M, x ∈ TaylorLogMetric.Qbar ∧ StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ' x = StandardLatticesGL3.cj M ρ x) ∧ TaylorLogMetric.lamConj TaylorLogMetric.Qbar ρ' (TaylorLogMetric.lamOf D cc dl) = TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc dl) ∧ 0 < TaylorLogMetric.area (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc dl)) ∧ ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (L₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → StandardLatticesGL3.SD D L₀ → StandardLatticesGL3.SD D L₀' → Even (a * b) → ∀ F F₀ : TaylorLogMetric.VC D a b → ℂ, StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' F → StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L₀ L₀' F₀ → TaylorLogMetric.CoefIn D F₀ M → TaylorLogMetric.normSq D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ') (TaylorLogMetric.La D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ') L L') (TaylorLogMetric.fnConj D TaylorLogMetric.Qbar ρ' F) = TaylorLogMetric.normSq D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) M ρ) (TaylorLogMetric.La D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) M ρ) L₀ L₀') (TaylorLogMetric.fnConj D M ρ F₀) := by
  intro D cc dl t0 hc ht M _ ρ hD
  have g1 := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨ρ', hρ'⟩ := GlobalTheory.ThetaConj.exists_cj_Qbar_eq M ρ
  have hle : ∀ x ∈ M, x ∈ TaylorLogMetric.Qbar := fun x hx =>
    mem_algebraicClosure_iff.mpr
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (⟨x, hx⟩ : M)).algHom M.val)
  have he : ∀ x ∈ M, ρ' (TaylorLogMetric.liftM TaylorLogMetric.Qbar x) = ρ (TaylorLogMetric.liftM M x) := fun x hx =>
    (hρ' x (hle x hx) hx).symm
  have hl : TaylorLogMetric.lamConj TaylorLogMetric.Qbar ρ' (TaylorLogMetric.lamOf D cc dl) = TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc dl) := by
    unfold TaylorLogMetric.lamConj
    rw [he (TaylorLogMetric.g2 (TaylorLogMetric.lamOf D cc dl)) hD.2.1, he (TaylorLogMetric.g3 (TaylorLogMetric.lamOf D cc dl)) hD.2.2]
  refine ⟨ρ', fun x hx => ⟨hle x hx, he x hx⟩, hl, area_lamConj_pos D cc dl hc M ρ hD, ?_⟩
  intro a b L L' L₀ L₀' h1 h2 h3 h4 hev F F₀ hF hF₀ hC
  obtain ⟨hQ, -⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D g1).2 cc dl hc
  obtain ⟨hA, -⟩ := GlobalTheory.ThetaAlgebraic.taylor_algebraic D cc dl hc t0 ht a b L L' h1 h2 hev F hF
  obtain ⟨t', ht'⟩ := (GlobalTheory.TwoTorsionPt.exists_point D cc dl hc).2 M ρ hD.2.1 hD.2.2
  obtain ⟨n1, -⟩ := GlobalTheory.ConjNorm.useNorm_all D cc dl hc t0 ht a b L L' h1 h2 hev F hF
    TaylorLogMetric.Qbar ρ' hQ hA t' (hl ▸ ht')
  obtain ⟨n2, -⟩ := GlobalTheory.ConjNorm.useNorm_all D cc dl hc t0 ht a b L₀ L₀' h3 h4 hev F₀ hF₀
    M ρ hD hC t' ht'
  rw [n1, n2, hl]

end GlobalTheory.ConjVacuumNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAxisUnitGeneratorsPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT.Hecke.PullInj

noncomputable section
namespace GlobalTheory.UPel.HT.Hecke.PullInj

theorem mul_inv_axis_comm_identity {G : Type*} [CommGroup G] (a b W R₁ R₂ : G) :
    a * b⁻¹ * W * (b * R₁) * (a * R₂)⁻¹ = W * R₁ * R₂⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem axis_unit : ∀ (A₀ A₀' X X' : Scheme.{0}) (ψ : A₀ ⟶ A₀') (e : A₀ ⟶ X) (e' : A₀' ⟶ X') (π : X ⟶ X'),
    e ≫ π = ψ ≫ e' → ∀ (Q₁ Q₂ : LB X'), Q₁.IsLB → Q₂.IsLB → ∀ (w : LB.Iso (Q₁.pull π) (Q₂.pull π)), w.IsGen →
    ∀ (ρ₁ : LB.Gen (Q₁.pull e')) (ρ₂ : LB.Gen (Q₂.pull e')), ρ₁.IsGen → ρ₂.IsGen →
    ∃ g : Γ(A₀, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ A₀) (z : Z) (k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)),
      e (r z) ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k →
      gm (r ≫ e) z _ (w.s k) * gm (r ≫ ψ) z _ (ρ₁.s k.2) = gm r z ⊤ g * gm (r ≫ ψ) z _ (ρ₂.s k.1) := by
  intro A₀ A₀' X X' ψ e e' π h Q₁ Q₂ hQ₁ hQ₂ w hw ρ₁ ρ₂ hρ₁ hρ₂
  have hpt : ∀ x : A₀, π (e x) = e' (ψ x) := fun x => by
    have := congrArg (fun f : A₀ ⟶ X' => f x) h
    simpa using this
  set D := LB.div (Q₂.pull π) (Q₁.pull π)
  let W : D.ι → A₀.Opens := fun k => e ⁻¹ᵁ D.U k
  have h₁ : ∀ k : D.ι, W k ≤ ψ ⁻¹ᵁ (Q₁.pull e').U k.2 := fun k x hx => by
    have hb := (mem_divPull.1 (show e x ∈ D.U k from hx)).2
    rw [hpt] at hb
    exact mem_pull.2 hb
  have h₂ : ∀ k : D.ι, W k ≤ ψ ⁻¹ᵁ (Q₂.pull e').U k.1 := fun k x hx => by
    have hb := (mem_divPull.1 (show e x ∈ D.U k from hx)).1
    rw [hpt] at hb
    exact mem_pull.2 hb
  let u : ∀ k, Γ(A₀, W k)ˣ := fun k =>
    pullU e _ (w.s k) * res (h₁ k) (pullU ψ _ (ρ₁.s k.2)) * (res (h₂ k) (pullU ψ _ (ρ₂.s k.1)))⁻¹
  have hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ A₀) (z : Z) (k : D.ι) (hz : r z ∈ W k),
      gm r z (W k) (u k) = gm (r ≫ e) z _ (w.s k) * gm (r ≫ ψ) z _ (ρ₁.s k.2) * (gm (r ≫ ψ) z _ (ρ₂.s k.1))⁻¹ := by
    intro Z r z k hz
    simp only [u, map_mul, map_inv]
    rw [gm_res r z (h₁ k) hz, gm_res r z (h₂ k) hz, gm_pull r e z _ hz, gm_pull r ψ z _ (h₁ k hz),
      gm_pull r ψ z _ (h₂ k hz)]
  have hcov : (⊤ : A₀.Opens) ≤ iSup W := fun x _ => by
    obtain ⟨i, hi⟩ := exists_chart hQ₂ (π (e x))
    obtain ⟨j, hj⟩ := exists_chart hQ₁ (π (e x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨((fun _ => i), (fun _ => j)), mem_divPull.2 ⟨hi, hj⟩⟩
  have hcomp : ∀ k l, ∀ x ∈ W k ⊓ W l, gm (𝟙 A₀) x (W k) (u k) = gm (𝟙 A₀) x (W l) (u l) := by
    intro k l x hx
    rw [hu _ _ x k hx.1, hu _ _ x l hx.2]
    simp only [Category.id_comp]
    have hk : e x ∈ D.U k := hx.1
    have hl : e x ∈ D.U l := hx.2
    have hk' := mem_divPull.1 hk
    have hl' := mem_divPull.1 hl
    have hk₁ : ψ x ∈ (Q₁.pull e').U k.2 := h₁ k hx.1
    have hl₁ : ψ x ∈ (Q₁.pull e').U l.2 := h₁ l hx.2
    have hk₂ : ψ x ∈ (Q₂.pull e').U k.1 := h₂ k hx.1
    have hl₂ : ψ x ∈ (Q₂.pull e').U l.1 := h₂ l hx.2
    have E := gen_germ hw e x hk hl
    rw [germ_div_g _ _ e x hk hl] at E
    rw [show e = 𝟙 A₀ ≫ e from (Category.id_comp e).symm] at E
    rw [gm_pull_g Q₂ π (𝟙 A₀ ≫ e) x hk'.1 hl'.1, gm_pull_g Q₁ π (𝟙 A₀ ≫ e) x hk'.2 hl'.2] at E
    simp only [Category.id_comp] at E
    have R₁ := gen_germ hρ₁ ψ x hk₁ hl₁
    have R₂ := gen_germ hρ₂ ψ x hk₂ hl₂
    rw [show ψ = 𝟙 A₀ ≫ ψ from (Category.id_comp ψ).symm] at R₁ R₂
    rw [gm_pull_g Q₁ e' (𝟙 A₀ ≫ ψ) x (mem_pull.1 hk₁) (mem_pull.1 hl₁)] at R₁
    rw [gm_pull_g Q₂ e' (𝟙 A₀ ≫ ψ) x (mem_pull.1 hk₂) (mem_pull.1 hl₂)] at R₂
    simp only [Category.id_comp, ← h] at E R₁ R₂
    rw [E, R₁, R₂]
    exact mul_inv_axis_comm_identity _ _ _ _ _
  obtain ⟨g, hg⟩ := glue_unit (⊤ : A₀.Opens) W (fun _ => le_top) hcov u hcomp
  refine ⟨g, fun Z r z k hk => ?_⟩
  have hz : r z ∈ W k := hk
  have e₁ : gm r z ⊤ g = gm r z (W k) (u k) := by rw [← hg k, gm_res r z le_top hz]
  rw [e₁, hu Z r z k hz, inv_mul_cancel_right]

end GlobalTheory.UPel.HT.Hecke.PullInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleCorrectionSquareZeroIdeal
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBLift

namespace CocCorr

variable {R : Type} [CommRing R] {I : Ideal R}

theorem mul_eq_zero_of_mem (hI : I ^ 2 = ⊥) {S : Type} [CommRing S] [Algebra R S] {x y : S}
    (hx : x ∈ I.map (algebraMap R S)) (hy : y ∈ I.map (algebraMap R S)) : x * y = 0 := by
  have h : I.map (algebraMap R S) ^ 2 = ⊥ := by rw [← Ideal.map_pow, hI, Ideal.map_bot]
  have := Ideal.mul_mem_mul hx hy
  rw [← pow_two, h] at this
  exact (Submodule.mem_bot _).1 this

theorem map_mem {S S' : Type} [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S'] (φ : S →+* S')
    (hφ : ∀ r : R, φ (algebraMap R S r) = algebraMap R S' r) {x : S}
    (hx : x ∈ I.map (algebraMap R S)) : φ x ∈ I.map (algebraMap R S') := by
  have h := Ideal.mem_map_of_mem φ hx
  rwa [Ideal.map_map, show φ.comp (algebraMap R S) = algebraMap R S' from RingHom.ext hφ] at h

end CocCorr

open CocCorr in
theorem cocycle_of_sqZero : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = ⊥ → ∀ (D T : Type) [Category.{0} D] [Category.{0} T] (F : D ⥤ CommAlgCat.{0} R) (F' : T ⥤ CommAlgCat.{0} R) (n₀ n₁ n₂ : CoefMap (RingHom.id R) F F'), PrimI I n₀ n₁ n₂ → ∀ (u : C1 F) (v : C0 F'), (∀ t t' a, IsUnit (u t t' a)) → In2 I F (mdef F u) → (∀ t, IsUnit (v t)) → MulRel I n₀ n₁ n₂ u v → ∃ u' : C1 F, In1 I F (u' - u) ∧ mdef F u' = 0 := by
  intro R _ I hI D T _ _ F F' n₀ n₁ n₂ hP u v hu hm hv hrel

  have hmpI : ∀ {t t' : D} (b : t ⟶ t') {x : F.obj t}, x ∈ I.map (algebraMap R (F.obj t)) →
      mp F b x ∈ I.map (algebraMap R (F.obj t')) := fun b x hx ↦
    map_mem (mp F b).toRingHom (fun r ↦ (mp F b).commutes r) hx
  have hmpI' : ∀ {t t' : T} (b : t ⟶ t') {x : F'.obj t}, x ∈ I.map (algebraMap R (F'.obj t)) →
      mp F' b x ∈ I.map (algebraMap R (F'.obj t')) := fun b x hx ↦
    map_mem (mp F' b).toRingHom (fun r ↦ (mp F' b).commutes r) hx
  have hαI : ∀ (n : CoefMap (RingHom.id R) F F') (t : T) {x : F.obj (n.G.obj t)},
      x ∈ I.map (algebraMap R (F.obj (n.G.obj t))) → n.α t x ∈ I.map (algebraMap R (F'.obj t)) := by
    intro n t x hx
    refine map_mem (n.α t) (fun r ↦ ?_) hx
    rw [Algebra.algebraMap_eq_smul_one, n.smul, map_one, RingHom.id_apply, Algebra.algebraMap_eq_smul_one]

  let z : C2 F := fun t t' t'' a b ↦ mdef F u t t' t'' a b * Ring.inverse (u t t'' (a ≫ b))
  have hzI : In2 I F z := fun t t' t'' a b ↦ Ideal.mul_mem_right _ _ (hm t t' t'' a b)
  have hz_eq : ∀ {t t' t'' : D} (a : t ⟶ t') (b : t' ⟶ t''),
      mp F b (u t t' a) * u t' t'' b = u t t'' (a ≫ b) + u t t'' (a ≫ b) * z t t' t'' a b := by
    intro t t' t'' a b
    have h1 := Ring.mul_inverse_cancel _ (hu t t'' (a ≫ b))
    simp only [z, mdef]
    linear_combination (-(mp F b (u t t' a) * u t' t'' b - u t t'' (a ≫ b))) * h1

  have hz2 : z ∈ Z2 F := by
    intro t t' t'' t''' a b c
    have e1 := congrArg (mp F c) (hz_eq a b)
    simp only [map_mul, map_add (f := _), ← mp_comp] at e1
    have e2 := hz_eq (a ≫ b) c
    have e3 := hz_eq a (b ≫ c)
    have e4 := hz_eq b c
    rw [Category.assoc] at e2
    have p1 := mul_eq_zero_of_mem hI (hmpI c (hzI _ _ _ a b)) (hzI _ _ _ (a ≫ b) c)
    have p2 := mul_eq_zero_of_mem hI (hzI _ _ _ a (b ≫ c)) (hzI _ _ _ b c)
    have hU : u t t''' (a ≫ b ≫ c) * (mp F c (z t t' t'' a b) + z t t'' t''' (a ≫ b) c
        - z t t' t''' a (b ≫ c) - z t' t'' t''' b c) = 0 := by
      linear_combination (-(u t'' t''' c)) * e1 - (1 + mp F c (z t t' t'' a b)) * e2
        + (1 + z t' t'' t''' b c) * e3 + mp F (b ≫ c) (u t t' a) * e4
        - u t t''' (a ≫ b ≫ c) * p1 + u t t''' (a ≫ b ≫ c) * p2
    have := ((hu _ _ _).mul_right_eq_zero).1 hU
    linear_combination this

  let U : CoefMap (RingHom.id R) F F' → C1 F' := fun n t t' a ↦ n.α t' (u _ _ (n.G.map a))
  let W : C1 F' := fun t t' a ↦ U n₁ t t' a * U n₂ t t' a * mp F' a (v t)
  let f : C1 F' := fun t t' a ↦ (U n₀ t t' a * v t' - W t t' a) * Ring.inverse (W t t' a)
  have hUu : ∀ n t t' a, IsUnit (U n t t' a) := fun n t t' a ↦ (hu _ _ _).map (n.α t')
  have hWu : ∀ t t' a, IsUnit (W t t' a) := fun t t' a ↦
    ((hUu n₁ t t' a).mul (hUu n₂ t t' a)).mul ((hv t).map (mp F' a))
  have hfI : In1 I F' f := fun t t' a ↦ Ideal.mul_mem_right _ _ (hrel t t' a)
  have hf_eq : ∀ {t t' : T} (a : t ⟶ t'), U n₀ t t' a * v t' =
      U n₁ t t' a * U n₂ t t' a * mp F' a (v t) + U n₁ t t' a * U n₂ t t' a * mp F' a (v t) * f t t' a := by
    intro t t' a
    have h1 := Ring.mul_inverse_cancel _ (hWu t t' a)
    simp only [f]
    linear_combination (-(U n₀ t t' a * v t' - W t t' a)) * h1
  have hUeq : ∀ (n : CoefMap (RingHom.id R) F F') {t t' t'' : T} (a : t ⟶ t') (b : t' ⟶ t''),
      mp F' b (U n t t' a) * U n t' t'' b = U n t t'' (a ≫ b) +
        U n t t'' (a ≫ b) * n.α t'' (z _ _ _ (n.G.map a) (n.G.map b)) := by
    intro n t t' t'' a b
    have h := congrArg (n.α t'') (hz_eq (n.G.map a) (n.G.map b))
    simp only [map_mul, map_add (f := _), n.naturality, ← Functor.map_comp] at h
    exact h
  have hd : d1 F' f = (n₀.pullbackTwoCocycle ⟨z, hz2⟩).1 - (n₁.pullbackTwoCocycle ⟨z, hz2⟩).1 - (n₂.pullbackTwoCocycle ⟨z, hz2⟩).1 := by
    funext t t' t'' a b
    simp only [d1_apply, Pi.sub_apply, CoefMap.pullCocycleTwo_apply]
    have ra := congrArg (mp F' b) (hf_eq a)
    simp only [map_mul, map_add (f := _), ← mp_comp] at ra
    have rb := hf_eq b
    have rab := hf_eq (a ≫ b)
    have h0 := hUeq n₀ a b
    have h1 := hUeq n₁ a b
    have h2 := hUeq n₂ a b
    set a0 := mp F' b (U n₀ t t' a)
    set a1 := mp F' b (U n₁ t t' a)
    set a2 := mp F' b (U n₂ t t' a)
    set b0 := U n₀ t' t'' b
    set b1 := U n₁ t' t'' b
    set b2 := U n₂ t' t'' b
    set c0 := U n₀ t t'' (a ≫ b)
    set c1 := U n₁ t t'' (a ≫ b)
    set c2 := U n₂ t t'' (a ≫ b)
    set V := mp F' (a ≫ b) (v t)
    set V' := mp F' b (v t')
    set V'' := v t''
    set F1 := mp F' b (f t t' a)
    set F2 := f t' t'' b
    set F3 := f t t'' (a ≫ b)
    set Z0 := n₀.α t'' (z _ _ _ (n₀.G.map a) (n₀.G.map b))
    set Z1 := n₁.α t'' (z _ _ _ (n₁.G.map a) (n₁.G.map b))
    set Z2' := n₂.α t'' (z _ _ _ (n₂.G.map a) (n₂.G.map b))
    have indexFFirst : F1 ∈ I.map (algebraMap R (F'.obj t'')) := hmpI' b (hfI _ _ a)
    have indexFSecond : F2 ∈ I.map (algebraMap R (F'.obj t'')) := hfI _ _ b
    have indexFThird : F3 ∈ I.map (algebraMap R (F'.obj t'')) := hfI _ _ (a ≫ b)
    have iZ0 : Z0 ∈ I.map (algebraMap R (F'.obj t'')) := hαI n₀ t'' (hzI _ _ _ _ _)
    have iZ1 : Z1 ∈ I.map (algebraMap R (F'.obj t'')) := hαI n₁ t'' (hzI _ _ _ _ _)
    have iZ2 : Z2' ∈ I.map (algebraMap R (F'.obj t'')) := hαI n₂ t'' (hzI _ _ _ _ _)
    have hT : c1 * c2 * V * V' * ((1 + Z1) * (1 + Z2') * (1 + F1) * (1 + F2) - (1 + F3) * (1 + Z0)) = 0 := by
      linear_combination (-(a1 * a2 * V * (1 + F1))) * rb - b0 * V'' * ra
        - V * V' * (1 + F1) * (1 + F2) * (c1 * (1 + Z1) * h2 + a2 * b2 * h1) + (1 + Z0) * V' * rab + V' * V'' * h0
    have hK : IsUnit (c1 * c2 * V * V') :=
      (((hUu n₁ _ _ _).mul (hUu n₂ _ _ _)).mul ((hv t).map _)).mul ((hv t').map _)
    have hX := (hK.mul_right_eq_zero).1 hT
    linear_combination hX - (1 + F1 + F2 + F1 * F2) * mul_eq_zero_of_mem hI iZ1 iZ2
      - (1 + F2) * mul_eq_zero_of_mem hI iZ1 indexFFirst - mul_eq_zero_of_mem hI iZ1 indexFSecond
      - (1 + F2) * mul_eq_zero_of_mem hI iZ2 indexFFirst - mul_eq_zero_of_mem hI iZ2 indexFSecond
      - mul_eq_zero_of_mem hI indexFFirst indexFSecond + mul_eq_zero_of_mem hI indexFThird iZ0

  obtain ⟨f₀, hf₀I, hf₀⟩ := hP ⟨z, hz2⟩ f hzI hfI hd
  refine ⟨fun t t' a ↦ u t t' a * (1 - f₀ t t' a), fun t t' a ↦ ?_, ?_⟩
  · simp only [Pi.sub_apply]
    rw [show u t t' a * (1 - f₀ t t' a) - u t t' a = -(u t t' a * f₀ t t' a) by ring]
    exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_left _ _ (hf₀I t t' a))
  · funext t t' t'' a b
    simp only [mdef, Pi.zero_apply, map_mul, map_sub, map_one]
    have e := hz_eq a b
    have ed := congrFun (congrFun (congrFun (congrFun (congrFun hf₀ t) t') t'') a) b
    rw [d1_apply] at ed
    have iF := hmpI b (hf₀I t t' a)
    have iG := hf₀I t' t'' b
    have iz := hzI t t' t'' a b
    linear_combination (1 - mp F b (f₀ t t' a)) * (1 - f₀ t' t'' b) * e - u t t'' (a ≫ b) * ed
      + u t t'' (a ≫ b) * (1 + z t t' t'' a b) * mul_eq_zero_of_mem hI iF iG
      - u t t'' (a ≫ b) * mul_eq_zero_of_mem hI iz iF - u t t'' (a ≫ b) * mul_eq_zero_of_mem hI iz iG

end GlobalTheory.LBLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeValuationEqDiscriminant
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem exists_mem_valuation_cube_eq_Δ : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ),
    p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∀ V : ValuationSubring ℂ,
      ∃ A ∈ F, A ≠ 0 ∧ V.valuation A ^ 3 = V.valuation (latticeCurve L).Δ := by
  intro p F L t hp h4 h3 hD V
  obtain ⟨N, ι, _, T, hNodd, hN3, hNv, hcard, hst, hT⟩ := _root_.GlobalTheory.CMModel.exists_stable_family_ker p F L t hp h4 h3 hD V
  have hΔ0 := latticeCurve_Δ_ne_zero L
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (latticeCurve L).Δ (by norm_num : 0 < 12)
  have hu0 : u ≠ 0 := by rintro rfl; exact hΔ0 (by rw [← hu]; simp)
  have hvu : V.valuation u ≠ 0 := (Valuation.ne_zero_iff _).2 hu0
  have hvΔ : V.valuation (latticeCurve L).Δ = V.valuation u ^ 12 := by rw [← hu, map_pow]
  have hβ : (sqrtNegNat p).im ≠ 0 := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    simp [sqrtNegNat, Real.sqrt_ne_zero'.2 this]
  have hN3' : ¬ 3 ∣ N := by omega
  have hU := fun i => _root_.GlobalTheory.CMModel.weierstrassP_sub_two_mul_unit L (sqrtNegNat p) u V N hD.mul hβ hvΔ.symm hNv hNodd hN3' (T i)
    (hT i).1 (hT i).2
  have hmem := (_root_.GlobalTheory.CMModel.stable_sym_mem F L ι T hD.g₂_mem hD.g₃_mem hst (fun i => (hT i).1)).2.2.2
    (fun i => (hU i).1)
  have hΔmem : (latticeCurve L).Δ ∈ F := by
    rw [latticeCurve_Δ]
    exact sub_mem (pow_mem hD.g₂_mem 3)
      (mul_mem (by simpa using natCast_mem F 27) (pow_mem hD.g₃_mem 2))
  set U := ∏ i, (L.weierstrassP (T i) - L.weierstrassP (2 * T i)) with hUdef
  obtain ⟨n, hn⟩ : ∃ n, N = 3 * n + 2 := ⟨N / 3, by omega⟩
  have hvU : V.valuation U = V.valuation u ^ (12 * n) * V.valuation u ^ 4 := by
    rw [hUdef, map_prod]
    simp_rw [fun i => (hU i).2]
    rw [Finset.prod_const, Finset.card_univ, hcard, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hU0 : U ≠ 0 := by
    intro h
    rw [h, map_zero] at hvU
    exact (mul_ne_zero (pow_ne_zero _ hvu) (pow_ne_zero _ hvu)) hvU.symm
  refine ⟨U / (latticeCurve L).Δ ^ n, div_mem hmem (pow_mem hΔmem n),
    div_ne_zero hU0 (pow_ne_zero _ hΔ0), ?_⟩
  rw [map_div₀, map_pow, hvU, hvΔ, ← pow_mul, mul_comm 12 n, mul_div_cancel_left₀ _ (pow_ne_zero _ hvu),
    ← pow_mul]

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldUnitMemOpenArchimedeanUnits
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix

namespace GlobalTheory.UnitsDense

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem denseRange_embeddings' : DenseRange fun (x : E) (w : InfinitePlace E) => w.embedding x := by
  have h1 := NumberField.InfiniteAdeleRing.denseRange_algebraMap E
  have hs : Function.Surjective
      (Pi.map fun w : InfinitePlace E => InfinitePlace.Completion.extensionEmbedding w) := by
    intro y
    choose x hx using fun w : InfinitePlace E =>
      InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex (IsTotallyComplex.isComplex w) (y w)
    exact ⟨x, funext hx⟩
  have hc : Continuous (Pi.map fun w : InfinitePlace E => InfinitePlace.Completion.extensionEmbedding w) :=
    continuous_pi fun w => (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)
  have := hs.denseRange.comp h1 hc
  convert this using 1
  funext x w
  change w.embedding x = InfinitePlace.Completion.extensionEmbedding w (algebraMap E (InfiniteAdeleRing E) x w)
  rw [InfiniteAdeleRing.algebraMap_apply]
  have := InfinitePlace.Completion.extensionEmbedding_coe (v := w) ((WithAbs.equiv w.1).symm x)
  simp only [RingEquiv.apply_symm_apply] at this
  rw [← this]
  rfl

theorem exists_unit_mem_open :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (V : Set (Cinf E)ˣ), IsOpen V → V.Nonempty →
      ∃ α : Eˣ, Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom α ∈ V := by
  intro E _ _ _ V hV ⟨v, hv⟩
  have hU : IsOpen (Units.val '' V) := Units.isOpenEmbedding_val.isOpenMap V hV
  have hd : DenseRange fun x : E => pInf E (algebraMap E (Ad E) x) := by
    have : (fun x : E => pInf E (algebraMap E (Ad E) x)) = fun (x : E) (w : InfinitePlace E) => w.embedding x := by
      funext x w; exact pInf_algebraMap x w
    rw [this]; exact denseRange_embeddings'
  obtain ⟨x, u, hu, hxu⟩ := hd.exists_mem_open hU ⟨v.1, v, hv, rfl⟩
  have hx : x ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hxu
    haveI : Nonempty (InfinitePlace E) := inferInstance
    exact u.ne_zero hxu
  refine ⟨Units.mk0 x hx, ?_⟩
  convert hu using 1
  ext
  simp [hxu]

end GlobalTheory.UnitsDense
end

