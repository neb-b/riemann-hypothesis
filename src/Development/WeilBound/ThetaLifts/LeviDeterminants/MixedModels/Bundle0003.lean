module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.Bundle0001
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0136

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.DarbouxModelRationalLatticeOf
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem PositivityTheory.Mix.darboux_model_rational_lattice_of (hA : PositivityTheory.Mix.AdelSt) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) (Fin n × Fin d),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∃ (e : Fn F n d →ₗ[ℂ] Fn F n d) (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
        (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ),
        Function.Surjective ei ∧ (∀ Φ ∈ schA F (Fin n × Fin d), e Φ ∈ schA F (Fin n × Fin d)) ∧
        (∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ u Φ) = co.rho B.ψ u (e Φ)) ∧
        (∀ v, (SB _).map (ev v) = SB _) ∧
        (∀ v, (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W).IsVac B.ψ v (ev v (M.vac v))) ∧
        (∀ᶠ v in cofinite, ev v (M.vac v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
        ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v) := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB _ _ hM co _
  obtain ⟨e, ei, ev, h1, h2, h3, h4, h5, h6⟩ := hA F B.ψ hB.std (Fin n × Fin d) (M.co.e.symm.trans co.e) fun w w' => by
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, ← co.form]
    simpa only [cA, incM, LinearEquiv.apply_symm_apply] using M.co.form (M.co.e.symm w) (M.co.e.symm w')
  have hS : ∀ u, (M.co.e.symm.trans co.e) (M.co.e u) = co.e u := fun u => by simp
  refine ⟨e, ei, ev, ei.surjective, h1, fun u Φ hΦ => ?_, fun v => SetLike.coe_injective (h3 v).image_eq, fun v => ?_, ?_,
    fun f φ hφ hv => h6 f φ hφ ?_⟩
  · have := h2 (M.co.e u) Φ hΦ
    rwa [hS] at this
  · obtain ⟨hsb, hne, θ, hθ, h⟩ := hM.vac v
    refine ⟨(h3 v).1 hsb, fun e0 => hne ((h3 v).2.1 hsb (zero_mem (SB _)) (e0.trans (map_zero _).symm)), θ, hθ, fun γ hγ => ?_⟩
    have hat : At (evFin F v) γ := by
      induction hγ using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, -, x, -, y, -, rfl⟩ := hz
        exact fun u hu => by rw [smul_smul, show u * a = 0 from ha u hu, zero_smul]
      | zero => exact fun u _ => smul_zero u
      | add a b _ _ ha hb => exact fun u hu => by rw [smul_add, ha u hu, hb u hu, add_zero]
      | neg a _ ha => exact fun u hu => by rw [smul_neg, ha u hu, neg_zero]
    have := h4 v (M.co.e γ) (fun u hu => by rw [← map_smul, hat u hu, map_zero]) _ hsb _ (h γ hγ)
    rwa [hS, map_smul] at this
  · filter_upwards [hM.std, h5] with v e1 e2
    rw [e1, e2]
  · filter_upwards [hM.std, hv] with v e1 e2
    rw [e2, e1]
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.PsiUnrOfNotLe
section
noncomputable section

namespace PositivityTheory.Mix

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.Idele WithZero
open GlobalTheory.StdDual (codiff codiff_ne_zero)

variable {F : Type} [Field F] [NumberField F]

theorem psiUnr_of_not_le {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (v : HeightOneSpectrum (𝓞 F))
    (hv : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) : PsiUnr ψ v := by
  classical
  intro x
  have hc := GlobalTheory.SplitUnram.count_codiff_eq_zero v (fun h => hv (Ideal.le_of_dvd h))
  set α : Af F := GlobalTheory.AdelicU.singleFin v x with hα
  have hαv : α v = x := GlobalTheory.AdelicU.evalV_singleFin_self v x
  have hαw : ∀ w, w ≠ v → α w = 0 := fun w hw => GlobalTheory.AdelicU.evalV_singleFin_ne hw x
  have h := GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.LatVacArith.psi_fin_rat hψ) α
  have key : (∀ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (x * y) = 1) ↔
      ∀ β : Af F, (∀ w, β w ∈ w.adicCompletionIntegers F) → ψ (pairA F 0 (β * α)) = 1 := by
    constructor
    · intro H β hβ
      have e : β * α = GlobalTheory.AdelicU.singleFin v (x * β v) := by
        apply GlobalTheory.AdelicU.af_ext
        intro u
        by_cases hu : u = v
        · subst hu
          rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
          change β u * x = x * β u
          ring
        · rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
      rw [e]
      exact H _ (hβ v)
    · intro H y hy
      have e : GlobalTheory.AdelicU.singleFin v y * α = GlobalTheory.AdelicU.singleFin v (x * y) := by
        rw [hα, ← GlobalTheory.AdelicU.singleFin_mul, mul_comm]
      have := H (GlobalTheory.AdelicU.singleFin v y) (fun w => by
        by_cases hw : w = v
        · subst hw
          change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin w y) ∈ _
          rw [GlobalTheory.AdelicU.evalV_singleFin_self]
          exact hy
        · change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin v y) ∈ _
          rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw]
          exact zero_mem _)
      rw [e] at this
      exact this
  rw [key, ← h, mem_adelicIdeal_iff codiff_ne_zero, HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro H
    have := H v
    rwa [hc, neg_zero, exp_zero, hαv] at this
  · intro H w
    by_cases hw : w = v
    · subst hw
      rw [hc, neg_zero, exp_zero, hαv]
      exact H
    · rw [hαw w hw, map_zero]
      exact zero_le

end PositivityTheory.Mix
end
end

