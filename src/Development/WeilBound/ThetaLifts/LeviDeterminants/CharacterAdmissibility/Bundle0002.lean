module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.DetNeHerm
public import Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.LagLine
public import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.LawWLevi
public import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.LevScalar2
public import Development.WeilBound.ThetaLifts.CTKernel

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.LeavesX
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.ThKF0.Chr

theorem axX (hA : PositivityTheory.Mix.AdelSt) {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) : Ax (adeleClass F) ψ :=
  by
    have hb : AxB (adeleClass F) ψ := by
      constructor
      · exact fun κ _ => (_root_.GlobalTheory.CompanionTheory.AdelicHeis.schr_mem_and_thetaSum F κ ψ hψ.1 (isStd_ne_one hψ) hψ.2.1).1
      · intro κ _
        obtain ⟨φ, h, h0⟩ := GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F κ
        exact ⟨φ, h, fun e => h0 (congrFun e 0)⟩
      · exact fun κ _ => adelicCoordinatesEvalZeroForm_mem_admissible κ
      · exact fun κ₁ κ _ _ j hj φ hφ => GlobalTheory.RestrSchA.mem_schA_comp_extend F j hj φ hφ
      · intro κ₁ κ _ _ j hj l hl g hg
        obtain ⟨T, hT⟩ := hl _ (GlobalTheory.RestrSchA.sb_comp_extend F hj hg)
        refine ⟨T.comp (GlobalTheory.RestrSchA.restrS F hj), fun f => ?_⟩
        rw [ContinuousLinearMap.comp_apply, ← hT]
        exact congrArg l (funext fun y => GlobalTheory.RestrSchA.pureA_extend F hj f g y)
      · exact fun κ κ' _ _ => GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ'
      · exact fun κ κ' _ _ => box_adm κ κ'
    exact ⟨hb, axDelta_of lagLine hψ, axImp_of hA hψ⟩

theorem theta_tower_hermitian_first (hA : PositivityTheory.Mix.AdelSt) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ (h : UA σ W.J), ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, h) Φ) = om₁ (1, h) (e Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he
  exact e_om_one_eq_om1_one_e (axX hA hP.base.std) hP hH hP₁ he

theorem theta_tower_hermitian_second (hA : PositivityTheory.Mix.AdelSt) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ (t : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) (g₁ : UA σ X₁.J) (m : UA σ X.J), IsLevi H t g₁ m → ∀ Φ ∈ schA F (Fin n × Fin d),
        e (om (m, 1) Φ) = ((χW t : ℂ) * (((absE F E t : ℝ) ^ ((d : ℝ) / 2) : ℝ) : ℂ)) • om₁ (g₁, 1) (e Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he
  exact mixX_levi (axX hA hP.base.std) hP hH hP₁ he

end PositivityTheory.ThKF0.Chr
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.MixWOfAdel
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.ThKF0.Chr

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}
  {n d d₁ r s r' s' r₁ s₁ i₀ i₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {M : Model σ X W}
  {M₁ : Model σ X W₁} {χX χW : Chr F E} {om : Rep σ X W} {om₁ : Rep σ X W₁} {e : Fn F n d →ₗ[ℂ] Fn F n d₁}

theorem lawW_unip (hA : PositivityTheory.Mix.AdelSt) (hP : IsPair B M χX χW om r s r' s') (hH : H'.IsAdapted σ B W W₁ i₀ i₁)
    (hP₁ : IsPair B M₁ χX χW om₁ r s r₁ s₁) (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e) :
    ∀ u ∈ unip σ W H', ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, u) Φ) = e Φ := by
  have hB := hP.base
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨S, j, hS, hj, hE, hrel, -⟩ := setW hB hP.herm hP.skew hP.good hH hP₁.good he
  obtain ⟨π, ρ, hF⟩ := fr_plane hB hH hP.skew.lat (-1) (fun i j => by simp [hP.skew.skew])
  have pr : ∀ x, ∀ Ψ ∈ schA F (Fin n × Fin d), om x Ψ ∈ schA F (Fin n × Fin d) := hP.weil.isUSplitting.pres
  have hmul : ∀ u v : UA σ W.J, ∀ Φ, om (1, u * v) Φ = om (1, u) (om (1, v) Φ) := fun u v Φ => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  intro u hu
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
    choose a ha using hu.2
    have key := TU (ax_of hA hB.std) hS hj hE hF hrel hP.weil.1 hP₁.weil.1
      (parabolic_character_trivial_on_diagonal F E σ hB.cm d₁ W₁.J (-1) (fun i j => by simp [hP₁.skew.skew])
        (det_ne_of_sig _ (hP₁.skew.sig (Classical.arbitrary _)))) u 1 1 (replicateRow Unit fun k => a (Pi.single k 1)) (by
        ext i k
        have := congrFun (ha (Pi.single k 1)) i
        rw [mulVec_mulVec] at this
        simpa [mat, mul_comm, Matrix.mul_apply] using this) (by
        ext i k
        exact (congrFun hu.1 i).trans (by simp))
    intro Φ hΦ
    simpa [fac, Prod.mk_one_one] using key Φ hΦ
  | one => intro Φ _; rw [Prod.mk_one_one, map_one, Module.End.one_apply]
  | mul u v _ _ hu hv => intro Φ hΦ; rw [hmul, hu _ (pr _ _ hΦ), hv _ hΦ]
  | inv u _ hu =>
    intro Φ hΦ
    rw [← hu _ (pr _ _ hΦ), ← hmul, mul_inv_cancel, Prod.mk_one_one, map_one, Module.End.one_apply]

end PositivityTheory.ThKF0.Chr

theorem PositivityTheory.ThKF0.mixW_of_adel (hA : PositivityTheory.Mix.AdelSt) : PositivityTheory.ThKG.MixW := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he g t h₁ m hm u hu Φ hΦ
  have pr : ∀ x, ∀ Ψ ∈ schA F (Fin n × Fin d), om x Ψ ∈ schA F (Fin n × Fin d) := hP.weil.isUSplitting.pres
  have h2 : om (g, u * m) = om (g, 1) * om (1, u) * om (1, m) := by
    rw [← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_one, mul_one, one_mul]
  rw [h2, Module.End.mul_apply, Module.End.mul_apply, Chr.lawW_left hA hP hH hP₁ he g _ (pr _ _ (pr _ _ hΦ)),
    Chr.lawW_unip hA hP hH hP₁ he u hu _ (pr _ _ hΦ), Chr.lawW_levi hA hP hH hP₁ he hm Φ hΦ, map_smul, ← Module.End.mul_apply,
    ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

end
end

