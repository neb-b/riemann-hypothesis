module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryIsomOfIsometry
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0007
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0013
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityUnique
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0008

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FundamentalDomainTransportCongruentForm
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FTransfer

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem actTup_ratTup {M n : ℕ} (g : GL (Fin M) E) (X : Fin n → Fin M → E) :
    actTup R (bc (inclR (F := F) R) g) (ratTup R X) =
      ratTup R (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X a) := by
  funext a i
  have h := RingHom.map_mulVec (inclR (F := F) R) (g : Matrix (Fin M) (Fin M) E) (X a) i
  exact h.symm

theorem actTup_mul {M n : ℕ} (a b : GL (Fin M) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E) :
    actTup R (a * b) X = actTup R a (actTup R b X) := by
  funext c
  simp [actTup, Matrix.mulVec_mulVec]

end Alg

section Group

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R]

theorem isTopologicalGroup_HA [IsTopologicalRing R] [Module.Finite F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : IsTopologicalGroup (HA R σ J) := by
  haveI : IsTopologicalRing (R ⊗[F] E) := GlobalTheory.CompanionTheory.SW.HIsom.isTopologicalRing_tens F E R
  exact inferInstanceAs (IsTopologicalGroup (HR R σ J))

theorem borelSpace_HA (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    BorelSpace (HA R σ J) := ⟨rfl⟩

end Group

end GlobalTheory.CompanionTheory.SW.FTransfer


open GlobalTheory.CompanionTheory.SW.FTransfer in
theorem GlobalTheory.CompanionTheory.SW.FTransfer.cntI_transfer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (g : GL (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), J' = cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∃ (μ' : Measure (HA (AF F) σ J')) (𝓕' : Set (HA (AF F) σ J')), IsHaarH F E σ M J' μ' ∧ IsFDH F E σ M J' μ' 𝓕' ∧ μ' 𝓕' = μ 𝓕 ∧ ∀ (n : ℕ) (S : Set (Fin n → Fin M → E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞), cntI σ J μ 𝓕 S Φ = cntI σ J' μ' 𝓕' {X | (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X a) ∈ S} (fun Y => Φ (actTup (AF F) (bc (inclR (AF F)) g) Y)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ g J' hJ' μ 𝓕 hμ h𝓕
  obtain ⟨e, he1, he2⟩ := GlobalTheory.CompanionTheory.SW.HIsom.unitaryIsom_of_isometry F E σ hCM M J hJ g J' hJ' (AF F)
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  haveI := isTopologicalGroup_HA (F := F) (E := E) (AF F) σ J
  haveI := isTopologicalGroup_HA (F := F) (E := E) (AF F) σ J'
  haveI := borelSpace_HA (F := F) (E := E) (AF F) σ J
  haveI := borelSpace_HA (F := F) (E := E) (AF F) σ J'
  haveI : μ.IsHaarMeasure := hμ
  let em : HA (AF F) σ J' ≃ᵐ HA (AF F) σ J := e.toHomeomorph.toMeasurableEquiv
  have hmp : MeasurePreserving em (μ.map em.symm) μ := by
    refine ⟨em.measurable, ?_⟩
    rw [Measure.map_map em.measurable em.symm.measurable]
    simp
  refine ⟨μ.map em.symm, em ⁻¹' 𝓕, ?_, ?_, ?_, ?_⟩
  · exact ContinuousMulEquiv.isHaarMeasure_map μ e.symm
  · have hq : Measure.QuasiMeasurePreserving em (μ.map em.symm) μ := hmp.quasiMeasurePreserving
    have hin₀ : ∀ x : HA (AF F) σ J, HA.mat (AF F) σ J x ∈ HFin (AF F) σ J →
        HA.mat (AF F) σ J' (e.symm x) ∈ HFin (AF F) σ J' := by
      intro x hx
      apply (he2 _).1
      rw [e.apply_symm_apply]
      exact hx
    have hin : ∀ a : HFinIn (AF F) σ J,
        HA.mat (AF F) σ J' (e.symm (a.1 : HA (AF F) σ J)) ∈ HFin (AF F) σ J' :=
      fun a => hin₀ a.1 a.2
    have hmulx : ∀ (y : HA (AF F) σ J) (x : HA (AF F) σ J'), e (e.symm y * x) = y * e x := by
      intro y x
      rw [map_mul, e.apply_symm_apply]
    let e' : HFinIn (AF F) σ J → HFinIn (AF F) σ J' := fun a =>
      ⟨(e.symm (a.1 : HA (AF F) σ J) : HA (AF F) σ J'), Subgroup.mem_subgroupOf.2 (hin a)⟩
    refine IsFundamentalDomain.preimage_of_equiv h𝓕 hq (e := e') ⟨?_, ?_⟩ ?_
    · intro a b hab
      have h1 : e.symm (a.1 : HA (AF F) σ J) = e.symm (b.1 : HA (AF F) σ J) :=
        congrArg (fun x : HFinIn (AF F) σ J' => (x.1 : HA (AF F) σ J')) hab
      exact Subtype.ext (e.symm.injective h1)
    · intro b
      have hb : HA.mat (AF F) σ J (e (b.1 : HA (AF F) σ J')) ∈ HFin (AF F) σ J :=
        (he2 _).2 b.2
      refine ⟨⟨(e (b.1 : HA (AF F) σ J') : HA (AF F) σ J), Subgroup.mem_subgroupOf.2 hb⟩, ?_⟩
      exact Subtype.ext (e.symm_apply_apply (b.1 : HA (AF F) σ J'))
    · intro a x
      exact hmulx a.1 x
  · rw [em.symm.map_apply]
    congr 1
    ext x
    simp
  · intro n S Φ
    have hrest : (μ.map em.symm).restrict (em ⁻¹' 𝓕) = (μ.restrict 𝓕).map em.symm := by
      rw [MeasurableEquiv.restrict_map]
      congr 2
      ext x
      simp
    unfold cntI
    rw [hrest, lintegral_map_equiv]
    refine lintegral_congr fun h => ?_
    have key : ∀ X : Fin n → Fin M → E,
        actTup (AF F) (bc (inclR (AF F)) g)
            (actW (AF F) σ J' (em.symm h)⁻¹ (ratTup (AF F) X)) =
          actW (AF F) σ J h⁻¹
            (ratTup (AF F) (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X a)) := by
      intro X
      have hu : e (em.symm h) = h := e.apply_symm_apply h
      have h1 := he1 (em.symm h)⁻¹
      rw [map_inv, hu] at h1
      simp only [actW]
      rw [← actTup_ratTup, h1, ← actTup_mul, ← actTup_mul]
      congr 1
      group
    let T : {X : Fin n → Fin M → E | (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X a) ∈ S} ≃ S :=
      { toFun := fun X => ⟨fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X.1 a, X.2⟩
        invFun := fun Y => ⟨fun a => ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ Y.1 a, by
          have : (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ
              (((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ Y.1 a)) = Y.1 := by
            funext a
            rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
              Matrix.one_mulVec]
          change (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ
              (((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ Y.1 a)) ∈ S
          rw [this]
          exact Y.2⟩
        left_inv := fun X => by
          apply Subtype.ext
          funext a
          change ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ
            ((g : Matrix (Fin M) (Fin M) E) *ᵥ X.1 a) = X.1 a
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Matrix.one_mulVec]
        right_inv := fun Y => by
          apply Subtype.ext
          funext a
          change (g : Matrix (Fin M) (Fin M) E) *ᵥ
            (((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ Y.1 a) = Y.1 a
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
            Matrix.one_mulVec] }
    refine (T.tsum_eq (fun X : S => Φ (actW (AF F) σ J h⁻¹
      (ratTup (AF F) (X : Fin n → Fin M → E))))).symm.trans (tsum_congr fun X => ?_)
    exact congrArg Φ (key X.1).symm
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussianContinuousRapidDecay
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BB.GaussReg

theorem exists_lower_sup {n : Type} [Fintype n] [DecidableEq n] {P : Matrix n n ℝ} (hP : P.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : n → ℝ, c * ‖x‖ ^ 2 ≤ x ⬝ᵥ (P *ᵥ x) := by
  have hpos : ∀ x : n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (P *ᵥ x) := fun x hx => by
    simpa using hP.dotProduct_mulVec_pos hx
  have hcont : Continuous fun x : n → ℝ => x ⬝ᵥ (P *ᵥ x) := by fun_prop
  obtain ⟨c, hc, hmin⟩ : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ Metric.sphere (0 : n → ℝ) 1, c ≤ u ⬝ᵥ (P *ᵥ u) := by
    rcases (Metric.sphere (0 : n → ℝ) 1).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨u, hu, hm⟩ := (isCompact_sphere (0 : n → ℝ) 1).exists_isMinOn h hcont.continuousOn
      refine ⟨_, hpos u ?_, fun v hv => hm hv⟩
      rintro rfl
      simp at hu
  refine ⟨c, hc, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hu : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : n → ℝ) 1 := by
    simp [norm_smul, hn]
  have h1 := hmin _ hu
  have h2 : (‖x‖⁻¹ • x) ⬝ᵥ (P *ᵥ (‖x‖⁻¹ • x)) = (‖x‖⁻¹) ^ 2 * (x ⬝ᵥ (P *ᵥ x)) := by
    simp [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, sq, mul_assoc]
  rw [h2] at h1
  have h3 : 0 < ‖x‖ ^ 2 := by positivity
  calc c * ‖x‖ ^ 2 ≤ ((‖x‖⁻¹) ^ 2 * (x ⬝ᵥ (P *ᵥ x))) * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h1 h3.le
    _ = x ⬝ᵥ (P *ᵥ x) := by field_simp

theorem posdef_quadratic_lower_bound_l1 {n : Type} [Fintype n] [DecidableEq n] {P : Matrix n n ℝ} (hP : P.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : n → ℝ, c * (∑ p, |x p|) ^ 2 ≤ x ⬝ᵥ (P *ᵥ x) := by
  obtain ⟨c, hc, h⟩ := exists_lower_sup hP
  set N : ℝ := (Fintype.card n : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  refine ⟨c / (N ^ 2 + 1), by positivity, fun x => (?_ : _ ≤ _).trans (h x)⟩
  have h1 : ∑ p, |x p| ≤ N * ‖x‖ := by
    calc ∑ p, |x p| ≤ ∑ _p : n, ‖x‖ := Finset.sum_le_sum fun p _ => norm_le_pi_norm x p
      _ = N * ‖x‖ := by simp [N]
  have h0 : 0 ≤ ∑ p, |x p| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h2 : (∑ p, |x p|) ^ 2 ≤ (N ^ 2 + 1) * ‖x‖ ^ 2 := by
    have := pow_le_pow_left₀ h0 h1 2
    nlinarith [sq_nonneg ‖x‖]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

theorem exists_lower_family {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n]
    {P : ι → Matrix n n ℝ} (hP : ∀ i, (P i).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : ι → n → ℝ,
      c * (∑ i, ∑ p, |y i p|) ^ 2 ≤ ∑ i, y i ⬝ᵥ (P i *ᵥ y i) := by
  choose c hc h using fun i => posdef_quadratic_lower_bound_l1 (hP i)
  obtain ⟨c0, hc0, hle⟩ : ∃ c0 : ℝ, 0 < c0 ∧ ∀ i, c0 ≤ c i := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨1, one_pos, fun i => (hι.false i).elim⟩
    · obtain ⟨i, hi⟩ := Finite.exists_min c
      exact ⟨c i, hc i, hi⟩
  set W : ℝ := (Fintype.card ι : ℝ)
  have hW : 0 ≤ W := Nat.cast_nonneg _
  refine ⟨c0 / (W + 1), by positivity, fun y => ?_⟩
  have h1 : (∑ i, ∑ p, |y i p|) ^ 2 ≤ W * ∑ i, (∑ p, |y i p|) ^ 2 := by
    simpa [W] using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ∑ p, |y i p|)
  have hS : 0 ≤ ∑ i, (∑ p, |y i p|) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2 : c0 * ∑ i, (∑ p, |y i p|) ^ 2 ≤ ∑ i, y i ⬝ᵥ (P i *ᵥ y i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      (mul_le_mul_of_nonneg_right (hle i) (sq_nonneg _)).trans (h i (y i))
  refine le_trans ?_ h2
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have h3 : (∑ i, ∑ p, |y i p|) ^ 2 ≤ (W + 1) * ∑ i, (∑ p, |y i p|) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h3 hc0.le]

theorem exp_mul_pow_le {a : ℝ} (ha : 0 < a) (N : ℕ) {s : ℝ} (hs : 0 ≤ s) {q : ℝ} (hq : a * s ^ 2 ≤ q) :
    Real.exp (-q) * (1 + s) ^ N ≤ Real.exp ((N : ℝ) ^ 2 / (4 * a)) := by
  have h1 : (1 + s) ^ N ≤ Real.exp ((N : ℝ) * s) := by
    rw [mul_comm, Real.exp_mul, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp s]) N
  calc Real.exp (-q) * (1 + s) ^ N ≤ Real.exp (-q) * Real.exp ((N : ℝ) * s) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = Real.exp (-q + (N : ℝ) * s) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.2
      have h2 : (N : ℝ) * s ≤ a * s ^ 2 + (N : ℝ) ^ 2 / (4 * a) := by
        have : 0 ≤ (2 * a * s - N) ^ 2 / (4 * a) := by positivity
        have e : (2 * a * s - N) ^ 2 / (4 * a) = a * s ^ 2 + (N : ℝ) ^ 2 / (4 * a) - N * s := by
          field_simp
          ring
        linarith
      linarith

end GlobalTheory.CompanionTheory.SW.BB.GaussReg

namespace GlobalTheory.CompanionTheory.SW.BB

open GaussReg

theorem sizeTup_eq_sum_xw {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {M d : ℕ} (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (he : ∀ y w, |e y w| = ‖y w‖) (X : Fin 1 → Fin M → Ainf F ⊗[F] E) :
    sizeTup b X = ∑ w, ∑ p, |xw e b X w p| := by
  simp only [sizeTup, sizeInf, xw, cv, he, Fintype.sum_prod_type, Fin.sum_univ_one]
  symm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem gaussQ_continuous_rapidDecay : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M d : ℕ) (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ y w, |e y w| = ‖y w‖) → ∀ (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ), Continuous (gaussQ e b Pm) ∧ ((∀ w, (Pm w).PosDef) → RapidDecay b (fun X => (gaussQ e b Pm X : ℂ))) := by
  intro F E _ _ _ _ _ σ hCM M d b e hom he Pm
  obtain ⟨h1, h2, h3, h4, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨-, -, -, -, -, -, hco, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)
  have hxw : ∀ w p, Continuous fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => xw e b X w p := by
    intro w p
    have h := (hco d b).continuous
    exact (continuous_apply w).comp (hom.continuous.comp ((continuous_apply p.2).comp
      (h.comp ((continuous_apply p.1).comp (continuous_apply 0)))))
  have hxw' : ∀ w, Continuous fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => xw e b X w := fun w =>
    continuous_pi (hxw w)
  refine ⟨?_, fun hP N => ?_⟩
  · unfold gaussQ
    refine Real.continuous_exp.comp (continuous_const.mul (continuous_finsetSum _ fun w _ => ?_))
    exact (hxw' w).dotProduct (Continuous.matrix_mulVec continuous_const (hxw' w))
  · obtain ⟨c, hc, hlow⟩ := exists_lower_family hP
    refine ⟨Real.exp ((N : ℝ) ^ 2 / (4 * (Real.pi * c))), fun X => ?_⟩
    have hs := sizeTup_eq_sum_xw b e he X
    have hs0 : 0 ≤ sizeTup b X := by
      rw [hs]
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hq := hlow fun w => xw e b X w
    rw [← hs] at hq
    have hn : ‖((gaussQ e b Pm X : ℝ) : ℂ)‖ = gaussQ e b Pm X := by
      rw [Complex.norm_real, gaussQ, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [hn]
    have key := exp_mul_pow_le (a := Real.pi * c) (mul_pos Real.pi_pos hc) N hs0
      (q := Real.pi * ∑ w, xw e b X w ⬝ᵥ (Pm w *ᵥ xw e b X w))
      (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hq Real.pi_pos.le)
    simpa [gaussQ, neg_mul] using key

end GlobalTheory.CompanionTheory.SW.BB
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussianFourierTransformFormula
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW.GaussFlat

def swapCurry (α β : Type) : (α × β → ℝ) ≃ᵐ (β → α → ℝ) where
  toFun x := fun b a => x (a, b)
  invFun z := fun p => z p.2 p.1
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    refine measurable_pi_iff.2 fun b => measurable_pi_iff.2 fun a => measurable_pi_apply _
  measurable_invFun := by
    refine measurable_pi_iff.2 fun p => ?_
    exact (measurable_pi_apply p.1).comp (measurable_pi_apply p.2)

theorem swapCurry_measurePreserving (α β : Type) [Fintype α] [Fintype β] :
    MeasurePreserving (swapCurry α β) volume volume := by
  have h : (volume : Measure (α × β → ℝ)) =
      (volume : Measure (β → α → ℝ)).map (swapCurry α β).symm := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hs)]
    have e : (swapCurry α β).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi (fun b => Set.univ.pi (fun a => s (a, b))) := by
      ext f
      simp only [Set.mem_preimage, Set.mem_univ_pi]
      exact ⟨fun H b a => H (a, b), fun H p => H p.2 p.1⟩
    rw [e, volume_pi, Measure.pi_pi]
    simp_rw [volume_pi, Measure.pi_pi]
    rw [Fintype.prod_prod_type_right]
  refine ⟨(swapCurry α β).measurable, ?_⟩
  rw [h, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
  simp

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem integral_cur (f : (InfinitePlace F → ι → ℝ) → ℂ) :
    ∫ x : ι × InfinitePlace F → ℝ, f (cur x) = ∫ z, f z :=
  (swapCurry_measurePreserving ι (InfinitePlace F)).integral_comp' f

theorem dot_DM [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (x y : ι × InfinitePlace F → ℝ) :
    x ⬝ᵥ (DM B ρ *ᵥ y) = ∑ w, cur x w ⬝ᵥ (B.map (ρ w) *ᵥ cur y w) := by
  have h : ∀ i w, (DM B ρ *ᵥ y) (i, w) = (B.map (ρ w) *ᵥ cur y w) i := by
    intro i w
    simp only [mulVec, dotProduct, DM, Fintype.sum_prod_type_right, blockDiagonal_apply, cur]
    rw [Finset.sum_eq_single w]
    · simp
    · intro v _ hv
      simp [hv.symm]
    · simp
  rw [dotProduct, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [dotProduct, h, cur]

theorem gauss_fourier_flat : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∀ y : ι × InfinitePlace F → ℝ, ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| : ℝ) : ℂ) * ∫ x : ι × InfinitePlace F → ℝ, gauss B ρ P τ (cur x) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ (DM B ρ *ᵥ y) : ℝ) : ℂ)) = cG B ρ P τ * gauss B ρ P (fun w => -(τ w)⁻¹) (cur y) := by
  intro F _ _ ι _ _ _ M B ρ P hQ τ hτ y
  have h := (GlobalTheory.CompanionTheory.SW.GaussFou.gauss_fourier F ι M B ρ P hQ τ hτ).2.2.2 (cur y)
  rw [← h, ← integral_cur (F := F) (ι := ι) (fun z => gauss B ρ P τ z *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((∑ w, z w ⬝ᵥ (B.map (ρ w) *ᵥ cur y w) : ℝ) : ℂ)))]
  simp only [dot_DM]

end GlobalTheory.CompanionTheory.SW.ThW.GaussFlat
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GermFormPulledBackCombinationsExpandMonomials
section
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.FibreJointCont

theorem continuousOn_integral_of_bounded {V X P : Type}
    [TopologicalSpace V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [LocallyCompactSpace X] [TopologicalSpace P]
    (fib : X → Measure V) (B : Set X) (hB : IsOpen B)
    (hloc : ∀ b, IsLocallyFiniteMeasure (fib b))
    (hbd : ∀ (C : Set V) (D : Set X), IsCompact C → IsCompact D → D ⊆ B →
      ∃ c : ℝ≥0, ∀ b ∈ D, fib b C ≤ c)
    (hcont : ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ →
      ContinuousOn (fun b => ∫ v, φ v ∂(fib b)) B)
    (W : Set P) (Φ : P → V → ℝ)
    (hΦ : ContinuousOn (fun p : P × V => Φ p.1 p.2) (W ×ˢ Set.univ)) (hW : IsOpen W)
    (C : Set V) (hC : IsCompact C) (hsupp : ∀ p ∈ W, ∀ v, v ∉ C → Φ p v = 0) :
    ContinuousOn (fun q : P × X => ∫ v, Φ q.1 v ∂(fib q.2)) (W ×ˢ B) := by

  have hAt : ∀ p ∈ W, ∀ v, ContinuousAt (fun p : P × V => Φ p.1 p.2) (p, v) := fun p hp v =>
    hΦ.continuousAt ((hW.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ v⟩)
  have hslice : ∀ p ∈ W, Continuous (Φ p) := fun p hp =>
    continuous_iff_continuousAt.2 fun v =>
      ContinuousAt.comp (f := fun v : V => (p, v)) (g := fun p : P × V => Φ p.1 p.2)
        (hAt p hp v) (by fun_prop)
  have hcs : ∀ p ∈ W, HasCompactSupport (Φ p) := fun p hp =>
    HasCompactSupport.intro hC (hsupp p hp)
  have hint : ∀ p ∈ W, ∀ b, Integrable (Φ p) (fib b) := fun p hp b => by
    haveI := hloc b
    exact (hslice p hp).integrable_of_hasCompactSupport (hcs p hp)
  rintro ⟨p₀, b₀⟩ ⟨hp₀, hb₀⟩
  simp only [Set.mem_prod] at hp₀ hb₀ ⊢
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨D, hDn, hDB, hDc⟩ := local_compact_nhds (hB.mem_nhds hb₀)
  obtain ⟨c, hc⟩ := hbd C D hC hDc hDB
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  set δ : ℝ := ε / (2 * ((c : ℝ) + 1)) with hδ
  have hc0 : (0 : ℝ) ≤ c := c.2
  have hδ0 : 0 < δ := by positivity

  have htube : ∀ᶠ p in 𝓝 p₀, ∀ v ∈ C, |Φ p v - Φ p₀ v| < δ := by
    refine hC.eventually_forall_of_forall_eventually fun v _ => ?_
    have h1 : ContinuousAt (fun z : P × V => Φ z.1 z.2 - Φ p₀ z.2) (p₀, v) :=
      (hAt p₀ hp₀ v).sub
        (ContinuousAt.comp (f := fun z : P × V => z.2) (g := Φ p₀)
          (hslice p₀ hp₀).continuousAt continuousAt_snd)
    have h2 : Filter.Tendsto (fun z : P × V => Φ z.1 z.2 - Φ p₀ z.2) (𝓝 (p₀, v)) (𝓝 0) := by
      have h3 := h1.tendsto
      simp only [sub_self] at h3
      exact h3
    have h4 := (Metric.tendsto_nhds.1 h2) δ hδ0
    filter_upwards [h4] with z hz
    simpa [Real.dist_eq] using hz
  have hb : ∀ᶠ b in 𝓝 b₀,
      |∫ v, Φ p₀ v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b₀)| < ε / 2 := by
    have h1 := ((hcont (Φ p₀) (hslice p₀ hp₀) (hcs p₀ hp₀)).continuousAt
      (hB.mem_nhds hb₀)).tendsto
    have h2 := (Metric.tendsto_nhds.1 h1) (ε / 2) (by positivity)
    filter_upwards [h2] with b hb
    simpa [Real.dist_eq] using hb
  rw [nhds_prod_eq]
  have hp : ∀ᶠ p in 𝓝 p₀, p ∈ W ∧ ∀ v ∈ C, |Φ p v - Φ p₀ v| < δ :=
    Filter.Eventually.and (hW.mem_nhds hp₀) htube
  have hbb : ∀ᶠ b in 𝓝 b₀, b ∈ D ∧
      |∫ v, Φ p₀ v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b₀)| < ε / 2 := Filter.Eventually.and hDn hb
  filter_upwards [hp.prod_mk hbb] with q hq
  obtain ⟨⟨hqW, hqt⟩, hqD, hqb⟩ := hq
  obtain ⟨p, b⟩ := q
  simp only at hqW hqt hqD hqb ⊢
  have hfin : fib b C < ∞ := (hc b hqD).trans_lt ENNReal.coe_lt_top
  have hdiff : ∫ v, Φ p v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b)
      = ∫ v in C, (Φ p v - Φ p₀ v) ∂(fib b) := by
    rw [← integral_sub (hint p hqW b) (hint p₀ hp₀ b)]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => ?_).symm
    rw [hsupp p hqW v hv, hsupp p₀ hp₀ v hv, sub_zero]
  have hreal : (fib b).real C ≤ c := by
    have := ENNReal.toReal_mono ENNReal.coe_ne_top (hc b hqD)
    simpa [Measure.real] using this
  have hle : |∫ v, Φ p v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b)| ≤ δ * (c : ℝ) := by
    rw [hdiff, ← Real.norm_eq_abs]
    have h5 : ‖∫ v in C, (Φ p v - Φ p₀ v) ∂(fib b)‖ ≤ δ * (fib b).real C :=
      norm_setIntegral_le_of_norm_le_const (C := δ) hfin fun v hv => by
        rw [Real.norm_eq_abs]; exact (hqt v hv).le
    exact h5.trans (mul_le_mul_of_nonneg_left hreal hδ0.le)
  have hδc : δ * (c : ℝ) ≤ ε / 2 := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  rw [Real.dist_eq]
  calc |∫ v, Φ p v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b₀)|
      = |(∫ v, Φ p v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b))
          + (∫ v, Φ p₀ v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b₀))| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ < ε := by linarith

theorem continuousOn_fibre_integral : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib → ∀ (P : Type) [TopologicalSpace P] (W : Set P) (Φ : P → V → ℝ), ContinuousOn (fun p : P × V => Φ p.1 p.2) (W ×ˢ Set.univ) → IsOpen W → ∀ C : Set V, IsCompact C → (∀ p ∈ W, ∀ v, v ∉ C → Φ p v = 0) → ContinuousOn (fun q : P × X => ∫ v, Φ q.1 v ∂(fib q.2)) (W ×ˢ B) := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ _ f g ι hι hg hfg B hB fib hF P _ W Φ hΦ hW C hC hsupp
  obtain ⟨hloc, -, -, hbd⟩ := _root_.GlobalTheory.CompanionTheory.SW.FibreFam.fibre_family_basic V X Y μ ν f g ι hι hg hfg B hB fib hF
  refine continuousOn_integral_of_bounded fib B hB hloc hbd ?_ W Φ hΦ hW C hC hsupp
  intro φ hφ hφc
  have h := (_root_.GlobalTheory.CompanionTheory.SW.FibreDensity.isContDensityOn_fibreIntegral V X Y μ ν f g ι hι hg hfg B hB fib hF (fun v => (φ v : ℂ))
    (Complex.continuous_ofReal.comp hφ) (hφc.comp_left Complex.ofReal_zero)).1.1
  have h2 : ContinuousOn (fun b => Complex.re (∫ v, ((φ v : ℝ) : ℂ) ∂(fib b))) B :=
    Complex.continuous_re.comp_continuousOn h
  refine h2.congr fun b _ => ?_
  have := integral_ofReal (μ := fib b) (𝕜 := ℂ) (f := φ)
  simp only [Complex.coe_algebraMap] at this
  show ∫ v, φ v ∂(fib b) = (∫ v, ((φ v : ℝ) : ℂ) ∂(fib b)).re
  rw [this]
  simp

end GlobalTheory.CompanionTheory.SW.FibreJointCont
end

