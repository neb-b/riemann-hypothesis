module

public import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.ZuckDualTOfZuckDual
public import CompanionTheory.AutomorphicTheory.SchurLimitBounds.SchurOrthogonality.SchurH
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Bundle0001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.UniformCoefficientBounds.CoefBoundUniform

@[expose] public section

-- bundled from CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.BetaAtInfinityZero
section
open Matrix PI.UpqRep Formalism.FourierDecayAlt MeasureTheory CompanionTheory.LimBd.Main CompanionTheory.LimBd.SchurHpk
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.CapEig

theorem kfin_iff (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (P : B.Mat k r) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : B.Mat k r → (H →L[ℂ] H)) (v : H) (hP : IsCayleyU k r ε P) :
    IsKFinHpk (k := k) (r := r) σ v ↔ IsKFin ε (fun g => σ (P⁻¹ * g * P)) v := by
  have hinv : P⁻¹ = star P := Matrix.inv_eq_left_inv (Unitary.star_mul_self_of_mem hP.2)
  have hPi : P⁻¹ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := hinv ▸ Unitary.star_mem hP.2
  constructor
  · rintro ⟨S, hS, hv, hst⟩
    refine ⟨S, hS, hv, fun g hg x hx => hst _ ⟨back_mem hP.1 ?_, ?_⟩ x hx⟩
    · show gᴴ * Jm ε * g = Jm ε
      have h1 : gᴴ * g = 1 := Unitary.star_mul_self_of_mem hg.1
      rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    · exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hPi hg.1) hP.2
  · rintro ⟨S, hS, hv, hst⟩
    refine ⟨S, hS, hv, fun x hx y hy => ?_⟩
    have hu : P * x * P⁻¹ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ :=
      Submonoid.mul_mem _ (Submonoid.mul_mem _ hP.2 hx.2) hPi
    have hJ : (P * x * P⁻¹)ᴴ * Jm ε * (P * x * P⁻¹) = Jm ε := forth_mem hP.1 hx.1
    have h1 : (P * x * P⁻¹) * (P * x * P⁻¹)ᴴ = 1 := Unitary.mul_star_self_of_mem hu
    have hK : P * x * P⁻¹ ∈ Kset ε := by
      refine ⟨hu, ?_⟩
      generalize P * x * P⁻¹ = g at hJ h1
      calc g * Jm ε = g * (gᴴ * Jm ε * g) := by rw [hJ]
        _ = (g * gᴴ) * Jm ε * g := by simp only [Matrix.mul_assoc]
        _ = Jm ε * g := by rw [h1, Matrix.one_mul]
    have := hst _ hK y hy
    simpa only [back_forth hP.1] using this

theorem eq_of_capelliPolynomial_eq {n : ℕ} {μ μ' : Fin n → ℝ} (hμ : StrictAnti μ) (hμ' : StrictAnti μ')
    (h : ∀ Y : ℂ, Formalism.QuantumDeterminants.capP (fun s => (μ s : ℂ)) Y = Formalism.QuantumDeterminants.capP (fun s => (μ' s : ℂ)) Y) : μ = μ' := by
  have key : ∀ {a b : Fin n → ℝ}, (∀ Y : ℂ, Formalism.QuantumDeterminants.capP (fun s => (a s : ℂ)) Y =
      Formalism.QuantumDeterminants.capP (fun s => (b s : ℂ)) Y) → Set.range a ⊆ Set.range b := by
    rintro a b hab _ ⟨s, rfl⟩
    have h0 : Formalism.QuantumDeterminants.capP (fun s => (a s : ℂ)) (-(a s : ℂ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ s) (by simp)
    rw [hab] at h0
    obtain ⟨t, -, ht⟩ := Finset.prod_eq_zero_iff.1 h0
    refine ⟨t, ?_⟩
    have : ((b t : ℝ) : ℂ) = (a s : ℂ) := by linear_combination ht
    exact_mod_cast this
  exact (hμ.range_inj hμ').1 (Set.Subset.antisymm (key h) (key fun Y => (h Y).symm))

theorem capelli_inequivalence : Inequiv := by
  intro hE k r ε ε' μ μ' H H' _ _ _ _ _ _ σ σ' hμ hμ' hσ hσ' hne
  rintro ⟨U, hU⟩
  apply hne
  obtain ⟨P, hP, hds⟩ := id hσ
  obtain ⟨S, hS, hSK, -, ⟨v, hvS, hv0, -⟩, -⟩ := hds.2.2.2.2.2.1
  have hv : IsKFinHpk (k := k) (r := r) σ v := (kfin_iff k r ε P H σ v hP).2 ⟨S, hS, hvS, hSK⟩
  have hv' : IsKFinHpk (k := k) (r := r) σ' (U v) := by
    obtain ⟨S₁, h1, h2, h3⟩ := hv
    refine ⟨S₁.map (U.toLinearEquiv : H →ₗ[ℂ] H'), inferInstance, Submodule.mem_map_of_mem h2, ?_⟩
    rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨σ g x, h3 g hg x hx, hU g hg.1 x⟩
  have c1 : IsCoef k r ε μ (fun g => ⟪v, σ g v⟫_ℂ) := ⟨H, _, _, inferInstance, σ, v, v, hμ, hσ, hv, hv, fun _ _ => rfl⟩
  have c2 : IsCoef k r ε' μ' (fun g => ⟪v, σ g v⟫_ℂ) :=
    ⟨H', _, _, inferInstance, σ', U v, U v, hμ', hσ', hv', hv', fun g hg => by
      rw [← hU g hg v, U.inner_map_map]⟩
  have h1G : (1 : B.Mat k r) ∈ B.GV k r := by
    show (1 : B.Mat k r)ᴴ * _ * 1 = _
    simp
  have hσ1 : σ 1 = 1 := (isURepOn_of_ds hσ).1.1
  refine eq_of_capelliPolynomial_eq hμ.1 hμ'.1 fun Y => ?_
  have e1 := hE k r ε μ _ ℂ ℂ 1 c1 Y 1 h1G
  have e2 := hE k r ε' μ' _ ℂ ℂ 1 c2 Y 1 h1G
  rw [e1] at e2
  have e3 := congrArg (fun T : ℂ →L[ℂ] ℂ => T 1) e2
  simp only [hσ1, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_eq_mul, mul_one] at e3
  exact mul_right_cancel₀ (inner_self_ne_zero.2 hv0) e3

end CompanionTheory.CapEig

end
end

-- bundled from CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.CoefCC
section
open Matrix MeasureTheory Set
open scoped ContDiff InnerProductSpace

noncomputable section

namespace CompanionTheory.CapEig

open CompanionTheory.D.Upq.Sm Formalism.FourierDecayAlt CompanionTheory.LimBd.Main

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Deriv

variable {k r : ℕ} {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup E] [NormedSpace ℂ E] {G : Set (B.Mat k r)} {σ : B.Mat k r → (H →L[ℂ] H)}

def cf (σ : B.Mat k r → (H →L[ℂ] H)) (x₀ : E) (a b : H) (g : B.Mat k r) : E := ⟪a, σ g b⟫_ℂ • x₀

theorem rw_cf (h : RepOn G σ) (x₀ : E) (a : H) {b : H} (hb : IsSm G σ b) {f : B.Mat k r → E}
    (hf : ∀ g ∈ G, f g = cf σ x₀ a b g) :
    ∀ {v : List (B.Mat k r)}, LieW G v → ∀ g ∈ G, B.Rw v f g = cf σ x₀ a (dsW σ v b) g
  | [], _, g, hg => hf g hg
  | X :: v, hv, g, hg => by
    have hv' : LieW G v := fun Y hY => hv Y (List.mem_cons_of_mem _ hY)
    have hX := hv X List.mem_cons_self
    change deriv (fun t : ℝ => B.Rw v f (g * ex X t)) 0 = _
    have e : (fun t : ℝ => B.Rw v f (g * ex X t)) =
        fun t => ⟪a, σ g (σ (ex X t) (dsW σ v b))⟫_ℂ • x₀ := by
      ext1 t
      rw [rw_cf h x₀ a hb hf hv' _ (h.mul_mem _ hg _ (hX t)), cf, h.apply_mul hg (hX t)]
    rw [e]
    have h1 := ((hb.dsW h hv').differentiableAt h hX).hasDerivAt
    let L : H →L[ℝ] E := (((innerSL ℂ a).comp (σ g)).smulRight x₀).restrictScalars ℝ
    exact (L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1).deriv

theorem lw_cf (h : RepOn G σ) (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) (x₀ : E) {a : H}
    (ha : IsSm G σ a) (b : H) {f : B.Mat k r → E} (hf : ∀ g ∈ G, f g = cf σ x₀ a b g) :
    ∀ {u : List (B.Mat k r)}, LieW G u → ∀ g ∈ G,
      u.foldr B.LdV f g = cf σ x₀ (dsW σ u a) b g
  | [], _, g, hg => hf g hg
  | X :: u, hu, g, hg => by
    have hu' : LieW G u := fun Y hY => hu Y (List.mem_cons_of_mem _ hY)
    have hX := hu X List.mem_cons_self
    change deriv (fun t : ℝ => u.foldr B.LdV f (NormedSpace.exp (-((t : ℂ) • X)) * g)) 0 = _
    have e : (fun t : ℝ => u.foldr B.LdV f (NormedSpace.exp (-((t : ℂ) • X)) * g)) =
        fun t => ⟪σ (ex X t) (dsW σ u a), σ g b⟫_ℂ • x₀ := by
      ext1 t
      have e1 : NormedSpace.exp (-((t : ℂ) • X)) = ex X (-t) := by simp [ex]
      rw [e1, lw_cf h hiso x₀ ha b hf hu' _ (h.mul_mem _ (hX _) _ hg), cf]
      let I : H →ₗᵢ[ℂ] H := ⟨σ (ex X t), hiso _ (hX t)⟩
      rw [← I.inner_map_map]
      change ⟪σ (ex X t) _, σ (ex X t) (σ (ex X (-t) * g) b)⟫_ℂ • x₀ = _
      rw [← h.apply_mul (hX t) (h.mul_mem _ (hX _) _ hg), ← Matrix.mul_assoc, ← ex_add,
        add_neg_cancel, ex_zero, Matrix.one_mul]
    rw [e]
    have h1 := ((ha.dsW h hu').differentiableAt h hX).hasDerivAt
    have h2 := (h1.inner ℂ (hasDerivAt_const (0 : ℝ) (σ g b))).smul_const x₀
    rw [h2.deriv]
    simp [cf, dsW_cons, ds]

end Deriv

theorem capelli_coefficient_smooth : CoefSmooth := by
  intro hK k r ε μ φ E _ _ T hφ g₀ hg₀
  obtain ⟨H, _, _, _, σ, v, w, hμ, hσ, hv, -, he⟩ := hφ
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hK k r ε μ H σ hμ hσ v hv g₀ hg₀
  refine ⟨U, fun x => (((innerSL ℂ w).smulRight T).restrictScalars ℝ) (F x), hU, hgU,
    (((innerSL ℂ w).smulRight T).restrictScalars ℝ).contDiff.comp_contDiffOn hF, fun g hg hgG => ?_⟩
  have e := hfF g hg hgG
  simp only at e
  simp [he g hgG, e]

theorem capelli_coefficient_continuity : CoefCC := by
  intro hK k r ε A h hD μ φ E _ _ x₀ m hφ hgap
  have hsm := capelli_coefficient_smooth hK k r ε μ φ E x₀ hφ
  obtain ⟨H, _, _, _, σ, v, w, hμ, hσ, hv, hw, he⟩ := hφ
  obtain ⟨P, ⟨⟨hP, hPJ⟩, -⟩, -, -, ⟨⟨h1, hm⟩, hiso, -⟩, -⟩ := id hσ
  obtain ⟨hc1, -⟩ := conj_facts hP hPJ
  have hG : PI.IsMatGroup (B.GV k r) := PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group k r
  have hrep : RepOn (B.GV k r) σ := repOn_of_conj hP hPJ h1 hm
  have hiso' : ∀ g ∈ B.GV k r, ∀ v, ‖σ g v‖ = ‖v‖ := fun g hg v => by
    obtain ⟨b, hb, rfl⟩ := hc1 g hg
    exact hiso b hb v
  have good : ∀ {x : H}, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ x → IsSm (B.GV k r) σ x ∧
      ∃ (T' : Submodule ℂ H) (C : ℝ), GoodSub (B.GV k r)
        (B.GV k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _)) σ T' ∧ 0 ≤ C ∧
        ∀ W : List (B.Mat k r), LieW (B.GV k r) W → (∀ X ∈ W, ‖X‖ ≤ 1) → W.length ≤ m →
          dsW σ W x ∈ T' ∧ ‖dsW σ W x‖ ≤ C := by
    rintro x ⟨S, hS, hxS, hSK⟩
    have hT : GoodSub (B.GV k r) (B.GV k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _))
        σ S := ⟨hS, fun v hv => hK k r ε μ H σ hμ hσ v ⟨S, hS, hv, hSK⟩, hSK⟩
    exact ⟨hT.sm x hxS, hT.words hG hrep inter_subset_left hxS m⟩
  obtain ⟨hvs, Tv, Cv, hTv, hCv, hWv⟩ := good hv
  obtain ⟨hws, Tw, Cw, hTw, hCw, hWw⟩ := good hw
  have := hTv.fin
  have := hTw.fin
  have hkf : ∀ a ∈ Tv ⊔ Tw, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ a := by
    intro a ha
    refine ⟨Tv ⊔ Tw, inferInstance, ha, fun g hg x hx => ?_⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hTv.stab g hg y hy) (hTw.stab g hg z hz)
  obtain ⟨C', hC', hb⟩ := coef_bound_uniform (G := B.GV k r) (σ := σ) (T := Tv ⊔ Tw)
    (ρ := fun g => (B.gN g ^ A)⁻¹) (fun g _ => inv_nonneg.2 (Real.rpow_nonneg (Real.sqrt_nonneg _) _))
    (fun a ha b hb => by
      obtain ⟨C, hd⟩ := hD μ H σ hμ hσ hgap b a (hkf b hb) (hkf a ha)
      refine ⟨C, fun g hg => ?_⟩
      have hp : 0 < B.gN g ^ A := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg)) A
      rw [← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]
      exact hd g hg)
  refine ⟨C' * Cw * Cv * ‖x₀‖, fun g₀ hg₀ => ?_, fun u v' hu hv' huv g hg => ?_⟩
  · obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hsm g₀ hg₀
    exact ⟨U, F, hU, hgU, hF.of_le (by exact_mod_cast le_top), hfF⟩
  · have hlie : ∀ W : List (B.Mat k r), (∀ X ∈ W, B.unitLie k r X) →
        LieW (B.GV k r) W ∧ ∀ X ∈ W, ‖X‖ ≤ 1 := fun W hW =>
      ⟨fun X hX t => ex_mem_of_lie (hW X hX).1 t,
        fun X hX => (Matrix.norm_le_iff zero_le_one).2 (hW X hX).2⟩
    obtain ⟨hu1, hu2⟩ := hWw u (hlie u hu).1 (hlie u hu).2 (by omega)
    obtain ⟨hv1, hv2⟩ := hWv v' (hlie v' hv').1 (hlie v' hv').2 (by omega)
    have e : B.dLR u v' (fun g => φ g • x₀) g = cf σ x₀ (dsW σ u w) (dsW σ v' v) g :=
      lw_cf hrep hiso' x₀ hws _ (rw_cf hrep x₀ w hvs (fun g hg => by rw [he g hg]; rfl) (hlie v' hv').1)
        (hlie u hu).1 g hg
    rw [e, cf, norm_smul]
    have hp : 0 < B.gN g ^ A := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg)) A
    have h2 := hb _ (Submodule.mem_sup_right hu1) _ (Submodule.mem_sup_left hv1) g hg
    have h5 : 0 ≤ (B.gN g ^ A)⁻¹ := inv_nonneg.2 hp.le
    calc _ ≤ B.gN g ^ A * (C' * Cw * Cv * (B.gN g ^ A)⁻¹ * ‖x₀‖) := by
          gcongr
          exact h2.trans (by gcongr)
      _ = (B.gN g ^ A * (B.gN g ^ A)⁻¹) * (C' * Cw * Cv * ‖x₀‖) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hp.ne', one_mul]

end CompanionTheory.CapEig

end
end

