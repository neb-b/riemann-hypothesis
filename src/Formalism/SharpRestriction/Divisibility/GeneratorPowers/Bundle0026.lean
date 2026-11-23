module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0025
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0024
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinK
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0004

@[expose] public section

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPoint
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Formalism.MainNotions.ModuliIntegralCharts ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

theorem etPoint_min {X : Type} [AddCommGroup X] (Q : X → ℤ) (hQ : ∀ a, 0 ≤ Q a) (y : X) (R' : ℕ) :
    ∃ z : X, ∀ z' : X, Q (y + R' • z) ≤ Q (y + R' • z') := by
  let S : Set ℕ := Set.range fun z : X => (Q (y + R' • z)).toNat
  have hS : S.Nonempty := ⟨_, 0, rfl⟩
  obtain ⟨z, hz⟩ := Nat.sInf_mem hS
  refine ⟨z, fun z' => ?_⟩
  have h1 : sInf S ≤ (Q (y + R' • z')).toNat := Nat.sInf_le ⟨z', rfl⟩
  have h2 := hQ (y + R' • z)
  have h3 := hQ (y + R' • z')
  have h4 : (Q (y + R' • z)).toNat = sInf S := hz
  omega

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartActionPoint
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

def ptm (C : ChartAt Xo c y) {n : ℕ} (P : Fin n → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (m : ℕ) :
    jO y (dL Dw) m 1 ⟶ jO y C.d m n :=
  homAt y.x (jetSubstPS (m := m) (fun p : Fin n × Fin C.d => P p.1 p.2))

theorem ptm_congr (C : ChartAt Xo c y) {n : ℕ} {P P' : Fin n → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S}
    (hP : ∀ i j, MvPowerSeries.constantCoeff (P i j) = 0) (hP' : ∀ i j, MvPowerSeries.constantCoeff (P' i j) = 0)
    (m : ℕ) (h : ∀ i j, psJet m (P i j) = psJet m (P' i j)) : ptm C P m = ptm C P' m := by
  unfold ptm
  refine congrArg (homAt y.x) (GermD.jet_hom_ext fun q => ?_)
  exact (ExpGF.jetSubstPS_X m (fun p : Fin n × Fin C.d => P p.1 p.2) (fun p => hP p.1 p.2) q).trans
    ((h q.1 q.2).trans (ExpGF.jetSubstPS_X m (fun p : Fin n × Fin C.d => P' p.1 p.2) (fun p => hP' p.1 p.2) q).symm)

theorem coe_actP (u : 𝓞 E) (q : Fin 1 × Fin (dL Dw)) :
    ((actP (Dw := Dw) (S := S) c u q : MvPolynomial _ S) : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) =
      actPS (Dw := Dw) (S := S) c u q := by
  simp only [actP, actPS, MvPolynomial.coe_mul, MvPolynomial.coe_C, MvPolynomial.coe_X]
  rw [← MvPowerSeries.smul_eq_C_mul, algebraMap_smul]

theorem cc_actP (u : 𝓞 E) (q : Fin 1 × Fin (dL Dw)) :
    MvPolynomial.constantCoeff (actP (Dw := Dw) (S := S) c u q) = 0 := by
  simp [actP]

theorem jetSubstP_actP (m : ℕ) (u : 𝓞 E) :
    jetSubstP m (actP (Dw := Dw) (S := S) c u) = jetSubstPS (m := m) (actPS (Dw := Dw) (S := S) c u) := by
  rw [ExpGF.jetSubstP_eq_jetSubstPS m _ (fun q => cc_actP u q)]
  congr 1
  funext q
  exact coe_actP u q

theorem sA_ptm (C : ChartAt Xo c y) {n : ℕ} (P : Fin n → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hP : ∀ i j, MvPowerSeries.constantCoeff (P i j) = 0) (m : ℕ) (u : 𝓞 E) :
    homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c u)) ≫ ptm C P m =
      ptm C (fun i j => MvPowerSeries.subst (actPS (Dw := Dw) (S := S) c u) (P i j)) m := by
  unfold ptm
  rw [GermD.homAt_comp, jetSubstP_actP,
    ExpGF.jetSubstPS_comp m (fun p : Fin n × Fin C.d => P p.1 p.2) (actPS (Dw := Dw) (S := S) c u)
      (fun p => hP p.1 p.2) (const_actPS c u)]

theorem ptm_copy (C : ChartAt Xo c y) {n : ℕ} (P : Fin n → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hP : ∀ i j, MvPowerSeries.constantCoeff (P i j) = 0) (m : ℕ) (i : Fin n) :
    ptm C P m ≫ homAt y.x (jetCopy C.d m i) = ptm C ![P i] m := by
  have hs : MvPowerSeries.HasSubst (fun p : Fin n × Fin C.d => P p.1 p.2) := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => hP p.1 p.2)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero (fun p => hP p.1 p.2)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun q => by rw [(fun p => hP p.1 p.2) q]; exact IsNilpotent.zero)
  unfold ptm
  rw [GermD.homAt_comp, ExpGF.jetCopy_eq_PS,
    ExpGF.jetSubstPS_comp m (fun p : Fin 1 × Fin C.d => (MvPowerSeries.X (i, p.2) : MvPowerSeries (Fin n × Fin C.d) S))
      (fun p : Fin n × Fin C.d => P p.1 p.2) (fun p => MvPowerSeries.constantCoeff_X _) (fun p => hP p.1 p.2)]
  refine congrArg (homAt y.x) (congrArg (jetSubstPS (m := m)) ?_)
  funext p
  obtain ⟨a, j⟩ := p
  fin_cases a
  simp [MvPowerSeries.subst_X hs]

theorem ptm_subst (C : ChartAt Xo c y) {n n' : ℕ} (P : Fin n → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hP : ∀ i j, MvPowerSeries.constantCoeff (P i j) = 0) (m : ℕ)
    (σ : Fin n' × Fin C.d → MvPolynomial (Fin n × Fin C.d) S) (hσ : ∀ k, MvPolynomial.constantCoeff (σ k) = 0) :
    ptm C P m ≫ homAt y.x (jetSubstP m σ) =
      ptm C (fun i j => MvPowerSeries.subst (fun p : Fin n × Fin C.d => P p.1 p.2)
        ((σ (i, j) : MvPolynomial _ S) : MvPowerSeries (Fin n × Fin C.d) S)) m := by
  unfold ptm
  rw [GermD.homAt_comp, ExpGF.jetSubstP_eq_jetSubstPS m σ hσ,
    ExpGF.jetSubstPS_comp m (fun k => ((σ k : MvPolynomial _ S) : MvPowerSeries (Fin n × Fin C.d) S))
      (fun p : Fin n × Fin C.d => P p.1 p.2) (fun k => by
        have h0 : AddMonoidAlgebra.coeff (σ k) 0 = 0 := hσ k
        rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe, h0]) (fun p => hP p.1 p.2)]

theorem jφ_eq (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (m : ℕ) :
    homAt y.x (jφ φ m) = ptm C ![φ] m := by
  have e : (fun p : Fin 1 × Fin C.d => φ p.2) = (fun p : Fin 1 × Fin C.d => (![φ] : Fin 1 → _) p.1 p.2) := by
    funext p
    obtain ⟨a, j⟩ := p
    fin_cases a
    rfl
  unfold ptm jφ
  rw [e]

theorem exp_chart_action_point (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (hx : IsExpChart y (xExp y C φ)) (m : ℕ) (u : 𝓞 E) :
    xExp y C φ m ≫ Xo.univ.t.act.act u = ptm C ![φa c φ u] m ≫ C.x m := by
  have hP : ∀ i j, MvPowerSeries.constantCoeff ((![φ] : Fin 1 → _) i j) = 0 := by
    intro i j
    fin_cases i
    exact hφ j
  have e : (fun i j => MvPowerSeries.subst (actPS (Dw := Dw) (S := S) c u) ((![φ] : Fin 1 → _) i j)) =
      ![φa c φ u] := by
    funext i j
    fin_cases i
    rfl
  rw [hx.act m u, xExp, ← Category.assoc, jφ_eq, sA_ptm C _ hP m u, e]

theorem ptm_jpt (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (hx : IsExpChart y (xExp y C φ)) (m : ℕ) {n : ℕ}
    (us : Fin n → 𝓞 E) (i : Fin n) :
    ptm C (fun k => φa c φ (us k)) m ≫ jpt y C.d C.x m i = xExp y C φ m ≫ Xo.univ.t.act.act (us i) := by
  have hP : ∀ k j, MvPowerSeries.constantCoeff (φa c φ (us k) j) = 0 := fun k j => const_φa c φ hφ (us k) j
  rw [jpt, ← Category.assoc, ptm_copy C _ hP m i, exp_chart_action_point C φ hφ hx m (us i)]

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinima
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Module Formalism.MainNotions.ModuliIntegralCharts Matrix PhiCMin

theorem const_eq (E : Type) [Field E] [NumberField E] :
    ((((discr E).natAbs : ℝ) ^ 2)⁻¹) ^ ((1 : ℝ) / finrank ℚ E) *
      |(discr E : ℝ)| ^ ((2 : ℝ) / finrank ℚ E) = 1 := by
  have hd : (discr E : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero E
  have ha : (((discr E).natAbs : ℝ)) = |(discr E : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [ha]
  have ha0 : 0 < |(discr E : ℝ)| := abs_pos.mpr hd
  rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
  have h2 : ((2 : ℕ) : ℝ) * (1 / (finrank ℚ E : ℝ)) = 2 / (finrank ℚ E : ℝ) := by
    push_cast; ring
  rw [h2]
  exact inv_mul_cancel₀ (Real.rpow_pos_of_pos ha0 _).ne'

theorem phiCMinima_holds : PhiCMinimaStatement := by
  intro E _ _ cj hcj hne w₀ hw Y _ _ _ _ β hβ
  classical
  obtain ⟨ι, hι, b0, hpd⟩ := hβ
  have hcard : Fintype.card ι = finrank ℤ Y := (Module.finrank_eq_card_basis b0).symm
  set d := finrank ℤ Y with hd_def
  let b : Basis (Fin d) ℤ Y := b0.reindex (Fintype.equivFinOfCardEq hcard)
  have hG : (Matrix.of fun a c => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c)).PosDef := by
    have h := hpd.submatrix (Fintype.equivFinOfCardEq hcard).symm.injective
    convert h using 1
    ext a c
    simp [b, Basis.reindex_apply]
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · have : IsEmpty (Fin d) := by rw [hd0]; infer_instance
    exact ⟨fun i => isEmptyElim i, linearIndependent_empty_type, fun i => isEmptyElim i⟩
  set G := Matrix.of fun a c => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c) with hGdef

  have hcjO : ∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c := cj_integral hcj
  let l0 : SymB cj Y →ₗ[ℝ] ℝ :=
    { toFun := fun γ => ∑ a, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • b a) (b a)
      map_add' := fun γ γ' => by simp [Finset.sum_add_distrib]
      map_smul' := fun t γ => by simp [Finset.mul_sum] }
  have hl0int : ∀ γ : SymB cj Y, (∀ a c, ∃ z : ℤ, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) →
      ∃ z : ℤ, l0 γ = z := by
    intro γ hγ
    choose f hf using hγ
    refine ⟨∑ a, f (w₀ • b a) (b a), ?_⟩
    show ∑ a, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • b a) (b a) = _
    push_cast
    exact Finset.sum_congr rfl fun a _ => hf _ _
  have hl0pos : ∀ γ : SymB cj Y, (∀ a, 0 ≤ (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) → γ ≠ 0 → 0 < l0 γ := by
    intro γ hγ hne0
    have h2 : ∀ a, 2 * (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • b a) (b a) =
        (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b a) := fun a => two_mul_form_half_unit hcjO w₀ hw γ (b a)
    have hnn : ∀ a, 0 ≤ (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • b a) (b a) := fun a => by
      linarith [h2 a, hγ (b a)]
    show 0 < ∑ a, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • b a) (b a)
    by_contra hle
    push Not at hle
    have hz : ∀ a, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • b a) (b a) = 0 := fun a =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hnn a)).1
        (le_antisymm hle (Finset.sum_nonneg fun a _ => hnn a)) a (Finset.mem_univ _)
    have hrad : ∀ a z, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) z = 0 := fun a z =>
      bil_rad _ γ.2.1 hγ (b a) (by rw [← h2 a, hz a, mul_zero]) z
    apply hne0
    apply Subtype.ext
    refine LinearMap.ext₂ fun y z => ?_
    rw [← repr_left b (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) y z]
    simp [hrad]

  let Q : (Fin d → ℤ) → ℝ := fun c => (fun i => (c i : ℝ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℝ))
  have hne_u : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hdpos⟩, Finset.mem_univ _⟩
  let F : (Fin d → Fin d → ℤ) → ℝ := fun c => Finset.univ.sup' hne_u fun j => Q (c j)
  let B0 : ℝ := (1 / 2) * l0 β * ((d : ℝ) / muC E + 1) ^ 2
  let T : Set (Fin d → Fin d → ℤ) := {c | LinearIndependent ℤ c ∧ ∀ j, Q (c j) ≤ B0}
  have hTfin : T.Finite := by
    refine (Set.Finite.pi (t := fun _ : Fin d => {c : Fin d → ℤ | Q c ≤ B0})
      fun _ => finiteShort_holds d G hG B0).subset ?_
    intro c hc j _
    exact hc.2 j
  obtain ⟨c1, hc1li, hc1⟩ := main_ineq hcj hne hdpos b β hG l0 hl0int hl0pos 1 one_pos
  have hTne : T.Nonempty := ⟨c1, hc1li, hc1⟩
  obtain ⟨cs, hcsT, hcsmin⟩ := Set.exists_min_image T F hTfin hTne
  have hclaim : ∀ l : SymB cj Y →ₗ[ℝ] ℝ,
      (∀ γ : SymB cj Y, (∀ a c, ∃ z : ℤ, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l γ = z) →
      (∀ γ : SymB cj Y, (∀ a, 0 ≤ (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) → γ ≠ 0 → 0 < l γ) →
      F cs ≤ (1 / 2) * l β * ((d : ℝ) / muC E) ^ 2 := by
    intro l hlint hlpos
    have hev : ∀ δ : ℝ, 0 < δ → F cs ≤ (1 / 2) * l β * ((d : ℝ) / muC E + δ) ^ 2 := by
      intro δ hδ
      obtain ⟨c, hcli, hcq⟩ := main_ineq hcj hne hdpos b β hG l hlint hlpos δ hδ
      by_cases hle : (1 / 2) * l β * ((d : ℝ) / muC E + δ) ^ 2 ≤ B0
      · exact (hcsmin c ⟨hcli, fun j => (hcq j).trans hle⟩).trans
          (Finset.sup'_le _ _ fun j _ => hcq j)
      · push Not at hle
        exact (Finset.sup'_le _ _ fun j _ => hcsT.2 j).trans hle.le
    have hcont : Continuous fun δ : ℝ => (1 / 2) * l β * ((d : ℝ) / muC E + δ) ^ 2 := by fun_prop
    have ht := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simp only [add_zero] at ht
    exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun δ hδ => hev δ hδ)

  have hn : (0 : ℝ) < finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have hD : (0 : ℝ) < ((discr E).natAbs : ℝ) := by
    exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero E)
  have hXpos : (0 : ℝ) < ((((discr E).natAbs : ℝ) ^ 2)⁻¹) ^ ((1 : ℝ) / finrank ℚ E) := by
    positivity
  have hP : |(discr E : ℝ)| ^ ((2 : ℝ) / finrank ℚ E) =
      (((((discr E).natAbs : ℝ) ^ 2)⁻¹) ^ ((1 : ℝ) / finrank ℚ E))⁻¹ :=
    eq_inv_of_mul_eq_one_right (const_eq E)
  have hdpos' : (0 : ℝ) < d := by exact_mod_cast hdpos
  set κ : ℝ := |(discr E : ℝ)| ^ ((2 : ℝ) / finrank ℚ E) / (finrank ℚ E) * (d : ℝ) ^ 2 with hκdef
  have hκpos : 0 < κ := by rw [hκdef, hP]; positivity
  have hκ : ∀ l : SymB cj Y →ₗ[ℝ] ℝ, (1 / 2) * l β * ((d : ℝ) / muC E) ^ 2 = κ * l β := by
    intro l
    rw [div_pow, muC_sq, hκdef, hP]
    field_simp
  have hphi : F cs ≤ κ * phiC cj β := by
    have h1 : F cs / κ ≤ phiC cj β := by
      unfold phiC
      refine le_csInf ⟨l0 β, l0, hl0int, hl0pos, rfl⟩ ?_
      rintro _ ⟨l, hl1, hl2, rfl⟩
      rw [div_le_iff₀ hκpos, mul_comm, ← hκ l]
      exact hclaim l hl1 hl2
    rwa [div_le_iff₀ hκpos, mul_comm] at h1

  refine ⟨fun j => b.equivFun.symm (cs j), ?_, fun j => ?_⟩
  · exact hcsT.1.map' b.equivFun.symm.toLinearMap (LinearEquiv.ker _)
  · have hr : ∀ a : Fin d, PhiCMin.bs b a (b.equivFun.symm (cs j)) = (cs j a : ℝ) := fun a => by
      rw [PhiCMin.bs_apply]
      congr 1
      rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    have hq : (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b.equivFun.symm (cs j)) (b.equivFun.symm (cs j)) =
        Q (cs j) := by
      rw [← gram_expand b _ (b.equivFun.symm (cs j)) (b.equivFun.symm (cs j))]
      simp only [hr, Q, dotProduct, Matrix.mulVec, hGdef, Matrix.of_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
    have hle : Q (cs j) ≤ F cs := Finset.le_sup' (fun j => Q (cs j)) (Finset.mem_univ j)
    rw [hq]
    have hk : κ * phiC cj β = 2 * (|(discr E : ℝ)| ^ ((2 : ℝ) / finrank ℚ E) /
        (2 * finrank ℚ E) * (d : ℝ) ^ 2 * phiC cj β) := by
      rw [hκdef]; field_simp
    linarith

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

