module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsDeg
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0008

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ExistsDecompOrthIsotropicPlus
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cl

variable (D : D7) (u : D.what₂.Word) (hT : Tu D u ≠ 0) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u)

include he in
theorem isotropic_le_orth_range : F0.X ≤ orth (hS D) (LinearMap.range (D.sp.iXY 0)) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, rfl⟩
  rw [he]
  change D.sp.hypE a ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))
  rw [Formalism.MainNotions.mem_orth_iff]
  rintro _ ⟨w, rfl⟩
  exact (D.sp.hyp_orthX a w).1

include hz in
theorem z_mem_orth_range : F0.z ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0)) := by
  rw [Formalism.MainNotions.mem_orth_iff]
  rintro _ ⟨w, rfl⟩
  rw [hz]
  exact Formalism.MainNotions.hT_swap_zero (z_orth_embedding D u w)


include hT he hz in
theorem exists_decomp_orth_isotropic_plus (x : (VS D).V) (hx : x ∈ orth (hS D) F0.Xplus) :
    ∃ w, x - D.sp.iXY 0 w ∈ F0.X := by
  have hW := (Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).1
  have hx' : x ∈ Wsp D ⊔ Xsp (lf D F0) := by rw [hW]; exact hx
  obtain ⟨a, ⟨w, rfl⟩, ξ, hξ, rfl⟩ := Submodule.mem_sup.1 hx'
  exact ⟨w, by simpa using hξ⟩


include hT he hz in
theorem exists_decomp_orth_isotropic (x : (VS D).V) (hx : x ∈ orth (hS D) F0.X) :
    ∃ (w : (D.sp.X 0).V) (c : D.host.E), x - (D.sp.iXY 0 w + c • F0.z) ∈ F0.X := by
  have hT' : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hT
  have hx' := (Formalism.MainNotions.mem_orth_iff _ _).1 hx
  obtain ⟨w, hw⟩ := exists_decomp_orth_isotropic_plus D u hT F0 he hz
    (x - (-((VS D).hT F0.z x) / ((Tu D u : ℕ) : D.host.E)) • F0.z) (by
      rw [Formalism.MainNotions.mem_orth_iff]
      refine Formalism.MainNotions.hT_zero_of_mem_Xplus F0 (fun a => ?_) ?_
      · rw [map_sub, map_smul, F0.z_orth a, smul_zero, sub_zero]
        exact hx' _ (Submodule.subset_span ⟨a, rfl⟩)
      · rw [map_sub, map_smul, F0.z_norm, smul_eq_mul]
        field_simp
        ring)
  refine ⟨w, -((VS D).hT F0.z x) / ((Tu D u : ℕ) : D.host.E), ?_⟩
  rw [add_comm, ← sub_sub]
  exact hw


include hT he hz in
theorem Lsub_eq_of_latticeWithZ_eq (Λ₁ Λ₂ : LatV D) (h : latticeWithZ D F0 Λ₁ = latticeWithZ D F0 Λ₂) :
    Lsub Λ₁ (lf D F0) = Lsub Λ₂ (lf D F0) := by
  have key : ∀ Λ : LatV D, ∀ x, x ∈ Lsub Λ (lf D F0) ↔
      x ∈ orth (hS D) F0.X ∧ ∀ (w : (D.sp.X 0).V) (c : D.host.E),
        x - (D.sp.iXY 0 w + c • F0.z) ∈ F0.X → (w, c) ∈ latticeWithZ D F0 Λ := by
    intro Λ x
    have hj : ∀ (w : (D.sp.X 0).V) (c : D.host.E), (w, c) ∈ latticeWithZ D F0 Λ ↔ D.sp.iXY 0 w + c • F0.z ∈ Lsub Λ (lf D F0) := by
      intro w c
      unfold latticeWithZ
      rw [Submodule.mem_comap]
      simp [embedWithZ]
    constructor
    · intro hx
      refine ⟨hx.2, fun w c hξ => ?_⟩
      rw [hj]
      have := (Lsub Λ (lf D F0)).sub_mem hx (isotropic_le_Lsub F0 Λ hξ)
      simpa using this
    · rintro ⟨hxO, hall⟩
      obtain ⟨w, c, hξ⟩ := exists_decomp_orth_isotropic D u hT F0 he hz x hxO
      have h1 := (hj w c).1 (hall w c hξ)
      have := (Lsub Λ (lf D F0)).add_mem h1 (isotropic_le_Lsub F0 Λ hξ)
      simpa using this
  ext x
  rw [key Λ₁, key Λ₂, h]

def projWAlt : (VS D).V →ₗ[D.host.E] (D.sp.X 0).V :=
  (LinearEquiv.ofInjective (D.sp.iXY 0) (embedding_W_injective D)).symm.toLinearMap ∘ₗ LinearMap.fst D.host.E _ _ ∘ₗ
    (Submodule.prodEquivOfIsCompl _ _ (isCompl_range_orth_range D)).symm.toLinearMap

theorem projW_apply (w : (D.sp.X 0).V) (b : (VS D).V) (hb : b ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))) :
    projWAlt D (D.sp.iXY 0 w + b) = w := by
  have e : D.sp.iXY 0 w + b = Submodule.prodEquivOfIsCompl _ _ (isCompl_range_orth_range D)
      (LinearEquiv.ofInjective (D.sp.iXY 0) (embedding_W_injective D) w, ⟨b, hb⟩) := by
    rw [Submodule.coe_prodEquivOfIsCompl']
    rfl
  rw [e]
  unfold projWAlt
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.fst_apply]


include hT he hz in
theorem exists_induced_isometry_W (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ stabF D F0) :
    ∃ γ ∈ isom (D.sp.X 0).hT, ∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ w) ∈ F0.X := by
  have hσ' : ∀ x y, (VS D).hT (σ x) (σ y) = (VS D).hT x y := hσ.1
  have hX : F0.X.map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X := by
    have := hσ.2.1 D.R.rS
    rwa [partial_isotropic_top] at this
  have hXp : F0.Xplus.map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.Xplus := by
    unfold FlagG.Xplus
    rw [Submodule.map_sup, hX, Submodule.map_span, Set.image_singleton]
    congr 3
    exact hσ.2.2
  have hWO : ∀ w, D.sp.iXY 0 w ∈ orth (hS D) F0.Xplus := by
    intro w
    have hW := (Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).1
    have : D.sp.iXY 0 w ∈ Wsp D ⊔ Xsp (lf D F0) := Submodule.mem_sup_left ⟨w, rfl⟩
    rw [hW] at this
    exact this
  have hdec : ∀ w, ∃ w', σ (D.sp.iXY 0 w) - D.sp.iXY 0 w' ∈ F0.X := by
    intro w
    refine exists_decomp_orth_isotropic_plus D u hT F0 he hz _ ?_
    rw [Formalism.MainNotions.mem_orth_iff]
    intro x hx
    rw [← hXp] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    change (VS D).hT (σ x') (σ (D.sp.iXY 0 w)) = 0
    rw [hσ']
    exact (Formalism.MainNotions.mem_orth_iff _ _).1 (hWO w) x' hx'
  let γ0 : (D.sp.X 0).V →ₗ[D.host.E] (D.sp.X 0).V :=
    projWAlt D ∘ₗ (σ : (VS D).V →ₗ[D.host.E] (VS D).V) ∘ₗ D.sp.iXY 0
  have hγ0 : ∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ0 w) ∈ F0.X := by
    intro w
    obtain ⟨w', hw'⟩ := hdec w
    have e : γ0 w = w' := by
      change projWAlt D (σ (D.sp.iXY 0 w)) = w'
      have : σ (D.sp.iXY 0 w) = D.sp.iXY 0 w' + (σ (D.sp.iXY 0 w) - D.sp.iXY 0 w') := by abel
      rw [this]
      exact projW_apply D w' _ (isotropic_le_orth_range D u F0 he hw')
    rw [e]
    exact hw'
  have hiso : ∀ w w', (D.sp.X 0).hT (γ0 w) (γ0 w') = (D.sp.X 0).hT w w' := by
    intro w w'
    have e1 : σ (D.sp.iXY 0 w) = D.sp.iXY 0 (γ0 w) + (σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ0 w)) := by abel
    have e2 : σ (D.sp.iXY 0 w') = D.sp.iXY 0 (γ0 w') + (σ (D.sp.iXY 0 w') - D.sp.iXY 0 (γ0 w')) := by abel
    have h1 := hσ' (D.sp.iXY 0 w) (D.sp.iXY 0 w')
    rw [e1, e2, inner_decomp_orth_range D _ _ _ _ (isotropic_le_orth_range D u F0 he (hγ0 w))
      (isotropic_le_orth_range D u F0 he (hγ0 w')), embedding_isometry_W,
      (Formalism.MainNotions.mem_orth_iff _ _).1 (isotropic_le_orth_isotropic F0 (hγ0 w')) _ (hγ0 w), add_zero] at h1
    exact h1
  have hinj : Function.Injective γ0 := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    refine (Submodule.mem_bot _).2 ((D.sp.X 0).nondeg.2 x (fun y => ?_))
    rw [← hiso y x, hx, map_zero]
  refine ⟨LinearEquiv.ofInjectiveEndo γ0 hinj, fun w w' => ?_, fun w => ?_⟩
  · simpa using hiso w w'
  · simpa using hγ0 w

end Cl

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsDegF
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rec

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

theorem rows_GamD_le (D : D7) (large₂ : SizeData₂ D) {Ca C2 C : ℝ} (hC2 : 2 * C2 ≤ C) (hCa : |Ca| ≤ C) :
    rows_GamD D large₂ Ca C2 ≤ GamS D large₂ * Real.exp (C * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) *
      (C / D.R.k) ^ (D.R.k * D.R.f) := by
  unfold rows_GamD
  have hb : Real.log large₂.sc.b = large₂.sc.L := by unfold Scale.b; exact Real.log_exp _
  have hL : 0 ≤ large₂.sc.L := by
    unfold Scale.L; exact Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have hG : 0 ≤ GamS D large₂ := by unfold GamS; positivity
  have hQ : 0 ≤ (D.R.m : ℝ) ^ 6 * D.R.f * large₂.sc.L := mul_nonneg (by positivity) hL
  have hE : Real.exp (C2 * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) ^ 2 ≤
      Real.exp (C * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) := by
    rw [sq, ← Real.exp_add, Real.exp_le_exp, hb]
    have := mul_le_mul_of_nonneg_right hC2 hQ
    linarith
  have hX : (Ca / D.R.k) ^ (D.R.k * D.R.f) ≤ (C / D.R.k) ^ (D.R.k * D.R.f) := by
    calc (Ca / D.R.k) ^ (D.R.k * D.R.f) ≤ |Ca / D.R.k| ^ (D.R.k * D.R.f) := by
          rw [← abs_pow]; exact le_abs_self _
      _ ≤ (C / D.R.k) ^ (D.R.k * D.R.f) := by
          apply pow_le_pow_left₀ (abs_nonneg _)
          rw [abs_div, abs_of_nonneg hk0]
          exact div_le_div_of_nonneg_right hCa hk0
  have hX2 : 0 ≤ (C / D.R.k) ^ (D.R.k * D.R.f) :=
    pow_nonneg (div_nonneg (le_trans (abs_nonneg _) hCa) hk0) _
  calc GamS D large₂ * Real.exp (C2 * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) ^ 2 * (Ca / D.R.k) ^ (D.R.k * D.R.f)
      ≤ GamS D large₂ * Real.exp (C2 * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) ^ 2 * (C / D.R.k) ^ (D.R.k * D.R.f) :=
        mul_le_mul_of_nonneg_left hX (mul_nonneg hG (sq_nonneg _))
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hG) hX2

theorem rows_degB_le {C' Cl Cg cb Cu cT CT C0 A c Ca C2 Ch C : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hc : 0 ≤ c) (hcC : c ≤ C) (hC1 : 1 ≤ C)
    (hC : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2) (hC2 : 2 * C2 ≤ C) (hCa : |Ca| ≤ C) (s : ℕ) :
    rows_degB D large₂ u c Ca C2 Ch s ≤
      LatticeSumBounds.degRow C D.R.k D.R.m D.R.f s large₂.sc.b (gg D) D.host.v (GamS D large₂) (XiB D large₂ u C) := by
  have hg2 := two_le_gg_of_count_hypotheses hH.1
  have hv1 : 1 ≤ D.host.v := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h19, _⟩ := hH.1.1
    exact h19
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast rows_f_pos D
  have hP1 := rows_P_one_le D large₂ c Ch
  have hmx : 0 ≤ max (Ch - c) 0 := le_max_right _ _
  have hexp := rows_exp_nd (m := D.R.m) (f := D.R.f) (s := s) (r := D.R.rS) (c := c) (mx := max (Ch - c) 0)
    (cf := cF D.R.f) (C := C) (rows_m_cast D) (by positivity) hf (by positivity) hc hmx (rows_cF_le hH) hC
  have hpe2 : 2 * pairCountExponentShift D c Ch ≤ C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m) := by
    have e1 : pairCountExponentShift D c Ch = (c ^ 2 + 2 * max (Ch - c) 0) * ((D.R.m : ℝ) ^ 3 * D.R.f) := by
      unfold pairCountExponentShift
      have : (D.R.rS : ℝ) + 1 = (D.R.m : ℝ) / 2 := by rw [rows_m_cast]; ring
      rw [this]; ring
    have h0 : 0 ≤ (D.R.m : ℝ) ^ 3 * D.R.f := by positivity
    have h1 : 2 * (c ^ 2 + 2 * max (Ch - c) 0) ≤ C ^ 2 := by
      have : 0 ≤ (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c) := by positivity
      nlinarith
    rw [e1]
    calc 2 * ((c ^ 2 + 2 * max (Ch - c) 0) * ((D.R.m : ℝ) ^ 3 * D.R.f))
        = (2 * (c ^ 2 + 2 * max (Ch - c) 0)) * ((D.R.m : ℝ) ^ 3 * D.R.f) := by ring
      _ ≤ C ^ 2 * ((D.R.m : ℝ) ^ 3 * D.R.f) := mul_le_mul_of_nonneg_right h1 h0
      _ = _ := by ring
  have hXs0 : 0 ≤ XiS D u (rows_P D large₂ c Ch ^ 2) c s := rows_XiS_nonneg D u (by positivity) hc s
  have hXs := rows_XiP_le D large₂ u hc hcC hpe2 s
  have core := rows_num_nd (k := D.R.k) (m := D.R.m) (f := D.R.f) (s := s) (r := D.R.rS) (b := large₂.sc.b) (g := 2)
    (v := D.host.v) (Γ := rows_GamD D large₂ Ca C2) (c := c) (C := C) (pe := pairCountExponentShift D c Ch) (E1 := pairCountExponent D c s)
    (cr := c * (D.R.rS : ℝ) ^ 2) (δ := 0) (rD := 1) (XiP := XiS D u (rows_P D large₂ c Ch ^ 2) c s)
    (Xi := XiB D large₂ u C) (d_two_le_b D large₂) (by norm_num) (by linarith) (rows_GamD_nonneg D large₂ Ca C2) hc hcC hC1 le_rfl
    zero_le_one zero_le_one hXs0 hXs (by unfold pairCountExponentShift pairCountExponent; exact hexp)
  unfold LatticeSumBounds.ndRow at core
  rw [div_self (two_ne_zero), one_pow] at core
  have hA0 : 0 ≤ (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) := by
    have : 0 ≤ gg D := by linarith
    positivity
  have hbig0 : 0 ≤ LatticeSumBounds.bigH C D.R.m D.R.f large₂.sc.b ^ (C * ((s : ℝ) + D.R.m) * (D.R.m : ℝ) ^ 2) := by
    unfold LatticeSumBounds.bigH
    have := d_two_le_b D large₂
    positivity
  have hM0 : 0 ≤ ((D.R.k : ℝ) * D.host.v) ^ (D.R.k * D.R.f) * XiB D large₂ u C s * C ^ (D.R.k * D.R.f) *
      LatticeSumBounds.bigH C D.R.m D.R.f large₂.sc.b ^ (C * ((s : ℝ) + D.R.m) * (D.R.m : ℝ) ^ 2) * (C * s * D.R.f) ^ (6 * s * D.R.f) := by
    have : 0 ≤ XiB D large₂ u C s := hXs0.trans hXs
    have : 0 ≤ D.host.v := by linarith
    positivity
  unfold rows_degB rows_RD rows_Phi LatticeSumBounds.degRow
  unfold rows_P at core ⊢
  calc (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) * ((D.R.k : ℝ) * D.host.v / (Real.exp 1 * Real.pi)) ^ (D.R.k * D.R.f) *
        (XiS D u ((large₂.sc.b ^ pairCountExponentShift D c Ch) ^ 2) c s *
          (((large₂.sc.b ^ pairCountExponentShift D c Ch) ^ pairCountExponent D c s) ^ 2 * ((large₂.sc.b ^ pairCountExponentShift D c Ch) ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2 *
            (c * s * D.R.f) ^ (6 * s * D.R.f) * rows_GamD D large₂ Ca C2)) *
        ((41 ^ D.R.f * (large₂.sc.b ^ pairCountExponentShift D c Ch) ^ 3) ^ ((D.R.rS + 1) ^ 2)) ^ 2
      = (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) *
        (1 * ((D.R.k : ℝ) * D.host.v / (Real.exp 1 * Real.pi)) ^ (D.R.k * D.R.f) *
        (XiS D u ((large₂.sc.b ^ pairCountExponentShift D c Ch) ^ 2) c s *
          (((large₂.sc.b ^ pairCountExponentShift D c Ch) ^ pairCountExponent D c s) ^ 2 * ((large₂.sc.b ^ pairCountExponentShift D c Ch) ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2 *
            (c * s * D.R.f) ^ (6 * s * D.R.f) * rows_GamD D large₂ Ca C2)) * ((1 + 0) * 1) *
        ((41 ^ D.R.f * (large₂.sc.b ^ pairCountExponentShift D c Ch) ^ 3) ^ ((D.R.rS + 1) ^ 2)) ^ 2) := by ring
    _ ≤ (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) * _ := mul_le_mul_of_nonneg_left core hA0
    _ = (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) * ((((D.R.k : ℝ) * D.host.v) ^ (D.R.k * D.R.f) * XiB D large₂ u C s *
          C ^ (D.R.k * D.R.f) * LatticeSumBounds.bigH C D.R.m D.R.f large₂.sc.b ^ (C * ((s : ℝ) + D.R.m) * (D.R.m : ℝ) ^ 2) *
          (C * s * D.R.f) ^ (6 * s * D.R.f)) * rows_GamD D large₂ Ca C2) := by ring
    _ ≤ (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) * ((((D.R.k : ℝ) * D.host.v) ^ (D.R.k * D.R.f) * XiB D large₂ u C s *
          C ^ (D.R.k * D.R.f) * LatticeSumBounds.bigH C D.R.m D.R.f large₂.sc.b ^ (C * ((s : ℝ) + D.R.m) * (D.R.m : ℝ) ^ 2) *
          (C * s * D.R.f) ^ (6 * s * D.R.f)) * (GamS D large₂ * Real.exp (C * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) *
          (C / D.R.k) ^ (D.R.k * D.R.f))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (rows_GamD_le D large₂ hC2 hCa) hM0) hA0
    _ = _ := by ring

theorem rows_RowsDeg_record {C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm C : ℝ} {q : ℕ}
    (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) (hK : rows_KBound Y c) (hc1 : 1 ≤ c)
    (hcC : c ≤ C) (hC1 : 1 ≤ C)
    (hC : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2) (hC2 : 2 * C2 ≤ C) (hCa : |Ca| ≤ C)
    (hq2 : 4 * (c * D.R.k) + 4 * pairCountExponent D c D.R.k + 4 * (c * (D.R.rS : ℝ) ^ 2) +
      (C2 * (D.R.m : ℝ) ^ 2 + C2 * (D.R.m : ℝ) ^ 4 * 2) / 2 + 12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤
        (q : ℝ) / ((D.R.rS : ℝ) + 1)) : RowsDeg X Y C := by
  intro s hs hsk
  have hsk' : (s : ℝ) ≤ D.R.k := by exact_mod_cast hsk
  have hm : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hE : pairCountExponent D c s ≤ pairCountExponent D c D.R.k := by
    unfold pairCountExponent
    have := mul_nonneg (mul_nonneg h.hc (sub_nonneg.2 hsk')) hm
    linarith
  have hq2s : 4 * (c * D.R.k) + 4 * pairCountExponent D c s + 4 * (c * (D.R.rS : ℝ) ^ 2) +
      (C2 * (D.R.m : ℝ) ^ 2 + C2 * (D.R.m : ℝ) ^ 4 * 2) / 2 + 12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤
        (q : ℝ) / ((D.R.rS : ℝ) + 1) := by linarith
  exact rows_RowBound_mono Y (rows_Deg_record Y h hK hc1 s hs hsk hq2s)
    (rows_degB_le h.hH h.hc hcC hC1 hC hC2 hCa s) h.hdim.le

end Rec

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)

end Fam

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsOneF
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem decay_length_sufficient {m k r c B : ℝ} (hm : m = 2 * r + 2) (hr : 0 ≤ r) (hk : m + 3 ≤ k) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (ha : B * m ^ 5 ≤ k) :
    (r + 1) * (12 * (c * r ^ 2) + B * m ^ 2 / 2 + B * m ^ 4 + 12 * (r + 1) ^ 2) + 1 ≤ (9 * c + 3) * k * m ^ 2 := by
  have hm2 : 2 ≤ m := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hr1 : r + 1 = m / 2 := by linarith
  have e : (r + 1) * (12 * (c * r ^ 2) + B * m ^ 2 / 2 + B * m ^ 4 + 12 * (r + 1) ^ 2) + 1 =
      6 * m * (c * r ^ 2) + (B * m ^ 3) / 4 + (B * m ^ 5) / 2 + (m / 2) * (12 * (m / 2) ^ 2) + 1 := by rw [hr1]; ring
  have p1 : 6 * m * (c * r ^ 2) ≤ 2 * (c * k * m ^ 2) := by
    have a : r ^ 2 ≤ m ^ 2 / 4 := by nlinarith
    have b : c * r ^ 2 ≤ c * (m ^ 2 / 4) := mul_le_mul_of_nonneg_left a hc
    have d : 6 * m * (c * r ^ 2) ≤ 6 * m * (c * (m ^ 2 / 4)) := mul_le_mul_of_nonneg_left b (by linarith)
    nlinarith [mul_nonneg (mul_nonneg hc (sq_nonneg m)) (by linarith : 0 ≤ k - m)]
  have m35 : m ^ 3 ≤ m ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have p2 : B * m ^ 3 ≤ k := le_trans (mul_le_mul_of_nonneg_left m35 hB) ha
  have p4 : (m / 2) * (12 * (m / 2) ^ 2) ≤ (3 / 2) * (k * m ^ 2) := by
    nlinarith [mul_nonneg (sq_nonneg m) (by linarith : 0 ≤ k - m)]
  have p5 : (1 : ℝ) ≤ (1 / 2) * (k * m ^ 2) := by nlinarith
  have hm4 : 4 ≤ m ^ 2 := by nlinarith
  have p6 : k ≤ (1 / 4) * (k * m ^ 2) := by nlinarith [mul_nonneg hk0 (sub_nonneg.2 hm4)]
  have hU : 0 ≤ c * k * m ^ 2 := by positivity
  rw [e]
  have t : (9 * c + 3) * k * m ^ 2 = 9 * (c * k * m ^ 2) + 3 * (k * m ^ 2) := by ring
  rw [t]
  linarith

theorem le_max_four (a b c d : ℝ) : a ≤ max (max a b) (max c d) ∧ b ≤ max (max a b) (max c d) ∧
    c ≤ max (max a b) (max c d) ∧ d ≤ max (max a b) (max c d) :=
  ⟨le_trans (le_max_left _ _) (le_max_left _ _), le_trans (le_max_right _ _) (le_max_left _ _),
    le_trans (le_max_left _ _) (le_max_right _ _), le_trans (le_max_right _ _) (le_max_right _ _)⟩

section Mono

variable {D : D7} {large₂ : SizeData₂ D} {u u' : D.what₂.Word}

theorem height_pow_mono_constant (large₂ : SizeData₂ D) (hrd : 0 < D.host.rdE) {c' c : ℝ} (h : |c'| + 2 ≤ c) (Z : GramM D) :
    HHZ D large₂.sc.b c' Z ^ (c' * (D.R.rS : ℝ) ^ 2) ≤ HHZ D large₂.sc.b c Z ^ (c * (D.R.rS : ℝ) ^ 2) := by
  have h1 : c' ≤ c := by linarith [le_abs_self c']
  have h2 : 2 ≤ c + c' := by linarith [neg_abs_le c']
  have mono := rows_HHZ_mono large₂ hrd h1 h2 Z
  have o := rows_one_le_HHZ' D large₂ c' Z
  have hc : 0 ≤ c := by linarith [abs_nonneg c']
  calc HHZ D large₂.sc.b c' Z ^ (c' * (D.R.rS : ℝ) ^ 2) ≤ HHZ D large₂.sc.b c' Z ^ (c * (D.R.rS : ℝ) ^ 2) :=
        Real.rpow_le_rpow_of_exponent_le o (by gcongr)
    _ ≤ HHZ D large₂.sc.b c Z ^ (c * (D.R.rS : ℝ) ^ 2) := Real.rpow_le_rpow (by linarith) mono (by positivity)

theorem switch_bound_mono_constant {C' Cl Cg cb Cu cT CT C0 A c' c : ℝ} (h1 : |c'| + 2 ≤ c)
    (h : UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c') : UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c := by
  intro hH F0 he hz what₂ hrows Z hZ
  have h0 := h hH F0 he hz what₂ hrows Z hZ
  unfold MeanLe at h0 ⊢
  have hB : HHZ D large₂.sc.b c' Z ^ (c' * (D.R.rS : ℝ) ^ 2) * ∏ τ, nV D (Tu D u) (Tu D u') Z τ ≤
      HHZ D large₂.sc.b c Z ^ (c * (D.R.rS : ℝ) ^ 2) * ∏ τ, nV D (Tu D u) (Tu D u') Z τ := by
    refine mul_le_mul_of_nonneg_right (height_pow_mono_constant large₂ (d_rdE_pos hH.1) h1 Z) ?_
    refine Finset.prod_nonneg fun τ _ => ?_
    unfold nV
    exact D.R.k_even.pow_nonneg _
  exact h0.trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hB))

theorem partner_count_bound_mono_constant {C' Cl Cg cb Cu cT CT C0 A c' c : ℝ} (h1 : |c'| + 2 ≤ c)
    (h : UnitaryVolumeMass.PartnerCountBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c') : UnitaryVolumeMass.PartnerCountBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c := by
  intro hH F0 he hz Λ hΛ F' hF' hgen hR Z hZ
  refine (h hH F0 he hz Λ hΛ F' hF' hgen hR Z hZ).trans (ENNReal.ofReal_le_ofReal ?_)
  have hrd := d_rdE_pos hH.1
  have k1 : c' ≤ c := by linarith [le_abs_self c']
  have k2 : 2 ≤ c + c' := by linarith [neg_abs_le c']
  have hc : 0 ≤ c := by linarith [abs_nonneg c']
  have ma := rows_HHZ_mono large₂ hrd k1 k2 (ZhatL (lf D F0) F')
  have mb := rows_HHZ_mono large₂ hrd k1 k2 Z
  have oa := rows_one_le_HHZ' D large₂ c' (ZhatL (lf D F0) F')
  have ob := rows_one_le_HHZ' D large₂ c' Z
  have o : 1 ≤ HHZ D large₂.sc.b c' (ZhatL (lf D F0) F') * HHZ D large₂.sc.b c' Z := one_le_mul_of_one_le_of_one_le oa ob
  have hp : c' ^ D.R.f ≤ c ^ D.R.f :=
    (le_abs_self _).trans (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) _)
  refine mul_le_mul hp ?_ (Real.rpow_nonneg (by linarith) _) (pow_nonneg hc _)
  calc (HHZ D large₂.sc.b c' (ZhatL (lf D F0) F') * HHZ D large₂.sc.b c' Z) ^ (c' * (D.R.rS : ℝ) ^ 2)
      ≤ (HHZ D large₂.sc.b c' (ZhatL (lf D F0) F') * HHZ D large₂.sc.b c' Z) ^ (c * (D.R.rS : ℝ) ^ 2) :=
        Real.rpow_le_rpow_of_exponent_le o (by gcongr)
    _ ≤ _ := Real.rpow_le_rpow (by linarith) (mul_le_mul ma mb (by linarith) (by linarith)) (by positivity)

end Mono

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)

end Fam

end Formalism.MainNotions.BridgeLemma₂

end
end

