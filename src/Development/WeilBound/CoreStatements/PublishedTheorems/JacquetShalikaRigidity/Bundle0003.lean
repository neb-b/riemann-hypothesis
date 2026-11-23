module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.DminNonneg
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PKIR

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem dt_pos (g : GA E k) : 0 < Dt g := (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det g)).2

theorem ht_nonneg (g : GA E k) (ξ : Fin k → E) : 0 ≤ ht g ξ :=
  div_nonneg (height_nonneg _ _) (Real.rpow_nonneg (dt_pos g).le _)

theorem dmin_nonneg (g : GA E k) : 0 ≤ dmin g := by
  unfold dmin
  exact Real.iInf_nonneg fun ξ => ht_nonneg g ξ.1

theorem wt_nonneg (M : ℕ) (g : GA E k) : 0 ≤ wt M g := by
  unfold wt
  exact pow_nonneg (le_min zero_le_one (dmin_nonneg g)) M

end PKIR

theorem kir_of : jumpWindows.S2 → jumpWindows.G0 → jumpWindows.G2a → jumpWindows.G2c → jumpWindows.G5 → jumpWindows.G5b → K2 → K3 → K4 → K9 → KIR := by
  intro hS2 hG0 hG2a hG2c _hG5 hG5b hK2 hK3 hK4 hK9 E _ _ _ k hk ψ hψ hcof π hπ
  obtain ⟨S₀, hS₀⟩ := hK9 E k hk ψ hψ hcof π hπ
  refine ⟨S₀, fun S hS α hα M j hj U hU Y hYc hYi hYπ => ?_⟩
  obtain ⟨_hcond, h9⟩ := hS₀ S hS
  obtain ⟨φ, hφ, h, x, hhS, hx, hsat, hlev, hwh⟩ := h9 α hα
  obtain ⟨ρ, J, hW, hsm⟩ := hK2 E k hk M
  obtain ⟨x₀, hx₀, hsm₀⟩ := hK3 E k hk M ρ J hW π hπ φ hφ
  have hJx₀ : J x₀ = x := DFunLike.coe_injective (hx₀.trans hx.symm)

  obtain ⟨_, _, _, hSg, hST, _⟩ := hS2 _ k (XB E k) (ρ.comp (infGL E k)) hW.poly
  obtain ⟨g1, g2, _, _, _, _, g7, _⟩ := hG0 E k
  have hsm1 : SmV (ρ.comp (infGL E k)) (ρ h x₀) := by
    set y := cInf h
    set hf := (infGL E k y)⁻¹ * h
    have hcf : cInf hf = 1 := by simp only [hf, map_mul, map_inv, g1, y, inv_mul_cancel]
    have hc : ∀ (g : GL (Fin k) (Cinf E)) z, ρ hf ((ρ.comp (infGL E k)) g z) = (ρ.comp (infGL E k)) g (ρ hf z) := by
      intro g z
      simp only [MonoidHom.comp_apply]
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, g7 hf hcf g, map_mul, ContinuousLinearMap.mul_apply]
    have := hSg y _ (hST (ρ hf) hc x₀ hsm₀)
    simpa only [MonoidHom.comp_apply, ← ContinuousLinearMap.mul_apply, ← map_mul, hf, mul_inv_cancel_left] using this

  obtain ⟨Yg, hYgc, hYgi, hYgm⟩ := hG2a E k ψ hψ
  have hw := fun w : Off E S => hG2c E k w.1 (Finset.univ.val.map (α w)) (by simp)
  choose Yw hYwc hYwi hYwm using hw
  set Y' : Submodule ℂ (XB E k) := Y ⊓ Yg ⊓ ⨅ w, Yw w with hY'
  have hmem : ∀ z, z ∈ Y' ↔ (z ∈ Y ∧ z ∈ Yg) ∧ ∀ w, z ∈ Yw w := fun z => by
    simp only [Y', Submodule.mem_inf, Submodule.mem_iInf]
  have hYOK : YOK ψ S Y' := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Submodule.coe_inf, Submodule.coe_inf, Submodule.coe_iInf]
      exact (hYc.inter hYgc).inter (isClosed_iInter hYwc)
    · intro g hg z hz
      rw [hmem] at hz ⊢
      exact ⟨⟨hYi g z hz.1.1, hYgi g z hz.1.2⟩, fun w => hYwi w g (hg w.1 w.2) z (hz.2 w)⟩
    · intro z hz
      exact ((hYgm z).1 ((hmem z).1 hz).1.2).1
  have hcusp := π.cusp φ hφ
  have hxY' : Rt E k h x ∈ Y' := by
    have hxg : x ∈ Yg := by
      refine (hYgm x).2 ⟨?_, fun γ g => ?_⟩
      · rw [hx]; exact _root_.GlobalTheory.CuspGeneric.good_of_isCuspForm E k ψ φ hcusp
      · rw [congrFun hx, congrFun hx]; exact hcusp.1.left γ g
    rw [hmem]
    exact ⟨⟨hYi h x (hYπ x ⟨φ, hφ, hx⟩), hYgi h x hxg⟩,
      fun w => hYwi w h (hhS w.1 w.2) x ((hYwm w x).2 (hsat w))⟩
  have hJ1 : J (ρ h x₀) = Rt E k h x := by rw [hW.inter, hJx₀]
  obtain ⟨x', C, hCU, hx'Y, hsm', hlev', hBlk, hBump⟩ := hK4 E k (wt M) ρ J hW ψ hψ S Y' hYOK j hj U hU (ρ h x₀)
    (hJ1 ▸ hxY') hsm1 (hJ1 ▸ (hG5b E k S).2.1 h x hlev) (hJ1 ▸ hwh)
  obtain ⟨⟨hx'1, hx'2⟩, hx'3⟩ := (hmem _).1 hx'Y
  obtain ⟨hgood, hinv⟩ := (hYgm _).1 hx'2
  refine ⟨J x', hx'1, ⟨hgood, hinv, fun w => (hYwm w _).1 (hx'3 w), hsm x' hsm', hlev', ?_, ⟨C, hCU, hBlk, hBump⟩⟩⟩
  refine ⟨‖x'‖, fun g => ?_⟩
  have hw0 := PKIR.wt_nonneg M g
  rw [hW.mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0, mul_comm ‖x'‖]
  exact mul_le_mul_of_nonneg_left (x'.norm_coe_le_norm g) hw0

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.EuclideanHeightMul
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace EuclideanHeightMul

open GroundTheory.Automorphic

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem euclid_add {F : Type*} [NormedField F] {n : ℕ} (y z : Fin n → F) :
    Reduction.euclidNorm (y + z) ≤ Reduction.euclidNorm y + Reduction.euclidNorm z := by
  have h : ∀ x : Fin n → F, Reduction.euclidNorm x = ‖(WithLp.toLp 2 x : PiLp 2 (fun _ : Fin n => F))‖ := by
    intro x; rw [PiLp.norm_eq_of_L2]; rfl
  rw [h, h, h, WithLp.toLp_add]
  exact norm_add_le _ _

theorem euclid_vecMul_near {F : Type*} [NormedField F] {n : ℕ} {M : Matrix (Fin n) (Fin n) F} {m : ℝ}
    (hm : 0 ≤ m) (hM : ∀ i j, ‖(M - 1) i j‖ ≤ m) (z : Fin n → F) :
    Reduction.euclidNorm (z ᵥ* M) ≤ (1 + √n * (n * m)) * Reduction.euclidNorm z := by
  have e : z ᵥ* M = z + z ᵥ* (M - 1) := by rw [Matrix.vecMul_sub, Matrix.vecMul_one]; abel
  rw [e]
  refine (euclid_add _ _).trans ?_
  have := Reduction.euclidNorm_vecMul_le hm hM z
  linarith

def Vn (m : ℝ) : Set (GA E k) :=
  {c | (∀ w : InfinitePlace E, ∀ i j,
      ‖((Reduction.infAt w c : Matrix (Fin k) (Fin k) w.Completion) - 1) i j‖ < m) ∧
    ∀ v, v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 E))) →
      Reduction.finAt v c ∈ GLnLocal.integralGL (v.adicCompletion E) k}

theorem Vn_mem {m : ℝ} (hm : 0 < m) : Vn (E := E) (k := k) m ∈ 𝓝 (1 : GA E k) := by
  have hinf : ∀ᶠ c in 𝓝 (1 : GA E k), ∀ w : InfinitePlace E, ∀ i j,
      ‖((Reduction.infAt w c : Matrix (Fin k) (Fin k) w.Completion) - 1) i j‖ < m := by
    refine Filter.eventually_all.2 fun w => Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    have hc : Continuous fun c : GA E k =>
        ‖((Reduction.infAt w c : Matrix (Fin k) (Fin k) w.Completion) - 1) i j‖ := by
      simp only [Matrix.sub_apply]
      exact (((Reduction.continuous_GL_apply i j).comp (Reduction.continuous_infAt w)).sub continuous_const).norm
    have h1 : ‖((Reduction.infAt w (1 : GA E k) : Matrix (Fin k) (Fin k) w.Completion) - 1) i j‖ = 0 := by
      simp [Reduction.infAt]
    exact hc.continuousAt.eventually_lt continuousAt_const (by rw [h1]; exact hm)
  have hfin := (Reduction.isOpen_setOf_forall_not_mem_imp (K := E) (n := k) ∅).mem_nhds
    (fun v _ => by
      have h1 : Reduction.finAt v (1 : GA E k) = 1 := by
        have h := Reduction.finAt_mul (K := E) (n := k) v 1 1
        rw [mul_one] at h
        exact left_eq_mul.1 h
      rw [h1]; exact Subgroup.one_mem _)
  filter_upwards [hinf, hfin] with c h1 h2
  exact ⟨h1, h2⟩

theorem height_mul_le {m : ℝ} (hm : 0 ≤ m) {c : GA E k} (hc : c ∈ Vn m) (g : GA E k) {ξ : Fin k → E}
    (hξ : ξ ≠ 0) : Reduction.height (g * c) ξ ≤
      (∏ w : InfinitePlace E, (1 + √k * (k * m)) ^ w.mult) * Reduction.height g ξ := by
  have hy := Reduction.hasFiniteContent_height g hξ
  have e : Reduction.height (g * c) ξ = Reduction.adelicNorm
      ((Reduction.ratVec ξ ᵥ* (g : Matrix (Fin k) (Fin k) (Ad E))) ᵥ* (c : Matrix (Fin k) (Fin k) (Ad E))) := by
    rw [Reduction.height, Units.val_mul, ← Matrix.vecMul_vecMul]
  rw [e, Reduction.height]
  have := Reduction.adelicNorm_le_of_local (hy.vecMul c) hy (fun _ => 1 + √k * (k * m)) (fun _ => 1) ∅
    (fun w => ?_) (fun _ _ => rfl) (fun v => ?_)
  · simpa only [Finset.prod_empty, mul_one] using this
  · rw [Reduction.infComp_vecMul_GL]
    exact euclid_vecMul_near hm (fun i j => (hc.1 w i j).le) _
  · rw [Reduction.finComp_vecMul_GL, Reduction.norm_vecMul_integralGL v (hc.2 v (Finset.notMem_empty v)), one_mul]

theorem exists_m {s : ℝ} (hs : 1 < s) :
    ∃ m : ℝ, 0 < m ∧ (∏ w : InfinitePlace E, (1 + √k * (k * m)) ^ w.mult) ≤ s := by
  have hcont : Continuous fun m : ℝ => ∏ w : InfinitePlace E, (1 + √k * (k * m)) ^ w.mult := by
    fun_prop
  have hev : ∀ᶠ m in 𝓝 (0 : ℝ), (∏ w : InfinitePlace E, (1 + √k * (k * m)) ^ w.mult) < s :=
    hcont.continuousAt.eventually_lt continuousAt_const (by simpa using hs)
  obtain ⟨m, hm, h⟩ := hev.exists_gt
  exact ⟨m, hm, h.le⟩

end EuclideanHeightMul

namespace EuclideanHeightMul

open GroundTheory.Automorphic

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem ht_mul_le (hDpos : ∀ g : GA E k, 0 < Dt g) (hDmul : ∀ g h : GA E k, Dt (g * h) = Dt g * Dt h)
    (hDcont : Continuous (Dt : GA E k → ℝ)) {r : ℝ} (hr : 1 < r) :
    ∃ U ∈ 𝓝 (1 : GA E k), ∀ c ∈ U, ∀ g ξ, ξ ≠ 0 → ht (g * c) ξ ≤ r * ht g ξ := by
  have hs : 1 < √r := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt zero_le_one hr
  obtain ⟨m, hm, hprod⟩ := exists_m (E := E) (k := k) hs
  have hD1 : Dt (1 : GA E k) = 1 := by
    have h := hDmul 1 1
    rw [mul_one] at h
    exact (mul_left_cancel₀ (hDpos 1).ne' (h.symm.trans (mul_one _).symm))
  have hcont : ContinuousAt (fun c : GA E k => (Dt c ^ (k : ℝ)⁻¹)⁻¹) 1 :=
    ((hDcont.rpow_const (fun _ => Or.inr (by positivity))).inv₀
      (fun c => (Real.rpow_pos_of_pos (hDpos c) _).ne')).continuousAt
  have hev : ∀ᶠ c in 𝓝 (1 : GA E k), (Dt c ^ (k : ℝ)⁻¹)⁻¹ < √r :=
    hcont.eventually_lt continuousAt_const (by simpa [hD1] using hs)
  refine ⟨{c | c ∈ Vn m ∧ (Dt c ^ (k : ℝ)⁻¹)⁻¹ < √r}, Filter.inter_mem (Vn_mem hm) hev, ?_⟩
  rintro c ⟨hc, hc2⟩ g ξ hξ
  have h1 := height_mul_le hm.le hc g hξ
  have hh0 : 0 ≤ Reduction.height g ξ := Reduction.height_nonneg _ _
  have ha : 0 < Dt g ^ (k : ℝ)⁻¹ := Real.rpow_pos_of_pos (hDpos g) _
  have hb : 0 < Dt c ^ (k : ℝ)⁻¹ := Real.rpow_pos_of_pos (hDpos c) _
  have hs0 : 0 ≤ √r := Real.sqrt_nonneg r
  unfold ht
  rw [hDmul, Real.mul_rpow (hDpos g).le (hDpos c).le]
  have h2 : Reduction.height (g * c) ξ ≤ √r * Reduction.height g ξ :=
    h1.trans (mul_le_mul_of_nonneg_right hprod hh0)
  calc Reduction.height (g * c) ξ / (Dt g ^ (k : ℝ)⁻¹ * Dt c ^ (k : ℝ)⁻¹)
      = Reduction.height (g * c) ξ * (Dt c ^ (k : ℝ)⁻¹)⁻¹ / Dt g ^ (k : ℝ)⁻¹ := by
        field_simp
    _ ≤ (√r * Reduction.height g ξ) * √r / Dt g ^ (k : ℝ)⁻¹ := by
        gcongr
    _ = (√r * √r) * (Reduction.height g ξ / Dt g ^ (k : ℝ)⁻¹) := by ring
    _ = r * (Reduction.height g ξ / Dt g ^ (k : ℝ)⁻¹) := by
        rw [Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ r)]

theorem bdd (hpos : ∀ (g : GA E k) ξ, ξ ≠ 0 → 0 < ht g ξ) (g : GA E k) :
    BddBelow (Set.range fun ξ : {ξ : Fin k → E // ξ ≠ 0} => ht g ξ.1) :=
  ⟨0, by rintro _ ⟨ξ, rfl⟩; exact (hpos g ξ.1 ξ.2).le⟩

theorem dmin_le (hpos : ∀ (g : GA E k) ξ, ξ ≠ 0 → 0 < ht g ξ) (g : GA E k) {ξ : Fin k → E} (hξ : ξ ≠ 0) :
    dmin g ≤ ht g ξ :=
  ciInf_le (bdd hpos g) (⟨ξ, hξ⟩ : {ξ : Fin k → E // ξ ≠ 0})

theorem dmin_eq (hDpos : ∀ g : GA E k, 0 < Dt g) (hpos : ∀ (g : GA E k) ξ, ξ ≠ 0 → 0 < ht g ξ)
    (hk : 1 ≤ k) (g : GA E k) : ∃ x : Fin k → E, x ≠ 0 ∧ dmin g = ht g x := by
  obtain ⟨x, hx, h⟩ := Reduction.exists_height_min (K := E) hk g
  have : Nonempty {ξ : Fin k → E // ξ ≠ 0} := ⟨⟨x, hx⟩⟩
  refine ⟨x, hx, le_antisymm (dmin_le hpos g hx) (le_ciInf fun ξ => ?_)⟩
  exact div_le_div_of_nonneg_right (h ξ.1 ξ.2) (Real.rpow_nonneg (hDpos g).le _)

theorem dmin_mul_le (hDpos : ∀ g : GA E k, 0 < Dt g) (hpos : ∀ (g : GA E k) ξ, ξ ≠ 0 → 0 < ht g ξ)
    (hk : 1 ≤ k) {r : ℝ} {c : GA E k} (hc : ∀ g ξ, ξ ≠ 0 → ht (g * c) ξ ≤ r * ht g ξ) (g : GA E k) :
    dmin (g * c) ≤ r * dmin g := by
  obtain ⟨x, hx, e⟩ := dmin_eq hDpos hpos hk g
  rw [e]
  exact (dmin_le hpos _ hx).trans (hc g x hx)

end EuclideanHeightMul

open EuclideanHeightMul in
theorem firstCohomologyBound_of_boundaryBound : D0 → H0 → K1 := by
  intro hD hH E _ _ _ k hk
  obtain ⟨hDpos, hDmul, hDcont, -⟩ := hD E k
  obtain ⟨hpos, hrat, -, hcpt, -⟩ := hH E k
  have dpos : ∀ g : GA E k, 0 < dmin g := fun g => by
    obtain ⟨x, hx, e⟩ := dmin_eq hDpos hpos hk g
    rw [e]; exact hpos g x hx
  refine ⟨?_, dpos, fun g ξ hξ => dmin_le hpos g hξ, ?_, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g₀ => tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
    · have hev : ∀ᶠ r in 𝓝 (1 : ℝ), r * a < dmin g₀ :=
        (continuous_id.mul continuous_const).continuousAt.eventually_lt continuousAt_const (by simpa using ha)
      obtain ⟨r, hr, hra⟩ := hev.exists_gt
      obtain ⟨U, hU, hUr⟩ := ht_mul_le hDpos hDmul hDcont hr
      have ht : Filter.Tendsto (fun g : GA E k => g⁻¹ * g₀) (𝓝 g₀) (𝓝 1) := by
        have h : Filter.Tendsto (fun g : GA E k => g⁻¹ * g₀) (𝓝 g₀) (𝓝 (g₀⁻¹ * g₀)) :=
          (continuous_inv.mul continuous_const).tendsto g₀
        rwa [inv_mul_cancel] at h
      filter_upwards [ht hU] with g hg
      have h := dmin_mul_le hDpos hpos hk (hUr _ hg) g
      rw [mul_inv_cancel_left] at h
      have : r * a < r * dmin g := by linarith
      exact lt_of_mul_lt_mul_left this (by linarith)
    · have hev : ∀ᶠ r in 𝓝 (1 : ℝ), r * dmin g₀ < b :=
        (continuous_id.mul continuous_const).continuousAt.eventually_lt continuousAt_const (by simpa using hb)
      obtain ⟨r, hr, hrb⟩ := hev.exists_gt
      obtain ⟨U, hU, hUr⟩ := ht_mul_le hDpos hDmul hDcont hr
      have ht : Filter.Tendsto (fun g : GA E k => g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := by
        have h : Filter.Tendsto (fun g : GA E k => g₀⁻¹ * g) (𝓝 g₀) (𝓝 (g₀⁻¹ * g₀)) :=
          (continuous_const.mul continuous_id).tendsto g₀
        rwa [inv_mul_cancel] at h
      filter_upwards [ht hU] with g hg
      have h := dmin_mul_le hDpos hpos hk (hUr _ hg) g₀
      rw [mul_inv_cancel_left] at h
      linarith
  · have hge : ∀ (γ : GL (Fin k) E) (g : GA E k), dmin g ≤ dmin (ratGL E k γ * g) := by
      intro γ g
      obtain ⟨x, hx, e⟩ := dmin_eq hDpos hpos hk (ratGL E k γ * g)
      rw [e, hrat]
      refine dmin_le hpos g fun h0 => hx ?_
      have := congrArg (· ᵥ* (γ⁻¹ : GL (Fin k) E).val) h0
      simpa [Matrix.vecMul_vecMul] using this
    intro γ g
    refine le_antisymm ?_ (hge γ g)
    have := hge γ⁻¹ (ratGL E k γ * g)
    rwa [map_inv, inv_mul_cancel_left] at this
  · intro C hC
    obtain ⟨B, hB⟩ := hcpt C hC
    refine ⟨max B 1, le_max_right _ _, fun c hc g => ?_⟩
    exact dmin_mul_le hDpos hpos hk (fun g ξ hξ =>
      (hB c hc g ξ hξ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hpos g ξ hξ).le)) g
  · intro f hf M
    obtain ⟨C0, h0⟩ := hf 0
    obtain ⟨C1, h1⟩ := hf M
    refine ⟨max C0 C1, fun g => ?_⟩
    obtain ⟨x, hx, e⟩ := dmin_eq hDpos hpos hk g
    have a := h0 g x hx
    have b := h1 g x hx
    rw [pow_zero, mul_one] at a
    rw [← e] at b
    unfold wt
    by_cases hd : dmin g ≤ 1
    · rw [min_eq_right hd]
      exact b.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (dpos g).le M))
    · rw [min_eq_left (le_of_not_ge hd), one_pow, mul_one]
      exact a.trans (le_max_left _ _)

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.HeightDropSingle
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace HeightDropSingle

open scoped NumberField.AdeleRing

theorem euclid_drop {F : Type*} [NormedField F] {n : ℕ} (p : Fin (n + 1)) (z : Fin (n + 1) → F)
    (hz : z p = 0) : euclidNorm z = euclidNorm (fun j => z (p.succAbove j)) := by
  simp only [euclidNorm]
  rw [Fin.sum_univ_succAbove _ p, hz]
  simp

theorem sup_drop {F : Type*} [NormedField F] {n : ℕ} (p : Fin (n + 1)) (z : Fin (n + 1) → F)
    (hz : z p = 0) : ‖z‖ = ‖fun j => z (p.succAbove j)‖ := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    rcases Fin.eq_self_or_eq_succAbove p i with rfl | ⟨j, rfl⟩
    · rw [hz, norm_zero]; exact norm_nonneg _
    · exact norm_le_pi_norm (fun j => z (p.succAbove j)) j
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => norm_le_pi_norm z _

theorem adelicNorm_drop {K : Type*} [Field K] [NumberField K] {n : ℕ} (p : Fin (n + 1))
    (y : Fin (n + 1) → 𝔸[K]) (hy : y p = 0) :
    adelicNorm y = adelicNorm (fun j => y (p.succAbove j)) := by
  unfold adelicNorm
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [euclid_drop p (infComp w y) (by show (y p).1 w = 0; rw [hy]; rfl)]
    rfl
  · refine finprod_congr fun v => ?_
    rw [sup_drop p (finComp v y) (by show (y p).2 v = 0; rw [hy]; rfl)]
    rfl

theorem height_single {K : Type*} [Field K] [NumberField K] {n : ℕ} (x : GL (Fin n) 𝔸[K]) (i : Fin n)
    (hx : x.val i = Pi.single i 1) : Reduction.height x (Pi.single i (1 : K)) = 1 := by
  unfold Reduction.height
  have : ratVec (Pi.single i (1 : K)) ᵥ* (x : Matrix (Fin n) (Fin n) 𝔸[K]) = x.val i := by
    ext c
    simp [ratVec, vecMul, dotProduct, Pi.single_apply]
  rw [this, hx, adelicNorm_single_one]

end HeightDropSingle

theorem short_rows_embedding_of : D0 → MinkowskiBoundAlt → K1 → CornerEmbedding → ShortRowsEmbedding := by
  intro hD hG hK1 hK5e E _ _ _ m k hk hkm ι hι
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨C, hC⟩ := hG E n (by omega)
  have hDm := hD E (n + 1)
  have hDk := hD E k
  have hDι : ∀ g, Dt (ι g) = Dt g := ((hK5e E (n + 1) k hkm.le).2 ι hι).2.2.2.1
  have hK := (hK1 E (n + 1) (by omega)).2.2.1
  refine ⟨C, fun g u => ⟨fun hu => ?_, fun hu => ?_⟩⟩
  · obtain ⟨x, hx⟩ : ∃ x, x = u * ι g := ⟨_, rfl⟩
    rw [← hx]
    have hDx : Dt x = Dt g := by rw [hx, hDm.2.1, hDm.2.2.2.2.1 0 u hu, hDι, one_mul]
    have hrow : x.val (Fin.last n) = Pi.single (Fin.last n) 1 := by
      ext c
      rw [hx, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last n)]
      · rw [hu.2.1, one_mul, hι g]
        have hk' : ¬ ((Fin.last n : ℕ) < k ∧ (c : ℕ) < k) := by simp; omega
        simp only [embM, Matrix.of_apply, dif_neg hk', Matrix.one_apply, Pi.single_apply, eq_comm]
      · intro j _ hj
        rw [hu.1 _ _ (lt_of_le_of_ne (Fin.le_last j) hj), zero_mul]
      · simp
    have hpos := hDk.1 g
    refine (hK x (Pi.single (Fin.last n) 1) fun h => by simpa using congrFun h (Fin.last n)).trans (le_of_eq ?_)
    unfold ht
    rw [HeightDropSingle.height_single x _ hrow, hDx, Real.rpow_neg hpos.le, one_div]
  · obtain ⟨x, hx⟩ : ∃ x, x = u * ι g := ⟨_, rfl⟩
    rw [← hx]
    have hDx : Dt x = Dt g := by rw [hx, hDm.2.1, hDm.2.2.2.2.1 (k + 1) u hu, hDι, one_mul]
    set p : Fin (n + 1) := ⟨k, hkm⟩ with hp
    have hcol : ∀ i, x.val i p = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) (Ad E)) i p := by
      intro i
      rw [hx, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single p]
      · rw [hι g]
        have hk' : ¬ ((p : ℕ) < k ∧ (p : ℕ) < k) := by simp [p]
        simp only [embM, Matrix.of_apply, dif_neg hk', Matrix.one_apply_eq, mul_one]
        exact hu.2.2 i p (by simp [p])
      · intro j _ hj
        rw [hι g]
        have hk' : ¬ ((j : ℕ) < k ∧ (p : ℕ) < k) := by simp [p]
        simp only [embM, Matrix.of_apply, dif_neg hk', Matrix.one_apply_ne hj, mul_zero]
      · simp
    set M' : Matrix (Fin n) (Fin n) (Ad E) := x.val.submatrix p.succAbove p.succAbove with hM'
    have hdet : M'.det = x.val.det := by
      rw [Matrix.det_succ_column x.val p, Finset.sum_eq_single p]
      · rw [hcol, Matrix.one_apply_eq, mul_one, Even.neg_one_pow ⟨(p : ℕ), rfl⟩, one_mul]
      · intro i _ hi
        rw [hcol, Matrix.one_apply_ne hi, mul_zero, zero_mul]
      · simp
    have hunit : IsUnit M'.det := by
      rw [hdet]; exact (Matrix.GeneralLinearGroup.det x).isUnit
    let g' : GA E n := M'.nonsingInvUnit hunit
    have hDg' : Dt g' = Dt x := by
      have : GeneralLinearGroup.det g' = GeneralLinearGroup.det x := Units.ext hdet
      unfold Dt; rw [this]
    obtain ⟨ξ', hξ'0, hξ'⟩ := hC g'
    let ξ : Fin (n + 1) → E := p.insertNth 0 ξ'
    have hξ0 : ξ ≠ 0 := by
      intro h; apply hξ'0; ext j
      simpa [ξ] using congrFun h (p.succAbove j)
    have hht : Reduction.height x ξ = Reduction.height g' ξ' := by
      unfold Reduction.height
      rw [HeightDropSingle.adelicNorm_drop p]
      · congr 1
        ext c
        simp only [vecMul, dotProduct]
        rw [Fin.sum_univ_succAbove _ p]
        simp [ξ, ratVec, g', M']
        rfl
      · simp only [vecMul, dotProduct]
        rw [Fin.sum_univ_succAbove _ p]
        simp [ξ, ratVec, hcol, Matrix.one_apply_ne (Fin.succAbove_ne p _)]
    have hpos := hDk.1 g
    refine (hK x ξ hξ0).trans ?_
    unfold ht at hξ' ⊢
    rw [hht, hDx]
    rw [hDg', hDx] at hξ'
    have h1 : Reduction.height g' ξ' ≤ C * Dt g ^ ((n : ℝ)⁻¹) :=
      (div_le_iff₀ (Real.rpow_pos_of_pos hpos _)).1 hξ'
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hpos _)]
    calc Reduction.height g' ξ' ≤ C * Dt g ^ ((n : ℝ)⁻¹) := h1
      _ = C * Dt g ^ ((((n + 1 : ℕ) : ℝ) - 1)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹) * Dt g ^ (((n + 1 : ℕ) : ℝ)⁻¹) := by
        rw [mul_assoc, ← Real.rpow_add hpos]
        congr 2
        push_cast
        ring

end PositivityTheory.AdelicQuotientData

end
end

