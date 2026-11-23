module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0036

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LinIndOrth
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.NormUnitsOrthogonality

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases Formalism.L2.SG.Pf.UnitPairSolutions

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

def NU (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (x : K) : Prop :=
  ∃ l : K, l ≠ 0 ∧ x * (l * star l) ∈ SP K 𝔭 ∧ (x * (l * star l))⁻¹ ∈ SP K 𝔭

variable {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime]

theorem NU.of_unit {u : K} (h1 : u ∈ SP K 𝔭) (h2 : u⁻¹ ∈ SP K 𝔭) : NU 𝔭 u :=
  ⟨1, one_ne_zero, by simpa using h1, by simpa using h2⟩

theorem NU.mul {x y : K} (hx : NU 𝔭 x) (hy : NU 𝔭 y) : NU 𝔭 (x * y) := by
  obtain ⟨a, ha, ha1, ha2⟩ := hx
  obtain ⟨b, hb, hb1, hb2⟩ := hy
  have e : x * y * (a * b * star (a * b)) = (x * (a * star a)) * (y * (b * star b)) := by
    rw [star_mul']
    ring
  refine ⟨a * b, mul_ne_zero ha hb, ?_, ?_⟩
  · rw [e]
    exact (SP K 𝔭).mul_mem ha1 hb1
  · rw [e, mul_inv]
    exact (SP K 𝔭).mul_mem ha2 hb2

theorem NU.inv {x : K} (hx : NU 𝔭 x) : NU 𝔭 x⁻¹ := by
  obtain ⟨a, ha, h1, h2⟩ := hx
  have hs : star a⁻¹ = (star a)⁻¹ := by
    first | exact star_inv₀ a | exact star_inv' a | simp
  have e : x⁻¹ * (a⁻¹ * star a⁻¹) = (x * (a * star a))⁻¹ := by
    rw [hs, mul_inv, mul_inv]
  refine ⟨a⁻¹, inv_ne_zero ha, ?_, ?_⟩
  · rw [e]
    exact h2
  · rw [e, inv_inv]
    exact h1

theorem NU.of_mul_left {x y : K} (hxy : NU 𝔭 (x * y)) (hy : NU 𝔭 y) (hy0 : y ≠ 0) : NU 𝔭 x := by
  have h := NU.mul hxy (NU.inv hy)
  rwa [mul_assoc, mul_inv_cancel₀ hy0, mul_one] at h

theorem NU.norm_mul {u z : K} (h1 : u ∈ SP K 𝔭) (h2 : u⁻¹ ∈ SP K 𝔭) (hz : z ≠ 0) :
    NU 𝔭 (star z * u * z) := by
  have hs : star z⁻¹ = (star z)⁻¹ := by
    first | exact star_inv₀ z | exact star_inv' z | simp
  have hsz : star z ≠ 0 := by
    first | exact star_ne_zero.2 hz | simpa using hz
  have e : star z * u * z * (z⁻¹ * star z⁻¹) = u := by
    rw [hs]
    calc star z * u * z * (z⁻¹ * (star z)⁻¹) = u * (z * z⁻¹) * (star z * (star z)⁻¹) := by ring
      _ = u := by rw [mul_inv_cancel₀ hz, mul_inv_cancel₀ hsz, mul_one, mul_one]
  refine ⟨z⁻¹, inv_ne_zero hz, ?_, ?_⟩
  · rw [e]
    exact h1
  · rw [e]
    exact h2

theorem NU.prod {ι : Type} (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, NU 𝔭 (f i)) :
    NU 𝔭 (∏ i ∈ s, f i) :=
  Finset.prod_induction f (NU 𝔭) (fun _ _ ha hb => NU.mul ha hb)
    (NU.of_unit (SP K 𝔭).one_mem (by rw [inv_one]; exact (SP K 𝔭).one_mem)) hf

theorem NU.pair {A C : K} (hA : A ≠ 0) (hAs : star A = A) (h1 : C * A⁻¹ ∈ SP K 𝔭)
    (h2 : A * C⁻¹ ∈ SP K 𝔭) : NU 𝔭 (A * C) := by
  have hs : star A⁻¹ = (star A)⁻¹ := by
    first | exact star_inv₀ A | exact star_inv' A | simp
  have e : A * C * (A⁻¹ * star A⁻¹) = C * A⁻¹ := by
    rw [hs, hAs]
    calc A * C * (A⁻¹ * A⁻¹) = C * A⁻¹ * (A * A⁻¹) := by ring
      _ = C * A⁻¹ := by rw [mul_inv_cancel₀ hA, mul_one]
  refine ⟨A⁻¹, inv_ne_zero hA, ?_, ?_⟩
  · rw [e]
    exact h1
  · rw [e, mul_inv, inv_inv, mul_comm]
    exact h2

section Vec

variable {V : Type} [AddCommGroup V] [Module K V]

theorem linInd_orth {ι : Type} {h : V →ₗ⋆[K] V →ₗ[K] K} (g : ι → V)
    (ho : ∀ s t, s ≠ t → h (g s) (g t) = 0) (hn : ∀ s, h (g s) (g s) ≠ 0) : LinearIndependent K g := by
  rw [linearIndependent_iff']
  intro s c hs i hi
  have key := congrArg (h (g i)) hs
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero, Finset.sum_eq_single i] at key
  · rw [map_smul, smul_eq_mul] at key
    exact (mul_eq_zero.1 key).resolve_right (hn i)
  · intro j _ hji
    rw [map_smul, ho i j (Ne.symm hji), smul_zero]
  · intro hi'
    exact absurd hi hi'

end Vec

end Formalism.L2.SG.Pf.NormUnitsOrthogonality
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXKS
section
noncomputable section

open MeasureTheory Matrix NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf
  Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.L2.SG.RealObj.InfCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Inv

variable {r k : ℕ}

def RcInv (y : LsNc5.CIdx r k → ℝ) : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) :=
  (fun c => (⟨y (eIdx (Sum.inl (c, false))), y (eIdx (Sum.inl (c, true)))⟩ : ℂ), fun a => y (eIdx (Sum.inr a)))

theorem Rc_RcInv (y : LsNc5.CIdx r k → ℝ) : Rc (RcInv y) = y := by
  funext i
  obtain ⟨j, rfl⟩ := eIdx.surjective i
  rcases j with ⟨c, b⟩ | a
  · cases b <;> simp [Rc, RcInv, LsNc5.reim]
  · simp [Rc, RcInv]

theorem measurable_RcInv : Measurable (RcInv (r := r) (k := k)) := by
  apply Continuous.measurable
  unfold RcInv
  have h : Continuous fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ) := Complex.equivRealProdCLM.symm.continuous
  exact Continuous.prodMk (continuous_pi fun c => h.comp'
      (f := fun a : LsNc5.CIdx r k → ℝ => (a (eIdx (Sum.inl (c, false))), a (eIdx (Sum.inl (c, true)))))
      ((continuous_apply _).prodMk (continuous_apply _)))
    (continuous_pi fun a => continuous_apply _)

def dYInv (T : ℝ) (y : LsNc5.CIdx r k → ℝ) : LsNc5.CIdx r k → ℝ := fun i => y i / dY T i

theorem dY_pos {T : ℝ} (hT : 0 < T) (i : LsNc5.CIdx r k) : 0 < dY T i := by
  rcases i with (a | a) | a <;> simp [dY, hT]

theorem LyM_dYInv {T : ℝ} (hT : 0 < T) (y : LsNc5.CIdx r k → ℝ) : LyM T (dYInv T y) = y := by
  funext i
  simp only [LyM, Matrix.toLin'_apply, Matrix.mulVec_diagonal, dYInv]
  field_simp [(dY_pos hT i).ne']

theorem measurable_dYInv (T : ℝ) : Measurable (dYInv (r := r) (k := k) T) := by
  unfold dYInv
  exact Measurable.of_eval fun i => (measurable_pi_apply i).div_const _

end Inv

theorem surjLoc {n r k : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ)
    (w : Fin k → Fin n → ℂ) (z : Fin n → ℂ) {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (w a) = 0) (hfw : ∀ c a, hJ ε (f c) (w a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (w a) = 0) :
    ∃ σL : (LsNc5.CIdx r k → ℝ) → Formalism.REAL.UJ ε, Measurable σL ∧
      ∀ y, σL y ∈ NLoc ε e z ∧ kapL ε e f w z (σL y) = y := by
  subst hn
  have hFJ := isFrameJ_of hT hee hff hef hww hew hfw hez hfz hzz hzw
  have emb := embQ hFJ
  have hQz : Qm e f w (z0v T z) *ᵥ zBv k r T = z := Qm_zB hT z
  set Ψ := cM (ε := ε) (Qi ε e f w (z0v T z)) (Qm e f w (z0v T z)) with hΨ
  let ψ0 : (LsNc5.CIdx r k → ℝ) → (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) := fun y => RcInv (dYInv T y)
  have hψ0 : Measurable ψ0 := measurable_RcInv.comp (measurable_dYInv T)
  let Φ : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) → Mt k r := fun t => WlocSk.NB.phi0 t.1 t.2
  have hΦc : Continuous Φ := WlocSk.NB.continuous_nilpotent_chart
  have hΦN : ∀ t : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ), WlocSk.NB.phi0 t.1 t.2 ∈ Nset k r := fun t =>
    WlocSk.NB.test_vector_mem_schwartz_bruhat t.1 t.2
  have hrange : ∀ t, Φ t ∈ Set.range Ψ := fun t => by
    refine ⟨toUJ _ (conjQ_UJ hFJ (hΦN t).1), ?_⟩
    show (Qi ε e f w (z0v T z) * uMat (toUJ _ (conjQ_UJ hFJ (hΦN t).1)) * Qm e f w (z0v T z) :
      Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = WlocSk.NB.phi0 t.1 t.2
    rw [uMat_toUJ, Qi_Qm_conj hFJ]
  let σL : (LsNc5.CIdx r k → ℝ) → Formalism.REAL.UJ ε := fun y => emb.equivRange.symm ⟨Φ (ψ0 y), hrange (ψ0 y)⟩
  have hσΨ : ∀ y, Ψ (σL y) = Φ (ψ0 y) := fun y => by
    have h1 := emb.equivRange.apply_symm_apply ⟨Φ (ψ0 y), hrange (ψ0 y)⟩
    rw [MeasurableEmbedding.equivRange_apply] at h1
    exact congrArg Subtype.val h1
  have hz0 : ∃ t : ℂ, z0v T z = t • (Qm e f w (z0v T z) *ᵥ zBv k r T) :=
    ⟨(((Real.sqrt T)⁻¹ : ℝ) : ℂ), by rw [hQz]; rfl⟩
  refine ⟨σL, ?_, fun y => ⟨?_, ?_⟩⟩
  · exact emb.equivRange.symm.measurable.comp
      ((hΦc.measurable.comp hψ0).subtype_mk)
  · have hN : Qi ε e f w (z0v T z) * uMat (σL y) * Qm e f w (z0v T z) ∈ Nset k r := by
      have : (Qi ε e f w (z0v T z) * uMat (σL y) * Qm e f w (z0v T z) :
          Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = WlocSk.NB.phi0 (ψ0 y).1 (ψ0 y).2 := hσΨ y
      rw [this]; exact hΦN _
    have h1 := inN_of_conj hFJ (inWb_zB T) hN
    rw [hQz] at h1
    exact h1
  · have hN : Qi ε e f w (z0v T z) * uMat (σL y) * Qm e f w (z0v T z) ∈ Nset k r := by
      have : (Qi ε e f w (z0v T z) * uMat (σL y) * Qm e f w (z0v T z) :
          Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = WlocSk.NB.phi0 (ψ0 y).1 (ψ0 y).2 := hσΨ y
      rw [this]; exact hΦN _
    rw [kapL_eq hFJ hT (σL y) hN]
    show Kc T (Ψ (σL y)) = y
    rw [hσΨ y]
    funext i
    rw [chart_kappa_coordinates T (ψ0 y) i, ← LyM_apply]
    show LyM T (Rc (RcInv (dYInv T y))) i = y i
    rw [Rc_RcInv, LyM_dYInv hT]

theorem kapSurj_holds : KapSurj := by
  intro D X u
  have hloc := fun v : InfinitePlace X.B.I.F => surjLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v)
    (ProductExactness.zV X u v) (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v) (fX_ww X u v) (fX_ew X u v)
    (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v)
  choose σL hσm hσ using hloc
  refine ⟨fun t v => σL v (fun i => Φc t (v, i)), ?_, fun t => ⟨fun v => (hσ v _).1, ?_⟩⟩
  · exact Measurable.of_eval fun v => (hσm v).comp
      (Measurable.of_eval fun i => (measurable_pi_apply (v, i)).comp measurable_Φc)
  · have hk : Φc (blk X u (fun v => σL v (fun i => Φc t (v, i)))) = Φc t := by
      rw [← kap_eq_Φc]
      funext p
      have := (hσ p.1 (fun i => Φc t (p.1, i))).2
      have h2 := congrFun (kapV_eq X u p.1 (fun v => σL v (fun i => Φc t (v, i)))) p.2
      exact h2.trans (congrFun this p.2)
    have := congrArg Ψc hk
    rwa [Ψc_Φc, Ψc_Φc] at this

end Formalism.L2.SG.Pf.NcReal.JX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RefNBoxOf
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem refNBox_of (hF : FrameRow) : RefNBox := by
  intro D X u w
  choose L hL hdet using fun v => hF X u w v
  have hTu := Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos (D := D) u
  have hTw := Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos (D := D) w
  have hdet0 : ∀ v, LinearMap.det (L v) ≠ 0 := fun v h0 => by
    have h1 := hdet v
    rw [h0, abs_zero] at h1
    exact (pow_pos (div_pos hTw hTu) _).ne' h1.symm
  have key : ∀ (s : X.B.I.Ginf) v i, LsNc5.kapV X w v s i =
      L v (kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) (s v)) i := fun s v i => by
    have h1 := congrFun (hL v s) i
    rw [kapV_eq (X := X) u v s] at h1
    exact h1
  have hbox : LsNc5.boxN X w = X.NinfU w ∩ Set.univ.pi (fun v =>
      (fun g => L v (kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) g)) ⁻¹' Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1)) := by
    rw [LsNc5.boxN_eq]
    congr 1
    ext s
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h v i
      rw [← key s v i]
      exact h (v, i)
    · rintro h ⟨v, i⟩
      show LsNc5.kapV X w v s i ∈ _
      rw [key s v i]
      exact h v i
  have hv : ∀ v, refNX X u v ((fun g => L v (kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) g)) ⁻¹'
      Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1)) =
      ENNReal.ofReal ((2 : ℝ) ^ (D.R.rS ^ 2 + D.R.rS * D.R.k) * (Tw w ^ D.R.rS)⁻¹) := fun v => by
    obtain ⟨hae, hmap⟩ := refN_map_kapL (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v)
      (ProductExactness.zV X u v) hTu (fX_ee (X := X) (v := v)) (fX_ff (X := X) (v := v))
      (fX_ef (X := X) (v := v)) (fX_ww (X := X) (u := u) (v := v)) (fX_ew (X := X) (u := u) (v := v))
      (fX_fw (X := X) (u := u) (v := v)) (fX_ez (X := X) (u := u) (v := v))
      (fX_fz (X := X) (u := u) (v := v)) (frame_real_z_z_eq_neg (X := X) (u := u) (v := v))
      (fX_zw (X := X) (u := u) (v := v))
    have hmeas : MeasurableSet ((L v) ⁻¹' Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1)) :=
      (L v).continuous_of_finiteDimensional.measurable (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
    have hpre : (fun g => L v (kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) g)) ⁻¹' Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1) =
        kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) ⁻¹' ((L v) ⁻¹' Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1)) := rfl
    rw [hpre, show refNX X u v = refNg (nX X) _ _ _ _ _ from rfl, ← Measure.map_apply_of_aemeasurable hae hmeas, hmap,
      Measure.smul_apply, smul_eq_mul, Measure.addHaar_preimage_linearMap _ (hdet0 v), Real.volume_pi_Ico]
    simp only [sub_zero, ENNReal.ofReal_one, Finset.prod_const_one, mul_one]
    rw [abs_inv, hdet v, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [div_pow]
    field_simp
  haveI : ∀ v, SigmaFinite (refNX X u v) := fun v =>
    (refNg_isHaarLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v)
      (ProductExactness.zV X u v) hTu (fX_ee (X := X) (v := v)) (fX_ff (X := X) (v := v))
      (fX_ef (X := X) (v := v)) (fX_ww (X := X) (u := u) (v := v)) (fX_ew (X := X) (u := u) (v := v))
      (fX_fw (X := X) (u := u) (v := v)) (fX_ez (X := X) (u := u) (v := v))
      (fX_fz (X := X) (u := u) (v := v)) (frame_real_z_z_eq_neg (X := X) (u := u) (v := v))
      (fX_zw (X := X) (u := u) (v := v)) (fX_ez (X := X) (u := u) (v := v))).1
  rw [hbox, Set.inter_comm, measure_inter_conull (refNX_haar X u w).2.2.1, Measure.pi_pi]
  simp only [hv, Finset.prod_const, Finset.card_univ]
  rw [← ENNReal.ofReal_pow (by positivity)]
  congr 1
  rw [inv_pow, ← inv_pow]
  ring

end Formalism.L2.SG.Pf.NcReal.JX
end
end

