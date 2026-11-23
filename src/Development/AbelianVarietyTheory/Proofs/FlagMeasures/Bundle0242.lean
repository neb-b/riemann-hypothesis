module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariant
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.SgInfDD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mat k r → (H →L[ℂ] H)}

theorem gg_mul {a b : Mat k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) : a * b ∈ GG k r :=
  Formalism.MainNotions.LowestKTypeMultiplicity.UH_mul ha hb

theorem gg_one : (1 : Mat k r) ∈ GG k r := Formalism.MainNotions.LowestKTypeMultiplicity.UH_one k r

theorem hasDeriv_dsig (hσ : IsURepOn (GG k r) σ) {v : H} (hv : IsSmoothVec (k := k) (r := r) σ v)
    {Y : Mat k r} (hY : InLieHpk k r Y) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Y)) v) (dsig σ Y v) 0 :=
  Formalism.MainNotions.LowestKTypeMultiplicity.dsigW_hasDeriv hσ hv [] (by simp) hY

theorem smooth_dsig (hσ : IsURepOn (GG k r) σ) {v : H} (hv : IsSmoothVec (k := k) (r := r) σ v)
    {Y : Mat k r} (hY : InLieHpk k r Y) : IsSmoothVec (k := k) (r := r) σ (dsig σ Y v) := by
  have h2 := Formalism.MainNotions.LowestKTypeMultiplicity.psiD_smooth hσ hv [Y] (by simpa using hY)
  intro g₀ hg₀
  obtain ⟨U, F, hU, hp, hF, hE⟩ := h2 ((1 : Mat k r), g₀) (gg_one) hg₀
  have hc : ContDiff ℝ ∞ (fun g : Mat k r => (((1 : Mat k r), g) : Mat k r × Mat k r)) :=
    contDiff_const.prodMk contDiff_id
  refine ⟨(fun g : Mat k r => (((1 : Mat k r), g) : Mat k r × Mat k r)) ⁻¹' U, fun g => F ((1 : Mat k r), g),
    hU.preimage hc.continuous, hp, hF.comp hc.contDiffOn (fun x hx => hx), ?_⟩
  intro g hgU hgH
  have := hE ((1 : Mat k r), g) hgU gg_one hgH
  simp only [hσ.1.1, ContinuousLinearMap.one_apply] at this
  exact this

theorem lie_conj {g Y : Mat k r} (hg : g ∈ GG k r) (hY : InLieHpk k r Y) :
    InLieHpk k r (g * Y * g⁻¹) := by
  have hd : IsUnit g.det := Formalism.MainNotions.LowestKTypeMultiplicity.UH_det hg
  have hM : g⁻¹ ∈ GG k r := Formalism.MainNotions.LowestKTypeMultiplicity.UH_inv hg
  have hgM : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hd
  have hMg : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hd
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hM' : (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r := hM
  have e1 : gᴴ * Hpk k r = Hpk k r * g⁻¹ := by
    calc gᴴ * Hpk k r = gᴴ * Hpk k r * (g * g⁻¹) := by rw [hgM, Matrix.mul_one]
      _ = (gᴴ * Hpk k r * g) * g⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Hpk k r * g⁻¹ := by rw [hg']
  have e2 : Hpk k r * g = (g⁻¹)ᴴ * Hpk k r := by
    calc Hpk k r * g = ((g⁻¹)ᴴ * Hpk k r * g⁻¹) * g := by rw [hM']
      _ = (g⁻¹)ᴴ * Hpk k r * (g⁻¹ * g) := by simp only [Matrix.mul_assoc]
      _ = (g⁻¹)ᴴ * Hpk k r := by rw [hMg, Matrix.mul_one]
  have hY' : Yᴴ * Hpk k r + Hpk k r * Y = 0 := hY
  show (g * Y * g⁻¹)ᴴ * Hpk k r + Hpk k r * (g * Y * g⁻¹) = 0
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc (g⁻¹)ᴴ * (Yᴴ * gᴴ) * Hpk k r + Hpk k r * (g * Y * g⁻¹)
      = (g⁻¹)ᴴ * Yᴴ * (gᴴ * Hpk k r) + (Hpk k r * g) * Y * g⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (g⁻¹)ᴴ * Yᴴ * (Hpk k r * g⁻¹) + ((g⁻¹)ᴴ * Hpk k r) * Y * g⁻¹ := by rw [e1, e2]
    _ = (g⁻¹)ᴴ * (Yᴴ * Hpk k r + Hpk k r * Y) * g⁻¹ := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hY', Matrix.mul_zero, Matrix.zero_mul]

theorem dsig_conj (hσ : IsURepOn (GG k r) σ) {v : H} (hv : IsSmoothVec (k := k) (r := r) σ v)
    {Y : Mat k r} (hY : InLieHpk k r Y) {g : Mat k r} (hg : g ∈ GG k r) :
    σ g (dsig σ Y v) = dsig σ (g * Y * g⁻¹) (σ g v) := by
  have hd : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 (Formalism.MainNotions.LowestKTypeMultiplicity.UH_det hg)
  have hM : g⁻¹ ∈ GG k r := Formalism.MainNotions.LowestKTypeMultiplicity.UH_inv hg
  have hMg : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g ((Matrix.isUnit_iff_isUnit_det g).1 hd)
  have h1 := hasDeriv_dsig hσ hv hY
  have h2 := ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have e : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • (g * Y * g⁻¹))) (σ g v)) =
      (⇑((σ g).restrictScalars ℝ) ∘ fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Y)) v) := by
    funext t
    have hx := Formalism.MainNotions.LowestKTypeMultiplicity.exp_mem_UH hY t
    have hs : (t : ℂ) • (g * Y * g⁻¹) = g * ((t : ℂ) • Y) * g⁻¹ := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [hs, Matrix.exp_conj _ _ hd]
    simp only [Function.comp, ContinuousLinearMap.coe_restrictScalars']
    have hc : g * NormedSpace.exp ((t : ℂ) • Y) ∈ GG k r := gg_mul hg hx
    rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ (gg_mul hc hM) g hg,
      ← ContinuousLinearMap.comp_apply, ← hσ.1.2 g hg _ hx]
    congr 2
    rw [Matrix.mul_assoc, hMg, Matrix.mul_one]
  show _ = deriv _ 0
  rw [e, h2.deriv]
  rfl

theorem smooth_dsigW (hσ : IsURepOn (GG k r) σ) {v : H} (hv : IsSmoothVec (k := k) (r := r) σ v) :
    ∀ Ys : List (Mat k r), (∀ Y ∈ Ys, InLieHpk k r Y) → IsSmoothVec (k := k) (r := r) σ (dsigW σ Ys v) := by
  intro Ys
  induction Ys with
  | nil => intro _; exact hv
  | cons Y Ys ih =>
    intro h
    exact smooth_dsig hσ (ih fun X hX => h X (List.mem_cons_of_mem _ hX)) (h Y List.mem_cons_self)

theorem dsigW_conj (hσ : IsURepOn (GG k r) σ) {v : H} (hv : IsSmoothVec (k := k) (r := r) σ v)
    {g : Mat k r} (hg : g ∈ GG k r) :
    ∀ Ys : List (Mat k r), (∀ Y ∈ Ys, InLieHpk k r Y) →
      σ g (dsigW σ Ys v) = dsigW σ (Ys.map fun Y => g * Y * g⁻¹) (σ g v) := by
  intro Ys
  induction Ys with
  | nil => intro _; rfl
  | cons Y Ys ih =>
    intro h
    have h' : ∀ X ∈ Ys, InLieHpk k r X := fun X hX => h X (List.mem_cons_of_mem _ hX)
    show σ g (dsig σ Y (dsigW σ Ys v)) = dsig σ (g * Y * g⁻¹) (dsigW σ (Ys.map fun Y => g * Y * g⁻¹) (σ g v))
    rw [dsig_conj hσ (smooth_dsigW hσ hv Ys h') (h Y List.mem_cons_self) hg, ih h']

theorem dsig_zero (Y : Mat k r) : dsig σ Y (0 : H) = 0 := by
  simp [dsig]

theorem dsig_add (hσ : IsURepOn (GG k r) σ) {a b : H} (ha : IsSmoothVec (k := k) (r := r) σ a)
    (hb : IsSmoothVec (k := k) (r := r) σ b) {Y : Mat k r} (hY : InLieHpk k r Y) :
    dsig σ Y (a + b) = dsig σ Y a + dsig σ Y b := by
  have h := (hasDeriv_dsig hσ ha hY).add (hasDeriv_dsig hσ hb hY)
  show deriv _ 0 = _
  simp only [map_add (f := _)]
  exact h.deriv

theorem dsig_smul (hσ : IsURepOn (GG k r) σ) {a : H} (ha : IsSmoothVec (k := k) (r := r) σ a)
    (c : ℂ) {Y : Mat k r} (hY : InLieHpk k r Y) :
    dsig σ Y (c • a) = c • dsig σ Y a := by
  have h := (hasDeriv_dsig hσ ha hY).const_smul c
  show deriv _ 0 = _
  simp only [map_smul]
  exact h.deriv

theorem DD_stable (hσ : IsURepOn (GG k r) σ) (w : H) {g : Mat k r} (hg : g ∈ GG k r) :
    DD σ w ≤ (DD σ w).comap (σ g : H →ₗ[ℂ] H) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨h, hh, rfl⟩
  show σ g (σ h w) ∈ DD σ w
  rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 g hg h hh]
  exact mem_DD σ w (gg_mul hg hh)

theorem mem_DD_self (hσ : IsURepOn (GG k r) σ) (w : H) : w ∈ DD σ w := by
  have := mem_DD σ w (gg_one (k := k) (r := r))
  rwa [hσ.1.1, ContinuousLinearMap.one_apply] at this

theorem DD_dense (hσ : IsURepOn (GG k r) σ) (hirr : IsIrredOn (GG k r) σ) {w : H} (hw : w ≠ 0) :
    Dense (DD σ w : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  have hst : ∀ g ∈ GG k r, ∀ v ∈ (DD σ w).topologicalClosure, σ g v ∈ (DD σ w).topologicalClosure := by
    intro g hg v hv
    have hle : (DD σ w).topologicalClosure ≤ ((DD σ w).topologicalClosure).comap (σ g : H →ₗ[ℂ] H) := by
      refine Submodule.topologicalClosure_minimal _ ?_ ?_
      · exact (DD_stable hσ w hg).trans (Submodule.comap_mono (DD σ w).le_topologicalClosure)
      · exact (DD σ w).isClosed_topologicalClosure.preimage (σ g).continuous
    exact hle hv
  rcases hirr (DD σ w).topologicalClosure (DD σ w).isClosed_topologicalClosure hst with h | h
  · exfalso
    have h1 : w ∈ (DD σ w).topologicalClosure := (DD σ w).le_topologicalClosure (mem_DD_self hσ w)
    rw [h, Submodule.mem_bot] at h1
    exact hw h1
  · exact h

theorem DD_le_Vinf (w : H) : DD σ w ≤ Vinf σ w := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, hg, rfl⟩
  exact Submodule.subset_span ⟨[], g, by simp, hg, rfl⟩

theorem Vinf_smooth (hσ : IsURepOn (GG k r) σ) {w : H} (hw : IsSmoothVec (k := k) (r := r) σ w) :
    ∀ v ∈ Vinf σ w, IsSmoothVec (k := k) (r := r) σ v := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Ys, g, hYs, hg, rfl⟩ := hx
    exact smooth_dsigW hσ (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hw hg) Ys hYs
  | zero => exact Formalism.MainNotions.LowestKTypeMultiplicity.smooth_zero
  | add x y _ _ hx hy => exact Formalism.MainNotions.LowestKTypeMultiplicity.smooth_add hx hy
  | smul a x _ hx => exact Formalism.MainNotions.LowestKTypeMultiplicity.smooth_smul a hx

theorem Vinf_stable (hσ : IsURepOn (GG k r) σ) {w : H} (hw : IsSmoothVec (k := k) (r := r) σ w)
    {g : Mat k r} (hg : g ∈ GG k r) : Vinf σ w ≤ (Vinf σ w).comap (σ g : H →ₗ[ℂ] H) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨Ys, h, hYs, hh, rfl⟩
  show σ g (dsigW σ Ys (σ h w)) ∈ Vinf σ w
  rw [dsigW_conj hσ (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hw hh) hg Ys hYs,
    ← ContinuousLinearMap.comp_apply, ← hσ.1.2 g hg h hh]
  refine Submodule.subset_span ⟨Ys.map fun Y => g * Y * g⁻¹, g * h, ?_, gg_mul hg hh, rfl⟩
  intro Y hY
  obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hY
  exact lie_conj hg (hYs X hX)

theorem Vinf_dsig (hσ : IsURepOn (GG k r) σ) {w : H} (hw : IsSmoothVec (k := k) (r := r) σ w)
    {Y : Mat k r} (hY : InLieHpk k r Y) : ∀ v ∈ Vinf σ w, dsig σ Y v ∈ Vinf σ w := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Ys, g, hYs, hg, rfl⟩ := hx
    refine Submodule.subset_span ⟨Y :: Ys, g, ?_, hg, rfl⟩
    intro X hX
    rcases List.mem_cons.1 hX with rfl | hX
    · exact hY
    · exact hYs X hX
  | zero => rw [dsig_zero]; exact (Vinf σ w).zero_mem
  | add x y hx hy ihx ihy =>
    rw [dsig_add hσ (Vinf_smooth hσ hw x hx) (Vinf_smooth hσ hw y hy) hY]
    exact (Vinf σ w).add_mem ihx ihy
  | smul a x hx ihx =>
    rw [dsig_smul hσ (Vinf_smooth hσ hw x hx) a hY]
    exact (Vinf σ w).smul_mem a ihx

theorem DD_stable_dense : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (w : H), IsURepOn (GG k r) σ →
    (∀ g ∈ GG k r, ∀ v ∈ DD σ w, σ g v ∈ DD σ w) ∧
    (IsIrredOn (GG k r) σ → w ≠ 0 → Dense (DD σ w : Set H)) ∧ DD σ w ≤ Vinf σ w ∧
    (∀ v, IsSmoothVec σ v → (∀ g ∈ GG k r, IsSmoothVec σ (σ g v)) ∧
      ∀ Y, InLieHpk k r Y → IsSmoothVec σ (dsig σ Y v) ∧
        ∀ g ∈ GG k r, InLieHpk k r (g * Y * g⁻¹) ∧ σ g (dsig σ Y v) = dsig σ (g * Y * g⁻¹) (σ g v)) ∧
    (IsSmoothVec σ w → (∀ v ∈ Vinf σ w, IsSmoothVec σ v) ∧ (∀ g ∈ GG k r, ∀ v ∈ Vinf σ w, σ g v ∈ Vinf σ w) ∧
      ∀ Y, InLieHpk k r Y → ∀ v ∈ Vinf σ w, dsig σ Y v ∈ Vinf σ w) := by
  intro k r H _ _ _ σ w hσ
  refine ⟨fun g hg v hv => DD_stable hσ w hg hv, fun hirr hw => DD_dense hσ hirr hw, DD_le_Vinf w,
    fun v hv => ⟨fun g hg => Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hv hg, fun Y hY =>
      ⟨smooth_dsig hσ hv hY, fun g hg => ⟨lie_conj hg hY, dsig_conj hσ hv hY hg⟩⟩⟩,
    fun hw => ⟨Vinf_smooth hσ hw, fun g hg v hv => Vinf_stable hσ hw hg hv, fun Y hY => Vinf_dsig hσ hw hY⟩⟩

end GlobalTheory.SgInfDD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalBlockCovolumesProd
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN.Covol

theorem sum_UTr_fst (r : ℕ) (u : Fin r → ℝ) :
    ∑ p : UTr r, u p.1.1 = ∑ a : Fin r, ((r - 1 - (a : ℕ) : ℕ) : ℝ) * u a := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun x : Fin r × Fin r => x.1 < x.2)) (by simp)
    (fun x => u x.1)]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_filter]
  dsimp only
  rw [Finset.sum_const, nsmul_eq_mul, ← Fin.card_Ioi]
  congr 3
  ext b; simp

theorem sum_UTr_snd (r : ℕ) (v : Fin r → ℝ) :
    ∑ p : UTr r, v p.1.2 = ∑ b : Fin r, ((b : ℕ) : ℝ) * v b := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun x : Fin r × Fin r => x.1 < x.2)) (by simp)
    (fun x => v x.2)]
  rw [Finset.sum_filter, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_filter]
  dsimp only
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [← Fin.card_Iio b]; congr 1; ext a; simp

theorem sum_UTr (r : ℕ) (u v : Fin r → ℝ) :
    ∑ p : UTr r, (u p.1.1 + v p.1.2) =
      ∑ a : Fin r, (((r - 1 - (a : ℕ) : ℕ) : ℝ) * u a + ((a : ℕ) : ℝ) * v a) := by
  rw [Finset.sum_add_distrib, sum_UTr_fst, sum_UTr_snd, ← Finset.sum_add_distrib]

theorem sum_fin_quad (r : ℕ) (c₀ c₁ c₂ : ℝ) :
    ∑ a : Fin r, (c₀ + c₁ * ((a : ℕ) : ℝ) + c₂ * ((a : ℕ) : ℝ) ^ 2) =
      c₀ * r + c₁ * (r * (r - 1) / 2) + c₂ * ((r - 1) * r * (2 * r - 1) / 6) := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => c₀ + c₁ * (i : ℝ) + c₂ * (i : ℝ) ^ 2) r]
  induction r with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

end GlobalTheory.SnMass.VolN.Covol

namespace GlobalTheory.SnMass.VolN


open Covol in
theorem covol_blocks_prod : ∀ (d : ℝ) (f k r : ℕ) (s : Fin r → ℝ), 0 < d → (∀ a, 0 < s a) → (2 : ℝ) ^ (f * (r * (r - 1) + r * (k + 1))) * ((∏ p : UTr r, (2⁻¹ : ℝ) ^ f * d ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) + 2 * ((r - p.1.2.val : ℕ) : ℝ)) * (s p.1.1 / s p.1.2) ^ (2 * f)) * (∏ a : Fin r, ((2⁻¹ : ℝ) ^ f * d ^ (1 - 2 * ((r - a.val : ℕ) : ℝ)) * s a ^ (2 * f)) ^ (k + 1)) * (∏ p : UTr r, (2⁻¹ : ℝ) ^ f * d ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) - 2 * ((r - p.1.2.val : ℕ) : ℝ)) * (s p.1.1 * s p.1.2) ^ (2 * f)) * ∏ a : Fin r, d ^ (1 / 2 - 2 * ((r - a.val : ℕ) : ℝ)) * (s a ^ 2) ^ f) = d ^ (-(((k : ℝ) + 1) * (r : ℝ) ^ 2) - 4 * ((r : ℝ) ^ 3 - r) / 3 - 3 * (r : ℝ) / 2) * (∏ a : Fin r, s a ^ (4 * (r - (a : ℕ)) + 2 * k)) ^ f := by
  intro d f k r s hd hs
  obtain ⟨δ, rfl⟩ : ∃ δ, d = Real.exp δ := ⟨Real.log d, (Real.exp_log hd).symm⟩
  obtain ⟨σ, rfl⟩ : ∃ σ : Fin r → ℝ, s = fun a => Real.exp (σ a) :=
    ⟨fun a => Real.log (s a), funext fun a => (Real.exp_log (hs a)).symm⟩
  beta_reduce
  have h2i : (2⁻¹ : ℝ) = Real.exp (-Real.log 2) := by rw [Real.exp_neg, Real.exp_log two_pos]
  have e1 : ∀ p : UTr r, (2⁻¹ : ℝ) ^ f * Real.exp δ ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) +
      2 * ((r - p.1.2.val : ℕ) : ℝ)) * (Real.exp (σ p.1.1) / Real.exp (σ p.1.2)) ^ (2 * f) =
      Real.exp ((-(f : ℝ) * Real.log 2 + δ * (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ)) + 2 * f * σ p.1.1) +
        (2 * δ * ((r - p.1.2.val : ℕ) : ℝ) - 2 * f * σ p.1.2)) := by
    intro p
    rw [h2i]
    simp only [← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_sub, ← Real.exp_add]
    congr 1; push_cast; ring
  have e3 : ∀ p : UTr r, (2⁻¹ : ℝ) ^ f * Real.exp δ ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) -
      2 * ((r - p.1.2.val : ℕ) : ℝ)) * (Real.exp (σ p.1.1) * Real.exp (σ p.1.2)) ^ (2 * f) =
      Real.exp ((-(f : ℝ) * Real.log 2 + δ * (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ)) + 2 * f * σ p.1.1) +
        (-(2 * δ * ((r - p.1.2.val : ℕ) : ℝ)) + 2 * f * σ p.1.2)) := by
    intro p
    rw [h2i]
    simp only [← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1; push_cast; ring
  have e2 : ∀ a : Fin r, ((2⁻¹ : ℝ) ^ f * Real.exp δ ^ (1 - 2 * ((r - a.val : ℕ) : ℝ)) *
      Real.exp (σ a) ^ (2 * f)) ^ (k + 1) =
      Real.exp (((k : ℝ) + 1) * (-(f : ℝ) * Real.log 2 + δ * (1 - 2 * ((r - a.val : ℕ) : ℝ)) + 2 * f * σ a)) := by
    intro a
    rw [h2i]
    simp only [← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1; push_cast; ring
  have e4 : ∀ a : Fin r, Real.exp δ ^ (1 / 2 - 2 * ((r - a.val : ℕ) : ℝ)) * (Real.exp (σ a) ^ 2) ^ f =
      Real.exp (δ * (1 / 2 - 2 * ((r - a.val : ℕ) : ℝ)) + 2 * f * σ a) := by
    intro a
    simp only [← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1; push_cast; ring
  have e5 : ∀ a : Fin r, Real.exp (σ a) ^ (4 * (r - (a : ℕ)) + 2 * k) =
      Real.exp (((4 * (r - (a : ℕ)) + 2 * k : ℕ) : ℝ) * σ a) := fun a => (Real.exp_nat_mul _ _).symm
  rw [Finset.prod_congr rfl (fun p _ => e1 p), Finset.prod_congr rfl (fun a _ => e2 a),
    Finset.prod_congr rfl (fun p _ => e3 p), Finset.prod_congr rfl (fun a _ => e4 a),
    Finset.prod_congr rfl (fun a _ => e5 a)]
  have hu1 := sum_UTr r
    (fun a => -(f : ℝ) * Real.log 2 + δ * (1 - 2 * ((r - a.val : ℕ) : ℝ)) + 2 * f * σ a)
    (fun b => 2 * δ * ((r - b.val : ℕ) : ℝ) - 2 * f * σ b)
  have hu3 := sum_UTr r
    (fun a => -(f : ℝ) * Real.log 2 + δ * (1 - 2 * ((r - a.val : ℕ) : ℝ)) + 2 * f * σ a)
    (fun b => -(2 * δ * ((r - b.val : ℕ) : ℝ)) + 2 * f * σ b)
  beta_reduce at hu1 hu3
  rw [← Real.exp_sum, ← Real.exp_sum, ← Real.exp_sum, ← Real.exp_sum, ← Real.exp_sum, hu1, hu3]
  rw [show (2 : ℝ) ^ (f * (r * (r - 1) + r * (k + 1))) =
      Real.exp (((f * (r * (r - 1) + r * (k + 1)) : ℕ) : ℝ) * Real.log 2) by
    rw [Real.exp_nat_mul, Real.exp_log two_pos]]
  simp only [← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_add]
  rw [Real.exp_eq_exp]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← sub_eq_zero, show ∀ x y z w : ℝ, x + y - (z + w) = (y - w) + (x - z) from fun _ _ _ _ => by ring,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (g := fun a : Fin r =>
      (δ * (2 * ((r : ℝ) - 1) * (1 - 2 * r) + ((k : ℝ) + 1) * (1 - 2 * r) + 1 / 2 - 2 * r) -
        Real.log 2 * f * (2 * r + k - 1)) +
      (δ * (8 * r + 2 * k - 2) + 2 * f * Real.log 2) * ((a : ℕ) : ℝ) + (-4 * δ) * ((a : ℕ) : ℝ) ^ 2) ?hc,
    sum_fin_quad]
  · have hN : ((f * (r * (r - 1) + r * (k + 1)) : ℕ) : ℝ) = f * (r * ((r : ℝ) - 1) + r * (k + 1)) := by
      rcases r with _ | n
      · simp
      · push_cast [Nat.add_sub_cancel]; ring
    rw [hN]; ring
  · intro a _
    have ha := a.isLt
    have h1 : ((r - (a : ℕ) : ℕ) : ℝ) = r - (a : ℕ) := by rw [Nat.cast_sub ha.le]
    have h2 : ((r - 1 - (a : ℕ) : ℕ) : ℝ) = r - 1 - (a : ℕ) := by
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
    have h3 : ((4 * (r - (a : ℕ)) + 2 * k : ℕ) : ℝ) = 4 * ((r : ℝ) - (a : ℕ)) + 2 * k := by
      push_cast [Nat.cast_sub ha.le]; ring
    rw [h3, h2, h1]; ring

end GlobalTheory.SnMass.VolN
end
end

