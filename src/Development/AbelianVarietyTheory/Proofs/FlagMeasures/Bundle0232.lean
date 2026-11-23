module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualUnipotentGroupActsUnitriangularOnto
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsKFinNeZeroOfCwCont
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_param_maxCompact {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mx k r}
    (hP : PI.UpqRep.IsCayleyU k r ε P) :
    ∃ κ : Formalism.REAL.KG ε → Mx k r, Continuous κ ∧ (∀ x, κ x ∈ GG k r) ∧ κ 1 = 1 ∧
      (∀ x y, κ (x * y) = κ x * κ y) ∧
      ∀ g ∈ PI.UpqRep.UH (PI.UpqRep.Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _),
        ∃ x, κ x = g := by
  obtain ⟨⟨-, hPJ⟩, hPU⟩ := hP
  have h1 : Pᴴ * P = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hPU
    rwa [Matrix.star_eq_conjTranspose] at h
  have h2 : P * Pᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hPU
    rwa [Matrix.star_eq_conjTranspose] at h
  have hcong : ∀ A B : Mx k r, (Pᴴ * A * P) * (Pᴴ * B * P) = Pᴴ * (A * B) * P := by
    intro A B
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P Pᴴ, h2, Matrix.one_mul]
  have hherm : ∀ A : Mx k r, (Pᴴ * A * P)ᴴ = Pᴴ * Aᴴ * P := by
    intro A
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hJ : Formalism.QuantumDeterminants.Hpk k r = Pᴴ * Formalism.REAL.Jm ε * P := hPJ.symm
  refine ⟨fun x => Pᴴ * Formalism.REAL.toMK x * P, ?_, ?_, ?_, ?_, ?_⟩
  · have hc : Continuous (fun x : Formalism.REAL.KG ε => Formalism.REAL.toMK x) :=
      Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
    exact (continuous_const.matrix_mul hc).matrix_mul continuous_const
  · intro x
    have hx : (Formalism.REAL.toMK x)ᴴ * Formalism.REAL.Jm ε * Formalism.REAL.toMK x = Formalism.REAL.Jm ε :=
      (x : Formalism.REAL.UJ ε).2
    show (Pᴴ * Formalism.REAL.toMK x * P)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Pᴴ * Formalism.REAL.toMK x * P) =
      Formalism.QuantumDeterminants.Hpk k r
    rw [hJ, hherm, hcong, hcong, hx]
  · show Pᴴ * Formalism.REAL.toMK (1 : Formalism.REAL.KG ε) * P = 1
    rw [show Formalism.REAL.toMK (1 : Formalism.REAL.KG ε) = 1 from rfl, Matrix.mul_one, h1]
  · intro x y
    show Pᴴ * Formalism.REAL.toMK (x * y) * P = (Pᴴ * Formalism.REAL.toMK x * P) * (Pᴴ * Formalism.REAL.toMK y * P)
    rw [hcong]
    rfl
  · rintro g ⟨hgH, hgU⟩
    have hgH' : gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g = Pᴴ * Formalism.REAL.Jm ε * P := by
      have h : gᴴ * PI.UpqRep.Hpk k r * g = PI.UpqRep.Hpk k r := hgH
      rw [← hPJ] at h
      exact h
    have g1 : gᴴ * g = 1 := by
      have h := Matrix.mem_unitaryGroup_iff'.mp hgU
      rwa [Matrix.star_eq_conjTranspose] at h
    have g2 : g * gᴴ = 1 := by
      have h := Matrix.mem_unitaryGroup_iff.mp hgU
      rwa [Matrix.star_eq_conjTranspose] at h
    set M := P * g * Pᴴ with hM
    have hMH : Mᴴ = P * gᴴ * Pᴴ := by
      rw [hM]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    have M1 : Mᴴ * M = 1 := by
      rw [hMH, hM]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Pᴴ P, h1, Matrix.one_mul, ← Matrix.mul_assoc gᴴ g, g1, Matrix.one_mul, h2]
    have M2 : M * Mᴴ = 1 := by
      rw [hMH, hM]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Pᴴ P, h1, Matrix.one_mul, ← Matrix.mul_assoc g gᴴ, g2, Matrix.one_mul, h2]
    have MJ : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε := by
      calc Mᴴ * Formalism.REAL.Jm ε * M = P * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * Pᴴ := by
            rw [hMH, hM]
            simp only [Matrix.mul_assoc]
        _ = P * (Pᴴ * Formalism.REAL.Jm ε * P) * Pᴴ := by rw [hgH']
        _ = Formalism.REAL.Jm ε := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc P Pᴴ, h2, Matrix.one_mul, Matrix.mul_one]
    have MK : M * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * M := by
      calc M * Formalism.REAL.Jm ε = M * (Mᴴ * Formalism.REAL.Jm ε * M) := by rw [MJ]
        _ = (M * Mᴴ) * Formalism.REAL.Jm ε * M := by simp only [Matrix.mul_assoc]
        _ = Formalism.REAL.Jm ε * M := by rw [M2, Matrix.one_mul]
    have MU : M ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
      exact M2
    let u : (Mx k r)ˣ := ⟨M, Mᴴ, M2, M1⟩
    have hu : u ∈ Formalism.REAL.UJ ε := MJ
    have hk : (⟨u, hu⟩ : Formalism.REAL.UJ ε) ∈ Formalism.REAL.KG ε := (⟨MU, MK⟩ : M ∈ Formalism.REAL.Kset ε)
    refine ⟨⟨⟨u, hu⟩, hk⟩, ?_⟩
    show Pᴴ * M * P = g
    rw [hM]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pᴴ P, h1, Matrix.one_mul, Matrix.mul_one]

theorem exists_kFin_ne_zero_of_cwCont : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (Bm : R.H → V), (∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) → (∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v) → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm → (∃ v ∈ R.sm, Bm v ≠ 0) → ∃ x, R.KFin x ∧ Bm x ≠ 0 := by
  intro hKS k r ε mu R hR V _ _ _ _ Bm hadd hsmul hcw hex
  obtain ⟨v, hv, hBv⟩ := hex
  haveI : SecondCountableTopology (Formalism.REAL.KG ε) :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  by_contra hcon
  push_neg at hcon
  obtain ⟨P, hP, -⟩ := hR.2
  obtain ⟨κ, hκc, hκG, hκ1, hκm, hκs⟩ := exists_param_maxCompact hP
  obtain ⟨hmul, hone, -, -, -, -, -, -, hσc⟩ := rep_basic_of_isDS hKS k r ε mu R hR
  have hBc := (cwCont_continuousOn_hasDerivAt hKS k r ε mu R hR V Bm hadd hsmul hcw v hv).1
  have hf : Continuous (fun x => Bm (R.σ (κ x) v)) := hBc.comp_continuous hκc hκG
  have hw : Continuous (fun x => R.σ (κ x) v) := (hσc v).comp_continuous hκc hκG
  have hint : ∀ q : Formalism.REAL.KG ε → ℂ, Continuous q →
      Integrable (fun x => q x • R.σ (κ x) v) (Formalism.REAL.muK ε) := fun q hq =>
    (hq.smul hw).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsig : ∀ y, ∀ q : Formalism.REAL.KG ε → ℂ, Continuous q →
      R.σ (κ y) (∫ x, q x • R.σ (κ x) v ∂(Formalism.REAL.muK ε)) =
        ∫ x, q (y⁻¹ * x) • R.σ (κ x) v ∂(Formalism.REAL.muK ε) := by
    intro y q hq
    calc R.σ (κ y) (∫ x, q x • R.σ (κ x) v ∂(Formalism.REAL.muK ε))
        = ∫ x, R.σ (κ y) (q x • R.σ (κ x) v) ∂(Formalism.REAL.muK ε) :=
          ((R.σ (κ y)).integral_comp_comm (hint q hq)).symm
      _ = ∫ x, (fun z => q (y⁻¹ * z) • R.σ (κ z) v) (y * x) ∂(Formalism.REAL.muK ε) := by
          congr 1
          funext x
          simp [hκm, hmul _ (hκG y) _ (hκG x)]
      _ = _ := integral_mul_left_eq_self (μ := Formalism.REAL.muK ε) (fun z => q (y⁻¹ * z) • R.σ (κ z) v) y
  let φ : C(Formalism.REAL.KG ε, ℂ) := ⟨fun x => ⟪Bm v, Bm (R.σ (κ x) v)⟫_ℂ, continuous_const.inner hf⟩
  have hφ : φ = 0 := by
    refine KHolExt.eq_zero_of_orth φ (fun p hp => ?_)
    obtain ⟨ι, _, a, b, -, hab⟩ := hp
    obtain ⟨u, hu⟩ : ∃ u, u = ∫ x, p x • R.σ (κ x) v ∂(Formalism.REAL.muK ε) := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : ι → R.H, ∀ i, c i = ∫ x, b i x • R.σ (κ x) v ∂(Formalism.REAL.muK ε) :=
      ⟨_, fun _ => rfl⟩
    have hdec : ∀ y, R.σ (κ y) u = ∑ i, a i y • c i := by
      intro y
      rw [hu, hsig y p p.continuous]
      have hx : ∀ x, p (y⁻¹ * x) • R.σ (κ x) v = ∑ i, a i y • (b i x • R.σ (κ x) v) := by
        intro x
        rw [hab, Finset.sum_smul]
        simp only [mul_smul]
      simp_rw [hx]
      rw [integral_finsetSum Finset.univ (f := fun i x => a i y • (b i x • R.σ (κ x) v))
        (fun i _ => (hint _ (b i).continuous).smul (a i y))]
      simp only [integral_smul, hc]
    have hFT : FiniteDimensional ℂ (Submodule.span ℂ (Set.range c)) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range c)
    let S := Submodule.span ℂ (Set.range fun y => R.σ (κ y) u)
    have hST : S ≤ Submodule.span ℂ (Set.range c) := by
      rw [Submodule.span_le]
      rintro _ ⟨y, rfl⟩
      show R.σ (κ y) u ∈ Submodule.span ℂ (Set.range c)
      rw [hdec y]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    have hKF : R.KFin u := by
      unfold BranchingSupport.Rep.KFin PI.UpqRep.IsKFinHpk
      refine ⟨S, Submodule.finiteDimensional_of_le hST, ?_, ?_⟩
      · have h1 : R.σ (κ 1) u ∈ S := Submodule.subset_span ⟨1, rfl⟩
        rwa [hκ1, hone] at h1
      · intro g hg x hx
        obtain ⟨y', rfl⟩ := hκs g hg
        have hmap : S.map (R.σ (κ y') : R.H →ₗ[ℂ] R.H) ≤ S := by
          rw [Submodule.map_span_le]
          rintro _ ⟨y, rfl⟩
          refine Submodule.subset_span ⟨y' * y, ?_⟩
          simp [hκm, hmul _ (hκG y') _ (hκG y)]
        exact hmap (Submodule.mem_map_of_mem hx)
    have hus : u ∈ R.sm := hKS k r ε mu R.H R.σ hR.1 hR.2 u hKF
    have hB0 : Bm u = 0 := hcon u hKF
    have hI := GlobalTheory.T.cwCont_integral_comm_alt hKS k r ε mu R hR V Bm hadd hsmul hcw (Formalism.REAL.KG ε) (Formalism.REAL.muK ε) κ p
      hκc hκG p.continuous v hv (hu ▸ hus)
    have hfi : Integrable (fun x => p x • Bm (R.σ (κ x) v)) (Formalism.REAL.muK ε) :=
      (p.continuous.smul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    calc ∫ x, p x * φ x ∂(Formalism.REAL.muK ε)
        = ∫ x, innerSL ℂ (Bm v) (p x • Bm (R.σ (κ x) v)) ∂(Formalism.REAL.muK ε) := by
          congr 1
          funext x
          simp [φ, inner_smul_right]
      _ = innerSL ℂ (Bm v) (∫ x, p x • Bm (R.σ (κ x) v) ∂(Formalism.REAL.muK ε)) :=
          (innerSL ℂ (Bm v)).integral_comp_comm hfi
      _ = 0 := by rw [← hI, ← hu, hB0, map_zero]
  have h1 := DFunLike.congr_fun hφ 1
  change ⟪Bm v, Bm (R.σ (κ 1) v)⟫_ℂ = 0 at h1
  rw [hκ1, hone, inner_self_eq_zero] at h1
  exact hBv h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnipotentAddIsotropicToAnisotropic
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

noncomputable section

namespace GlobalTheory.LocOver.ZStep

open GlobalTheory.LocOver.UnipOnto

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

def eichG (x v : V) (c : E) (w : V) : V :=
  w + H.h w v • x - H.h w x • v + (c * H.h w x) • x

def eichGL (x v : V) (c : E) : V →ₗ[E] V where
  toFun := eichG H x v c
  map_add' y y' := by
    simp only [eichG, H.h_add_left, add_smul, mul_add]; abel
  map_smul' a y := by
    simp only [eichG, H.h_smul_left, RingHom.id_apply]; module

lemma eichG_hL (x v : V) (c : E) (y w : V) : H.h (eichG H x v c y) w =
    H.h y w + H.h y v * H.h x w - H.h y x * H.h v w + c * H.h y x * H.h x w := by
  simp only [eichG, H.h_add_left, h_sub_left, H.h_smul_left]

lemma eichG_hR (x v : V) (c : E) (w y : V) : H.h w (eichG H x v c y) =
    H.h w y + M.L.cj (H.h y v) * H.h w x - M.L.cj (H.h y x) * H.h w v +
      M.L.cj c * M.L.cj (H.h y x) * H.h w x := by
  simp only [eichG, h_add_right, h_sub_right, h_smul_right, map_mul]

variable {H}

lemma eichG_isom {x v : V} {c : E} (hxx : H.h x x = 0) (hxv : H.h x v = 0)
    (hc : c + M.L.cj c + H.h v v = 0) (y y' : V) :
    H.h (eichG H x v c y) (eichG H x v c y') = H.h y y' := by
  have hvx : H.h v x = 0 := by rw [h_right, hxv, map_zero]
  have e1 : H.h x y' = M.L.cj (H.h y' x) := h_right H x y'
  have e2 : H.h v y' = M.L.cj (H.h y' v) := h_right H v y'
  simp only [eichG_hL, eichG_hR]
  rw [hxx, hxv, hvx, e1, e2]
  linear_combination (H.h y x * M.L.cj (H.h y' x)) * hc

lemma eichG_inv {x v : V} {c c' : E} (hxx : H.h x x = 0) (hxv : H.h x v = 0)
    (hc : c + c' + H.h v v = 0) (w : V) :
    eichG H x v c (eichG H (-x) v c' w) = w := by
  have hvx : H.h v x = 0 := by rw [h_right, hxv, map_zero]
  have e1 : H.h (eichG H (-x) v c' w) v = H.h w v + H.h w x * H.h v v := by
    rw [eichG_hL, h_neg_left, h_neg_right, hxv]; ring
  have e2 : H.h (eichG H (-x) v c' w) x = H.h w x := by
    rw [eichG_hL, h_neg_left, h_neg_right, hxx, hvx]; ring
  have key : eichG H x v c (eichG H (-x) v c' w) - w = ((c + c' + H.h v v) * H.h w x) • x := by
    unfold eichG at e1 e2 ⊢
    rw [e1, e2, h_neg_right]
    module
  rw [hc, zero_mul, zero_smul, sub_eq_zero] at key
  exact key

lemma smul_memO {Λ : Submodule M.L.O V} {α : E} (hα : α ∈ M.L.O) {v : V} (hv : v ∈ Λ) : α • v ∈ Λ :=
  Λ.smul_mem ⟨α, hα⟩ hv

lemma span_h_left {s : Set V} {u : V} (hs : ∀ g ∈ s, H.h g u ∈ M.L.O) :
    ∀ g ∈ Submodule.span M.L.O s, H.h g u ∈ M.L.O := by
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg => exact hs g hg
  | zero => rw [H.h_zero_left]; exact M.L.O.zero_mem
  | add a b _ _ ha hb => rw [H.h_add_left]; exact M.L.O.add_mem ha hb
  | smul α a _ ha =>
    show H.h ((α : E) • a) u ∈ M.L.O
    rw [H.h_smul_left]; exact M.L.O.mul_mem α.2 ha

lemma span_h_right {s : Set V} {g : V} (hs : ∀ u ∈ s, H.h g u ∈ M.L.O) :
    ∀ u ∈ Submodule.span M.L.O s, H.h g u ∈ M.L.O := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem u hu => exact hs u hu
  | zero => rw [h_zero_right]; exact M.L.O.zero_mem
  | add a b _ _ ha hb => rw [h_add_right]; exact M.L.O.add_mem ha hb
  | smul α a _ ha =>
    show H.h g ((α : E) • a) ∈ M.L.O
    rw [h_smul_right]; exact M.L.O.mul_mem (GlobalTheory.UnramOrder.cj_mem M.L α.2) ha

lemma eichG_maps {Λ : Submodule M.L.O V} {x v : V} {c : E} (hc : c ∈ M.L.O) (hxL : x ∈ Λ) (hvL : v ∈ Λ)
    (hgx : ∀ g ∈ Λ, H.h g x ∈ M.L.O) (hgv : ∀ g ∈ Λ, H.h g v ∈ M.L.O) :
    ∀ w ∈ Λ, eichG H x v c w ∈ Λ := by
  intro w hw
  unfold eichG
  refine Λ.add_mem (Λ.sub_mem (Λ.add_mem hw (smul_memO (hgv w hw) hxL)) (smul_memO (hgx w hw) hvL))
    (smul_memO (M.L.O.mul_mem hc (hgx w hw)) hxL)

end GlobalTheory.LocOver.ZStep

namespace GlobalTheory.LocOver.ZStep

open GlobalTheory.LocOver.UnipOnto

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ} (Fr : FrameD H r)

lemma e_mem_X (a : Fin r) : Fr.f a.castSucc ∈ H.X Fr.f := Submodule.subset_span ⟨a, rfl⟩

lemma spanO_le_X {x : V} (hx : x ∈ Submodule.span M.L.O (Set.range fun a : Fin r => Fr.f a.castSucc)) :
    x ∈ H.X Fr.f := by
  induction hx using Submodule.span_induction with
  | mem u hu => exact Submodule.subset_span hu
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul α a _ ha => exact Submodule.smul_mem _ (α : E) ha

lemma e_mem_LamStd (L : Submodule M.L.O (H.Wb Fr.f)) (a : Fin r) : Fr.f a.castSucc ∈ Fr.LamStd L := by
  refine Submodule.subset_span ⟨fun b => ?_, fun b => ?_, ⟨0, ?_, by simp⟩⟩
  · rw [Fr.h_es]; split_ifs
    · exact M.L.O.one_mem
    · exact M.L.O.zero_mem
  · rw [FrameD.e, Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last a))]; exact M.L.O.zero_mem
  · have h2 : ∀ b, H.h (Fr.f a.castSucc) (Fr.e b) = 0 := fun b => Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last a))
    simp only [FrameD.prF, Fr.h_es, h2, zero_smul, Finset.sum_const_zero, sub_zero, ite_smul, one_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp [FrameD.e]

end GlobalTheory.LocOver.ZStep

namespace GlobalTheory.LocOver.ZStep

open GlobalTheory.LocOver.UnipOnto

theorem zstep : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V]
    (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)), Fr.IsInner L →
    ∀ y : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f y ∈ L → H.h (Fr.f (Fin.last r)) (y : V) = 1 →
    (∀ a, H.h (y : V) (Fr.es a) = 0) →
    ∀ x ∈ Submodule.span M.L.O (Set.range fun a : Fin r => Fr.f a.castSucc),
    ∃ n ∈ Fr.N, n (Fr.f (Fin.last r)) = Fr.f (Fin.last r) + x ∧ (∀ w ∈ H.X Fr.f, n w = w) ∧
      img n (Fr.LamStd L) = Fr.LamStd L := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H r Fr L hL y hyL hzy hyes x hx
  letI := hOK.loc
  haveI := hOK.char0

  have hyX : ∀ w ∈ H.X Fr.f, H.h w (y : V) = 0 := fun w hw => by rw [h_right, y.2 w hw, map_zero]
  have hxX : x ∈ H.X Fr.f := spanO_le_X Fr hx
  have hxx : H.h x x = 0 := X_iso Fr x hxX x hxX
  have hxy : H.h x y = 0 := hyX x hxX
  have hnx : H.h (-x) (-x) = 0 := by rw [h_neg_left, h_neg_right, neg_neg, hxx]
  have hny : H.h (-x) y = 0 := by rw [h_neg_left, hxy, neg_zero]

  have hyy : H.h (y : V) y ∈ M.L.O := (hL.2.1 y).1 hyL y hyL
  obtain ⟨t, ht⟩ := GlobalTheory.UnramOrder.exists_int_of_fixed M.L hyy (H.h_herm _ _).symm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨c, hcO, hc⟩ := (GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ).1 (-t)
  have hc1 : c + M.L.cj c + H.h (y : V) y = 0 := by
    rw [hc, ht, ← map_add (f := _)]
    simp
  have hc2 : M.L.cj c + c + H.h (y : V) y = 0 := by rw [← hc1]; ring
  have hcjO : M.L.cj c ∈ M.L.O := GlobalTheory.UnramOrder.cj_mem M.L hcO

  let n : V ≃ₗ[E] V := LinearEquiv.ofLinear (ZStep.eichGL H x y c) (ZStep.eichGL H (-x) y (M.L.cj c))
    (LinearMap.ext fun w => ZStep.eichG_inv hxx hxy hc1 w)
    (LinearMap.ext fun w => by
      have := ZStep.eichG_inv (c := M.L.cj c) (c' := c) hnx hny hc2 w
      rw [neg_neg] at this
      exact this)
  have hn : ∀ w, n w = ZStep.eichG H x y c w := fun w => rfl

  set Λ := Fr.LamStd L with hΛ
  have heL : ∀ a : Fin r, Fr.f a.castSucc ∈ Λ := fun a => e_mem_LamStd Fr L a
  have hxL : x ∈ Λ := by
    refine Submodule.span_le.2 ?_ hx
    rintro _ ⟨a, rfl⟩
    exact heL a
  have hyLam : (y : V) ∈ Λ := by
    refine Submodule.subset_span ⟨fun a => by rw [hyes a]; exact M.L.O.zero_mem,
      fun a => by rw [show H.h (y : V) (Fr.e a) = 0 from y.2 _ (e_mem_X Fr a)]; exact M.L.O.zero_mem, ⟨y, ?_, hyL⟩⟩
    have h2 : ∀ a, H.h (y : V) (Fr.e a) = 0 := fun a => y.2 _ (e_mem_X Fr a)
    simp [FrameD.prF, hyes, h2]

  have hgen : ∀ g ∈ {v | (∀ a, H.h v (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h v (Fr.e a) ∈ M.L.O) ∧
      ∃ w : ↥(H.perp (H.X Fr.f)), (w : V) = Fr.prF v ∧ H.mkW Fr.f w ∈ L},
      H.h g y ∈ M.L.O ∧ H.h g x ∈ M.L.O := by
    rintro g ⟨hges, hge, w, hw, hwL⟩
    refine ⟨?_, ?_⟩
    · have hpr : H.h (Fr.prF g) y = H.h g y := by
        have h1 : ∀ a, H.h (Fr.es a) (y : V) = 0 := fun a => by rw [h_right, hyes a, map_zero]
        have h2 : ∀ a, H.h (Fr.e a) (y : V) = 0 := fun a => hyX _ (e_mem_X Fr a)
        simp only [FrameD.prF, h_sub_left]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [show H.h (∑ a, H.h g (Fr.es a) • Fr.e a) (y : V) = UnipOnto.lf H (y : V) (∑ a, H.h g (Fr.es a) • Fr.e a) from rfl,
          show H.h (∑ a, H.h g (Fr.e a) • Fr.es a) (y : V) = UnipOnto.lf H (y : V) (∑ a, H.h g (Fr.e a) • Fr.es a) from rfl,
          map_sum, map_sum]
        simp [UnipOnto.lf, H.h_smul_left, h1, h2]
      rw [← hpr, ← hw]
      exact (hL.2.1 w).1 hwL y hyL
    · refine span_h_right (s := Set.range fun a : Fin r => Fr.f a.castSucc) ?_ x hx
      rintro _ ⟨a, rfl⟩
      exact hge a
  have hgy : ∀ g ∈ Λ, H.h g y ∈ M.L.O := span_h_left fun g hg => (hgen g hg).1
  have hgx : ∀ g ∈ Λ, H.h g x ∈ M.L.O := span_h_left fun g hg => (hgen g hg).2
  have hgnx : ∀ g ∈ Λ, H.h g (-x) ∈ M.L.O := fun g hg => by
    rw [h_neg_right]; exact M.L.O.neg_mem (hgx g hg)
  have hmap := eichG_maps hcO hxL hyLam hgx hgy
  have hmap' := eichG_maps hcjO (Λ.neg_mem hxL) hyLam hgnx hgy
  refine ⟨n, ?_, ?_, ?_, ?_⟩
  · rw [N_eq]
    show n ∈ NU H Fr.f
    refine ⟨fun w w' => eichG_isom hxx hxy hc1 w w', fun a => ?_, fun v hv => ?_⟩
    · have h1 : H.h (Fr.f a.castSucc) y = 0 := hyX _ (e_mem_X Fr a)
      have h2 : H.h (Fr.f a.castSucc) x = 0 := X_iso Fr _ (e_mem_X Fr a) x hxX
      rw [hn]
      simp only [eichG, h1, h2, zero_smul, mul_zero, add_zero, sub_zero, sub_self]
      exact Submodule.zero_mem _
    · have h2 : H.h v x = 0 := hv x hxX
      rw [hn]
      have : eichG H x y c v - v = H.h v y • x := by simp [eichG, h2]
      rw [this]
      exact Submodule.smul_mem _ _ hxX
  · rw [hn]
    have hzx : H.h (Fr.f (Fin.last r)) x = 0 := z_X Fr x hxX
    simp [eichG, hzy, hzx]
  · intro w hw
    rw [hn]
    have h1 : H.h w y = 0 := hyX w hw
    have h2 : H.h w x = 0 := X_iso Fr w hw x hxX
    simp [eichG, h1, h2]
  · apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact hmap w hw
    · intro w hw
      exact ⟨eichG H (-x) y (M.L.cj c) w, hmap' w hw, eichG_inv hxx hxy hc1 w⟩

end GlobalTheory.LocOver.ZStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFintypeProd
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.Push


open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
variable {ι : Type} [Fintype ι] {X : ι → Type} {mX : ∀ i, MeasurableSpace (X i)}
    {μ : (i : ι) → Measure (X i)} [∀ i, SigmaFinite (μ i)] in
private theorem lmarginal_prod_eq_prod_lintegral_mul_prod [DecidableEq ι] (f : (i : ι) → X i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (s : Finset ι) (x : (i : ι) → X i) :
    (∫⋯∫⁻_s, (fun z => ∏ i, f i (z i)) ∂μ) x =
      (∏ i ∈ s, ∫⁻ y, f i y ∂(μ i)) * ∏ i ∈ sᶜ, f i (x i) := by
  have hF : Measurable fun z : (i : ι) → X i => ∏ i, f i (z i) :=
    Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
  induction s using Finset.induction_on generalizing x with
  | empty => simp
  | insert i s hi ih =>
    rw [lmarginal_insert _ hF hi]
    simp_rw [ih]
    have h : ∀ y, ∏ j ∈ sᶜ, f j (Function.update x i y j) =
        f i y * ∏ j ∈ (insert i s)ᶜ, f j (x j) := by
      intro y
      rw [Finset.compl_insert, ← Finset.mul_prod_erase _ _ (Finset.mem_compl.2 hi),
        Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    simp_rw [h]
    rw [Finset.prod_insert hi, lintegral_const_mul _ ((hf i).mul_const _),
      lintegral_mul_const _ (hf i)]
    ring

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
theorem _root_.GlobalTheory.SnMass.Push.lintegral_fintype_prod {ι : Type} [Fintype ι] {X : ι → Type}
    {mX : ∀ i, MeasurableSpace (X i)}
    {μ : (i : ι) → Measure (X i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : ι) → X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → X i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  classical
  by_cases hne : ∀ i, Nonempty (X i)
  · rw [lintegral_eq_lmarginal_univ (fun i => (hne i).some), lmarginal_prod_eq_prod_lintegral_mul_prod f hf]
    simp
  · push_neg at hne
    obtain ⟨i, hi⟩ := hne
    haveI : IsEmpty ((i : ι) → X i) := ⟨fun x => hi.elim (x i)⟩
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Measure.eq_zero_of_isEmpty (μ i)])]
    simp [Measure.eq_zero_of_isEmpty (Measure.pi μ)]

end GlobalTheory.SnMass.Push
end
end

