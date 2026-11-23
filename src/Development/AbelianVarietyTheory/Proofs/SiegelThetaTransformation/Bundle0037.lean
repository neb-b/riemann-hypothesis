module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteClsAndStab
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsExOfPow
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsVacuaAndMultipliers
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.VacEx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {n : ℕ}

theorem row_mul_transpose (y : Matrix (Fin n) (Fin r) E) (γ : Matrix (Fin r) (Fin r) E)
    (k : Fin n) : (y * γᵀ) k = γ *ᵥ y k := by
  funext j
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]

theorem epsW_mul_transpose (w : E) (γ : GL (Fin r) E) (hγ : IsUn X γ)
    (y : Matrix (Fin n) (Fin r) E) :
    epsW X w (y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) = epsW X w y := by

  have key : ∀ k, EF X ((y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) k) (w • (y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) k) =
      EF X (y k) (w • y k) := by
    intro k
    rw [row_mul_transpose, ← Matrix.mulVec_smul, EF_def, EF_def, hγ (y k) (w • y k)]
  unfold epsW
  simp only [key]

end GlobalTheory.SW.VacEx

namespace GlobalTheory.SW

open VacEx

theorem exists_vacua_and_multipliers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ D : Level X, ∃ (v₀ : Lt E r → TF n g) (μ : GL (Fin r) E → Lt E r → ℂ), (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) ∧ ∀ γ ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx γ (v₀ L) = (μ γ L * (D.lam k : ℂˣ)) • v₀ (mapL γ L) := by
  intro E _ _ _ r X g bas idx n hs hn D

  obtain ⟨-, huniq, hgrp, hlats, -, -, -⟩ :=
    _root_.GlobalTheory.SW.level_laws E r X g bas idx (2 * r) hs ⟨r, two_mul r⟩ D (by omega)
  obtain ⟨-, hstd, -⟩ := GlobalTheory.SW.finite_cls_and_stab E n 1 one_pos

  have hvac : ∀ L, SelfD X L → (∃ v, IsVac X bas D.w (tens (stdL E n) L) v) ∧
      ∀ v v', IsVac X bas D.w (tens (stdL E n) L) v → IsSB v' →
        (∀ y ∈ tens (stdL E n) L, epsW X D.w y • heisG X bas y v' = v') → ∃ c : ℂ, v' = c • v := by
    intro L hL
    obtain ⟨h1, h2, -, -⟩ :=
      GlobalTheory.SW.TensVac.vacua E r X g bas idx n hs hn D.w D.w_int D.w_tr L hL 1 (stdL E n) hstd
    exact ⟨h1, fun v v' hv hv' hfix => ⟨_, h2 v v' hv hv' hfix⟩⟩
  classical
  let v₀ : Lt E r → TF n g := fun L =>
    if h : ∃ v, IsVac X bas D.w (tens (stdL E n) (D.sh L)) v then h.choose else 0
  have hv₀ : ∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L) := by
    intro L hL
    have h := (hvac _ (hlats L hL).1).1
    rw [show v₀ L = h.choose from dif_pos h]
    exact h.choose_spec

  let μ : GL (Fin r) E → Lt E r → ℂ := fun γ L =>
    if h : (∃ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k) ∧
        ∃ c : ℂ, wG X bas idx γ (v₀ L) = c • v₀ (mapL γ L)
    then h.2.choose * (((D.lam h.1.choose)⁻¹ : ℂˣ) : ℂ) else 0
  refine ⟨v₀, μ, hv₀, ?_⟩
  intro γ hγ L hL k hk
  obtain ⟨hγu, -⟩ := (hgrp γ).1 hγ
  obtain ⟨-, -, -, hmove⟩ := hlats L hL
  obtain ⟨hL', hsh⟩ := hmove γ hγ
  obtain ⟨hSB, -, hfix⟩ := hv₀ L hL
  have hv' := hv₀ _ hL'
  rw [hsh] at hv'
  have hSD' : SelfD X (mapL γ (D.sh L)) := by
    rw [← hsh]
    exact (hlats _ hL').1
  have hlaw := GlobalTheory.SW.wG_laws E r X g bas idx n hs hn γ hγu (v₀ L) hSB

  have himg : ∀ y ∈ tens (stdL E n) (mapL γ (D.sh L)),
      epsW X D.w y • heisG X bas y (wG X bas idx γ (v₀ L)) = wG X bas idx γ (v₀ L) := by
    intro y hy
    set y₀ : Matrix (Fin n) (Fin r) E := y * ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)ᵀ with hy₀
    have hyy : y₀ * (γ : Matrix (Fin r) (Fin r) E)ᵀ = y := by
      rw [hy₀, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
        Matrix.mul_one]
    have hy₀m : y₀ ∈ tens (stdL E n) (D.sh L) := by
      rw [GlobalTheory.SW.TensLat.mem_tens_stdL] at hy ⊢
      intro k
      obtain ⟨x, hx, hxk⟩ := Submodule.mem_map.mp (hy k)
      rw [hy₀, VacEx.row_mul_transpose, ← hxk]
      simp only [LinearMap.restrictScalars_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
        Units.inv_mul, Matrix.one_mulVec]
      exact hx
    have hSB0 : IsSB (heisG X bas y₀ (v₀ L)) := (GlobalTheory.SW.TensVac.laws idx hs hn y₀ hSB).1
    have hlaw0 := GlobalTheory.SW.wG_laws E r X g bas idx n hs hn γ hγu _ hSB0
    rw [← hyy, ← hlaw.2.2.2.2.2.2 y₀, VacEx.epsW_mul_transpose X D.w γ hγu y₀, ← hlaw0.2.2.2.1,
      hfix y₀ hy₀m]
  have hex : ∃ c : ℂ, wG X bas idx γ (v₀ L) = c • v₀ (mapL γ L) :=
    (hvac _ hSD').2 _ _ hv' hlaw.1 himg
  have hcond : (∃ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k) ∧
      ∃ c : ℂ, wG X bas idx γ (v₀ L) = c • v₀ (mapL γ L) := ⟨⟨k, hk⟩, hex⟩

  have hk' : hcond.1.choose = k := Subtype.ext (huniq _ _ _ hcond.1.choose_spec hk)
  have hμ : μ γ L = hcond.2.choose * (((D.lam hcond.1.choose)⁻¹ : ℂˣ) : ℂ) := dif_pos hcond
  rw [hμ, hk', mul_assoc, Units.inv_mul, mul_one]
  exact hcond.2.choose_spec

end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatticeOperatorCoefficients
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.Coef

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem ip_smul_smul {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι]
    {φ ψ : Matrix κ ι K → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ) (a b : ℂ) :
    ip (a • φ) (b • ψ) = a * conj b * ip φ ψ := by
  have hc : IsSB fun x => conj (ψ x) :=
    (isSB_algebra_haar_linear K κ ι ψ ψ hψ hψ).2.2.2.1
  have hp : IsSB (φ * fun x => conj (ψ x)) :=
    (isSB_algebra_haar_linear K κ ι φ _ hφ hc).2.2.1
  have hs := (isSB_algebra_haar_linear K κ ι _ _ hp hp).2.2.2.2.2.1 (a * conj b)
  have key : (fun x => (a • φ) x * conj ((b • ψ) x)) =
      (a * conj b) • (φ * fun x => conj (ψ x)) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, map_mul]
    ring
  unfold ip
  rw [key, hs]
  rfl

theorem classSum_eq_sum {M : ℕ} [Fintype (Cls E n M)] (f : Lt E n → ℂ) :
    classSum M f = ∑ c : Cls E n M, (wt M (Quot.out c).1 : ℂ) * f (Quot.out c).1 := by
  unfold classSum
  exact finsum_eq_sum_of_fintype _

theorem exists_mass {M : ℕ} (hM : 0 < M) : ∃ m : ℝ, 0 < m ∧
    (∀ (f : Lt E n → ℂ) (a : ℂ), (∀ Λ ∈ Vset E n M, f Λ = a) → classSum M f = m * a) ∧
    ∀ (f : Lt E n → ℂ) (b : ℝ), (∀ Λ ∈ Vset E n M, ‖f Λ‖ ≤ b) → ‖classSum M f‖ ≤ m * b := by
  classical
  obtain ⟨hfin, hstd, hwt, -, -⟩ := finite_cls_and_stab E n M hM
  let _ : Fintype (Cls E n M) := Fintype.ofFinite _
  refine ⟨∑ c : Cls E n M, wt M (Quot.out c).1, ?_, ?_, ?_⟩
  · apply Finset.sum_pos
    · intro c _
      exact (hwt _ (Quot.out c).2).2
    · exact ⟨(Quot.mk _ ⟨stdL E n, hstd⟩ : Cls E n M), Finset.mem_univ _⟩
  · intro f a hf
    rw [classSum_eq_sum, Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hf _ (Quot.out c).2]
  · intro f b hf
    rw [classSum_eq_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    have hw := (hwt _ (Quot.out c).2).2
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw.le]
    exact mul_le_mul_of_nonneg_left (hf _ (Quot.out c).2) hw.le

theorem classSum_mul {M : ℕ} (hM : 0 < M) (f : Lt E n → ℂ) (a : ℂ) :
    classSum M f * a = classSum M fun Λ => f Λ * a := by
  classical
  have := (finite_cls_and_stab E n M hM).1
  let _ : Fintype (Cls E n M) := Fintype.ofFinite _
  rw [classSum_eq_sum, classSum_eq_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => mul_assoc _ _ _

end GlobalTheory.SW.Coef

namespace GlobalTheory.SW

open Coef

private theorem classSum_congr_of_eqOn_Vset {E : Type} [Field E] [NumberField E] [IsCMField E]
    {n M : ℕ} {f g : Lt E n → ℂ} (h : ∀ Λ ∈ Vset E n M, f Λ = g Λ) :
    classSum M f = classSum M g := by
  unfold classSum
  exact finsum_congr fun c => by rw [h _ (Quot.out c).2]

theorem lattice_operator_coefficients : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (M : ℕ) (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)) (Φ : Lt E r → Lt E n → TF n g) (μ : GL (Fin r) E → Lt E r → ℂ), 0 < M → IsSystem X bas idx M Δ 𝓛 Φ μ → ∃ (a θ : ℝ), 0 < a ∧ θ < 1 ∧ (∀ L ∈ 𝓛, classSum M (fun Λ => ip (Φ L Λ) (Φ L Λ)) = a ∧ Summable (fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} => ‖classSum M (fun Λ => ip (Φ L Λ) (Φ L'.1 Λ))‖) ∧ ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, ‖classSum M (fun Λ => ip (Φ L Λ) (Φ L'.1 Λ))‖ ≤ θ * a) ∧ ∀ γ ∈ Δ, ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, classSum M (fun Λ => ip (Φ (mapL γ L) Λ) (Φ (mapL γ L') Λ)) * μ γ L * conj (μ γ L') = classSum M (fun Λ => ip (Φ L Λ) (Φ L' Λ)) := by
  intro E _ _ _ r X g bas idx n hs hn M Δ 𝓛 Φ μ hM hsys
  obtain ⟨m, hm, hconst, hbd⟩ := Coef.exists_mass (E := E) (n := n) hM
  obtain ⟨a, ha, hdiag, b, θ, hθ, hoff, hbt⟩ := hsys.norm
  have hma : 0 < m * a := mul_pos hm ha
  refine ⟨m * a, θ, hma, hθ, fun L hL => ?_, ?_⟩
  · have hb : ∀ L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L},
        ‖classSum M (fun Λ => ip (Φ L Λ) (Φ L'.1 Λ))‖ ≤ m * a * b L L'.1 := fun L' => by
      rw [mul_assoc]
      exact hbd _ (a * b L L'.1) fun Λ hΛ => hoff L hL L'.1 L'.2.1 Λ hΛ
    have hS : Summable fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} => m * a * b L L'.1 :=
      (hbt L hL).1.mul_left (m * a)
    have hT := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hS
    refine ⟨?_, hT, ?_⟩
    · rw [hconst _ (a : ℂ) fun Λ hΛ => hdiag L hL Λ hΛ]
      exact (Complex.ofReal_mul m a).symm
    · calc _ ≤ ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, m * a * b L L'.1 :=
            Summable.tsum_le_tsum hb hT hS
        _ = m * a * ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, b L L'.1 := tsum_mul_left
        _ ≤ m * a * θ := mul_le_mul_of_nonneg_left (hbt L hL).2 hma.le
        _ = θ * (m * a) := mul_comm _ _
  · intro γ hγ L hL L' hL'
    have hun := hsys.un γ hγ
    have key : ∀ Λ ∈ Vset E n M, ip (Φ L Λ) (Φ L' Λ) =
        ip (Φ (mapL γ L) Λ) (Φ (mapL γ L') Λ) * (μ γ L * conj (μ γ L')) := by
      intro Λ hΛ
      have hw := wG_laws E r X g bas idx n hs hn γ hun (Φ L Λ) (hsys.sb L hL Λ hΛ)
      rw [← (hw.2.2.1 (Φ L' Λ) (hsys.sb L' hL' Λ hΛ)).1, (hsys.mu γ hγ L hL).2 Λ hΛ,
        (hsys.mu γ hγ L' hL').2 Λ hΛ,
        Coef.ip_smul_smul (hsys.sb _ (hsys.stab γ hγ L hL) Λ hΛ)
          (hsys.sb _ (hsys.stab γ hγ L' hL') Λ hΛ)]
      ring
    rw [mul_assoc, Coef.classSum_mul hM]
    exact classSum_congr_of_eqOn_Vset fun Λ hΛ => (key Λ hΛ).symm

end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPeriodMapHomeomorphRiemannFormDensity
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker

theorem dense_of_span_real {g : ℕ} (S : Submodule ℚ (Fin g → ℂ))
    (hS : Submodule.span ℝ (S : Set (Fin g → ℂ)) = ⊤) : Dense (S : Set (Fin g → ℂ)) := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro z
  have hz : z ∈ Submodule.span ℝ (S : Set (Fin g → ℂ)) := hS ▸ Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem w hw => exact subset_closure hw
  | zero => exact subset_closure S.zero_mem
  | add a b _ _ ha hb => exact map_mem_closure₂ continuous_add ha hb fun c hc d hd => S.add_mem hc hd
  | smul t w _ hw =>

    have hq : ∀ q : ℚ, (q : ℝ) • w ∈ closure (S : Set (Fin g → ℂ)) := fun q =>
      map_mem_closure (continuous_const_smul (q : ℝ)) hw fun u hu => by
        rw [SetLike.mem_coe, Rat.cast_smul_eq_qsmul ℝ q u]
        exact S.smul_mem q hu
    have hcl : IsClosed {s : ℝ | s • w ∈ closure (S : Set (Fin g → ℂ))} :=
      isClosed_closure.preimage (continuous_id.smul continuous_const)
    have hsub : closure (Set.range fun q : ℚ => (q : ℝ)) ⊆ {s : ℝ | s • w ∈ closure (S : Set (Fin g → ℂ))} :=
      hcl.closure_subset_iff.2 (by rintro _ ⟨q, rfl⟩; exact hq q)
    exact hsub ((Rat.denseRange_cast (𝕜 := ℝ)).closure_range ▸ Set.mem_univ t)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r) {n : ℕ}

noncomputable def zRLin (x : Frame X.Ψ r) : WR X n →ₗ[ℝ] (Fin n → Fin g → ℂ) where
  toFun := zR X idx x
  map_add' u v := by
    funext k i
    simp only [zR, Pi.add_apply]
    split_ifs
    · simp [hermC, mul_add, Finset.sum_add_distrib]
    · rw [mulVec_add, Pi.add_apply]
  map_smul' t v := by
    funext k i
    simp only [zR, Pi.smul_apply, RingHom.id_apply]
    split_ifs
    · simp only [hermC, Pi.smul_apply, real_smul, map_mul, conj_ofReal, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    · rw [mulVec_smul, Pi.smul_apply]

theorem denseRange_pv (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    DenseRange (pv X idx x) := by

  have hrange : ((LinearMap.range ((LinearMap.funLeft ℚ ℂ idx).comp (perLin X x)) :
      Submodule ℚ (Fin g → ℂ)) : Set (Fin g → ℂ)) = Set.range (pv X idx x) := by
    ext z
    simp only [SetLike.mem_coe, LinearMap.mem_range, Set.mem_range]
    exact Iff.rfl
  unfold DenseRange
  rw [← hrange]
  apply dense_of_span_real
  rw [hrange]
  exact GlobalTheory.Dict.span_range_pv idx hs hx

theorem denseRange_zR_embR (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    DenseRange (zR X idx x ∘ embR X (n := n)) := by
  have h : zR X idx x ∘ embR X (n := n) = fun y k => pv X idx x (y k) := by
    funext y k
    exact zR_embR X idx x y k
  rw [h]
  exact DenseRange.piMap fun _ => denseRange_pv X idx hs hx

theorem exists_equiv_zR (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ L : WR X n ≃L[ℝ] (Fin n → Fin g → ℂ), ∀ v, L v = zR X idx x v := by

  have hsurj : Function.Surjective (zRLin X idx x (n := n)) := by
    have hcl : IsClosed (LinearMap.range (zRLin X idx x (n := n)) : Set (Fin n → Fin g → ℂ)) :=
      Submodule.closed_of_finiteDimensional _
    have hd : Dense (LinearMap.range (zRLin X idx x (n := n)) : Set (Fin n → Fin g → ℂ)) := by
      refine (denseRange_zR_embR X idx hs hx (n := n)).mono ?_
      rintro _ ⟨y, rfl⟩
      exact ⟨embR X y, rfl⟩
    have huniv := hcl.closure_eq.symm.trans hd.closure_eq
    intro z
    have hz : z ∈ (LinearMap.range (zRLin X idx x (n := n)) : Set (Fin n → Fin g → ℂ)) := by
      rw [huniv]
      trivial
    exact LinearMap.mem_range.1 hz

  have hg : g = Fintype.card X.Ψ * r := by
    simpa [Fintype.card_prod] using Fintype.card_congr idx
  have hdim : Module.finrank ℝ (WR X n) = Module.finrank ℝ (Fin n → Fin g → ℂ) := by
    simp only [WR, Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, hg]
    ring
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
  exact ⟨(LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).toContinuousLinearEquiv, fun v => rfl⟩

theorem EFR_embR (y y' : Matrix (Fin n) (Fin r) E) :
    EFR X (embR X y) (embR X y') = ((∑ k, EF X (y k) (y' k) : ℚ) : ℝ) := by
  have key : ∀ (τ : X.Ψ) (k : Fin n),
      hermC τ.1 X.Gm (embR X y τ k) (embR X y' τ k) = τ.1 (herm X.Gm (y k) (y' k)) :=
    fun τ k => ReciprocityTheory.ChartRestriction.G.FD.hermC_emb τ.1 X.Gm (y k) (y' k)
  rw [EFR, Rat.cast_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [EF_def, GlobalTheory.UnitFrame.trace_eq_sum_re X.Ψ X.cmType]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [key, map_mul]

theorem zR_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, (∃ L : WR X n ≃L[ℝ] (Fin n → Fin g → ℂ), ∀ v, L v = zR X idx x v) ∧ (∀ v v' : WR X n, (∑ k, hx X bas idx x (zR X idx x v k) (zR X idx x v' k)).im = EFR X v v') ∧ (∀ y y' : Matrix (Fin n) (Fin r) E, EFR X (embR X y) (embR X y') = ((∑ k, EF X (y k) (y' k) : ℚ) : ℝ)) ∧ DenseRange (embR X (n := n)) ∧ ∀ γ : GL (Fin r) E, IsUn X γ → ∀ v : WR X n, zR X idx (lact γ x) (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k) = zR X idx x v := by
  intro E _ _ _ r X g q0 _ bas idx n hs hn x hxd
  obtain ⟨L, hL⟩ := exists_equiv_zR X idx (n := n) hs hxd
  have hlaws := GlobalTheory.Dict.hx_laws E r X g bas idx n hs hn x hxd

  have hD : DenseRange (embR X (n := n)) := by
    have h1 : embR X (n := n) = L.symm ∘ (zR X idx x ∘ embR X) := by
      funext y
      simp only [Function.comp_apply, ← hL, ContinuousLinearEquiv.symm_apply_apply]
    rw [h1]
    exact L.symm.surjective.denseRange.comp (denseRange_zR_embR X idx hs hxd) L.symm.continuous

  have hB : ∀ v v' : WR X n,
      (∑ k, hx X bas idx x (zR X idx x v k) (zR X idx x v' k)).im = EFR X v v' := by
    have hc1 : Continuous fun p : WR X n × WR X n =>
        (∑ k, hx X bas idx x (zR X idx x p.1 k) (zR X idx x p.2 k)).im := by
      simp only [← hL, GlobalTheory.Dict.hx]
      fun_prop
    have hc2 : Continuous fun p : WR X n × WR X n => EFR X p.1 p.2 := by
      simp only [EFR, hermC]
      fun_prop
    have heq := (hD.prodMap hD).equalizer hc1 hc2 (by
      funext ⟨y, y'⟩
      simp only [Function.comp_apply, Prod.map_apply]
      rw [EFR_embR X y y', Complex.im_sum, Rat.cast_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [zR_embR, zR_embR]
      exact hlaws.2.2.1 (y k) (y' k))
    exact fun v v' => congrFun heq (v, v')

  have hF : ∀ γ : GL (Fin r) E, IsUn X γ → ∀ v : WR X n,
      zR X idx (lact γ x) (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k) =
        zR X idx x v := by
    intro γ hγ
    have hA : Continuous fun v : WR X n =>
        (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k : WR X n) := by
      fun_prop
    have hc1 : Continuous fun v : WR X n =>
        zR X idx (lact γ x) (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k) :=
      (LinearMap.continuous_of_finiteDimensional (zRLin X idx (lact γ x) (n := n))).comp hA
    have hc2 : Continuous fun v : WR X n => zR X idx x v := by
      simp only [← hL]
      exact L.continuous
    have heq := hD.equalizer hc1 hc2 (by
      funext y
      simp only [Function.comp_apply]
      have hemb : (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ embR X y τ k : WR X n) =
          embR X (Matrix.of fun k => (γ : Matrix (Fin r) (Fin r) E) *ᵥ y k) := by
        funext τ k
        exact (GlobalTheory.PerMove.emb_mulVec τ.1 _ (y k)).symm
      rw [hemb]
      funext k
      rw [zR_embR, zR_embR]
      exact (hlaws.2.2.2.2.2.2.2 γ hγ).2.1 (y k))
    exact fun v => congrFun heq v
  exact ⟨⟨L, hL⟩, hB, fun y y' => EFR_embR X y y', hD, hF⟩

end GlobalTheory.Ker
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumTensorLatticeFixedRationalHeisenberg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.Phase

theorem vacS_of_isVac : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ Λ ∈ Vset E n 1, ∀ v : TF n g, IsVac X bas w (tens Λ L) v → ∃ A ε, VacS A ε v := by
  intro E _ _ _ r X g bas idx n hs hn w hw hw' L hL Λ hΛ v hv
  have hA : TensVac.Good X w (tens Λ L) := by
    obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.tensorLattice_selfDual_semicharacter_index E r X g bas idx n hs hn w hw hw' L hL 1 Λ hΛ
    exact ⟨h1, h2, h3⟩
  let e := AddEquiv.ofBijective _ (TensVac.crdHom_bijective (n := n) hs)
  have he (y) : e.symm (TensVac.crdHom hs y) = y := e.symm_apply_apply y
  have ho (y y' : Matrix (Fin n) (Fin r) E) :
      Phase.om (TensVac.crdHom hs y) (TensVac.crdHom hs y') = -∑ k, EF X (y k) (y' k) :=
    TensVac.om_crdHom hs y y'
  refine ⟨(tens Λ L).map (TensVac.crdHom hs), fun p => epsW X w (e.symm p),
    Vac.fg_map hA.1 _, ?_, ?_, ?_, ⟨2, two_pos, ?_⟩, hv.1, ?_⟩
  · intro p
    obtain ⟨y, rfl⟩ := (TensVac.crdHom_bijective hs).2 p
    rw [AddSubgroup.mem_map_iff_mem (TensVac.crdHom_bijective hs).1, hA.2.1]
    constructor
    · rintro h _ ⟨y', hy', rfl⟩
      obtain ⟨k, hk⟩ := h y' hy'
      exact ⟨-k, by rw [ho, hk, Int.cast_neg]⟩
    · intro h y' hy'
      obtain ⟨k, hk⟩ := h _ ⟨y', hy', rfl⟩
      rw [ho] at hk
      exact ⟨-k, by rw [Int.cast_neg, ← hk, neg_neg]⟩
  · rintro _ ⟨y, hy, rfl⟩
    have := congrArg norm (TensVac.epsW_mul_conj (X := X) w (e.symm (TensVac.crdHom hs y)))
    rw [norm_mul, Complex.norm_conj, norm_one] at this
    exact (mul_self_eq_one_iff.1 this).resolve_right fun h => by
      linarith [norm_nonneg (epsW X w (e.symm (TensVac.crdHom hs y)))]
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    rw [← map_add (f := _), he, he, he, ho, (hA.2.2 y hy).2 y' hy', Rat.cast_neg, mul_neg]
  · rintro _ ⟨y, hy, rfl⟩
    rw [← map_nsmul, he, hA.eps_two hs hy]
  · rintro _ ⟨y, hy, rfl⟩
    rw [he]
    exact hv.2.2 y hy

end GlobalTheory.Phase
end

