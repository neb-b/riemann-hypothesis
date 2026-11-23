module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSizeRWordNeTopOfLe
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.Grow GlobalTheory.Mem.AutSpace
open scoped ENNReal

namespace GlobalTheory.Size

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {V : HSp D} {φ : GA D V → ℂ} {N : ℕ}

private lemma rderC_sum_smul (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) (τ : D.what₂.Tau) {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (c : ι → ℂ) (M : ι → Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    RderC θ V τ (∑ a ∈ s, c a • M a) φ = ∑ a ∈ s, c a • RderC θ V τ (M a) φ := by
  induction s using Finset.induction_on with
  | empty =>

    have h0 := GlobalTheory.Mem.RealTranslate.RderC_smul hθ hs τ (0 : ℂ) (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    rw [zero_smul, zero_smul] at h0
    rw [Finset.sum_empty, Finset.sum_empty, h0]
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, GlobalTheory.Mem.RealTranslate.RderC_add hθ hs,
      GlobalTheory.Mem.RealTranslate.RderC_smul hθ hs, ih]

theorem RderC_eq_sum_glDer (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) (τ : D.what₂.Tau)
    (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    RderC θ V τ Z φ = ∑ a : Fin V.rank × Fin V.rank, Z a.1 a.2 • glDer θ V (τ, a) φ := by

  have hZ : Z = ∑ a : Fin V.rank × Fin V.rank, Z a.1 a.2 • Matrix.single a.1 a.2 (1 : ℂ) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Fintype.sum_prod_type]

    rw [Fintype.sum_eq_single i fun x hx => by simp [hx], Fintype.sum_eq_single j fun y hy => by simp [hy]]
    simp
  conv_lhs => rw [hZ]
  rw [rderC_sum_smul hθ hs τ]
  simp only [glDer]

theorem Rder_eq_sum_glDer (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    Rder θ V τ X φ = ∑ a : Fin V.rank × Fin V.rank, X a.1 a.2 • glDer θ V (τ, a) φ := by

  rw [← GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hX φ]
  exact RderC_eq_sum_glDer hθ hs τ X


variable (θ V N) in
def wordFin (l : List (D.what₂.Tau × Fin V.rank × Fin V.rank)) : Submodule ℂ (GA D V → ℂ) where
  carrier := {f | f ∈ SmFun θ V ∧ growthSize V N (wordAct (glDer θ V) l f) ≠ ∞}
  add_mem' h h' := ⟨add_mem h.1 h'.1, by
    rw [(linOnSm_glWord l).add _ h.1 _ h'.1]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨h.2, h'.2⟩) growthSize_add_le⟩
  zero_mem' := ⟨zero_mem _, by
    have := (linOnSm_glWord (θ := θ) l).smul 0 0
    rw [zero_smul, zero_smul] at this
    rw [this]
    exact (growthSize_const (0 : ℂ)).trans_ne enorm_ne_top⟩
  smul_mem' c _ h := ⟨(SmFun θ V).smul_mem c h.1, by
    rw [(linOnSm_glWord l).smul, growthSize_smul]
    exact ENNReal.mul_ne_top enorm_ne_top h.2⟩

theorem rWord_mem_wordFin (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) {d : ℕ} (h : growthSob θ V d N φ ≠ ∞)
    (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (hl : IsLieWord V l) :
    ∀ l', l'.length + l.length ≤ d → rWord θ V l φ ∈ wordFin θ V N l' := by
  have hsum : wordSum (glDer θ V) (growthSize V N) d φ ≠ ∞ := h
  induction l with
  | nil =>

    intro l' hl'
    have hlen : l'.length ≤ d := by simpa using hl'
    have hw : rWord θ V [] φ = φ := wordAct_nil _ φ
    rw [hw]
    show φ ∈ SmFun θ V ∧ growthSize V N (wordAct (glDer θ V) l' φ) ≠ ∞
    exact ⟨hs, wordSum_ne_top_iff.1 hsum l' hlen⟩
  | cons p t ih =>

    intro l' hl'
    have hp : p.2 ∈ lieAt V p.1 := hl p (List.mem_cons_self ..)
    have ht : IsLieWord V t := fun q hq => hl q (List.mem_cons_of_mem p hq)
    have hψ : rWord θ V t φ ∈ SmFun θ V :=
      (show _ ∧ _ from ih ht [] (by simp only [List.length_cons, List.length_nil] at hl' ⊢; omega)).1
    have hw : rWord θ V (p :: t) φ = Rder θ V p.1 p.2 (rWord θ V t φ) := wordAct_cons _ p t φ
    rw [hw, Rder_eq_sum_glDer hθ hψ hp]
    refine sum_mem fun a _ => Submodule.smul_mem _ _ ?_
    have hm : growthSize V N (wordAct (glDer θ V) (l' ++ [(p.1, a)]) (rWord θ V t φ)) ≠ ∞ :=
      (show _ ∧ _ from ih ht (l' ++ [(p.1, a)])
        (by simp only [List.length_cons, List.length_append, List.length_nil] at hl' ⊢; omega)).2
    have he : wordAct (glDer θ V) (l' ++ [(p.1, a)]) (rWord θ V t φ) =
        wordAct (glDer θ V) l' (glDer θ V (p.1, a) (rWord θ V t φ)) := by
      rw [wordAct_append, wordAct_cons, wordAct_nil]
    show glDer θ V (p.1, a) (rWord θ V t φ) ∈ SmFun θ V ∧
      growthSize V N (wordAct (glDer θ V) l' (glDer θ V (p.1, a) (rWord θ V t φ))) ≠ ∞
    rw [← he]
    exact ⟨(linOnSm_RderC p.1 _).mem _ hψ, hm⟩

theorem growthSize_rWord_ne_top_of_le (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) {d : ℕ} (h : growthSob θ V d N φ ≠ ∞)
    {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)} (hl : IsLieWord V l) (hd : l.length ≤ d) :
    growthSize V N (rWord θ V l φ) ≠ ∞ := by
  have hm := rWord_mem_wordFin hθ hs h l hl [] (by simpa using hd)
  have h2 : growthSize V N (wordAct (glDer θ V) [] (rWord θ V l φ)) ≠ ∞ := (show _ ∧ _ from hm).2
  rwa [wordAct_nil] at h2

theorem growthSize_rWord_ne_top (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) (h : ∀ d, growthSob θ V d N φ ≠ ∞) :
    ∀ l, IsLieWord V l → growthSize V N (rWord θ V l φ) ≠ ∞ := fun l hl =>
  growthSize_rWord_ne_top_of_le hθ hs (h l.length) hl le_rfl

theorem unifModGrowth_iff_growthSob (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) :
    UnifModGrowth V θ φ ↔ ∃ N, ∀ d, growthSob θ V d N φ ≠ ∞ := by
  refine ⟨exists_growthSob_ne_top hs, ?_⟩
  rintro ⟨M, hM⟩
  exact unifModGrowth_iff.2 ⟨M, growthSize_rWord_ne_top hθ hs hM⟩

end GlobalTheory.Size

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergEquivariantIsometry
section
open MeasureTheory
open scoped SchwartzMap

noncomputable section

namespace GlobalTheory.HeisenbergL2

section Real

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def heisS (a : V) (L : V →L[ℝ] ℝ) (c t : ℝ) (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ
    (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ)))
    (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f)

def derS (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f -
    (2 * Real.pi * Complex.I) • SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) f

theorem heisS_apply (a : V) (L : V →L[ℝ] ℝ) (c t : ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    heisS a L c t f x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ)) * f (x + t • a) := by
  rw [heisS, SchwartzMap.smulLeftCLM_apply_apply (by
      rw [GlobalTheory.LinPhaseSeminorm.phase_eq]; exact GlobalTheory.LinPhaseSeminorm.hasTemperateGrowth_phase L c t),
    SchwartzMap.compSubConstCLM_apply, smul_eq_mul, sub_neg_eq_add]

theorem derS_apply (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    derS a L f x = fderiv ℝ f x a - 2 * Real.pi * Complex.I * ((L x : ℝ) : ℂ) * f x := by
  have hL : Function.HasTemperateGrowth (fun x => ((L x : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.comp L).hasTemperateGrowth
  rw [derS, SchwartzMap.sub_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hL,
    LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul, smul_eq_mul]
  ring

theorem seminorm_heisS_sub_le (a : V) (L : V →L[ℝ] ℝ) (c : ℝ) (f : 𝓢(V, ℂ)) (k n : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 →
      SchwartzMap.seminorm ℂ k n (heisS a L c t f - f - (t : ℂ) • derS a L f) ≤ C * t ^ 2 := by
  set P : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) with hP
  set d := LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f with hd
  obtain ⟨C3, hC3⟩ := GlobalTheory.LinPhaseSeminorm.seminorm_smulLeft_phase_le L c k n
  choose C1 hC1 using fun m => GlobalTheory.SchwartzTranslate.seminorm_translate_sub_le a f k m
  obtain ⟨C2, hC2⟩ := GlobalTheory.LinearPhase.seminorm_phase_sub_le L c d k n
  obtain ⟨C0, hC0⟩ := GlobalTheory.LinearPhase.seminorm_phase_sub_le L c f k n
  set p := SchwartzMap.seminorm ℂ k n (E := V) (F := ℂ) with hp
  refine ⟨|C3| * ∑ m ∈ Finset.range (n + 1), |C1 m| + |C2| + 2 * Real.pi * p (P d) + |C0|, fun t ht => ?_⟩
  set M : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ
    (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ))) with hM
  set X := SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f - (t : ℂ) • d with hX
  set Y := M d - d + ((t : ℂ) * (2 * Real.pi * Complex.I)) • P d with hY
  set Z := M f - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • P f with hZ
  have e : heisS a L c t f - f - (t : ℂ) • derS a L f =
      M X + (t : ℂ) • Y - ((t : ℂ) ^ 2 * (2 * Real.pi * Complex.I)) • P d + Z := by
    rw [heisS, derS, ← hM, ← hP, ← hd, hX, hY, hZ, map_sub, map_sub, map_smul]
    module
  rw [e]
  have t1 : p (M X) ≤ |C3| * (∑ m ∈ Finset.range (n + 1), |C1 m|) * t ^ 2 := by
    refine (hC3 t ht X).trans ?_
    calc C3 * ∑ m ∈ Finset.range (n + 1), SchwartzMap.seminorm ℂ k m X
        ≤ |C3| * ∑ m ∈ Finset.range (n + 1), SchwartzMap.seminorm ℂ k m X :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Finset.sum_nonneg fun _ _ => apply_nonneg _ _)
      _ ≤ |C3| * ∑ m ∈ Finset.range (n + 1), |C1 m| * t ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ =>
            (hC1 m t ht).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))) (abs_nonneg _)
      _ = |C3| * (∑ m ∈ Finset.range (n + 1), |C1 m|) * t ^ 2 := by rw [← Finset.sum_mul]; ring
  have t2 : p ((t : ℂ) • Y) ≤ |C2| * t ^ 2 := by
    rw [map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 := hC2 t ht
    calc |t| * p Y ≤ 1 * (C2 * t ^ 2) := mul_le_mul ht h2 (apply_nonneg _ _) zero_le_one
      _ ≤ |C2| * t ^ 2 := by rw [one_mul]; exact mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
  have t3 : p (((t : ℂ) ^ 2 * (2 * Real.pi * Complex.I)) • P d) = 2 * Real.pi * p (P d) * t ^ 2 := by
    rw [map_smul_eq_mul]
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat, Complex.norm_I,
      abs_of_pos Real.pi_pos, sq_abs]
    ring
  have t4 : p Z ≤ |C0| * t ^ 2 := (hC0 t ht).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))
  have tri : p (M X + (t : ℂ) • Y - ((t : ℂ) ^ 2 * (2 * Real.pi * Complex.I)) • P d + Z) ≤
      p (M X) + p ((t : ℂ) • Y) + p (((t : ℂ) ^ 2 * (2 * Real.pi * Complex.I)) • P d) + p Z := by
    refine (map_add_le_add p _ _).trans (add_le_add ?_ le_rfl)
    refine (map_sub_le_add p _ _).trans (add_le_add ?_ le_rfl)
    exact map_add_le_add p _ _
  rw [t3] at tri
  nlinarith [t1, t2, t4, tri]

end Real

section L2

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

theorem toLp_heisS_sub_le (μ : Measure V) [μ.HasTemperateGrowth] (a : V) (L : V →L[ℝ] ℝ) (c : ℝ)
    (f : 𝓢(V, ℂ)) : ∃ K : ℝ, ∀ t : ℝ, |t| ≤ 1 →
      ‖(heisS a L c t f - f - (t : ℂ) • derS a L f).toLp 2 μ‖ ≤ K * t ^ 2 := by
  obtain ⟨k, C, hC0, hC⟩ := SchwartzMap.norm_toLp_le_seminorm ℂ ℂ 2 μ
  choose K hK using fun p : ℕ × ℕ => seminorm_heisS_sub_le a L c f p.1 p.2
  refine ⟨C * ∑ p ∈ Finset.Iic (k, 0), |K p|, fun t ht => ?_⟩
  refine (hC _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC0
  rw [Finset.sum_mul]
  refine Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun _ _ => by positivity) fun p hp => ?_
  refine ((hK p t ht).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg t))).trans ?_
  exact Finset.single_le_sum (f := fun q => |K q| * t ^ 2) (fun _ _ => by positivity) hp

theorem norm_toLp_two (μ : Measure V) [μ.HasTemperateGrowth] (u : 𝓢(V, ℂ)) :
    ‖u.toLp 2 μ‖ = Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂μ) := by
  rw [SchwartzMap.norm_toLp' (by norm_num) (by norm_num), ENNReal.toReal_ofNat]
  simp only [Real.rpow_two]
  rw [Real.sqrt_eq_rpow, one_div]

theorem map_dHeis_of_isometry : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (T : SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ), (∀ f, ∫ x, ‖T f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    ∀ w w' : V × V, (∀ (s : ℝ) (f g : SchwartzMap V ℂ), ⇑g = GlobalTheory.GaussLine.heisFun β (s • w).1 (s • w).2 ⇑f →
      ⇑(T g) = GlobalTheory.GaussLine.heisFun β (s • w').1 (s • w').2 ⇑(T f)) →
    ∀ f g : SchwartzMap V ℂ, (∀ x, g x = GlobalTheory.GaussLine.dHeis β w ⇑f x) →
    ∀ x, T g x = GlobalTheory.GaussLine.dHeis β w' ⇑(T f) x := by
  intro V _ _ _ _ _ μ _ β T hT w w' hw f g hg x
  haveI : μ.HasTemperateGrowth := MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth
  let Lf : V × V → (V →L[ℝ] ℝ) := fun p => LinearMap.toContinuousLinearMap (β.flip p.2)
  have hLf : ∀ p y, Lf p y = β y p.2 := fun p y => rfl
  have hheis : ∀ (p : V × V) (F : 𝓢(V, ℂ)) (t : ℝ),
      ⇑(heisS p.1 (Lf p) (β p.1 p.2 / 2) t F) = GlobalTheory.GaussLine.heisFun β (t • p).1 (t • p).2 ⇑F := by
    intro p F t
    funext y
    rw [heisS_apply, GlobalTheory.GaussLine.heisFun_apply, hLf, Prod.smul_fst, Prod.smul_snd]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    congr 3
    ring_nf
  have hder : ∀ (p : V × V) (F : 𝓢(V, ℂ)) y, derS p.1 (Lf p) F y = GlobalTheory.GaussLine.dHeis β p ⇑F y := by
    intro p F y
    rw [derS_apply, GlobalTheory.GaussLine.dHeis, hLf]
  have hgS : g = derS w.1 (Lf w) f := by
    ext y
    rw [hg, hder]
  set G := derS w'.1 (Lf w') (T f) with hG
  set c := β w.1 w.2 / 2
  set c' := β w'.1 w'.2 / 2
  have hHT : ∀ t : ℝ, T (heisS w.1 (Lf w) c t f) = heisS w'.1 (Lf w') c' t (T f) := fun t =>
    DFunLike.coe_injective ((hw t f _ (hheis w f t)).trans (hheis w' (T f) t).symm)
  obtain ⟨K, hK⟩ := toLp_heisS_sub_le μ w.1 (Lf w) c f
  obtain ⟨K', hK'⟩ := toLp_heisS_sub_le μ w'.1 (Lf w') c' (T f)
  set ℓ := SchwartzMap.toLpCLM ℂ ℂ 2 μ with hℓ
  have hiso : ∀ u, ‖ℓ (T u)‖ = ‖ℓ u‖ := by
    intro u
    rw [hℓ, SchwartzMap.toLpCLM_apply, SchwartzMap.toLpCLM_apply, norm_toLp_two, norm_toLp_two, hT]
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖ℓ (T g - G)‖ ≤ (K + K') * t := by
    intro t ht0 ht1
    have hta : |t| ≤ 1 := by rw [abs_of_pos ht0]; exact ht1
    have e1 : (t : ℂ) • (T g - G) = (heisS w'.1 (Lf w') c' t (T f) - T f - (t : ℂ) • G) -
        T (heisS w.1 (Lf w) c t f - f - (t : ℂ) • g) := by
      rw [map_sub, map_sub, map_smul, hHT, smul_sub]
      abel
    have h1 : ‖ℓ ((t : ℂ) • (T g - G))‖ = t * ‖ℓ (T g - G)‖ := by
      rw [map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg ht0.le]
    have h2 : ‖ℓ ((t : ℂ) • (T g - G))‖ ≤ K' * t ^ 2 + K * t ^ 2 := by
      rw [e1, map_sub]
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · have := hK' t hta
        rw [hℓ, SchwartzMap.toLpCLM_apply]
        exact this
      · rw [hiso, hgS, hℓ, SchwartzMap.toLpCLM_apply]
        exact hK t hta
    rw [h1] at h2
    have h3 : t * ‖ℓ (T g - G)‖ ≤ t * ((K + K') * t) := by nlinarith
    exact le_of_mul_le_mul_left h3 ht0
  have ha : ‖ℓ (T g - G)‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖ℓ (T g - G)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    set a := ‖ℓ (T g - G)‖
    set M := |K + K'| + 1 with hMdef
    have hM : 0 < M := by positivity
    set t := min 1 (a / (2 * M)) with htdef
    have ht0 : 0 < t := lt_min one_pos (by positivity)
    have h1 := key t ht0 (min_le_left _ _)
    have h2 : t ≤ a / (2 * M) := min_le_right _ _
    have h3 : (K + K') * t ≤ M * t := mul_le_mul_of_nonneg_right ((le_abs_self _).trans (by linarith)) ht0.le
    have h4 : M * t ≤ M * (a / (2 * M)) := mul_le_mul_of_nonneg_left h2 hM.le
    have h5 : M * (a / (2 * M)) = a / 2 := by field_simp
    linarith
  have h0 : (T g - G).toLp 2 μ = (0 : 𝓢(V, ℂ)).toLp 2 μ := by
    have := norm_eq_zero.1 ha
    rw [hℓ, SchwartzMap.toLpCLM_apply] at this
    rw [this]
    exact ((map_zero ℓ).symm.trans (SchwartzMap.toLpCLM_apply))
  have h00 : T g - G = 0 := SchwartzMap.injective_toLp 2 μ h0
  have := congrArg (fun u : 𝓢(V, ℂ) => u x) (sub_eq_zero.1 h00)
  rw [this, hG, hder]

end L2

end GlobalTheory.HeisenbergL2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentTwistedGroupEndomorphism
section
noncomputable section

namespace GlobalTheory.UnitaryIdemCut

section Gen

open Matrix Formalism.UG

variable {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]

def cutM (b : A) (hb : b * b = b) : Matrix n n A →* Matrix n n A where
  toFun M := b • M + (1 - b) • 1
  map_one' := by rw [← add_smul]; simp
  map_mul' M N := by
    have h1 : b * (1 - b) = 0 := by linear_combination -hb
    have h2 : (1 - b) * b = 0 := by linear_combination -hb
    have h3 : (1 - b) * (1 - b) = 1 - b := by linear_combination hb
    simp only [add_mul, mul_add, smul_mul_smul_comm, hb, h1, h2, h3, zero_smul, add_zero, zero_add, mul_one]

def cutGL (b : A) (hb : b * b = b) : GL n A →* GL n A := Units.map (cutM b hb)

theorem cutGL_val (b : A) (hb : b * b = b) (g : GL n A) :
    (cutGL b hb g).val = b • g.val + (1 - b) • 1 := rfl

theorem map_cut (φ : A →+* B) (b : A) (M : Matrix n n A) :
    (b • M + (1 - b) • (1 : Matrix n n A)).map φ = φ b • M.map φ + (1 - φ b) • (1 : Matrix n n B) := by
  ext i j
  by_cases h : i = j <;> simp [h]

theorem bc_cutGL (φ : A →+* B) (b : A) (hb : b * b = b) (b' : B) (hb' : b' * b' = b') (e : φ b = b')
    (g : GL n A) : bc φ (cutGL b hb g) = cutGL b' hb' (bc φ g) := by
  subst e
  exact Units.ext (map_cut φ b g.val)

theorem bc_cutGL_eq_one (φ : A →+* B) (b : A) (hb : b * b = b) {g : GL n A} (hg : bc φ g = 1) :
    bc φ (cutGL b hb g) = 1 := by
  rw [bc_cutGL φ b hb _ (by rw [← map_mul, hb]) rfl, hg, map_one]

theorem cutGL_conj (b : A) (hb : b * b = b) (β g : GL n A) :
    cutGL b hb (β * g * β⁻¹) = β * cutGL b hb g * β⁻¹ := by
  apply Units.ext
  simp only [cutGL_val, Units.val_mul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, Units.mul_inv]

theorem cutGL_mem_UJ (σ : A →+* A) (J : Matrix n n A) (b : A) (hb : b * b = b) (hσ : σ b = b) {g : GL n A}
    (hg : g ∈ UJ σ J) : cutGL b hb g ∈ UJ σ J := by
  have hg' : cT σ g.val * J * g.val = J := hg
  show cT σ (b • g.val + (1 - b) • 1) * J * (b • g.val + (1 - b) • 1) = J
  have e : cT σ (b • g.val + (1 - b) • (1 : Matrix n n A)) = b • cT σ g.val + (1 - b) • 1 := by
    unfold cT
    rw [map_cut, hσ, transpose_add, transpose_smul, transpose_smul, transpose_one]
  have h1 : b * (1 - b) = 0 := by linear_combination -hb
  have h2 : (1 - b) * b = 0 := by linear_combination -hb
  have h3 : (1 - b) * (1 - b) = 1 - b := by linear_combination hb
  rw [e]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, hb, h1, h2, h3, zero_smul, add_zero,
    zero_add, mul_one, one_mul, hg']
  rw [← add_smul]; simp

def cutUJ (σ : A →+* A) (J : Matrix n n A) (b : A) (hb : b * b = b) (hσ : σ b = b) : UJ σ J →* UJ σ J :=
  ((cutGL b hb).comp (UJ σ J).subtype).codRestrict _ fun g => cutGL_mem_UJ σ J b hb hσ g.2

end Gen

section Ad

open NumberField IsDedekindDomain Formalism.UG Formalism.L2.DIV
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem idem_mem_intAd (a : FiniteAdeleRing (𝓞 F) F) (ha : a * a = a) : a ∈ intAd F := by
  intro v
  have h : a v * a v = a v := congrArg (fun x : FiniteAdeleRing (𝓞 F) F => x v) ha
  rcases eq_or_ne (a v) 0 with h0 | h0
  · rw [h0]; exact zero_mem _
  · rw [mul_left_cancel₀ h0 (h.trans (mul_one _).symm)]; exact one_mem _

theorem cutGL_mem_St (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (b : E ⊗[F] Formalism.L2.Herm.Af F) (hb : b * b = b)
    (hi : b ∈ Formalism.L2.Herm.intAf F E) {g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hg : g ∈ St β) :
    cutGL b hb g ∈ St β := by
  obtain ⟨y, rfl⟩ := hg
  refine ⟨cutGL (⟨b, hi⟩ : Formalism.L2.Herm.intAf F E) (Subtype.ext hb) y, ?_⟩
  show β * intGL F E n _ * β⁻¹ = cutGL b hb (β * intGL F E n y * β⁻¹)
  rw [cutGL_conj]
  unfold intGL
  rw [bc_cutGL _ _ _ b hb rfl]

theorem bc_cutGL_mem_St {A : Type} [CommRing A] (φ : A →+* E ⊗[F] Formalism.L2.Herm.Af F)
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (b : A) (hb : b * b = b)
    (hi : φ b ∈ Formalism.L2.Herm.intAf F E) {g : GL (Fin n) A} (hg : bc φ g ∈ St β) :
    bc φ (cutGL b hb g) ∈ St β := by
  have hb' : φ b * φ b = φ b := by rw [← map_mul, hb]
  rw [bc_cutGL φ b hb _ hb' rfl]
  exact cutGL_mem_St β _ hb' hi hg

end Ad

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sigR_algebraMap {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (r : R) : sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem exists_cutHA {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (r : R)
    (hb : algebraMap R (R ⊗[F] E) r * algebraMap R (R ⊗[F] E) r = algebraMap R (R ⊗[F] E) r) :
    ∃ κ : HA R σ J →* HA R σ J, ∀ g, HA.mat R σ J (κ g) = cutGL _ hb (HA.mat R σ J g) :=
  ⟨cutUJ (sigR R σ) (JR R J) _ hb (sigR_algebraMap R σ r), fun _ => rfl⟩

theorem mem_GfC_iff {D : D7} (V : HSp D) (g : GA D V) :
    g ∈ GfC V ↔ Formalism.UG.bc (infPart D) (matHom V g) = 1 := Iff.rfl

theorem finE_eq {D : D7} (V : HSp D) (g : GA D V) : finE V g = Formalism.UG.bc (toEAf D) (matHom V g) :=
  Units.ext (finE_val V g)

theorem exists_cut : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (ε : AF D.host.F), ε * ε = ε → ∃ κ : GA D V →* GA D V, ∀ g, Formalism.L2.Theta.mt V (κ g) = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt V g + (1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) ∧ (Stab V β g → Stab V β (κ g)) := by
  intro D V β ε hε
  have hb : algebraMap (AF D.host.F) (AE D) ε * algebraMap (AF D.host.F) (AE D) ε = algebraMap (AF D.host.F) (AE D) ε := by
    rw [← map_mul, hε]
  obtain ⟨κ, hκ⟩ := exists_cutHA (AF D.host.F) D.sp.cm.sig V.gram ε hb
  have hκ' : ∀ g, matHom V (κ g) = cutGL _ hb (matHom V g) := hκ
  refine ⟨κ, fun g => ⟨congrArg Units.val (hκ' g), fun h => ⟨?_, ?_⟩⟩⟩
  · have h1 := (mem_GfC_iff V g).1 h.1
    rw [mem_GfC_iff, hκ']
    exact bc_cutGL_eq_one (infPart D) _ hb h1
  · have h1 := h.2
    rw [finE_eq] at h1
    have hi : toEAf D (algebraMap (AF D.host.F) (AE D) ε) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      Subring.subset_closure (Or.inr ⟨⟨sndA D.host.F ε, idem_mem_intAd _ (by rw [← map_mul, hε])⟩, rfl⟩)
    rw [finE_eq, hκ']
    exact bc_cutGL_mem_St (toEAf D) β _ hb hi h1

end GlobalTheory.UnitaryIdemCut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyFockModelOfUnitaryPairCovers
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory

theorem nonempty_fockData_of_covers :
    ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q)
      (T2 : GrpData r s), Nonempty (FockData T0 T1 T2) :=
  _root_.GlobalTheory.nonempty_fockData_pair

end GlobalTheory
end

