module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0160
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSumIntegralCubeDerivatives
section
open MeasureTheory
open scoped ContDiff

namespace GlobalTheory.CubeTaylor

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

open MeasureTheory in
open scoped ContDiff in
private theorem integral_cube_succ_eq_iterated {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (N : ℕ) (s : ℝ) (F : (Fin (N + 1) → ℝ) → K)
    (hF : Continuous F) :
    ∫ t in Set.univ.pi (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s), F t =
      ∫ t in Set.univ.pi (fun _ : Fin N => Set.Icc (0 : ℝ) s),
        ∫ r in Set.Icc (0 : ℝ) s, F (Fin.snoc t r) := by
  have hsnoc : Continuous fun p : (Fin N → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (N + 1) → ℝ) :=
    Continuous.finSnoc (A := fun _ => ℝ) continuous_fst continuous_snd
  have hF' : Continuous fun p : (Fin N → ℝ) × ℝ => F (Fin.snoc p.1 p.2) := hF.comp hsnoc
  have hG : Continuous fun t : Fin N → ℝ => ∫ r in Set.Icc (0 : ℝ) s, F (Fin.snoc t r) :=
    continuous_parametric_integral_of_continuous (f := fun t r => F (Fin.snoc t r)) hF'
      isCompact_Icc
  have hcube : IsCompact (Set.univ.pi fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hcube' : IsCompact (Set.univ.pi fun _ : Fin N => Set.Icc (0 : ℝ) s) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  set X := ∫ t in Set.univ.pi (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s), F t with hX
  set Y := ∫ t in Set.univ.pi (fun _ : Fin N => Set.Icc (0 : ℝ) s),
    ∫ r in Set.Icc (0 : ℝ) s, F (Fin.snoc t r) with hY
  have key : ∀ e : K, (inner ℂ e X).re = (inner ℂ e Y).re := by
    intro e
    let L : K →L[ℝ] ℝ := Complex.reCLM.comp ((innerSL ℂ e).restrictScalars ℝ)
    have hL : ∀ x, L x = (inner ℂ e x).re := fun x => rfl
    rw [← hL, ← hL, hX, hY,
      ← L.integral_comp_comm (hF.continuousOn.integrableOn_compact hcube),
      ← L.integral_comp_comm (hG.continuousOn.integrableOn_compact hcube'),
      (_root_.GlobalTheory.integral_cube_succ_last N s (fun t => L (F t)) (L.continuous.comp hF)).2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    exact L.integral_comp_comm
      ((hF.comp (Continuous.finSnoc (A := fun _ => ℝ) continuous_const continuous_id)).continuousOn.integrableOn_compact
        isCompact_Icc)
  have h := key (X - Y)
  have h2 : ‖X - Y‖ ^ 2 = 0 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_sub_right, map_sub]
    simp only [RCLike.re_to_complex]
    rw [h, sub_self]
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2))

open MeasureTheory in
open scoped ContDiff in
private theorem eq_interval_average_sub_weighted_deriv
    {G : Type} [Group G] [TopologicalSpace G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (ρ : G →* (K →L[ℂ] K)) (hcont : ∀ v, Continuous fun g => ρ g v)
    {s : ℝ} (hs : 0 < s) (c : ℝ → G) (hc : Continuous c) (hc0 : c 0 = 1)
    (hadd : ∀ a b, c (a + b) = c a * c b) (w w' : K)
    (hd : HasDerivAt (fun t : ℝ => ρ (c t) w) w' 0) :
    w = (∫ r in Set.Icc 0 s, ((1 / s : ℝ) : ℂ) • ρ (c r) w) -
      ∫ r in Set.Icc 0 s, (((s - r) / s : ℝ) : ℂ) • ρ (c r) w' := by
  have hg : ∀ r, HasDerivAt (fun t => ρ (c t) w) (ρ (c r) w') r := by
    intro r
    have h1 : HasDerivAt (fun t => ρ (c (t - r)) w) w' r := by
      have := hd
      rw [← sub_self r] at this
      exact this.comp_sub_const r r
    have h2 := ((ρ (c r)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r h1
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← hadd, add_sub_cancel]
  have hb : ∀ r : ℝ, HasDerivAt (fun t : ℝ => (((s - t) / s : ℝ) : ℂ)) (((-(1 / s)) : ℝ) : ℂ) r := by
    intro r
    have : HasDerivAt (fun t : ℝ => (s - t) / s) (-(1 / s)) r := by
      simpa [neg_div] using ((hasDerivAt_id r).const_sub s).div_const s
    exact this.ofReal_comp
  have hh : ∀ r ∈ Set.uIcc 0 s, HasDerivAt (fun t => (((s - t) / s : ℝ) : ℂ) • ρ (c t) w)
      ((((s - r) / s : ℝ) : ℂ) • ρ (c r) w' + (((-(1 / s)) : ℝ) : ℂ) • ρ (c r) w) r :=
    fun r _ => (hb r).smul (hg r)
  have hgc : Continuous fun t => ρ (c t) w := (hcont w).comp hc
  have hg'c : Continuous fun t => ρ (c t) w' := (hcont w').comp hc
  have hA : Continuous fun r : ℝ => (((s - r) / s : ℝ) : ℂ) • ρ (c r) w' := by
    exact (Complex.continuous_ofReal.comp ((continuous_const.sub continuous_id).div_const s)).smul hg'c
  have hB : Continuous fun r : ℝ => (((-(1 / s)) : ℝ) : ℂ) • ρ (c r) w :=
    continuous_const.smul hgc
  have hE := intervalIntegral.integral_eq_sub_of_hasDerivAt hh
    ((hA.add hB).intervalIntegrable 0 s)
  rw [intervalIntegral.integral_add (hA.intervalIntegrable 0 s) (hB.intervalIntegrable 0 s),
    intervalIntegral.integral_of_le hs.le, intervalIntegral.integral_of_le hs.le] at hE
  simp only [sub_self, zero_div, Complex.ofReal_zero, zero_smul, sub_zero, div_self hs.ne',
    Complex.ofReal_one, one_smul, hc0, map_one, ContinuousLinearMap.one_apply] at hE
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
  have hneg : ∫ r in Set.Ioc 0 s, (((-(1 / s)) : ℝ) : ℂ) • ρ (c r) w =
      -∫ r in Set.Ioc 0 s, ((1 / s : ℝ) : ℂ) • ρ (c r) w := by
    rw [← integral_neg]
    congr 1
    funext r
    rw [Complex.ofReal_neg, neg_smul]
  rw [hneg] at hE
  have key : ∀ x A B : K, A + -B = 0 - x → x = B - A := by
    intro x A B h
    calc x = -(0 - x) := by abel
      _ = -(A + -B) := by rw [h]
      _ = B - A := by abel
  exact key _ _ _ hE


open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] in
theorem _root_.GlobalTheory.CubeTaylor.eq_sum_integral_cube_derivatives : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K], ∀ (ρ : G →* (K →L[ℂ] K)), (∀ g v, ‖ρ g v‖ = ‖v‖) → (∀ v, Continuous fun g => ρ g v) → ∀ (s : ℝ), 0 < s → ∀ (N : ℕ) (c : Fin N → ℝ → G), (∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b) → ∃ (J : Type) (_ : Fintype J) (κ : J → (Fin N → ℝ) → ℂ) (l : J → List (Fin N)), (∀ j, Continuous (κ j)) ∧ ∀ (d : Fin N → K → K) (S : Set K), (∀ v ∈ S, ∀ i, d i v ∈ S ∧ HasDerivAt (fun t : ℝ => ρ (c i t) v) (d i v) 0) → ∀ v ∈ S, v = ∑ j, ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), κ j t • ρ (List.ofFn fun i => c i (t i)).prod ((l j).foldr d v) := by
  intro G _ _ _ K _ _ _ ρ _ hcont s hs N
  induction N with
  | zero =>
    intro c hc
    refine ⟨Unit, inferInstance, fun _ _ => 1, fun _ => [], fun _ => continuous_const, ?_⟩
    intro d S hS v hv
    simp [Measure.real, Real.volume_Icc_pi]
  | succ N ih =>
    intro c hc
    obtain ⟨J, hJ, κ, l, hκ, hrep⟩ := ih (fun i => c (Fin.castSucc i)) (fun i => hc _)
    have hinit : Continuous (fun t : Fin (N + 1) → ℝ => Fin.init t) :=
      continuous_pi fun i => continuous_apply (Fin.castSucc i)
    refine ⟨J × Bool, inferInstance,
      fun p t => κ p.1 (Fin.init t) * (if p.2 then ((1 / s : ℝ) : ℂ)
        else -(((s - t (Fin.last N)) / s : ℝ) : ℂ)),
      fun p => if p.2 then (l p.1).map Fin.castSucc else Fin.last N :: (l p.1).map Fin.castSucc,
      ?_, ?_⟩
    · rintro ⟨j, _ | _⟩
      · simp only [Bool.false_eq_true, if_false]
        exact ((hκ j).comp hinit).mul (by fun_prop)
      · simp only [if_true]
        exact ((hκ j).comp hinit).mul continuous_const
    intro d S hS v hv
    have hS' : ∀ v ∈ S, ∀ i : Fin N, d (Fin.castSucc i) v ∈ S ∧
        HasDerivAt (fun t : ℝ => ρ (c (Fin.castSucc i) t) v) (d (Fin.castSucc i) v) 0 :=
      fun v hv i => hS v hv _
    have h1 := hrep (fun i => d (Fin.castSucc i)) S hS' v hv
    have hmem : ∀ l' : List (Fin N), l'.foldr (fun i => d (Fin.castSucc i)) v ∈ S := by
      intro l'
      induction l' with
      | nil => exact hv
      | cons a l' ihl => exact (hS _ ihl _).1
    have hfold : ∀ l' : List (Fin N),
        (l'.map Fin.castSucc).foldr d v = l'.foldr (fun i => d (Fin.castSucc i)) v := by
      intro l'
      rw [List.foldr_map]
    have hPc : ∀ x : K, Continuous fun t : Fin N → ℝ =>
        ρ (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod x := fun x =>
      (hcont x).comp (_root_.GlobalTheory.continuous_prod_ofFn_curves N _ fun i => (hc _).1)
    have hcF : ∀ (f : (Fin (N + 1) → ℝ) → ℂ) (x : K), Continuous f →
        Continuous fun t => f t • ρ (List.ofFn fun i => c i (t i)).prod x := fun f x hf =>
      hf.smul ((hcont x).comp (_root_.GlobalTheory.continuous_prod_ofFn_curves _ c fun i => (hc i).1))
    have hprod : ∀ (t : Fin N → ℝ) (r : ℝ),
        (List.ofFn fun i => c i ((Fin.snoc t r : Fin (N + 1) → ℝ) i)).prod =
          (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod * c (Fin.last N) r := by
      intro t r
      rw [List.ofFn_succ', List.prod_concat]
      simp
    rw [Fintype.sum_prod_type]
    refine h1.trans (Finset.sum_congr rfl fun j _ => ?_)
    simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, List.foldr_cons, hfold]
    rw [integral_cube_succ_eq_iterated N s _ (hcF (fun t => κ j (Fin.init t) * ((1 / s : ℝ) : ℂ)) _
        (((hκ j).comp hinit).mul continuous_const)),
      integral_cube_succ_eq_iterated N s _
        (hcF (fun t => κ j (Fin.init t) * -(((s - t (Fin.last N)) / s : ℝ) : ℂ)) _
        (((hκ j).comp hinit).mul (by fun_prop)))]
    simp only [Fin.init_snoc, Fin.snoc_last, hprod, map_mul, ContinuousLinearMap.mul_apply]
    set u := (l j).foldr (fun i => d (Fin.castSucc i)) v with hu_def
    have hu : u ∈ S := hmem _
    set cl := c (Fin.last N) with hcl
    have hA := eq_interval_average_sub_weighted_deriv ρ hcont hs cl (hc _).1 (hc _).2.1
      (hc _).2.2 u (d (Fin.last N) u) (hS u hu _).2
    have hI1 : IntegrableOn (fun r => ((1 / s : ℝ) : ℂ) • ρ (cl r) u) (Set.Icc 0 s) :=
      (continuous_const.smul ((hcont u).comp (hc _).1)).continuousOn.integrableOn_compact
        isCompact_Icc
    have hI2 : IntegrableOn (fun r => (((s - r) / s : ℝ) : ℂ) • ρ (cl r) (d (Fin.last N) u))
        (Set.Icc 0 s) :=
      ((Complex.continuous_ofReal.comp ((continuous_const.sub continuous_id).div_const s)).smul
        ((hcont _).comp (hc _).1)).continuousOn.integrableOn_compact isCompact_Icc
    have e1 : ∀ t : Fin N → ℝ, ∫ r in Set.Icc (0 : ℝ) s, (κ j t * ((1 / s : ℝ) : ℂ)) •
        ρ (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod (ρ (cl r) u) =
        κ j t • ρ (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod
          (∫ r in Set.Icc 0 s, ((1 / s : ℝ) : ℂ) • ρ (cl r) u) := by
      intro t
      rw [← ContinuousLinearMap.integral_comp_comm _ hI1, ← integral_smul]
      congr 1
      funext r
      rw [map_smul, smul_smul]
    have e2 : ∀ t : Fin N → ℝ, ∫ r in Set.Icc (0 : ℝ) s, (κ j t * -(((s - r) / s : ℝ) : ℂ)) •
        ρ (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod (ρ (cl r) (d (Fin.last N) u)) =
        -(κ j t • ρ (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod
          (∫ r in Set.Icc 0 s, (((s - r) / s : ℝ) : ℂ) • ρ (cl r) (d (Fin.last N) u))) := by
      intro t
      rw [← ContinuousLinearMap.integral_comp_comm _ hI2, ← integral_smul, ← integral_neg]
      congr 1
      funext r
      rw [map_smul, smul_smul, mul_neg, neg_smul]
    simp only [e1, e2]
    have hcube : IsCompact (Set.univ.pi fun _ : Fin N => Set.Icc (0 : ℝ) s) :=
      isCompact_univ_pi fun _ => isCompact_Icc
    have hi : ∀ x : K, IntegrableOn (fun t : Fin N → ℝ =>
        κ j t • ρ (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod x)
        (Set.univ.pi fun _ => Set.Icc (0 : ℝ) s) := fun x =>
      ((hκ j).smul (hPc x)).continuousOn.integrableOn_compact hcube
    rw [integral_neg, ← sub_eq_add_neg, ← integral_sub (hi _) (hi _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [← smul_sub, ← map_sub, ← hA]

end GlobalTheory.CubeTaylor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivalenceGeneratedTorusRel
section
open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls

noncomputable section
namespace GlobalTheory.UCls
open scoped TensorProduct
open IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem isKM_mul {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ}
    {k k' : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) (hk' : IsKM c G L M k') :
    IsKM c G L M (k * k') := by
  obtain ⟨⟨hd, hh⟩, h2, h3⟩ := hk
  obtain ⟨⟨hd', hh'⟩, h2', h3'⟩ := hk'
  refine ⟨⟨by rw [det_mul]; exact hd.mul hd', fun x y => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · rw [← mulVec_mulVec, ← mulVec_mulVec, hh, hh']
  · obtain ⟨y2, hy2, e2⟩ := h2' x hx
    have hx' : k' *ᵥ x ∈ hat F L := by
      have : k' *ᵥ x = x + M • y2 := by rw [← e2]; abel
      rw [this]; exact add_mem hx (nsmul_mem hy2 _)
    obtain ⟨y1, hy1, e1⟩ := h2 _ hx'
    refine ⟨y1 + y2, add_mem hy1 hy2, ?_⟩
    rw [← mulVec_mulVec, smul_add, ← e1, ← e2]; abel
  · obtain ⟨y1, hy1, e1⟩ := h3 x hx
    obtain ⟨y2, hy2, e2⟩ := h3' y1 hy1
    exact ⟨y2, hy2, by rw [← mulVec_mulVec, e2, e1]⟩

theorem isKM_inv {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ}
    {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) :
    IsKM c G L M k⁻¹ := by
  obtain ⟨⟨hd, hh⟩, h2, h3⟩ := hk
  have hkk : k * k⁻¹ = 1 := mul_nonsing_inv k hd
  have hkk' : k⁻¹ * k = 1 := nonsing_inv_mul k hd
  have hmem : ∀ x ∈ hat F L, k *ᵥ x ∈ hat F L := by
    intro x hx
    obtain ⟨y, hy, e⟩ := h2 x hx
    have : k *ᵥ x = x + M • y := by rw [← e]; abel
    rw [this]; exact add_mem hx (nsmul_mem hy _)
  refine ⟨⟨?_, fun x y => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · rw [det_nonsing_inv]; exact hd.ringInverse
  · rw [← hh, mulVec_mulVec, mulVec_mulVec, hkk, one_mulVec, one_mulVec]
  · obtain ⟨y, hy, e⟩ := h3 x hx
    obtain ⟨z, hz, ez⟩ := h2 y hy
    refine ⟨-z, neg_mem hz, ?_⟩
    have : k⁻¹ *ᵥ x = y := by rw [← e, mulVec_mulVec, hkk', one_mulVec]
    rw [this, ← e, smul_neg, ← ez]; abel
  · exact ⟨k *ᵥ x, hmem x hx, by rw [mulVec_mulVec, hkk', one_mulVec]⟩

theorem tEquiv_refl (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ) (t : RA F E) :
    TEquiv c G L M t t :=
  ⟨1, by simp, 1, isKM_one c G L M, by simp [Algebra.TensorProduct.one_def.symm]⟩

theorem tEquiv_symm {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ} {t t' : RA F E}
    (h : TEquiv c G L M t t') : TEquiv c G L M t' t := by
  obtain ⟨u, hu, k, hk, rfl⟩ := h
  have hu0 : u ≠ 0 := left_ne_zero_of_mul_eq_one hu
  refine ⟨u⁻¹, by rw [map_inv₀, ← mul_inv, hu, inv_one], k⁻¹, isKM_inv hk, ?_⟩
  have hd : IsUnit k.det := hk.1.1
  have e1 : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u⁻¹) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hu0, Algebra.TensorProduct.one_def]
  have e2 : k.det * k⁻¹.det = 1 := by rw [det_nonsing_inv, Ring.mul_inverse_cancel _ hd]
  calc t = (((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u⁻¹) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u)) * t * (k.det * k⁻¹.det) := by
        rw [e1, e2, one_mul, mul_one]
    _ = _ := by ring

theorem tEquiv_trans {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ} {t t' t'' : RA F E}
    (h : TEquiv c G L M t t') (h' : TEquiv c G L M t' t'') : TEquiv c G L M t t'' := by
  obtain ⟨u, hu, k, hk, rfl⟩ := h
  obtain ⟨u', hu', k', hk', rfl⟩ := h'
  refine ⟨u' * u, ?_, k * k', isKM_mul hk hk', ?_⟩
  · rw [map_mul]
    calc u' * u * (c u' * c u) = (u' * c u') * (u * c u) := by ring
      _ = 1 := by rw [hu, hu', one_mul]
  · have e : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (u' * u)) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u') * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [det_mul, e]; ring

theorem tEquiv_of_eqvGen {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ}
    (a b : {t : RA F E // IsTA c t})
    (h : Relation.EqvGen (fun a b : {t : RA F E // IsTA c t} => TEquiv c G L M a.1 b.1) a b) :
    TEquiv c G L M a.1 b.1 :=
  (Equivalence.eqvGen_iff (r := fun a b : {t : RA F E // IsTA c t} => TEquiv c G L M a.1 b.1)
    ⟨fun a => tEquiv_refl c G L M a.1, fun h => tEquiv_symm h, fun h h' => tEquiv_trans h h'⟩).1 h

end GlobalTheory.UCls
end

theorem GlobalTheory.UCls.torus_eqvGen_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t}), Relation.EqvGen (fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} => TEquiv (IsCMField.complexConj E) G L M a.1 b.1) a b → TEquiv (IsCMField.complexConj E) G L M a.1 b.1 :=
  by intro E _ _ _ r M G L a b h; exact GlobalTheory.UCls.tEquiv_of_eqvGen a b h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAwayQuotientEqLocalization
section
namespace GlobalTheory

theorem etale_away_quotient_eq_localization :
    ∀ (B D : Type) [CommRing B] [IsDedekindDomain B] [CommRing D] [Algebra B D] [Algebra.Etale B D]
      (f : B), f ≠ 0 → ∀ (P : Ideal B), P.IsMaximal → f ∈ P → ∀ (Q : Ideal D), Q.IsPrime →
      Q.comap (algebraMap B D) = P → (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) →
      ∃ g : D, (∀ a : Localization.Away g, ∃ b : B,
          a - algebraMap B (Localization.Away g) b ∈
            Ideal.span {algebraMap B (Localization.Away g) f}) ∧
        ∀ b : B, algebraMap B (Localization.Away g) b ∈
            Ideal.span {algebraMap B (Localization.Away g) f} ↔
          ∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f} := by
  intro B D _ _ _ _ _ f hf P hP hfP Q hQ hQP hres

  have hQmax : Q.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨fun h1 => ?_, fun J x hQJ hx hxJ => ?_⟩
    · have : (1 : B) ∈ Q.comap (algebraMap B D) := by simpa using h1
      rw [hQP] at this
      exact hP.ne_top ((Ideal.eq_top_iff_one _).2 this)
    · obtain ⟨b, hb⟩ := hres x
      have hbP : b ∉ P := by
        intro hbP
        apply hx
        have : algebraMap B D b ∈ Q := by
          rw [← Ideal.mem_comap, hQP]; exact hbP
        simpa using Q.add_mem hb this
      obtain ⟨c, hc⟩ : ∃ c : B, c * b - 1 ∈ P := by
        obtain ⟨c, i, hi, hci⟩ := hP.exists_inv hbP
        refine ⟨c, ?_⟩
        have : c * b - 1 = -i := by rw [← hci]; ring
        rw [this]; exact P.neg_mem hi
      have h1 : algebraMap B D (c * b - 1) ∈ Q := by
        rw [← Ideal.mem_comap, hQP]; exact hc
      have h2 : algebraMap B D c * x - 1 ∈ Q := by
        have : algebraMap B D c * x - 1 =
            algebraMap B D c * (x - algebraMap B D b) + algebraMap B D (c * b - 1) := by
          simp only [map_sub, map_mul, map_one]; ring
        rw [this]
        exact Q.add_mem (Q.mul_mem_left _ hb) h1
      have h3 : algebraMap B D c * x ∈ J := J.mul_mem_left _ hxJ
      have : (1 : D) = algebraMap B D c * x - (algebraMap B D c * x - 1) := by ring
      rw [this]
      exact J.sub_mem h3 (hQJ h2)
  obtain ⟨g, hgQ, hQ'⟩ := GlobalTheory.T.isolate_maximal_among_primes_containing_etale B D f hf Q hQmax
  refine ⟨g, ?_⟩
  haveI : Algebra.Etale D (Localization.Away g) := Algebra.Etale.of_isLocalizationAway g
  haveI : Algebra.Etale B (Localization.Away g) := Algebra.Etale.comp B D (Localization.Away g)
  have hφ : ∀ b : B, algebraMap B (Localization.Away g) b =
      algebraMap D (Localization.Away g) (algebraMap B D b) := fun b =>
    IsScalarTower.algebraMap_apply B D (Localization.Away g) b

  have hunit := GlobalTheory.T.localization_inverse_mod_f B D f P Q g hQP hQ'

  have hker : ∀ b : B, (∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f}) →
      algebraMap B (Localization.Away g) b ∈
        Ideal.span {algebraMap B (Localization.Away g) f} := by
    rintro b ⟨s, hs, hsb⟩
    obtain ⟨t, ht⟩ := hunit s hs
    have h1 : algebraMap B (Localization.Away g) (s * b) ∈
        Ideal.span {algebraMap B (Localization.Away g) f} := by
      rw [Ideal.mem_span_singleton] at hsb ⊢
      obtain ⟨c, hc⟩ := hsb
      exact ⟨algebraMap B _ c, by rw [hc, map_mul]⟩
    have : algebraMap B (Localization.Away g) b = algebraMap B _ (s * b) * t -
        (algebraMap B _ s * t - 1) * algebraMap B (Localization.Away g) b := by
      rw [map_mul]; ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_right _ _ ht)
  refine ⟨?_, fun b => ⟨fun hb => ?_, hker b⟩⟩
  ·
    obtain ⟨N, hN⟩ := GlobalTheory.T.dedekind_power_localization B f hf P hP
    have hPN : (P ^ N).map (algebraMap B (Localization.Away g)) ≤
        Ideal.span {algebraMap B (Localization.Away g) f} := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      exact hker b (hN b hb)
    have hfib : ∀ Q' : Ideal (Localization.Away g), Q'.IsPrime →
        P.map (algebraMap B (Localization.Away g)) ≤ Q' →
        Q' = Q.map (algebraMap D (Localization.Away g)) := by
      intro Q' hQ'p hPQ'
      have hc : Q'.comap (algebraMap D (Localization.Away g)) = Q := by
        apply hQ' _ (Ideal.comap_isPrime _ _)
        · rw [Ideal.mem_comap, ← hφ]
          exact hPQ' (Ideal.mem_map_of_mem _ hfP)
        · intro hg
          rw [Ideal.mem_comap] at hg
          exact hQ'p.ne_top (Ideal.eq_top_of_isUnit_mem _ hg
            (IsLocalization.Away.algebraMap_isUnit g))
      rw [← hc]
      exact (IsLocalization.map_under (Submonoid.powers g) (Localization.Away g) Q').symm
    have hle := GlobalTheory.T.etale_unique_prime_le_map_maximal B (Localization.Away g) P hP
      (Q.map (algebraMap D (Localization.Away g))) hfib
    have hres' := GlobalTheory.T.localization_residue_approximation B D P hP Q g hgQ hQP hres
    refine GlobalTheory.T.nilpotent_approximation_surjective B (Localization.Away g) P _ N (fun a => ?_) hPN
    obtain ⟨b, hb⟩ := hres' a
    exact ⟨b, Ideal.mem_sup_left (hle hb)⟩
  ·
    have hgu : IsUnit (algebraMap D (Localization.AtPrime Q) g) :=
      IsLocalization.map_units (Localization.AtPrime Q) (⟨g, hgQ⟩ : Q.primeCompl)
    let ρ : Localization.Away g →+* Localization.AtPrime Q := IsLocalization.Away.lift g hgu
    have hρ : ∀ d : D, ρ (algebraMap D (Localization.Away g) d) =
        algebraMap D (Localization.AtPrime Q) d :=
      fun d => IsLocalization.Away.lift_eq g hgu d
    have e : ∀ x : B, algebraMap B (Localization.AtPrime Q) x =
        ρ (algebraMap B (Localization.Away g) x) := by
      intro x
      rw [hφ, hρ, IsScalarTower.algebraMap_apply B D (Localization.AtPrime Q)]
    have hloc : algebraMap B (Localization.AtPrime Q) b ∈
        Ideal.span {algebraMap B (Localization.AtPrime Q) f} := by
      rw [Ideal.mem_span_singleton] at hb ⊢
      obtain ⟨c, hc⟩ := hb
      exact ⟨ρ c, by rw [e, e, hc, map_mul]⟩
    obtain ⟨s, hs, hsb⟩ := GlobalTheory.T.flat_localization_membership B D Q f b hloc
    rw [hQP] at hs
    exact ⟨s, hs, hsb⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationOfInjectiveCokernelKilled
section
open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

theorem etale_localization_of_cokernel_killed (S : Type) [CommRing S] (A B : Type) [CommRing A]
    [CommRing B] [Algebra S A] [Algebra S B] (ι : A →ₐ[S] B) (hι : Function.Injective ι)
    (p : Ideal S) [p.IsPrime] (s : S) (hs : s ∉ p) (hB : ∀ y : B, s • y ∈ ι.range)
    (hA : Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A)) :
    Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) B) := by
  let Φ : TensorProduct S (Localization.AtPrime p) A →ₐ[Localization.AtPrime p]
      TensorProduct S (Localization.AtPrime p) B :=
    Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ι
  have inj : Function.Injective Φ :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := Localization.AtPrime p)
      (ι.toLinearMap.restrictScalars S) hι
  have hu : IsUnit (algebraMap S (Localization.AtPrime p) s) :=
    IsLocalization.map_units (Localization.AtPrime p) (⟨s, hs⟩ : p.primeCompl)
  obtain ⟨u, hu'⟩ := hu
  have surj : Function.Surjective Φ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul r y =>
      obtain ⟨a, ha⟩ := hB y
      refine ⟨(r * ↑u⁻¹) ⊗ₜ a, ?_⟩
      simp only [Φ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rw [show ι a = s • y from ha, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.smul_def, ← hu', mul_left_comm, Units.mul_inv, mul_one]
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩
  exact Algebra.Etale.of_equiv (AlgEquiv.ofBijective Φ ⟨inj, surj⟩)

end GlobalTheory
end

