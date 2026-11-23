module

public import Mathlib
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
public import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
public import GroundTheory.AutomorphicForms.Bundle0015
public import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0121
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0396
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0390
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0382
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0386

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSobolevRepresentationProdExp
section
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory
namespace SobolevRep

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

theorem prodExp_succ {d : ℕ} (X : Fin (d + 1) → 𝔤) (t : Fin (d + 1) → ℝ) :
    h.prodExp X t = h.expG (t 0 • X 0) * h.prodExp (Fin.tail X) (Fin.tail t) := by
  simp [IsExpLieAlgebra.prodExp, List.ofFn_succ, Fin.tail]

theorem continuous_prodExp' {d : ℕ} (X : Fin d → 𝔤) : Continuous (h.prodExp X) := by
  have : h.prodExp X = fun t => (h.revProdExp X (-t))⁻¹ := by
    funext t; rw [h.revProdExp_inv, neg_neg]
  rw [this]
  exact ((h.continuous_revProdExp X).comp continuous_neg).inv

theorem isSmoothFun_foldr {f : G → ℂ} (hf : h.IsSmoothFun f) :
    ∀ l : List 𝔤, h.IsSmoothFun (l.foldr h.rightDeriv f)
  | [] => hf
  | X :: l => h.isSmoothFun_rightDeriv (isSmoothFun_foldr hf l) X

theorem continuous_of_isSmoothFun {f : G → ℂ} (hf : h.IsSmoothFun f) : Continuous f := by
  letI := h.chartedSpace
  exact ContMDiff.continuous hf

theorem integral_cons {d : ℕ} (X : Fin (d + 1) → 𝔤) {ε : ℝ} (hε : 0 ≤ ε) {a : ℝ → ℂ}
    (ha : Continuous a) (has : tsupport a ⊆ Set.Icc (-ε) ε) {K : (Fin d → ℝ) → ℂ}
    (hK : Continuous K) (hKs : tsupport K ⊆ Metric.closedBall 0 ε) {F : G → ℂ}
    (hF : Continuous F) (x : G) :
    ∫ t, a (t 0) * K (Fin.tail t) * F (x * h.prodExp X t) =
      ∫ s, ∫ t', a s * (K t' * F (x * h.expG (s • X 0) * h.prodExp (Fin.tail X) t')) := by
  have hint : Integrable
      (fun t : Fin (d + 1) → ℝ => a (t 0) * K (Fin.tail t) * F (x * h.prodExp X t)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((ha.comp (continuous_apply 0)).mul
        (hK.comp (continuous_pi fun j => continuous_apply j.succ))).mul
        (hF.comp (continuous_const.mul (continuous_prodExp' h X)))
    · exact HasCompactSupport.mul_right (f := fun t : Fin (d + 1) → ℝ => a (t 0) * K (Fin.tail t))
        ((isCompact_closedBall 0 ε).of_isClosed_subset (isClosed_tsupport _)
          (tsupport_cons_kernel hε has hKs))
  rw [integral_fin_succ_cons hint]
  congr 1; funext s; congr 1; funext t'
  simp only [Fin.cons_zero, Fin.tail_cons, prodExp_succ h, mul_assoc]

theorem integrable_integral_cons {d : ℕ} (X : Fin (d + 1) → 𝔤) {ε : ℝ} {a : ℝ → ℂ}
    (ha : Continuous a) (has : tsupport a ⊆ Set.Icc (-ε) ε) {K : (Fin d → ℝ) → ℂ}
    (hK : Continuous K) (hKs : tsupport K ⊆ Metric.closedBall 0 ε) {F : G → ℂ}
    (hF : Continuous F) (x : G) :
    Integrable (fun s : ℝ =>
      ∫ t', a s * (K t' * F (x * h.expG (s • X 0) * h.prodExp (Fin.tail X) t'))) := by
  have hc : Continuous (fun p : ℝ × (Fin d → ℝ) =>
      a p.1 * (K p.2 * F (x * h.expG (p.1 • X 0) * h.prodExp (Fin.tail X) p.2))) :=
    (ha.comp continuous_fst).mul ((hK.comp continuous_snd).mul (hF.comp
      ((continuous_const.mul (h.continuous_expG.comp (continuous_fst.smul continuous_const))).mul
        ((continuous_prodExp' h (Fin.tail X)).comp continuous_snd))))
  have hs : HasCompactSupport (fun p : ℝ × (Fin d → ℝ) =>
      a p.1 * (K p.2 * F (x * h.expG (p.1 • X 0) * h.prodExp (Fin.tail X) p.2))) := by
    refine HasCompactSupport.intro
      ((isCompact_Icc (a := -ε) (b := ε)).prod (isCompact_closedBall (0 : Fin d → ℝ) ε)) ?_
    intro p hp
    rw [Set.mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · rw [image_eq_zero_of_notMem_tsupport (fun h' => hp (has h')), zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport (fun h' => hp (hKs h')), zero_mul, mul_zero]
  exact (hc.integrable_of_hasCompactSupport hs).integral_prod_left

theorem sum_integral_cons {d m : ℕ} (X : Fin (d + 1) → 𝔤) {ε : ℝ} (hε : 0 ≤ ε)
    {a : ℝ → ℂ} (ha : Continuous a) (has : tsupport a ⊆ Set.Icc (-ε) ε)
    {K : Fin m → (Fin d → ℝ) → ℂ} (hK : ∀ i, Continuous (K i))
    (hKs : ∀ i, tsupport (K i) ⊆ Metric.closedBall 0 ε) {F : Fin m → G → ℂ}
    (hF : ∀ i, Continuous (F i)) {f₁ : G → ℂ}
    (hd : ∀ y, f₁ y = ∑ i, ∫ t', K i t' * F i (y * h.prodExp (Fin.tail X) t')) (x : G) :
    ∑ i, ∫ t, a (t 0) * K i (Fin.tail t) * F i (x * h.prodExp X t) =
      ∫ s, a s * f₁ (x * h.expG (s • X 0)) := by
  rw [Finset.sum_congr rfl fun i _ => integral_cons h X hε ha has (hK i) (hKs i) (hF i) x,
    ← integral_finsetSum _ fun i _ =>
      integrable_integral_cons h X ha has (hK i) (hKs i) (hF i) x]
  congr 1; funext s
  rw [hd, Finset.mul_sum]
  congr 1; funext i
  rw [← integral_const_mul]

theorem exists_rep {ε : ℝ} (hε : 0 < ε) : ∀ (n : ℕ) (X : Fin n → 𝔤),
    ∃ (N : ℕ) (l : Fin N → List 𝔤) (κ : Fin N → (Fin n → ℝ) → ℂ),
      (∀ i, Continuous (κ i) ∧ tsupport (κ i) ⊆ Metric.closedBall 0 ε) ∧
      ∀ f : G → ℂ, h.IsSmoothFun f → ∀ g,
        f g = ∑ i, ∫ t, κ i t * (l i).foldr h.rightDeriv f (g * h.prodExp X t) := by
  intro n
  induction n with
  | zero =>
    intro X
    refine ⟨1, fun _ => [], fun _ _ => 1, fun _ => ⟨continuous_const, ?_⟩, fun f _ g => ?_⟩
    · intro t _
      rw [Subsingleton.elim t 0]; exact Metric.mem_closedBall_self hε.le
    · have hv : (volume : Measure (Fin 0 → ℝ)).real Set.univ = 1 := by
        simp [Measure.real, MeasureTheory.volume_pi]
      simp [IsExpLieAlgebra.prodExp, hv]
  | succ d ih =>
    intro X
    obtain ⟨N, l, K, hK, hrep⟩ := ih (Fin.tail X)
    obtain ⟨a, ha, hu⟩ := _root_.GlobalTheory.value_at_zero_eq_sum_integral_kernel_iteratedDeriv ε hε
    refine ⟨3 * N,
      fun j => l (finProdFinEquiv.symm j).2 ++ List.replicate (finProdFinEquiv.symm j).1 (X 0),
      fun j t => a (finProdFinEquiv.symm j).1 (t 0) * K (finProdFinEquiv.symm j).2 (Fin.tail t),
      fun j => ⟨?_, tsupport_cons_kernel hε.le (ha _).2 (hK _).2⟩, fun f hf g => ?_⟩
    · exact ((ha _).1.comp (continuous_apply 0)).mul
        ((hK _).1.comp (continuous_pi fun j => continuous_apply j.succ))
    · rw [← finProdFinEquiv.sum_comp]
      simp only [Equiv.symm_apply_apply, List.foldr_append]
      rw [Fintype.sum_prod_type]
      have h0 := hu _ (_root_.GlobalTheory.iteratedDeriv_expG_line_eq_rightDeriv_pow 𝔸 G 𝔤 h f hf (X 0) g 0).1
      simp only [zero_smul, h.expG_zero, mul_one] at h0
      rw [h0]
      refine Finset.sum_congr rfl fun p _ => ?_
      have hp := isSmoothFun_foldr h hf (List.replicate p (X 0))
      rw [sum_integral_cons h X hε.le (ha p).1 (ha p).2 (fun i => (hK i).1) (fun i => (hK i).2)
        (fun i => continuous_of_isSmoothFun h (isSmoothFun_foldr h hp (l i))) (hrep _ hp) g]
      congr 1; funext s
      rw [(_root_.GlobalTheory.iteratedDeriv_expG_line_eq_rightDeriv_pow 𝔸 G 𝔤 h f hf (X 0) g p).2 s]

end SobolevRep

theorem exists_sobolev_representation_prodExp :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
      (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (ε : ℝ), 0 < ε →
      ∀ (n : ℕ) (X : Fin n → 𝔤),
      ∃ (N : ℕ) (l : Fin N → List 𝔤) (κ : Fin N → (Fin n → ℝ) → ℂ),
        (∀ i, Continuous (κ i) ∧ tsupport (κ i) ⊆ Metric.closedBall 0 ε) ∧
        ∀ f : G → ℂ, h.IsSmoothFun f → ∀ g,
          f g = ∑ i, ∫ t, κ i t * (l i).foldr h.rightDeriv f (g * h.prodExp X t) :=
  fun _ _ _ _ _ _ _ h _ hε n X => SobolevRep.exists_rep h hε n X

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTypicalCurveBasisAdaptedToSaturatedFrame
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem det_eq_det_minor_of_unit_rows {K : Type} [CommRing K] {i d : ℕ} (r : Fin i → Fin d)
    (hr : Function.Injective r) (M : Matrix (Fin d) (Fin d) K)
    (hM : ∀ e, e ∉ Set.range r → ∀ c, M e c = if c = e then 1 else 0) :
    M.det = (M.submatrix r r).det := by
  classical
  let E : Fin i ⊕ {e // e ∉ Set.range r} ≃ Fin d :=
    (Equiv.sumCongr (Equiv.ofInjective r hr) (Equiv.refl _)).trans
      (Equiv.sumCompl (fun e => e ∈ Set.range r))
  have hEl : ∀ a, E (Sum.inl a) = r a := fun a => rfl
  have hEr : ∀ e, E (Sum.inr e) = e.1 := fun e => rfl
  rw [← Matrix.det_submatrix_equiv_self E M, ← Matrix.fromBlocks_toBlocks (M.submatrix E E)]
  have h21 : (M.submatrix E E).toBlocks₂₁ = 0 := by
    ext e b
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, Matrix.zero_apply, hEl, hEr]
    rw [hM e.1 e.2, if_neg]
    rintro h
    exact e.2 ⟨b, h⟩
  have h22 : (M.submatrix E E).toBlocks₂₂ = 1 := by
    ext e e'
    simp only [Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.submatrix_apply, hEr, Matrix.one_apply]
    rw [hM e.1 e.2]
    by_cases hee : e = e'
    · subst hee; simp
    · rw [if_neg (fun h => hee (Subtype.ext h).symm), if_neg hee]
  have h11 : (M.submatrix E E).toBlocks₁₁ = M.submatrix r r := by
    ext a b
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply, hEl]
  rw [h21, Matrix.det_fromBlocks_zero₂₁, h22, Matrix.det_one, mul_one, h11]

end GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem exists_basis_adapted_frame : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (d h : ℕ), 0 < h →
    ∀ (ty : Fin d → ZMod h) (G : LogFGL v d), MuAction G p h ty → ∀ (τ : ZMod h) (j i : ℕ),
    (Finset.univ.filter fun a => ty a = τ + 1).card ≤ j → ∀ u : Fin i → Fin d → C,
    IsSatFrame v u → (∀ a e, ty e ≠ τ → u a e = 0) →
    ∃ (γ : Fin d → Fin d → PowerSeries C) (r : Fin i ↪ Fin d) (g : Matrix (Fin i) (Fin i) C),
      IsBasis G p ty γ ∧ (∀ a b, IsIntV v (g a b)) ∧ v g.det = 0 ∧
      (∀ a, tangent (γ (r a)) = ∑ a', g a a' • u a') ∧
      ∀ a : Fin i, j ≤ a.val → G.lc p (γ (r a)) 1 = 0 := by
  intro C _ _ _ v p hp hv d h hh ty G hmu τ j i hj u hu hut
  classical
  obtain ⟨hPT2, -⟩ := _root_.GlobalTheory.TypicalCurveBases.typical_curves_tangent_and_bases
  choose η hηc hηt hηtan using fun a : Fin i =>
    hPT2 C v p hp hv d h hh ty G hmu τ (u a) (hu.1 a) (hut a)
  have hspan : Module.finrank C (Submodule.span C (Set.range fun a =>
      (LinearMap.id : (Fin d → C) →ₗ[C] (Fin d → C)) (G.lc p (η a) 1))) ≤ j := by
    let W := Submodule.span C
      (Set.range fun e : {e : Fin d // ty e = τ + 1} => (Pi.single e.1 (1 : C) : Fin d → C))
    have hle : Submodule.span C (Set.range fun a =>
        (LinearMap.id : (Fin d → C) →ₗ[C] (Fin d → C)) (G.lc p (η a) 1)) ≤ W := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      show G.lc p (η a) 1 ∈ W
      rw [← Finset.univ_sum_single (G.lc p (η a) 1)]
      refine Submodule.sum_mem _ fun e _ => ?_
      by_cases he : ty e = τ + 1
      · have : (Pi.single e (G.lc p (η a) 1 e) : Fin d → C) =
            G.lc p (η a) 1 e • (Pi.single e (1 : C) : Fin d → C) := by
          ext c; simp [Pi.single_apply]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨e, he⟩, rfl⟩)
      · rw [(hηt a).2 1 e (by simpa using he), Pi.single_zero]
        exact Submodule.zero_mem _
    calc _ ≤ Module.finrank C W := Submodule.finrank_mono hle
      _ ≤ Fintype.card {e : Fin d // ty e = τ + 1} := finrank_range_le_card _
      _ = _ := Fintype.card_subtype _
      _ ≤ j := hj
  obtain ⟨x, hxi, hxd, hxt, hxty, hxl⟩ := _root_.GlobalTheory.RootTrick.root_statement C v p hp hv d h i ty τ G η
    (fun a => hηc a) (fun a => hηt a) 1 j le_rfl (Fin d → C) LinearMap.id hspan
  set γ' : Fin i → Fin d → PowerSeries C :=
    fun w => G.sumF fun u => rescaleCurve (x w u) (η u) with hγ'
  have hγ'c : ∀ w, IsCurve v (γ' w) := fun w =>
    (pt6' C v p hp hv d i G η (x w) (fun a => hηc a) (fun a => hxi w a)).1
  obtain ⟨r0, hr0⟩ := hu.2
  set U : Matrix (Fin i) (Fin i) C := Matrix.of fun a b => u a (r0 b) with hU
  have hUne : U.det ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hr0
    exact WithTop.top_ne_zero hr0
  have hinj : Function.Injective r0 := by
    intro b1 b2 heq
    by_contra hne
    exact hUne (Matrix.det_zero_of_column_eq hne (fun a => by simp [hU, heq]))
  have hty0 : ∀ b, ty (r0 b) = τ := by
    intro b
    by_contra hne
    exact hUne (Matrix.det_eq_zero_of_column_eq_zero b (fun a => by simp [hU, hut a _ hne]))
  choose ζ hζc hζt hζtan using fun e : Fin d =>
    hPT2 C v p hp hv d h hh ty G hmu (ty e) (Pi.single e 1)
      (fun c => by
        unfold IsIntV
        by_cases hc : c = e
        · subst hc; simp
        · simp [Pi.single_apply, hc])
      (fun c hc => by
        have : c ≠ e := fun h' => hc (h' ▸ rfl)
        simp [Pi.single_apply, this])
  let γ : Fin d → Fin d → PowerSeries C := fun e =>
    if hm : e ∈ Set.range r0 then γ' ((Equiv.ofInjective r0 hinj).symm ⟨e, hm⟩) else ζ e
  have hγr : ∀ a, γ (r0 a) = γ' a := by
    intro a
    simp only [γ, dif_pos (Set.mem_range_self a)]
    rw [Equiv.ofInjective_symm_apply]
  have hγn : ∀ e, e ∉ Set.range r0 → γ e = ζ e := fun e he => by simp only [γ, dif_neg he]
  have htan : ∀ a, tangent (γ (r0 a)) = ∑ a', x a a' • u a' := by
    intro a
    rw [hγr, hxt a]
    simp only [hηtan]
  refine ⟨γ, ⟨r0, hinj⟩, x, ⟨fun e => ?_, fun e => ?_, ?_⟩, hxi, hxd, htan, fun a ha => ?_⟩
  · by_cases he : e ∈ Set.range r0
    · obtain ⟨b, rfl⟩ := he
      rw [hγr]; exact hγ'c b
    · rw [hγn e he]; exact hζc e
  · by_cases he : e ∈ Set.range r0
    · obtain ⟨b, rfl⟩ := he
      rw [hγr, hty0]; exact hxty b
    · rw [hγn e he]; exact hζt e
  · rw [det_eq_det_minor_of_unit_rows r0 hinj]
    · have hsub : (Matrix.of fun a b => tangent (γ a) b).submatrix r0 r0 = x * U := by
        ext a b
        simp only [Matrix.submatrix_apply, Matrix.of_apply, htan, Matrix.mul_apply, hU,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [hsub, Matrix.det_mul, AddValuation.map_mul, hxd, hr0, add_zero]
    · intro e he c
      simp only [Matrix.of_apply, hγn e he, hζtan, Pi.single_apply]
  · show G.lc p (γ (r0 a)) 1 = 0
    rw [hγr]
    simpa using hxl a ha

end GlobalTheory.FGDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitAnalyticFunction
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD

open Polynomial

theorem isIntegral_of_le {k F K : Type} [Field k] [Field F] [Field K] [Algebra k F] [Algebra F K]
    {A A' : Subalgebra k F} (h : A ≤ A') {y : K} (hy : IsIntegral A y) : IsIntegral A' y := by
  obtain ⟨p, hm, he⟩ := hy
  refine ⟨p.map (Subalgebra.inclusion h), hm.map _, ?_⟩
  rw [eval₂_map]
  exact he

theorem rA_mono (k : Type) [Field k] {F : Type} [Field F] [Algebra k F] {d : ℕ} (x : Fin (d + 1) → F)
    {I J : Finset (Fin (d + 1))} (h : I ⊆ J) : rA k x I ≤ rA k x J := by
  apply Algebra.adjoin_mono
  rintro y ⟨i, hi, j, rfl⟩
  exact ⟨i, h hi, j, rfl⟩

theorem rB_mono_loc : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K]
    [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x →
    ∀ (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I →
    (∀ J, I ⊆ J → rB k K x I ≤ rB k K x J) ∧
    ∀ y : K, y ∈ rB k K x I ↔ ∃ N : ℕ, y * algebraMap F K (∏ j ∈ I, x j / x i) ^ N ∈ rB k K x {i} := by
  intro k _ _ F K _ _ _ _ _ _ d x hK I i hi
  have memB : ∀ (J : Finset (Fin (d + 1))) (y : K), y ∈ rB k K x J ↔ IsIntegral (rA k x J) y := fun J y => by
    rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  refine ⟨fun J hJ y hy => (memB J y).2 (isIntegral_of_le (rA_mono k x hJ) ((memB I y).1 hy)), fun y => ?_⟩
  set s : F := ∏ j ∈ I, x j / x i with hs
  have hsi : s ∈ rA k x {i} := Subalgebra.prod_mem _ fun j _ =>
    Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, j, rfl⟩
  have hsinv : s⁻¹ ∈ rA k x I := by
    rw [hs, ← Finset.prod_inv_distrib]
    refine Subalgebra.prod_mem _ fun j hj => ?_
    rw [inv_div]
    exact Algebra.subset_adjoin ⟨j, hj, i, rfl⟩
  have hsne : s ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => div_ne_zero (hK.pd.ne j) (hK.pd.ne i)
  have hiI : rA k x {i} ≤ rA k x I := rA_mono k x (Finset.singleton_subset_iff.2 hi)
  simp only [memB]
  constructor
  · rintro ⟨p, hm, he⟩
    have hc : ∀ m, ∃ N : ℕ, (p.coeff m : F) * s ^ N ∈ rA k x {i} := fun m =>
      (GlobalTheory.T.mem_standardOpenCoordinateRing_iff_localization_chart k F d x hK.pd I i hi (p.coeff m : F)).1 (p.coeff m).2
    choose Nf hNf using hc
    set N := (Finset.range (p.natDegree + 1)).sup Nf
    have hcN : ∀ m, (p.coeff m : F) * s ^ N ∈ rA k x {i} := by
      intro m
      by_cases hmd : m ≤ p.natDegree
      · have hle : Nf m ≤ N := Finset.le_sup (f := Nf) (Finset.mem_range.2 (Nat.lt_succ_of_le hmd))
        rw [← Nat.add_sub_cancel' hle, pow_add, ← mul_assoc]
        exact Subalgebra.mul_mem _ (hNf m) (Subalgebra.pow_mem _ hsi _)
      · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hmd)]
        simp
    set q : F[X] := (p.map (algebraMap (rA k x I) F)).scaleRoots (s ^ N)
    have hqm : q.Monic := (monic_scaleRoots_iff _).2 (hm.map _)
    have hdeg : (p.map (algebraMap (rA k x I) F)).natDegree = p.natDegree :=
      natDegree_map_eq_of_injective (fun a b h => Subtype.ext h) _
    have hl : q ∈ lifts (algebraMap (rA k x {i}) F) := by
      rw [lifts_iff_coeff_lifts]
      intro m
      rw [coeff_scaleRoots, coeff_map, hdeg]
      have hmem : (algebraMap (rA k x I) F (p.coeff m)) * (s ^ N) ^ (p.natDegree - m) ∈ rA k x {i} := by
        by_cases hmd : m < p.natDegree
        · obtain ⟨e, he'⟩ : ∃ e, p.natDegree - m = e + 1 := ⟨p.natDegree - m - 1, by omega⟩
          rw [he', pow_succ', ← mul_assoc]
          exact Subalgebra.mul_mem _ (hcN m) (Subalgebra.pow_mem _ (Subalgebra.pow_mem _ hsi _) _)
        · rw [Nat.sub_eq_zero_of_le (not_lt.1 hmd), pow_zero, mul_one]
          rcases (not_lt.1 hmd).eq_or_lt with h | h
          · rw [← h, hm.coeff_natDegree, map_one]
            exact Subalgebra.one_mem _
          · rw [coeff_eq_zero_of_natDegree_lt h, map_zero]
            exact Subalgebra.zero_mem _
      exact ⟨⟨_, hmem⟩, rfl⟩
    obtain ⟨q0, hq0, -, hq0m⟩ := lifts_and_natDegree_eq_and_monic hl hqm
    refine ⟨N, q0, hq0m, ?_⟩
    have h1 : eval₂ (algebraMap F K) y (p.map (algebraMap (rA k x I) F)) = 0 := by
      rw [eval₂_map]
      exact he
    have h2 : eval₂ (algebraMap F K) (algebraMap F K (s ^ N) * y) q = 0 :=
      scaleRoots_eval₂_eq_zero (algebraMap F K) (s := s ^ N) h1
    rw [← map_pow, mul_comm]
    rw [← hq0, eval₂_map] at h2
    exact h2
  · rintro ⟨N, hN⟩
    have h1 : IsIntegral (rA k x I) (y * algebraMap F K s ^ N) := isIntegral_of_le hiI hN
    have h2 : IsIntegral (rA k x I) (algebraMap F K s⁻¹ ^ N) := by
      have : IsIntegral (rA k x I) (algebraMap (rA k x I) K ⟨s⁻¹, hsinv⟩) := isIntegral_algebraMap
      exact this.pow N
    have h3 := h1.mul h2
    rwa [mul_assoc, ← mul_pow, ← map_mul, mul_inv_cancel₀ hsne, map_one, one_pow, mul_one] at h3

end GlobalTheory.PD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeCardOfVanish
section
open NumberField Matrix

namespace GlobalTheory.SylvesterInertia

theorem re_quad_eq_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian) (u : Fin n → ℂ) :
    (star u ⬝ᵥ M *ᵥ u).re = ∑ i, hM.eigenvalues i * Complex.normSq
      ((star (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ u) i) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hD : star U * M * U = diagonal (RCLike.ofReal ∘ hM.eigenvalues) := by
    have := hM.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_apply, hU] using this
  set y := star U *ᵥ u with hy
  have hu : u = U *ᵥ y := by
    rw [hy, mulVec_mulVec, hU, Matrix.mem_unitaryGroup_iff.mp hM.eigenvectorUnitary.2, one_mulVec]
  have h1 : star u ⬝ᵥ M *ᵥ u = star y ⬝ᵥ (star U * M * U) *ᵥ y := by
    conv_lhs => rw [hu]
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, star_eq_conjTranspose, Matrix.mul_assoc]
  rw [h1, hD, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal]
  simp only [Pi.star_apply, Function.comp_apply, Complex.star_def, Complex.normSq_apply, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
  have e1 : ((RCLike.ofReal (hM.eigenvalues i) : ℂ)).re = hM.eigenvalues i := by simp
  have e2 : ((RCLike.ofReal (hM.eigenvalues i) : ℂ)).im = 0 := by simp
  simp only [e1, e2]
  ring

theorem finrank_le_card_of_vanish {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (P : Submodule ℂ (Fin n → ℂ))
    (s : Fin n → Prop) [DecidablePred s]
    (h : ∀ u ∈ P, (∀ i, s i → (U *ᵥ u) i = 0) → u = 0) :
    Module.finrank ℂ P ≤ Fintype.card {i // s i} := by
  let f : P →ₗ[ℂ] ({i // s i} → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (Subtype.val : {i // s i} → Fin n)) ∘ₗ (Matrix.mulVecLin U) ∘ₗ P.subtype
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have := h u u.2 (fun i hi => by
      have := congrFun hu ⟨i, hi⟩
      simpa [f, LinearMap.funLeft_apply] using this)
    exact Subtype.ext this
  have := LinearMap.finrank_le_finrank_of_injective hf
  simpa using this

end GlobalTheory.SylvesterInertia
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierIntertwinesSiegelLeviOperatorStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_intertwines_siegelLeviOperator : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∀ p ∈ sieg c ν, ∀ q ∈ sieg c ν, weyl c ν * p = q * weyl c ν → ∀ φ : Matrix α ν E → ℂ, fou c ψ Q μ (parFun c ψ χ Q (mat c p) φ) = parFun c ψ χ Q (mat c q) (fou c ψ Q μ φ) := by
  first | exact @GlobalTheory.KSp.fou_parFun_levi | exact GlobalTheory.KSp.fou_parFun_levi | (intros; apply GlobalTheory.KSp.fou_parFun_levi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafSectionLocallyFiniteCombinationStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination : ∀ (R : Type) [CommRing R] (P : PSh) (U : Scheme.{0}), (∀ y : Sec ((free R).obj P) U, Loc U fun V g => ∃ c : P.obj (op V) →₀ ULift.{1} R, Sec.res g y = c.sum fun x r => r • freeGen R P V x) ∧ ∀ c : P.obj (op U) →₀ ULift.{1} R, (c.sum fun x r => r • freeGen R P U x) = 0 → Loc U fun _ g => Finsupp.mapDomain (P.map g.op) c = 0 := by
  first | (exact @GlobalTheory.EtC.free_sec_loc) | (exact GlobalTheory.EtC.free_sec_loc) | (intros; apply GlobalTheory.EtC.free_sec_loc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAWExistsUniqueBiadditiveEtaleStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
theorem _root_.GlobalTheory.T.isAW_existsUnique_biadditive_etale : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k), (∀ (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m), ∃! γ, μ.IsAW hk α β γ) ∧ (∀ α α' β γ γ', μ.IsAW (E := E) hk α β γ → μ.IsAW hk α' β γ' → μ.IsAW hk (α + α') β (γ + γ')) ∧ (∀ α β β' γ γ', μ.IsAW (E := E) hk α β γ → μ.IsAW hk α β' γ' → μ.IsAW hk α (β + β') (γ + γ')) := by
  first | exact @GlobalTheory.EtC.isAW_existsUnique_biadditive | exact GlobalTheory.EtC.isAW_existsUnique_biadditive | (intros; apply GlobalTheory.EtC.isAW_existsUnique_biadditive <;> assumption)
end

