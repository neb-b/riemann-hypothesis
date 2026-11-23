module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0112
public import Mathlib
public import GroundTheory.GlobalFields.TateThesis.Bundle0002
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0085
public import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0087

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdjoinRestrictedSectionsOfLocal
section
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.QcSub.Local

theorem adjoin_mem_of_away {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A']
    [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R']
    [IsLocalization.Away (algebraMap R A g) A'] (T : Set A) (b : A)
    (hb : algebraMap A A' b ∈ Algebra.adjoin R' (algebraMap A A' '' T)) :
    ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Algebra.adjoin R T := by
  classical
  have hgen : ∀ k : ℕ, algebraMap R A g ^ k ∈ Algebra.adjoin R T := fun k =>
    pow_mem (Subalgebra.algebraMap_mem _ g) k
  have hgA : algebraMap A A' (algebraMap R A g) = algebraMap R' A' (algebraMap R R' g) := by
    rw [← IsScalarTower.algebraMap_apply R A A', ← IsScalarTower.algebraMap_apply R R' A']
  have key : ∀ x ∈ Algebra.adjoin R' (algebraMap A A' '' T), ∃ m : ℕ, ∃ s ∈ Algebra.adjoin R T,
      algebraMap A A' (algebraMap R A g) ^ m * x = algebraMap A A' s := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨t, ht, rfl⟩ := hx
      exact ⟨0, t, Algebra.subset_adjoin ht, by simp⟩
    | algebraMap r =>
      obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers g) r
      refine ⟨n, algebraMap R A a, Subalgebra.algebraMap_mem _ a, ?_⟩
      have h2 := congrArg (algebraMap R' A') hr
      simp only [map_mul, map_pow] at h2
      rw [mul_comm, hgA, h2, ← IsScalarTower.algebraMap_apply R R' A',
        ← IsScalarTower.algebraMap_apply R A A']
    | add x y _ _ hx hy =>
      obtain ⟨m1, s1, hs1, e1⟩ := hx
      obtain ⟨m2, s2, hs2, e2⟩ := hy
      refine ⟨m1 + m2, algebraMap R A g ^ m2 * s1 + algebraMap R A g ^ m1 * s2,
        add_mem (mul_mem (hgen _) hs1) (mul_mem (hgen _) hs2), ?_⟩
      rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, ← e1, ← e2]
      ring
    | mul x y _ _ hx hy =>
      obtain ⟨m1, s1, hs1, e1⟩ := hx
      obtain ⟨m2, s2, hs2, e2⟩ := hy
      refine ⟨m1 + m2, s1 * s2, mul_mem hs1 hs2, ?_⟩
      rw [map_mul, ← e1, ← e2]
      ring
  obtain ⟨m, s, hs, hms⟩ := key _ hb
  rw [← map_pow, ← map_mul] at hms
  obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
    (IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap R A g)) A').mp hms
  refine ⟨k + m, ?_⟩
  have h3 : algebraMap R A g ^ (k + m) * b = algebraMap R A g ^ k * s := by
    rw [pow_add, mul_assoc]
    exact hk
  rw [h3]
  exact mul_mem (hgen k) hs

theorem mem_gen_of_local (X : Scheme.{0}) (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    (V W : X.Opens) (T : Set (F.obj (op V))) (b : F.obj (op W))
    (H : ∀ x ∈ W ⊓ V, ∃ D : X.Opens, IsAffineOpen D ∧ x ∈ D ∧ ∃ (hW : D ≤ W) (hV : D ≤ V),
      (F.map (homOfLE hW).op).hom b ∈ gen F α hV T)
    (W' : X.Opens) (hW' : IsAffineOpen W') (hW : W' ≤ W) (hV : W' ≤ V) :
    (F.map (homOfLE hW).op).hom b ∈ gen F α hV T := by
  classical
  let _ : Algebra Γ(X, W') (F.obj (op W')) := (α.app (op W')).hom.toAlgebra
  have comp : ∀ {U₁ U₂ U₃ : X.Opens} (h₁₂ : U₂ ≤ U₁) (h₂₃ : U₃ ≤ U₂) (y : F.obj (op U₁)),
      (F.map (homOfLE h₂₃).op).hom ((F.map (homOfLE h₁₂).op).hom y) =
        (F.map (homOfLE (h₂₃.trans h₁₂)).op).hom y := by
    intro U₁ U₂ U₃ h₁₂ h₂₃ y
    show (F.map (homOfLE h₁₂).op ≫ F.map (homOfLE h₂₃).op).hom y = _
    rw [← F.map_comp]
    rfl
  let b' := (F.map (homOfLE hW).op).hom b
  let T' : Set (F.obj (op W')) := (F.map (homOfLE hV).op).hom '' T
  let S := Algebra.adjoin Γ(X, W') T'
  let I : Ideal Γ(X, W') :=
    (Subalgebra.toSubmodule S).comap (LinearMap.toSpanSingleton Γ(X, W') (F.obj (op W')) b')
  have hI : ∀ r, r ∈ I ↔ (α.app (op W')).hom r * b' ∈ S := fun r => by
    simp only [I, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Subalgebra.mem_toSubmodule,
      Algebra.smul_def]
    rfl
  have key : ∀ (D : X.Opens) (f : Γ(X, W')) (hfD : X.basicOpen f ≤ D) (hDW : D ≤ W) (hDV : D ≤ V),
      (F.map (homOfLE hDW).op).hom b ∈ gen F α hDV T → f ∈ I.radical := by
    intro D f hfD hDW hDV hbD
    let _ : Algebra Γ(X, X.basicOpen f) (F.obj (op (X.basicOpen f))) :=
      (α.app (op (X.basicOpen f))).hom.toAlgebra
    let _ : Algebra (F.obj (op W')) (F.obj (op (X.basicOpen f))) :=
      (F.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
    let _ : Algebra Γ(X, W') (F.obj (op (X.basicOpen f))) :=
      ((F.map (homOfLE (X.basicOpen_le f)).op).hom.comp (α.app (op W')).hom).toAlgebra
    have : IsScalarTower Γ(X, W') (F.obj (op W')) (F.obj (op (X.basicOpen f))) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have : IsScalarTower Γ(X, W') Γ(X, X.basicOpen f) (F.obj (op (X.basicOpen f))) :=
      IsScalarTower.of_algebraMap_eq (fun x => by
        have h := congrArg (fun φ => φ.hom x) (α.naturality (homOfLE (X.basicOpen_le f)).op)
        exact h.symm)
    have : IsLocalization.Away f Γ(X, X.basicOpen f) := hW'.isLocalization_basicOpen f
    have : IsLocalization.Away (algebraMap Γ(X, W') (F.obj (op W')) f)
        (F.obj (op (X.basicOpen f))) := isLocalizationAway F α hα hW' f
    have hres := res_mem_gen_of_mem F α hDV hfD T hbD
    rw [gen_eq_adjoin] at hres
    have hb'' : algebraMap (F.obj (op W')) (F.obj (op (X.basicOpen f))) b' ∈
        Algebra.adjoin Γ(X, X.basicOpen f)
          (algebraMap (F.obj (op W')) (F.obj (op (X.basicOpen f))) '' T') := by
      have e1 : algebraMap (F.obj (op W')) (F.obj (op (X.basicOpen f))) b' =
          (F.map (homOfLE hfD).op).hom ((F.map (homOfLE hDW).op).hom b) :=
        (comp hW (X.basicOpen_le f) b).trans (comp hDW hfD b).symm
      have e2 : algebraMap (F.obj (op W')) (F.obj (op (X.basicOpen f))) '' T' =
          (F.map (homOfLE (hfD.trans hDV)).op).hom '' T := by
        simp only [T', Set.image_image]
        exact Set.image_congr (fun y _ => comp hV (X.basicOpen_le f) y)
      rw [e1, e2]
      exact hres
    obtain ⟨m, hm⟩ := adjoin_mem_of_away f T' b' hb''
    exact ⟨m, (hI _).mpr (by rw [map_pow]; exact hm)⟩
  have cover : W' ≤ ⨆ f : (I.radical : Set Γ(X, W')), X.basicOpen f.1 := by
    intro x hx
    rw [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨D, hD, hxD, hDW, hDV, hbD⟩ := H x (by exact ⟨hW hx, hV hx⟩)
    obtain ⟨f, hfD, hxf⟩ := hW'.exists_basicOpen_le (V := D) ⟨x, hxD⟩ hx
    exact ⟨⟨f, key D f hfD hDW hDV hbD⟩, hxf⟩
  have htop : I = ⊤ := by
    rw [← Ideal.radical_eq_top, ← Ideal.span_eq I.radical]
    exact (hW'.self_le_iSup_basicOpen_iff).mp cover
  have h1 : (1 : Γ(X, W')) ∈ I := htop ▸ Submodule.mem_top
  rw [hI, map_one, one_mul] at h1
  rw [gen_eq_adjoin]
  exact h1

end GlobalTheory.QcSub.Local
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureWideGaussianMulSchwartz
section
open FourierTransform MeasureTheory Filter Topology
open scoped ContDiff Nat SchwartzMap

noncomputable section

namespace GlobalTheory.GaussCutoff

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def cutErr (c : ℝ) (y : E) : ℂ := GroundTheory.Global.gaussianSchwartz E (c • y) - 1

theorem contDiff_cutErr (c : ℝ) : ContDiff ℝ ∞ (cutErr (E := E) c) :=
  (((GroundTheory.Global.gaussianSchwartz E).smooth ⊤).comp (contDiff_const_smul c)).sub contDiff_const

theorem norm_cutErr_le (c : ℝ) (y : E) : ‖cutErr c y‖ ≤ Real.pi * c ^ 2 * ‖y‖ ^ 2 := by
  unfold cutErr
  rw [GroundTheory.Global.gaussianSchwartz_apply]
  have hx : ‖c • y‖ ^ 2 = c ^ 2 * ‖y‖ ^ 2 := by rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [hx]
  set a := Real.pi * c ^ 2 * ‖y‖ ^ 2 with ha_def
  have ha : 0 ≤ a := by positivity
  have h1 : Real.exp (-Real.pi * (c ^ 2 * ‖y‖ ^ 2)) = Real.exp (-a) := by
    congr 1; rw [ha_def]; ring
  have he : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 ha)
  rw [h1, show ((Real.exp (-a) : ℝ) : ℂ) - 1 = ((Real.exp (-a) - 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  linarith [Real.add_one_le_exp (-a)]

theorem norm_iteratedFDeriv_cutErr_le (c : ℝ) {j : ℕ} (hj : j ≠ 0) (y : E) :
    ‖iteratedFDeriv ℝ j (cutErr c) y‖ ≤
      |c| ^ j * SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E) := by
  set g := GroundTheory.Global.gaussianSchwartz E with hg
  set L : E →L[ℝ] E := c • ContinuousLinearMap.id ℝ E with hL
  have hgL : ContDiff ℝ ∞ ((g : E → ℂ) ∘ L) := (g.smooth ⊤).comp L.contDiff
  have hfun : cutErr (E := E) c = ((g : E → ℂ) ∘ L) - fun _ => (1 : ℂ) := by
    funext z; simp [cutErr, hL, hg]
  rw [hfun, iteratedFDeriv_sub_apply (hgL.contDiffAt.of_le (by exact_mod_cast le_top)) contDiffAt_const,
    iteratedFDeriv_const_of_ne hj, Pi.zero_apply, sub_zero,
    L.iteratedFDeriv_comp_right (g.smooth ⊤) y (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hLn : ‖L‖ ≤ |c| := by
    rw [hL]; refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs]; exact mul_le_of_le_one_right (abs_nonneg c) ContinuousLinearMap.norm_id_le
  have hD : ‖iteratedFDeriv ℝ j g (L y)‖ ≤ SchwartzMap.seminorm ℝ 0 j g := by
    simpa using SchwartzMap.le_seminorm ℝ 0 j g (L y)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hLn j) hD (norm_nonneg _)
    (pow_nonneg (abs_nonneg c) j)

theorem norm_iteratedFDeriv_cutErr_le' (c : ℝ) (hc : |c| ≤ 1) (j : ℕ) (y : E) :
    ‖iteratedFDeriv ℝ j (cutErr c) y‖ ≤
      |c| * (Real.pi + SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E)) * (1 + ‖y‖) ^ 2 := by
  have hS : 0 ≤ SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E) := apply_nonneg _ _
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hc0 : 0 ≤ |c| := abs_nonneg c
  have hpi := Real.pi_pos
  have h1 : 1 ≤ (1 + ‖y‖) ^ 2 := one_le_pow₀ (by linarith)
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [norm_iteratedFDeriv_zero]
    refine (norm_cutErr_le c y).trans ?_
    have hc2 : c ^ 2 ≤ |c| := by rw [← sq_abs]; nlinarith
    have hy2 : ‖y‖ ^ 2 ≤ (1 + ‖y‖) ^ 2 := by nlinarith
    calc Real.pi * c ^ 2 * ‖y‖ ^ 2 ≤ Real.pi * |c| * (1 + ‖y‖) ^ 2 := by gcongr
      _ = |c| * Real.pi * (1 + ‖y‖) ^ 2 := by ring
      _ ≤ _ := by gcongr; linarith
  · refine (norm_iteratedFDeriv_cutErr_le c hj.ne' y).trans ?_
    have hcj : |c| ^ j ≤ |c| := pow_le_of_le_one hc0 hc hj.ne'
    calc |c| ^ j * SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E)
        ≤ |c| * SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E) := by gcongr
      _ ≤ |c| * (Real.pi + SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E)) * 1 := by
          rw [mul_one]; gcongr; linarith
      _ ≤ _ := by gcongr

theorem cut_bound (h : 𝓢(E, ℂ)) (k n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, |c| ≤ 1 → ∀ y : E,
    ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => cutErr c y * h y) y‖ ≤ |c| * K := by
  set S : ℕ → ℝ := fun i => SchwartzMap.seminorm ℝ 0 i (GroundTheory.Global.gaussianSchwartz E) with hS
  set P := (Finset.Iic (k + 2, n)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) h with hP_def
  have hP : 0 ≤ P := apply_nonneg _ _
  have hS0 : ∀ i, 0 ≤ S i := fun i => apply_nonneg _ _
  have hpi := Real.pi_pos
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (Real.pi + S i) * (2 ^ (k + 2) * P),
    Finset.sum_nonneg fun i _ => by have := hS0 i; positivity, fun c hc y => ?_⟩
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hL := norm_iteratedFDeriv_mul_le (contDiff_cutErr (E := E) c) (h.smooth ⊤) y (n := n)
    (by exact_mod_cast le_top)
  calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => cutErr c y * h y) y‖
      ≤ ‖y‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (cutErr c) y‖ *
          ‖iteratedFDeriv ℝ (n - i) h y‖ := by gcongr
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (‖iteratedFDeriv ℝ i (cutErr c) y‖ *
          (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖)) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((|c| * (Real.pi + S i)) *
          ((1 + ‖y‖) ^ 2 * (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := norm_iteratedFDeriv_cutErr_le' c hc i y
        have h0 : 0 ≤ ‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖ := by positivity
        have e : |c| * (Real.pi + S i) * ((1 + ‖y‖) ^ 2 * (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖)) =
          (|c| * (Real.pi + S i) * (1 + ‖y‖) ^ 2) * (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖) := by ring
        rw [e]; gcongr
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((|c| * (Real.pi + S i)) * (2 ^ (k + 2) * P)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hS0i := hS0 i
        have hX : (1 + ‖y‖) ^ 2 * (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖) ≤ 2 ^ (k + 2) * P := by
          calc (1 + ‖y‖) ^ 2 * (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖)
              ≤ (1 + ‖y‖) ^ 2 * ((1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖) := by
                gcongr; linarith
            _ = (1 + ‖y‖) ^ (k + 2) * ‖iteratedFDeriv ℝ (n - i) h y‖ := by ring
            _ ≤ 2 ^ (k + 2) * P :=
                SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k + 2, n)) le_rfl
                  (Nat.sub_le n i) h y
        gcongr
    _ = |c| * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (Real.pi + S i) * (2 ^ (k + 2) * P) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring

def cutMap (h : 𝓢(E, ℂ)) (c : ℝ) (hc : |c| ≤ 1) : 𝓢(E, ℂ) where
  toFun y := cutErr c y * h y
  smooth' := (contDiff_cutErr c).mul (h.smooth ⊤)
  decay' k n := by
    obtain ⟨K, -, hK⟩ := cut_bound h k n
    exact ⟨|c| * K, hK c hc⟩

theorem cutMap_apply (h : 𝓢(E, ℂ)) (c : ℝ) (hc : |c| ≤ 1) (y : E) :
    cutMap h c hc y = cutErr c y * h y := rfl

end GlobalTheory.GaussCutoff


open GlobalTheory.GaussCutoff in
theorem GlobalTheory.GaussCutoff.mem_closure_gauss_mul (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (h : SchwartzMap E ℂ) :
    h ∈ closure {u : SchwartzMap E ℂ | ∃ b : ℝ, 0 < b ∧ ∀ y, u y = Complex.exp (-((b * ‖y‖ ^ 2 : ℝ) : ℂ)) * h y} := by
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨s, r, hr, hsub⟩ := ((schwartz_withSeminorms ℝ E ℂ).mem_nhds_iff h U).1 hU
  choose K hK0 hK using fun m : ℕ × ℕ => cut_bound h m.1 m.2
  set M := ∑ m ∈ s, K m with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun m _ => hK0 m
  set c := min 1 (r / (2 * (M + 1))) with hc_def
  have hcpos : 0 < c := lt_min one_pos (by positivity)
  have hc1 : |c| ≤ 1 := by rw [abs_of_pos hcpos]; exact min_le_left _ _
  have hcr : c * (M + 1) ≤ r / 2 := by
    have := min_le_right 1 (r / (2 * (M + 1)))
    rw [← hc_def] at this
    calc c * (M + 1) ≤ r / (2 * (M + 1)) * (M + 1) := by gcongr
      _ = r / 2 := by field_simp
  refine ⟨h + cutMap h c hc1, hsub ?_, Real.pi * c ^ 2, by positivity, fun y => ?_⟩
  · rw [Seminorm.mem_ball, add_sub_cancel_left]
    refine Seminorm.finset_sup_apply_lt hr fun m hm => ?_
    have h1 : SchwartzMap.seminorm ℝ m.1 m.2 (cutMap h c hc1) ≤ |c| * K m :=
      SchwartzMap.seminorm_le_bound ℝ m.1 m.2 _ (mul_nonneg (abs_nonneg c) (hK0 m)) (hK m c hc1)
    have h2 : K m ≤ M := Finset.single_le_sum (fun m _ => hK0 m) hm
    show SchwartzMap.seminorm ℝ m.1 m.2 (cutMap h c hc1) < r
    rw [abs_of_pos hcpos] at h1
    nlinarith
  · rw [add_apply, cutMap_apply, cutErr, GroundTheory.Global.gaussianSchwartz_apply, Complex.ofReal_exp]
    have e : -Real.pi * ‖c • y‖ ^ 2 = -(Real.pi * c ^ 2 * ‖y‖ ^ 2) := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
    rw [e]; push_cast; ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGLintIffMatrixImageStandardLatticeEq
section
open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.LatOrbGL

variable {K : Type} [Field K] (V : ValuationSubring K)

theorem mem_range_iff (x : K) : x ∈ (algebraMap V K).range ↔ x ∈ V := by
  constructor
  · rintro ⟨a, rfl⟩; exact a.2
  · intro h; exact ⟨⟨x, h⟩, rfl⟩

theorem matLat_le_of_entries {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (hg : ∀ i j, g i j ∈ V) :
    matLat V g (stdLat V n) ≤ stdLat V n := by
  intro v hv
  rw [mem_matLat] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  rw [mem_stdLat] at hu ⊢
  intro i
  have hu' := fun j => (mem_range_iff V _).1 (hu j)
  apply (mem_range_iff V _).2
  simp only [Matrix.mulVec, dotProduct]
  exact V.toSubring.sum_mem fun j _ => V.toSubring.mul_mem (hg i j) (hu' j)

theorem entries_of_matLat_le {n : ℕ} (g : Matrix (Fin n) (Fin n) K)
    (hg : matLat V g (stdLat V n) ≤ stdLat V n) (i j : Fin n) : g i j ∈ V := by
  have hs : (Pi.single j (1 : K) : Fin n → K) ∈ stdLat V n := by
    rw [mem_stdLat]
    intro l
    rw [mem_range_iff]
    by_cases h : l = j
    · subst h; simp [V.one_mem]
    · simp [Pi.single_apply, h, V.zero_mem]
  have hm : g *ᵥ (Pi.single j (1 : K)) ∈ stdLat V n := hg ((mem_matLat _ _ _).2 ⟨_, hs, rfl⟩)
  rw [mem_stdLat] at hm
  have := (mem_range_iff V _).1 (hm i)
  simpa [Matrix.mulVec_single] using this

theorem matLat_mono {n : ℕ} (g : Matrix (Fin n) (Fin n) K) {M N : Submodule V (Fin n → K)}
    (h : M ≤ N) : matLat V g M ≤ matLat V g N := Submodule.map_mono h

end GlobalTheory.LatOrbGL


open GlobalTheory.LatOrbGL in
theorem GlobalTheory.LatOrb.mem_GLint_iff_matLat_std :
    ∀ {K : Type} [Field K] (V : ValuationSubring K) (n : ℕ) (k : GL (Fin n) K),
    k ∈ Formalism.UG.GLint (Fin n) V.toSubring ↔ matLat V k.val (stdLat V n) = stdLat V n := by
  intro K _ V n k
  constructor
  · rintro ⟨g, rfl⟩
    set k := Formalism.UG.bc V.toSubring.subtype g with hk
    have e1 : ∀ i j, k.val i j ∈ V := by
      intro i j; exact ((g : Matrix (Fin n) (Fin n) V.toSubring) i j).2
    have e2 : ∀ i j, (k⁻¹).val i j ∈ V := by
      intro i j; rw [hk, ← map_inv]; exact (((g⁻¹ : GL (Fin n) V.toSubring) : Matrix (Fin n) (Fin n) V.toSubring) i j).2
    apply le_antisymm (matLat_le_of_entries V _ e1)
    have : k.val * (k⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc stdLat V n = matLat V (k.val * (k⁻¹).val) (stdLat V n) := by rw [this, matLat_one]
      _ = _ := matLat_mul _ _ _
      _ ≤ _ := matLat_mono V _ (matLat_le_of_entries V _ e2)
  · intro h
    have e1 := entries_of_matLat_le V k.val h.le
    have h2 : matLat V (k⁻¹ : GL (Fin n) K).val (stdLat V n) = stdLat V n := by
      conv_lhs => rw [← h]
      rw [← matLat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, matLat_one]
    have e2 := entries_of_matLat_le V (k⁻¹ : GL (Fin n) K).val h2.le
    let A : Matrix (Fin n) (Fin n) V.toSubring := Matrix.of fun i j => ⟨k.val i j, e1 i j⟩
    let B : Matrix (Fin n) (Fin n) V.toSubring := Matrix.of fun i j => ⟨(k⁻¹ : GL (Fin n) K).val i j, e2 i j⟩
    have hA : (RingHom.mapMatrix V.toSubring.subtype) A = k.val := by ext i j; rfl
    have hB : (RingHom.mapMatrix V.toSubring.subtype) B = (k⁻¹ : GL (Fin n) K).val := by ext i j; rfl
    have inj : Function.Injective (RingHom.mapMatrix (m := Fin n) V.toSubring.subtype) := by
      intro X Y hXY; ext i j; exact congrFun (congrFun hXY i) j
    have hAB : A * B = 1 := inj (by rw [map_mul, hA, hB, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one])
    have hBA : B * A = 1 := inj (by rw [map_mul, hA, hB, map_one, ← Units.val_mul, inv_mul_cancel, Units.val_one])
    refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
    ext i j
    rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIntermediateFieldOfForallComplexAutFixed
section
namespace GlobalTheory.CMModel

theorem mem_of_forall_ringEquiv_fixed :
    ∀ (F : IntermediateField ℚ ℂ) (x : ℂ),
      (∀ σ : ℂ ≃+* ℂ, (∀ y ∈ F, σ y = y) → σ x = x) → x ∈ F := fun F x hx ↦ by
  obtain ⟨y, rfl⟩ := GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := F) x
    fun σ ↦ hx σ.toRingEquiv fun y hy ↦ σ.commutes ⟨y, hy⟩
  exact y.2

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanHeisenbergTranslatesOfVacuumStatement
section
open Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_heisenberg_translates_of_vacuum : ∀ (X M : Type) [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (β : X → X → ℂ) (ρ : X → M →ₗ[ℂ] M) (Λ : AddSubgroup X) (e : M), (∀ x y z, β (x + y) z = β x z * β y z) → (∀ x y z, β x (y + z) = β x y * β x z) → (∀ x, β x x = 1) → (∀ v, ρ 0 v = v) → (∀ x y v, ρ x (ρ y v) = β x y • ρ (x + y) v) → (∀ x, x ∈ Λ ↔ ∀ a ∈ Λ, β x a ^ 2 = 1) → (∀ N : ℕ, 0 < N → ∀ x : X, ∃ y : X, N • y = x) → (∀ N : ℕ, 0 < N → ∃ R : Set X, R.Finite ∧ ∀ t ∈ Λ, ∃ r ∈ R, ∃ u ∈ Λ, t = r + N • u) → e ≠ 0 → (∀ u ∈ Λ, ∃ ε : ℂ, ρ u e = ε • e) → (∀ u ∈ Λ, ρ (2 • u) e = e) → (∀ v : M, (∀ u ∈ Λ, ∀ ε : ℂ, ρ u e = ε • e → ρ u v = ε • v) → ∃ c : ℂ, v = c • e) → ∀ v : M, (∃ N : ℕ, 0 < N ∧ ∀ u ∈ Λ, ρ (N • u) v = v) → v ∈ Submodule.span ℂ (Set.range fun x => ρ x e) := by
  first | exact @GlobalTheory.HeisVacuum.mem_span_translates_vacuum | exact GlobalTheory.HeisVacuum.mem_span_translates_vacuum | (intros; apply GlobalTheory.HeisVacuum.mem_span_translates_vacuum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportQuotientSpanIffOfIsPushout
section
open CategoryTheory CategoryTheory.Limits TensorProduct

namespace GlobalTheory.SupportBC

theorem mem_support_quotient_span_iff_of_isPushout :
    ∀ (R S R' S' : CommRingCat.{0}) (qa : R ⟶ S) (ba : R ⟶ R') (ga : S ⟶ S') (qa' : R' ⟶ S'),
      IsPushout qa ba ga qa' → qa.hom.Finite → ∀ {ι : Type} (s : ι → S) (p : PrimeSpectrum R'),
      ((letI := qa'.hom.toAlgebra;
        p ∈ Module.support R' (S' ⧸ Submodule.span R' (Set.range (fun i => ga.hom (s i))))) ↔
      (letI := qa.hom.toAlgebra;
        PrimeSpectrum.comap ba.hom p ∈ Module.support R (S ⧸ Submodule.span R (Set.range s)))) := by
  first
  | exact @_root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff
  | exact _root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff
  | (apply _root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff ..)

end GlobalTheory.SupportBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicSplitsValuationSubringOfSeparableReductionStatement
section
open Polynomial IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monic_splits_valuationSubring_of_separable_reduction : ∀ (Ω : Type) [Field Ω] [IsSepClosed Ω] (V : ValuationSubring Ω) (q : Polynomial V), q.Monic → (q.map (IsLocalRing.residue V)).Separable → ∃ s : Multiset V, q = (s.map fun b => Polynomial.X - Polynomial.C b).prod := by
  first | exact @GlobalTheory.monic_splits_of_separable_residue | exact GlobalTheory.monic_splits_of_separable_residue | (intros; apply GlobalTheory.monic_splits_of_separable_residue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuCoeffPartialDerivMuEqSuccMul
section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem t_coefM_pderiv : T_coefM_pderiv := by
  intro n L k s
  simp only [coefM, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
    Polynomial.lcoeff_apply, AlgEquiv.toLinearMap_apply]
  exact GlobalTheory.optionEquivLeft_pderiv_none_coeff k s

end GlobalTheory.PsCo.Cw2a
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentApproximationSurjective
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilpotent_approximation_surjective : ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] (I : Ideal B) (K : Ideal A) (N : ℕ), (∀ a : A, ∃ b : B, a - algebraMap B A b ∈ I.map (algebraMap B A) ⊔ K) → (I ^ N).map (algebraMap B A) ≤ K → ∀ a : A, ∃ b : B, a - algebraMap B A b ∈ K := by
  first | (exact @GlobalTheory.surj_mod_of_surj_mod_map_sup_of_pow_map_le) | (exact GlobalTheory.surj_mod_of_surj_mod_map_sup_of_pow_map_le) | (intros; apply GlobalTheory.surj_mod_of_surj_mod_map_sup_of_pow_map_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoetherNormalizationFiniteAevalPowAddStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noether_normalization_finite_aeval_pow_add : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] (t a : A), (Polynomial.aeval (R := k) t).Finite → ∃ M : ℕ, (Polynomial.aeval (R := k) (t ^ M + a)).Finite := by
  first | exact @GlobalTheory.noether_trick | exact GlobalTheory.noether_trick | (intros; apply GlobalTheory.noether_trick <;> assumption)
end

