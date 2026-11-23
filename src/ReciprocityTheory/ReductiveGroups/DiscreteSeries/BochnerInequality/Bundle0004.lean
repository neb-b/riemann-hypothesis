module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Weights
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.BigCas
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.PositionPrependMemNoncompactPositionSubmodule

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.InnerCrossOpEigEqZero
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section One

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem Wm_le_ncV : Wm ε E V ≤ ncV ε V 1 := by
  unfold Wm
  exact iSup₂_le fun _ _ => inf_le_right

theorem inner_crossOp_eig_eq_zero (hU : IsInfUnitary ε E) {θ θ' : ℝ} (hθ : θ ≠ θ')
    {u v : Big n 1 M} (hu : crossOp ε E 1 0 u = (θ : ℂ) • u)
    (hv : crossOp ε E 1 0 v = (θ' : ℂ) • v) : inner ℂ u v = 0 := by
  have h := crossOp_symm hU 1 0 u v
  rw [hu, hv, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
  have hne : (θ : ℂ) ≠ (θ' : ℂ) := by exact_mod_cast hθ
  by_contra h0
  exact hne (mul_right_cancel₀ h0 h)

theorem Wm_perp_Wp (hU : IsInfUnitary ε E) {x y : Big n 1 M} (hx : x ∈ Wm ε E V)
    (hy : y ∈ Wp ε E V) : inner ℂ x y = 0 := by
  have h : (Wm ε E V).IsOrtho (Wp ε E V) := by
    unfold Wm Wp
    refine Submodule.isOrtho_iSup_left.mpr fun θ => Submodule.isOrtho_iSup_left.mpr fun hθ =>
      Submodule.isOrtho_iSup_right.mpr fun θ' => Submodule.isOrtho_iSup_right.mpr fun hθ' => ?_
    rw [Submodule.isOrtho_iff_inner_eq]
    intro u hu v hv
    rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff] at hu hv
    exact inner_crossOp_eig_eq_zero hU (ne_of_lt (hθ.trans hθ')) hu.1 hv.1
  exact Submodule.isOrtho_iff_inner_eq.mp h x hx y hy

theorem mem_V_of_mem_ncV {k : ℕ} {F : Big n k M} (hF : F ∈ ncV ε V k)
    (κ : Fin k → Fin n × Fin n) : F κ ∈ V := by
  exact ncV_mem hF κ

private theorem casimirK_eq_casValK_smul_of_isKHWVec {X : Type*} [AddCommGroup X] [Module ℂ X]
    {A : Fin n → Fin n → Module.End ℂ X} (hA : IsGlRep A) {μ : Fin n → ℝ} {w : X}
    (hw : IsKHWVec ε A μ w) : casimirK ε A w = (casValK ε μ : ℂ) • w := by
  have hA' : ∀ a b c d : Fin n, A a b * A c d - A c d * A a b =
      (if b = c then A a d else 0) - (if d = a then A c b else 0) := hA
  have term : ∀ a b : Fin n, ε b = ε a → A a b (A b a w) =
      ((((if b = a then μ a ^ 2 else 0) + (if a < b then μ a - μ b else 0) : ℝ)) : ℂ) • w := by
    intro a b hab
    rcases lt_trichotomy b a with h | h | h
    · rw [hw.2 b a h hab, map_zero, if_neg (ne_of_lt h), if_neg (lt_asymm h)]
      simp
    · subst h
      rw [if_pos rfl, if_neg (lt_irrefl b), add_zero, hw.1 b, map_smul, hw.1 b, smul_smul,
        ← Complex.ofReal_mul, ← sq]
    · have e := LinearMap.congr_fun (hA' a b b a) w
      simp only [LinearMap.sub_apply, Module.End.mul_apply, eq_self_iff_true, if_true,
        hw.2 a b h hab.symm, map_zero, sub_zero] at e
      rw [e, if_neg (ne_of_gt h), if_pos h, hw.1 a, hw.1 b]
      simp [sub_smul]
  have hsum : casimirK ε A w = ((∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
      ((if b = a then μ a ^ 2 else 0) + (if a < b then μ a - μ b else 0)) : ℝ) : ℂ) • w := by
    simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply, Complex.ofReal_sum,
      Finset.sum_smul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb =>
      term a b (Finset.mem_filter.mp hb).2
  have hA2 : ∀ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
      ((if b = a then μ a ^ 2 else 0) + (if a < b then μ a - μ b else 0)) =
      μ a ^ 2 + ((∑ b, if a < b ∧ ε b = ε a then μ a else 0) -
        ∑ b, if a < b ∧ ε b = ε a then μ b else 0) := by
    intro a
    rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
    have h2 : μ a ^ 2 = ∑ b, (if b = a then μ a ^ 2 else 0) := by simp
    conv_rhs => rw [h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp_all
  have hC : (∑ a, ∑ b, if a < b ∧ ε b = ε a then μ b else 0) =
      ∑ a, ∑ b, if b < a ∧ ε b = ε a then μ a else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h1 : b < a ∧ ε a = ε b
    · rw [if_pos h1, if_pos ⟨h1.1, h1.2.symm⟩]
    · rw [if_neg h1, if_neg fun h2 => h1 ⟨h2.1, h2.2.symm⟩]
  have hρ : ∀ a, 2 * rhoC ε a = (∑ b, if a < b ∧ ε b = ε a then (1 : ℝ) else 0) -
      ∑ b, if b < a ∧ ε b = ε a then (1 : ℝ) else 0 := by
    intro a
    simp only [rhoC]
    rw [Finset.sum_boole, Finset.sum_boole]
    ring
  have hR : casValK ε μ = ∑ a, (μ a ^ 2 + μ a * (2 * rhoC ε a)) := by
    simp only [casValK, nsq, dot, Pi.add_apply]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hsum, hR, Finset.sum_congr rfl fun a _ => hA2 a]
  congr 2
  simp only [hρ, mul_sub, Finset.mul_sum, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, hC]

theorem crossOp_khw (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) {x : Big n 1 M} (hx : x ∈ ncV ε V 1) (hx0 : x ≠ 0)
    {ν : Fin n → ℝ} (hν : IsKHWVec ε (bAct E 1) ν x) :
    ∃ r s : Fin n, ε r ≠ ε s ∧ ν = lowK ε lam + root r s ∧
      (2 : ℂ) • crossOp ε E 1 0 x =
        ((casValK ε ν - n - casValK ε (lowK ε lam) : ℝ) : ℂ) • x := by
  obtain ⟨γ, hγ, hνγ⟩ := khw_big_weight hE hV hx hx0 hν
  refine ⟨(γ 0).1, (γ 0).2, hγ 0, ?_, ?_⟩
  · rw [Fin.sum_univ_one] at hνγ
    rw [← hνγ]
    abel
  · have hm : casimirK ε (mAct E 1) x = (casValK ε (lowK ε lam) : ℂ) • x := by
      ext κ
      rw [casimirK_mAct_apply, casimirK_irr hE hV _ (ncV_mem hx κ)]
      rfl
    have hcas := LinearMap.congr_fun (casimirK_bAct (ε := ε) (E := E) 1) x
    rw [casimirK_eq_casValK_smul_of_isKHWVec (bAct_isGlRep hE 1) hν] at hcas
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Fin.sum_univ_one, factorCasimir_ncV_one hx,
      hm, two_smul] at hcas
    rw [two_smul]
    push_cast
    rw [sub_smul, sub_smul, hcas]
    abel

theorem Wm_kStable (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) : IsKStableSub ε (bAct E 1) (Wm ε E V) := by
  intro a b hab v hv
  have hVs : IsKStableSub ε E V := hV.2.1
  have hle : Wm ε E V ≤ (Wm ε E V).comap (bAct E 1 a b) := by
    unfold Wm
    refine iSup₂_le fun θ hθ x hx => ?_
    rw [Submodule.mem_comap]
    rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff] at hx
    have hc : crossOp ε E 1 0 (bAct E 1 a b x) = bAct E 1 a b (crossOp ε E 1 0 x) :=
      LinearMap.congr_fun (crossOp_comm hE 1 0 hab) x
    have hmem : bAct E 1 a b x ∈
        Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1 := by
      rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff]
      refine ⟨?_, ncV_kStable hVs 1 a b hab x hx.2⟩
      rw [hc, hx.1, map_smul]
    exact Submodule.mem_iSup_of_mem θ (Submodule.mem_iSup_of_mem hθ hmem)
  exact hle hv

end One

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerWeight
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section LayerWeight

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem lift_layer (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hVfd : FiniteDimensional ℂ V)
    (hVk : IsKStableSub ε E V) {k : ℕ} {w : M} (hw : w ∈ layer ε E V (k + 1))
    (hperp : ∀ u ∈ layer ε E V k, inner ℂ u w = 0) {μ : Fin n → ℝ} (hμ : IsKHWVec ε E μ w)
    (hw0 : w ≠ 0) :
    ∃ P ∈ ncV ε V (k + 1), P ≠ 0 ∧ IsKHWVec ε (bAct E (k + 1)) μ P ∧
      ∀ F ∈ ncV ε V (k + 1), phi E (k + 1) F ∈ layer ε E V k → inner ℂ F P = 0 := by
  classical
  set Lk := layer ε E V k with hLk
  haveI : FiniteDimensional ℂ Lk := finiteDimensional_layer (ε := ε) (E := E) hVfd k
  set N := ncV ε V (k + 1) with hN
  haveI : FiniteDimensional ℂ N := finiteDimensional_ncV (ε := ε) hVfd (k + 1)
  set U : Submodule ℂ (Big n (k + 1) M) := N ⊓ Lk.comap (phi E (k + 1)) with hUdef
  haveI : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le inf_le_left

  have hKu : ∀ a b, ε a = ε b → ∀ x y : M, inner ℂ x (E a b y) = inner ℂ (E b a x) y := by
    intro a b hab x y
    rw [hU b a x y]
    simp [adjSign, hab.symm]
  have hLkK : IsKStableSub ε E Lk := layer_kStable hE hVk k
  have hLkoK : ∀ a b, ε a = ε b → ∀ y ∈ Lkᗮ, E a b y ∈ Lkᗮ := by
    intro a b hab y hy
    rw [Submodule.mem_orthogonal] at hy ⊢
    intro u hu
    rw [hKu a b hab u y]
    exact hy _ (hLkK b a hab.symm u hu)
  have hBu := bAct_isKUnitary hU (k + 1)
  have hNK : IsKStableSub ε (bAct E (k + 1)) N := ncV_kStable hVk (k + 1)
  have hUK : ∀ a b, ε a = ε b → ∀ H ∈ U, bAct E (k + 1) a b H ∈ U := by
    intro a b hab H hH
    refine ⟨hNK a b hab H hH.1, ?_⟩
    show phi E (k + 1) (bAct E (k + 1) a b H) ∈ Lk
    rw [wordContraction_tensorAction hE]
    exact hLkK a b hab _ hH.2
  have hUoK : ∀ a b, ε a = ε b → ∀ H ∈ Uᗮ, bAct E (k + 1) a b H ∈ Uᗮ := by
    intro a b hab H hH
    rw [Submodule.mem_orthogonal] at hH ⊢
    intro u hu
    rw [← hBu b a hab.symm u H]
    exact hH _ (hUK b a hab.symm u hu)

  let Ψ : Big n (k + 1) M →ₗ[ℂ] M :=
    (LinearMap.id - ((Lk.starProjection : M →L[ℂ] M) : M →ₗ[ℂ] M)) ∘ₗ phi E (k + 1)
  have hΨ : ∀ H, Ψ H = phi E (k + 1) H - Lk.starProjection (phi E (k + 1) H) := fun H => rfl
  have hPmem : ∀ v, Lk.starProjection v ∈ Lk := fun v => by
    rw [Submodule.starProjection_apply]; exact SetLike.coe_mem _
  have hzero : ∀ x, x ∈ Lk → x ∈ Lkᗮ → x = 0 := by
    intro x h1 h2
    have hm : x ∈ Lk ⊓ Lkᗮ := ⟨h1, h2⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hm
    exact hm
  have hΨo : ∀ H, Ψ H ∈ Lkᗮ := fun H => by
    rw [hΨ]; exact Submodule.sub_starProjection_mem_orthogonal _
  have hΨeq : ∀ a b, ε a = ε b → ∀ H, Ψ (bAct E (k + 1) a b H) = E a b (Ψ H) := by
    intro a b hab H
    rw [← sub_eq_zero]
    apply hzero
    · rw [hΨ, hΨ, wordContraction_tensorAction hE, map_sub]
      have e : E a b (phi E (k + 1) H) - Lk.starProjection (E a b (phi E (k + 1) H)) -
          (E a b (phi E (k + 1) H) - E a b (Lk.starProjection (phi E (k + 1) H))) =
          E a b (Lk.starProjection (phi E (k + 1) H)) -
            Lk.starProjection (E a b (phi E (k + 1) H)) := by abel
      rw [e]
      exact Lk.sub_mem (hLkK a b hab _ (hPmem _)) (hPmem _)
    · exact Lkᗮ.sub_mem (hΨo _) (hLkoK a b hab _ (hΨo _))
  have hinj : ∀ H ∈ Uᗮ, H ∈ N → Ψ H = 0 → H = 0 := by
    intro H hHo hHN h0
    have hphi : phi E (k + 1) H ∈ Lk := by
      rw [hΨ, sub_eq_zero] at h0
      rw [h0]; exact hPmem _
    have hm : H ∈ U ⊓ Uᗮ := ⟨⟨hHN, hphi⟩, hHo⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hm
    exact hm

  obtain ⟨l, hl, y, hy, hly⟩ := Submodule.mem_sup.mp (layer_succ_le hE hVk k hw)
  obtain ⟨G0, hG0, rfl⟩ := Submodule.mem_map.mp hy
  have hUmem : U.starProjection G0 ∈ U := by
    rw [Submodule.starProjection_apply]; exact SetLike.coe_mem _
  set G := G0 - U.starProjection G0 with hG
  have hGo : G ∈ Uᗮ := Submodule.sub_starProjection_mem_orthogonal G0
  have hGN : G ∈ N := N.sub_mem hG0 hUmem.1
  have hwo : w ∈ Lkᗮ := by rw [Submodule.mem_orthogonal]; exact hperp
  have hΨG : Ψ G = w := by
    rw [← sub_eq_zero]
    apply hzero
    · rw [hΨ, hG, map_sub, ← hly]
      have hpu : phi E (k + 1) (U.starProjection G0) ∈ Lk := hUmem.2
      have e : phi E (k + 1) G0 - phi E (k + 1) (U.starProjection G0) -
          Lk.starProjection (phi E (k + 1) G0 - phi E (k + 1) (U.starProjection G0)) -
          (l + phi E (k + 1) G0) =
          -(phi E (k + 1) (U.starProjection G0)) -
            Lk.starProjection (phi E (k + 1) G0 - phi E (k + 1) (U.starProjection G0)) - l := by
        abel
      rw [e]
      exact Lk.sub_mem (Lk.sub_mem (Lk.neg_mem hpu) (hPmem _)) hl
    · exact Lkᗮ.sub_mem (hΨo G) hwo
  refine ⟨G, hGN, ?_, ?_, ?_⟩
  · intro h0
    apply hw0
    rw [← hΨG, h0, map_zero]
  · constructor
    · intro a
      have hD : bAct E (k + 1) a a G - ((μ a : ℂ)) • G = 0 := by
        apply hinj
        · exact Uᗮ.sub_mem (hUoK a a rfl G hGo) (Uᗮ.smul_mem _ hGo)
        · exact N.sub_mem (hNK a a rfl G hGN) (N.smul_mem _ hGN)
        · rw [map_sub, map_smul, hΨeq a a rfl, hΨG, hμ.1 a, sub_self]
      exact sub_eq_zero.mp hD
    · intro a b hab hεab
      apply hinj _ (hUoK a b hεab G hGo) (hNK a b hεab G hGN)
      rw [hΨeq a b hεab, hΨG, hμ.2 a b hab hεab]
  · intro F hF hphi
    rw [Submodule.mem_orthogonal] at hGo
    exact hGo F ⟨hF, hphi⟩

theorem khw_layer_weight (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (k : ℕ) {μ : Fin n → ℝ} {w : M}
    (hw : w ∈ layer ε E V k) (hw0 : w ≠ 0) (hμ : IsKHWVec ε E μ w) :
    ∃ j ≤ k, IsNCSum ε j (μ - lowK ε lam) := by
  classical
  obtain ⟨w₀, hw₀V, hw₀, ws, hsum, hws⟩ := layer_khw_decomp hE hU hV.1 hV.2.1 hw hμ
  by_cases h0 : w₀ = 0
  · have hex : ∃ j, ws j ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply hw0
      rw [hsum, h0]
      simp [hc]
    obtain ⟨j, hj⟩ := hex
    obtain ⟨hj1, hj2, hj3⟩ := hws j
    obtain ⟨P, hPN, hP0, hPk, -⟩ := lift_layer hE hU hV.1 hV.2.1 hj1 hj2 hj3 hj
    exact ⟨(j : ℕ) + 1, by omega, khw_big_weight hE hV hPN hP0 hPk⟩
  ·
    let F : Big n 0 M := WithLp.toLp 2 (fun _ => w₀)
    have hF : ∀ κ, F κ = w₀ := fun κ => rfl
    have hFN : F ∈ ncV ε V 0 := by
      rw [mem_ncV_iff]
      intro κ
      simp [hF, hw₀V]
    have hF0 : F ≠ 0 := by
      intro hF'
      apply h0
      have := congrArg (fun G : Big n 0 M => G (fun i => i.elim0)) hF'
      simpa [hF] using this
    have hFk : IsKHWVec ε (bAct E 0) μ F := by
      constructor
      · intro a
        ext κ
        rw [bAct_apply]
        simp [hF, hw₀.1 a]
      · intro a b hab hε
        ext κ
        rw [bAct_apply]
        simp [hF, hw₀.2 a b hab hε]
    exact ⟨0, Nat.zero_le _, khw_big_weight hE hV hFN hF0 hFk⟩

end LayerWeight

end ReciprocityTheory.ChartRestriction.DS
end
end

