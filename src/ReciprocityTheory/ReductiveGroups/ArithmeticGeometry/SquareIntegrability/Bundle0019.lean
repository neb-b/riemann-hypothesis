module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0018

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.OneChar
section
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

set_option maxHeartbeats 1000000 in
lemma one_char [IsCMField E] (hNP : Ext.NearestPlane) {dim : (E →+* ℂ) → ℕ}
    (L I : Submodule ℤ (Vsp dim))
    (hLs : ∀ (α : 𝓞 E) x, x ∈ L → act α x ∈ L) (hIs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I)
    (hiso : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) (hsep : ∀ g ∈ Xg L I, g ≠ 0 → 1 ≤ ‖g‖)
    (ω : Fin (Module.finrank ℚ E) → 𝓞 E) (hω : LinearIndependent ℚ (fun j => (ω j : E)))
    (B : ℝ) (hωB : ∀ j (τ : E →+* ℂ), ‖τ (ω j : E)‖ ≤ B)
    (D : ℕ) (hD : Module.finrank ℝ (IR I) ≤ D) (σ : E →+* ℂ) (W : Submodule ℂ (Vsp dim))
    (k : ℕ) (χ : ℕ → Vsp dim) (hχX : ∀ j < k, χ j ∈ Xg L I) (hχW : ∀ j < k, prj σ (χ j) ∈ W)
    (hWχ : W ≤ Submodule.span ℂ ((fun i => prj σ (χ i)) '' Set.Iio k))
    (hflag : ∀ j < k, ∃ μ, χ j ∈ Zs L I μ ∧ ∀ y ∈ Xg L I, prj σ y ∉ W → μ ≤ ‖y‖)
    (v : Vsp dim) (hvX : v ∈ Xg L I) (hvW : prj σ v ∉ W)
    (hvmin : ∀ y ∈ Xg L I, prj σ y ∉ W → ‖v‖ ≤ ‖y‖) (T : ℝ) (hT : 0 < T) :
    ∃ t χ' : Vsp dim, (∀ w ∈ W, inner ℂ w (prj σ t) = 0) ∧ ‖prj σ t‖ = T ∧
      ‖t‖ ^ 2 = 2 * T ^ 2 ∧ χ' ∈ Xg L I ∧ χ' ∈ Zs L I ‖v‖ ∧
      ‖χ' - t‖ ^ 2 ≤ D * (B * ‖v‖) ^ 2 / 4 ∧
      ∀ u ∈ Xg L I, |2 * inner ℝ χ' u| ≤ ‖u‖ ^ 2 ∨ ‖v‖ ≤ ‖u‖ := by
  classical

  have hMc1 : ∀ (c : ℂ) (x : Vsp dim), Mc σ 1 (Mc σ c x) = Mc σ c x := by
    intro c x
    ext i
    simp only [Mc, LinearMap.coe_mk, AddHom.coe_mk]
    split_ifs <;> simp
  have hprj1 : ∀ x : Vsp dim, prj σ (Mc σ 1 x) = prj σ x := by
    intro x; rw [prj_Mc, one_smul]
  have hZact : ∀ (α : 𝓞 E) x, x ∈ Zs L I ‖v‖ → act α x ∈ Zs L I ‖v‖ :=
    fun α x hx => Zs_act L I _ α hx
  have hZMc : ∀ (c : ℂ) {x : Vsp dim}, x ∈ Zs L I ‖v‖ → Mc σ c x ∈ Zs L I ‖v‖ :=
    fun c x hx => Mc_mem σ (Zs L I ‖v‖) hZact c hx
  have hvZ : v ∈ Zs L I ‖v‖ := Zs_self L I hvX le_rfl
  have hχZ : ∀ j < k, χ j ∈ Zs L I ‖v‖ := by
    intro j hj
    obtain ⟨μ, hμ, hμle⟩ := hflag j hj
    exact Zs_mono L I (hμle v hvX hvW) hμ
  have hshort : ∀ u ∈ Xg L I, ‖u‖ < ‖v‖ → prj σ u ∈ W := by
    intro u hu huv
    by_contra h
    exact absurd (hvmin u hu h) (not_le.mpr huv)

  obtain ⟨U, hU⟩ : ∃ U : Submodule ℝ (Vsp dim), U = Submodule.span ℝ
      {x | ∃ c : ℂ, ∃ y ∈ Zs L I ‖v‖, prj σ y ∈ W ∧ x = Mc σ c y} := ⟨_, rfl⟩
  have hUgen : ∀ (c : ℂ) y, y ∈ Zs L I ‖v‖ → prj σ y ∈ W → Mc σ c y ∈ U := by
    intro c y hy hyW
    rw [hU]; exact Submodule.subset_span ⟨c, y, hy, hyW, rfl⟩
  have hUZ : U ≤ Zs L I ‖v‖ := by
    rw [hU]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨c, y, hy, -, rfl⟩
    exact hZMc c hy
  have hUprj : ∀ x ∈ U, prj σ x ∈ W := by
    intro x hx
    rw [hU] at hx
    refine prj_mem_of_span σ W _ ?_ hx
    rintro y ⟨c, y', -, hy', rfl⟩
    rw [prj_Mc]; exact W.smul_mem c hy'
  have hUMc : ∀ x ∈ U, Mc σ 1 x ∈ U := by
    intro x hx
    rw [hU] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, y', hy', hy'W, rfl⟩ := hy
      rw [hMc1]; exact hUgen c y' hy' hy'W
    | zero => rw [map_zero]; exact U.zero_mem
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact U.add_mem ha hb
    | smul r a _ ha => rw [LinearMap.map_smul_of_tower]; exact U.smul_mem r ha

  haveI : CompleteSpace U := FiniteDimensional.complete ℝ U
  obtain ⟨y₀, hy₀U, z, hzU, hxyz⟩ := U.exists_add_mem_mem_orthogonal (Mc σ 1 v)
  have hz : z = Mc σ 1 v - y₀ := by rw [hxyz]; abel
  have hzZ : z ∈ Zs L I ‖v‖ := by
    rw [hz]; exact Submodule.sub_mem _ (hZMc 1 hvZ) (hUZ hy₀U)
  have hzperp : ∀ u ∈ U, inner ℝ (Mc σ 1 z) u = 0 := by
    intro u hu
    rw [real_inner_Mc, map_one]
    exact Submodule.inner_left_of_mem_orthogonal (hUMc u hu) hzU
  have hprjt₀ : prj σ (Mc σ 1 z) = prj σ v - prj σ y₀ := by
    rw [hprj1, hz, map_sub, hprj1]
  have hp0 : prj σ (Mc σ 1 z) ≠ 0 := by
    intro h0
    apply hvW
    have h' : prj σ v = prj σ y₀ := by rw [← sub_eq_zero, ← hprjt₀, h0]
    rw [h']; exact hUprj y₀ hy₀U
  have hWorth : ∀ w ∈ W, inner ℂ w (prj σ (Mc σ 1 z)) = 0 := by
    have hsub : W ≤ (Submodule.span ℂ {prj σ (Mc σ 1 z)})ᗮ := by
      refine hWχ.trans (Submodule.span_le.mpr ?_)
      rintro _ ⟨j, hj, rfl⟩
      have hj' : j < k := hj
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
      have hH := orth_prj hiso σ (Zs_IR hIs _ (hZMc 1 hzZ))
        (fun c => Zs_IR hIs _ (hZMc c (hχZ j hj')))
        (fun c => hzperp _ (hUgen c _ (hχZ j hj') (hχW j hj')))
      have key : inner ℂ (prj σ (χ j)) (prj σ (Mc σ 1 z)) =
          Hf (prj σ (Mc σ 1 z)) (prj σ (χ j)) := by
        simp only [Hf, PiLp.inner_apply, RCLike.inner_apply]
      rw [key]; exact hH
    intro w hw
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp (hsub hw)

  have hpn : 0 < ‖prj σ (Mc σ 1 z)‖ := norm_pos_iff.mpr hp0
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = T / ‖prj σ (Mc σ 1 z)‖ := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact div_pos hT hpn
  obtain ⟨t, ht⟩ : ∃ t : Vsp dim, t = r • Mc σ 1 z := ⟨_, rfl⟩
  have htZ : t ∈ Zs L I ‖v‖ := by rw [ht]; exact Submodule.smul_mem _ r (hZMc 1 hzZ)
  have hprjt : prj σ t = r • prj σ (Mc σ 1 z) := by rw [ht, prj_rsmul]
  have hnT : ‖prj σ t‖ = T := by
    rw [hprjt, norm_smul, Real.norm_of_nonneg hr0.le, hr, div_mul_cancel₀ _ hpn.ne']
  have hWt : ∀ w ∈ W, inner ℂ w (prj σ t) = 0 := by
    intro w hw
    rw [hprjt, ← Complex.coe_smul, inner_smul_right, hWorth w hw, mul_zero]
  have hMt : Mc σ 1 t = t := by rw [ht, LinearMap.map_smul_of_tower, hMc1]
  have htn : ‖t‖ ^ 2 = 2 * T ^ 2 := by
    have h := norm_projection_sq hiso σ t (by rw [hMt]; exact Zs_IR hIs _ htZ)
      (Zs_IR hIs _ (hZMc Complex.I htZ))
    rw [hMt, hnT] at h; exact h
  have htorth : ∀ u ∈ Xg L I, ‖u‖ < ‖v‖ → inner ℝ t u = 0 := by
    intro u hu huv
    rw [ht, real_inner_smul_left, real_inner_Mc, map_one,
      Submodule.inner_left_of_mem_orthogonal
        (hUgen 1 u (Zs_self L I hu huv.le) (hshort u hu huv)) hzU, mul_zero]

  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : AddSubgroup (Vsp dim), Λ = Xg L I ⊓ (Zs L I ‖v‖).toAddSubgroup :=
    ⟨_, rfl⟩
  have hΛ : ∀ g, g ∈ Λ ↔ g ∈ Xg L I ∧ g ∈ Zs L I ‖v‖ := by
    intro g; rw [hΛdef, AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup]
  obtain ⟨χ', hχ'Λ, hclose⟩ :=
    exists_closest Λ (fun g hg hg0 => hsep g ((hΛ g).1 hg).1 hg0) t

  obtain ⟨S', hS'⟩ : ∃ S' : Set (Vsp dim),
      S' = {x | ∃ j, ∃ y ∈ Xg L I, ‖y‖ ≤ ‖v‖ ∧ x = act (ω j) y} := ⟨_, rfl⟩
  have hS'Λ : ∀ x ∈ S', x ∈ Λ := by
    intro x hx
    rw [hS'] at hx
    obtain ⟨j, y, hy, hyv, rfl⟩ := hx
    exact (hΛ _).2 ⟨Xg_act hLs hIs (ω j) hy, Zs_act L I _ (ω j) (Zs_self L I hy hyv)⟩
  have hS'norm : ∀ x ∈ S', ‖x‖ ≤ B * ‖v‖ := by
    intro x hx
    rw [hS'] at hx
    obtain ⟨j, y, hy, hyv, rfl⟩ := hx
    have hB : 0 ≤ B := (norm_nonneg _).trans (hωB j σ)
    exact (norm_act_le (ω j) B (hωB j) y).trans (mul_le_mul_of_nonneg_left hyv hB)
  have hZS' : Zs L I ‖v‖ ≤ Submodule.span ℝ S' := by
    unfold Zs
    refine Submodule.span_le.mpr ?_
    rintro x ⟨α, y, hy, hyv, rfl⟩
    refine Submodule.span_mono ?_ (act_omega_expand ω hω α y)
    rintro _ ⟨j, rfl⟩
    rw [hS']
    exact ⟨j, y, hy, hyv, rfl⟩
  obtain ⟨b, hbS', hbspan, hbli⟩ := exists_linearIndependent ℝ S'
  have hli : LinearIndependent ℝ (fun x : b => (x : Vsp dim)) := hbli
  haveI : Finite b := hli.finite
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin b
  obtain ⟨vv, hvvdef⟩ : ∃ vv : Fin n → Vsp dim, vv = fun i => ((e.symm i : b) : Vsp dim) :=
    ⟨_, rfl⟩
  have hvv : LinearIndependent ℝ vv := by
    rw [hvvdef]; exact hli.comp e.symm e.symm.injective
  have hvvS' : ∀ i, vv i ∈ S' := fun i => by rw [hvvdef]; exact hbS' (e.symm i).2
  have hrange : Set.range vv = b := by
    ext x; constructor
    · rintro ⟨i, rfl⟩; rw [hvvdef]; exact (e.symm i).2
    · intro hx; exact ⟨e ⟨x, hx⟩, by rw [hvvdef]; simp⟩
  have htspan : t ∈ Submodule.span ℝ (Set.range vv) := by
    rw [hrange, hbspan]; exact hZS' htZ
  obtain ⟨c, hc⟩ := hNP (Vsp dim) n vv hvv t htspan
  have hnD : (n : ℝ) ≤ D := by
    have h1 : Module.finrank ℝ (Submodule.span ℝ (Set.range vv)) = n := by
      rw [finrank_span_eq_card hvv, Fintype.card_fin]
    have h2 : Submodule.span ℝ (Set.range vv) ≤ IR I := by
      rw [hrange, hbspan]
      exact Submodule.span_le.mpr fun x hx => Zs_IR hIs _ ((hΛ x).1 (hS'Λ x hx)).2
    have h3 : n ≤ D := by rw [← h1]; exact (Submodule.finrank_mono h2).trans hD
    exact_mod_cast h3
  have hgΛ : (∑ i, (c i : ℝ) • vv i) ∈ Λ := by
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    exact AddSubgroup.zsmul_mem _ (hS'Λ _ (hvvS' i)) _
  have hsum : ∑ i, ‖vv i‖ ^ 2 ≤ n * (B * ‖v‖) ^ 2 := by
    calc ∑ i, ‖vv i‖ ^ 2 ≤ ∑ _i : Fin n, (B * ‖v‖) ^ 2 :=
          Finset.sum_le_sum fun i _ => by gcongr; exact hS'norm _ (hvvS' i)
      _ = n * (B * ‖v‖) ^ 2 := by simp
  have hbound : ‖χ' - t‖ ^ 2 ≤ D * (B * ‖v‖) ^ 2 / 4 := by
    have h1 : ‖t - χ'‖ ≤ ‖t - ∑ i, (c i : ℝ) • vv i‖ := hclose _ hgΛ
    have h2 : ‖t - χ'‖ ^ 2 ≤ ‖t - ∑ i, (c i : ℝ) • vv i‖ ^ 2 := by gcongr
    have h3 : (n : ℝ) * (B * ‖v‖) ^ 2 ≤ D * (B * ‖v‖) ^ 2 :=
      mul_le_mul_of_nonneg_right hnD (sq_nonneg _)
    rw [norm_sub_rev]
    linarith

  have hlast : ∀ u ∈ Xg L I, |2 * inner ℝ χ' u| ≤ ‖u‖ ^ 2 ∨ ‖v‖ ≤ ‖u‖ := by
    intro u hu
    by_cases huv : ‖v‖ ≤ ‖u‖
    · exact Or.inr huv
    left
    push_neg at huv
    have huΛ : u ∈ Λ := (hΛ u).2 ⟨hu, Zs_self L I hu huv.le⟩
    have h1 := hclose (χ' + u) (Λ.add_mem hχ'Λ huΛ)
    have h2 := hclose (χ' - u) (Λ.sub_mem hχ'Λ huΛ)
    have e1 : t - (χ' + u) = (t - χ') - u := by abel
    have e2 : t - (χ' - u) = (t - χ') + u := by abel
    rw [e1] at h1
    rw [e2] at h2
    have s1 : ‖t - χ'‖ ^ 2 ≤ ‖(t - χ') - u‖ ^ 2 := by gcongr
    have s2 : ‖t - χ'‖ ^ 2 ≤ ‖(t - χ') + u‖ ^ 2 := by gcongr
    rw [norm_sub_sq_real (t - χ') u] at s1
    rw [norm_add_sq_real (t - χ') u] at s2
    have hi : inner ℝ (t - χ') u = - inner ℝ χ' u := by
      rw [inner_sub_left, htorth u hu huv, zero_sub]
    rw [hi] at s1 s2
    rw [abs_le]; constructor <;> linarith
  exact ⟨t, χ', hWt, hnT, htn, ((hΛ χ').1 hχ'Λ).1, ((hΛ χ').1 hχ'Λ).2, hbound, hlast⟩

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ShortVectorBoundLeKappa
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem short_vector_bound_le_kappa [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) (hph : 0 < P.ph) :
    PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E) ≤ P.ka0 * P.ph := by
  unfold Par.ka0 Par.ph RR
  have hph' : 0 < X.ph (th P.q P.R0) := hph
  have hf1 : 1 ≤ PT.f E := le_trans (Nat.one_le_pow 4 P.m P.hm1) P.hmf
  have hm2 : P.m ^ 2 ≤ PT.f E := le_trans (Nat.pow_le_pow_right P.hm1 (by norm_num)) P.hmf
  have hF : (1 : ℝ) ≤ PT.f E := by exact_mod_cast hf1
  have hM2 : (P.m : ℝ) ^ 2 ≤ PT.f E := by exact_mod_cast hm2
  have hFR : (PT.f E : ℝ) ≤ PT.rd E := P.hfrd
  have hR : (16 : ℝ) ≤ PT.rd E := P.hrd
  have hM0 : (0 : ℝ) ≤ P.m := Nat.cast_nonneg _
  have hd : (dstar (E := E) P.m : ℝ) = 2 * (PT.f E : ℝ) * P.m := by unfold dstar; push_cast; ring
  rw [hd, div_le_iff₀ (by linarith)]
  have key1 : (PT.f E : ℝ) * (P.m : ℝ) ^ 2 ≤ PT.rd E ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hM2 (by linarith : (0 : ℝ) ≤ PT.f E),
      mul_le_mul hFR hFR (by linarith) (by linarith)]
  have h3 : PT.rd E ^ 4 * (PT.f E : ℝ) ≤ PT.rd E ^ 7 * PT.f E :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) (by norm_num)) (by linarith)
  have h4 := mul_le_mul_of_nonneg_left key1 (by positivity : (0 : ℝ) ≤ 4 * PT.rd E ^ 2 * PT.f E)
  have key2 : PT.rd E ^ 2 * (2 * (PT.f E : ℝ) * P.m) ^ 2 ≤ 8 * PT.rd E ^ 7 * PT.f E := by
    nlinarith [h3, h4, (by positivity : (0 : ℝ) ≤ PT.rd E ^ 7 * PT.f E)]
  have hd2 := mul_nonneg (sq_nonneg (2 * (PT.f E : ℝ) * P.m)) hph'.le
  nlinarith [mul_le_mul_of_nonneg_right key2 hd2]

theorem tof_inv_sqrt_le [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) (hph : 0 < P.ph) (n : ℕ)
    (hn : n ≤ dstar (E := E) P.m) (c : ℝ) (hc : 0 < c)
    (h1 : 1 ≤ c * Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) ^ n) :
    1 / Real.sqrt (c * (2 : ℝ) ^ (-(n : ℝ) / 2)) ≤
      Real.exp (dstar (E := E) P.m) * (P.ka0 * P.ph) ^ ((dstar (E := E) P.m : ℝ) / 4) := by
  have hU := short_vector_bound_le_kappa P hph
  have hf1 : 1 ≤ PT.f E := le_trans (Nat.one_le_pow 4 P.m P.hm1) P.hmf
  have hF : (1 : ℝ) ≤ PT.f E := by exact_mod_cast hf1
  have hR : (16 : ℝ) ≤ PT.rd E := P.hrd
  have hR0 : (0 : ℝ) < PT.rd E := by linarith
  have hdR : ((dstar (E := E) P.m : ℕ) : ℝ) = 2 * (PT.f E : ℝ) * P.m := by
    unfold dstar; push_cast; ring
  have hm1 : (1 : ℝ) ≤ P.m := by exact_mod_cast P.hm1
  have hd1 : (1 : ℝ) ≤ ((dstar (E := E) P.m : ℕ) : ℝ) := by rw [hdR]; nlinarith
  have hph2 := hph
  unfold Par.ph PT.ph at hph2
  split_ifs at hph2 with hlt
  swap
  · exact absurd hph2 (lt_irrefl 0)
  have hL0 : 0 ≤ X.la1 := by
    unfold PT.la1
    exact Real.sInf_nonneg (by rintro t ⟨x, -, -, rfl⟩; exact norm_nonneg x)
  have hla : 0 < X.la1 ^ 2 := by
    rcases (sq_nonneg X.la1).lt_or_eq with h | h
    · exact h
    · rw [← h] at hph2; simp at hph2
  have hC1 := P.C1
  have hom : (1 : ℝ) ≤ omStar (E := E) := by
    unfold omStar
    first
      | nlinarith [Real.one_le_rpow hF (by norm_num : (0 : ℝ) ≤ 3 / 2)]
      | nlinarith [one_le_pow₀ (n := 3 / 2) hF]
      | (norm_num; nlinarith)
  have hZ : (1 : ℝ) ≤ ((dstar (E := E) P.m : ℕ) : ℝ) ^ 2 * omStar (E := E) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hd1) hom
  have h2 := mul_self_lt_mul_self hL0 hlt
  have hth : X.la1 ^ 2 < 1 := by
    nlinarith [hC1, hZ, h2, mul_nonneg (sub_nonneg.mpr hZ) (lt_of_le_of_lt (mul_self_nonneg X.la1) h2).le]
  have hK1 : 1 ≤ P.ka0 * P.ph := by
    unfold Par.ka0 Par.ph PT.ph RR
    rw [if_pos hlt]
    have hden : PT.rd E ^ 2 * X.la1 ^ 2 ≠ 0 := (mul_pos (pow_pos hR0 2) hla).ne'
    have hY := div_mul_cancel₀ (2 * (PT.f E : ℝ)) hden
    set Y : ℝ := 2 * (PT.f E : ℝ) / (PT.rd E ^ 2 * X.la1 ^ 2) with hYd
    have hY0 : 0 < Y := hph2
    have h5 : 2 * (PT.f E : ℝ) ≤ Y * PT.rd E ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hth.le) (mul_pos hY0 (pow_pos hR0 2)).le]
    have h6 : (1 : ℝ) ≤ PT.rd E ^ 5 * ((dstar (E := E) P.m : ℕ) : ℝ) ^ 2 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (one_le_pow₀ hd1)
    nlinarith [mul_le_mul h6 h5 (by positivity) (by linarith)]
  set K : ℝ := P.ka0 * P.ph with hKd
  have hK0 : 0 ≤ K := by linarith
  have hsK : 1 ≤ √K := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hK1
  have e1 := by
    first
      | exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hU) n
      | exact pow_le_pow_left (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hU) n
  have e2 : √K ^ n ≤ √K ^ (dstar (E := E) P.m) := by
    first
      | exact pow_le_pow_right₀ hsK hn
      | exact pow_le_pow_right hsK hn
  have hcK : 1 ≤ c * √K ^ (dstar (E := E) P.m) :=
    h1.trans (mul_le_mul_of_nonneg_left (e1.trans e2) hc.le)
  have hpow : (K ^ (((dstar (E := E) P.m : ℕ) : ℝ) / 4)) ^ 2 = √K ^ (dstar (E := E) P.m) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_natCast (K ^ (1 / 2 : ℝ)),
      ← Real.rpow_mul hK0, ← Real.rpow_mul hK0]
    congr 1
    push_cast
    ring
  have hE : (1 : ℝ) ≤ Real.exp ((dstar (E := E) P.m : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (-(n : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul, ← Real.exp_add]
    refine le_trans ?_ (Real.add_one_le_exp _)
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hnd : (n : ℝ) ≤ ((dstar (E := E) P.m : ℕ) : ℝ) := by exact_mod_cast hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hl2 hn0]
  have hc2 : 0 < c * (2 : ℝ) ^ (-(n : ℝ) / 2) := mul_pos hc (Real.rpow_pos_of_pos (by norm_num) _)
  have hA : 0 < √(c * (2 : ℝ) ^ (-(n : ℝ) / 2)) := Real.sqrt_pos.mpr hc2
  rw [div_le_iff₀ hA]
  have hx0 : 0 ≤ Real.exp ((dstar (E := E) P.m : ℕ) : ℝ) * K ^ (((dstar (E := E) P.m : ℕ) : ℝ) / 4) *
      √(c * (2 : ℝ) ^ (-(n : ℝ) / 2)) :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hK0 _)) (Real.sqrt_nonneg _)
  have hsq : (Real.exp ((dstar (E := E) P.m : ℕ) : ℝ) * K ^ (((dstar (E := E) P.m : ℕ) : ℝ) / 4) *
      √(c * (2 : ℝ) ^ (-(n : ℝ) / 2))) ^ 2 =
      (c * √K ^ (dstar (E := E) P.m)) *
        (Real.exp ((dstar (E := E) P.m : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (-(n : ℝ) / 2)) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hc2.le, hpow]
    ring
  have hge := one_le_mul_of_one_le_of_one_le hcK hE
  rw [← hsq] at hge
  nlinarith [hge, hx0]

end

end ReciprocityTheory.ChartRestriction.G.I2
end

