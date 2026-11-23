module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0012

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofFinrankIRLe
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem tof_shell_term (d k : ℕ) (hd : 2 ≤ d) :
    (3 * ((k : ℝ) + 1)) ^ d * Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) ≤
      (3 * (d : ℝ)) ^ d * (Real.exp (-1) * Real.exp (1 - Real.pi / 2) ^ k) := by
  have hpi := Real.pi_gt_three
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hE : Real.exp (-1) * Real.exp (1 - Real.pi / 2) ^ k =
      Real.exp (-1 + k * (1 - Real.pi / 2)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
  rw [hE]
  have key : (3 * ((k : ℝ) + 1)) ^ d ≤
      (3 * (d : ℝ)) ^ d * Real.exp (Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2))) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk
    · subst hk0
      have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have hdd : (4 : ℝ) ≤ (d : ℝ) ^ d := by
        calc (4 : ℝ) = 2 ^ 2 := by norm_num
          _ ≤ (d : ℝ) ^ 2 := by gcongr
          _ ≤ (d : ℝ) ^ d := pow_le_pow_right₀ (by linarith) hd
      have hQ : Real.pi / 2 * ((0 : ℕ) : ℝ) ^ 2 + (-1 + ((0 : ℕ) : ℝ) * (1 - Real.pi / 2)) = -1 := by
        simp
      rw [hQ, Real.exp_neg]
      have h1 : (1 : ℝ) ≤ (d : ℝ) ^ d * (Real.exp 1)⁻¹ := by
        rw [le_mul_inv_iff₀ (Real.exp_pos 1)]
        linarith
      calc (3 * (((0 : ℕ) : ℝ) + 1)) ^ d = 3 ^ d * 1 := by simp
        _ ≤ 3 ^ d * ((d : ℝ) ^ d * (Real.exp 1)⁻¹) := by gcongr
        _ = (3 * (d : ℝ)) ^ d * (Real.exp 1)⁻¹ := by rw [mul_pow]; ring
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      by_cases hkd : k + 1 ≤ d
      · have hkd' : (k : ℝ) + 1 ≤ d := by exact_mod_cast hkd
        have h1 : (3 * ((k : ℝ) + 1)) ^ d ≤ (3 * (d : ℝ)) ^ d :=
          pow_le_pow_left₀ (by positivity) (by linarith) d
        have h2 : 0 ≤ Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2)) := by
          nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ Real.pi / 2)
            (by linarith : (0 : ℝ) ≤ k)) (by linarith : (0 : ℝ) ≤ k - 1)]
        calc (3 * ((k : ℝ) + 1)) ^ d ≤ (3 * (d : ℝ)) ^ d := h1
          _ ≤ _ := le_mul_of_one_le_right (by positivity) (Real.one_le_exp h2)
      · have hdk : (d : ℝ) ≤ k := by exact_mod_cast (by omega : d ≤ k)
        have hk2 : (2 : ℝ) ≤ k := le_trans hd' hdk
        have h1 : ((k : ℝ) + 1) ^ d ≤ Real.exp ((k : ℝ) * k) := by
          calc ((k : ℝ) + 1) ^ d ≤ (Real.exp k) ^ d :=
                pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (k : ℝ)]) d
            _ = Real.exp (d * k) := by rw [← Real.exp_nat_mul]
            _ ≤ Real.exp (k * k) := Real.exp_le_exp.mpr (by nlinarith)
        have h2 : (k : ℝ) * k ≤ Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2)) := by
          have hkk : 2 ≤ (k : ℝ) * ((k : ℝ) - 1) := by nlinarith
          have hpp : (1 : ℝ) / 2 ≤ Real.pi / 2 - 1 := by linarith
          nlinarith [mul_le_mul hpp hkk (by norm_num) (by linarith)]
        have h3 : (1 : ℝ) ≤ (d : ℝ) ^ d := one_le_pow₀ (by linarith)
        calc (3 * ((k : ℝ) + 1)) ^ d = 3 ^ d * ((k : ℝ) + 1) ^ d := mul_pow _ _ _
          _ ≤ 3 ^ d * Real.exp (Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2))) := by
            gcongr
            exact h1.trans (Real.exp_le_exp.mpr h2)
          _ ≤ 3 ^ d * ((d : ℝ) ^ d *
              Real.exp (Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2)))) := by
            gcongr
            exact le_mul_of_one_le_left (Real.exp_pos _).le h3
          _ = _ := by rw [mul_pow]; ring
  have hexp : Real.exp (Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2))) *
      Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) = Real.exp (-1 + k * (1 - Real.pi / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc _ ≤ (3 * (d : ℝ)) ^ d * Real.exp (Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2))) *
        Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right key (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, hexp]

theorem tof_shell_sum (d K : ℕ) (hd : 2 ≤ d) :
    ∑ k ∈ Finset.range K, (3 * ((k : ℝ) + 1)) ^ d * Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) ≤
      2 * (3 * (d : ℝ)) ^ d := by
  set r := Real.exp (1 - Real.pi / 2) with hr
  have hpi := Real.pi_gt_three
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r ≤ 2 / 3 := by
    have h := Real.add_one_le_exp (Real.pi / 2 - 1)
    have hrr : r * Real.exp (Real.pi / 2 - 1) = 1 := by
      rw [hr, ← Real.exp_add]
      simp
    nlinarith
  have he1 : Real.exp (-1) ≤ 1 / 2 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    have hrr : Real.exp (-1) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]
      simp
    have := Real.exp_pos (-1)
    nlinarith
  have hsum0 : 0 ≤ ∑ k ∈ Finset.range K, r ^ k := Finset.sum_nonneg (fun k _ => pow_nonneg hr0.le k)
  have hS : ∑ k ∈ Finset.range K, r ^ k ≤ 3 := by
    have h := geom_sum_mul r K
    have : 0 ≤ r ^ K := by positivity
    nlinarith
  have hd0 : (0 : ℝ) ≤ (3 * (d : ℝ)) ^ d := by positivity
  calc ∑ k ∈ Finset.range K, (3 * ((k : ℝ) + 1)) ^ d * Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2)
      ≤ ∑ k ∈ Finset.range K, (3 * (d : ℝ)) ^ d * (Real.exp (-1) * r ^ k) :=
        Finset.sum_le_sum (fun k _ => tof_shell_term d k hd)
    _ = (3 * (d : ℝ)) ^ d * Real.exp (-1) * ∑ k ∈ Finset.range K, r ^ k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        ring
    _ ≤ (3 * (d : ℝ)) ^ d * (1 / 2) * 3 := by gcongr
    _ ≤ 2 * (3 * (d : ℝ)) ^ d := by nlinarith

theorem tof_uMap_sep [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) {x x' : Vsp X.dim} (hx : x ∈ X.L) (hx' : x' ∈ X.L)
    (hne : uMap I x ≠ uMap I x') : 1 ≤ ‖uMap I x - uMap I x'‖ := by
  have hsub : uMap I x - uMap I x' = uMap I (x - x') := (map_sub (uMap I) x x').symm
  have hne' : uMap I (x - x') ≠ 0 := by
    rw [← hsub]
    exact sub_ne_zero.mpr hne
  have hb := hI.sep (x - x') (X.L.sub_mem hx hx') (uMap I (x - x')) (isU_uMap I (x - x')) hne'
  have h1 : (1 : ℝ) ≤ ‖uMap I (x - x')‖ ^ 2 := le_trans P.C2 hb
  rw [hsub]
  by_contra hlt
  have hlt' : ‖uMap I (x - x')‖ < 1 := lt_of_not_ge hlt
  have h0 := norm_nonneg (uMap I (x - x'))
  nlinarith

theorem tof_finrank_IR_le [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) : Module.finrank ℝ (IR I) ≤ dstar (E := E) P.m := by
  obtain ⟨ρ, hρ, h⟩ := hI.rank
  rw [h]
  unfold dstar
  exact Nat.mul_le_mul_left _ hρ

theorem tof_two_le_dstar {X : PT E} {DF : ℕ} (P : Par X DF) : 2 ≤ dstar (E := E) P.m := by
  have h1 : 1 ≤ PT.f E := le_trans (Nat.one_le_pow _ _ P.hm1) P.hmf
  have h2 := P.hm1
  unfold dstar
  calc 2 = 2 * 1 * 1 := by norm_num
    _ ≤ 2 * PT.f E * P.m := by gcongr

theorem tof_sep_sum [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hP : Ext.PackingCount) (u : Vsp X.dim) (hu : u ∈ IR I)
    (F : Finset (Vsp X.dim)) (hF : ∀ y ∈ F, ∃ x ∈ X.L, y = uMap I x) :
    ∑ y ∈ F, Real.exp (-(Real.pi / 2) * ‖u - y‖ ^ 2) ≤
      2 * (3 * (dstar (E := E) P.m : ℝ)) ^ dstar (E := E) P.m := by
  classical
  set d := dstar (E := E) P.m with hd
  have hd2 : 2 ≤ d := tof_two_le_dstar P
  have hDd : Module.finrank ℝ (IR I) ≤ d := tof_finrank_IR_le P hI
  have hyR : ∀ y ∈ F, y ∈ IR I := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hF y hy
    exact (IR I).starProjection_apply_mem _
  let e := (stdOrthonormalBasis ℝ (IR I)).repr
  let g : Vsp X.dim → EuclideanSpace ℝ (Fin (Module.finrank ℝ (IR I))) := fun y =>
    e ⟨(IR I).starProjection (y - u), (IR I).starProjection_apply_mem _⟩
  have hproj : ∀ y ∈ F, (IR I).starProjection (y - u) = y - u := fun y hy =>
    (Submodule.starProjection_eq_self_iff).mpr ((IR I).sub_mem (hyR y hy) hu)
  have hgn : ∀ y ∈ F, ‖g y‖ = ‖u - y‖ := by
    intro y hy
    simp only [g, LinearIsometryEquiv.norm_map, Submodule.coe_norm, hproj y hy]
    rw [norm_sub_rev]
  have hgd : ∀ y ∈ F, ∀ y' ∈ F, dist (g y) (g y') = ‖y - y'‖ := by
    intro y hy y' hy'
    rw [dist_eq_norm]
    simp only [g, ← map_sub, LinearIsometryEquiv.norm_map]
    simp only [Submodule.coe_norm, Submodule.coe_sub, hproj y hy, hproj y' hy']
    congr 1
    abel
  have hsep : ∀ y ∈ F, ∀ y' ∈ F, y ≠ y' → 1 ≤ ‖y - y'‖ := by
    intro y hy y' hy' hne
    obtain ⟨x, hx, rfl⟩ := hF y hy
    obtain ⟨x', hx', rfl⟩ := hF y' hy'
    exact tof_uMap_sep P hI hx hx' hne
  set K := (F.sup fun y => ⌊‖u - y‖⌋₊) + 1 with hK
  have hmaps : ∀ y ∈ F, ⌊‖u - y‖⌋₊ ∈ Finset.range K := by
    intro y hy
    rw [Finset.mem_range, hK]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun y => ⌊‖u - y‖⌋₊) hy)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine le_trans (Finset.sum_le_sum (fun k _ => ?_)) (tof_shell_sum d K hd2)
  set Fk := F.filter (fun y => ⌊‖u - y‖⌋₊ = k) with hFk
  have hFkF : ∀ y ∈ Fk, y ∈ F := fun y hy => (Finset.mem_filter.mp hy).1
  have hterm : ∀ y ∈ Fk, Real.exp (-(Real.pi / 2) * ‖u - y‖ ^ 2) ≤
      Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) := by
    intro y hy
    have hk : ⌊‖u - y‖⌋₊ = k := (Finset.mem_filter.mp hy).2
    have hle : (k : ℝ) ≤ ‖u - y‖ := by
      rw [← hk]
      exact Nat.floor_le (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    have : (k : ℝ) ^ 2 ≤ ‖u - y‖ ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg k) hle 2
    nlinarith [Real.pi_pos]
  have hinj : Set.InjOn g Fk := by
    intro y hy y' hy' hgg
    by_contra hne
    have h1 := hsep y (hFkF y hy) y' (hFkF y' hy') hne
    have h2 := hgd y (hFkF y hy) y' (hFkF y' hy')
    rw [hgg, dist_self] at h2
    linarith
  have hcard : (Fk.card : ℝ) ≤ (3 * ((k : ℝ) + 1)) ^ Module.finrank ℝ (IR I) := by
    rw [← Finset.card_image_of_injOn hinj]
    have hpk := hP (Module.finrank ℝ (IR I)) (Fk.image g) 1 ((k : ℝ) + 1) one_pos
      (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
      (by
        intro p hp
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
        rw [hgn y (hFkF y hy)]
        have hk : ⌊‖u - y‖⌋₊ = k := (Finset.mem_filter.mp hy).2
        rw [← hk]
        exact (Nat.lt_floor_add_one _).le)
      (by
        intro p hp p' hp' hne
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
        obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hp'
        rw [hgd y (hFkF y hy) y' (hFkF y' hy')]
        exact hsep y (hFkF y hy) y' (hFkF y' hy') (fun h => hne (by rw [h])))
    simpa using hpk
  calc ∑ y ∈ Fk, Real.exp (-(Real.pi / 2) * ‖u - y‖ ^ 2)
      ≤ ∑ y ∈ Fk, Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) := Finset.sum_le_sum hterm
    _ = (Fk.card : ℝ) * Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 * ((k : ℝ) + 1)) ^ Module.finrank ℝ (IR I) * Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) := by
        gcongr
    _ ≤ (3 * ((k : ℝ) + 1)) ^ d * Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) := by
        gcongr
        · have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          linarith

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofUMapSqSmul
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E]

def PerFactor {X : PT E} {DF : ℕ} (P : Par X DF) (I : Submodule ℤ (Vsp X.dim))
    (s : (Fin 1 → Vsp X.dim) → ℂ) : Prop :=
  ∀ w : Vsp X.dim, ∃ y ∈ X.L, Real.sqrt (X.ptN2 1 s fun _ => w) / Real.sqrt (X.l2 1 s) ≤
    Real.exp (P.p1 + P.p2 + dstar (E := E) P.m) *
      (P.ka0 * P.ph) ^ ((dstar (E := E) P.m : ℝ) / 4) *
        Real.exp (-(Real.pi / 2) * ‖uMap I w - uMap I y‖ ^ 2)

theorem Par_ka0_nonneg {X : PT E} {DF : ℕ} (P : Par X DF) : 0 ≤ P.ka0 := by
  have h : (0 : ℝ) ≤ PT.rd E := by linarith [P.hrd]
  have hR : (0 : ℝ) ≤ RR (E := E) := by
    unfold RR
    exact pow_nonneg h 7
  unfold Par.ka0
  exact mul_nonneg (mul_nonneg (by norm_num) hR) (sq_nonneg _)

theorem tof_uMap_sq_smul {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) (r1 : ℕ) (a y : Vsp dim) :
    ‖uMap I (((r1 : ℂ) ^ 2) • a - ((r1 : ℂ) ^ 2) • y)‖ ^ 2 =
      (r1 : ℝ) ^ 4 * ‖uMap I a - uMap I y‖ ^ 2 := by
  have h : ((r1 : ℂ) ^ 2) • a - ((r1 : ℂ) ^ 2) • y = ((r1 : ℝ) ^ 2) • (a - y) := by
    first
    | (rw [← smul_sub, ← Complex.coe_smul, Complex.ofReal_pow, Complex.ofReal_natCast])
    | (rw [← smul_sub]; norm_cast)
    | (rw [← smul_sub, ← Complex.coe_smul]; push_cast; rfl)
  rw [h, map_smul, map_sub, norm_smul, mul_pow, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  ring

theorem t_assemble [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hpf : PerFactor P I s)
    (r1 : ℕ) (hr1 : 2 ≤ r1) (a : Fin X.r → Vsp X.dim) (ha : ∀ j, ((r1 : ℂ) ^ 2) • a j ∈ X.L)
    (hgen : ∀ x ∈ X.L, ∃ c : Fin X.r → 𝓞 E, ∃ y ∈ X.L,
      x = ∑ j, act (c j) (((r1 : ℂ) ^ 2) • a j) + (r1 : ℂ) • y) (hph : 0 < P.ph) :
    ∏ j, Real.sqrt (X.ptN2 1 s fun _ => a j) / Real.sqrt (X.l2 1 s) ≤
      Real.exp P.p3 * (P.ka0 * P.ph) ^ ((X.r * dstar (E := E) P.m : ℝ) / 4) *
        Real.exp (-(Real.pi * P.ph / (r1 : ℝ) ^ 4)) := by
  choose y hyL hb using fun j => hpf (a j)
  set C : ℝ := Real.exp (P.p1 + P.p2 + dstar (E := E) P.m) *
      (P.ka0 * P.ph) ^ ((dstar (E := E) P.m : ℝ) / 4) with hC
  set D : Fin X.r → ℝ := fun j => ‖uMap I (a j) - uMap I (y j)‖ ^ 2 with hD
  have hkp : 0 ≤ P.ka0 * P.ph := mul_nonneg (Par_ka0_nonneg P) hph.le
  have h1 : ∏ j, Real.sqrt (X.ptN2 1 s fun _ => a j) / Real.sqrt (X.l2 1 s) ≤
      ∏ j, (C * Real.exp (-(Real.pi / 2) * D j)) :=
    Finset.prod_le_prod₀ (fun j _ => by positivity) (fun j _ => hb j)
  have h2 : ∏ j, (C * Real.exp (-(Real.pi / 2) * D j)) =
      C ^ X.r * Real.exp (-(Real.pi / 2) * ∑ j, D j) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_sum, Finset.mul_sum]
  have h3 : C ^ X.r = Real.exp P.p3 * (P.ka0 * P.ph) ^ ((X.r * dstar (E := E) P.m : ℝ) / 4) := by
    rw [hC, mul_pow, ← Real.exp_nat_mul, ← Real.rpow_natCast ((P.ka0 * P.ph) ^ _),
      ← Real.rpow_mul hkp, Par.p3]
    congr 2; ring

  set xb : Fin X.r → Vsp X.dim := fun j => ((r1 : ℂ) ^ 2) • a j - ((r1 : ℂ) ^ 2) • y j with hxb
  have hxL : ∀ j, xb j ∈ X.L ∧ IsU I (xb j) (uMap I (xb j)) := by
    intro j
    refine ⟨X.L.sub_mem (ha j) ?_, isU_uMap I _⟩
    have : ((r1 : ℂ) ^ 2) • y j = (r1 ^ 2 : ℕ) • y j := by
      rw [← Nat.cast_smul_eq_nsmul ℂ]; push_cast; rfl
    rw [this]; exact X.L.nsmul_mem (hyL j) _
  have hspan := tof_span_condition (X := X) I r1 hr1 a y hyL hgen
  have hu2 := hI.u2 X.r xb (fun j => uMap I (xb j)) hxL hspan
  have hsum : ∑ j, ‖uMap I (xb j)‖ ^ 2 / 2 = (r1 : ℝ) ^ 4 / 2 * ∑ j, D j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hxb]; dsimp only
    rw [tof_uMap_sq_smul]; ring
  rw [hsum] at hu2
  have hr4 : (0 : ℝ) < (r1 : ℝ) ^ 4 := by
    have : (0 : ℝ) < r1 := by exact_mod_cast (by omega : 0 < r1)
    positivity
  have h4 : Real.exp (-(Real.pi / 2) * ∑ j, D j) ≤ Real.exp (-(Real.pi * P.ph / (r1 : ℝ) ^ 4)) := by
    apply Real.exp_le_exp.2
    have : Real.pi * P.ph / (r1 : ℝ) ^ 4 ≤ Real.pi / 2 * ∑ j, D j := by
      rw [div_le_iff₀ hr4]
      have := mul_le_mul_of_nonneg_left hu2 Real.pi_pos.le
      nlinarith
    linarith
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ C ^ X.r * Real.exp (-(Real.pi * P.ph / (r1 : ℝ) ^ 4)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by rw [h3]

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtDataPf
section
namespace ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem sum_castLE_eq {n : ℕ} (h : n ≤ r) (g : Fin r → ℝ) :
    ∑ a : Fin n, g (Fin.castLE h a) = ∑ b ∈ Finset.univ.filter (fun b : Fin r => (b : ℕ) < n), g b := by
  classical
  refine Finset.sum_bij (fun a _ => Fin.castLE h a) (fun a _ => by simp) (fun a _ b _ hab => Fin.castLE_injective h hab)
    (fun b hb => ⟨⟨b, by simpa using hb⟩, Finset.mem_univ _, Fin.ext rfl⟩) (fun a _ => rfl)

theorem sum_shift_eq {n m : ℕ} (hn : n ≤ r) (hm : m = r - n) (g : Fin r → ℝ) (f : Fin m → Fin r)
    (hf : ∀ a, (f a : ℕ) = n + a) :
    ∑ a : Fin m, g (f a) = ∑ b ∈ Finset.univ.filter (fun b : Fin r => ¬ (b : ℕ) < n), g b := by
  classical
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 := congrArg Fin.val hab
    rw [hf, hf] at h1
    exact Fin.ext (by omega)
  refine Finset.sum_bij (fun a _ => f a) (fun a _ => by simp [hf]) (fun a _ b _ hab => hinj hab)
    (fun b hb => ?_) (fun a _ => rfl)
  have hb' : ¬ (b : ℕ) < n := by simpa using hb
  refine ⟨⟨b - n, by have := b.isLt; omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
  rw [hf]
  simp only
  omega

theorem conj_conj_X (φ : E →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ :=
  star_star φ

theorem cols_linInd (X : Data E r) (x : Frame X.Ψ r) (A : TorusAt X x) (τ : X.Ψ) :
    LinearIndependent ℂ (X.colP x τ) := by
  have h := A.e_flag τ r le_rfl
  have h1 : (fun a : Fin r => A.e τ (Fin.castLE le_rfl a)) = A.e τ := funext fun a => rfl
  have h2 : (fun a : Fin r => col (mat x τ) (Fin.castLE le_rfl a)) = fun a => col (mat x τ) a :=
    funext fun a => rfl
  rw [h1, h2, e_span X τ (A.e τ) (A.e_orth τ)] at h
  have hcols : LinearIndependent ℂ (fun a : Fin r => col (mat x τ) a) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank h.le (by simp)
  exact hcols.comp _ (Fin.castLE_injective X.p0_le)

theorem norm_sq_eq (X : Data E r) (x : Frame X.Ψ r) (A : TorusAt X x) (v : Fin r → E) :
    ‖A.φ v‖ ^ 2 = ∑ τ : X.Ψ, X.c τ * X.maj x τ (Data.emb τ.1 v) := by
  classical
  have hc : ∀ τ : X.Ψ, 0 ≤ X.c τ := fun τ => by unfold Data.c; positivity
  have hmaj : ∀ τ : X.Ψ, X.maj x τ (Data.emb τ.1 v) =
      ∑ b : Fin r, ‖hermC τ.1 X.Gm (Data.emb τ.1 v) (A.e τ b)‖ ^ 2 := fun τ =>
    maj_eq_sum X τ (A.e τ) (A.e_orth τ) x (A.e_flag τ X.p0 X.p0_le) (cols_linInd X x A τ) _
  let F : (E →+* ℂ) → ℝ := fun σ => ∑ a : Fin (A.T.dim σ), ‖A.φ v ⟨σ, a⟩‖ ^ 2
  have hpos : ∀ τ : X.Ψ, F τ.1 = X.c τ * ∑ b ∈ Finset.univ.filter (fun b : Fin r => (b : ℕ) < X.p0),
      ‖hermC τ.1 X.Gm (Data.emb τ.1 v) (A.e τ b)‖ ^ 2 := by
    intro τ
    have hle : A.T.dim τ.1 ≤ r := by rw [A.dim_pos τ]; exact X.p0_le
    have e1 : ∀ a : Fin (A.T.dim τ.1), ‖A.φ v ⟨τ.1, a⟩‖ ^ 2 =
        X.c τ * ‖hermC τ.1 X.Gm (Data.emb τ.1 v) (A.e τ (Fin.castLE hle a))‖ ^ 2 := by
      intro a
      rw [A.coord_pos τ a v, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (hc τ)]
    show ∑ a : Fin (A.T.dim τ.1), ‖A.φ v ⟨τ.1, a⟩‖ ^ 2 = _
    rw [Finset.sum_congr rfl fun a _ => e1 a, ← Finset.mul_sum,
      sum_castLE_eq hle (fun b => ‖hermC τ.1 X.Gm (Data.emb τ.1 v) (A.e τ b)‖ ^ 2), A.dim_pos τ]
  have hneg : ∀ τ : X.Ψ, F (ComplexEmbedding.conjugate τ.1) =
      X.c τ * ∑ b ∈ Finset.univ.filter (fun b : Fin r => ¬ (b : ℕ) < X.p0),
        ‖hermC τ.1 X.Gm (Data.emb τ.1 v) (A.e τ b)‖ ^ 2 := by
    intro τ
    have hlt : ∀ a : Fin (A.T.dim (ComplexEmbedding.conjugate τ.1)), X.p0 + a.1 < r := by
      intro a
      have h1 : a.1 < r - X.p0 := lt_of_lt_of_eq a.2 (A.dim_neg τ)
      have := X.p0_le
      omega
    have e1 : ∀ a : Fin (A.T.dim (ComplexEmbedding.conjugate τ.1)),
        ‖A.φ v ⟨ComplexEmbedding.conjugate τ.1, a⟩‖ ^ 2 =
          X.c τ * ‖hermC τ.1 X.Gm (Data.emb τ.1 v) (A.e τ ⟨X.p0 + a.1, hlt a⟩)‖ ^ 2 := by
      intro a
      rw [A.coord_neg τ a v, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (hc τ), Complex.norm_conj, norm_neg]
    show ∑ a : Fin (A.T.dim (ComplexEmbedding.conjugate τ.1)),
      ‖A.φ v ⟨ComplexEmbedding.conjugate τ.1, a⟩‖ ^ 2 = _
    rw [Finset.sum_congr rfl fun a _ => e1 a, ← Finset.mul_sum]
    congr 1
    exact sum_shift_eq X.p0_le (A.dim_neg τ) (fun b => ‖hermC τ.1 X.Gm (Data.emb τ.1 v) (A.e τ b)‖ ^ 2)
      (fun a => ⟨X.p0 + a.1, hlt a⟩) (fun a => rfl)
  have hsplit : ∑ σ, F σ = ∑ τ : X.Ψ, (F τ.1 + F (ComplexEmbedding.conjugate τ.1)) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun σ => σ ∈ X.Ψ)]
    have hfilt : Finset.univ.filter (fun σ => σ ∈ X.Ψ) = X.Ψ := by ext; simp
    have hcomp : ∑ σ ∈ Finset.univ.filter (fun σ => σ ∉ X.Ψ), F σ =
        ∑ τ ∈ X.Ψ, F (ComplexEmbedding.conjugate τ) := by
      refine Finset.sum_nbij' (fun σ => ComplexEmbedding.conjugate σ)
        (fun τ => ComplexEmbedding.conjugate τ) ?_ ?_ ?_ ?_ ?_
      · intro σ hσ
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
        rw [X.cmType, conj_conj_X]
        exact hσ
      · intro τ hτ
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
        exact (X.cmType τ).mp hτ
      · intro σ _; exact conj_conj_X σ
      · intro τ _; exact conj_conj_X τ
      · intro σ _; rw [conj_conj_X]
    rw [hfilt, hcomp, ← Finset.sum_add_distrib,
      ← Finset.sum_coe_sort X.Ψ (fun σ => F σ + F (ComplexEmbedding.conjugate σ))]
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sigma]
  show ∑ σ, F σ = _
  rw [hsplit]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [hpos τ, hneg τ, hmaj τ, ← mul_add, Finset.sum_filter_add_sum_filter_not]

theorem torusAtIs_holds : TorusAtIsStatement := by
  intro E _ _ _ r X x A
  exact ⟨A.φ, A.sg, A.sg_pm, A.lat, A.act_eq, fun v _ => norm_sq_eq X x A v, A.im_eq⟩

end ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
end

