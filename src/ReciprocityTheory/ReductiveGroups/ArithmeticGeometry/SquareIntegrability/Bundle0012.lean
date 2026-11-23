module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofSpanCondition
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex NumberField

noncomputable section

variable {E : Type} [Field E] [NumberField E]

def uMap {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) : Vsp dim →ₗ[ℝ] Vsp dim :=
  (IR I).starProjection.toLinearMap ∘ₗ
    (((-Complex.I) • LinearMap.id : Vsp dim →ₗ[ℂ] Vsp dim).restrictScalars ℝ)

theorem tof_re_inner_negI {ι : Type} [Fintype ι] (a x : EuclideanSpace ℂ ι) :
    inner ℝ a ((-Complex.I) • x) = (Hf x a).im := by
  simp only [real_inner_eq_re_inner ℂ, PiLp.inner_apply, Hf, Complex.re_sum, Complex.im_sum,
    PiLp.smul_apply, smul_eq_mul, RCLike.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re, Complex.mul_im]

theorem isU_uMap {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) (x : Vsp dim) :
    IsU I x (uMap I x) := by
  refine ⟨(IR I).starProjection_apply_mem _, fun a ha => ?_⟩
  show inner ℝ ((IR I).starProjection ((-Complex.I) • x)) a = (Hf x a).im
  have h0 := Submodule.starProjection_inner_eq_zero (K := IR I) ((-Complex.I) • x) a ha
  rw [inner_sub_left, sub_eq_zero] at h0
  rw [← h0, real_inner_comm]
  exact tof_re_inner_negI a x

theorem tof_act_add {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (v w : Vsp dim) :
    act α (v + w) = act α v + act α w := by
  ext i
  simp [act, mul_add]

theorem tof_act_smul {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (c : ℂ) (v : Vsp dim) :
    act α (c • v) = c • act α v := by
  ext i
  simp [act]
  ring

theorem tof_fg_div_eq_bot {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
    (M : Submodule ℤ Q) (hM : M.FG)
    (r : ℕ) (hr : 2 ≤ r) (hdiv : ∀ m ∈ M, ∃ m' ∈ M, m = r • m') : M = ⊥ := by
  obtain ⟨a, ha1, ha⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    (Ideal.span {(r : ℤ)}) M hM (by
      intro m hm
      obtain ⟨m', hm', rfl⟩ := hdiv m hm
      rw [← Nat.cast_smul_eq_nsmul ℤ]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hm')
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Ideal.mem_span_singleton] at ha1
    have h1 : (r : ℤ) ∣ 1 := by simpa using ha1
    have h2 := Int.eq_one_of_dvd_one (by positivity) h1
    omega
  rw [eq_bot_iff]
  intro m hm
  have h := ha m hm
  rw [← Int.cast_smul_eq_zsmul ℝ] at h
  rw [Submodule.mem_bot]
  exact (smul_eq_zero.mp h).resolve_left (by exact_mod_cast ha0)

theorem tof_span_condition [IsCMField E] {X : PT E} (I : Submodule ℤ (Vsp X.dim)) (r1 : ℕ) (hr1 : 2 ≤ r1)
    (a yb : Fin X.r → Vsp X.dim) (hyb : ∀ j, yb j ∈ X.L)
    (hgen : ∀ x ∈ X.L, ∃ c : Fin X.r → 𝓞 E, ∃ y ∈ X.L,
      x = ∑ j, act (c j) (((r1 : ℂ) ^ 2) • a j) + (r1 : ℂ) • y) :
    Submodule.span ℝ {w | ∃ j, ∃ α : 𝓞 E,
      IsU I (act α (((r1 : ℂ) ^ 2) • a j - ((r1 : ℂ) ^ 2) • yb j)) w} = IR I := by
  have huniq : ∀ x w, IsU I x w → w = uMap I x := by
    rintro x w ⟨hw, hwa⟩
    have hu := isU_uMap I x
    have hd : w - uMap I x ∈ IR I := (IR I).sub_mem hw hu.1
    have horth : ∀ b ∈ IR I, inner ℝ (w - uMap I x) b = 0 := fun b hb => by
      rw [inner_sub_left, hwa b hb, hu.2 b hb, sub_self]
    exact sub_eq_zero.mp (inner_self_eq_zero (𝕜 := ℝ).mp (horth _ hd))
  have hset : {w | ∃ j, ∃ α : 𝓞 E, IsU I (act α (((r1 : ℂ) ^ 2) • a j - ((r1 : ℂ) ^ 2) • yb j)) w} =
      Set.range (fun p : Fin X.r × 𝓞 E =>
        uMap I (act p.2 (((r1 : ℂ) ^ 2) • a p.1 - ((r1 : ℂ) ^ 2) • yb p.1))) := by
    ext w
    constructor
    · rintro ⟨j, α, h⟩
      exact ⟨(j, α), (huniq _ _ h).symm⟩
    · rintro ⟨⟨j, α⟩, rfl⟩
      exact ⟨j, α, isU_uMap I _⟩
  set T : Submodule ℝ (Vsp X.dim) := Submodule.span ℝ (Set.range fun p : Fin X.r × 𝓞 E =>
    act p.2 (((r1 : ℂ) ^ 2) • a p.1 - ((r1 : ℂ) ^ 2) • yb p.1)) with hT
  let f0 : Vsp X.dim →ₗ[ℝ] Vsp X.dim := LinearMap.id - (T.starProjection : Vsp X.dim →ₗ[ℝ] Vsp X.dim)
  have hf0T : ∀ v ∈ T, f0 v = 0 := fun v hv => by
    have h := Submodule.starProjection_mem_subspace_eq_self (K := T) ⟨v, hv⟩
    show v - T.starProjection v = 0
    rw [show ((⟨v, hv⟩ : T) : Vsp X.dim) = v from rfl] at h
    rw [h, sub_self]
  have hf0inv : ∀ v, f0 v = 0 → v ∈ T := fun v hv => by
    have h : v - T.starProjection v = 0 := hv
    rw [sub_eq_zero.mp h]
    exact T.starProjection_apply_mem v
  let f : Vsp X.dim →ₗ[ℤ] Vsp X.dim := f0.toAddMonoidHom.toIntLinearMap
  have hsq : ∀ z : Vsp X.dim, ((r1 : ℂ) ^ 2) • z = r1 • r1 • z := fun z => by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul ℂ, sq, mul_smul]
  have hLfg : X.L.FG := Submodule.fg_span (Set.finite_range X.b)
  have hM := tof_fg_div_eq_bot (X.L.map f) (hLfg.map f) r1 hr1 (by
    rintro m ⟨x, hx, rfl⟩
    obtain ⟨c, y, hy, hxe⟩ := hgen x hx
    refine ⟨f (y + ∑ j, r1 • act (c j) (yb j)),
      ⟨_, X.L.add_mem hy (X.L.sum_mem fun j _ => nsmul_mem (X.stable _ _ (hyb j)) r1), rfl⟩, ?_⟩
    have e1 : ∀ j, act (c j) (((r1 : ℂ) ^ 2) • a j) =
        act (c j) (((r1 : ℂ) ^ 2) • a j - ((r1 : ℂ) ^ 2) • yb j) + r1 • r1 • act (c j) (yb j) := by
      intro j
      rw [← hsq, ← tof_act_smul, ← tof_act_add, sub_add_cancel]
    have hz : ∀ j, f (act (c j) (((r1 : ℂ) ^ 2) • a j - ((r1 : ℂ) ^ 2) • yb j)) = 0 := fun j =>
      hf0T _ (Submodule.subset_span ⟨(j, c j), rfl⟩)
    rw [hxe]
    simp_rw [e1]
    rw [Finset.sum_add_distrib, Nat.cast_smul_eq_nsmul ℂ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_nsmul, hz, Finset.sum_const_zero, zero_add, smul_add, Finset.smul_sum]
    abel)
  have hLT : ∀ x ∈ X.L, x ∈ T := fun x hx => hf0inv x (by
    have h : f x ∈ X.L.map f := ⟨x, hx, rfl⟩
    rw [hM] at h
    exact (Submodule.mem_bot ℤ).mp h)
  have hTtop : T = ⊤ := by
    rw [eq_top_iff, ← X.b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hLT _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [hset]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact (isU_uMap I _).1
  · intro v hv
    have hv' : uMap I (Complex.I • v) = v := by
      show (IR I).starProjection ((-Complex.I) • Complex.I • v) = v
      rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
      exact Submodule.starProjection_mem_subspace_eq_self (K := IR I) ⟨v, hv⟩
    rw [← hv']
    have hIv : Complex.I • v ∈ T := by rw [hTtop]; exact Submodule.mem_top
    have h2 : uMap I (Complex.I • v) ∈ T.map (uMap I) := ⟨_, hIv, rfl⟩
    rw [hT, Submodule.map_span, ← Set.range_comp] at h2
    exact h2

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtDataPfA
section
namespace ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section Frame

variable (X : Data E r) (τ : X.Ψ) (e : Fin r → Fin r → ℂ)
  (he : ∀ a b, hermC τ.1 X.Gm (e a) (e b) = if a = b then ((sgn X.p0 a : ℝ) : ℂ) else 0)

theorem sgn_sq (a : Fin r) : ((sgn X.p0 a : ℝ) : ℂ) * ((sgn X.p0 a : ℝ) : ℂ) = 1 := by
  unfold sgn; split_ifs <;> push_cast <;> norm_num

include he in
theorem pair_sum (β : Fin r → ℂ) (s : Finset (Fin r)) (c : Fin r) :
    hermC τ.1 X.Gm (∑ a ∈ s, β a • e a) (e c) =
      if c ∈ s then β c * ((sgn X.p0 c : ℝ) : ℂ) else 0 := by
  rw [hermC_sum_left]
  simp only [hermC_smul_left, he, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']

include he in
theorem e_linInd : LinearIndependent ℂ e := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h1 := pair_sum X τ e he g Finset.univ i
  rw [hg, hermC_zero_left, if_pos (Finset.mem_univ i)] at h1
  have h2 := sgn_sq X i
  calc g i = g i * (((sgn X.p0 i : ℝ) : ℂ) * ((sgn X.p0 i : ℝ) : ℂ)) := by rw [h2, mul_one]
    _ = (g i * ((sgn X.p0 i : ℝ) : ℂ)) * ((sgn X.p0 i : ℝ) : ℂ) := by ring
    _ = 0 := by rw [← h1, zero_mul]

include he in
theorem e_span : Submodule.span ℂ (Set.range e) = ⊤ := by
  rcases isEmpty_or_nonempty (Fin r) with h | h
  · exact Subsingleton.elim _ _
  · exact (e_linInd X τ e he).span_eq_top_of_card_eq_finrank (by simp)

include he in
theorem expand (u : Fin r → ℂ) :
    u = ∑ a : Fin r, (((sgn X.p0 a : ℝ) : ℂ) * hermC τ.1 X.Gm u (e a)) • e a := by
  have hu : u ∈ Submodule.span ℂ (Set.range e) := by rw [e_span X τ e he]; trivial
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hu
  have hc : ∀ a : Fin r, ((sgn X.p0 a : ℝ) : ℂ) * hermC τ.1 X.Gm u (e a) = β a := by
    intro a
    rw [← hβ, pair_sum X τ e he β Finset.univ a, if_pos (Finset.mem_univ a)]
    calc ((sgn X.p0 a : ℝ) : ℂ) * (β a * ((sgn X.p0 a : ℝ) : ℂ))
        = β a * (((sgn X.p0 a : ℝ) : ℂ) * ((sgn X.p0 a : ℝ) : ℂ)) := by ring
      _ = β a := by rw [sgn_sq, mul_one]
  simp_rw [hc]
  exact hβ.symm

include he in
theorem self_pair (u : Fin r → ℂ) :
    (hermC τ.1 X.Gm u u).re = ∑ a : Fin r, sgn X.p0 a * ‖hermC τ.1 X.Gm u (e a)‖ ^ 2 := by
  have hx := expand X τ e he u
  calc (hermC τ.1 X.Gm u u).re
      = (hermC τ.1 X.Gm u (∑ a : Fin r,
          (((sgn X.p0 a : ℝ) : ℂ) * hermC τ.1 X.Gm u (e a)) • e a)).re := by rw [← hx]
    _ = ∑ a : Fin r, sgn X.p0 a * ‖hermC τ.1 X.Gm u (e a)‖ ^ 2 := by
      rw [hermC_sum_right, Complex.re_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hermC_smul_right, map_mul, Complex.conj_ofReal, mul_assoc, Complex.conj_mul',
        ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

end Frame

section Pos

variable (X : Data E r) (τ : X.Ψ) (e : Fin r → Fin r → ℂ)
  (he : ∀ a b, hermC τ.1 X.Gm (e a) (e b) = if a = b then ((sgn X.p0 a : ℝ) : ℂ) else 0)
  (x : Frame X.Ψ r)
  (hflag : Submodule.span ℂ (Set.range fun a : Fin X.p0 => e (Fin.castLE X.p0_le a)) =
      Submodule.span ℂ (Set.range fun a : Fin X.p0 => X.colP x τ a))
  (hind : LinearIndependent ℂ (X.colP x τ))

theorem sgn_castLE (a : Fin X.p0) : ((sgn X.p0 (Fin.castLE X.p0_le a : ℕ) : ℝ) : ℂ) = 1 := by
  simp [sgn, Fin.coe_castLE, a.isLt]

include he in
theorem proj (y : Fin r → ℂ)
    (hy : y ∈ Submodule.span ℂ (Set.range fun a : Fin X.p0 => e (Fin.castLE X.p0_le a))) :
    y = ∑ a : Fin X.p0, hermC τ.1 X.Gm y (e (Fin.castLE X.p0_le a)) • e (Fin.castLE X.p0_le a) := by
  obtain ⟨β, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hy
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  symm
  rw [hermC_sum_left]
  simp only [hermC_smul_left, he, Fin.castLE_inj, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ c), sgn_castLE, mul_one]

include he hflag hind in
theorem gramPos_det_ne : (X.gramPos x τ).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨w, hw⟩ : ∃ w : Fin r → ℂ, w = ∑ b : Fin X.p0, conj (v b) • X.colP x τ b := ⟨_, rfl⟩
  have h1 : ∀ a, hermC τ.1 X.Gm (X.colP x τ a) w = 0 := by
    intro a
    have ha := congrFun hv a
    simp only [Matrix.mulVec, dotProduct, Data.gramPos_apply, Pi.zero_apply] at ha
    rw [hw, hermC_sum_right]
    simp only [hermC_smul_right, Complex.conj_conj]
    rw [← ha]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  have h2 : ∀ a, hermC τ.1 X.Gm w (X.colP x τ a) = 0 := fun a => by
    rw [← hermC_conj τ.1 X.Gm_herm (X.colP x τ a) w, h1, map_zero]
  have h3 : ∀ y ∈ Submodule.span ℂ (Set.range fun a : Fin X.p0 => X.colP x τ a),
      hermC τ.1 X.Gm w y = 0 := by
    intro y hy
    obtain ⟨δ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hy
    simp [hermC_sum_right, hermC_smul_right, h2]
  have hwf : w ∈ Submodule.span ℂ (Set.range fun a : Fin X.p0 => e (Fin.castLE X.p0_le a)) := by
    rw [hflag, hw]
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  have hw0 : w = 0 := by
    rw [proj X τ e he w hwf]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [h3 _ (by rw [← hflag]; exact Submodule.subset_span ⟨a, rfl⟩), zero_smul]
  have hz := Fintype.linearIndependent_iff.mp hind (fun b => conj (v b)) (hw ▸ hw0)
  apply hv0
  funext b
  simpa using hz b

include he hflag hind in
theorem posPart_eq (u : Fin r → ℂ) :
    X.posPart x τ u = ∑ a : Fin X.p0, ‖hermC τ.1 X.Gm u (e (Fin.castLE X.p0_le a))‖ ^ 2 := by
  have hdet := gramPos_det_ne X τ e he x hflag hind
  have hG : (X.gramPos x τ)⁻¹ * X.gramPos x τ = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  have hA : ∀ d, hermC τ.1 X.Gm (X.ppos x τ u) (X.colP x τ d) = hermC τ.1 X.Gm u (X.colP x τ d) := by
    intro d
    rw [Data.ppos_eq, hermC_sum_left]
    simp only [hermC_smul_left, ← Data.gramPos_apply]
    have hs : ∑ a : Fin X.p0, (∑ b : Fin X.p0, hermC τ.1 X.Gm u (X.colP x τ b) *
        (X.gramPos x τ)⁻¹ b a) * X.gramPos x τ a d
        = ∑ b : Fin X.p0, hermC τ.1 X.Gm u (X.colP x τ b) *
          ((X.gramPos x τ)⁻¹ * X.gramPos x τ) b d := by
      simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
      exact Finset.sum_comm
    rw [hs, hG]
    simp [Matrix.one_apply]
  have hmemC : ∀ y ∈ Submodule.span ℂ (Set.range fun a : Fin X.p0 => X.colP x τ a),
      hermC τ.1 X.Gm (X.ppos x τ u) y = hermC τ.1 X.Gm u y := by
    intro y hy
    obtain ⟨δ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hy
    simp only [hermC_sum_right, hermC_smul_right, hA]
  have hp : X.ppos x τ u ∈
      Submodule.span ℂ (Set.range fun a : Fin X.p0 => e (Fin.castLE X.p0_le a)) := by
    rw [hflag, Data.ppos_eq]
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  have hpe := proj X τ e he (X.ppos x τ u) hp
  have hcoef : ∀ a : Fin X.p0, hermC τ.1 X.Gm (X.ppos x τ u) (e (Fin.castLE X.p0_le a))
      = hermC τ.1 X.Gm u (e (Fin.castLE X.p0_le a)) := fun a =>
    hmemC _ (by rw [← hflag]; exact Submodule.subset_span ⟨a, rfl⟩)
  simp_rw [hcoef] at hpe
  have h1 : X.posPart x τ u = (hermC τ.1 X.Gm (X.ppos x τ u) u).re := by
    rw [Data.hermC_ppos_self]; rfl
  rw [h1, hpe, hermC_sum_left, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hermC_smul_left, ← hermC_conj τ.1 X.Gm_herm u (e (Fin.castLE X.p0_le a)),
    Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]

include he hflag hind in
theorem maj_eq_sum (u : Fin r → ℂ) :
    X.maj x τ u = ∑ b : Fin r, ‖hermC τ.1 X.Gm u (e b)‖ ^ 2 := by
  set t : Fin r → ℝ := fun b => ‖hermC τ.1 X.Gm u (e b)‖ ^ 2 with ht
  have hsplit : ∑ b : Fin r, (if (b : ℕ) < X.p0 then t b else 0)
      = ∑ a : Fin X.p0, t (Fin.castLE X.p0_le a) := by
    rw [← Finset.sum_filter]
    exact Finset.sum_bij' (fun b hb => ⟨b, (Finset.mem_filter.mp hb).2⟩)
      (fun a _ => Fin.castLE X.p0_le a) (fun _ _ => Finset.mem_univ _)
      (fun a _ => by simp [Finset.mem_filter, a.isLt]) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl)
  have hsg : ∑ b : Fin r, sgn X.p0 b * t b
      = 2 * ∑ b : Fin r, (if (b : ℕ) < X.p0 then t b else 0) - ∑ b : Fin r, t b := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold sgn; split_ifs <;> ring
  unfold Data.maj
  rw [posPart_eq X τ e he x hflag hind u, self_pair X τ e he u]
  change 2 * ∑ a : Fin X.p0, t (Fin.castLE X.p0_le a) - ∑ b : Fin r, sgn X.p0 b * t b
    = ∑ b : Fin r, t b
  rw [hsg, hsplit]
  ring

end Pos

end ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
end

