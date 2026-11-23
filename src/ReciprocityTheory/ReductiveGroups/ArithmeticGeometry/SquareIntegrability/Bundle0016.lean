module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.QuotientTorusMinimumBound

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.OneLeKappaMulPhase
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem tof_pack_card [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hP : Ext.PackingCount) (u : Vsp X.dim) (hu : u ∈ IR I) (R : ℝ) (hR : 1 ≤ R)
    (F : Finset (Vsp X.dim)) (hF : ∀ y ∈ F, ∃ x ∈ X.L, y = uMap I x)
    (hFR : ∀ y ∈ F, ‖u - y‖ ≤ R) : (F.card : ℝ) ≤ (3 * R) ^ Module.finrank ℝ (IR I) := by
  classical

  let K : Submodule ℝ (Vsp X.dim) := IR I
  let B := stdOrthonormalBasis ℝ K
  let φ : Vsp X.dim → EuclideanSpace ℝ (Fin (Module.finrank ℝ K)) :=
    fun v => B.repr (K.orthogonalProjectionOnto (v - u))
  have hmem : ∀ y ∈ F, y - u ∈ K := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := hF y hy
    exact K.sub_mem (isU_uMap I x).1 hu
  have hpr : ∀ y (hy : y ∈ F), K.orthogonalProjectionOnto (y - u) = ⟨y - u, hmem y hy⟩ := fun y hy =>
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨y - u, hmem y hy⟩
  have hφ : ∀ y ∈ F, ∀ y' ∈ F, ‖φ y - φ y'‖ = ‖y - y'‖ := by
    intro y hy y' hy'
    show ‖B.repr (K.orthogonalProjectionOnto (y - u)) - B.repr (K.orthogonalProjectionOnto (y' - u))‖
      = ‖y - y'‖
    rw [hpr y hy, hpr y' hy', ← map_sub, LinearIsometryEquiv.norm_map]
    show ‖(y - u) - (y' - u)‖ = ‖y - y'‖
    congr 1
    abel
  have hinj : Set.InjOn φ F := by
    intro y hy y' hy' h
    have e := hφ y hy y' hy'
    rw [h, sub_self, norm_zero] at e
    exact sub_eq_zero.mp (norm_eq_zero.mp e.symm)
  have hcard : ((F.image φ).card : ℝ) ≤ (3 * R / 1) ^ Module.finrank ℝ K := by
    apply hP (Module.finrank ℝ K) (F.image φ) 1 R one_pos hR
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      show ‖B.repr (K.orthogonalProjectionOnto (y - u))‖ ≤ R
      rw [hpr y hy, LinearIsometryEquiv.norm_map]
      show ‖y - u‖ ≤ R
      rw [norm_sub_rev]
      exact hFR y hy
    · intro z hz z' hz' hne
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hz'
      rw [dist_eq_norm, hφ y hy y' hy']
      have hyy : y ≠ y' := fun h => hne (by rw [h])
      obtain ⟨x, hx, rfl⟩ := hF y hy
      obtain ⟨x', hx', rfl⟩ := hF y' hy'
      exact tof_uMap_sep P hI hx hx' hyy
  rw [Finset.card_image_of_injOn hinj, div_one] at hcard
  exact hcard

theorem tof_exists_nearest [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hP : Ext.PackingCount) (u : Vsp X.dim) (hu : u ∈ IR I) :
    ∃ y0 ∈ X.L, ∀ x ∈ X.L, ‖u - uMap I y0‖ ≤ ‖u - uMap I x‖ := by
  classical

  let S : Set (Vsp X.dim) := {y | (∃ x ∈ X.L, y = uMap I x) ∧ ‖u - y‖ ≤ ‖u‖}
  have hfin : S.Finite := by
    by_contra hinf
    obtain ⟨t, ht, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf
      (Nat.ceil ((3 * (‖u‖ + 1)) ^ Module.finrank ℝ (IR I)) + 1)
    have hb := tof_pack_card P hI hP u hu (‖u‖ + 1) (by linarith [norm_nonneg u]) t
      (fun y hy => (ht (Finset.mem_coe.2 hy)).1)
      (fun y hy => le_trans (ht (Finset.mem_coe.2 hy)).2 (by linarith))
    rw [hcard] at hb
    push_cast at hb
    have hc := Nat.le_ceil ((3 * (‖u‖ + 1)) ^ Module.finrank ℝ (IR I))
    linarith
  have h0 : (0 : Vsp X.dim) ∈ S :=
    ⟨⟨0, X.L.zero_mem, (map_zero (uMap I)).symm⟩, by rw [sub_zero]⟩
  obtain ⟨y, hyS, hmin⟩ :=
    hfin.toFinset.exists_min_image (fun y => ‖u - y‖) ⟨0, hfin.mem_toFinset.2 h0⟩
  obtain ⟨⟨y0, hy0, rfl⟩, hyu⟩ := hfin.mem_toFinset.1 hyS
  refine ⟨y0, hy0, fun x hx => ?_⟩
  by_cases hxs : ‖u - uMap I x‖ ≤ ‖u‖
  · exact hmin _ (hfin.mem_toFinset.2 ⟨⟨x, hx, rfl⟩, hxs⟩)
  · push_neg at hxs
    linarith

theorem tof_gauss_min_sum [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hP : Ext.PackingCount) (u : Vsp X.dim) (hu : u ∈ IR I) :
    ∃ y0 ∈ X.L, ∀ F : Finset (Vsp X.dim), (∀ y ∈ F, ∃ x ∈ X.L, y = uMap I x) →
      ∑ y ∈ F, Real.exp (-Real.pi * ‖u - y‖ ^ 2) ≤
        2 * (3 * (dstar (E := E) P.m : ℝ)) ^ dstar (E := E) P.m *
          Real.exp (-(Real.pi / 2) * ‖u - uMap I y0‖ ^ 2) := by
  obtain ⟨y0, hy0, hmin⟩ := tof_exists_nearest P hI hP u hu
  refine ⟨y0, hy0, fun F hF => ?_⟩
  have hsum := tof_sep_sum P hI hP u hu F hF
  have hc0 : 0 ≤ ‖u - uMap I y0‖ := norm_nonneg _

  have hterm : ∀ y ∈ F, Real.exp (-Real.pi * ‖u - y‖ ^ 2) ≤
      Real.exp (-(Real.pi / 2) * ‖u - uMap I y0‖ ^ 2) *
        Real.exp (-(Real.pi / 2) * ‖u - y‖ ^ 2) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hF y hy
    have h1 : ‖u - uMap I y0‖ ≤ ‖u - uMap I x‖ := hmin x hx
    have h2 : ‖u - uMap I y0‖ ^ 2 ≤ ‖u - uMap I x‖ ^ 2 := by
      nlinarith [mul_self_le_mul_self hc0 h1]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left h2 Real.pi_pos.le]
  calc ∑ y ∈ F, Real.exp (-Real.pi * ‖u - y‖ ^ 2)
      ≤ ∑ y ∈ F, Real.exp (-(Real.pi / 2) * ‖u - uMap I y0‖ ^ 2) *
          Real.exp (-(Real.pi / 2) * ‖u - y‖ ^ 2) := Finset.sum_le_sum hterm
    _ = Real.exp (-(Real.pi / 2) * ‖u - uMap I y0‖ ^ 2) *
          ∑ y ∈ F, Real.exp (-(Real.pi / 2) * ‖u - y‖ ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (-(Real.pi / 2) * ‖u - uMap I y0‖ ^ 2) *
          (2 * (3 * (dstar (E := E) P.m : ℝ)) ^ dstar (E := E) P.m) :=
        mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ = 2 * (3 * (dstar (E := E) P.m : ℝ)) ^ dstar (E := E) P.m *
          Real.exp (-(Real.pi / 2) * ‖u - uMap I y0‖ ^ 2) := by ring

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TranslationZeroModeLift
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open Complex NumberField
open scoped InnerProductSpace

noncomputable section

namespace Col

variable {E : Type} [Field E] [NumberField E]

def Uq {dim : (E →+* ℂ) → ℕ} (q : ℕ) (a : Vsp dim) (F : Vsp dim → ℂ) : Vsp dim → ℂ :=
  fun v => cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a)

def Uh (X : PT E) (q : ℕ) (a : Vsp X.dim) (F : Vsp X.dim → ℂ) : Vsp X.dim → ℂ :=
  fun v => (X.eps a : ℂ) ^ q * Uq q a F v

def F0 {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) (q : ℕ)
    (β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ) : Vsp dim → ℂ :=
  fun v => cexp ((q * Real.pi / 2 : ℂ) * S (IR I) v) * β (wmap (IR I) v)

theorem Uh_add (X : PT E) (q : ℕ) {a b : Vsp X.dim} (ha : a ∈ X.L) (hb : b ∈ X.L) (F : Vsp X.dim → ℂ) :
    Uh X q a (Uh X q b F) = Uh X q (a + b) F := by
  funext v
  obtain ⟨k, hk⟩ := X.integral a b ha hb
  have hε := X.eps_add a ha b hb
  rw [hk] at hε
  have hsin : Real.sin (Real.pi * k) = 0 := by
    rw [mul_comm]; exact Real.sin_int_mul_pi k
  have hεC : (X.eps (a + b) : ℂ) = X.eps a * X.eps b * (Real.cos (Real.pi * k) : ℝ) := by
    exact_mod_cast hε

  have h1 : Hf v (a + b) = Hf v a + Hf v b := by
    simp only [Hf, PiLp.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
  have h2 : Hf (v - a) b = Hf v b - Hf a b := by
    simp only [Hf, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have h3 : Hf (a + b) (a + b) = Hf a a + Hf a b + Hf b a + Hf b b := by
    simp only [Hf, PiLp.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]
    ring
  have h4 : Hf b a = (starRingEnd ℂ) (Hf a b) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Hf, map_sum, map_mul, Complex.conj_conj]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h5 : Hf b a - Hf a b = -(2 * (k : ℂ) * Complex.I) := by
    rw [h4]
    have hz := Complex.re_add_im (Hf a b)
    rw [← hz, hk]
    simp only [map_add (f := _), map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hexp : Complex.exp (-(q * Real.pi * (2 * (k : ℂ) * Complex.I)) / 2) =
      ((Real.cos (Real.pi * k) : ℝ) : ℂ) ^ q := by
    have : -(q * Real.pi * (2 * (k : ℂ) * Complex.I)) / 2 = q * (-((Real.pi * k : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_nat_mul, Complex.exp_mul_I]
    congr 1
    rw [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hsin]
    simp
  have hAB : Complex.exp ((q : ℂ) * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) *
      Complex.exp ((q : ℂ) * Real.pi * (Hf v b - Hf a b) - q * Real.pi * Hf b b / 2) =
      Complex.exp ((q : ℂ) * Real.pi * (Hf v a + Hf v b) -
        q * Real.pi * (Hf a a + Hf a b + Hf b a + Hf b b) / 2) *
        ((Real.cos (Real.pi * k) : ℝ) : ℂ) ^ q := by
    rw [← Complex.exp_add, ← hexp, ← Complex.exp_add]
    congr 1
    linear_combination ((q : ℂ) * Real.pi / 2) * h5
  simp only [Uh, Uq]
  rw [sub_sub, hεC, h1, h2, h3]
  linear_combination ((X.eps a : ℂ) ^ q * (X.eps b : ℂ) ^ q * F (v - (a + b))) * hAB

theorem Uh_shift (X : PT E) (q : ℕ) (a : Vsp X.dim) (G : Vsp X.dim → ℂ) (v : Vsp X.dim) :
    Uh X q a G (v + a) = (X.eps a : ℂ) ^ q * cexp (q * Real.pi * Hf v a + q * Real.pi * Hf a a / 2) * G v := by
  have hH : Hf (v + a) a = Hf v a + Hf a a := by
    simp only [Hf, PiLp.add_apply, add_mul, Finset.sum_add_distrib]
  simp only [Uh, Uq, add_sub_cancel_right, hH]
  have he : (q : ℂ) * Real.pi * (Hf v a + Hf a a) - q * Real.pi * Hf a a / 2 =
      q * Real.pi * Hf v a + q * Real.pi * Hf a a / 2 := by ring
  rw [he]; ring

section F0sec

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
  (hP : Ext.PackingCount) (q : ℕ) {β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ}
  (hβ : β ∈ (YB hI hP q).Sec q)
include hI hβ

theorem zeroModeLift_add_lattice {x : Vsp X.dim} (hx : x ∈ Ip X I) (v : Vsp X.dim) :
    F0 I q β (v + x) = (X.eps x : ℂ) ^ q * cexp (q * Real.pi * Hf v x + q * Real.pi * Hf x x / 2) * F0 I q β v := by
  unfold GT.Sec at hβ
  obtain ⟨-, hsec⟩ := hβ
  have hγ : wmap (IR I) x ∈ lat (YB hI hP q).b := by
    show wmap (IR I) x ∈ lat (bB hI hP)
    rw [lat_bB]
    exact wmap_mem_GB hx
  have h1 := hsec _ hγ (wmap (IR I) v)
  rw [show (YB hI hP q).ka = kaB X I q from rfl, kaB_wmap hI _ hx] at h1
  push_cast at h1
  have hz : ∀ k, z (IR I) k (v + x) = z (IR I) k v + z (IR I) k x := by
    intro k
    first
    | (simp only [z]; rw [Hf_add_l])
    | simp [z, Hf_add_l]
  have hzr : ∀ k, (starRingEnd ℂ) (z (IR I) k x) = z (IR I) k x := fun k =>
    Complex.conj_eq_iff_im.mpr (z_im_Ip hx k)
  have hd1 := Hf_decomp (K := IR I) (hK_of hI) v x
  have hd2 := Hf_decomp (K := IR I) (hK_of hI) x x
  unfold F0 S
  rw [map_add (f := _), h1, Hf_wmap (hK_of hI), Hf_wmap (hK_of hI), hd1, hd2]
  simp only [hz, hzr]
  have hexp : ∀ a b c d : ℂ, a + b = c + d → cexp a * cexp b = cexp c * cexp d := by
    intro a b c d h
    rw [← Complex.exp_add, ← Complex.exp_add, h]
  have hs : ∑ k, (z (IR I) k v + z (IR I) k x) ^ 2 = ∑ k, z (IR I) k v ^ 2 +
      2 * ∑ k, z (IR I) k v * z (IR I) k x + ∑ k, z (IR I) k x * z (IR I) k x := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have key := hexp ((q : ℂ) * Real.pi / 2 * ∑ k, (z (IR I) k v + z (IR I) k x) ^ 2)
    ((q : ℂ) * Real.pi * Hf (p2 (IR I) v) (p2 (IR I) x) +
      q * Real.pi * Hf (p2 (IR I) x) (p2 (IR I) x) / 2)
    ((q : ℂ) * Real.pi * (∑ k, z (IR I) k v * z (IR I) k x + Hf (p2 (IR I) v) (p2 (IR I) x)) +
      q * Real.pi * (∑ k, z (IR I) k x * z (IR I) k x + Hf (p2 (IR I) x) (p2 (IR I) x)) / 2)
    ((q : ℂ) * Real.pi / 2 * ∑ k, z (IR I) k v ^ 2) (by rw [hs]; ring)
  linear_combination ((X.eps x : ℂ) ^ q * β (wmap (IR I) v)) * key

theorem translation_zeroModeLift {x : Vsp X.dim} (hx : x ∈ Ip X I) : Uh X q x (F0 I q β) = F0 I q β := by
  funext v
  have h := zeroModeLift_add_lattice hI hP q hβ hx (v - x)
  rw [sub_add_cancel] at h
  have h2 : Hf (v - x) x = Hf v x - Hf x x := by
    simp only [Hf, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [h2] at h
  simp only [Uh, Uq]
  rw [h]
  have he : (q : ℂ) * Real.pi * (Hf v x - Hf x x) + q * Real.pi * Hf x x / 2 =
      q * Real.pi * Hf v x - q * Real.pi * Hf x x / 2 := by ring
  rw [he]; ring

end F0sec

def NIp (X : PT E) (I : Submodule ℤ (Vsp X.dim)) : Submodule ℤ X.L := (Ip X I).comap X.L.subtype

abbrev Qc (X : PT E) (I : Submodule ℤ (Vsp X.dim)) := X.L ⧸ NIp X I

def Tm (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (q : ℕ) (β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ)
    (γ : X.L) : Vsp X.dim → ℂ :=
  Uh X q γ (F0 I q β)

def Tc (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (q : ℕ) (β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ)
    (c : Qc X I) : Vsp X.dim → ℂ :=
  Tm X I q β (Quotient.out c)

def sP (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (q : ℕ) (β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ)
    (v : Vsp X.dim) : ℂ :=
  ∑' c : Qc X I, Tc X I q β c v

section Tsec

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
  (hP : Ext.PackingCount) (q : ℕ) {β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ}
  (hβ : β ∈ (YB hI hP q).Sec q)
include hI hβ

theorem Tm_congr {γ γ' : X.L} (h : γ - γ' ∈ NIp X I) : Tm X I q β γ = Tm X I q β γ' := by
  have hd : ((γ - γ' : X.L) : Vsp X.dim) ∈ Ip X I := h
  unfold Tm
  have e : (γ : Vsp X.dim) = (γ' : Vsp X.dim) + ((γ - γ' : X.L) : Vsp X.dim) := by
    simp
  rw [e, ← Uh_add X q γ'.2 (γ - γ').2, translation_zeroModeLift hI hP q hβ hd]

theorem Tc_mk (γ : X.L) : Tc X I q β (Submodule.Quotient.mk γ) = Tm X I q β γ := by
  unfold Tc
  apply Tm_congr hI hP q hβ
  rw [← Submodule.Quotient.eq]
  first
  | exact Quotient.out_eq _
  | exact Quotient.out_eq' _
  | simp

theorem Tc_shift (c : Qc X I) (γ0 : X.L) (v : Vsp X.dim) :
    Tc X I q β c (v + (γ0 : Vsp X.dim)) = (X.eps (γ0 : Vsp X.dim) : ℂ) ^ q *
      cexp (q * Real.pi * Hf v (γ0 : Vsp X.dim) + q * Real.pi * Hf (γ0 : Vsp X.dim) γ0 / 2) *
        Tc X I q β (c - Submodule.Quotient.mk γ0) v := by
  have hc : c - Submodule.Quotient.mk γ0 = Submodule.Quotient.mk (Quotient.out c - γ0) := by
    rw [Submodule.Quotient.mk_sub]
    congr 1
    exact (Quotient.out_eq c).symm
  rw [hc, Tc_mk hI hP q hβ]
  unfold Tc Tm
  have e : ((Quotient.out c : X.L) : Vsp X.dim) =
      (γ0 : Vsp X.dim) + ((Quotient.out c - γ0 : X.L) : Vsp X.dim) := by
    simp
  rw [e, ← Uh_add X q γ0.2 (Quotient.out c - γ0).2, Uh_shift]

theorem sP_shift (γ0 : X.L) (v : Vsp X.dim) :
    sP X I q β (v + (γ0 : Vsp X.dim)) = (X.eps (γ0 : Vsp X.dim) : ℂ) ^ q *
      cexp (q * Real.pi * Hf v (γ0 : Vsp X.dim) + q * Real.pi * Hf (γ0 : Vsp X.dim) γ0 / 2) *
        sP X I q β v := by
  unfold sP
  simp only [Tc_shift hI hP q hβ]
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.subRight (Submodule.Quotient.mk γ0 : Qc X I)).tsum_eq (fun c => Tc X I q β c v)

end Tsec

end Col

end

end ReciprocityTheory.ChartRestriction.G.I2
end

