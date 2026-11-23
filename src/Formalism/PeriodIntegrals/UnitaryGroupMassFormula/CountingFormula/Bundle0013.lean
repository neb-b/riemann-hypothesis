module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0011

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GramCondIff
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S ValuativeRel
open Classical

namespace FC

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]
variable {ϖ : 𝒪[F]} {k : Type} [Field k] {r : M.L.O →+* k} {n : ℕ} {b : Fin n → V}
  {Λ : Submodule M.L.O V}

theorem span_pi_iff (hR : RedData ϖ k r n b Λ) (x : M.L.O) :
    (x : E) ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)} ↔ r x = 0 := by
  rw [Submodule.mem_span_singleton, hR.ker]
  constructor
  · rintro ⟨o, ho⟩
    exact ⟨o, o.2, by rw [← ho]; show (o : E) * _ = _; ring⟩
  · rintro ⟨z, hz, hzx⟩
    exact ⟨⟨z, hz⟩, by rw [hzx]; show z * _ = _; ring⟩

theorem cj_mem {x : E} (hx : x ∈ M.L.O) : M.L.cj x ∈ M.L.O := by
  rw [M.L.O_def] at hx ⊢
  exact hx.map (M.L.cj.toAlgHom.restrictScalars 𝒪[F])

def Ph (r : M.L.O →+* k) (H : Loc.HermSp M V) (b : Fin n → V) (hint : ∀ i j, H.h (b i) (b j) ∈ M.L.O) :
    Matrix (Fin n) (Fin n) k := fun i j => r ⟨H.h (b i) (b j), hint i j⟩

theorem gram_mem (hR : RedData ϖ k r n b Λ) (H : Loc.HermSp M V) (hint : ∀ i j, H.h (b i) (b j) ∈ M.L.O)
    {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    H.h x y = ∑ i, ∑ j, cO hR x i * M.L.cj (cO hR y j) * H.h (b i) (b j) ∧ H.h x y ∈ M.L.O := by
  have he : H.h x y = ∑ i, ∑ j, cO hR x i * M.L.cj (cO hR y j) * H.h (b i) (b j) := by
    conv_lhs => rw [cO_sum hR hx, cO_sum hR hy]
    exact h_expand H b _ _
  refine ⟨he, ?_⟩
  rw [he]
  exact M.L.O.sum_mem fun i _ => M.L.O.sum_mem fun j _ =>
    M.L.O.mul_mem (M.L.O.mul_mem (cO_mem hR x i) (cj_mem (cO_mem hR y j))) (hint i j)

theorem gram_red (hR : RedData ϖ k r n b Λ) (H : Loc.HermSp M V) (hint : ∀ i j, H.h (b i) (b j) ∈ M.L.O)
    (q : ℕ) (rfrob : ∀ x y : M.L.O, (y : E) = M.L.cj x → r y = r x ^ q)
    {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    r ⟨H.h x y, (gram_mem hR H hint hx hy).2⟩ =
      ∑ i, ∑ j, red hR x i * Ph r H b hint i j * red hR y j ^ q := by
  have h1 : (⟨H.h x y, (gram_mem hR H hint hx hy).2⟩ : M.L.O) =
      ∑ i, ∑ j, (⟨cO hR x i, cO_mem hR x i⟩ : M.L.O) * ⟨M.L.cj (cO hR y j), cj_mem (cO_mem hR y j)⟩ *
        ⟨H.h (b i) (b j), hint i j⟩ := by
    apply Subtype.ext
    show H.h x y = _
    rw [(gram_mem hR H hint hx hy).1]
    push_cast
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, rfrob ⟨cO hR y j, cO_mem hR y j⟩ ⟨M.L.cj (cO hR y j), cj_mem (cO_mem hR y j)⟩ rfl]
  simp only [red, Ph]
  ring

theorem gram_cond_iff (hR : RedData ϖ k r n b Λ) (H : Loc.HermSp M V)
    (hint : ∀ i j, H.h (b i) (b j) ∈ M.L.O)
    (q : ℕ) (rfrob : ∀ x y : M.L.O, (y : E) = M.L.cj x → r y = r x ^ q)
    {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) (g : E) (hg : g ∈ M.L.O) :
    H.h x y - g ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)} ↔
      ∑ i, ∑ j, red hR x i * Ph r H b hint i j * red hR y j ^ q = r ⟨g, hg⟩ := by
  have hm := (gram_mem hR H hint hx hy).2
  have := span_pi_iff hR ⟨H.h x y - g, M.L.O.sub_mem hm hg⟩
  simp only at this
  rw [this, show (⟨H.h x y - g, M.L.O.sub_mem hm hg⟩ : M.L.O) = ⟨H.h x y, hm⟩ - ⟨g, hg⟩ from
    Subtype.ext rfl, map_sub, sub_eq_zero, gram_red hR H hint q rfrob hx hy]

end FC

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.HTIntLeft
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem inW_add (D : Formalism.BasicNotions.D7) {x y : (VS D).V} (hx : InW D x) (hy : InW D y) : InW D (x + y) := by
  unfold InW at *
  obtain ⟨h1, h2, h3⟩ := hx
  obtain ⟨k1, k2, k3⟩ := hy
  exact ⟨fun a => by rw [map_add (f := _), h1 a, k1 a, add_zero], fun a => by rw [map_add (f := _), h2 a, k2 a, add_zero],
    by rw [map_add (f := _), h3, k3, add_zero]⟩

theorem inW_smul (D : Formalism.BasicNotions.D7) (k : D.host.E) {x : (VS D).V} (hx : InW D x) : InW D (k • x) := by
  unfold InW at *
  obtain ⟨h1, h2, h3⟩ := hx
  exact ⟨fun a => by rw [map_smul, h1 a, smul_zero], fun a => by rw [map_smul, h2 a, smul_zero],
    by rw [map_smul, h3, smul_zero]⟩

theorem inW_zero (D : Formalism.BasicNotions.D7) : InW D 0 := by
  unfold InW
  exact ⟨fun a => map_zero _, fun a => map_zero _, map_zero _⟩

theorem inW_sum (D : Formalism.BasicNotions.D7) {ι : Type} (s : Finset ι) (x : ι → (VS D).V) (hx : ∀ i, InW D (x i)) :
    InW D (∑ i ∈ s, x i) := by
  exact Finset.sum_induction x (InW D) (fun a b ha hb => inW_add D ha hb) (inW_zero D) (fun i _ => hx i)

def LamW (D : Formalism.BasicNotions.D7) (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Submodule (𝓞 D.host.E) (VS D).V where
  carrier := {y | y ∈ Λ ∧ InW D y}
  add_mem' hx hy := ⟨Λ.add_mem hx.1 hy.1, inW_add D hx.2 hy.2⟩
  zero_mem' := ⟨Λ.zero_mem, inW_zero D⟩
  smul_mem' o _ hx := ⟨Λ.smul_mem o hx.1, by
    rw [← algebraMap_smul D.host.E o]; exact inW_smul D _ hx.2⟩

theorem hT_int_left (D : Formalism.BasicNotions.D7) (n : ℤ) (x y : (VS D).V) :
    (VS D).hT ((n : D.host.E) • x) y = (n : D.host.E) * (VS D).hT x y := by
  rw [LinearMap.map_smulₛₗ₂, smul_eq_mul, starRingEnd_apply, star_intCast]

private theorem hT_isIntegral_of_mem_unimodular (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) {y v : (VS D).V} (hy : y ∈ Λ) (hv : v ∈ Λ) :
    ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (VS D).hT y v := by
  have h : Formalism.E.hdual (VS D).hT Λ = Λ := hU
  have hv' : v ∈ Formalism.E.hdual (VS D).hT Λ := by rw [h]; exact hv
  simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply] at hv'
  exact Submodule.mem_one.mp (hv' y hy)

theorem pW_lat (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) (heΛ : ∀ a, D.sp.hypE a ∈ Λ) (d : ℤ)
    (hdF : ∀ a, (d : D.host.E) • D.sp.hypF a ∈ Λ)
    (hdz : ((d : D.host.E) * (D.sp.T : D.host.E)⁻¹) • D.sp.zm ∈ Λ) {v : (VS D).V} (hv : v ∈ Λ) :
    (d : D.host.E) ^ 2 • pW D v ∈ Λ := by
  have hT0 : (D.sp.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr D.sp.T_prime.ne_zero
  have hsm : ∀ (o : 𝓞 D.host.E) {y : (VS D).V}, y ∈ Λ → algebraMap (𝓞 D.host.E) D.host.E o • y ∈ Λ :=
    fun o y hy => by rw [algebraMap_smul]; exact Λ.smul_mem o hy
  have hint : ∀ (n : ℤ) {y : (VS D).V}, y ∈ Λ → (n : D.host.E) • y ∈ Λ := fun n y hy => by
    have := hsm (n : 𝓞 D.host.E) hy; rwa [map_intCast] at this
  have hnat : ∀ (n : ℕ) {y : (VS D).V}, y ∈ Λ → (n : D.host.E) • y ∈ Λ := fun n y hy => by
    have := hsm (n : 𝓞 D.host.E) hy; rwa [map_natCast] at this
  unfold pW
  simp only [smul_add, smul_sub, Finset.smul_sum]
  refine Λ.add_mem (Λ.sub_mem (Λ.sub_mem ?_ ?_) ?_) ?_
  · rw [pow_two, mul_smul]; exact hint d (hint d hv)
  · refine Λ.sum_mem (fun a _ => ?_)
    obtain ⟨o, ho⟩ := hT_isIntegral_of_mem_unimodular D hU (hdF a) hv
    have heq : (d : D.host.E) ^ 2 • ((VS D).hT (D.sp.hypF a) v • D.sp.hypE a) =
        algebraMap (𝓞 D.host.E) D.host.E ((d : 𝓞 D.host.E) * o) • D.sp.hypE a := by
      simp only [smul_smul]
      rw [map_mul, map_intCast, ho, hT_int_left]
      congr 1
      ring
    rw [heq]; exact hsm _ (heΛ a)
  · refine Λ.sum_mem (fun a _ => ?_)
    obtain ⟨o, ho⟩ := hT_isIntegral_of_mem_unimodular D hU (heΛ a) hv
    have heq : (d : D.host.E) ^ 2 • ((VS D).hT (D.sp.hypE a) v • D.sp.hypF a) =
        algebraMap (𝓞 D.host.E) D.host.E ((d : 𝓞 D.host.E) * o) • ((d : D.host.E) • D.sp.hypF a) := by
      simp only [smul_smul]
      rw [map_mul, map_intCast, ho]
      congr 1
      ring
    rw [heq]; exact hsm _ (hdF a)
  · obtain ⟨o, ho⟩ := hT_isIntegral_of_mem_unimodular D hU hdz hv
    have hc : (VS D).hT (((d : D.host.E) * (D.sp.T : D.host.E)⁻¹) • D.sp.zm) v =
        (d : D.host.E) * (D.sp.T : D.host.E)⁻¹ * (VS D).hT D.sp.zm v := by
      rw [LinearMap.map_smulₛₗ₂, smul_eq_mul]
      congr 1
      simp
    have hdzm : (d : D.host.E) • D.sp.zm ∈ Λ := by
      have := hnat D.sp.T hdz
      rwa [smul_smul, ← mul_assoc, mul_comm (D.sp.T : D.host.E) (d : D.host.E), mul_assoc,
        mul_inv_cancel₀ hT0, mul_one] at this
    have heq : (d : D.host.E) ^ 2 • (((VS D).hT D.sp.zm v / (D.sp.T : D.host.E)) • D.sp.zm) =
        algebraMap (𝓞 D.host.E) D.host.E o • ((d : D.host.E) • D.sp.zm) := by
      simp only [smul_smul]
      rw [ho, hc]
      congr 1
      rw [div_eq_mul_inv]
      ring
    rw [heq]; exact hsm _ hdzm

def Pm (D : Formalism.BasicNotions.D7) (Z : MatZ D) (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E) :
    Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E :=
  1 - R * betaZ D Z

theorem beta_Pm (D : Formalism.BasicNotions.D7) (Z : MatZ D) (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E)
    (hR : betaZ D Z * R = 1) : betaZ D Z * Pm D Z R = 0 := by
  unfold Pm
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hR, Matrix.one_mul, sub_self]

def Gfl (D : Formalism.BasicNotions.D7) (T' : D.host.E) (b1 b2 : Fin (D.R.rS + 1)) : D.host.E :=
  if b1 = Fin.last D.R.rS ∧ b2 = Fin.last D.R.rS then -T' else 0

def gam (D : Formalism.BasicNotions.D7) (Z : MatZ D) (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E) (c0 : D.host.E)
    (b : Fin (D.R.rS + 1)) : D.host.E :=
  (∑ b', Pm D Z R b' b * (Z (Fin.last D.R.rS) b' / star c0)) / (D.sp.T : D.host.E)

def kap (D : Formalism.BasicNotions.D7) (T' : D.host.E) (Z : MatZ D) (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E)
    (c0 : D.host.E) (b : Fin (D.R.rS + 1)) : D.host.E :=
  (∑ b1, ∑ b2, star (Pm D Z R b1 b) * Pm D Z R b2 b * Gfl D T' b1 b2) +
    (D.sp.T : D.host.E) * star (gam D Z R c0 b) * gam D Z R c0 b

def tv (D : Formalism.BasicNotions.D7) (Z : MatZ D) (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E)
    (x : (Fin D.R.rS → (VS D).V) × (VS D).V) (b : Fin (D.R.rS + 1)) : (VS D).V :=
  ∑ b', Pm D Z R b' b • pWf D x b'

private theorem hT_swap_eq_star' (D : Formalism.BasicNotions.D7) (p q : (VS D).V) :
    (VS D).hT q p = star ((VS D).hT p q) := by
  first
  | exact ((VS D).herm p q).symm
  | exact ((VS D).herm.eq p q).symm
  | simpa using ((VS D).herm p q).symm
  | simpa using ((VS D).herm.eq p q).symm

private theorem pW_add' (D : Formalism.BasicNotions.D7) (u v : (VS D).V) : pW D (u + v) = pW D u + pW D v := by
  unfold pW
  simp only [map_add (f := _), add_smul, Finset.sum_add_distrib, add_div]
  abel

private theorem pW_smul' (D : Formalism.BasicNotions.D7) (c : D.host.E) (v : (VS D).V) :
    pW D (c • v) = c • pW D v := by
  unfold pW
  simp only [map_smul, smul_eq_mul, mul_div_assoc, mul_smul, smul_sub, smul_add, Finset.smul_sum]

private theorem pW_sum' (D : Formalism.BasicNotions.D7) {ι : Type} (s : Finset ι) (f : ι → (VS D).V) :
    pW D (∑ i ∈ s, f i) = ∑ i ∈ s, pW D (f i) := by
  exact map_sum (AddMonoidHom.mk' (pW D) (pW_add' D)) f s

private theorem hT_pW_self_of_hT_hypE_eq_zero (D : Formalism.BasicNotions.D7) (w : (VS D).V)
    (hw : ∀ a, (VS D).hT (D.sp.hypE a) w = 0) :
    (VS D).hT (pW D w) (pW D w) = (VS D).hT w w +
      (D.sp.T : D.host.E) * star ((VS D).hT D.sp.zm w / (D.sp.T : D.host.E)) *
        ((VS D).hT D.sp.zm w / (D.sp.T : D.host.E)) := by
  have hs : ∀ p q : (VS D).V, (VS D).hT q p = star ((VS D).hT p q) := fun p q => hT_swap_eq_star' D p q
  have hee : ∀ a a', (VS D).hT (D.sp.hypE a) (D.sp.hypE a') = 0 := D.sp.hyp_ee
  have hze : ∀ a, (VS D).hT D.sp.zm (D.sp.hypE a) = 0 := fun a => (D.sp.hyp_orthz a).1
  have hez : ∀ a, (VS D).hT (D.sp.hypE a) D.sp.zm = 0 := fun a => by rw [hs, hze, star_zero]
  have hwe : ∀ a, (VS D).hT w (D.sp.hypE a) = 0 := fun a => by rw [hs, hw a, star_zero]
  have hzz : (VS D).hT D.sp.zm D.sp.zm = -(D.sp.T : D.host.E) := D.sp.zm_norm
  have hT0 : (D.sp.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr D.sp.T_prime.ne_zero
  have hwz : (VS D).hT w D.sp.zm = star ((VS D).hT D.sp.zm w) := hs _ _
  unfold pW
  simp only [hw, zero_smul, Finset.sum_const_zero, sub_zero]
  set g := (VS D).hT D.sp.zm w / (D.sp.T : D.host.E) with hg
  set s := ∑ a, (VS D).hT (D.sp.hypF a) w • D.sp.hypE a with hsdef
  have hsy : ∀ y, (VS D).hT s y = ∑ a, star ((VS D).hT (D.sp.hypF a) w) * (VS D).hT (D.sp.hypE a) y := by
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hsdef, map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, LinearMap.map_sum₂, LinearMap.map_smulₛₗ₂]
  have hys : ∀ y, (VS D).hT y s = ∑ a, (VS D).hT (D.sp.hypF a) w * (VS D).hT y (D.sp.hypE a) := by
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hsdef, map_sum, map_smul, smul_eq_mul]
  have h1 : (VS D).hT s w = 0 := by rw [hsy]; simp [hw]
  have h2 : (VS D).hT s s = 0 := by rw [hsy]; simp [hys, hee]
  have h3 : (VS D).hT s D.sp.zm = 0 := by rw [hsy]; simp [hez]
  have h4 : (VS D).hT w s = 0 := by rw [hys]; simp [hwe]
  have h5 : (VS D).hT D.sp.zm s = 0 := by rw [hys]; simp [hze]
  have h6 : (VS D).hT D.sp.zm w = (D.sp.T : D.host.E) * g := by
    rw [hg, mul_div_assoc', mul_comm, mul_div_assoc, div_self hT0, mul_one]
  simp only [map_add (f := _), map_sub, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, h1, h2, h3, h4, h5, hzz, hwz, h6,
    starRingEnd_apply, star_mul', star_natCast]
  ring

theorem tv_norm (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (Z : MatZ D) (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E)
    (hR : betaZ D Z * R = 1) (he : F0.e = D.sp.hypE) {c0 : D.host.E} (hc0 : c0 ≠ 0) (hz : F0.z = c0 • D.sp.zm)
    {x : (Fin D.R.rS → (VS D).V) × (VS D).V} (hx : Good D T' F0 Λ Z x) (b : Fin (D.R.rS + 1)) :
    (VS D).hT (tv D Z R x b) (tv D Z R x b) = kap D T' Z R c0 b := by
  obtain ⟨-, hZ, hG⟩ := hx
  set w := ∑ b', Pm D Z R b' b • fr D x b' with hw
  have htv : tv D Z R x b = pW D w := by
    show ∑ b', Pm D Z R b' b • pW D (fr D x b') = pW D w
    rw [hw, pW_sum']
    simp only [pW_smul']
  have hEu : ∀ a b', (VS D).hT (D.sp.hypE a) (fr D x b') = Z (Fin.castSucc a) b' := by
    intro a b'
    have h := hZ (Fin.castSucc a) b'
    simpa [brS, FlagG.fvec, he] using h
  have hzu : ∀ b', (VS D).hT D.sp.zm (fr D x b') = Z (Fin.last D.R.rS) b' / star c0 := by
    intro b'
    have h := hZ (Fin.last D.R.rS) b'
    simp only [brS, FlagG.fvec, Fin.snoc_last, hz, LinearMap.map_smulₛₗ₂, smul_eq_mul,
      starRingEnd_apply] at h
    rw [eq_div_iff (star_ne_zero.mpr hc0), ← h, mul_comm]
  have hGu : ∀ b1 b2, (VS D).hT (fr D x b1) (fr D x b2) = Gfl D T' b1 b2 := by
    intro b1 b2
    rw [hG b1 b2]
    unfold Gfl
    split_ifs <;> first | rfl | (exfalso; tauto)
  have hEw : ∀ a, (VS D).hT (D.sp.hypE a) w = 0 := by
    intro a
    have h0 : (betaZ D Z * Pm D Z R) a b = 0 := by rw [beta_Pm D Z R hR]; rfl
    rw [Matrix.mul_apply] at h0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hw, map_sum]
    simp only [map_smul, smul_eq_mul, hEu]
    simpa [betaZ, Matrix.submatrix_apply, mul_comm] using h0
  have hww : (VS D).hT w w =
      ∑ b1, ∑ b2, star (Pm D Z R b1 b) * Pm D Z R b2 b * Gfl D T' b1 b2 := by
    rw [hw]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.map_sum₂, LinearMap.map_smulₛₗ₂, map_sum, map_smul, map_smulₛₗ,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b1 _ => Finset.sum_congr rfl (fun b2 _ => ?_))
    rw [hGu b1 b2]
    ring
  have hzw : (VS D).hT D.sp.zm w = ∑ b', Pm D Z R b' b * (Z (Fin.last D.R.rS) b' / star c0) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hw, map_sum]
    simp only [map_smul, smul_eq_mul, hzu]
  rw [htv, hT_pW_self_of_hT_hypE_eq_zero D w hEw]
  unfold kap gam
  rw [hww, hzw]

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.LocalDensityIntegral
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S
open ValuativeRel

theorem fl_inj {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) : Function.Injective (algebraMap F E) := by
  haveI : Nontrivial E := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have h1 := L.rank
    have h2 := Module.finrank_zero_of_subsingleton (R := F) (M := E)
    omega
  exact (algebraMap F E).injective

theorem fl_norm_ne {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hE : ∀ x : E, x ≠ 0 → IsUnit x)
    {x : E} (hx0 : x ≠ 0) (n : 𝒪[F]) (hn : algebraMap F E n = x * L.cj x) : n ≠ 0 := by
  haveI : Nontrivial E := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have h1 := L.rank
    have h2 := Module.finrank_zero_of_subsingleton (R := F) (M := E)
    omega
  intro hn0
  rw [hn0] at hn
  have hcj : L.cj x ≠ 0 := fun h => hx0 ((map_eq_zero_iff L.cj L.cj.injective).mp h)
  have hu : IsUnit (x * L.cj x) := (hE x hx0).mul (hE _ hcj)
  apply hu.ne_zero
  rw [← hn]
  simp

theorem fl_fact {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hl : IsNonarchimedeanLocalField F)
    (hE : ∀ x : E, x ≠ 0 → IsUnit x) (hinj : Function.Injective (algebraMap F E))
    (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) :
    ∀ x ∈ L.O, x ≠ 0 → ∃ k : ℕ, ∃ u ∈ L.O, (∃ w ∈ L.O, u * w = 1) ∧ x = algebraMap F E ϖ ^ k * u := by
  haveI := hl
  have key : ∀ n : 𝒪[F], ∀ x ∈ L.O, x ≠ 0 → algebraMap F E n = x * L.cj x →
      ∃ k : ℕ, ∃ u ∈ L.O, (∃ w ∈ L.O, u * w = 1) ∧ x = algebraMap F E ϖ ^ k * u := by
    intro n
    refine WellFounded.induction (wellFounded_dvdNotUnit (α := 𝒪[F]))
      (C := fun n : 𝒪[F] => ∀ x ∈ L.O, x ≠ 0 → algebraMap F E n = x * L.cj x →
        ∃ k : ℕ, ∃ u ∈ L.O, (∃ w ∈ L.O, u * w = 1) ∧ x = algebraMap F E ϖ ^ k * u) n ?_
    intro n ih x hx hx0 hn
    by_cases hdiv : ∃ z ∈ L.O, x = algebraMap F E ϖ * z
    · obtain ⟨z, hz, rfl⟩ := hdiv
      have hz0 : z ≠ 0 := by
        rintro rfl
        simp at hx0
      obtain ⟨n', hn'⟩ := fl_norm L hinj hz
      have hcj : L.cj (algebraMap F E ϖ) = algebraMap F E ϖ := L.cj.commutes _
      have heq : n = n' * (ϖ * ϖ) := by
        apply Subtype.ext
        apply hinj
        calc algebraMap F E (n : F) = algebraMap F E ϖ * z * L.cj (algebraMap F E ϖ * z) := hn
          _ = (z * L.cj z) * (algebraMap F E ϖ * algebraMap F E ϖ) := by rw [map_mul, hcj]; ring
          _ = algebraMap F E n' * (algebraMap F E ϖ * algebraMap F E ϖ) := by rw [hn']
          _ = algebraMap F E ((n' * (ϖ * ϖ) : 𝒪[F]) : F) := by
            rw [show ((n' * (ϖ * ϖ) : 𝒪[F]) : F) = (n' : F) * ((ϖ : F) * (ϖ : F)) from rfl, map_mul, map_mul]
      have hdvd : DvdNotUnit n' n := by
        refine ⟨fl_norm_ne L hE hz0 n' hn', ϖ * ϖ, ?_, heq⟩
        rw [IsUnit.mul_iff]
        exact fun h => hϖ.not_isUnit h.1
      obtain ⟨k, u, hu, hw, hzu⟩ := ih n' hdvd z hz hz0 hn'
      exact ⟨k + 1, u, hu, hw, by rw [hzu, pow_succ]; ring⟩
    · obtain ⟨y, hy, hxy⟩ := fl_local L hl hE hinj ϖ hϖ x hx hdiv
      exact ⟨0, x, hx, ⟨y, hy, hxy⟩, by simp⟩
  intro x hx hx0
  obtain ⟨n, hn⟩ := fl_norm L hinj hx
  exact key n x hx hx0 hn

theorem local_density_integral : FLocO := by
  intro F E _ _ _ _ _ _ L hl _ hE ϖ hϖ
  have hinj := fl_inj L
  exact ⟨fl_local L hl hE hinj ϖ hϖ, fl_den L, fl_fact L hl hE hinj ϖ hϖ⟩

end PI.UnitaryGroupMassFormula.CntFormula
end
end

