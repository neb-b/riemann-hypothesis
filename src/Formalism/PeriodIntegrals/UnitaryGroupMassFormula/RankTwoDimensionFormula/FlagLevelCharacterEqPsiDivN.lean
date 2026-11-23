module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0021

@[expose] public section

noncomputable section

namespace PI.UnitaryDimensionFormula.unitaryCongruence

open MeasureTheory NumberField Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped TensorProduct

section Gen

variable (I : AutInst)

theorem fmat_mul (x y : I.Gf) : I.fmat (x * y) = I.fmat x * I.fmat y := rfl
theorem fmat_one : I.fmat 1 = 1 := rfl
theorem fmat_inv_mul (x : I.Gf) : I.fmat x⁻¹ * I.fmat x = 1 := by
  rw [← fmat_mul I, inv_mul_cancel, fmat_one I]

theorem K_one : (1 : I.Gf) ∈ I.Kset := by
  show ((1 : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
  exact (Formalism.UG.stabGL I.Lf).one_mem
theorem K_mv {x : I.Gf} (hx : x ∈ I.Kset) {y : VA I} (hy : y ∈ I.Lf) : I.fmat x *ᵥ y ∈ I.Lf := by
  have h : ∀ v, v ∈ I.Lf ↔ I.fmat x *ᵥ v ∈ I.Lf := hx
  exact (h y).1 hy

def mvO (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) : VA I →ₗ[IntAf I.F I.E] VA I where
  toFun v := M *ᵥ v
  map_add' := Matrix.mulVec_add M
  map_smul' c v := by
    show M *ᵥ ((c : I.E ⊗[I.F] Af I.F) • v) = (c : I.E ⊗[I.F] Af I.F) • (M *ᵥ v)
    exact Matrix.mulVec_smul M _ v

def Mo (g : ℕ) (S : Set (VA I)) : Submodule (IntAf I.F I.E) (VA I) :=
  Submodule.span (IntAf I.F I.E) S ⊔ mL I g

theorem smul_mem_mL {g : ℕ} {y : VA I} (hy : y ∈ I.Lf) :
    ((g : I.E ⊗[I.F] Af I.F) • y) ∈ mL I g := by
  unfold Formalism.L2.SG.HidaSetting.mL
  exact Submodule.subset_span ⟨y, hy, rfl⟩

theorem Mo_mono {g : ℕ} {S T : Set (VA I)} (h : S ⊆ T) : Mo I g S ≤ Mo I g T := by
  unfold Mo
  exact sup_le_sup_right (Submodule.span_mono h) _
theorem sub_Mo {g : ℕ} {S : Set (VA I)} : S ⊆ Mo I g S := by
  intro s hs
  unfold Mo
  exact Submodule.mem_sup_left (Submodule.subset_span hs)
theorem mL_Mo {g : ℕ} {S : Set (VA I)} : mL I g ≤ Mo I g S := by
  unfold Mo
  exact le_sup_right

theorem mv_mem (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (g : ℕ) (S : Set (VA I))
    (N : Submodule (IntAf I.F I.E) (VA I)) (hS : ∀ s ∈ S, M *ᵥ s ∈ N)
    (hm : ∀ y ∈ I.Lf, M *ᵥ ((g : I.E ⊗[I.F] Af I.F) • y) ∈ N) :
    ∀ v ∈ Mo I g S, M *ᵥ v ∈ N := by
  intro v hv
  have h : Submodule.span (IntAf I.F I.E) S ⊔ mL I g ≤ N.comap (mvO I M) := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      intro s hs
      exact hS s hs
    · unfold Formalism.L2.SG.HidaSetting.mL
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      exact hm y hy
  exact h hv

theorem mL_mv {M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hM : ∀ y ∈ I.Lf, M *ᵥ y ∈ I.Lf)
    (g : ℕ) {N : Submodule (IntAf I.F I.E) (VA I)} (hN : mL I g ≤ N) :
    ∀ y ∈ I.Lf, M *ᵥ ((g : I.E ⊗[I.F] Af I.F) • y) ∈ N := by
  intro y hy
  rw [Matrix.mulVec_smul]
  exact hN (smul_mem_mL I (hM y hy))

theorem pres {x : I.Gf} (hx : x ∈ I.Kset) (g : ℕ) (S : Set (VA I)) (N : Submodule (IntAf I.F I.E) (VA I))
    (hSN : S ⊆ N) (hS : ∀ s ∈ S, (I.fmat x - 1) *ᵥ s ∈ N) (hN : mL I g ≤ N) :
    ∀ v ∈ Mo I g S, I.fmat x *ᵥ v ∈ N := by
  refine mv_mem I (I.fmat x) g S N (fun s hs => ?_) (mL_mv I (fun y hy => K_mv I hx hy) g hN)
  have e : I.fmat x *ᵥ s = (I.fmat x - 1) *ᵥ s + s := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]
  rw [e]
  exact N.add_mem (hS s hs) (hSN hs)

theorem sigA_tmul (a : I.E) (b : Af I.F) : sigA I (a ⊗ₜ[I.F] b) = star a ⊗ₜ[I.F] b := by
  exact Algebra.TensorProduct.map_tmul I.cm.sig (AlgHom.id I.F (Af I.F)) a b

theorem sigA_sigA (a : I.E ⊗[I.F] Af I.F) : sigA I (sigA I a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => rw [sigA_tmul, sigA_tmul, star_star]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem sigA_inclE (a : I.E) : sigA I (Formalism.UG.inclE (F := I.F) (Af I.F) a) =
    Formalism.UG.inclE (F := I.F) (Af I.F) (star a) := by
  show sigA I (a ⊗ₜ[I.F] (1 : Af I.F)) = star a ⊗ₜ[I.F] (1 : Af I.F)
  exact sigA_tmul I a 1

theorem star_intOE {a : I.E} (ha : a ∈ Formalism.UG.intOE I.E) : star a ∈ Formalism.UG.intOE I.E := by
  obtain ⟨x, rfl⟩ := ha
  exact ⟨⟨star (x : I.E), x.isIntegral_coe.map (starRingEnd I.E).toIntAlgHom⟩, rfl⟩

theorem sigA_mem {a : I.E ⊗[I.F] Af I.F} (ha : a ∈ IntAf I.F I.E) : sigA I a ∈ IntAf I.F I.E := by
  have h : IntAf I.F I.E ≤ (IntAf I.F I.E).comap (sigA I) := by
    show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    rintro _ (⟨⟨s, hs⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · show sigA I (s ⊗ₜ[I.F] (1 : Af I.F)) ∈ IntAf I.F I.E
      rw [sigA_tmul]
      exact Subring.subset_closure (Or.inl ⟨⟨star s, star_intOE I hs⟩, rfl⟩)
    · show sigA I ((1 : I.E) ⊗ₜ[I.F] y) ∈ IntAf I.F I.E
      rw [sigA_tmul, star_one]
      exact Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  exact h ha

theorem inclE_mem {a : I.E} (ha : a ∈ Formalism.UG.intOE I.E) :
    Formalism.UG.inclE (F := I.F) (Af I.F) a ∈ IntAf I.F I.E := by
  exact Subring.subset_closure (Or.inl ⟨⟨a, ha⟩, rfl⟩)

theorem hA_add_right (u v w : VA I) : hA I u (v + w) = hA I u v + hA I u w := by
  unfold Formalism.L2.SG.HidaSetting.hA Formalism.UG.hform
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hA_smul_right (u v : VA I) (c : I.E ⊗[I.F] Af I.F) : hA I u (c • v) = c * hA I u v := by
  unfold Formalism.L2.SG.HidaSetting.hA Formalism.UG.hform
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hA_add_left (u u' v : VA I) : hA I (u + u') v = hA I u v + hA I u' v := by
  unfold Formalism.L2.SG.HidaSetting.hA Formalism.UG.hform
  simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hA_smul_left (u v : VA I) (c : I.E ⊗[I.F] Af I.F) : hA I (c • u) v = sigA I c * hA I u v := by
  unfold Formalism.L2.SG.HidaSetting.hA Formalism.UG.hform
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def hL (u : VA I) : VA I →ₗ[I.E ⊗[I.F] Af I.F] (I.E ⊗[I.F] Af I.F) where
  toFun := hA I u
  map_add' := hA_add_right I u
  map_smul' c v := hA_smul_right I u v c

theorem hL_apply (u v : VA I) : hL I u v = hA I u v := rfl

theorem hA_incl (x y : Fin I.n → I.E) : hA I (incl I x) (incl I y) =
    Formalism.UG.inclE (F := I.F) (Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J x y) := by
  unfold Formalism.L2.SG.HidaSetting.hA Formalism.UG.hform Formalism.L2.SG.HidaSetting.incl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, map_sum, map_mul, starRingEnd_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [sigA_inclE]

theorem J_conj (i j : Fin I.n) : star (I.J i j) = I.J j i := by
  have h0 : Formalism.UG.cT (starRingEnd I.E) I.J = I.J := I.J_herm
  have h := congrFun (congrFun h0 j) i
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at h
  exact h

theorem hA_symm (u v : VA I) : hA I v u = sigA I (hA I u v) := by
  unfold Formalism.L2.SG.HidaSetting.hA Formalism.UG.hform
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Matrix.map_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [sigA_sigA, sigA_inclE, J_conj]
  ring

theorem hA_int {u v : VA I} (hu : u ∈ I.Lf) (hv : v ∈ I.Lf) : hA I u v ∈ IntAf I.F I.E := by
  have gen : ∀ x ∈ I.L, ∀ y ∈ I.L, hA I (incl I x) (incl I y) ∈ IntAf I.F I.E := by
    intro x hx y hy
    rw [hA_incl]
    exact inclE_mem I ((I.L_dual y).1 hy x hx)
  have h1 : ∀ x ∈ I.L, ∀ w ∈ I.Lf, hA I (incl I x) w ∈ IntAf I.F I.E := by
    intro x hx w hw
    let P : Submodule (IntAf I.F I.E) (VA I) :=
      { carrier := {w | hA I (incl I x) w ∈ IntAf I.F I.E}
        add_mem' := fun {a b} ha hb => by
          show hA I (incl I x) (a + b) ∈ IntAf I.F I.E
          rw [hA_add_right]
          exact add_mem ha hb
        zero_mem' := by
          show hL I (incl I x) 0 ∈ IntAf I.F I.E
          rw [map_zero]
          exact zero_mem _
        smul_mem' := fun c w hw => by
          show hA I (incl I x) ((c : I.E ⊗[I.F] Af I.F) • w) ∈ IntAf I.F I.E
          rw [hA_smul_right]
          exact mul_mem c.2 hw }
    have hle : I.Lf ≤ P := by
      show Submodule.span _ _ ≤ P
      rw [Submodule.span_le]
      rintro _ ⟨⟨y, hy⟩, rfl⟩
      exact gen x hx y hy
    exact hle hw
  let Q : Submodule (IntAf I.F I.E) (VA I) :=
    { carrier := {w | hA I w v ∈ IntAf I.F I.E}
      add_mem' := fun {a b} ha hb => by
        show hA I (a + b) v ∈ IntAf I.F I.E
        rw [hA_add_left]
        exact add_mem ha hb
      zero_mem' := by
        show hA I 0 v ∈ IntAf I.F I.E
        have h0 := hA_smul_left I 0 v 0
        rw [zero_smul, map_zero, zero_mul] at h0
        rw [h0]
        exact zero_mem _
      smul_mem' := fun c w hw => by
        show hA I ((c : I.E ⊗[I.F] Af I.F) • w) v ∈ IntAf I.F I.E
        rw [hA_smul_left]
        exact mul_mem (sigA_mem I c.2) hw }
  have hle : I.Lf ≤ Q := by
    show Submodule.span _ _ ≤ Q
    rw [Submodule.span_le]
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    exact h1 y hy v hv
  exact hle hu

theorem hA_sub_right (u v w : VA I) : hA I u (v - w) = hA I u v - hA I u w := by
  show hL I u (v - w) = hL I u v - hL I u w
  exact map_sub _ _ _

end Gen

section Cong

theorem lt_sub {r : ℕ} {p q : ℕ} (h : p ≤ q) : {c : Fin r | c.1 < p} ⊆ {c | c.1 < q} := by
  intro c hc
  exact lt_of_lt_of_le hc h

variable (I : AutInst) (g : ℕ) {r k : ℕ} (e0 : Fin r → VA I) (z0 : VA I) (bw : Fin k → VA I)

theorem K_mul {x y : I.Gf} (hx : x ∈ I.Kset) (hy : y ∈ I.Kset) : x * y ∈ I.Kset := by
  exact (Formalism.UG.stabGL I.Lf).mul_mem hx hy

end Cong

section Chi

variable (I : AutInst) (g : ℕ)

theorem Z_zero : ZMod' I g 0 := by
  unfold Formalism.L2.SG.HidaSetting.ZMod'
  exact ⟨0, zero_mem _, (mul_zero _).symm⟩
theorem Z_add {a b : I.E ⊗[I.F] Af I.F} (ha : ZMod' I g a) (hb : ZMod' I g b) : ZMod' I g (a + b) := by
  unfold Formalism.L2.SG.HidaSetting.ZMod' at ha hb ⊢
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  exact ⟨s + t, add_mem hs ht, (mul_add _ _ _).symm⟩
theorem Z_sub {a b : I.E ⊗[I.F] Af I.F} (ha : ZMod' I g a) (hb : ZMod' I g b) : ZMod' I g (a - b) := by
  unfold Formalism.L2.SG.HidaSetting.ZMod' at ha hb ⊢
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  exact ⟨s - t, sub_mem hs ht, (mul_sub _ _ _).symm⟩
theorem Z_sum {ι : Type*} (s : Finset ι) (f : ι → I.E ⊗[I.F] Af I.F) (h : ∀ i ∈ s, ZMod' I g (f i)) :
    ZMod' I g (∑ i ∈ s, f i) := by
  exact Finset.sum_induction f (ZMod' I g) (fun a b ha hb => Z_add I g ha hb) (Z_zero I g) h
theorem Z_smul {c a : I.E ⊗[I.F] Af I.F} (hc : c ∈ IntAf I.F I.E) (ha : ZMod' I g a) : ZMod' I g (c * a) := by
  unfold Formalism.L2.SG.HidaSetting.ZMod' at ha ⊢
  obtain ⟨t, ht, rfl⟩ := ha
  exact ⟨c * t, mul_mem hc ht, by ring⟩
theorem Z_sig {a : I.E ⊗[I.F] Af I.F} (ha : ZMod' I g a) : ZMod' I g (sigA I a) := by
  unfold Formalism.L2.SG.HidaSetting.ZMod' at ha ⊢
  obtain ⟨t, ht, rfl⟩ := ha
  exact ⟨sigA I t, sigA_mem I ht, by rw [map_mul, map_natCast]⟩

def Qs (f : VA I) : Submodule (IntAf I.F I.E) (VA I) where
  carrier := {v | ZMod' I g (hA I f v)}
  add_mem' {v w} hv hw := by
    show ZMod' I g (hA I f (v + w)); rw [hA_add_right]; exact Z_add I g hv hw
  zero_mem' := by
    show ZMod' I g (hL I f 0); rw [map_zero]; exact Z_zero I g
  smul_mem' c v hv := by
    show ZMod' I g (hA I f ((c : I.E ⊗[I.F] Af I.F) • v)); rw [hA_smul_right]; exact Z_smul I g c.2 hv

theorem mL_Qs {f : VA I} (hf : f ∈ I.Lf) : mL I g ≤ Qs I g f := by
  unfold Formalism.L2.SG.HidaSetting.mL
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  show ZMod' I g (hA I f ((g : I.E ⊗[I.F] Af I.F) • x))
  rw [hA_smul_right]
  unfold Formalism.L2.SG.HidaSetting.ZMod'
  exact ⟨_, hA_int I hf hx, rfl⟩

variable {ψ : I.E ⊗[I.F] Af I.F → ℂ} (hadd : ∀ x y, ψ (x + y) = ψ x * ψ y)
  (hint : ∀ x ∈ IntAf I.F I.E, ψ x = 1)
include hadd hint

end Chi

section Frame

variable (I : AutInst) (g : ℕ) {r k : ℕ} (e0 f0 : Fin r → VA I) (z0 : VA I) (bw bwd : Fin k → VA I)

theorem Mb_Q (hbwd : ∀ i, bwd i ∈ I.Lf) (hbe : ∀ i a, ZMod' I g (hA I (bwd i) (e0 a)))
    (hbb : ∀ i j : Fin k, i ≠ j → ZMod' I g (hA I (bwd i) (bw j))) (i : Fin k) :
    Mo I g (Set.range e0 ∪ bw '' {j | j.1 < i.1}) ≤ Qs I g (bwd i) := by
  unfold Mo
  refine sup_le ?_ (mL_Qs I g (hbwd i))
  rw [Submodule.span_le]
  rintro _ (⟨a, rfl⟩ | ⟨j, hj, rfl⟩)
  · exact hbe i a
  · exact hbb i j (by intro h; subst h; exact lt_irrefl i.1 hj)

end Frame

end PI.UnitaryDimensionFormula.unitaryCongruence
