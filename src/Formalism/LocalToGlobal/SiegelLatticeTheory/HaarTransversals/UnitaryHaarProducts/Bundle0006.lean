module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKuCore
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.PoincareInHH.Cut.GU

open Formalism.L2.SG.Pf.Level

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Level

variable {D : D7} (X : HidaSetting D)

theorem zs_mL {t : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (ht : ZMod' X.B.I X.B.g t) {b : VA X.B.I}
    (hb : b ∈ X.B.I.Lf) : t • b ∈ mL X.B.I X.B.g := by
  obtain ⟨s, hs, rfl⟩ := ht
  rw [mul_comm, mul_smul]
  exact intsmul_mem X hs (unitaryCongruence.smul_mem_mL X.B.I hb)

theorem Mo_le_Qs {f : VA X.B.I} (hf : f ∈ X.B.I.Lf) (T : Set (VA X.B.I))
    (hT : ∀ s ∈ T, ZMod' X.B.I X.B.g (hA X.B.I f s)) :
    unitaryCongruence.Mo X.B.I X.B.g T ≤ unitaryCongruence.Qs X.B.I X.B.g f :=
  sup_le (Submodule.span_le.mpr fun s hs => hT s hs) (unitaryCongruence.mL_Qs X.B.I X.B.g hf)

def Gm (m : ℕ) : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I) :=
  unitaryCongruence.Mo X.B.I X.B.g (Set.range X.e0 ∪ X.bw '' {j | j.1 < m})

theorem flag {κ : X.B.I.Gf} (hκ : κ ∈ X.K2) :
    ∀ m, m ≤ D.R.k → ∀ w ∈ Gm X m, ((X.B.I.fmat κ - 1) ^ m) *ᵥ w ∈ Gm X 0 := by
  intro m
  induction m with
  | zero => intro _ w hw; rwa [pow_zero, one_mulVec]
  | succ m ih =>
    intro hm w hw
    rw [pow_succ, ← mulVec_mulVec]
    apply ih (Nat.le_of_succ_le hm)
    exact unitaryCongruence.b_step X.B.I X.B.g X.e0 X.z0 X.bw hκ.1 hκ.2 ⟨m, hm⟩ w hw

theorem bw_Gk (j : Fin D.R.k) : X.bw j ∈ Gm X D.R.k :=
  unitaryCongruence.sub_Mo X.B.I (Or.inr ⟨j, j.2, rfl⟩)

theorem adj1 (κ : X.B.I.Gf) (a b : VA X.B.I) :
    hA X.B.I a ((X.B.I.fmat κ - 1) *ᵥ b) = hA X.B.I ((X.B.I.fmat κ⁻¹ - 1) *ᵥ a) b := by
  have h0 : hA X.B.I a (X.B.I.fmat κ *ᵥ b) = hA X.B.I (X.B.I.fmat κ⁻¹ *ᵥ a) b := by
    have := hA_fmat X κ (X.B.I.fmat κ⁻¹ *ᵥ a) b
    rwa [mulVec_mulVec, fmat_mul_inv, one_mulVec] at this
  rw [sub_mulVec, sub_mulVec, one_mulVec, one_mulVec, unitaryCongruence.hA_sub_right, hA_sub_left, h0]

theorem adj (κ : X.B.I.Gf) : ∀ m (a b : VA X.B.I),
    hA X.B.I a (((X.B.I.fmat κ - 1) ^ m) *ᵥ b) = hA X.B.I (((X.B.I.fmat κ⁻¹ - 1) ^ m) *ᵥ a) b := by
  intro m
  induction m with
  | zero => intro a b; simp only [pow_zero, one_mulVec]
  | succ m ih =>
    intro a b
    rw [pow_succ, ← mulVec_mulVec, ih, adj1, pow_succ', ← mulVec_mulVec]

theorem pow_Lf {κ : X.B.I.Gf} (hκ : κ ∈ X.B.I.Kset) :
    ∀ m, ∀ y ∈ X.B.I.Lf, ((X.B.I.fmat κ - 1) ^ m) *ᵥ y ∈ X.B.I.Lf := by
  intro m
  induction m with
  | zero => intro y hy; rwa [pow_zero, one_mulVec]
  | succ m ih =>
    intro y hy
    rw [pow_succ, ← mulVec_mulVec]
    exact ih _ (unitaryCongruence.K_sub_mv X.B.I hκ hy)

theorem pow_Y (κ : X.B.I.Gf) (Y : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I))
    (hYM : ∀ v ∈ Y, X.B.I.fmat κ *ᵥ v ∈ Y) :
    ∀ m, ∀ y ∈ Y, ((X.B.I.fmat κ - 1) ^ m) *ᵥ y ∈ Y := by
  intro m
  induction m with
  | zero => intro y hy; rwa [pow_zero, one_mulVec]
  | succ m ih =>
    intro y hy
    rw [pow_succ, ← mulVec_mulVec]
    apply ih
    rw [sub_mulVec, one_mulVec]
    exact Y.sub_mem (hYM y hy) hy

theorem decomp (hP : ProjModG X) {v : VA X.B.I} (hv : v ∈ X.B.I.Lf)
    (ho : (∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) v) ∧ ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) v)) ∧
      ZMod' X.B.I X.B.g (hA X.B.I X.z0 v)) :
    v - ∑ i, hA X.B.I (X.bwd i) v • X.bw i - ∑ i, hA X.B.I (X.bw i) v • X.bwd i ∈ mL X.B.I X.B.g := by
  have hA' : ∑ a, hA X.B.I (X.f0 a) v • X.e0 a ∈ mL X.B.I X.B.g :=
    Submodule.sum_mem _ fun a _ => zs_mL X (ho.1 a).2 (X.vectorsInLattice.1 a).1
  have hB' : ∑ a, hA X.B.I (X.e0 a) v • X.f0 a ∈ mL X.B.I X.B.g :=
    Submodule.sum_mem _ fun a _ => zs_mL X (ho.1 a).1 (X.vectorsInLattice.1 a).2
  have hC' : hA X.B.I X.z0 v • X.z0 ∈ mL X.B.I X.B.g := zs_mL X ho.2 X.vectorsInLattice.2.1
  have he : v - ∑ i, hA X.B.I (X.bwd i) v • X.bw i - ∑ i, hA X.B.I (X.bw i) v • X.bwd i =
      piG X v + ∑ a, hA X.B.I (X.f0 a) v • X.e0 a + ∑ a, hA X.B.I (X.e0 a) v • X.f0 a -
        hA X.B.I X.z0 v • X.z0 := by
    unfold piG; abel
  rw [he]
  exact Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (hP v hv) hA') hB') hC'

theorem dual_zero (i : Fin D.R.k) (w : VA X.B.I) (hw : w = sigA X.B.I X.ew • w) :
    hA X.B.I (X.bwd i) w = 0 := by
  have h1 : hA X.B.I (sigA X.B.I X.ew • X.bwd i) w = X.ew * hA X.B.I (X.bwd i) w := by
    rw [unitaryCongruence.hA_smul_left, unitaryCongruence.sigA_sigA]
  rw [← X.bwd_w i] at h1
  have h2 : hA X.B.I (X.bwd i) w = sigA X.B.I X.ew * hA X.B.I (X.bwd i) w := by
    conv_lhs => rw [hw]
    rw [unitaryCongruence.hA_smul_right]
  calc hA X.B.I (X.bwd i) w = X.ew * (sigA X.B.I X.ew * hA X.B.I (X.bwd i) w) := by rw [← h2, ← h1]
    _ = (X.ew * sigA X.B.I X.ew) * hA X.B.I (X.bwd i) w := by ring
    _ = 0 := by rw [X.ew_orth, zero_mul]

theorem sigA_smul_bwd_sum_eq (c : Fin D.R.k → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :
    ∑ j, c j • X.bwd j = sigA X.B.I X.ew • ∑ j, c j • X.bwd j := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [X.bwd_w j]
  rw [smul_comm]

theorem coreOfProj {D : D7} (X : HidaSetting D) : CoreOfProj X := by
  intro hP κ hκ hκi Y hYL hYM hYo v hv
  set M := X.B.I.fmat κ with hMdef
  have hvL : v ∈ X.B.I.Lf := hYL hv
  set z := ((M - 1) ^ D.R.k) *ᵥ v with hzdef
  have hzY : z ∈ Y := pow_Y X κ Y hYM _ v hv
  have hzL : z ∈ X.B.I.Lf := hYL hzY

  have ha : ∀ i, ZMod' X.B.I X.B.g (hA X.B.I (X.bw i) z) := by
    intro i
    rw [hzdef, adj X κ]
    have hG : ((X.B.I.fmat κ⁻¹ - 1) ^ D.R.k) *ᵥ X.bw i ∈ Gm X 0 :=
      flag X hκi D.R.k le_rfl (X.bw i) (bw_Gk X i)
    have hle : Gm X 0 ≤ unitaryCongruence.Qs X.B.I X.B.g v := by
      refine Mo_le_Qs X hvL _ ?_
      rintro s (⟨a, rfl⟩ | ⟨j, hj, _⟩)
      · rw [unitaryCongruence.hA_symm X.B.I (X.e0 a) v]
        exact unitaryCongruence.Z_sig X.B.I X.B.g ((hYo v hv).1 a).1
      · exact absurd hj (Nat.not_lt_zero _)
    have hq : ZMod' X.B.I X.B.g (hA X.B.I v (((X.B.I.fmat κ⁻¹ - 1) ^ D.R.k) *ᵥ X.bw i)) := hle hG
    rw [unitaryCongruence.hA_symm X.B.I v]
    exact unitaryCongruence.Z_sig X.B.I X.B.g hq

  have hb : ∀ i, ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) z) := by
    intro i
    set v1 := ∑ j, hA X.B.I (X.bwd j) v • X.bw j with hv1
    set v2 := ∑ j, hA X.B.I (X.bw j) v • X.bwd j with hv2
    have hm : v - v1 - v2 ∈ mL X.B.I X.B.g := decomp X hP hvL (hYo v hv)
    have hsplit : z = ((M - 1) ^ D.R.k) *ᵥ v1 + ((M - 1) ^ D.R.k) *ᵥ v2 +
        ((M - 1) ^ D.R.k) *ᵥ (v - v1 - v2) := by
      rw [hzdef, ← mulVec_add, ← mulVec_add]; congr 1; abel
    rw [hsplit, unitaryCongruence.hA_add_right, unitaryCongruence.hA_add_right]
    refine unitaryCongruence.Z_add X.B.I X.B.g (unitaryCongruence.Z_add X.B.I X.B.g ?_ ?_) ?_
    · have hv1G : v1 ∈ Gm X D.R.k :=
        Submodule.sum_mem _ fun j _ =>
          intsmul_mem X (unitaryCongruence.hA_int X.B.I (X.vectorsInLattice.2.2 j).2 hvL) (bw_Gk X j)
      have hG := flag X hκ D.R.k le_rfl v1 hv1G
      have hle : Gm X 0 ≤ unitaryCongruence.Qs X.B.I X.B.g (X.bwd i) := by
        refine Mo_le_Qs X (X.vectorsInLattice.2.2 i).2 _ ?_
        rintro s (⟨a, rfl⟩ | ⟨j, hj, _⟩)
        · exact (reference_frame_congruences X).2.2.1 i a
        · exact absurd hj (Nat.not_lt_zero _)
      exact hle hG
    · rw [dual_zero X i _ (by rw [hv2, ← mulVec_smul, ← sigA_smul_bwd_sum_eq X])]
      exact unitaryCongruence.Z_zero X.B.I X.B.g
    · exact Z_right X (X.vectorsInLattice.2.2 i).2
        (mL_pres X _ (pow_Lf X hκ.1 D.R.k) _ hm)

  have hd := decomp X hP hzL (hYo z hzY)
  have h1 : ∑ i, hA X.B.I (X.bwd i) z • X.bw i ∈ mL X.B.I X.B.g :=
    Submodule.sum_mem _ fun i _ => zs_mL X (hb i) (X.vectorsInLattice.2.2 i).1
  have h2 : ∑ i, hA X.B.I (X.bw i) z • X.bwd i ∈ mL X.B.I X.B.g :=
    Submodule.sum_mem _ fun i _ => zs_mL X (ha i) (X.vectorsInLattice.2.2 i).2
  have he : z = (z - ∑ i, hA X.B.I (X.bwd i) z • X.bw i - ∑ i, hA X.B.I (X.bw i) z • X.bwd i) +
      ∑ i, hA X.B.I (X.bwd i) z • X.bw i + ∑ i, hA X.B.I (X.bw i) z • X.bwd i := by abel
  rw [he]
  exact Submodule.add_mem _ (Submodule.add_mem _ hd h1) h2

end Formalism.L2.SG.PoincareInHH.Cut.GU
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKuProj
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.PoincareInHH.Cut.GU

open Formalism.L2.SG.Pf.Level

variable {D : D7} (X : HidaSetting D)

theorem Zneg {t : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (h : ZMod' X.B.I X.B.g t) :
    ZMod' X.B.I X.B.g (-t) := by
  have := Formalism.L2.SG.Pf.unitaryCongruence.Z_sub X.B.I X.B.g (Formalism.L2.SG.Pf.unitaryCongruence.Z_zero X.B.I X.B.g) h
  rwa [zero_sub] at this

theorem Zswap {x y : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (h : ZMod' X.B.I X.B.g (x - y)) :
    ZMod' X.B.I X.B.g (y - x) := by
  have := Zneg X h; rwa [neg_sub] at this

theorem Zsw {u v : VA X.B.I} (h : ZMod' X.B.I X.B.g (hA X.B.I u v)) :
    ZMod' X.B.I X.B.g (hA X.B.I v u) := by
  rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_symm X.B.I u v]; exact Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I X.B.g h

theorem Z0 {t : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (h : ZMod' X.B.I X.B.g t) :
    ZMod' X.B.I X.B.g (0 - t) := by
  rw [zero_sub]; exact Zneg X h

theorem Zsw_ite {m : ℕ} {u v : VA X.B.I} {c d : Fin m} (x : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
    (h : ZMod' X.B.I X.B.g (hA X.B.I u v - if c = d then x else 0)) :
    ZMod' X.B.I X.B.g ((if d = c then sigA X.B.I x else 0) - hA X.B.I v u) := by
  have h' := Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I X.B.g h
  rw [map_sub, ← Formalism.L2.SG.Pf.unitaryCongruence.hA_symm X.B.I u v] at h'
  have h'' := Zswap X h'
  have e : sigA X.B.I (if c = d then x else 0) = if d = c then sigA X.B.I x else 0 := by
    by_cases h1 : d = c
    · subst h1; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg h1, if_neg (Ne.symm h1), map_zero]
  rw [e] at h''
  exact h''

theorem smul_mL {t : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} {b : VA X.B.I} (ht : ZMod' X.B.I X.B.g t)
    (hb : b ∈ X.B.I.Lf) : t • b ∈ mL X.B.I X.B.g := by
  obtain ⟨s, hs, rfl⟩ := ht
  rw [mul_comm, mul_smul]
  exact Formalism.L2.SG.Pf.Level.intsmul_mem X hs (Formalism.L2.SG.Pf.unitaryCongruence.smul_mem_mL X.B.I hb)

theorem sum_mL {m : ℕ} (c : Fin m → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (b : Fin m → VA X.B.I)
    (hc : ∀ i, ZMod' X.B.I X.B.g (c i)) (hb : ∀ i, b i ∈ X.B.I.Lf) :
    ∑ i, c i • b i ∈ mL X.B.I X.B.g :=
  Submodule.sum_mem _ fun i _ => smul_mL X (hc i) (hb i)

theorem piG_add (v w : VA X.B.I) : piG X (v + w) = piG X v + piG X w := by
  simp only [piG, Formalism.L2.SG.Pf.unitaryCongruence.hA_add_right, add_smul, Finset.sum_add_distrib]
  abel

theorem piG_zero : piG X 0 = 0 := by
  have h := piG_add X 0 0
  rw [add_zero] at h
  simpa using h

theorem piG_smul (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (v : VA X.B.I) : piG X (c • v) = c • piG X v := by
  simp only [piG, Formalism.L2.SG.Pf.unitaryCongruence.hA_smul_right, mul_smul, smul_sub, smul_add, Finset.smul_sum]

def PS : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I) where
  carrier := {v | piG X v ∈ mL X.B.I X.B.g}
  add_mem' {v w} hv hw := by
    show piG X (v + w) ∈ mL X.B.I X.B.g
    rw [piG_add]; exact add_mem hv hw
  zero_mem' := by
    show piG X 0 ∈ mL X.B.I X.B.g
    rw [piG_zero]; exact zero_mem _
  smul_mem' c v hv := by
    show piG X (c • v) ∈ mL X.B.I X.B.g
    rw [Subring.smul_def, piG_smul]; exact Formalism.L2.SG.Pf.Level.intsmul_mem X c.2 hv

theorem piG_reduce (b : VA X.B.I) (α β : Fin D.R.rS → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
    (γ : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (μ ν : Fin D.R.k → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
    (hb : b - (∑ a, α a • X.e0 a + ∑ a, β a • X.f0 a - γ • X.z0 + ∑ i, μ i • X.bw i
      + ∑ i, ν i • X.bwd i) ∈ mL X.B.I X.B.g)
    (hα : ∀ a, ZMod' X.B.I X.B.g (α a - hA X.B.I (X.f0 a) b))
    (hβ : ∀ a, ZMod' X.B.I X.B.g (β a - hA X.B.I (X.e0 a) b))
    (hγ : ZMod' X.B.I X.B.g (γ - hA X.B.I X.z0 b))
    (hμ : ∀ i, ZMod' X.B.I X.B.g (μ i - hA X.B.I (X.bwd i) b))
    (hν : ∀ i, ZMod' X.B.I X.B.g (ν i - hA X.B.I (X.bw i) b)) : piG X b ∈ mL X.B.I X.B.g := by
  have e : piG X b = (b - (∑ a, α a • X.e0 a + ∑ a, β a • X.f0 a - γ • X.z0 + ∑ i, μ i • X.bw i
      + ∑ i, ν i • X.bwd i)) + ∑ a, (α a - hA X.B.I (X.f0 a) b) • X.e0 a
      + ∑ a, (β a - hA X.B.I (X.e0 a) b) • X.f0 a - (γ - hA X.B.I X.z0 b) • X.z0
      + ∑ i, (μ i - hA X.B.I (X.bwd i) b) • X.bw i + ∑ i, (ν i - hA X.B.I (X.bw i) b) • X.bwd i := by
    simp only [piG, sub_smul, Finset.sum_sub_distrib]
    abel
  rw [e]
  have he : ∀ a, X.e0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).1
  have hf : ∀ a, X.f0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).2
  have hz : X.z0 ∈ X.B.I.Lf := X.vectorsInLattice.2.1
  have hw : ∀ i, X.bw i ∈ X.B.I.Lf := fun i => (X.vectorsInLattice.2.2 i).1
  have hd : ∀ i, X.bwd i ∈ X.B.I.Lf := fun i => (X.vectorsInLattice.2.2 i).2
  exact add_mem (add_mem (sub_mem (add_mem (add_mem hb (sum_mL X _ _ hα he)) (sum_mL X _ _ hβ hf))
    (smul_mL X hγ hz)) (sum_mL X _ _ hμ hw)) (sum_mL X _ _ hν hd)

theorem hA_bw_bw (i j : Fin D.R.k) : hA X.B.I (X.bw i) (X.bw j) = 0 := by
  calc hA X.B.I (X.bw i) (X.bw j) = hA X.B.I (X.ew • X.bw i) (X.ew • X.bw j) := by
        rw [← X.bw_w i, ← X.bw_w j]
    _ = sigA X.B.I X.ew * (X.ew * hA X.B.I (X.bw i) (X.bw j)) := by
        rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_smul_left, Formalism.L2.SG.Pf.unitaryCongruence.hA_smul_right]
    _ = 0 := by rw [← mul_assoc, mul_comm (sigA X.B.I X.ew) X.ew, X.ew_orth, zero_mul]

theorem hA_bwd_bwd (i j : Fin D.R.k) : hA X.B.I (X.bwd i) (X.bwd j) = 0 := by
  calc hA X.B.I (X.bwd i) (X.bwd j)
        = hA X.B.I (sigA X.B.I X.ew • X.bwd i) (sigA X.B.I X.ew • X.bwd j) := by
        rw [← X.bwd_w i, ← X.bwd_w j]
    _ = sigA X.B.I (sigA X.B.I X.ew) * (sigA X.B.I X.ew * hA X.B.I (X.bwd i) (X.bwd j)) := by
        rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_smul_left, Formalism.L2.SG.Pf.unitaryCongruence.hA_smul_right]
    _ = 0 := by rw [Formalism.L2.SG.Pf.unitaryCongruence.sigA_sigA, ← mul_assoc, X.ew_orth, zero_mul]

theorem piG_mL {m : VA X.B.I} (hm : m ∈ mL X.B.I X.B.g) : piG X m ∈ mL X.B.I X.B.g := by
  refine piG_reduce X m 0 0 0 0 0 ?_ ?_ ?_ ?_ ?_ ?_
  · simpa using hm
  · intro a; exact Z0 X (Formalism.L2.SG.Pf.Level.Z_right X (X.vectorsInLattice.1 a).2 hm)
  · intro a; exact Z0 X (Formalism.L2.SG.Pf.Level.Z_right X (X.vectorsInLattice.1 a).1 hm)
  · exact Z0 X (Formalism.L2.SG.Pf.Level.Z_right X X.vectorsInLattice.2.1 hm)
  · intro i; exact Z0 X (Formalism.L2.SG.Pf.Level.Z_right X (X.vectorsInLattice.2.2 i).2 hm)
  · intro i; exact Z0 X (Formalism.L2.SG.Pf.Level.Z_right X (X.vectorsInLattice.2.2 i).1 hm)

theorem projection_e0_mem_ideal (c : Fin D.R.rS) : piG X (X.e0 c) ∈ mL X.B.I X.B.g := by
  refine piG_reduce X _ (fun a => if a = c then sigA X.B.I 1 else 0) 0 0 0 0 ?_ ?_ ?_ ?_ ?_ ?_
  · simp
  · intro a; exact Zsw_ite X 1 (X.gramIntegral c a).2.2
  · intro a; exact Z0 X (X.gramIntegral a c).1
  · exact Z0 X (Zsw X (X.formsAtZero.2 c).1)
  · intro i; exact Z0 X (Zsw X ((X.weightVectorsIntegral i).2.2 c).2.2.1)
  · intro i; exact Z0 X (Zsw X ((X.weightVectorsIntegral i).2.2 c).1)

theorem projection_f0_mem_ideal (c : Fin D.R.rS) : piG X (X.f0 c) ∈ mL X.B.I X.B.g := by
  refine piG_reduce X _ 0 (fun a => if a = c then 1 else 0) 0 0 0 ?_ ?_ ?_ ?_ ?_ ?_
  · simp
  · intro a; exact Z0 X (X.gramIntegral a c).2.1
  · intro a; exact Zswap X (X.gramIntegral a c).2.2
  · exact Z0 X (Zsw X (X.formsAtZero.2 c).2)
  · intro i; exact Z0 X (Zsw X ((X.weightVectorsIntegral i).2.2 c).2.2.2)
  · intro i; exact Z0 X (Zsw X ((X.weightVectorsIntegral i).2.2 c).2.1)

theorem projection_z0_mem_ideal : piG X X.z0 ∈ mL X.B.I X.B.g := by
  refine piG_reduce X _ 0 0 (-1) 0 0 ?_ ?_ ?_ ?_ ?_ ?_
  · simp
  · intro a; exact Z0 X (X.formsAtZero.2 a).2
  · intro a; exact Z0 X (X.formsAtZero.2 a).1
  · have := Zneg X X.formsAtZero.1
    rw [neg_add, add_comm] at this
    rwa [sub_eq_add_neg]
  · intro i; exact Z0 X (Zsw X (X.weightVectorsIntegral i).2.1)
  · intro i; exact Z0 X (Zsw X (X.weightVectorsIntegral i).1)

theorem piG_bw (c : Fin D.R.k) : piG X (X.bw c) ∈ mL X.B.I X.B.g := by
  refine piG_reduce X _ 0 0 0 (fun i => if i = c then X.ew else 0) 0 ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, ite_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, zero_add, add_zero, sub_zero]
    rw [← X.bw_w c, sub_self]; exact zero_mem _
  · intro a; exact Z0 X ((X.weightVectorsIntegral c).2.2 a).2.1
  · intro a; exact Z0 X ((X.weightVectorsIntegral c).2.2 a).1
  · exact Z0 X (X.weightVectorsIntegral c).1
  · intro i; exact Zswap X (X.bw_dual i c)
  · intro i; rw [hA_bw_bw, Pi.zero_apply, sub_zero]; exact Formalism.L2.SG.Pf.unitaryCongruence.Z_zero X.B.I X.B.g

theorem piG_bwd (c : Fin D.R.k) : piG X (X.bwd c) ∈ mL X.B.I X.B.g := by
  refine piG_reduce X _ 0 0 0 0 (fun i => if i = c then sigA X.B.I X.ew else 0) ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, ite_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, zero_add, add_zero, sub_zero]
    rw [← X.bwd_w c, sub_self]; exact zero_mem _
  · intro a; exact Z0 X ((X.weightVectorsIntegral c).2.2 a).2.2.2
  · intro a; exact Z0 X ((X.weightVectorsIntegral c).2.2 a).2.2.1
  · exact Z0 X (X.weightVectorsIntegral c).2.1
  · intro i; rw [hA_bwd_bwd, Pi.zero_apply, sub_zero]; exact Formalism.L2.SG.Pf.unitaryCongruence.Z_zero X.B.I X.B.g
  · intro i; exact Zsw_ite X X.ew (X.bw_dual c i)

theorem projModG_holds {D : D7} (X : HidaSetting D) : ProjModG X := by
  intro v hv
  have h : v ∈ Submodule.span (IntAf X.B.I.F X.B.I.E)
      (Set.range X.e0 ∪ Set.range X.f0 ∪ {X.z0} ∪ Set.range X.bw ∪ Set.range X.bwd) ⊔ mL X.B.I X.B.g :=
    X.latticeSpan v hv
  have hle : Submodule.span (IntAf X.B.I.F X.B.I.E)
      (Set.range X.e0 ∪ Set.range X.f0 ∪ {X.z0} ∪ Set.range X.bw ∪ Set.range X.bwd) ⊔ mL X.B.I X.B.g
        ≤ PS X := by
    refine sup_le (Submodule.span_le.2 ?_) (fun m hm => piG_mL X hm)
    rintro _ ((((⟨a, rfl⟩ | ⟨a, rfl⟩) | h0) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · exact projection_e0_mem_ideal X a
    · exact projection_f0_mem_ideal X a
    · rw [Set.mem_singleton_iff] at h0; subst h0; exact projection_z0_mem_ideal X
    · exact piG_bw X i
    · exact piG_bwd X i
  exact hle h

end Formalism.L2.SG.PoincareInHH.Cut.GU
end
end

