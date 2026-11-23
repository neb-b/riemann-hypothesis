module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscriminantNormShapesBis
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0021
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0017
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscEquiv

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiagQConjTranspose
section
open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.discriminantNormShapes

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5

def SolveOnto : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (m : ℕ) (a : Fin m → 𝓞 F), (∀ i, a i ≠ 0) →
    ∀ k : ℕ, 2 * vJof 𝔭 a + 1 ≤ k → ∀ Y : udPre K 𝔭 k a,
      ∃ Y' P W Z Z₀ : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k),
        Y' - Y.1 = Z₀ * diagQ K 𝔭 k a ∧ P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y' ∧
        Y'ᴴ * diagQ K 𝔭 k a * Y' - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a ∧
        W + Pᴴ * Z + Zᴴ * P + Zᴴ * diagQ K 𝔭 k a * Z = 0

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}

private theorem star_algebraMap_ringOfIntegers (x : 𝓞 F) :
    star (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap (𝓞 F) (𝓞 K) x := by
  have h := Formalism.HermitianLattices.Ext.L3.localizedQuotients.star_ι (K := K) (F := F) Fact.out x
  exact FaithfulSMul.algebraMap_injective (𝓞 K) K h

theorem diagQ_conjTranspose (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) :
    (diagQ K 𝔭 k a)ᴴ = diagQ K 𝔭 k a := by
  unfold diagQ
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  rw [Pi.star_apply, star_mk, star_algebraMap_ringOfIntegers]

theorem hom_shift {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : Fin m → 𝓞 F}
    {Y P : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)}
    (hPY : P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y) (Z : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) :
    (P + diagQ K 𝔭 k a * Z) * diagQ K 𝔭 k a = diagQ K 𝔭 k a * (Y + Z * diagQ K 𝔭 k a) := by
  rw [Matrix.add_mul, hPY, Matrix.mul_add, Matrix.mul_assoc]

theorem form_shift {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : Fin m → 𝓞 F}
    {Y P W : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)}
    (hPY : P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y)
    (hW : Yᴴ * diagQ K 𝔭 k a * Y - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a)
    (Z : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) :
    (Y + Z * diagQ K 𝔭 k a)ᴴ * diagQ K 𝔭 k a * (Y + Z * diagQ K 𝔭 k a) - diagQ K 𝔭 k a =
      diagQ K 𝔭 k a * (W + Pᴴ * Z + Zᴴ * P + Zᴴ * diagQ K 𝔭 k a * Z) * diagQ K 𝔭 k a := by
  have hH := diagQ_conjTranspose (K := K) 𝔭 k a
  have h1 : Yᴴ * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Pᴴ := by
    have h := congrArg Matrix.conjTranspose hPY
    rw [conjTranspose_mul, conjTranspose_mul, hH] at h
    exact h.symm
  calc _ = Yᴴ * diagQ K 𝔭 k a * Y - diagQ K 𝔭 k a + Yᴴ * diagQ K 𝔭 k a * Z * diagQ K 𝔭 k a + diagQ K 𝔭 k a * Zᴴ * (diagQ K 𝔭 k a * Y) +
        diagQ K 𝔭 k a * Zᴴ * diagQ K 𝔭 k a * Z * diagQ K 𝔭 k a := by
        simp only [conjTranspose_add, conjTranspose_mul, hH, Matrix.add_mul, Matrix.mul_add,
          Matrix.mul_assoc]
        abel
    _ = _ := by
        rw [hW, h1, ← hPY]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]

theorem mem_skSet_of_solve {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : Fin m → 𝓞 F}
    {Y P W Z : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)}
    (hPY : P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y)
    (hW : Yᴴ * diagQ K 𝔭 k a * Y - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a)
    (hZ : W + Pᴴ * Z + Zᴴ * P + Zᴴ * diagQ K 𝔭 k a * Z = 0) :
    Y + Z * diagQ K 𝔭 k a ∈ skSet K 𝔭 k a := by
  show (Y + Z * diagQ K 𝔭 k a)ᴴ * diagQ K 𝔭 k a * (Y + Z * diagQ K 𝔭 k a) = diagQ K 𝔭 k a
  have h := form_shift hPY hW Z
  rw [hZ, Matrix.mul_zero, Matrix.zero_mul] at h
  exact sub_eq_zero.mp h

theorem liftOnto_of_solve (hS : SolveOnto) : LiftOnto := by
  intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk Y
  obtain ⟨Y', P, W, Z, Z₀, hY, hPY, hW, hZ⟩ := hS K F hK 𝔭 h𝔭 m a ha k hk Y
  refine ⟨Y' + Z * diagQ K 𝔭 k a, mem_skSet_of_solve hPY hW hZ, Z₀ + Z, ?_⟩
  rw [Matrix.add_mul, ← hY]
  abel

theorem discOnto_of_solve (hU : UDModel) (hS : SolveOnto) : DiscOnto :=
  discOnto_of_lift hU (liftOnto_of_solve hS)

end Formalism.L2.SG.Pf.discriminantNormShapes
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsDualGen
section
noncomputable section

open NumberField Module Formalism.MainNotions.S
open Classical

namespace Formalism.L2.SG.Pf.Cnt.R1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

theorem surj_pairing {m : ℕ} (f : Fin m → S.V) (hf : LinearIndependent E f) :
    Function.Surjective (LinearMap.pi (fun a => S.hT (f a)) : S.V →ₗ[E] (Fin m → E)) := by
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
  set c : Fin m → E := fun a => φ (fun j => if a = j then 1 else 0) with hc
  have hφx : ∀ x : Fin m → E, φ x = ∑ a, x a * c a := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_smul, hc]
  have hv : ∀ v : S.V, S.hT (∑ a, star (c a) • f a) v = 0 := by
    intro v
    have h1 : φ ((LinearMap.pi (fun a => S.hT (f a)) : S.V →ₗ[E] (Fin m → E)) v) = 0 := by
      have : (LinearMap.pi (fun a => S.hT (f a)) : S.V →ₗ[E] (Fin m → E)) v ∈
          LinearMap.range (LinearMap.pi (fun a => S.hT (f a)) : S.V →ₗ[E] (Fin m → E)) := ⟨v, rfl⟩
      have h2 := Submodule.mem_map_of_mem (f := φ) this
      exact (Submodule.eq_bot_iff _).1 hφ _ h2
    rw [hφx] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    simp only [LinearMap.map_smulₛₗ, starRingEnd_apply, star_star, LinearMap.smul_apply, smul_eq_mul]
    rw [← h1]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [LinearMap.pi_apply, mul_comm]
  have h0 : ∑ a, star (c a) • f a = 0 := S.nondeg.1 _ hv
  have hc0 : ∀ a, c a = 0 := by
    intro a
    have := Fintype.linearIndependent_iff.1 hf _ h0 a
    simpa using this
  apply hφ0
  apply LinearMap.ext
  intro x
  rw [hφx]
  simp [hc0]

variable {r : ℕ}

theorem exists_dual_gen (e : Fin r → S.V) (z : S.V) (N : ℕ) (hN : 0 < N) (hind : LinearIndependent E e)
    (he : ∀ a b, S.hT (e a) (e b) = 0) (hez : ∀ a, S.hT (e a) z = 0) (hzz : S.hT z z = -(N : E)) :
    ∃ y : Fin r → S.V, Dual e y z N := by
  let f : Fin (r + 1) → S.V := Fin.snoc (α := fun _ => S.V) e z
  have hze : ∀ a, S.hT z (e a) = 0 := fun a => hsw0 S (hez a)
  have hzz0 : S.hT z z ≠ 0 := by rw [hzz, neg_ne_zero]; exact_mod_cast hN.ne'
  have hf : LinearIndependent E f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fin.sum_univ_castSucc] at hc
    simp only [f, Fin.snoc_castSucc, Fin.snoc_last] at hc
    have hl : c (Fin.last r) = 0 := by
      have h1 := congrArg (S.hT z) hc
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), map_sum, map_zero] at h1
      simp only [map_smul, smul_eq_mul, hze, mul_zero, Finset.sum_const_zero, zero_add] at h1
      exact (mul_eq_zero.1 h1).resolve_right hzz0
    rw [hl, zero_smul, add_zero] at hc
    have hcs := Fintype.linearIndependent_iff.1 hind _ hc
    intro i
    induction i using Fin.lastCases with
    | last => exact hl
    | cast a => exact hcs a
  have hs := surj_pairing f hf
  choose y0 hy0 using fun a : Fin r => hs (fun j => if j = Fin.castSucc a then (1 : E) else 0)
  have hey0 : ∀ b a, S.hT (e b) (y0 a) = if b = a then 1 else 0 := by
    intro b a
    have := congrFun (hy0 a) (Fin.castSucc b)
    simp only [LinearMap.pi_apply, f, Fin.snoc_castSucc, Fin.castSucc_inj] at this
    exact this
  have hzy0 : ∀ a, S.hT z (y0 a) = 0 := by
    intro a
    have := congrFun (hy0 a) (Fin.last r)
    simp only [LinearMap.pi_apply, f, Fin.snoc_last] at this
    rw [this, if_neg (Fin.castSucc_lt_last a).ne']
  have hy0e : ∀ a d, S.hT (y0 a) (e d) = if d = a then 1 else 0 := by
    intro a d; rw [hsw, hey0]; split_ifs <;> simp
  have hL : ∀ (c : Fin r → E) (v : S.V), S.hT (∑ d, c d • e d) v = ∑ d, star (c d) * S.hT (e d) v := by
    intro c v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
  have hR : ∀ (c : Fin r → E) (v : S.V), S.hT v (∑ d, c d • e d) = ∑ d, c d * S.hT v (e d) := by
    intro c v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul]
  set c : Fin r → Fin r → E := fun a d => S.hT (y0 d) (y0 a) / 2 with hc
  set y : Fin r → S.V := fun a => y0 a - ∑ d, c a d • e d with hy
  have hst : ∀ a b, star (S.hT (y0 b) (y0 a)) = S.hT (y0 a) (y0 b) := fun a b => (hsw S _ _).symm
  refine ⟨y, ⟨he, fun a b => ?_, fun a b => ?_, hez, fun a => ?_, hzz⟩⟩
  · have h1 : S.hT (y0 a) (∑ d, c b d • e d) = c b a := by
      rw [hR]; simp [hy0e]
    have h2 : S.hT (∑ d, c a d • e d) (y0 b) = star (c a b) := by
      rw [hL]; simp [hey0]
    have h3 : S.hT (∑ d, c a d • e d) (∑ d, c b d • e d) = 0 := by
      rw [hL]; simp [hR, he]
    simp only [hy, map_sub, LinearMap.sub_apply, h1, h2, h3]
    simp only [hc]
    rw [star_div₀, hst, star_ofNat]
    ring
  · simp only [hy, map_sub, hR, hey0, he, mul_zero, Finset.sum_const_zero, sub_zero]
  · simp only [hy, map_sub, LinearMap.sub_apply, hL, hez, mul_zero, Finset.sum_const_zero, sub_zero]
    rw [hsw, hzy0, star_zero]

def Wsp (e y : Fin r → S.V) (z : S.V) : Submodule E S.V :=
  LinearMap.ker (LinearMap.pi (Sum.elim (Sum.elim (fun a => S.hT (e a)) (fun a => S.hT (y a)))
    (fun _ : Unit => S.hT z)) : S.V →ₗ[E] ((Fin r ⊕ Fin r) ⊕ Unit → E))

theorem mem_Wsp {e y : Fin r → S.V} {z w : S.V} : w ∈ Wsp e y z ↔ IsW e y z w := by
  simp only [Wsp, LinearMap.mem_ker, funext_iff, LinearMap.pi_apply, Pi.zero_apply, Sum.forall,
    Sum.elim_inl, Sum.elim_inr, forall_const, IsW]
  tauto

theorem finrank_Wsp (e y : Fin r → S.V) (z : S.V) :
    finrank E S.V ≤ finrank E (Wsp e y z) + (2 * r + 1) := by
  have h := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi (Sum.elim (Sum.elim (fun a => S.hT (e a))
    (fun a => S.hT (y a))) (fun _ : Unit => S.hT z)) : S.V →ₗ[E] ((Fin r ⊕ Fin r) ⊕ Unit → E))
  have h2 := Submodule.finrank_le (LinearMap.range (LinearMap.pi (Sum.elim (Sum.elim (fun a => S.hT (e a))
    (fun a => S.hT (y a))) (fun _ : Unit => S.hT z)) : S.V →ₗ[E] ((Fin r ⊕ Fin r) ⊕ Unit → E)))
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at h2
  rw [Wsp]
  omega

end Gen

section D7

variable (D : Formalism.BasicNotions.D7)

theorem dual_of_flag {N : ℕ} (hN : 0 < N) (F0 : FlagG (VS D) D.R.rS (N : D.host.E)) :
    ∃ y, Dual F0.e y F0.z N :=
  exists_dual_gen F0.e F0.z N hN F0.e_indep F0.e_iso F0.z_orth F0.z_norm

theorem posW {N : ℕ} (hN : 0 < N) {e y : Fin D.R.rS → (VS D).V} {z : (VS D).V} (h : Dual e y z N)
    (w : (VS D).V) (hw : IsW e y z w) (hw0 : w ≠ 0) (φ : D.host.E →+* ℂ) : 0 < (φ ((VS D).hT w w)).re := by
  have hτ : ∀ τ : D.host.E →+* ℂ, ∀ a, τ (star a) = starRingEnd ℂ (τ a) := fun τ => D.sp.cm.cmUnram.2.1 τ
  have hsemi : ∀ τ : D.host.E →+* ℂ, ∀ v, IsW e y z v → 0 ≤ (τ ((VS D).hT v v)).re := by
    intro τ v hv
    have hs := D.sp.Y_sig 0 τ
    rw [D.sp.baseSpace_signature_eq τ] at hs
    exact semidefG h hN τ (hτ τ) hs v hv
  refine lt_of_le_of_ne (hsemi φ w hw) fun h0 => hw0 ?_
  refine isoZeroG h hN φ (hτ φ) (hsemi φ) w hw ?_
  apply φ.injective
  rw [real_of φ (hτ φ) w, ← h0, Complex.ofReal_zero, map_zero]

theorem two_le_Wsp (e y : Fin D.R.rS → (VS D).V) (z : (VS D).V) : 2 ≤ finrank D.host.E (Wsp e y z) := by
  have hV : finrank D.host.E (VS D).V = D.R.k + D.R.m - 1 := by
    rw [(VS D).rank_eq, D.sp.Y_rank 0 (Nat.zero_le _)]
    simp [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.r]
  have hm2 := D.R.two_le_m
  obtain ⟨j, hj⟩ := D.R.m_even
  have hrS : 2 * D.R.rS + 1 = D.R.m - 1 := by
    unfold Formalism.BasicNotions.Ranks.rS
    rw [hj]
    omega
  have h1 := finrank_Wsp e y z
  rw [hV, hrS] at h1
  have hk := D.R.f_le_k
  have he : 0 < D.R.ord := D.R.ord_pos
  generalize finrank D.host.E (Wsp e y z) = w at h1 ⊢
  omega


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem exists_W_vec {N : ℕ} (hN : 0 < N) {e y : Fin D.R.rS → (VS D).V} {z : (VS D).V} (h : Dual e y z N)
    (t : D.host.E) (ht : star t = t) (htp : Formalism.HermitianLattices.Ext.L3.TotPos t) :
    ∃ w : (VS D).V, IsW e y z w ∧ (VS D).hT w w = t := by
  let hW : Wsp e y z →ₗ⋆[D.host.E] Wsp e y z →ₗ[D.host.E] D.host.E :=
    ((VS D).hT.comp (Wsp e y z).subtype).compl₂ (Wsp e y z).subtype
  have hs : hW.IsSymm := ⟨fun x x' => (VS D).herm.eq x x'⟩
  have hd : Formalism.HermitianLattices.Ext.L3.IsTotPosDef hW := by
    intro x hx φ
    have hx' : (x : (VS D).V) ≠ 0 := fun h0 => hx (Subtype.ext h0)
    exact posW D hN h x (mem_Wsp.1 x.2) hx' φ
  obtain ⟨x, hx⟩ := Formalism.HermitianLattices.Ext.L3.exists_vec_of_hermRep Formalism.HermitianLattices.Ext.L3.hermRepUnram D.sp.cm.cmUnram hs hd
    (two_le_Wsp D e y z) t ht htp
  exact ⟨x, mem_Wsp.1 x.2, hx⟩

end D7

end Formalism.L2.SG.Pf.Cnt.R1
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsPermOfMin
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

def cntGe {n : ℕ} (e : Fin n → ℕ) (v : ℕ) : ℕ := (Finset.univ.filter fun i => v ≤ e i).card

theorem cntGe_succ {n : ℕ} (e : Fin n → ℕ) (v : ℕ) :
    cntGe e (v + 1) + ∑ i, min (e i) v = ∑ i, min (e i) (v + 1) := by
  unfold cntGe
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> omega

theorem cntGe_eq {n : ℕ} (e e' : Fin n → ℕ) (H : ∀ j, ∑ i, min (e i) j = ∑ i, min (e' i) j) (v : ℕ) :
    cntGe e v = cntGe e' v := by
  cases v with
  | zero => simp [cntGe]
  | succ w =>
    have h1 := cntGe_succ e w
    have h2 := cntGe_succ e' w
    rw [H w, H (w + 1)] at h1
    omega

theorem card_eq_val {n : ℕ} (e : Fin n → ℕ) (v : ℕ) :
    (Finset.univ.filter fun i => e i = v).card = cntGe e v - cntGe e (v + 1) := by
  have key : cntGe e v = (Finset.univ.filter fun i => e i = v).card + cntGe e (v + 1) := by
    unfold cntGe
    simp only [Finset.card_filter]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> omega
  omega

theorem exists_perm_of_min {n : ℕ} (e e' : Fin n → ℕ) (H : ∀ j, ∑ i, min (e i) j = ∑ i, min (e' i) j) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, e' (σ i) = e i := by
  classical
  have hc : ∀ v, (Finset.univ.filter fun i => e i = v).card =
      (Finset.univ.filter fun i => e' i = v).card := by
    intro v
    rw [card_eq_val, card_eq_val, cntGe_eq e e' H, cntGe_eq e e' H]
  refine ⟨Equiv.ofFiberEquiv (f := e) (g := e') fun v => Fintype.equivOfCardEq ?_,
    fun i => Equiv.ofFiberEquiv_map _ i⟩
  rw [Fintype.card_subtype, Fintype.card_subtype]
  convert hc v

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem isJordanIn_perm {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V} {L : Submodule (𝓞 K) V}
    {𝔭 : Ideal (𝓞 F)} {b : Fin (finrank K X) → V} {a : Fin (finrank K X) → 𝓞 F}
    (hb : IsJordanIn h X L 𝔭 b a) (σ : Equiv.Perm (Fin (finrank K X))) :
    IsJordanIn h X L 𝔭 (b ∘ σ) (a ∘ σ) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hb
  have hr : Set.range (b ∘ σ) = Set.range b := σ.surjective.range_comp b
  refine ⟨fun i => h1 _, ?_, fun i j hij => h3 _ _ (σ.injective.ne hij), fun i => h4 _,
    fun i => h5 _⟩
  rw [hr]
  exact h2

theorem nondegOn_orth {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h)
    {U : Submodule K V} (hUW : IsCompl U (orthK h U)) : NondegOn h (orthK h U) := by
  intro x hx hxy
  apply hnd
  intro v
  have hv : v ∈ U ⊔ orthK h U := by rw [hUW.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add (f := _), hxy w hw, add_zero]
  have h1 : h u x = 0 := by
    have hx' := hx
    simp only [orthK, Submodule.mem_iInf, LinearMap.mem_ker] at hx'
    exact hx' u hu
  rw [← hs.eq u x, h1, map_zero]

theorem integral_of_fib (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h)
    {U : Submodule K V} (hUc : IsCompl U (orthK h U)) {M T : Submodule (𝓞 K) V} (hM : IsLatIn U M)
    (hT : IsLatIn (orthK h U) T) (hfib : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → fibP h U 𝔭 M T ≠ 0) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h T := by
  intro x hx y hy
  rw [← Formalism.HermitianLattices.Ext.L3.LocF.iInf_locF (K := K) (F := F) (1 : Submodule (𝓞 K) K),
    Submodule.mem_iInf]
  rintro ⟨𝔭, h𝔭⟩
  have hne := hfib 𝔭 h𝔭
  unfold fibP at hne
  obtain ⟨⟨Λ, _, hdual, _, hΛT⟩⟩ := (Nat.card_ne_zero.1 hne).1
  have hsub : ∀ z ∈ T, z ∈ Λ := fun z hz =>
    (Submodule.mem_inf.1 (hΛT.symm ▸ Formalism.HermitianLattices.Ext.L3.LocF.le_locF 𝔭 T hz :
      z ∈ Λ ⊓ (orthK h U).restrictScalars (𝓞 K))).1
  have hyd : y ∈ dualF h 𝔭 Λ := by
    rw [hdual]
    exact hsub y hy
  exact hyd x (hsub x hx)

theorem genus_of_fib (h1 : JordanExists) (h2 : JordanInv) (h6 : GlueLoc) (hI : IsomFixOfExp)
    (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hnd : Nondeg h) {U : Submodule K V} (hUc : IsCompl U (orthK h U)) (hpos : PosDefOn h (orthK h U))
    {M : Submodule (𝓞 K) V} (hM : IsLatIn U M) {Λ₀ : Submodule (𝓞 K) V} (hΛ₀ : Λ₀ ∈ GlueSet h U M)
    {T : Submodule (𝓞 K) V} (hT : IsLatIn (orthK h U) T)
    (hfib : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → fibP h U 𝔭 M T ≠ 0) :
    SameGenusFix (F := F) h U (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K)) T := by
  intro 𝔭 h𝔭
  have hΛ₀full : Submodule.IsFullLattice K Λ₀ :=
    { toIsLattice := hΛ₀.1
      span_eq_top := GlobalTheory.LoopC.Base.span_eq_top_of_unimodular h hs
        (nondegenerate_of hs hnd) hΛ₀.1 hΛ₀.2.1 }
  have hT₀ : IsLatIn (orthK h U) (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K)) :=
    isLatIn_cut hΛ₀full _
  have hrefl : SameGenusFix (F := F) h U (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K))
      (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K)) := fun 𝔮 _ =>
    ⟨1, (isomFix h U).one_mem, by ext z; simp [Formalism.HermitianLatticesTheory.gmap]⟩
  have hfib₀ : ∀ 𝔮 : Ideal (𝓞 F), 𝔮.IsMaximal →
      fibP h U 𝔮 M (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K)) ≠ 0 := fun 𝔮 h𝔮 =>
    fibP_ne_zero_of_genus hF hs hnd hUc hM hΛ₀ hrefl h𝔮
  have hint := integral_of_fib hF hs hnd hUc hM hT hfib
  have hint₀ := integral_of_fib hF hs hnd hUc hM hT₀ hfib₀
  have hnd' := nondegOn_orth hs hnd hUc
  obtain ⟨b, a, hb⟩ := (h1 K F V hK hF h hs).1 (orthK h U) _ hnd' hT₀ hint₀ 𝔭 h𝔭
  obtain ⟨b', a', hb'⟩ := (h1 K F V hK hF h hs).1 (orthK h U) T hnd' hT hint 𝔭 h𝔭
  obtain ⟨e₀⟩ := ((h6 K F V hK hF h hs hnd U hUc M _ hM hT₀ 𝔭 h𝔭).1 (hfib₀ 𝔭 h𝔭)).1
  obtain ⟨e⟩ := ((h6 K F V hK hF h hs hnd U hUc M T hM hT 𝔭 h𝔭).1 (hfib 𝔭 h𝔭)).1
  have hmin := h2 K F V V hK hF h h hs hs (orthK h U) (orthK h U) _ T hT₀ hT 𝔭 h𝔭 b a b' a'
    hb hb' ⟨e₀.symm.trans e⟩
  obtain ⟨σ, hσ⟩ := exists_perm_of_min (fun i => vF 𝔭 (a i)) (fun i => vF 𝔭 (a' i)) hmin
  exact hI K F V hK hF h hs hnd U hUc hpos _ T hT₀ hT 𝔭 h𝔭 b a (b' ∘ σ) (a' ∘ σ) hb
    (isJordanIn_perm hb' σ) (fun i => (hσ i).symm)

end Formalism.L2.SG.Pf.G8
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanInvariantsHolds
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.G2

theorem jordan_invariants_holds : JordanInv := by
  intro K F V V' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _hK hF h h' _hs _hs' X X' L L' hL hL' 𝔭 h𝔭 b a b' a'
    hJ hJ' hiso j
  obtain ⟨f⟩ := hiso
  obtain ⟨g⟩ := disc_equiv hF h𝔭 hL hJ.1 hJ.2.1 hJ.2.2.1 hJ.2.2.2.1 hJ.2.2.2.2
  obtain ⟨g'⟩ := disc_equiv hF h𝔭 hL' hJ'.1 hJ'.2.1 hJ'.2.2.1 hJ'.2.2.2.1 hJ'.2.2.2.2
  have hc := card_quot_smul_top_congr ((g.symm.trans f).trans g') (extP K 𝔭 ^ j)
  rw [card_pi_quot, card_pi_quot] at hc
  exact Nat.pow_right_injective (two_le_absNorm h𝔭) hc

end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanSplittingExists
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

theorem jordan_splitting_exists : JordanExists := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs
  exact ⟨fun X L hnd hL hLi 𝔭 h𝔭 => G1.jordan_exists hK hF hs X L hnd hL hLi 𝔭 h𝔭,
    fun L _ 𝔭 h𝔭 b a hJ => G1.vd_eq_vJof hK hF L 𝔭 h𝔭 b a hJ⟩

end Formalism.L2.SG.Pf.Cnt
end
end

