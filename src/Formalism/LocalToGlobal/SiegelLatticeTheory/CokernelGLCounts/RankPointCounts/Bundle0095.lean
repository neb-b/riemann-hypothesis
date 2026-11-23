module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0092
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolIn

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupMUIndep
section
noncomputable section

open scoped Classical
open Module Matrix
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem witt_tuple {ι : Type} [Fintype ι] (x y : ι → S.V) (hx : LinearIndependent E x) (hy : LinearIndependent E y)
    (hG : ∀ i j, S.hT (x i) (x j) = S.hT (y i) (y j)) :
    ∃ g : S.V ≃ₗ[E] S.V, g ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ ∀ i, g (x i) = y i := by
  set U := Submodule.span E (Set.range x) with hU
  let b : Basis ι E U := Basis.span hx
  have hb : ∀ i, (b i : S.V) = x i := fun i => by
    show ((Basis.span hx i : U) : S.V) = x i
    rw [Basis.span_apply]
  let f : U →ₗ[E] S.V := b.constr E y
  have hfu : ∀ u : U, f u = ∑ i, b.equivFun u i • y i := fun u => b.constr_apply_fintype E y u
  have hu : ∀ u : U, (u : S.V) = ∑ i, b.equivFun u i • x i := by
    intro u
    have := congrArg Subtype.val (b.sum_repr u)
    rw [← this, Submodule.coe_sum]
    simp only [Submodule.coe_smul, hb, Basis.equivFun_apply]
  have hexp : ∀ (z : ι → S.V) (c d : ι → E), S.hT (∑ i, c i • z i) (∑ j, d j • z j) =
      ∑ i, ∑ j, star (c i) * d j * S.hT (z i) (z j) := by
    intro z c d
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
      starRingEnd_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hiso : ∀ u v : U, S.hT (f u) (f v) = S.hT u v := by
    intro u v
    rw [hfu, hfu, hu u, hu v, hexp, hexp]
    simp only [hG]
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro u hu0
    rw [LinearMap.mem_ker, hfu] at hu0
    have hc := Fintype.linearIndependent_iff.1 hy _ hu0
    refine (Submodule.mem_bot E).2 (Subtype.ext ?_)
    rw [hu u]
    simp [hc]
  obtain ⟨g, hg, hgf⟩ := witt_extension_theorem E S.V S.hT (fun x y => (hT_swap x y).symm)
    (fun x hx => S.nondeg.1 x hx) U f hinj hiso
  refine ⟨g, hg, fun i => ?_⟩
  have := hgf (b i)
  rw [hb] at this
  rw [this]
  exact b.constr_basis E y i

def tupMU (F : FlagG S r T) (F1 : FlagG S r T') (M U : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Fin (r + 1) ⊕ Fin (r + 1) → S.V :=
  Sum.elim (fun a => ∑ c, M c a • F.fvec c) (fun b => ∑ c, U c b • F1.fvec c)

theorem gram_moved (F : FlagG S r T) (F1 F2 : FlagG S r T') (M U : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hM : IsUpUni M) (hU : IsUpUni U) (hZ : Zhat F F2 = Mᴴ * Zhat F F1 * U) :
    ∀ i j, S.hT (tupMU F F1 M U i) (tupMU F F1 M U j) =
      S.hT (Sum.elim F.fvec F2.fvec i) (Sum.elim F.fvec F2.fvec j) := by
  have hexp : ∀ (z w : Fin (r + 1) → S.V) (c d : Fin (r + 1) → E), S.hT (∑ i, c i • z i) (∑ j, d j • w j) =
      ∑ i, ∑ j, star (c i) * d j * S.hT (z i) (w j) := by
    intro z w c d
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
      starRingEnd_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hFF : ∀ (G : FlagG S r T) c d, S.hT (G.fvec c) (G.fvec d) =
      if c = Fin.last r ∧ d = Fin.last r then -T else 0 := fun G c d => by
    have := brS_fvec G d c
    simp only [brS] at this
    rw [this]
    by_cases h1 : c = Fin.last r <;> by_cases h2 : d = Fin.last r <;> simp [h1, h2]
  have hFF' : ∀ (G : FlagG S r T') c d, S.hT (G.fvec c) (G.fvec d) =
      if c = Fin.last r ∧ d = Fin.last r then -T' else 0 := fun G c d => by
    have := brS_fvec G d c
    simp only [brS] at this
    rw [this]
    by_cases h1 : c = Fin.last r <;> by_cases h2 : d = Fin.last r <;> simp [h1, h2]
  have hdiag : ∀ (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hA : IsUpUni A) (t : E) (a b : Fin (r + 1)),
      ∑ i, ∑ j, star (A i a) * A j b * (if i = Fin.last r ∧ j = Fin.last r then t else 0) =
        if a = Fin.last r ∧ b = Fin.last r then t else 0 := by
    intro A hA t a b
    simp only [mul_ite, mul_zero, ite_and]
    rw [Finset.sum_eq_single (Fin.last r), Finset.sum_eq_single (Fin.last r)]
    · simp only [if_true, upUni_last hA]
      by_cases h1 : a = Fin.last r <;> by_cases h2 : b = Fin.last r <;> simp [h1, h2]
    · intro j _ hj; simp [hj]
    · simp
    · intro i _ hi; simp [hi]
    · simp
  have hcross : ∀ a b, S.hT (tupMU F F1 M U (Sum.inl a)) (tupMU F F1 M U (Sum.inr b)) = S.hT (F.fvec a) (F2.fvec b) := by
    intro a b
    simp only [tupMU, Sum.elim_inl, Sum.elim_inr]
    rw [hexp]
    have h2 : S.hT (F.fvec a) (F2.fvec b) = Zhat F F2 a b := rfl
    rw [h2, hZ, Matrix.mul_apply]
    simp only [Matrix.mul_apply, conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    simp only [Zhat, brS]
    ring
  intro i j
  rcases i with a | a <;> rcases j with b | b
  · simp only [tupMU, Sum.elim_inl]
    rw [hexp]
    simp only [hFF]
    exact hdiag M hM (-T) a b
  · exact hcross a b
  · rw [hT_swap, hcross b a, ← hT_swap]
    rfl
  · simp only [tupMU, Sum.elim_inr]
    rw [hexp]
    simp only [hFF']
    exact hdiag U hU (-T') a b

theorem tupMU_indep (F : FlagG S r T) (F1 : FlagG S r T') (M U : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hM : IsUpUni M) (hU : IsUpUni U) (hG : Gflag F F1 ≠ 0) : LinearIndependent E (tupMU F F1 M U) := by
  have hli := PI.PairCorankPos.W.linIndep F F1 hG
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro g hg
  have hsum : ∑ i, g i • tupMU F F1 M U i =
      ∑ s, (Sum.elim (M *ᵥ fun a => g (Sum.inl a)) (U *ᵥ fun b => g (Sum.inr b)) s) •
        Sum.elim F.fvec F1.fvec s := by
    simp only [Fintype.sum_sum_type, tupMU, Sum.elim_inl, Sum.elim_inr, Finset.smul_sum, smul_smul, mulVec,
      dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm, Finset.sum_comm (f := fun x y => (U x y * g (Sum.inr y)) • F1.fvec x)]
    congr 1 <;> refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_ <;> rw [mul_comm]
  rw [hsum] at hg
  have h0 := hli _ hg
  have hMd : M.det ≠ 0 := by rw [upUni_det hM]; exact one_ne_zero
  have hUd : U.det ≠ 0 := by rw [upUni_det hU]; exact one_ne_zero
  have hl : (fun a => g (Sum.inl a)) = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero hMd (funext fun a => h0 (Sum.inl a))
  have hr : (fun b => g (Sum.inr b)) = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero hUd (funext fun b => h0 (Sum.inr b))
  intro s
  rcases s with a | b
  · exact congrFun hl a
  · exact congrFun hr b

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolLat
section
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolLat

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem mem_of_mul (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (hI : I ≠ 0) (m n : ℤ) (y : D.host.E)
    (h : ∀ x ∈ I ^ n, x * y ∈ I ^ m) : y ∈ I ^ (m - n) := by
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) y * I ^ n ≤ I ^ m := by
    refine FractionalIdeal.mul_le.2 fun a ha b hb => ?_
    obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 ha
    rw [smul_mul_assoc, mul_comm]
    exact (FractionalIdeal.mem_coe).1 (Submodule.smul_mem _ c ((FractionalIdeal.mem_coe).2 (h b hb)))
  have h2 : I ^ (-n) * (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) y * I ^ n) ≤ I ^ (-n) * I ^ m :=
    mul_right_mono hle
  rw [mul_comm (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) y), ← mul_assoc, ← zpow_add₀ hI,
    neg_add_cancel, zpow_zero, one_mul, ← zpow_add₀ hI, neg_add_eq_sub] at h2
  exact h2 (FractionalIdeal.mem_spanSingleton_self _ y)

theorem coef_XS {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) {v : (VS D).V} (hv : v ∈ XS D F0)
    (y : Fin D.R.rS → D.host.E) (hy : v = ∑ a, y a • F0.e a) (a : Fin D.R.rS) :
    y a ∈ (ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have key : ∃ y' : Fin D.R.rS → D.host.E, (∀ a : Fin D.R.rS, y' a ∈ (ddS D ^ (-((D.R.rS : ℤ) - ((a : Fin D.R.rS) : ℕ))) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ∧ v = ∑ a, y' a • F0.e a := by
    clear hy
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, x, hx, rfl⟩ := hx
      refine ⟨Pi.single a x, fun b => ?_, ?_⟩
      · by_cases h : b = a
        · subst h
          simpa using hx
        · rw [Pi.single_eq_of_ne h]
          exact FractionalIdeal.zero_mem _
      · rw [Finset.sum_eq_single a (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul]) (by simp),
          Pi.single_eq_same]
    | zero => exact ⟨0, fun _ => FractionalIdeal.zero_mem _, by simp⟩
    | add x w _ _ hx hw =>
      obtain ⟨y1, h1, rfl⟩ := hx
      obtain ⟨y2, h2, rfl⟩ := hw
      exact ⟨y1 + y2, fun a => (FractionalIdeal.mem_coe).1 (Submodule.add_mem _ ((FractionalIdeal.mem_coe).2 (h1 a))
        ((FractionalIdeal.mem_coe).2 (h2 a))), by simp [add_smul, Finset.sum_add_distrib]⟩
    | smul c x _ hx =>
      obtain ⟨y1, h1, rfl⟩ := hx
      refine ⟨fun a => (c : D.host.E) * y1 a, fun a => ?_, ?_⟩
      · have := (FractionalIdeal.mem_coe).1 (Submodule.smul_mem _ c ((FractionalIdeal.mem_coe).2 (h1 a)))
        rwa [Algebra.smul_def] at this
      · rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← smul_assoc, Algebra.smul_def]
  obtain ⟨y', hy', hv'⟩ := key
  have hyy : y = y' := by
    have h := F0.e_indep
    rw [Fintype.linearIndependent_iff] at h
    funext b
    have := h (y - y') (by simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, ← hy, ← hv', sub_self]) b
    exact sub_eq_zero.1 this
  rw [hyy]
  exact hy' a

end Formalism.L2.SG.Pf.ZsVolLat

end
end

