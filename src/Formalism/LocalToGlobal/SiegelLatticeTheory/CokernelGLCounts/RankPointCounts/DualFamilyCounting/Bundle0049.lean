module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0047
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0044
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TermTiesEmptyOfLargeIndex
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0042

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemClRow
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem mem_cl_row (b : Fin D.R.rS) (x : InfinitePlace X.B.I.F → Fin (D.R.k + 1) → ℂ) :
    x ∈ cLat X u (Sum.inl (Sum.inr b)) ↔ ∃ y ∈ aaLb X b, rowV X u y = x := by
  let f : (VS D).V →+ (InfinitePlace X.B.I.F → Fin (D.R.k + 1) → ℂ) :=
    AddMonoidHom.mk' (rowV X u) (fun x y => rowV_add (X := X) (u := u) x y)
  let S : AddSubgroup (VS D).V := (Submodule.span (𝓞 D.host.E)
    {y | ∃ c ∈ (aaD D b : Set D.host.E), ∃ l ∈ X.Lb, y = c • l}).toAddSubgroup
  have hc : cLat X u (Sum.inl (Sum.inr b)) = S.map f := AddSubgroup.closure_eq (S.map f)
  have key : x ∈ cLat X u (Sum.inl (Sum.inr b)) ↔ x ∈ S.map f := by
    rw [hc]; exact Iff.rfl
  exact key.trans AddSubgroup.mem_map

def imSub (a : Fin D.R.rS) : AddSubgroup D.host.E where
  carrier := {t | t ∈ ((aaD D a * aaD D a : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E) ∧
    D.host.conj t = -t}
  add_mem' := fun {s t} hs ht => ⟨Submodule.add_mem _ hs.1 ht.1, by rw [map_add (f := _), hs.2, ht.2, neg_add]⟩
  zero_mem' := ⟨Submodule.zero_mem _, by rw [map_zero, neg_zero]⟩
  neg_mem' := fun {t} ht => ⟨Submodule.neg_mem _ ht.1, by rw [map_neg, ht.2]⟩

def imHom : D.host.E →+ (InfinitePlace X.B.I.F → ℝ) where
  toFun t := fun v => (embS D (X.pl v) t).im
  map_zero' := by funext v; simp
  map_add' s t := by funext v; simp

theorem mem_cl_im (a : Fin D.R.rS) (x : InfinitePlace X.B.I.F → ℝ) :
    x ∈ cLat X u (Sum.inr (Sum.inr a)) ↔
      ∃ t : D.host.E, t ∈ aaD D a * aaD D a ∧ D.host.conj t = -t ∧ (fun v => (embS D (X.pl v) t).im) = x := by
  have hc : cLat X u (Sum.inr (Sum.inr a)) = (imSub a).map (imHom X) :=
    AddSubgroup.closure_eq ((imSub a).map (imHom X))
  have key : x ∈ cLat X u (Sum.inr (Sum.inr a)) ↔ x ∈ (imSub a).map (imHom X) := by
    rw [hc]; exact Iff.rfl
  refine key.trans (AddSubgroup.mem_map.trans ?_)
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
    exact ⟨t, h1, h2, rfl⟩
  · rintro ⟨t, h1, h2, rfl⟩
    exact ⟨t, ⟨h1, h2⟩, rfl⟩

theorem im_inj {t t' : D.host.E} (ht : D.host.conj t = -t) (ht' : D.host.conj t' = -t')
    (h : ∀ v : InfinitePlace X.B.I.F, (embS D (X.pl v) t).im = (embS D (X.pl v) t').im) : t = t' := by
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace X.B.I.F))
  have hs : D.host.conj (t - t') = -(t - t') := by rw [map_sub, ht, ht']; ring
  have h1 := CovB.embS_conj (D := D) (X.pl v) (t - t')
  rw [hs, map_neg] at h1
  have him : (embS D (X.pl v) (t - t')).im = 0 := by rw [map_sub, Complex.sub_im, h v, sub_self]
  have hre : (embS D (X.pl v) (t - t')).re = 0 := by
    have h2 := congrArg Complex.re h1
    simp only [Complex.neg_re, Complex.conj_re] at h2
    linarith
  have h0 : embS D (X.pl v) (t - t') = 0 := Complex.ext hre him
  exact sub_eq_zero.mp ((map_eq_zero_iff _ (RingHom.injective _)).mp h0)

theorem aaLb_inW {b : Fin D.R.rS} {y : (VS D).V} (hy : y ∈ aaLb X b) : InW X y := by
  have hL : ∀ l ∈ X.Lb, InW X l := by
    intro l hl
    have hp := Alg.pW_inW (X := X) l
    have he : pW X l = l := by
      have h1 := Level.prV_Lb (X := X) l hl
      rw [Level.prV_apply] at h1
      simpa only [pW] using h1
    rwa [he] at hp
  simp only [aaLb, SetLike.mem_coe] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, -, l, hl, rfl⟩ := hx
    intro d
    exact ⟨by rw [map_smul, ((hL l hl) d).1, smul_zero], by rw [map_smul, ((hL l hl) d).2, smul_zero]⟩
  | zero => intro d; exact ⟨map_zero _, map_zero _⟩
  | add x z _ _ hx hz =>
    intro d
    exact ⟨by rw [map_add (f := _), (hx d).1, (hz d).1, add_zero], by rw [map_add (f := _), (hx d).2, (hz d).2, add_zero]⟩
  | smul o x _ hx =>
    intro d
    refine ⟨?_, ?_⟩
    · rw [← algebraMap_smul D.host.E o x, map_smul, (hx d).1, smul_zero]
    · rw [← algebraMap_smul D.host.E o x, map_smul, (hx d).2, smul_zero]

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibOnto
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Onto

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem hc_congr (x y : BV X) (hX : ∀ p, x (Sum.inl (Sum.inl p)) = y (Sum.inl (Sum.inl p)))
    (hR : ∀ b, x (Sum.inl (Sum.inr b)) = y (Sum.inl (Sum.inr b))) : Hc X u x = Hc X u y := by
  funext v
  have h1 : Xc X x v = Xc X y v := by
    ext b a
    simp only [Xc, hX]
  have h2 : Gc X u x v = Gc X u y v := by
    ext b c
    simp only [Gc, hR]
  simp only [Hc, h1, h2]

theorem aaLb_inW {b : Fin D.R.rS} {y : (VS D).V} (hy : y ∈ aaLb X b) : InW X y := by
  rw [aaLb, SetLike.mem_coe] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, -, l, hl, rfl⟩ := hz
    intro a
    obtain ⟨h1, h2⟩ := X.Lb_perp l hl a
    simp only [map_smul, h1, h2, smul_zero, and_self]
  | zero =>
    intro a
    simp only [map_zero, and_self]
  | add z w _ _ hz hw =>
    intro a
    simp only [map_add (f := _), (hz a).1, (hz a).2, (hw a).1, (hw a).2, add_zero, and_self]
  | smul r z _ hz =>
    intro a
    simp only [LinearMap.map_smul_of_tower, (hz a).1, (hz a).2, smul_zero, and_self]

theorem mem_cl_row (b : Fin D.R.rS) (z : InfinitePlace X.B.I.F → Fin (D.R.k + 1) → ℂ) :
    z ∈ AddSubgroup.closure (rowV X u '' aaLb X b) ↔ ∃ y ∈ aaLb X b, rowV X u y = z := by
  exact mem_closure_image (rowHom X u)
    (Submodule.span (𝓞 D.host.E) {y | ∃ c ∈ (aaD D b : Set D.host.E), ∃ l ∈ X.Lb, y = c • l}).toAddSubgroup z

def imH (a : Fin D.R.rS) : AddSubgroup D.host.E where
  carrier := {t | t ∈ ((aaD D a * aaD D a : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
      Set D.host.E) ∧ D.host.conj t = -t}
  zero_mem' := ⟨Submodule.zero_mem _, by simp⟩
  add_mem' := by
    rintro s t ⟨hs1, hs2⟩ ⟨ht1, ht2⟩
    exact ⟨Submodule.add_mem _ hs1 ht1, by rw [map_add (f := _), hs2, ht2, neg_add]⟩
  neg_mem' := by
    rintro s ⟨hs1, hs2⟩
    exact ⟨Submodule.neg_mem _ hs1, by rw [map_neg, hs2]⟩

def imHom : D.host.E →+ (InfinitePlace X.B.I.F → ℝ) where
  toFun t := fun v => (embS D (X.pl v) t).im
  map_zero' := by funext v; simp
  map_add' s t := by funext v; simp

theorem mem_cl_im (a : Fin D.R.rS) (z : InfinitePlace X.B.I.F → ℝ) :
    z ∈ cLat X u (Sum.inr (Sum.inr a)) ↔ ∃ t ∈ imH a, imHom X t = z := by
  exact mem_closure_image (imHom X) (imH a) z

end Onto


open Onto in
theorem fibOnto_holds : FibOnto := by
  intro D X u x hx
  have hA : ∀ p : LsNc5.LtPair D.R.rS, ∃ t ∈ aaD D p.1.1 * (aaD D p.1.2)⁻¹,
      embV X t = x (Sum.inl (Sum.inl p)) := by
    intro p
    have h := hx (Sum.inl (Sum.inl p))
    simp only [tauQ, sub_zero] at h
    exact (mem_cl_emb X _ _).1 h
  have hB : ∀ b : Fin D.R.rS, ∃ y ∈ aaLb X b, rowV X u y = x (Sum.inl (Sum.inr b)) := by
    intro b
    have h := hx (Sum.inl (Sum.inr b))
    simp only [tauQ, sub_zero] at h
    exact (mem_cl_row X u b _).1 h
  have hC : ∀ p : LsNc5.LtPair D.R.rS, ∃ s ∈ aaD D p.1.1 * aaD D p.1.2,
      embV X s = fun v => x (Sum.inr (Sum.inl p)) v - Hc X u x v p.1.1 p.1.2 / 2 :=
    fun p => (mem_cl_emb X _ _).1 (hx (Sum.inr (Sum.inl p)))
  have hD : ∀ a : Fin D.R.rS, ∃ t ∈ imH a, imHom X t =
      fun v => x (Sum.inr (Sum.inr a)) v - -((Hc X u x v a a).re * (embS D (X.pl v) (theta D)).im) :=
    fun a => (mem_cl_im X u a _).1 (hx (Sum.inr (Sum.inr a)))
  choose tA htA htA' using hA
  choose xs hxs hxs' using hB
  choose sC hsC hsC' using hC
  choose tD htD htD' using hD
  obtain ⟨X0, hX0⟩ : ∃ X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E,
      X0 = fun b a => if h : b < a then tA ⟨(b, a), h⟩ else if b = a then 1 else 0 := ⟨_, rfl⟩
  have hup : ∀ b a : Fin D.R.rS, a < b → X0 b a = 0 := by
    intro b a h
    simp [hX0, not_lt_of_gt h, ne_of_gt h]
  have hdg : ∀ a, X0 a a = 1 := by
    intro a
    simp [hX0]
  have hX0p : ∀ p : LsNc5.LtPair D.R.rS, X0 p.1.1 p.1.2 = tA p := by
    intro p
    simp [hX0, p.2]
  have hW : ∀ b, InW X (xs b) := fun b => aaLb_inW X (hxs b)
  have hGh : ∀ i j, star (Gp D X0 xs j i) = Gp D X0 xs i j := by
    intro i j
    have := congrFun (congrFun (Gp_herm X0 xs) i) j
    rwa [Matrix.conjTranspose_apply] at this
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E,
      M = fun b a => if h : b < a then sC ⟨(b, a), h⟩
        else if h' : a < b then -Gp D X0 xs b a - star (sC ⟨(a, b), h'⟩)
        else tD a - Gp D X0 xs a a * theta D := ⟨_, rfl⟩
  have hMlt : ∀ p : LsNc5.LtPair D.R.rS, M p.1.1 p.1.2 = sC p := by
    intro p
    simp [hM, p.2]
  have hMgt : ∀ p : LsNc5.LtPair D.R.rS,
      M p.1.2 p.1.1 = -Gp D X0 xs p.1.2 p.1.1 - star (sC p) := by
    intro p
    simp [hM, p.2, not_lt_of_gt p.2]
  have hMd : ∀ a, M a a = tD a - Gp D X0 xs a a * theta D := by
    intro a
    simp [hM]
  have hth : star (theta D) = 1 - theta D := by
    rw [Inh.tie_star]
    exact eq_sub_of_add_eq' (theta_spec D).2
  have hData : DataOK X X0 xs M := by
    refine ⟨hup, hdg, hW, ?_⟩
    ext i j
    simp only [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.neg_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [hMlt ⟨(i, j), h⟩, hMgt ⟨(i, j), h⟩, star_sub, star_neg, star_star, hGh]
      ring
    · obtain ⟨-, hc⟩ := htD i
      rw [hMd, star_sub, star_mul', Inh.tie_star D (tD i), hc, hth, hGh]
      ring
    · rw [hMlt ⟨(j, i), h⟩, hMgt ⟨(j, i), h⟩]
      ring
  have hXb : ∀ p, x (Sum.inl (Sum.inl p)) = blkQ X u X0 xs M (Sum.inl (Sum.inl p)) := by
    intro p
    show _ = embV X (X0 p.1.1 p.1.2)
    rw [hX0p]
    exact (htA' p).symm
  have hRb : ∀ b, x (Sum.inl (Sum.inr b)) = blkQ X u X0 xs M (Sum.inl (Sum.inr b)) := by
    intro b
    exact (hxs' b).symm
  have hHc : ∀ v, Hc X u x v = (Gp D X0 xs).map (embS D (X.pl v)) := by
    intro v
    rw [hc_congr X u x _ hXb hRb]
    exact Hc_blkQ X u X0 xs M hup hdg hW v
  refine ⟨X0, xs, M, hData, ?_⟩
  funext p
  rcases p with ((p | b) | (p | a))
  · exact (hXb p).symm
  · exact (hRb b).symm
  · funext v
    show (embS D (X.pl v) (M p.1.1 p.1.2) - star (embS D (X.pl v) (M p.1.2 p.1.1))) / 2 = _
    have hs := congrFun (hsC' p) v
    simp only [embV, hHc v, Matrix.map_apply] at hs
    have e1 : star (embS D (X.pl v) (M p.1.2 p.1.1)) =
        -embS D (X.pl v) (Gp D X0 xs p.1.1 p.1.2) - embS D (X.pl v) (sC p) := by
      rw [hMgt, ← emb_star X, star_sub, star_neg, star_star, hGh, map_sub, map_neg]
    rw [e1, hMlt]
    linear_combination hs
  · funext v
    show (embS D (X.pl v) (M a a)).im = _
    have hs := congrFun (htD' a) v
    simp only [imHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hHc v, Matrix.map_apply] at hs
    have hr : (embS D (X.pl v) (Gp D X0 xs a a)).im = 0 := by
      have := congrArg (embS D (X.pl v)) (hGh a a)
      rw [emb_star X] at this
      exact Complex.conj_eq_iff_im.mp this
    rw [hMd, map_sub, map_mul, Complex.sub_im, Complex.mul_im, hr]
    linear_combination hs

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.StarEqConj
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem star_eq_conj' (t : D.host.E) : star t = D.host.conj t := by
  apply D.host.φ₀.injective
  rw [Formalism.BasicNotions.Examples₂.emb_star, Formalism.BasicNotions.Examples₂.emb_conj]

theorem theta_spec : IsIntegral ℤ (theta D) ∧ theta D + D.host.conj (theta D) = 1 := by
  have h := thetaEx_holds D
  unfold theta
  rw [dite_eq_left h]
  exact h.choose_spec

theorem entry_rel {X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E} {xs : Fin D.R.rS → (VS D).V}
    {M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E} (hok : DataOK X X0 xs M) (b a : Fin D.R.rS) :
    M b a + star (M a b) = -Gp D X0 xs b a := by
  have hok' := hok
  obtain ⟨-, -, -, hM⟩ := hok'
  have h := congrFun (congrFun hM b) a
  simpa only [Matrix.add_apply, Matrix.neg_apply, Matrix.conjTranspose_apply] using h

theorem kblk {X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E} {xs : Fin D.R.rS → (VS D).V}
    {M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E} (hok : DataOK X X0 xs M) (p : Formalism.L2.SG.Pf.LsNc5.LtPair D.R.rS) :
    blkQ X u X0 xs M (Sum.inr (Sum.inl p)) - tauQ X u (Sum.inr (Sum.inl p)) (blkQ X u X0 xs M) =
      embV X (M p.1.1 p.1.2) := by
  have hok' := hok
  obtain ⟨hup, hd, hW, -⟩ := hok'
  show (fun v => (embS D (X.pl v) (M p.1.1 p.1.2) - star (embS D (X.pl v) (M p.1.2 p.1.1))) / 2) -
      (fun v => Hc X u (blkQ X u X0 xs M) v p.1.1 p.1.2 / 2) =
      fun v => embS D (X.pl v) (M p.1.1 p.1.2)
  funext v
  simp only [Pi.sub_apply]
  rw [Hc_blkQ X u X0 xs M hup hd hW v, Matrix.map_apply]
  have e := congrArg (embS D (X.pl v)) (entry_rel X hok p.1.1 p.1.2)
  rw [map_add (f := _), map_neg, Formalism.BasicNotions.Examples₂.emb_star, starRingEnd_apply] at e
  rw [show embS D (X.pl v) (Gp D X0 xs p.1.1 p.1.2) =
      -(embS D (X.pl v) (M p.1.1 p.1.2) + star (embS D (X.pl v) (M p.1.2 p.1.1))) by
    rw [e, neg_neg]]
  ring

def xiA (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (a : Fin D.R.rS) : D.host.E :=
  M a a + Gp D X0 xs a a * theta D

theorem Gp_diag_star (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V) (a : Fin D.R.rS) :
    star (Gp D X0 xs a a) = Gp D X0 xs a a := by
  have h := congrFun (congrFun (Gp_herm X0 xs) a) a
  simpa only [Matrix.conjTranspose_apply] using h

theorem xiA_conj {X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E} {xs : Fin D.R.rS → (VS D).V}
    {M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E} (hok : DataOK X X0 xs M) (a : Fin D.R.rS) :
    D.host.conj (xiA X0 xs M a) = -xiA X0 xs M a := by
  have hs : ∀ t : D.host.E, D.host.conj t = star t := fun t => (star_eq_conj' t).symm
  have hθ : D.host.conj (theta D) = 1 - theta D := eq_sub_of_add_eq' (theta_spec (D := D)).2
  have hM : star (M a a) = -Gp D X0 xs a a - M a a := eq_sub_of_add_eq' (entry_rel X hok a a)
  unfold xiA
  rw [map_add (f := _), map_mul, hθ, hs (M a a), hs (Gp D X0 xs a a), Gp_diag_star X0 xs a, hM]
  ring

theorem imblk {X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E} {xs : Fin D.R.rS → (VS D).V}
    {M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E} (hok : DataOK X X0 xs M) (a : Fin D.R.rS) :
    blkQ X u X0 xs M (Sum.inr (Sum.inr a)) - tauQ X u (Sum.inr (Sum.inr a)) (blkQ X u X0 xs M) =
      fun v => (embS D (X.pl v) (xiA X0 xs M a)).im := by
  have hok' := hok
  obtain ⟨hup, hd, hW, -⟩ := hok'
  show (fun v => (embS D (X.pl v) (M a a)).im) -
      (fun v => -((Hc X u (blkQ X u X0 xs M) v a a).re * (embS D (X.pl v) (theta D)).im)) =
      fun v => (embS D (X.pl v) (xiA X0 xs M a)).im
  funext v
  simp only [Pi.sub_apply]
  rw [Hc_blkQ X u X0 xs M hup hd hW v, Matrix.map_apply]
  have hreal : (embS D (X.pl v) (Gp D X0 xs a a)).im = 0 := by
    have h1 := congrArg (embS D (X.pl v)) (Gp_diag_star X0 xs a)
    rw [Formalism.BasicNotions.Examples₂.emb_star] at h1
    exact Complex.conj_eq_iff_im.mp h1
  simp only [xiA, map_add (f := _), map_mul, Complex.add_im, Complex.mul_im, hreal]
  ring

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

