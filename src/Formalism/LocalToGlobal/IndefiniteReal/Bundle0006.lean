module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.NonGenericAndKTwoTheorems
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.LocalToGlobal.GlobalTheory.DivPassageP
public import Formalism.LocalToGlobal.IndefiniteForms.PairingConditionOfInverseMatrixIdentity

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.CutPassage
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace CxData

theorem rinv_spec {d n : ℕ} (P : Matrix (Fin d) (Fin n) K) (h : Function.Surjective P.mulVec) :
    P * rinv P = 1 := by
  have hex : ∃ R : Matrix (Fin n) (Fin d) K, P * R = 1 := by
    choose f hf using h
    refine ⟨Matrix.of fun i k => f (Pi.single k 1) i, ?_⟩
    ext i k
    have h1 := congrFun (hf (Pi.single k 1)) i
    rw [Pi.single_apply] at h1
    rw [Matrix.one_apply, ← h1]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]
  unfold rinv
  rw [dite_eq_left hex]
  exact hex.choose_spec

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc)

theorem cutPairing : X.CutPairing cr := by
  intro ζ sEE hW h2 hBt hMI hZ
  refine ⟨?_, fun u => by simp [colDef, colOf, hZ.1 u], fun u t => inv_ne_zero (hZ.2.1 u t),
    fun u w => ?_⟩
  swap
  · show vw w (ζ u (X.μ w))⁻¹ = 0
    rw [ValuationRepresentative.vw_inv, hZ.2.2 u w, neg_zero]
  intro u t φ F
  by_cases ht : t = Bs.μ0
  · subst ht
    show (fc X.zs).Dc.Pt u Bs.μ0 φ F =
      (ζ u Bs.μ0)⁻¹ * X.Bdef u φ ((X.rowMat cr true Bs.μ0).mulVec (((lv (fc X.zs) true).Pq Bs.μ0).mulVec F))
    rw [rowMat_base X cr true h2, Matrix.one_mulVec, hZ.1 u, inv_one, one_mul]
    show (fc X.zs).Dc.Pt u Bs.μ0 φ F = (fc X.zs).Dc.Pt u Bs.μ0 φ
      ((rinv ((fc X.zs).Df1.Pq Bs.μ0)).mulVec (((fc X.zs).Df1.Pq Bs.μ0).mulVec F))
    have hR := rinv_spec _ (hW.Pq_surj Bs.μ0)
    have hk : F - (rinv ((fc X.zs).Df1.Pq Bs.μ0)).mulVec (((fc X.zs).Df1.Pq Bs.μ0).mulVec F) ∈
        (fc X.zs).Df1.U Bs.μ0 := by
      rw [DefSide.U, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hR,
        Matrix.one_mulVec, sub_self]
    have h0 := hBt u φ _ hk
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  · show (fc X.zs).Dc.Pt u t φ F = (ζ u t)⁻¹ * X.Bdef u φ ((X.rowMat cr true t).mulVec (((fc X.zs).Df1.Pq t).mulVec F))
    rw [← hMI u t ht φ F, ← mul_assoc, inv_mul_cancel₀ (hZ.2.1 u t), one_mul]

theorem cutTuples2 (C CH : ℝ) : X.CutTuples2 cr C CH := by
  intro hH0 hW1
  apply Formalism.IndefR.NonGenericAndKTwoTheorems.hecke_tuple_condition K Bs _ (X.data cr false) _
  · rintro w ⟨j, hj⟩
    show X.μ w ≠ Bs.μ0
    rw [← hH0.2 w]
    apply hW1
    rcases hj with h | h
    · by_contra hc
      apply h
      simp only [CxData.W1, not_exists, not_or, not_not] at hc
      obtain ⟨h1, h2, h3, -, -, -⟩ := hc j
      simp [Formalism.IndefR.HeckeTupleConditions.Atup, h1, h2, h3]
    · exact ⟨j, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
  · exact hH0.2

end CxData

end Formalism.IndefR.Cx
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.CxCoreRG
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

structure RowHyp : Prop where

  wf : (lv (fc X.zs) b).WF

  h4pos : X.H4pos

  h2 : X.H2 cr b

  ratMu : X.RATmu cr b

  h3 : X.H3 cr b

  h4 : X.H4 cr b

  partsOrth : X.PartsOrth b (fc := fc)

structure LiftHyp : Prop where

  h5 : X.H5 cr b

  ratTh : X.RATth cr b

  kForm : X.KForm b

  ewNorm : X.EWnorm b

  thmA : X.ThmA cr b

  galD : X.GalD cr b

  h3W : X.H3W cr b

  mLat : X.MLat b

theorem XE_specR (hR : RowHyp X cr b) :
    (∀ v, IsUnit (X.XE cr b v).det) ∧ X.XE cr b Bs.v0 = frameOf (X.gramE cr b) :=
  let h := rowXE_spec (Df := lv (fc X.zs) b) hR.wf _ (X.gramE_unit cr b (hR.h2) (hR.h4pos.2.2 b)) X.κ hR.h4pos.1
    (fun j p v => X.lam j Bs.μ0 p v) (fun j p v => hR.h4pos.2.1 j Bs.μ0 p v)
  ⟨h.1, h.2.1⟩

theorem scal_rowsR (hR : RowHyp X cr b) (t : Bs.Tup) (v : InfinitePlace K)
    (htv : t = Bs.μ0 ∨ v = Bs.v0) (p : Bs.Ix) :
    IsScalarOn ((lv (fc X.zs) b).XQ t) (X.data cr b).XE v ((X.data cr b).ι t) ((X.data cr b).Qpart t p)
      ((X.data cr b).κ v * ∏ j, (X.data cr b).lam j t p v) := by
  intro x hx y
  have hx' : X.iC cr b t (cpt Bs.v0.embedding x) ∈ X.EEp p := by
    have h : (X.rowMat cr b t).mulVec x ∈ X.Ep cr b p := hx
    rwa [mem_Ep, key_row X cr b (hR.h2) (hR.ratMu)] at h
  by_cases hv : v = Bs.v0
  · subst hv
    change Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin ((lv (fc X.zs) b).dQ Bs.μ0))) (X.XE cr b) Bs.v0 ((X.rowMat cr b t).mulVec x) ((X.rowMat cr b t).mulVec y) = _
    rw [majAt_gram_smul (X.XE cr b) Bs.v0 (fun i => X.iC cr b Bs.μ0 (Pi.single i 1))
      (li_of_lin_injective (by rw [lin_basis]; exact (hR.h2).1)) _ (inv_pos.mpr (hR.h4pos.2.2 b))
      (X.XE_specR cr b hR).2, lin_basis,
      key_row X cr b (hR.h2) (hR.ratMu), key_row X cr b (hR.h2) (hR.ratMu), (hR.h4) t p x hx' y]
    have hn : (X.nP b : ℂ) ≠ 0 := by exact_mod_cast (hR.h4pos.2.2 b).ne'
    push_cast
    field_simp
    dsimp only [CxData.data]
    ring
  · rcases htv with rfl | h
    · change Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin ((lv (fc X.zs) b).dQ Bs.μ0))) (X.XE cr b) v ((X.rowMat cr b Bs.μ0).mulVec x) ((X.rowMat cr b Bs.μ0).mulVec y) = _
      rw [X.rowMat_base cr b (hR.h2), Matrix.one_mulVec, Matrix.one_mulVec]
      have hxQ : x ∈ (lv (fc X.zs) b).Qp Bs.μ0 p := ((hR.h3) p x).2 hx'
      exact rowXE_part (lv (fc X.zs) b) hR.wf _ (X.gramE_unit cr b (hR.h2) (hR.h4pos.2.2 b)) X.κ hR.h4pos.1
        (fun j p v => X.lam j Bs.μ0 p v) (fun j p v => hR.h4pos.2.1 j Bs.μ0 p v) v hv
        (fun p q hpq x hx y hy => (hR.partsOrth) v hv p q hpq x hx y hy) p x hxQ y
    · exact absurd h hv

theorem scal_liftsR (hR : RowHyp X cr b) (hF : LiftHyp X cr b) (j : Bs.J) (t : Bs.Tup) (v : InfinitePlace K)
    (htv : t = Bs.μ0 ∨ v = Bs.v0) (p : Bs.Ix) :
    IsScalarOn ((lv (fc X.zs) b).XT j t) ((X.data cr b).XW j) v ((X.data cr b).θ j t) ((X.data cr b).Zpart j t p)
      ((X.data cr b).lam j t p v) := by
  intro x hx y
  have hx' : X.tC cr b j t (cpt Bs.v0.embedding x) ∈ X.Wp j p := by
    have h : (X.liftMat cr b j t).mulVec x ∈ X.WpK b j p := hx
    rwa [mem_WpK, key_lift X cr b (hF.h5) (hF.ratTh)] at h
  change Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (X.dW b j))) (X.XW b j) v ((X.liftMat cr b j t).mulVec x) ((X.liftMat cr b j t).mulVec y) = _
  rw [majAt_gram (X.XW b j) v (X.bW b j v) ((hF.kForm) j v).1 rfl]
  by_cases hv : v = Bs.v0
  · subst hv
    have hn : ((X.nP b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hR.h4pos.2.2 b).ne'
    have he := (hF.ewNorm) j (X.wC b j Bs.v0 (cpt Bs.v0.embedding ((X.liftMat cr b j t).mulVec x)))
      (X.wC b j Bs.v0 (cpt Bs.v0.embedding ((X.liftMat cr b j t).mulVec y)))
    change ⟪X.w0C b j (cpt Bs.v0.embedding ((X.liftMat cr b j t).mulVec x)),
      X.w0C b j (cpt Bs.v0.embedding ((X.liftMat cr b j t).mulVec y))⟫_ℂ = _ at he
    rw [key_lift X cr b (hF.h5) (hF.ratTh), key_lift X cr b (hF.h5) (hF.ratTh),
      (hF.thmA) j t p x hx' y] at he
    change ⟪X.wC b j Bs.v0 (cpt Bs.v0.embedding ((X.liftMat cr b j t).mulVec x)),
      X.wC b j Bs.v0 (cpt Bs.v0.embedding ((X.liftMat cr b j t).mulVec y))⟫_ℂ = _
    apply mul_left_cancel₀ hn
    rw [← he]
    dsimp only [CxData.data]
    push_cast
    ring
  · rcases htv with rfl | h
    · exact (hF.galD) j v hv p x hx' y
    · exact absurd h hv

def rowsOfR (hR : RowHyp X cr b) (hF : LiftHyp X cr b) (hpos : (lv (fc X.zs) b).Pos) (hprov : (lv (fc X.zs) b).Proviso)
    (htypes : (lv (fc X.zs) b).Types) (hh0 : X.H0) (hl1d : (X.data cr b).DimensionsOfPartsAgree) : IndefRows (lv (fc X.zs) b) where
  toIndefData := X.data cr b
  pos := hpos
  proviso := hprov
  types := htypes
  h0 := hh0
  frames := ⟨(X.XE_specR cr b hR).1, fun j v => frame_gram_unit _ ((hF.kForm) j v).1, hF.mLat⟩
  l1a := by
    refine ⟨fun p => ?_, fun j p => ?_⟩
    · change ((lv (fc X.zs) b).Qp Bs.μ0 p).map (X.rowMat cr b Bs.μ0).mulVecLin = X.Ep cr b p
      rw [X.rowMat_base cr b (hR.h2), Matrix.mulVecLin_one, Submodule.map_id]
      ext x
      rw [mem_Ep]
      exact (hR.h3) p x
    · change ((lv (fc X.zs) b).Zp j Bs.μ0 p).map (X.liftMat cr b j Bs.μ0).mulVecLin = X.WpK b j p
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [Matrix.mulVecLin_apply, mem_WpK, key_lift X cr b (hF.h5) (hF.ratTh)]
        exact ((hF.h3W) j p x).1 hx
      · intro hy
        obtain ⟨x, rfl⟩ := (X.liftMat_bij cr b (hF.kForm) (hF.ewNorm) (hR.h4pos.2.2 b) (hF.h5) (hF.ratTh) j Bs.μ0).2 y
        refine ⟨x, ?_, rfl⟩
        rw [mem_WpK, key_lift X cr b (hF.h5) (hF.ratTh)] at hy
        exact ((hF.h3W) j p x).2 hy
  l1c := ⟨fun t => X.rowMat_bij cr b (hR.h2) (hR.ratMu) t,
    fun j t => X.liftMat_bij cr b (hF.kForm) (hF.ewNorm) (hR.h4pos.2.2 b) (hF.h5) (hF.ratTh) j t, hR.h4pos.1,
    fun j t p v => hR.h4pos.2.1 j t p v, fun t v htv p => X.scal_rowsR cr b hR t v htv p,
    fun j t v htv p => X.scal_liftsR cr b hR hF j t v htv p⟩
  l1d := hl1d

def colsOfR (hR : RowHyp X cr true) (hpos : (lv (fc X.zs) true).Pos) (hh0 : X.H0) (Y : CxCol (fc := fc) X)
    (N : IndefNum Bs) (hl6 : (X.data cr true).L6 N) (hl1b : (X.colOf cr Y).PairingFactorsThroughPeriods) (hl1e : (X.colOf cr Y).L1e) :
    IndefColsR (lv (fc X.zs) true) (fc X.zs).Dc (fc X.zs).Sp N where
  toIndefData := X.data cr true
  pos := hpos
  h0 := hh0
  frames := (X.XE_specR cr true hR).1
  l1a := fun p => by
    change ((lv (fc X.zs) true).Qp Bs.μ0 p).map (X.rowMat cr true Bs.μ0).mulVecLin = X.Ep cr true p
    rw [X.rowMat_base cr true hR.h2, Matrix.mulVecLin_one, Submodule.map_id]
    ext x
    rw [mem_Ep]
    exact hR.h3 p x
  l1c := ⟨fun t => X.rowMat_bij cr true hR.h2 hR.ratMu t, hR.h4pos.1, fun j t p v => hR.h4pos.2.1 j t p v,
    fun t v htv p => X.scal_rowsR cr true hR t v htv p⟩
  l6 := hl6
  col := X.colOf cr Y
  l1b := hl1b
  l1e := hl1e

def cxPkgR (cf : ConvFace Bs) (Y : CxCol (fc := fc) X) (C CH : ℝ) (hst : X.zs.Stable) (hin : X.zs.InBlock)
    (hR0 : X.RowHyp cr false) (hF0 : X.LiftHyp cr false) (hpos : ∀ b, (lv (fc X.zs) b).Pos)
    (hprov : (lv (fc X.zs) false).Proviso) (htypes : (lv (fc X.zs) false).Types) (hh0 : X.H0)
    (hl1d : (X.data cr false).DimensionsOfPartsAgree) (hl3 : (X.data cr false).L3 ((fc X.zs).Z.num C CH))
    (hon : (X.data cr false).ON ((fc X.zs).Z.num C CH)) (hR1 : X.RowHyp cr true)
    (hl6 : (X.data cr true).L6 ((fc X.zs).Z.num C CH)) (hl1b : (X.colOf cr Y).PairingFactorsThroughPeriods) (hl1e : (X.colOf cr Y).L1e)
    (huntw : (X.data cr false).Untwisted ((fc X.zs).Z.num C CH))
    (hpass : Passage ((fc X.zs).Z.num C CH) (X.data cr false) (X.data cr true))
    (hfun0 : (X.data cr false).FUN ((fc X.zs).Z.num C CH)) (hconv : IndefConv Bs X.μ cf)
    (hB : HeckeAll cf (X.data cr false)) (hCc : HeckeRows cf (X.data cr true)) : IndefPkgR A fc cf C CH where
  Zs := X.zs
  stable := hst
  inBlock := hin
  core :=
    { base := { toIndefRows := X.rowsOfR cr false hR0 hF0 (hpos false) hprov htypes hh0 hl1d, l3 := hl3, on := hon }
      cols := X.colsOfR cr hR1 (hpos true) hh0 Y _ hl6 hl1b hl1e
      extra := { untw := huntw, level := ⟨rfl, rfl, rfl⟩, passage := hpass, fun0 := hfun0 } }
  conv := hconv
  heckeB := hB
  heckeC := hCc

end CxData

end Formalism.IndefR.Cx
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.CxHecke
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem cpt_smul (σ : K →+* ℂ) {n : ℕ} (a : K) (x : Fin n → K) : cpt σ (a • x) = σ a • cpt σ x := by
  funext i
  simp [cpt]

theorem relMat_op_key (σ : K →+* ℂ) {E : Type} [AddCommGroup E] [Module ℂ E] {D : ℕ} (f : (Fin D → ℂ) →ₗ[ℂ] E)
    (S : Module.End ℂ E) (hS : ∀ y, S (f y) ∈ LinearMap.range f) (hr : IsRat σ (relMat f (S ∘ₗ f)))
    (x : Fin D → K) :
    f (cpt σ ((kMat σ (relMat f (S ∘ₗ f))).mulVec x)) = S (f (cpt σ x)) := by
  have hsol : ∀ e ∈ LinearMap.range f, f (solve f e) = e := by
    rintro e ⟨y, rfl⟩
    have h : ∃ y', f y' = f y := ⟨y, rfl⟩
    simp only [solve, dif_pos h]
    exact h.choose_spec
  have hk : ∀ i k, σ (kOf σ (relMat f (S ∘ₗ f) i k)) = relMat f (S ∘ₗ f) i k := by
    intro i k
    obtain ⟨a, ha⟩ := hr i k
    have h : ∃ a : K, σ a = relMat f (S ∘ₗ f) i k := ⟨a, ha⟩
    simp only [kOf, dif_pos h]
    exact h.choose_spec
  have hc : cpt σ ((kMat σ (relMat f (S ∘ₗ f))).mulVec x) = (relMat f (S ∘ₗ f)).mulVec (cpt σ x) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [cpt, Matrix.mulVec, dotProduct, kMat, Matrix.map_apply, map_sum, map_mul, hk]
  rw [hc]
  have hv : ∀ v : Fin D → ℂ, v = ∑ k, v k • (Pi.single k (1 : ℂ) : Fin D → ℂ) := fun v => by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hcol : ∀ k, f (fun i => relMat f (S ∘ₗ f) i k) = S (f (Pi.single k 1)) := by
    intro k
    have h : (fun i => relMat f (S ∘ₗ f) i k) = solve f (S (f (Pi.single k 1))) := by
      funext i
      simp [relMat]
    rw [h, hsol _ (hS _)]
  have hM : (relMat f (S ∘ₗ f)).mulVec (cpt σ x) =
      ∑ k, (cpt σ x) k • (fun i => relMat f (S ∘ₗ f) i k) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hM, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [hv (cpt σ x), map_sum, map_sum]
  simp only [map_smul, hcol]

theorem eig_transport (σ : K →+* ℂ) {E : Type} [AddCommGroup E] [Module ℂ E] {D : ℕ} {H : Type}
    (f : (Fin D → ℂ) →ₗ[ℂ] E) (hf : Function.Injective f) (S : H → Module.End ℂ E)
    (hS : ∀ T y, S T (f y) ∈ LinearMap.range f) (hr : ∀ T, IsRat σ (relMat f (S T ∘ₗ f)))
    (P : Submodule ℂ E) (e : H → K)
    (hP : P ⊓ LinearMap.range f = (⨅ T, LinearMap.ker (S T - σ (e T) • LinearMap.id)) ⊓ LinearMap.range f) :
    P.comap (f.comp (cptL σ D)) =
      ⨅ T, LinearMap.ker (Matrix.toLin' (kMat σ (relMat f (S T ∘ₗ f))) - e T • LinearMap.id) := by
  have hcinj : ∀ {a b : Fin D → K}, cpt σ a = cpt σ b → a = b := fun h =>
    funext fun i => σ.injective (congrFun h i)
  have key : ∀ x, x ∈ P.comap (f.comp (cptL σ D)) ↔ f (cpt σ x) ∈ P := fun x => Iff.rfl
  ext x
  rw [key]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, Matrix.toLin'_apply, sub_eq_zero]
  have hmem : f (cpt σ x) ∈ LinearMap.range f := LinearMap.mem_range_self f _
  constructor
  · intro hx T
    have h1 : f (cpt σ x) ∈ P ⊓ LinearMap.range f := Submodule.mem_inf.mpr ⟨hx, hmem⟩
    rw [hP] at h1
    have h2 := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp h1).1 T
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h2
    apply hcinj
    apply hf
    rw [relMat_op_key σ f (S T) (hS T) (hr T) x, cpt_smul, map_smul]
    exact h2
  · intro hx
    have h1 : f (cpt σ x) ∈ P ⊓ LinearMap.range f := by
      rw [hP]
      refine Submodule.mem_inf.mpr ⟨(Submodule.mem_iInf _).mpr fun T => ?_, hmem⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
      have h3 := relMat_op_key σ f (S T) (hS T) (hr T) x
      rw [hx T, cpt_smul, map_smul] at h3
      exact h3.symm
    exact (Submodule.mem_inf.mp h1).1

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)
  (cf : ConvFace Bs)

structure HeckeRowsC where

  hC : cf.Hk → Module.End ℂ X.EE

  maps : ∀ T, ∀ e ∈ X.EEl b, hC T e ∈ X.EEl b

  rat : ∀ T, IsRat Bs.v0.embedding (relMat (X.iC cr b Bs.μ0) (hC T ∘ₗ X.iC cr b Bs.μ0))

  eig : ∀ c, X.EEp c ⊓ X.EEl b =
    (⨅ T, LinearMap.ker (hC T - Bs.v0.embedding (cf.ev c T) • LinearMap.id)) ⊓ X.EEl b

structure HeckeWC where

  hC : ∀ j, cf.Hk → Module.End ℂ (X.W j)

  maps : ∀ j T y, hC j T (X.w0C b j y) ∈ LinearMap.range (X.w0C b j)

  rat : ∀ j T, IsRat Bs.v0.embedding (relMat (X.w0C b j) (hC j T ∘ₗ X.w0C b j))

  eig : ∀ j c, X.Wp j c ⊓ LinearMap.range (X.w0C b j) =
    (⨅ T, LinearMap.ker (hC j T - Bs.v0.embedding (cf.ev c T) • LinearMap.id)) ⊓ LinearMap.range (X.w0C b j)

variable {X cr b cf}

def HeckeRowsC.hEK (H : X.HeckeRowsC cr b cf) (T : cf.Hk) :
    Module.End K (Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) :=
  Matrix.toLin' (kMat Bs.v0.embedding (relMat (X.iC cr b Bs.μ0) (H.hC T ∘ₗ X.iC cr b Bs.μ0)))

def HeckeWC.hWK (H : X.HeckeWC b cf) (j : Bs.J) (T : cf.Hk) : Module.End K (Fin (X.dW b j) → K) :=
  Matrix.toLin' (kMat Bs.v0.embedding (relMat (X.w0C b j) (H.hC j T ∘ₗ X.w0C b j)))

theorem HeckeRowsC.maps' (h2 : X.H2 cr b) (H : X.HeckeRowsC cr b cf) (T : cf.Hk) (y) :
    H.hC T (X.iC cr b Bs.μ0 y) ∈ LinearMap.range (X.iC cr b Bs.μ0) := by
  rw [h2.2.2]
  apply H.maps
  rw [← h2.2.2]
  exact LinearMap.mem_range_self _ y

theorem HeckeRowsC.key (h2 : X.H2 cr b) (H : X.HeckeRowsC cr b cf) (T : cf.Hk)
    (x : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) :
    X.iC cr b Bs.μ0 (cpt Bs.v0.embedding (H.hEK T x)) = H.hC T (X.iC cr b Bs.μ0 (cpt Bs.v0.embedding x)) := by
  simpa [HeckeRowsC.hEK, Matrix.toLin'_apply] using
    relMat_op_key Bs.v0.embedding (X.iC cr b Bs.μ0) (H.hC T) (H.maps' h2 T) (H.rat T) x

theorem HeckeWC.key (H : X.HeckeWC b cf) (j : Bs.J) (T : cf.Hk) (x : Fin (X.dW b j) → K) :
    X.w0C b j (cpt Bs.v0.embedding (H.hWK j T x)) = H.hC j T (X.w0C b j (cpt Bs.v0.embedding x)) := by
  simpa [HeckeWC.hWK, Matrix.toLin'_apply] using
    relMat_op_key Bs.v0.embedding (X.w0C b j) (H.hC j T) (H.maps j T) (H.rat j T) x

theorem HeckeRowsC.eigE (h2 : X.H2 cr b) (H : X.HeckeRowsC cr b cf) (c : Bs.Ix) :
    X.Ep cr b c = ⨅ T, LinearMap.ker (H.hEK T - cf.ev c T • LinearMap.id) := by
  have h := eig_transport Bs.v0.embedding (X.iC cr b Bs.μ0) h2.1 H.hC (H.maps' h2) H.rat (X.EEp c) (cf.ev c)
    (by rw [h2.2.2]; exact H.eig c)
  exact h

theorem HeckeWC.eigW (hk : X.KForm b) (he : X.EWnorm b) (hn : 0 < X.nP b) (H : X.HeckeWC b cf) (j : Bs.J)
    (c : Bs.Ix) :
    X.WpK b j c = ⨅ T, LinearMap.ker (H.hWK j T - cf.ev c T • LinearMap.id) := by
  have hinjW : Function.Injective (X.wC b j Bs.v0) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c' hc
    simp only [wC, lin, Fintype.linearCombination_apply] at hc
    funext i
    exact Fintype.linearIndependent_iff.mp (hk j Bs.v0).1 c' hc i
  have hinjE : Function.Injective (X.eW b j) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h := he j x x
    rw [hx, inner_zero_left] at h
    have h' : ((X.nP b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have h'' : ⟪x, x⟫_ℂ = 0 := (mul_eq_zero.mp h.symm).resolve_left h'
    exact inner_self_eq_zero.mp h''
  have hinj : Function.Injective (X.w0C b j) := by
    first
    | exact hinjE.comp hinjW
    | (simp only [w0C, LinearMap.coe_comp]; exact hinjE.comp hinjW)
  exact eig_transport Bs.v0.embedding (X.w0C b j) hinj (H.hC j) (H.maps j) (H.rat j) (X.Wp j c) (cf.ev c)
    (H.eig j c)

def heckeRows_of (h2 : X.H2 cr b) (H : X.HeckeRowsC cr b cf) : HeckeRows cf (X.data cr b) where
  hE := H.hEK
  eigE := H.eigE h2

def heckeAll_of (h2 : X.H2 cr b) (hk : X.KForm b) (he : X.EWnorm b) (hn : 0 < X.nP b) (H : X.HeckeRowsC cr b cf)
    (HW : X.HeckeWC b cf) : HeckeAll cf (X.data cr b) where
  toHeckeRows := heckeRows_of h2 H
  hW := HW.hWK
  eigW := HW.eigW hk he hn

theorem heckeB_of (h2 : X.H2 cr false) (hk : X.KForm false) (he : X.EWnorm false) (hp : X.H4pos)
    (H : X.HeckeRowsC cr false cf) (HW : X.HeckeWC false cf) : Nonempty (HeckeAll cf (X.data cr false)) := ⟨heckeAll_of h2 hk he (hp.2.2 false) H HW⟩

theorem heckeC_of (h2 : X.H2 cr true) (H : X.HeckeRowsC cr true cf) : Nonempty (HeckeRows cf (X.data cr true)) := ⟨heckeRows_of h2 H⟩

end CxData

end Formalism.IndefR.Cx
end
end

