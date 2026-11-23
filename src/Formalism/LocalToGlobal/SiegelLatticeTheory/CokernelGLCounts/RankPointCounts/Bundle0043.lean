module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0040
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabKset
section
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Stab

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

abbrev stabR (h : Hfin X u) : Subgroup (Hfin X u) := gamR X u ⊓ (kR X u).map (MulAut.conj h).toMonoidHom

theorem kset_one : (1 : X.B.I.Gf) ∈ X.B.I.Kset := (Formalism.UG.stabGL X.B.I.Lf).one_mem

theorem stab_kset {h g : Hfin X u} (hg : g ∈ (kR X u).map (MulAut.conj h).toMonoidHom) :
    ((h⁻¹ * g⁻¹ * h : Hfin X u) : X.B.I.Gf) ∈ X.B.I.Kset := by
  rw [mem_map_conj, mem_kR_iff] at hg
  have e : h⁻¹ * g⁻¹ * h = (h⁻¹ * g * h)⁻¹ := by group
  rw [e, Subgroup.coe_inv]
  exact kset_inv' X.B.I hg

variable {X u}

def matR {g : Hfin X u} (hg : g ∈ gamR X u) : GL (Fin X.B.I.n) X.B.I.E := Classical.choose (gamR_mat hg)

theorem matR_spec {g : Hfin X u} (hg : g ∈ gamR X u) :
    matR hg ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J ∧
      X.B.I.fmat (g : X.B.I.Gf) = (matR hg : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) :=
  Classical.choose_spec (gamR_mat hg)

theorem matR_mem (h g : Hfin X u) (hg : g ∈ stabR X u h) :
    matE X (matR (Subgroup.mem_inf.1 hg).1) ∈ AH X u (lat X u h) := by
  obtain ⟨hM, hMf⟩ := matR_spec (Subgroup.mem_inf.1 hg).1
  have hfix : ∀ y ∈ fixSet X u, (matR (Subgroup.mem_inf.1 hg).1 : Matrix _ _ _).map
      (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) *ᵥ incl X.B.I y = incl X.B.I y := fun y hy => by
    rw [← hMf]; exact hfin_fix X u g y hy
  refine ⟨matE_isom X _ hM, fun a => matE_fix X u _ hfix _ (Or.inl (Or.inl ⟨a, rfl⟩)),
    fun a => matE_fix X u _ hfix _ (Or.inl (Or.inr ⟨a, rfl⟩)), matE_fix X u _ hfix _ (Or.inr rfl), ?_⟩
  have e : g * h * (h⁻¹ * g⁻¹ * h) = h := by group
  have := lat_act X u g h (h⁻¹ * g⁻¹ * h) _ hMf (stab_kset X u (Subgroup.mem_inf.1 hg).2)
  rw [e] at this
  exact this.symm

theorem card_stab (h : Hfin X u) : Nat.card ↥(stabR X u h) = Nat.card ↥(AH X u (lat X u h)) := by
  let Φ : ↥(stabR X u h) → ↥(AH X u (lat X u h)) := fun g =>
    ⟨matE X (matR (Subgroup.mem_inf.1 g.2).1), matR_mem h g g.2⟩
  have hinj : Function.Injective Φ := by
    intro g g' hgg
    have e1 : matE X (matR (Subgroup.mem_inf.1 g.2).1) = matE X (matR (Subgroup.mem_inf.1 g'.2).1) :=
      congrArg Subtype.val hgg
    have e2 := matE_inj X e1
    have f1 := (matR_spec (Subgroup.mem_inf.1 g.2).1).2
    have f2 := (matR_spec (Subgroup.mem_inf.1 g'.2).1).2
    have e3 : X.B.I.fmat ((g : Hfin X u) : X.B.I.Gf) = X.B.I.fmat ((g' : Hfin X u) : X.B.I.Gf) := by
      rw [f1, f2, e2]
    exact Subtype.ext (Subtype.ext (Subtype.ext (Units.ext e3)))
  have hsurj : Function.Surjective Φ := by
    rintro ⟨γ, hγ⟩
    obtain ⟨hi, he, hf, hz, hl⟩ := hγ
    set g := gOf X u γ hi he hf hz with hgdef
    have hgR : g ∈ gamR X u := (mem_gamR_iff X u g).2 ⟨glOf X γ, glOf_unitary X γ hi, rfl⟩
    have hlat : lat X u (g * h * 1) = lat X u h := by
      rw [lat_act X u g h 1 (glOf X γ) rfl (kset_one X), matE_glOf, hl]
    have hgK : g ∈ (kR X u).map (MulAut.conj h).toMonoidHom := by
      rw [mem_map_conj, mem_kR_iff]
      have hK := LatDictK.dict_K X ((h : X.B.I.Gf) * X.xu u) (((g * h * 1 : Hfin X u) : X.B.I.Gf) * X.xu u)
        (latOf X u h) (fun y => Iff.rfl) (fun y => by
          show y ∈ latOf X u h ↔ y ∈ latOf X u (g * h * 1)
          rw [← lat_coe X u h, ← lat_coe X u (g * h * 1), hlat])
      have e4 : ((h : X.B.I.Gf) * X.xu u)⁻¹ * (((g * h * 1 : Hfin X u) : X.B.I.Gf) * X.xu u) =
          (X.xu u)⁻¹ * ((h⁻¹ * g * h : Hfin X u) : X.B.I.Gf) * X.xu u := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
        group
      rw [e4] at hK
      have e5 : ((h⁻¹ * g * h : Hfin X u) : X.B.I.Gf) =
          X.xu u * ((X.xu u)⁻¹ * ((h⁻¹ * g * h : Hfin X u) : X.B.I.Gf) * X.xu u) * (X.xu u)⁻¹ := by group
      rw [e5]
      exact kset_mul' X.B.I (kset_mul' X.B.I (X.xu_K u) hK) (kset_inv' X.B.I (X.xu_K u))
    have hg : g ∈ stabR X u h := Subgroup.mem_inf.2 ⟨hgR, hgK⟩
    refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
    show matE X (matR (Subgroup.mem_inf.1 hg).1) = γ
    have f1 := (matR_spec (Subgroup.mem_inf.1 hg).1).2
    have e6 : matR (Subgroup.mem_inf.1 hg).1 = glOf X γ := by
      apply Units.ext
      apply Matrix.map_injective (inclInj_holds X)
      show ((matR (Subgroup.mem_inf.1 hg).1 : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map
          (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) =
        ((glOf X γ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map
          (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F))
      rw [← f1]
      rfl
    rw [e6, matE_glOf]
  exact Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)

end Stab

end Formalism.L2.SG.RhoPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolGrp
section
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolGrp

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ZsVolCut Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Uni

variable {R : Type*} [CommRing R] {n : ℕ}

theorem det_lo {l : Matrix (Fin n) (Fin n) R} (h1 : ∀ a, l a a = 1) (h2 : ∀ a b, a < b → l a b = 0) : l.det = 1 := by
  rw [Matrix.det_of_lowerTriangular l (fun i j hij => h2 i j hij)]
  exact Finset.prod_eq_one fun i _ => h1 i

theorem det_up {l : Matrix (Fin n) (Fin n) R} (h1 : ∀ a, l a a = 1) (h2 : ∀ a b, b < a → l a b = 0) : l.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => h2 i j hij)]
  exact Finset.prod_eq_one fun i _ => h1 i

theorem inv_eq_adj {l : Matrix (Fin n) (Fin n) R} (h : l.det = 1) : l⁻¹ = l.adjugate := by
  rw [Matrix.inv_def, h, Ring.inverse_one, one_smul]

theorem adj_mem (S : Subring R) {l : Matrix (Fin n) (Fin n) R} (h : ∀ a b, l a b ∈ S) (i j : Fin n) :
    l.adjugate i j ∈ S := by
  let lS : Matrix (Fin n) (Fin n) S := fun a b => ⟨l a b, h a b⟩
  have e : l = S.subtype.mapMatrix lS := by
    ext a b
    rfl
  rw [e, ← RingHom.map_adjugate]
  exact (lS.adjugate i j).2

end Uni

section Int

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E] [TopologicalSpace E]
  [MeasurableSpace E] (Mp : Loc.Model F E) {n : ℕ}

theorem intLow_one : Formalism.MainNotions.S.TieN.IntLow Mp (1 : Matrix (Fin n) (Fin n) E) :=
  ⟨fun a => by simp, fun a b h => by simp [Matrix.one_apply, h.ne], fun a b => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

theorem intUp_one : Formalism.MainNotions.S.TieN.IntUp Mp (1 : Matrix (Fin n) (Fin n) E) :=
  ⟨fun a => by simp, fun a b h => by simp [Matrix.one_apply, h.ne'], fun a b => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

theorem intLow_mul {l l' : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntLow Mp l)
    (h' : Formalism.MainNotions.S.TieN.IntLow Mp l') : Formalism.MainNotions.S.TieN.IntLow Mp (l * l') := by
  first | exact GlobalTheory.LowerIntegralMul.intLow_mul .. | (apply GlobalTheory.LowerIntegralMul.intLow_mul <;> assumption) | (intros; apply GlobalTheory.LowerIntegralMul.intLow_mul <;> assumption) | (apply @GlobalTheory.LowerIntegralMul.intLow_mul <;> assumption) | (intros; apply @GlobalTheory.LowerIntegralMul.intLow_mul <;> assumption) | (apply @GlobalTheory.LowerIntegralMul.intLow_mul <;> first | assumption | infer_instance) | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› Mp n l l' h h' | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› Mp n l l' h | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› Mp n l l' | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› Mp n l | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› Mp n | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› Mp | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E | exact @GlobalTheory.LowerIntegralMul.intLow_mul F

theorem intUp_mul {l l' : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntUp Mp l)
    (h' : Formalism.MainNotions.S.TieN.IntUp Mp l') : Formalism.MainNotions.S.TieN.IntUp Mp (l * l') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨fun a => ?_, fun a b hab => ?_, fun a b => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [h1, h1', mul_one]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [h2 a c h, zero_mul]
      · rw [h2' c a h, mul_zero]
    · simp
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with h | h
    · rw [h2 a c h, zero_mul]
    · rw [h2' c b (lt_of_lt_of_le hab h), mul_zero]
  · rw [Matrix.mul_apply]
    exact sum_mem fun c _ => mul_mem (h3 a c) (h3' c b)

theorem intLow_inv {l : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntLow Mp l) :
    Formalism.MainNotions.S.TieN.IntLow Mp l⁻¹ ∧ l⁻¹ * l = 1 ∧ l * l⁻¹ = 1 := by
  obtain ⟨h1, h2, h3⟩ := h
  have hd := det_lo h1 h2
  have hu : IsUnit l.det := by rw [hd]; exact isUnit_one
  have hli : l⁻¹ * l = 1 := Matrix.nonsing_inv_mul l hu
  have hil : l * l⁻¹ = 1 := Matrix.mul_nonsing_inv l hu
  have := Matrix.invertibleOfIsUnitDet l hu
  have hb : l⁻¹.BlockTriangular OrderDual.toDual :=
    Matrix.blockTriangular_inv_of_blockTriangular (fun i j hij => h2 i j hij)
  have hz : ∀ a b, a < b → l⁻¹ a b = 0 := fun a b hab => hb hab
  refine ⟨⟨fun a => ?_, hz, fun a b => ?_⟩, hli, hil⟩
  · have e := congrFun (congrFun hil a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a, h1, one_mul] at e
    · simpa using e
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [hz c a h, mul_zero]
      · rw [h2 a c h, zero_mul]
    · simp
  · rw [inv_eq_adj hd]
    exact adj_mem Mp.R h3 a b

theorem intUp_inv {l : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntUp Mp l) :
    Formalism.MainNotions.S.TieN.IntUp Mp l⁻¹ ∧ l⁻¹ * l = 1 ∧ l * l⁻¹ = 1 := by
  obtain ⟨h1, h2, h3⟩ := h
  have hd := det_up h1 h2
  have hu : IsUnit l.det := by rw [hd]; exact isUnit_one
  have hli : l⁻¹ * l = 1 := Matrix.nonsing_inv_mul l hu
  have hil : l * l⁻¹ = 1 := Matrix.mul_nonsing_inv l hu
  have := Matrix.invertibleOfIsUnitDet l hu
  have hb : l⁻¹.BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular (fun i j hij => h2 i j hij)
  have hz : ∀ a b, b < a → l⁻¹ a b = 0 := fun a b hab => hb hab
  refine ⟨⟨fun a => ?_, hz, fun a b => ?_⟩, hli, hil⟩
  · have e := congrFun (congrFun hil a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a, h1, one_mul] at e
    · simpa using e
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [h2 a c h, zero_mul]
      · rw [hz c a h, mul_zero]
    · simp
  · rw [inv_eq_adj hd]
    exact adj_mem Mp.R h3 a b

end Int

theorem zhatOM_zhatOM {K : Type*} [CommRing K] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    ZhatOM (ZhatOM Z) = Z := by
  ext a b
  simp only [ZhatOM]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

end Formalism.L2.SG.Pf.ZsVolGrp

end
end

