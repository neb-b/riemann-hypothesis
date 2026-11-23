module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeAlt
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DualCon

theorem Rep.baseChange (S : Scheme.{0}) (A B S' S'' B'' : Over S) [GrpObj A] (b : B ⟶ S')
    (P : LB (A ⊗ B).left) (h : S'' ⟶ S') (k : B'' ⟶ B) (b'' : B'' ⟶ S'') (hR : Rep A b P)
    (hpb : IsPullback k b'' b h) : Rep A b'' (ev P (fst A B'') (snd A B'' ≫ k)) := by
  have hP : P.IsLB := hR.fam.isLB
  have hP' : (ev P (fst A B'') (snd A B'' ≫ k)).IsLB := pull_isLB hP _
  have key : ∀ (Y : Over S) (a : Y ⟶ A) (y : Y ⟶ B''), evc hP' a y = evc hP a (y ≫ k) := by
    intro Y a y
    rw [evc_ev hP, lift_fst, lift_snd_assoc]
  have iso : ∀ (T : Over S) (N : LB (A ⊗ T).left) (hN : N.IsLB) (y : T ⟶ B''),
      LBIso N (ev (ev P (fst A B'') (snd A B'' ≫ k)) (fst A T) (snd A T ≫ y)) ↔
        LBIso N (ev P (fst A T) (snd A T ≫ y ≫ k)) := by
    intro T N hN y
    rw [← cls_eq_iff hN (pull_isLB hP' _), ← cls_eq_iff hN (pull_isLB hP _), cls_ev hP', cls_ev hP, key,
      Category.assoc]
  refine ⟨⟨hP', (isAdditive_iff hP').2 fun Y a a' t ↦ ?_⟩, fun T t N hN ↦ ?_⟩
  · rw [key, key, key]
    exact (isAdditive_iff hP).1 hR.fam.add Y a a' (t ≫ k)
  · obtain ⟨x, ⟨hx1, hx2⟩, hu⟩ := hR.univ T (t ≫ h) N hN
    refine ⟨hpb.lift x t hx1, ⟨hpb.lift_snd _ _ _, (iso T N hN.isLB _).2 ?_⟩, fun y ⟨hy1, hy2⟩ ↦ ?_⟩
    · rw [hpb.lift_fst]
      exact hx2
    · have e : y ≫ k = x := hu (y ≫ k) ⟨by rw [Category.assoc, hpb.w, ← Category.assoc, hy1],
        (iso T N hN.isLB y).1 hy2⟩
      exact hpb.hom_ext (by rw [e, hpb.lift_fst]) (by rw [hy1, hpb.lift_snd])

end GlobalTheory.DualCon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigCellEigenbasisCombinationCoeffUnique
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPole

open GlobalTheory.Reg GlobalTheory.FlagMod
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

theorem cell_eigComb_coeff_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsCell TF Z U e v W k L N → ∀ (S : Type) [CommRing S] (zw : Sp S ⟶ Y₀ TF.X Z) (hzw : ⊤ ≤ zw ⁻¹ᵁ W) (x : Sp S ⟶ TF.Y.X) (hx : zw ≫ toBase TF Z = x) (hUx : ⊤ ≤ x ⁻¹ᵁ U.1) (σ : E →+* ℂ) (a b : Fin (Dw.mult σ) → S) (w' : Sp (DualNumber S) ⟶ TF.Y.t.G.left), IsCombAtG TF.Y.t x (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) a w' → IsCombAtG TF.Y.t x (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) b w' → a = b := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv W k L N hC S _ zw hzw x hx hUx σ a b w' ha hb
  subst hx
  obtain ⟨-, -, hWk, hLz, hLu, hNz, hN1, hcomb⟩ := hC
  have hk : ⊤ ≤ (zw ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := fun p hp => hWk (hzw hp)
  have hxx : (zw ≫ inc₀ TF.X Z) ≫ TF.X.π = zw ≫ toBase TF Z := Category.assoc _ _ _
  have hvT : ∀ m, IsTanAtG TF.Y.t (zw ≫ toBase TF Z) (spMap (dualMap (ev (zw ≫ toBase TF Z) U.1 hUx)) ≫ v m) :=
    fun m => GlobalTheory.LieMet.isTan_map _ (spMap_ev _ U.2 hUx) (hv.1 m)
  let f : Fin (Dw.mult σ) → TanM (zw ≫ toBase TF Z) TF.Y.t.G := fun j => GlobalTheory.LieMet.tanOf (hvT (e ⟨σ, j⟩))
  have uniq : ∀ {w₁ w₂ : Sp (DualNumber S) ⟶ TF.Y.t.G.left} (cf : Fin (Dw.mult σ) → S),
      IsCombAtG TF.Y.t (zw ≫ toBase TF Z) (fun j => (tv (f j)).left) cf w₁ →
      IsCombAtG TF.Y.t (zw ≫ toBase TF Z) (fun j => (tv (f j)).left) cf w₂ → w₁ = w₂ := by
    intro w₁ w₂ cf h₁ h₂
    obtain ⟨u₁, hu₁, hw₁⟩ := h₁
    obtain ⟨u₂, hu₂, hw₂⟩ := h₂
    have hu : u₁ = u₂ := funext fun i => Over.OverMorphism.ext ((hu₁ i).trans (hu₂ i).symm)
    rw [← hw₁, ← hw₂, hu]
  have hsum : ∀ cf : Fin (Dw.mult σ) → S,
      IsCombAtG TF.Y.t (zw ≫ toBase TF Z) (fun j => (tv (f j)).left) cf (tv (∑ j, cf j • f j)).left :=
    fun cf => (GlobalTheory.LieMet.isComb_iff f cf _).2 rfl
  have hab : ∑ j, a j • f j = ∑ j, b j • f j :=
    GlobalTheory.LieMet.tan_ext ((uniq a (hsum a) ha).trans (uniq b (hsum b) hb).symm)
  let V := TF.X.F.vecAt k (zw ≫ inc₀ TF.X Z) hk hxx σ
  let C : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S := (L σ * N σ).map (ev zw W hzw)
  have hV : ∀ i, V i = ∑ j, C i j • f j := fun i =>
    (GlobalTheory.LieMet.isComb_iff f _ _).1 (hcomb S zw hzw hUx hk hxx σ i)
  have hCdet : IsUnit C.det := by
    have hm : C = (L σ).map (ev zw W hzw) * (N σ).map (ev zw W hzw) := Matrix.map_mul
    rw [hm, Matrix.det_mul]
    refine IsUnit.mul ?_ ?_
    · rw [Matrix.det_of_lowerTriangular _ (fun i j h => by
        show ev zw W hzw (L σ i j) = 0
        rw [hLz σ i j (OrderDual.toDual_lt_toDual.1 h), map_zero])]
      exact IsUnit.prod_univ_iff.2 fun i => (hLu σ i).map (ev zw W hzw)
    · rw [Matrix.det_of_upperTriangular (M := (N σ).map (ev zw W hzw)) (fun i j h => by
        show ev zw W hzw (N σ i j) = 0
        rw [hNz σ i j h, map_zero])]
      refine IsUnit.prod_univ_iff.2 fun i => ?_
      show IsUnit (ev zw W hzw (N σ i i))
      rw [hN1, map_one]; exact isUnit_one
  have hf' : ∀ j, f j = ∑ i, C⁻¹ j i • V i := fun j => by
    simp only [hV, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    have e2 : ∀ l, (∑ i, C⁻¹ j i * C i l) = (1 : Matrix _ _ S) j l := fun l => by
      rw [← Matrix.nonsing_inv_mul _ hCdet, Matrix.mul_apply]
    simp only [e2, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have key : ∀ cf : Fin (Dw.mult σ) → S, ∑ j, cf j • f j = ∑ i, Matrix.vecMul cf C⁻¹ i • V i := fun cf => by
    simp only [hf', Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, Matrix.vecMul, dotProduct]
  have hg : Matrix.vecMul a C⁻¹ = Matrix.vecMul b C⁻¹ := funext
    (Fintype.linearIndependent_iffₛ.1 (TF.X.F.linearIndependent_vecAt k _ hk hxx σ) _ _
      (by rw [← key, ← key, hab]))
  calc a = Matrix.vecMul (Matrix.vecMul a C⁻¹) C := by
        rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hCdet, Matrix.vecMul_one]
    _ = Matrix.vecMul (Matrix.vecMul b C⁻¹) C := by rw [hg]
    _ = b := by rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hCdet, Matrix.vecMul_one]

end GlobalTheory.LogPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigCellFramedPointVectorsLowerTriangularEigenbas
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.LogPole.frVec_cell_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsCell TF Z U e v W k L N → ∀ (S : Type) [CommRing S] [Algebra c.F S] (w : FrPt Xo c S) (zw : Sp S ⟶ Y₀ TF.X Z) (hzw : ⊤ ≤ zw ⁻¹ᵁ W) (x : Sp S ⟶ TF.Y.X) (hx : frX w ≫ TF.Y.j = x) (hUx : ⊤ ≤ x ⁻¹ᵁ U.1), zw ≫ inc₀ TF.X Z = TF.X.ptY w → ∃ B : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, (∀ σ i j, i < j → B σ i j = 0) ∧ (∀ σ i, IsUnit (B σ i i)) ∧ ∀ σ i, IsCombAtG TF.Y.t x (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) (fun j => (B σ * (L σ * N σ).map (ev zw W hzw)) i j) (tv (frVec TF.Y w hx σ i)).left := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv W k L N h S _ _ w zw hzw x hx hUx hpt
  have hl : TF.X.F.Lies (zw ≫ inc₀ TF.X Z) w := hpt ▸ TF.X.lies_ptY w
  have hk : ⊤ ≤ (zw ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := GlobalTheory.FlagMod.le_preimage_map _ h.2.2.1 hzw
  have hxz' : (zw ≫ inc₀ TF.X Z) ≫ TF.X.π = zw ≫ toBase TF Z := Category.assoc _ _ _
  have hxz : zw ≫ toBase TF Z = x := hxz'.symm.trans (hl.1.trans hx)
  subst hxz
  obtain ⟨Q, hQ⟩ := TF.X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd w) hl.1 k hk
  obtain ⟨t, ht⟩ := hQ.exists_frBor hl
  choose b hb hdiag hsum using fun σ =>
    GlobalTheory.FlagMod.frVec_of_frBor (M := (TF.X.F.M k).toMChart) (TF.X.F.inM hk hxz') (hQ.over.trans hxz') hx ht σ
  refine ⟨fun σ i j => b σ j i, fun σ i j hij => hb σ hij, fun σ i => by show IsUnit (b σ i i); rw [hdiag]; exact Units.isUnit _,
    fun σ i => ?_⟩
  have hv' : ∀ j, IsTanAtG TF.Y.t (zw ≫ toBase TF Z)
      (spMap (dualMap (ev (zw ≫ toBase TF Z) U.1 hUx)) ≫ v j) := by
    intro j
    have h0 := GlobalTheory.FactorDepth.isTanAtG_map TF.Y.t (ev (zw ≫ toBase TF Z) U.1 hUx) (hv.1 j)
    rwa [LogKS.chart, GlobalTheory.FlagMod.spMap_ev _ U.2 hUx] at h0
  have hcell := h.2.2.2.2.2.2.2 S zw hzw hUx hk hxz' σ
  have h2 : IsCombAtG TF.Y.t (zw ≫ toBase TF Z)
      (fun j => (tv (TF.X.F.vecAt k (zw ≫ inc₀ TF.X Z) hk hxz' σ j)).left) (fun j => b σ j i)
      (tv (frVec TF.Y w hx σ i)).left := by
    rw [GlobalTheory.LieMet.isComb_iff, hsum σ i, hQ.frVec_eq hxz' (hQ.over.trans hxz') σ]
  have h3 := GlobalTheory.TangentLinear.isCombAtG_mulVec _ (fun j => hv' (e ⟨σ, j⟩)) _
    (Matrix.of fun m j => ev zw W hzw ((L σ * N σ) j m)) (fun j => b σ j i) _ (fun j => hcell j) h2
  convert h3 using 1
  funext m
  show ∑ j, b σ j i * ev zw W hzw ((L σ * N σ) j m) = ∑ j, ev zw W hzw ((L σ * N σ) j m) * b σ j i
  exact Finset.sum_congr rfl fun j _ => _root_.mul_comm _ _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigCellPointEqOfBaseAndCellCoordinatesEq
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPole.CellMono

open GlobalTheory.Reg GlobalTheory.FlagMod MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

theorem initSpan_eq_of_lowerTri {R : Type} [CommRing R] {m : ℕ} {M : Type} [AddCommGroup M] [Module R M]
    {A : Matrix (Fin m) (Fin m) R} (hA : ∀ i j, i < j → A i j = 0) (hd : ∀ i, IsUnit (A i i)) {u w : Fin m → M}
    (e : ∀ i, u i = ∑ j, A i j • w j) (k : ℕ) : initSpan R u k = initSpan R w k := by
  have hB : A.BlockTriangular OrderDual.toDual := fun i j h => hA i j (OrderDual.toDual_lt_toDual.1 h)
  have hdet : IsUnit A.det := by
    rw [Matrix.det_of_lowerTriangular A hB]
    exact IsUnit.prod_univ_iff.2 hd
  have : Invertible A := Matrix.invertibleOfIsUnitDet A hdet
  have hB' := Matrix.blockTriangular_inv_of_blockTriangular hB
  refine le_antisymm (initSpan_le_of_tri (B := A.transpose) (fun i j h => hA j i h) e k)
    (initSpan_le_of_tri (B := A⁻¹.transpose) (fun i j h => hB' (OrderDual.toDual_lt_toDual.2 h)) (fun i => ?_) k)
  simp only [e, Finset.smul_sum, smul_smul, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have e2 : ∀ l, (∑ j, A⁻¹ i j * A j l) = (1 : Matrix _ _ R) i l := fun l => by
    rw [← Matrix.nonsing_inv_mul A hdet, Matrix.mul_apply]
  simp only [e2, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {S : Type} [CommRing S] [Algebra c.F S]

theorem eq_of_initSpan_eq (X : FlagCover Y) {y : Sp S ⟶ Xo.XF c}
    (hy : y ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) {x : Sp S ⟶ Y.X} (hxy : x = y ≫ Y.j) {z z' : Sp S ⟶ X.YY}
    (hx : z ≫ X.π = x) (hx' : z' ≫ X.π = x) {k k' : X.F.J} (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k) (hz' : ⊤ ≤ z' ⁻¹ᵁ X.F.U k')
    (h : ∀ σ i, initSpan S (X.F.vecAt k' z' hz' hx' σ) i = initSpan S (X.F.vecAt k z hz hx σ) i) : z = z' := by
  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr hy (hx.trans hxy) k hz
  obtain ⟨P, hP⟩ := X.top.exists_chartFr hy (hx'.trans hxy) k' hz'
  have hQx := hQ.over.trans hx
  have hPx := hP.over.trans hx'
  have ex : ∀ σ, ∃ b : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧
      ∀ i, frVec Y P hPx σ i = ∑ j, b j i • frVec Y Q hQx σ j := fun σ => by
    rw [hQ.frVec_eq hx, hP.frVec_eq hx']
    exact exists_tri_of_eq (X.F.linearIndependent_vecAt k z hz hx σ) (h σ)
  choose b hb hu hv using ex
  have e : P.x = Q.x := by
    rw [← frX_fst, ← frX_fst, xF_ext (Y := Y) (frX_snd P) (frX_snd Q) (hPx.trans hQx.symm)]
  have hB : ∃ t, FrBor t Q P := by
    obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := P
    dsimp only at e
    subst e
    obtain ⟨u0, hu0⟩ := gen_unit Q.s s' Q.gen t4'
    exact ⟨_, frBor_of_frVec (X.F.inM hz hx) hQx hPx
      (fun ix => match ix with | none => u0 | some p => (hu p.1 p.2).unit) b hb (fun _ _ => rfl) hv fun _ => hu0⟩
  obtain ⟨t, ht⟩ := hB
  exact (X.rep S P).unique (hQ.lies.frBor ht) hP.lies

end GlobalTheory.LogPole.CellMono

namespace GlobalTheory.LogPole

open GlobalTheory.Reg GlobalTheory.FlagMod MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

theorem eq_of_cellCoord_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N) (S : Type) [CommRing S] (z₁ z₂ : Sp S ⟶ Y₀ TF.X Z) (h₁ : ⊤ ≤ z₁ ⁻¹ᵁ W) (h₂ : ⊤ ≤ z₂ ⁻¹ᵁ W), ⊤ ≤ z₁ ⁻¹ᵁ U₀ TF.X Z → ⊤ ≤ z₂ ⁻¹ᵁ U₀ TF.X Z → (∀ r, ev z₁ W h₁ (((toBase TF Z).appLE U.1 W h.2.1).hom r) = ev z₂ W h₂ (((toBase TF Z).appLE U.1 W h.2.1).hom r)) → (∀ i, ev z₁ W h₁ (cellCoord N i) = ev z₂ W h₂ (cellCoord N i)) → z₁ = z₂ := by
  intro E _ _ _ H Dw l Xo c TF Z _ U n e v hv W k L N hC S _ z₁ z₂ h₁ h₂ o₁ _ hr hN
  have hU : ∀ {z : Sp S ⟶ Y₀ TF.X Z}, ⊤ ≤ z ⁻¹ᵁ W → ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1 := fun hz p hp => hC.2.1 (hz hp)
  have hb : z₂ ≫ toBase TF Z = z₁ ≫ toBase TF Z := by
    rw [← spMap_ev _ U.2 (hU h₁), ← spMap_ev _ U.2 (hU h₂)]
    congr 2
    ext r
    exact (ev_appLE z₂ _ hC.2.1 h₂ (hU h₂) r).symm.trans ((hr r).symm.trans (ev_appLE z₁ _ hC.2.1 h₁ (hU h₁) r))
  obtain ⟨-, -, hWk, hLz, hLu, hNz, hN1, hcomb⟩ := hC
  have hNN : ∀ σ i j, ev z₂ W h₂ (N σ i j) = ev z₁ W h₁ (N σ i j) := fun σ i j => by
    rcases lt_trichotomy i j with h | rfl | h
    · exact (hN ⟨σ, ⟨(i, j), h⟩⟩).symm
    · rw [hN1, map_one, map_one]
    · rw [hNz σ i j h, map_zero, map_zero]
  have hvT : ∀ m, IsTanAtG TF.Y.t (z₁ ≫ toBase TF Z) (spMap (dualMap (ev (z₁ ≫ toBase TF Z) U.1 (hU h₁))) ≫ v m) :=
    fun m => GlobalTheory.LieMet.isTan_map _ (spMap_ev _ U.2 (hU h₁)) (hv.1 m)
  have key : ∀ (z : Sp S ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k)
      (x : Sp S ⟶ TF.Y.X) (hxU : ⊤ ≤ x ⁻¹ᵁ U.1) (hT : ∀ m, IsTanAtG TF.Y.t x (spMap (dualMap (ev x U.1 hxU)) ≫ v m))
      (_ : z ≫ toBase TF Z = x) (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = x) σ i,
      initSpan S (TF.X.F.vecAt k _ hk hx σ) i = initSpan S
        (fun a => ∑ j, ev z W hz (N σ a j) • GlobalTheory.LieMet.tanOf (hT (e ⟨σ, j⟩))) i := by
    rintro z hz hk _ hxU hT rfl hx σ
    refine CellMono.initSpan_eq_of_lowerTri (A := (L σ).map (ev z W hz)) (fun i j h => ?_)
      (fun i => (hLu σ i).map (ev z W hz)) fun i => ?_
    · show ev z W hz (L σ i j) = 0
      rw [hLz σ i j h, map_zero]
    · rw [(GlobalTheory.LieMet.isComb_iff (fun j => GlobalTheory.LieMet.tanOf (hT (e ⟨σ, j⟩))) _ _).1 (hcomb S z hz hxU hk hx σ i)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, map_sum, map_mul, Finset.sum_smul, Matrix.map_apply]
      exact Finset.sum_comm
  have hrg : Set.range (z₁ ≫ inc₀ TF.X Z) ⊆ Set.range TF.X.inc := by
    rintro _ ⟨s, rfl⟩; exact (opensRange_inc TF.X).ge (o₁ (Set.mem_univ s))
  obtain ⟨w, hw⟩ : ∃ w, w ≫ TF.X.inc = z₁ ≫ inc₀ TF.X Z := ⟨_, IsOpenImmersion.lift_fac TF.X.inc _ hrg⟩
  letI : Algebra c.F S := ((ev (w ≫ pullback.snd TF.X.π TF.Y.j ≫ pullback.snd _ _) ⊤ le_top).comp (toΓ c.F)).toAlgebra
  have hy : (w ≫ pullback.snd TF.X.π TF.Y.j) ≫ pullback.snd _ _ = spMap (algebraMap c.F S) :=
    (Category.assoc _ _ _).trans (spMap_ev_top _).symm
  have hx₁ : (z₁ ≫ inc₀ TF.X Z) ≫ TF.X.π = z₁ ≫ toBase TF Z := Category.assoc _ _ _
  have hx₂ : (z₂ ≫ inc₀ TF.X Z) ≫ TF.X.π = z₁ ≫ toBase TF Z := (Category.assoc _ _ _).trans hb
  have hxy : z₁ ≫ toBase TF Z = (w ≫ pullback.snd TF.X.π TF.Y.j) ≫ TF.Y.j := by
    rw [← hx₁, ← hw, Category.assoc, Category.assoc, pullback.condition]
  have hk₁ : ⊤ ≤ (z₁ ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := fun p hp => hWk (h₁ hp)
  have hk₂ : ⊤ ≤ (z₂ ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := fun p hp => hWk (h₂ hp)
  rw [← cancel_mono (inc₀ TF.X Z)]
  refine CellMono.eq_of_initSpan_eq TF.X hy hxy hx₁ hx₂ hk₁ hk₂ fun σ i => ?_
  rw [key z₁ h₁ hk₁ _ (hU h₁) hvT rfl hx₁, key z₂ h₂ hk₂ _ (hU h₁) hvT hb hx₂]
  simp only [hNN]

end GlobalTheory.LogPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveSectionsPreimageAffineProperBirational
section
open AlgebraicGeometry CategoryTheory

open TopologicalSpace

namespace GlobalTheory.ZariskiSections

theorem bijective_of_finite_of_fractionRing {A B K : Type} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [CommRing B] [Field K] [Algebra A K] [IsFractionRing A K]
    (φ : A →+* B) (hφ : φ.Finite) (θ : B →+* K) (hθ : Function.Injective θ)
    (h : ∀ a, θ (φ a) = algebraMap A K a) : Function.Bijective φ := by
  refine ⟨fun a a' e => IsFractionRing.injective A K (by rw [← h, ← h, e]), fun b => ?_⟩
  letI := φ.toAlgebra
  have : Module.Finite A B := hφ
  have hb : _root_.IsIntegral A b := Algebra.IsIntegral.isIntegral b
  let θ' : B →ₐ[A] K := { θ with commutes' := fun a => h a }
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hb.map θ')
  exact ⟨a, hθ (by rw [h]; exact ha)⟩

theorem finite_appTop_restrict {Y Z : Scheme.{0}} (π : Y ⟶ Z) [IsProper π] [IsLocallyNoetherian Z]
    {V : Z.Opens} (hV : IsAffineOpen V) : (π ∣_ V).appTop.hom.Finite := by
  let f : (π ⁻¹ᵁ V).toScheme ⟶ Spec (.of Γ(Z, V)) := (π ∣_ V) ≫ hV.isoSpec.hom
  have : IsNoetherianRing Γ(Z, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  letI := GlobalTheory.algebraΓOfHom f
  have h1 := GlobalTheory.ProperFinite.finite_coh_of_isProper f (GlobalTheory.structureModule _) 0
  have h2 : Module.Finite Γ(Z, V) Γ((π ⁻¹ᵁ V).toScheme, ⊤) :=
    Module.Finite.equiv ((GlobalTheory.coh.zeroUnitEquiv _).restrictScalars Γ(Z, V))
  let e := (Scheme.ΓSpecIso (.of Γ(Z, V))).inv ≫ hV.isoSpec.hom.appTop
  haveI : IsIso hV.isoSpec.hom.appTop := by
    first
    | exact (inferInstance : IsIso (Scheme.Γ.map hV.isoSpec.hom.op))
    | exact Scheme.Hom.isIso_app _ ⊤ (by simp)
    | exact Scheme.Hom.isIso_app _ ⊤ (fun x _ => (ConcreteCategory.bijective_of_isIso hV.isoSpec.hom.base).2 x)
  haveI he' : IsIso e := by dsimp only [e]; infer_instance
  have h3 : (e ≫ (π ∣_ V).appTop).hom.Finite := by
    have he : e ≫ (π ∣_ V).appTop = (Scheme.ΓSpecIso (.of Γ(Z, V))).inv ≫ f.appTop := by
      simp only [e, f, Scheme.Hom.comp_appTop, Category.assoc]
    rw [he]
    exact h2
  have h4 : (π ∣_ V).appTop = inv e ≫ (e ≫ (π ∣_ V).appTop) := by rw [IsIso.inv_hom_id_assoc]
  rw [h4, CommRingCat.hom_comp]
  exact RingHom.Finite.comp h3
    (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (inv e)).2)

theorem bijective_appTop_restrict : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsProper π] [IsIntegral Y]
    [IsIntegral Z] [IsLocallyNoetherian Z], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z →
    ∀ U : Z.Opens, (U : Set Z).Nonempty → IsIso (π ∣_ U) → ∀ V : Z.Opens, IsAffineOpen V →
    Function.Bijective (π ∣_ V).appTop := by
  intro Y Z π _ _ _ _ hN U hU hiso V hV
  have hV0 : V.ι ''ᵁ ⊤ = V := Scheme.Opens.ι_image_top V
  have hO : (π ⁻¹ᵁ V).ι ''ᵁ ⊤ = π ⁻¹ᵁ V := Scheme.Opens.ι_image_top _
  by_cases hne : (V : Set Z).Nonempty
  swap
  · have hVb : V = ⊥ := by
      ext x; simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hne ⟨x, hx⟩
    have s1 : Subsingleton Γ(Z, V.ι ''ᵁ ⊤) :=
      CommRingCat.subsingleton_of_isTerminal (Z.sheaf.isTerminalOfEqEmpty (hV0.trans hVb))
    have s2 : Subsingleton Γ(Y, (π ⁻¹ᵁ V).ι ''ᵁ ⊤) :=
      CommRingCat.subsingleton_of_isTerminal (Y.sheaf.isTerminalOfEqEmpty (by
        rw [hO]; ext x; simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
        intro hx; exact hne ⟨_, hx⟩))
    exact ⟨fun a b _ => s1.elim a b, fun b => ⟨0, s2.elim _ _⟩⟩

  set η := genericPoint Z
  have hηU : η ∈ U := ((genericPoint_spec Z).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have hηV : η ∈ V := ((genericPoint_spec Z).mem_open_set_iff V.isOpen).mpr (by simpa using hne)

  obtain ⟨y', hy'⟩ := (π ∣_ U).surjective ⟨η, hηU⟩
  set y : Y := y'.1
  have hy : π y = η := by
    have := congrArg Subtype.val hy'
    simpa [morphismRestrict_base_coe] using this
  haveI : IsIso (π.stalkMap y) :=
    (MorphismProperty.isomorphisms _).arrow_mk_iso_iff (morphismRestrictStalkMap π U y') |>.mp
      (inferInstance : IsIso ((π ∣_ U).stalkMap y'))
  have hyO : y ∈ (π ⁻¹ᵁ V).ι ''ᵁ ⊤ := by rw [hO]; show π y ∈ V; rw [hy]; exact hηV
  haveI : Nonempty (V.ι ''ᵁ ⊤) := ⟨⟨η, hV0.symm ▸ hηV⟩⟩
  haveI := GlobalTheory.IsNormalScheme.of_pred hN
  have hA : IsAffineOpen (V.ι ''ᵁ ⊤) := hV0.symm ▸ hV
  haveI := functionField_isFractionRing_of_isAffineOpen Z _ hA
  haveI := GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hA
  let θ : Γ(Y, (π ⁻¹ᵁ V).ι ''ᵁ ⊤) ⟶ Z.functionField :=
    Y.presheaf.germ _ y hyO ≫ inv (π.stalkMap y) ≫ (Z.presheaf.stalkCongr (Inseparable.of_eq hy)).hom
  have hθ : Function.Injective θ.hom := by
    simp only [θ, CommRingCat.hom_comp, RingHom.coe_comp]
    exact ((ConcreteCategory.bijective_of_isIso _).1.comp (ConcreteCategory.bijective_of_isIso _).1).comp
      (germ_injective_of_isIntegral Y y hyO)
  refine bijective_of_finite_of_fractionRing (A := Γ(Z, V.ι ''ᵁ ⊤)) (K := Z.functionField)
    (π ∣_ V).appTop.hom (finite_appTop_restrict π hV) θ.hom hθ fun a => ?_
  have hle : (π ⁻¹ᵁ V).ι ''ᵁ ⊤ ≤ π ⁻¹ᵁ (V.ι ''ᵁ ⊤) := by rw [hO, hV0]
  have h1 : (π ∣_ V).appTop = π.app (V.ι ''ᵁ ⊤) ≫ Y.presheaf.map (homOfLE hle).op :=
    morphismRestrict_app π V ⊤
  have hyV : π y ∈ V.ι ''ᵁ ⊤ := by rw [hV0, hy]; exact hηV
  have key : (π.app (V.ι ''ᵁ ⊤) ≫ Y.presheaf.map (homOfLE hle).op) ≫ θ =
      Z.germToFunctionField (V.ι ''ᵁ ⊤) := by
    simp only [θ, Category.assoc]
    rw [TopCat.Presheaf.germ_res_assoc, ← Scheme.Hom.germ_stalkMap_assoc π (V.ι ''ᵁ ⊤) y hyV,
      IsIso.hom_inv_id_assoc]
    exact TopCat.Presheaf.germ_stalkSpecializes _ _ (Inseparable.of_eq hy).specializes'
  have := congrArg (fun g => g.hom a) key
  rw [← h1] at this
  exact this

end GlobalTheory.ZariskiSections
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartRestrEqGerm
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.LogKSDiv.Spread'

theorem germ_pt' {X : Scheme.{0}} (B : X.Opens) (y : B.toScheme) {U : X.Opens} (hU : IsAffineOpen U)
    (hy : B.ι y ∈ U) :
    spMap (X.presheaf.germ U (B.ι y) hy ≫ B.ι.stalkMap y).hom ≫ hU.fromSpec = B.toScheme.fromSpecStalk y ≫ B.ι := by
  show Spec.map (X.presheaf.germ U (B.ι y) hy ≫ B.ι.stalkMap y) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, ← IsAffineOpen.fromSpecStalk, hU.fromSpecStalk_eq_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

end GlobalTheory.LogKSDiv.Spread'

set_option autoImplicit false

theorem GlobalTheory.LogKSDiv.chartRestr_eq_germ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι → ∀ r, ρ r = algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r) := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U hU hx ρ hρ r
  have hη : (barComp TF.Y Z).ι (genericPoint (X₀ TF.Y Z)) ∈ U.1 := by
    have h := (genericPoint_spec (X₀ TF.Y Z)).mem_open_set_iff ((barComp TF.Y Z).ι ⁻¹ᵁ U.1).isOpen
    exact h.2 ⟨x, trivial, hx⟩
  set ψ := (TF.Y.X.presheaf.germ U.1 _ hη ≫ (barComp TF.Y Z).ι.stalkMap (genericPoint (X₀ TF.Y Z))).hom with hψ
  have hg := GlobalTheory.LogKSDiv.Spread'.germ_pt' (barComp TF.Y Z) (genericPoint (X₀ TF.Y Z)) U.2 hη
  have hmono : Mono (LogKS.chart U) := by
    unfold LogKS.chart
    have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
    infer_instance
  have e1 : spMap ρ = spMap ψ := by
    rw [← cancel_mono (LogKS.chart U), hρ]
    exact hg.symm
  have e2 : ρ = ψ := by
    have := Spec.map_injective e1
    exact congrArg CommRingCat.Hom.hom this
  rw [e2, hψ, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.germ_stalkMap_apply]
  simp only [GlobalTheory.LogKSDiv.stalkHom, RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
  change _ = ((X₀ TF.Y Z).presheaf.germ _ x hx ≫ (X₀ TF.Y Z).presheaf.stalkSpecializes _).hom _
  erw [TopCat.Presheaf.germ_stalkSpecializes]
end

