module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Formalism.HarderNarasimhan.StatementPl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1265
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1280
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1257
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedSectionChartCoords
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSKerRes

section Dictionary

variable {Y : Scheme.{0}} {M N : LB Y} {O W : Y.Opens}

theorem coord_resM (h : W ≤ O) (s : Γ(LB.toMod M, O)) (i : M.ι) :
    LB.coord (Twist.resM (LB.toMod M) h s) i = resG Y (inf_le_inf_right _ h) (LB.coord s i) :=
  LB.coord_map h s i

theorem le_tens (O : Y.Opens) (q : (tens M N).ι) : O ⊓ (tens M N).U q ≤ O ⊓ N.U q.2 ⊓ M.U q.1 :=
  fun _ hy => ⟨⟨hy.1, hy.2.2⟩, hy.2.1⟩

def ofTwistFun (s : Γ(twist (LB.toMod M) N, O)) : Γ(LB.toMod (tens M N), O) :=
  LB.mkSec (fun q => resG Y (le_tens O q) (LB.coord (Twist.coord s q.2) q.1)) fun p q => by
    have h₁ : O ⊓ (tens M N).U p ⊓ (tens M N).U q ≤ O ⊓ N.U p.2 := fun _ hy => ⟨hy.1.1, hy.1.2.2⟩
    have h₂ : O ⊓ (tens M N).U p ⊓ (tens M N).U q ≤ O ⊓ N.U q.2 := fun _ hy => ⟨hy.1.1, hy.2.2⟩
    have h₃ : O ⊓ (tens M N).U p ⊓ (tens M N).U q ≤ M.U p.1 := fun _ hy => hy.1.2.1
    have h₄ : O ⊓ (tens M N).U p ⊓ (tens M N).U q ≤ M.U q.1 := fun _ hy => hy.2.1
    have e₁ := congrArg (fun r => resG Y (le_inf le_rfl h₄) (LB.coord r q.1))
      (Twist.coord_rel s p.2 q.2 h₁ h₂ (le_inf (h₁.trans inf_le_right) (h₂.trans inf_le_right)))
    have e₂ := LB.coord_rel (Twist.coord s p.2) p.1 q.1 (le_inf h₁ h₃) (le_inf h₁ h₄) (le_inf h₃ h₄)
    simp only [coord_resM, LB.coord_smul, map_mul, LB.resG_resG] at e₁
    simp only [LB.resG_resG]
    refine e₂.trans ?_
    rw [e₁, ← mul_assoc]
    refine congrArg (· * _) ?_
    exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (LB.resG_resG _ _ _) (LB.resG_resG _ _ _))).symm

theorem coord_ofTwistFun (s : Γ(twist (LB.toMod M) N, O)) (q : (tens M N).ι) :
    LB.coord (ofTwistFun s) q = resG Y (le_tens O q) (LB.coord (Twist.coord s q.2) q.1) := rfl

def ofTwist : Γ(twist (LB.toMod M) N, O) →+ Γ(LB.toMod (tens M N), O) where
  toFun := ofTwistFun
  map_zero' := LB.sec_ext fun q => by
    rw [coord_ofTwistFun, Twist.coord_zero, LB.coord_zero, map_zero, LB.coord_zero]
  map_add' s t := LB.sec_ext fun q => by
    rw [LB.coord_add, coord_ofTwistFun, coord_ofTwistFun, coord_ofTwistFun, Twist.coord_add, LB.coord_add, map_add (f := _)]

theorem tens_le (O : Y.Opens) (i : M.ι) (j : N.ι) : O ⊓ N.U j ⊓ M.U i ≤ O ⊓ (tens M N).U (i, j) :=
  fun _ hy => ⟨hy.1.1, hy.2, hy.1.2⟩

theorem tens_rel (f : Γ(LB.toMod (tens M N), O)) (i i' : M.ι) (j j' : N.ι) (h : W ≤ O ⊓ (tens M N).U (i, j))
    (h' : W ≤ O ⊓ (tens M N).U (i', j')) (hM : W ≤ M.U i ⊓ M.U i') (hN : W ≤ N.U j ⊓ N.U j') :
    resG Y h (LB.coord f (i, j)) = resG Y hM (M.g i i' : Γ(Y, M.U i ⊓ M.U i')) *
      resG Y hN (N.g j j' : Γ(Y, N.U j ⊓ N.U j')) * resG Y h' (LB.coord f (i', j')) := by
  refine (LB.coord_rel f (i, j) (i', j') h h' (le_inf (h.trans inf_le_right) (h'.trans inf_le_right))).trans ?_
  refine congrArg (· * _) ?_
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (LB.resG_resG _ _ _) (LB.resG_resG _ _ _))

theorem surjective_ofTwist (hM : M.IsLB) (hN : N.IsLB) :
    Function.Surjective (ofTwist : Γ(twist (LB.toMod M) N, O) → Γ(LB.toMod (tens M N), O)) := fun f => by
  let a : ∀ j : N.ι, Γ(LB.toMod M, O ⊓ N.U j) := fun j =>
    LB.mkSec (fun i => resG Y (tens_le O i j) (LB.coord f (i, j))) fun i i' => by
      simp only [LB.resG_resG]
      refine (tens_rel f i i' j j _ (by exact fun _ hy => ⟨hy.1.1.1, hy.2, hy.1.1.2⟩)
        (by exact fun _ hy => ⟨hy.1.2, hy.2⟩) (by exact fun _ hy => ⟨hy.1.1.2, hy.1.1.2⟩)).trans ?_
      exact congrArg (· * _) ((congrArg (_ * ·) (LB.resG_g_self hN _ _)).trans (mul_one _))
  have ha : ∀ j i, LB.coord (a j) i = resG Y (tens_le O i j) (LB.coord f (i, j)) := fun _ _ => rfl
  refine ⟨Twist.mkSec a fun j j' => LB.sec_ext fun i => ?_, LB.sec_ext fun q => ?_⟩
  · simp only [coord_resM, LB.coord_smul, ha, LB.resG_resG]
    refine (tens_rel f i i j j' _ (by exact fun _ hy => ⟨hy.1.1.1, hy.2, hy.1.2⟩)
      (by exact fun _ hy => ⟨hy.2, hy.2⟩) (by exact fun _ hy => ⟨hy.1.1.2, hy.1.2⟩)).trans ?_
    exact congrArg (· * _) ((congrArg (· * _) (LB.resG_g_self hM _ _)).trans (one_mul _))
  · refine (coord_ofTwistFun _ q).trans ?_
    exact (LB.resG_resG (tens_le O q.1 q.2) (le_tens O q) (LB.coord f q)).trans (LB.resG_self _ _)

variable {k : Type} [CommRing k] (p : Y ⟶ Sp k) {L : LB Y} {n l : ℤ}

def toH0 : Γ(twistZ (LB.toMod M) L n, O) →+ Vanishing.H0 p (tw M L n) O := ofTwist

theorem restricted_section_chart_coords (s : Γ(twistZ (LB.toMod M) L n, O)) (i : M.ι) (j : L.ι)
    (h : W ≤ O ⊓ (tw M L n).U (twIdx n i j)) (h' : W ≤ O ⊓ L.U j ⊓ M.U i) :
    resG Y h ((toH0 p s).loc (twIdx n i j)) = resG Y h' (LB.coord (Twist.zcoord s j) i) := by
  rw [Twist.zcoord, coord_resM, LB.resG_resG]
  exact LB.resG_resG _ _ _

theorem germ_of_global_section (s : Γ(twistZ (LB.toMod M) L n, O)) (i : M.ι) (j : L.ι) (y : Y) (hy : y ∈ O)
    (hi : y ∈ M.U i) (hj : y ∈ L.U j) :
    H0.germ (twIdx n i j) y hy (mem_tw_U.2 ⟨hi, hj⟩) (toH0 p s) =
      ger y (memInf (memInf hy hj) hi) (LB.coord (Twist.zcoord s j) i) := by
  have h : O ⊓ L.U j ⊓ M.U i ≤ O ⊓ (tw M L n).U (twIdx n i j) := fun _ hz => ⟨hz.1.1, mem_tw_U.2 ⟨hz.2, hz.1.2⟩⟩
  have e := congrArg (ger y (memInf (memInf hy hj) hi)) (restricted_section_chart_coords p s i j h le_rfl)
  rwa [ger_resG, ger_resG] at e

theorem global_section_mul (hM : M.IsLB) (hL : L.IsLB) (w : L.Sec) (h : n + 1 = l) (s : Γ(twistZ (LB.toMod M) L n, O)) :
    toH0 p ((Twist.mulSecOfEq (LB.toMod M) (Twist.zofSec w) h).app O s) = mulSec hM hL w h (toH0 p s) :=
  tw_ext hM hL fun i j y hy hi hj => by
    rw [germ_mulSec _ _ _ _ _ _ _ _ _ hi hj, germ_of_global_section p _ i j y hy hi hj, germ_of_global_section p _ i j y hy hi hj,
      Twist.zcoord_mulSecOfEq_app, LB.coord_smul, map_mul, ger_resG, ger_resG, Twist.zfun_zofSec]

theorem exists_local (hM : M.IsLB) (hL : L.IsLB) {d : ℕ} (t : Fin d → L.Sec) (h : n + 1 = l)
    (s : Γ(twistZ (LB.toMod M) L l, ⊤)) (hs : VanishesTo (cutIdeal hL t) 1 (toH0 p s)) (y : Y) :
    ∃ (W : Y.Opens) (_ : y ∈ W) (m : Fin d → Γ(twistZ (LB.toMod M) L n, W)),
      (twistZ (LB.toMod M) L l).presheaf.map (homOfLE le_top).op s =
        ∑ i, (Twist.mulSecOfEq (LB.toMod M) (Twist.zofSec (t i)) h).app W (m i) := by
  obtain ⟨i, hi⟩ := exists_chart hM y
  obtain ⟨j, hj⟩ := exists_chart hL y
  obtain ⟨V, hV, e⟩ := exists_affine (memInf hi hj)
  have hVi : V.1 ≤ M.U i := e.trans inf_le_left
  have hVj : V.1 ≤ L.U j := e.trans inf_le_right
  have h₁ : V.1 ≤ ⊤ ⊓ (tw M L l).U (twIdx l i j) := fun _ hz => ⟨trivial, mem_tw_U.2 ⟨hVi hz, hVj hz⟩⟩
  have h₂ := vanishesTo_iff_affine.1 hs V _ h₁
  rw [pow_one, ideal_cutIdeal hL t V j hVj, restricted_section_chart_coords p s i j h₁ (le_inf (le_inf le_top hVj) hVi)] at h₂
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 h₂
  refine ⟨V.1, hV, fun a => (Twist.zchartEquiv hL n j hVj).symm ((LB.chartEquiv hM i hVi).symm (c a)), ?_⟩
  refine (Twist.zchartEquiv hL l j hVj).injective ((LB.chartEquiv hM i hVi).injective ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Twist.zchartEquiv_mulSecOfEq_app, map_smul, LinearEquiv.apply_symm_apply, Twist.zfun_zofSec,
    smul_eq_mul]
  rw [LB.chartEquiv_apply, Twist.zchartEquiv_apply]
  refine Eq.trans ?_ (hc.symm.trans (Finset.sum_congr rfl fun a _ => mul_comm _ _))
  rw [coord_resM]
  erw [Twist.zcoord_resM]
  rw [coord_resM, LB.resG_resG, LB.resG_resG]

end Dictionary

section Main

variable {K : Type} [Field K] [NumberField K] (G : Geo K)

theorem ger_comb_sum {ι : Type} [Fintype ι] (a : ι → K) (u : ι → Fin G.N → K) (j : G.L.ι) (y : G.Y) (hj : y ∈ G.L.U j) :
    ger y hj ((G.comb (∑ i, a i • u i)).f j) = ∑ i, H0.const G.str y (a i) * ger y hj ((G.comb (u i)).f j) := by
  have key (v : Fin G.N → K) : H0.ofSec G.str ⊤ (G.comb v) =
      Fintype.linearCombination K (fun c => H0.ofSec G.str ⊤ (G.b c)) v := G.ofSec_comb ⊤ v
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← H0.germ_ofSec (p := G.str) j y (TopologicalSpace.Opens.mem_top y) hj, key, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, H0.germ_smul, ← key, H0.germ_ofSec]

theorem vanishesTo_of_isUnit (s : Fin G.D → Fin G.N → K) (g : Matrix (Fin G.D) (Fin G.D) K) (hg : IsUnit g.det)
    {B : LB G.Y} {O : G.Y.Opens} {f : Vanishing.H0 G.str B O} (hf : VanishesTo (G.ideal s) 1 f) :
    VanishesTo (G.ideal fun i => ∑ j, g i j • s j) 1 f := fun y _ hy c hc => by
  have h := vanishesTo_iff_forall.1 hf y hy c hc
  obtain ⟨j, hj⟩ := exists_chart G.isLB y
  rw [pow_one, stalkId_cutIdeal G.isLB _ j y hj] at h ⊢
  refine Ideal.span_le.2 (Set.range_subset_iff.2 fun a => ?_) h
  have e : s a = ∑ i, g⁻¹ a i • ∑ j, g i j • s j := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.nonsing_inv_mul g hg, Matrix.one_apply, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  change ger y hj ((G.comb (s a)).f j) ∈ Ideal.span _
  rw [e, ger_comb_sum]
  exact sum_mem fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

end Main

theorem exists_global {k : Type} [Field k] {Y : Scheme.{0}} [Algebra k Γ(Y, ⊤)] (hY : IsProjOver (GlobalTheory.strHom k (X := Y)))
    (p : Y ⟶ Sp k) {M L : LB Y} (hM : M.IsLB) (hL : L.IsLB) {d : ℕ} (t : Fin d → L.Sec) {n l : ℤ} (h : n + 1 = l)
    (hreg : RegSeq hL (LB.toMod M) (List.ofFn t)) (hvan : VanishFrom L (LB.toMod M) 0) (hd : (d : ℤ) ≤ n + 1)
    (f : Vanishing.H0 p (tw M L l) ⊤) (hf : VanishesTo (cutIdeal hL t) 1 f) :
    ∃ μ : Fin d → Vanishing.H0 p (tw M L n) ⊤, f = ∑ i, mulSec hM hL (t i) h (μ i) := by
  subst h
  obtain ⟨σ, rfl⟩ : ∃ σ : Γ(twistZ (LB.toMod M) L (n + 1), ⊤), toH0 p σ = f :=
    surjective_ofTwist hM (Twist.isLB_lbZPow hL _) f
  have := (VB.isVB_toMod hM).isFiniteQC
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_global_combination_of_local_regular_ideal k Y hY L hL d t (LB.toMod M) 0 n hreg hvan ((zero_add _).trans_le hd) σ
    (exists_local p hM hL t rfl σ hf)
  refine ⟨fun i => toH0 p (m i), (congrArg (toH0 p) hm).trans ?_⟩
  exact (map_sum (toH0 p) _ _).trans (Finset.sum_congr rfl fun i _ => global_section_mul p hM hL _ rfl (m i))

theorem kerRes : Quoted → KerRes := by
  intro Q K _ _ G hnef hbig s hs l hl f hf
  obtain ⟨⟨f, rfl⟩, hv⟩ := mem_Fil.1 hf
  have hB : (tens G.K.bundle G.LA).IsLB := isLB_tens G.K.isLB G.isLBA
  obtain ⟨g, hg, hreg⟩ := _root_.GlobalTheory.RegBasis.exists_regular_basis K G s hs _ hB
  have hv' := vanishesTo_of_isUnit G s g hg ((vanishesTo_restr_iff hs.inU le_top).1 hv)
  have hproj : IsProjOver (GlobalTheory.strHom K (X := G.Y)) := by
    rw [GlobalTheory.strHom_eq (f := G.str) fun _ => rfl]
    exact G.geom.alg.variety.proj
  obtain ⟨μ, e⟩ := exists_global hproj G.str hB G.isLB _ (Nat.cast_succ l).symm hreg (_root_.GlobalTheory.HSCore.VanishNumberField.vanishFrom_adj Q K G hnef hbig)
    (by exact_mod_cast hl) f hv'
  refine ⟨fun j => H0.restr le_top (∑ i, g i j • μ i), fun j => ⟨_, rfl⟩, ?_⟩
  have e' (i) : H0.restr (le_top : G.U ≤ ⊤) (mulSec hB G.isLB (G.comb (∑ j, g i j • s j)) (Nat.cast_succ l).symm (μ i)) =
      G.mulW l (∑ j, g i j • s j) (H0.restr le_top (μ i)) := by
    rw [G.mulW_apply, mulSec, mulSec, ProdChart.restr_mul, H0.restr_ofSec]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [e', map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_comm

end GlobalTheory.HSKerRes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzCoordinatesInInfiniteFamily
section
open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SchwartzCoord

variable {D : D7}

theorem repr_map {R : Type} [CommRing R] [Algebra D.host.F R] (π : AF D.host.F →ₐ[D.host.F] R) {d : ℕ}
    (ε : Module.Basis (Fin d) D.host.F D.host.E) (z : AE D) (k : Fin d) :
    π ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr z k) =
      (Algebra.TensorProduct.basis R ε).repr (Algebra.TensorProduct.map π (AlgHom.id D.host.F D.host.E) z) k := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.map_tmul, Finsupp.mapRange_apply]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

end GlobalTheory.SchwartzCoord

namespace GlobalTheory.SchwartzCoord
variable {D : D7}
theorem finPart_eq (z : AE D) : finPart D z = Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) z := rfl
theorem infPart_eq (z : AE D) : infPart D z = Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z := rfl
theorem snd_eq (a : AF D.host.F) : a.2 = sndA D.host.F a := rfl
theorem fin_coord {d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) (z : AE D) (k : Fin d) :
    ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr z k).2 =
      (Algebra.TensorProduct.basis (Af D.host.F) ε).repr (finPart D z) k := by
  rw [snd_eq, finPart_eq]
  exact repr_map (sndA D.host.F) ε z k
end GlobalTheory.SchwartzCoord

namespace GlobalTheory.SchwartzCoord

variable {D : D7}

def finCoord {m n d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) :
    (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ≃ₜ (Fin m × Fin n × Fin d → Af D.host.F) := by
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  let b := Algebra.TensorProduct.basis (Af D.host.F) ε
  exact
  { toFun := fun y p => b.equivFun (y p.1 p.2.1) p.2.2
    invFun := fun c i j => b.equivFun.symm fun k => c (i, j, k)
    left_inv := fun y => by
      funext i j
      simp only
      conv_rhs => rw [← b.equivFun.symm_apply_apply (y i j)]
    right_inv := fun c => by
      funext p
      simp only [LinearEquiv.apply_symm_apply]
    continuous_toFun := continuous_pi fun p =>
      ((continuous_apply p.2.2).comp (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)).comp
        ((continuous_apply p.2.1).comp (continuous_apply p.1))
    continuous_invFun := continuous_pi fun i => continuous_pi fun j =>
      (IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap).comp
        (continuous_pi fun k => continuous_apply (i, j, k)) }

theorem finCoord_apply {m n d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E)
    (y : Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) (p : Fin m × Fin n × Fin d) :
    finCoord ε y p = (Algebra.TensorProduct.basis (Af D.host.F) ε).repr (y p.1 p.2.1) p.2.2 := by
  simp [finCoord]

end GlobalTheory.SchwartzCoord

namespace GlobalTheory.SchwartzCoord

variable {D : D7}

theorem continuous_mixed (F : Type) [Field F] [NumberField F] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  have : (InfiniteAdeleRing.ringEquiv_mixedSpace F : InfiniteAdeleRing F → mixedEmbedding.mixedSpace F) =
      fun x => ((fun v : {w : InfinitePlace F // InfinitePlace.IsReal w} =>
          InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
        (fun v : {w : InfinitePlace F // InfinitePlace.IsComplex w} =>
          InfinitePlace.Completion.extensionEmbedding v.1 (x v))) := by
    funext x; exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x
  rw [this]
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      (continuous_apply _)

def realCoord (σ : (D.what₂.Tau → ℂ) →+ AE D) {m n d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) :
    (D.what₂.Tau → Fin m → Fin n → ℂ) →+ (Fin m × Fin n × Fin d → mixedEmbedding.mixedSpace D.host.F) where
  toFun c p := InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
    (fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (σ fun τ => c τ p.1 p.2.1) p.2.2))
  map_zero' := by
    funext p
    have : (σ fun τ => (0 : D.what₂.Tau → Fin m → Fin n → ℂ) τ p.1 p.2.1) = 0 := σ.map_zero
    show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (fstA D.host.F
      ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (σ fun τ => (0 : D.what₂.Tau → Fin m → Fin n → ℂ) τ p.1 p.2.1)
        p.2.2)) = 0
    rw [this, map_zero, Finsupp.zero_apply, map_zero, map_zero]
  map_add' c c' := by
    funext p
    have : (σ fun τ => (c + c') τ p.1 p.2.1) = σ (fun τ => c τ p.1 p.2.1) + σ (fun τ => c' τ p.1 p.2.1) :=
      σ.map_add _ _
    show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (fstA D.host.F
      ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (σ fun τ => (c + c') τ p.1 p.2.1) p.2.2)) = _
    rw [this, map_add (f := _), Finsupp.add_apply, map_add (f := _), map_add (f := _)]
    rfl

theorem continuous_realCoord {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : Continuous σ) {m n d : ℕ}
    (ε : Module.Basis (Fin d) D.host.F D.host.E) : Continuous (realCoord σ (m := m) (n := n) ε) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  refine continuous_pi fun p => (continuous_mixed D.host.F).comp (continuous_fst.comp ?_)
  exact ((continuous_apply p.2.2).comp (IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis (AF D.host.F) ε).equivFun.toLinearMap)).comp
    (hσ.comp (continuous_pi fun τ => (continuous_apply p.2.1).comp ((continuous_apply p.1).comp (continuous_apply τ))))

end GlobalTheory.SchwartzCoord

namespace GlobalTheory.SchwartzCoord

variable {D : D7}

theorem finCoord_coord {m n d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) (x : Mx D m n) :
    (fun p => (coord ε x p).2) = finCoord ε (fun i j => finPart D (x i j)) := by
  funext p
  rw [finCoord_apply]
  exact fin_coord ε (x p.1 p.2.1) p.2.2

theorem inf_coord {d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) (z : AE D) (k : Fin d) :
    ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr z k).1 =
      (Algebra.TensorProduct.basis (Ainf D.host.F) ε).repr (infPart D z) k := by
  rw [infPart_eq]
  exact repr_map (fstA D.host.F) ε z k

theorem realCoord_compAt {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ)
    {s : (Af D.host.F ⊗[D.host.F] D.host.E) →+ AE D} (hsf : ∀ a, finPart D (s a) = a) (hsi : ∀ a, infPart D (s a) = 0)
    {m n d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) (x : Mx D m n) :
    (fun p => InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (coord ε x p).1) =
      realCoord σ ε (fun τ i j => compAt θ τ x i j) := by
  funext p
  have hx : x p.1 p.2.1 = s (finPart D (x p.1 p.2.1)) + σ (fun τ => compAt θ τ x p.1 p.2.1) :=
    congrFun (congrFun (GlobalTheory.SchwartzBruhatTensor.decomp hσ hsf hsi x) p.1) p.2.1
  have h0 : fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (s (finPart D (x p.1 p.2.1))) p.2.2) = 0 :=
    (inf_coord ε _ _).trans (by rw [hsi, map_zero, Finsupp.zero_apply])
  show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
      (fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (x p.1 p.2.1) p.2.2)) =
    InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
      (fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (σ fun τ => compAt θ τ x p.1 p.2.1) p.2.2))
  conv_lhs => rw [hx]
  rw [map_add (f := _), Finsupp.add_apply, map_add (fstA D.host.F), h0, zero_add]

end GlobalTheory.SchwartzCoord

namespace GlobalTheory.SchwartzCoord

variable {D : D7}

theorem injective_realCoord {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) {m n d : ℕ}
    (ε : Module.Basis (Fin d) D.host.F D.host.E) : Function.Injective (realCoord σ (m := m) (n := n) ε) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  funext τ i j
  have h0 : infPart D (σ fun τ => c τ i j) = 0 := by
    apply (Algebra.TensorProduct.basis (Ainf D.host.F) ε).repr.injective
    ext k
    rw [map_zero, Finsupp.zero_apply]
    have e : InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
        (fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (σ fun τ => c τ i j) k)) = 0 :=
      congrFun hc (i, j, k)
    have e2 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).injective).1 e
    rw [← e2, repr_map (fstA D.host.F) ε]
    rfl
  have h1 := hσ.comp (fun τ => c τ i j) τ
  rw [h0, map_zero] at h1
  exact h1.symm

theorem mem_schwartzA_comp_coord : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n d : ℕ)
    (ε : Module.Basis (Fin d) D.host.F D.host.E) (φ : WeilM.schA D.host.F (Fin m × Fin n × Fin d)),
    φ.1 ∘ coord ε ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ m n := by
  intro D θ hθ m n d ε φ
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨s, -, hsf, hsi⟩ := GlobalTheory.SchwartzBruhatTensor.exists_finSection D
  obtain ⟨M, hM⟩ : ∃ M : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] (Fin m × Fin n × Fin d → mixedEmbedding.mixedSpace D.host.F),
      ⇑M = ⇑(realCoord σ ε) := ⟨(realCoord σ ε).toRealLinearMap (continuous_realCoord hσ.cont ε), rfl⟩
  have hMi : Function.Injective M.toLinearMap := by
    intro a b h
    have h' : M a = M b := h
    rw [hM] at h'
    exact injective_realCoord hσ ε h'
  obtain ⟨K, -, hK⟩ := (LinearMap.injective_iff_antilipschitz _).1 hMi
  have hbound : ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖M x‖) ^ k := ⟨1, K, fun x => by
    have h := hK.le_mul_dist x 0
    rw [dist_zero_right, map_zero, dist_zero_right] at h
    have hK0 : (0 : ℝ) ≤ K := K.coe_nonneg
    calc ‖x‖ ≤ K * ‖M x‖ := h
      _ ≤ K * (1 + ‖M x‖) ^ 1 := by rw [pow_one]; exact mul_le_mul_of_nonneg_left (by linarith) hK0⟩
  obtain ⟨φ, hφ⟩ := φ
  induction hφ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    let f' : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ := SchwartzMap.compCLM ℂ M.hasTemperateGrowth hbound f
    have hf' : ∀ c, f' c = f (M c) := fun c => rfl
    let g' : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := g ∘ finCoord ε
    have hg' : g' ∈ WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
      ⟨hg.1.comp_continuous (finCoord ε).continuous, hg.2.comp_homeomorph _⟩
    have heq : WeilM.pureA D.host.F f g ∘ coord ε =
        fun x => f' (fun τ i j => compAt θ τ x i j) * g' (fun i j => finPart D (x i j)) := by
      funext x
      rw [hf']
      show f (fun p => InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (coord ε x p).1) * g (fun p => (coord ε x p).2) =
        f (M (fun τ i j => compAt θ τ x i j)) * g (finCoord ε (fun i j => finPart D (x i j)))
      rw [realCoord_compAt hσ hsf hsi ε x, finCoord_coord ε x, ← hM]
    rw [heq]
    exact Submodule.subset_span ⟨f', g', hg', rfl⟩
  | zero =>
    have e : (0 : (Fin m × Fin n × Fin d → AdeleRing (𝓞 D.host.F) D.host.F) → ℂ) ∘ coord ε = 0 := rfl
    rw [e]
    exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 =>
    have e : (Φ + Ψ) ∘ coord ε = Φ ∘ coord ε + Ψ ∘ coord ε := rfl
    rw [e]
    exact Submodule.add_mem _ h1 h2
  | smul a Φ _ h =>
    have e : (a • Φ) ∘ coord ε = a • (Φ ∘ coord ε) := rfl
    rw [e]
    exact Submodule.smul_mem _ a h

end GlobalTheory.SchwartzCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedAdelicUnitaryPointOfLocalMatrixStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supported_adelic_unitary_point_of_local_matrix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F)) (n : ℕ) (X : Spc F E n) (L : Type) [Field L]
    (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) →
      ∀ (g : UA σ X.J) (A : Matrix (Fin n) (Fin n) L),
        mat g = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + A.map ι → g ∈ UAt σ X (evFin F v) := by
  first | exact @GlobalTheory.InertLocFrame.uAt_of_local | exact GlobalTheory.InertLocFrame.uAt_of_local | (intros; apply GlobalTheory.InertLocFrame.uAt_of_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedMatrixIffFrameCoordinatesOfInertStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supported_matrix_iff_frame_coordinates_of_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F)) (n d : ℕ) (L : Type) [Field L] (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Function.Injective ι → (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      ∀ (PV : GL (Fin n) L) (PW : GL (Fin d) L) (z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
        At (evFin F v) z ↔ ∃ x, GlobalTheory.InertLocFrame.xm ι PV PW x = z := by
  first | exact @GlobalTheory.InertLocFrame.xm_bij_at | exact GlobalTheory.InertLocFrame.xm_bij_at | (intros; apply GlobalTheory.InertLocFrame.xm_bij_at <;> assumption)
end

