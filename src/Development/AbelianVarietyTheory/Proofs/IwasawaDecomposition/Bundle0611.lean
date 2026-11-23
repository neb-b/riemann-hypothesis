module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VecMulVecComm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0262
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0600
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinkowskiWeylOrthantConeIntegralConstraints
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyConjLinearSubstCurvature
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

namespace GlobalTheory.ChernConj

theorem charpolyRev_map_hom {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m : ℕ}
    (M : Matrix (Fin m) (Fin m) R) : M.charpolyRev.map f = (M.map f).charpolyRev := by
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h]

theorem charpolyRev_conj {R : Type} [CommRing R] {m : ℕ} (P Q M : Matrix (Fin m) (Fin m) R)
    (hPQ : P * Q = 1) : (P * M * Q).charpolyRev = M.charpolyRev := by
  have hPQ' : P.map Polynomial.C * Q.map Polynomial.C = 1 := by
    rw [← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Matrix.charpolyRev, Matrix.charpolyRev]
  have e : (1 : Matrix (Fin m) (Fin m) (Polynomial R)) - (Polynomial.X : Polynomial R) • (P * M * Q).map Polynomial.C
      = P.map Polynomial.C * (1 - (Polynomial.X : Polynomial R) • M.map Polynomial.C) * Q.map Polynomial.C := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ', Matrix.mul_smul, Matrix.smul_mul,
      Matrix.map_mul, Matrix.map_mul]
  rw [e, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, hPQ', Matrix.det_one, one_mul]

theorem chernPoly_conj_subst : ∀ {n r : ℕ} (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin r) (Fin r) ℂ) (v v' : ReciprocityTheory.L2DbarEstimates.V n) (J : Matrix (Fin n) (Fin n) ℂ) (S : Matrix (Fin r) (Fin r) ℂ), IsUnit S.det → (∀ a b, curv F v (coordVec a) (coordVec b) = S⁻¹ * (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) • curv F v' (coordVec c) (coordVec d)) * S) → ∀ k, chernPoly F v k = aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)) (chernPoly F v' k) := by
  intro n r F v v' J S hS h k
  set φ : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
    aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)) with hφ
  have hP : (S⁻¹).map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) * S.map C = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hS, Matrix.map_one _ (map_zero _) (map_one _)]
  have hA : curvPoly F v = (S⁻¹).map C * (curvPoly F v').map φ * S.map C := by
    refine Matrix.ext fun i j => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [curvPoly, h, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, aeval_C, aeval_X, hφ, MvPolynomial.algebraMap_eq, Finset.mul_sum, Finset.sum_mul]
    conv_rhs => enter [2, q, 2, p, 2, c]; rw [Finset.sum_comm]
    conv_rhs => enter [2, q, 2, p]; rw [Finset.sum_comm]
    conv_rhs => enter [2, q]; rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    conv_rhs => enter [2, a, 2, q, 2, p, 2, c]; rw [Finset.sum_comm]
    conv_rhs => enter [2, a, 2, q, 2, p]; rw [Finset.sum_comm]
    conv_rhs => enter [2, a, 2, q]; rw [Finset.sum_comm]
    conv_rhs => enter [2, a]; rw [Finset.sum_comm]
    conv_rhs => enter [2, a, 2, b, 2, q]; rw [Finset.sum_comm]
    conv_rhs => enter [2, a, 2, b, 2, q, 2, c]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  have hN : -curvPoly F v = (S⁻¹).map C * (-curvPoly F v').map (φ : MvPolynomial (Fin n × Fin n) ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) * S.map C := by
    rw [hA, Matrix.map_neg, Matrix.mul_neg, Matrix.neg_mul]
    · rfl
    · exact fun a => map_neg φ a
  unfold chernPoly
  rw [hN, charpolyRev_conj _ _ _ hP, ← charpolyRev_map_hom, Polynomial.coeff_map]
  rfl

end GlobalTheory.ChernConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityGrassmannRelationOriginZero
section
noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
open scoped Matrix

namespace GlobalTheory.PointChernRel

open GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointChern GlobalTheory.GrassModel MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField

theorem chernPoly_reindex {n m p : ℕ} (h : p = m) (K : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin p) (Fin p) ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ) :
    chernPoly (fun u => Matrix.reindex (finCongr h) (finCongr h) (K u)) v k = chernPoly K v k := by
  subst h
  simp

theorem curvPoly_model {n r s : ℕ} (f g : Fin r → Fin s → Fin n) :
    curvPoly (fun u : ReciprocityTheory.L2DbarEstimates.V n =>
      (1 - (Matrix.of fun i j => u (f i j)).map (starRingEnd ℂ) * (Matrix.of fun i j => u (g i j))ᵀ)⁻¹) 0 =
      -Matrix.of fun i j => ∑ c, X (g i c, f j c) := by
  refine Matrix.ext fun i j => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [curvPoly, Matrix.of_apply, _root_.GlobalTheory.HermFrame.curv_inv_one_sub_conj_mul_transpose_zero, Matrix.neg_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    coordVec, PiLp.single_apply, apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero, map_neg, map_sum,
    neg_mul, Finset.sum_neg_distrib, Finset.sum_mul, neg_inj]
  have h (x y : Fin n) (c : Fin s) : C (if f j c = y then if g i c = x then (1 : ℂ) else 0 else 0) * X (x, y) =
      if (g i c, f j c) = (x, y) then X (g i c, f j c) else (0 : MvPolynomial (Fin n × Fin n) ℂ) := by
    by_cases h1 : f j c = y <;> by_cases h2 : g i c = x <;> simp [h1, h2]
  simp only [h]
  rw [← Fintype.sum_prod_type' (f := fun x y => ∑ c, if (g i c, f j c) = (x, y) then X (g i c, f j c) else 0), Finset.sum_comm]
  simp

theorem coeff_comp_neg_X' {R : Type} [CommRing R] (p : Polynomial R) (b : ℕ) :
    (p.comp (-Polynomial.X)).coeff b = (-1) ^ b * p.coeff b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [Polynomial.add_comp, hp, hq, mul_add]
  | monomial m a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp, neg_pow,
      ← mul_assoc, show ((-1 : Polynomial R)) ^ m = Polynomial.C ((-1) ^ m) by simp, ← Polynomial.C_mul,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
    split_ifs with h
    · subst h; ring
    · simp

theorem coeff_neg_charpolyRev {R : Type} [CommRing R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (b : ℕ) :
    (-M).charpolyRev.coeff b = (-1) ^ b * M.charpolyRev.coeff b := by
  have h : (-M).charpolyRev = M.charpolyRev.comp (-Polynomial.X) := by
    rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_compRingHom_apply, RingHom.map_det]
    congr 1
    ext a c : 2
    by_cases h : a = c <;> simp [h]
  rw [h, coeff_comp_neg_X']

theorem charpolyRev_map' {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m : ℕ} (M : Matrix (Fin m) (Fin m) R) :
    M.charpolyRev.map f = (M.map f).charpolyRev := by
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h]

theorem relation_top_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (τ : GlobalTheory.AllWt.Psi H) (k : ℕ), 1 ≤ k → ∀ P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ, chernTop (relPoly τ k * P) (fun u => modelGram H Dw (coordOf ix u)) 0 = 0 := by
  intro E _ _ _ H Dw n ix τ k hk P
  set e : Fin Dw.p × Fin Dw.q → Fin n := fun x => ix.symm (τ, x.1, x.2) with he
  have hL : ∀ j, chernPoly (fun u => modelGram H Dw (coordOf ix u) τ.1) 0 j = (blockPoly e).charpolyRev.coeff j := by
    intro j
    have h1 : (fun u => modelGram H Dw (coordOf ix u) τ.1) = fun u =>
        Matrix.reindex (finCongr (mult_of_mem Dw τ.2).symm) (finCongr (mult_of_mem Dw τ.2).symm)
          ((1 - (Matrix.of fun i c => u (e (i, c))).map (starRingEnd ℂ) * (Matrix.of fun i c => u (e (i, c)))ᵀ)⁻¹) := by
      funext u
      simp only [modelGram, dif_pos τ.2]
      rfl
    rw [h1, chernPoly_reindex, chernPoly, curvPoly_model (fun i c => e (i, c)) (fun i c => e (i, c)), neg_neg]
    rfl
  have hc1 : ¬ conjEmb τ.1 (H.rt : E) = H.rt0 := GlobalTheory.AllWt.conj_not_mem τ
  have hc2 : conjEmb (conjEmb τ.1) (H.rt : E) = H.rt0 := by rw [GlobalTheory.AllWt.conjEmb_conjEmb]; exact τ.2
  have hD : ∀ j, chernPoly (fun u => modelGram H Dw (coordOf ix u) (conjEmb τ.1)) 0 j =
      (blockPolyBar e).charpolyRev.coeff j := by
    intro j
    have hτ : (⟨conjEmb (conjEmb τ.1), hc2⟩ : GlobalTheory.AllWt.Psi H) = τ := Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)
    have h1 : (fun u => modelGram H Dw (coordOf ix u) (conjEmb τ.1)) = fun u =>
        Matrix.reindex (finCongr (mult_of_not_mem Dw hc1).symm) (finCongr (mult_of_not_mem Dw hc1).symm)
          ((1 - (Matrix.of fun b i => u (e (i, b))).map (starRingEnd ℂ) * (Matrix.of fun b i => u (e (i, b)))ᵀ)⁻¹) := by
      funext u
      simp only [modelGram, dif_neg hc1, dif_pos hc2, hτ]
      rfl
    rw [h1, chernPoly_reindex, chernPoly, curvPoly_model (fun b i => e (i, b)) (fun b i => e (i, b)), neg_neg]
    rfl
  have hrel : aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => modelGram H Dw (coordOf ix u) x.1) 0 x.2) (relPoly τ k) =
      ((blockPoly e).charpolyRev * (-blockPolyBar e).charpolyRev).coeff k := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [relPoly, map_sum, map_mul, aeval_X, aeval_C, hL, hD, Polynomial.coeff_mul, coeff_neg_charpolyRev]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [map_pow, map_neg, map_one]
    ring
  have hzero : toEven n (((blockPoly e).charpolyRev * (-blockPolyBar e).charpolyRev).coeff k) = 0 := by
    have h2 := GlobalTheory.T.charpolyRev_mul_eq_one_of_trace_pow_add_eq_zero (K := ℂ) _ _ (GlobalTheory.T.trace_pow_grassmannBlockCurvature_supertrace_zero e)
    have e1 : ((blockPoly e).map (toEven n)).charpolyRev = (blockPoly e).charpolyRev.map (toEven n).toRingHom :=
      (charpolyRev_map' _ _).symm
    have e2 : ((-blockPolyBar e).map (toEven n)).charpolyRev =
        (-blockPolyBar e).charpolyRev.map (toEven n).toRingHom := (charpolyRev_map' _ _).symm
    rw [e1, e2, ← Polynomial.map_mul] at h2
    have h3 := congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f k) h2
    simp only [Polynomial.coeff_map, Polynomial.coeff_one, if_neg (show k ≠ 0 by omega)] at h3
    exact h3
  rw [chernTop, map_mul, hrel, _root_.GlobalTheory.GrassModel.TopRead.topCoeff_eq_topBig, map_mul, hzero, zero_mul]
  simp

end GlobalTheory.PointChernRel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConcreteSplitPrimeAutomorphicDataDivisionLattice
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Top.Bl.WitTr
open Formalism.MainNotions.G Formalism.UG Formalism.L2.Forms Formalism.L2.G
attribute [local instance] Formalism.BasicNotions.factResChar

section Gen

variable {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) {X : Formalism.L2.Herm.Herm0 D}


set_option maxHeartbeats 2000000 in
def cmpInS (I : Cmp.CmpIn D X) : Cmp.CmpIn (setDiv D N h) (DivTr.herm0S N h X) := { I with }


set_option maxHeartbeats 2000000 in
theorem cmpHyp0P_setDiv {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : Cmp.CmpIn D X} (H : CmpHyp0P T Gt I) :
    CmpHyp0P (D := setDiv D N h) (fun u => DivTr.forms0S N h (T u)) (gatTr N h Gt) (cmpInS N h I) :=
  ⟨H.ex, H.evInj, H.ptEx, H.ptAll, H.chi, H.latM⟩

theorem stdB_setDiv {B : GL (Fin D.R.k) D.host.E} (hB : Cmp.StdB D B) : Cmp.StdB (setDiv D N h) B := hB


set_option maxHeartbeats 2000000 in
theorem cmpHyp_setDiv {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : Cmp.CmpIn D X} (H : Cmp.CmpHyp T Gt I) :
    Cmp.CmpHyp (D := setDiv D N h) (fun u => DivTr.forms0S N h (T u)) (gatTr N h Gt) (cmpInS N h I) :=
  ⟨H.ex, H.uniq, H.pos, H.chi, H.li, H.latM⟩


set_option maxHeartbeats 2000000 in
theorem latCmpC_setDiv {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : Cmp.CmpIn D X} (H : Cmp.CmpHyp T Gt I) :
    cmpTr N h (Cmp.latCmpC T Gt I H) =
      Cmp.latCmpC (D := setDiv D N h) (fun u => DivTr.forms0S N h (T u)) (gatTr N h Gt) (cmpInS N h I) (cmpHyp_setDiv N h H) := rfl


set_option maxHeartbeats 2000000 in
theorem sigma_setDiv {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : Cmp.CmpIn D X} (H : Cmp.CmpHyp T Gt I)
    (H0 : Formalism.L2.Herm.Herm0 D) :
    (⟨setDiv D N h, gatTr N h Gt, cmpTr N h (Cmp.latCmpC T Gt I H), DivTr.herm0S N h H0, fun u => DivTr.forms0S N h (T u)⟩ :
      Σ D : D7, GatTies D × LatCmp D × Formalism.L2.Herm.Herm0 D × ∀ u, Forms0 D u) =
    ⟨setDiv D N h, gatTr N h Gt,
      Cmp.latCmpC (D := setDiv D N h) (fun u => DivTr.forms0S N h (T u)) (gatTr N h Gt) (cmpInS N h I) (cmpHyp_setDiv N h H),
      DivTr.herm0S N h H0, fun u => DivTr.forms0S N h (T u)⟩ := by
  rw [latCmpC_setDiv]

end Gen

attribute [local instance_reducible] tauRec hP frobSet lamRec packC locPackC recG gatTiesG extRec embRec cmpInC hermitianLevelZeroOfRecursion levTieG gatRecP_lev gatRec_lev gatRec_pos
  DivTr.herm0S DivTr.forms0S DivTr.atTTS cmpInS LocPack.posOK


set_option maxHeartbeats 1600000 in
theorem isRecG_setDiv : ∀ (sc : Scale) (D : D7) (Gt : GatTies D) (c : LatCmp D) (H : Formalism.L2.Herm.Herm0 D)
    (F : ∀ u, Formalism.L2.Forms.Forms0 D u) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ),
    IsRecG sc D Gt c H F → IsRecG sc (setDiv D N h) (gatTr N h Gt) (cmpTr N h c) (DivTr.herm0S N h H)
      (fun u => DivTr.forms0S N h (F u)) := by
  intro sc D Gt c H F N h hR
  obtain ⟨D0, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, eq⟩ := hR
  cases eq
  refine IsRecG.intro (setDiv D0 N h) Lc I ?a1 ?a2 ?a3 ?a4 ?a5 B ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 ?a13
  case a1 => with_reducible_and_instances exact ψ
  case a2 => with_reducible_and_instances exact hd
  case a3 => with_reducible_and_instances exact DivTr.herm0S N h H0
  case a4 => with_reducible_and_instances exact hL
  case a5 => with_reducible_and_instances exact fun u => DivTr.forms0S N h (T u)
  case a6 => with_reducible_and_instances exact stdB_setDiv N h hBs
  case a7 => with_reducible_and_instances exact hB
  case a8 => with_reducible_and_instances exact iK
  case a9 => with_reducible_and_instances exact lam
  case a10 => with_reducible_and_instances exact hK
  case a11 => with_reducible_and_instances exact hPos
  case a12 => with_reducible_and_instances exact cmpHyp0P_setDiv N h CH
  case a13 =>
    with_reducible_and_instances refine Eq.trans (sigma_setDiv N h _ H0) ?_
    with_reducible_and_instances exact Eq.refl _

end GlobalTheory.Mem.Top.Bl.WitTr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeMatchRaysOfLinearIndependentIntForms
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

namespace ConeMatch

variable {V : Type} [AddCommGroup V] [Module ℝ V]

theorem coef_eq {n : ℕ} {P : Fin n → V} (hP : LinearIndependent ℝ P) {a b : Fin n → ℝ}
    (h : ∑ i, a i • P i = ∑ i, b i • P i) : a = b := by
  have := Fintype.linearIndependent_iff.1 hP (a - b) (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self])
  funext i; exact sub_eq_zero.1 (this i)

theorem exists_pos_of_sum_eq_one {n : ℕ} (f : Fin n → ℝ) (h : ∑ i, f i = 1) : ∃ i, 0 < f i := by
  by_contra hc
  push_neg at hc
  have : ∑ i, f i ≤ 0 := Finset.sum_nonpos fun i _ => hc i
  linarith

theorem match_vec {k m : ℕ} (P : Fin k → V) (Q : Fin m → V) (hP : LinearIndependent ℝ P)
    (hQ : LinearIndependent ℝ Q) (t : Fin k → ℝ) (c : Fin m → ℝ) (ht : ∀ i, 0 < t i) (hc : ∀ j, 0 ≤ c j)
    (hsum : ∑ i, t i • P i = ∑ j, c j • Q j)
    (hPQ : ∀ i, ∃ a : Fin m → ℝ, (∀ j, 0 ≤ a j) ∧ P i = ∑ j, a j • Q j)
    (hQP : ∀ j, 0 < c j → ∃ b : Fin k → ℝ, (∀ l, 0 ≤ b l) ∧ Q j = ∑ l, b l • P l) :
    (∀ i, ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ P i = d • Q j) ∧
    (∀ j, 0 < c j → ∃ i, ∃ d : ℝ, 0 < d ∧ P i = d • Q j ∧ c j = t i * d) := by
  choose D hD0 hD using hPQ
  have hQP' : ∀ j, ∃ b : Fin k → ℝ, (∀ l, 0 ≤ b l) ∧ (0 < c j → Q j = ∑ l, b l • P l) := fun j => by
    by_cases h : 0 < c j
    · obtain ⟨b, hb, e⟩ := hQP j h
      exact ⟨b, hb, fun _ => e⟩
    · exact ⟨0, fun _ => le_rfl, fun h' => absurd h' h⟩
  choose E hE0 hE using hQP'

  have hcD : ∀ j, c j = ∑ i, t i * D i j := by
    have h1 : ∑ j, c j • Q j = ∑ j, (∑ i, t i * D i j) • Q j := by
      rw [← hsum]
      simp only [hD, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    exact congrFun (coef_eq hQ h1)
  have hDz : ∀ i j, ¬ 0 < c j → D i j = 0 := fun i j h => by
    have h0 : c j = 0 := le_antisymm (not_lt.1 h) (hc j)
    rw [hcD j] at h0
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (ht i).le (hD0 i j)).1 h0 i
      (Finset.mem_univ _)
    exact (mul_eq_zero.1 this).resolve_left (ht i).ne'
  have hDQ : ∀ i j, D i j • Q j = D i j • ∑ l, E j l • P l := fun i j => by
    by_cases h : 0 < c j
    · rw [← hE j h]
    · simp [hDz i j h]
  have hDE : ∀ i l, ∑ j, D i j * E j l = if i = l then 1 else 0 := by
    intro i l
    have h1 : ∑ l, (if i = l then (1 : ℝ) else 0) • P l = ∑ l, (∑ j, D i j * E j l) • P l := by
      rw [show ∑ l, (if i = l then (1 : ℝ) else 0) • P l = P i by simp [ite_smul]]
      conv_lhs => rw [hD i]
      simp only [hDQ, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    exact (congrFun (coef_eq hP h1) l).symm
  have hED : ∀ j, 0 < c j → ∀ j', ∑ l, E j l * D l j' = if j = j' then 1 else 0 := by
    intro j hj j'
    have h1 : ∑ j', (if j = j' then (1 : ℝ) else 0) • Q j' = ∑ j', (∑ l, E j l * D l j') • Q j' := by
      rw [show ∑ j', (if j = j' then (1 : ℝ) else 0) • Q j' = Q j by simp [ite_smul]]
      conv_lhs => rw [hE j hj]
      simp only [hD, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    exact (congrFun (coef_eq hQ h1) j').symm
  have single : ∀ i j, 0 < D i j * E j i → 0 < c j ∧ 0 < D i j ∧ P i = D i j • Q j := by
    intro i j hpos
    have hcj : 0 < c j := by
      by_contra h
      rw [hDz i j h, zero_mul] at hpos
      exact lt_irrefl _ hpos
    have hEne : E j i ≠ 0 := fun h => by rw [h, mul_zero] at hpos; exact lt_irrefl _ hpos
    have hDpos : 0 < D i j := lt_of_le_of_ne (hD0 i j) fun h => by rw [← h, zero_mul] at hpos; exact lt_irrefl _ hpos
    have hoff : ∀ j', j' ≠ j → D i j' = 0 := fun j' hj' => by
      have hle : E j i * D i j' ≤ ∑ l, E j l * D l j' :=
        Finset.single_le_sum (f := fun l => E j l * D l j') (fun l _ => mul_nonneg (hE0 j l) (hD0 l j'))
          (Finset.mem_univ i)
      rw [hED j hcj j', if_neg (Ne.symm hj')] at hle
      have h0 : E j i * D i j' = 0 := le_antisymm hle (mul_nonneg (hE0 j i) (hD0 i j'))
      exact (mul_eq_zero.1 h0).resolve_left hEne
    refine ⟨hcj, hDpos, ?_⟩
    rw [hD i, Finset.sum_eq_single j (fun j' _ hj' => by rw [hoff j' hj', zero_smul])
      (fun h => absurd (Finset.mem_univ j) h)]
  refine ⟨fun i => ?_, fun j hj => ?_⟩
  · obtain ⟨j, hj⟩ := exists_pos_of_sum_eq_one _ ((hDE i i).trans (if_pos rfl))
    obtain ⟨hcj, hd, e⟩ := single i j hj
    exact ⟨j, hcj, D i j, hd, e⟩
  · obtain ⟨l, hl⟩ := exists_pos_of_sum_eq_one _ ((hED j hj j).trans (if_pos rfl))
    have hl' : 0 < D l j * E j l := by rw [mul_comm]; exact hl
    obtain ⟨-, hd, e⟩ := single l j hl'
    have hEne : E j l ≠ 0 := fun h => by rw [h, zero_mul] at hl; exact lt_irrefl _ hl
    have hoff : ∀ i, i ≠ l → D i j = 0 := fun i hi => by
      have hle : D i j * E j l ≤ ∑ j'', D i j'' * E j'' l :=
        Finset.single_le_sum (f := fun j'' => D i j'' * E j'' l) (fun j'' _ => mul_nonneg (hD0 i j'') (hE0 j'' l))
          (Finset.mem_univ j)
      rw [hDE i l, if_neg hi] at hle
      have h0 : D i j * E j l = 0 := le_antisymm hle (mul_nonneg (hD0 i j) (hE0 j l))
      exact (mul_eq_zero.1 h0).resolve_right hEne
    refine ⟨l, D l j, hd, e, ?_⟩
    rw [hcD j, Finset.sum_eq_single l (fun i _ hi => by rw [hoff i hi, mul_zero])
      (fun h => absurd (Finset.mem_univ l) h)]

end ConeMatch

section Forms

variable {X : Type} [AddCommGroup X]

theorem linearIndependent_toReal {n : ℕ} {p : Fin n → LinearMap.BilinForm ℤ X} (hp : LinearIndependent ℤ p) :
    LinearIndependent ℝ fun i => toReal (p i) := by
  refine Fintype.linearIndependent_iff.2 fun g hg => ?_
  have hind : ∀ (d : Fin 0 → ℤ) (c : Fin n → ℤ), ∑ j, c j • p j = ∑ k, d k • (Fin.elim0 k : LinearMap.BilinForm ℤ X) →
      c = 0 := fun d c h => by
    funext i
    exact Fintype.linearIndependent_iff.1 hp c (by simpa using h) i
  have := eq_zero_of_toReal_rel (u := p) (v := (Fin.elim0 : Fin 0 → LinearMap.BilinForm ℤ X)) hind
    (r := g) (s := 0) (by simpa using hg)
  exact fun i => congrFun this i

theorem cone_match_rays {X : Type} [AddCommGroup X] {k m : ℕ} (p : Fin k → LinearMap.BilinForm ℤ X)
    (δ : Fin m → LinearMap.BilinForm ℤ X) :
    LinearIndependent ℤ p → LinearIndependent ℤ δ →
    ∀ (t : Fin k → ℝ) (c : Fin m → ℝ), (∀ i, 0 < t i) → (∀ j, 0 ≤ c j) →
      ∑ i, t i • toReal (p i) = ∑ j, c j • toReal (δ j) →
      (∀ i, InRCone δ (p i)) → (∀ j, 0 < c j → InRCone p (δ j)) →
      (∀ i, ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j)) ∧
      (∀ j, 0 < c j → ∃ i, ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j) ∧ c j = t i * d) :=
  fun hp hδ t c ht hc hsum hpδ hδp =>
    ConeMatch.match_vec (fun i => toReal (p i)) (fun j => toReal (δ j)) (linearIndependent_toReal hp)
      (linearIndependent_toReal hδ) t c ht hc hsum hpδ hδp

end Forms

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfPrimitiveBalancedFormSameRealRay
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.SmoothEnd

theorem eq_of_isPrim_of_toReal_eq_smul : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] (x y : LinearMap.BilinForm ℤ X)
    (hx : x ∈ balForms bar X) (hy : y ∈ balForms bar X), IsPrim bar (⟨x, hx⟩ : balForms bar X) →
    IsPrim bar (⟨y, hy⟩ : balForms bar X) → ∀ b : ℝ, 0 < b → toReal x = b • toReal y → x = y := by
  intro O _ bar X _ _ x y hx hy px py b hb h
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact not_isPrim_zero (bar := bar) py
  obtain ⟨a, c, hac⟩ : ∃ a c, y a c ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy0 (LinearMap.ext₂ hc)
  have hR : ∀ u v, (x u v : ℝ) = b * (y u v : ℝ) := fun u v => by
    have := LinearMap.congr_fun₂ h u v
    simpa [toReal_apply] using this
  have hacR : (y a c : ℝ) ≠ 0 := by exact_mod_cast hac
  have hxac : x a c ≠ 0 := by
    have : (x a c : ℝ) ≠ 0 := by rw [hR]; exact mul_ne_zero hb.ne' hacR
    exact_mod_cast this
  have habs : |(x a c : ℝ)| = b * |(y a c : ℝ)| := by
    rw [hR, abs_mul, abs_of_pos hb]
  apply eq_of_isPrim hx hy px py (k := (y a c).natAbs) (n := (x a c).natAbs)
    (Int.natAbs_pos.2 hac) (Int.natAbs_pos.2 hxac)
  apply LinearMap.ext₂
  intro u v
  simp only [LinearMap.smul_apply, smul_eq_mul, Int.natCast_natAbs]
  have e : |(y a c : ℝ)| * (x u v : ℝ) = |(x a c : ℝ)| * (y u v : ℝ) := by
    rw [hR u v, habs]; ring
  exact_mod_cast e

end GlobalTheory.PolFan.SmoothEnd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCellOfContactSetIntInequalitiesStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cell_of_contactSet_intInequalities : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (ψ : InvFun O) (K : ℕ) (Λ : (X × X) →₀ ℤ) (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (A : Set (Fin m → ℤ)), A.Finite → 0 < K → (∀ i y z, u i y z = u i z y) → (∀ i y, 0 ≤ u i y y) → (∀ (β : LinearMap.BilinForm ℤ X) (t : Fin m → ℝ), toReal β = ∑ i, t i • toReal (u i) → ∀ i, ∃ z : ℤ, t i = z) → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (K : ℝ) * ψ.evalZ β ≤ evalW Λ (toReal β)) → (∀ B ∈ psdCone (bar := bar) (X := X), (K : ℝ) * evalR ψ B = evalW Λ B → ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i) ∧ (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) ∧ B = ∑ i, t i • toReal (u i)) → (∀ t : Fin m → ℝ, (∀ i, 0 ≤ t i) → (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) → ∑ i, t i • toReal (u i) ∈ realForms bar X → (K : ℝ) * evalR ψ (∑ i, t i • toReal (u i)) = evalW Λ (∑ i, t i • toReal (u i))) → ∃ (s : ℕ) (γ : Fin s → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ ∀ B ∈ psdCone (bar := bar) (X := X), (K : ℝ) * evalR ψ B = evalW Λ B → B ∈ rcone γ := by
  first | exact @GlobalTheory.PolCell.exists_isCell_of_contact | exact GlobalTheory.PolCell.exists_isCell_of_contact | (intros; apply GlobalTheory.PolCell.exists_isCell_of_contact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonDenominatorStrictnessSmoothFanStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_denominator_strictness_smooth_fan : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (φ : InvFun ℤ), IsPolFanOn (id : ℤ → ℤ) φ X → ∃ N : ℕ, 0 < N ∧ ∀ B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X), ∃ (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ), IsCone (id : ℤ → ℤ) φ u ∧ StrictWith (id : ℤ → ℤ) φ N (linW w) u ∧ B ∈ rcone u := by
  first | exact @GlobalTheory.PolCell.exists_common_den | exact GlobalTheory.PolCell.exists_common_den | (intros; apply GlobalTheory.PolCell.exists_common_den <;> assumption)
end

