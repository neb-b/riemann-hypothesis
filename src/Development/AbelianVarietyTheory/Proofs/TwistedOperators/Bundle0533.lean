module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToDoubledFirstFactorBigCellInertPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0521
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0528
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicStripSetMeasurableReadOnRealPart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0456
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0517
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0520
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AntidiagonalUnipotentConjSiegelSquareSplit
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitDblGenLeft

open GlobalTheory.InertDbl GlobalTheory.InertBigCell

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sq_smul_eq {n : Type} {v : Pl (F := F)} {c : AE F E} (hc : ∀ z : AE F E, At (evFin F v) z → c * c * z = z)
    {X : Matrix n n (AE F E)} (hX : At (evFin F v) X) : (c * c) • X = X := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul]
  exact hc _ fun u hu => by simpa using congrFun (congrFun (hX u hu) i) j

theorem inlD_mem_closure_of_split {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {d : ℕ} (W : Spc F E d) (v : Pl (F := F))
    (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (k : UA σ W.J) (hk : k ∈ GlobalTheory.InertSph.KAt σ W v) :
    inlD σ W k ∈ Subgroup.closure (ParD σ W v ∪ NabD σ W v) := by
  obtain ⟨c, hcσ, hcat, hcsq, hclat⟩ := GlobalTheory.T.exists_antiInvariant_sign_adele_splitPlace F E σ B hB v hv
  obtain ⟨p, hp, hpm⟩ := GlobalTheory.T.exists_parD_matD_eq_diagonalFixingDoublingMatrix F E σ d W v h2 c hcσ hcat (hclat d W)
  obtain ⟨n, hn, hnm⟩ := GlobalTheory.T.nablaUnipotent_mem_integralDoubledUnipotent F E σ d W v h2 c hcσ (hclat d W) k hk
  have e1 : mat k * mat k⁻¹ = 1 := by
    show mat (k * k⁻¹) = 1
    rw [mul_inv_cancel]; rfl
  have e2 : mat k⁻¹ * mat k = 1 := by
    show mat (k⁻¹ * k) = 1
    rw [inv_mul_cancel]; rfl
  have hsq : (c * c) • (mat k - 1) = mat k - 1 := sq_smul_eq hcsq hk.1
  have hid := GlobalTheory.T.diagonalFixingDoublingMatrix_mul_fromBlocks_mul_diagCols F E d c (mat k) (mat k⁻¹) e1 e2 hsq
  have ht := GlobalTheory.T.splitDoublingTMatrix_mul_inverse_eq_one F E d c (mat k) (mat k⁻¹) e1 hsq
  let t : GL (Fin d) (AE F E) := ⟨GlobalTheory.SplitDblGen.tMat c (mat k), GlobalTheory.SplitDblGen.tMat c (mat k⁻¹), ht, mul_eq_one_comm.1 ht⟩
  have hq : n⁻¹ * (p * inlD σ W k) ∈ ParD σ W v := by
    refine ⟨KAtD_mul (KAtD_inv hn.1) (KAtD_mul hp.1 (inlD_mem hk)), t, ?_⟩
    have en : matD n⁻¹ * matD n = 1 := (n.1).inv_val
    show matD n⁻¹ * (matD p * matD (inlD σ W k)) * diagCols (Fin d) = diagCols (Fin d) * GlobalTheory.SplitDblGen.tMat c (mat k)
    rw [matD_inlD, hpm]
    rw [← hnm] at hid
    erw [Matrix.mul_assoc, hid, ← Matrix.mul_assoc, ← Matrix.mul_assoc, en, Matrix.one_mul]
    rfl
  have e : inlD σ W k = p⁻¹ * (n * (n⁻¹ * (p * inlD σ W k))) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inl hp)))
    (Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr hn)) (Subgroup.subset_closure (Or.inl hq)))

theorem inlD_mem_closure_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, GlobalTheory.InertDbl.inlD σ G.V' k ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.V' v ∪ GlobalTheory.InertDbl.NabD σ G.V' v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv _ h2 k hk
  exact inlD_mem_closure_of_split hT.base G.V' v hv h2 k hk

end GlobalTheory.SplitDblGenLeft
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselCharacterRealPlaceUnipotentEqTrace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesselCoords

open GlobalTheory.BesselChar

section Alg

variable {R : Type} [CommRing R] {n r : ℕ}

theorem cols_resid {L : Matrix (Fin r) (Fin n) R} {E : Matrix (Fin n) (Fin r) R} (hL : L * E = 1)
    {U : Matrix (Fin n) (Fin n) R} (h : ∀ i : Fin r, ∃ a : Fin r → R, (U - 1) *ᵥ (fun k => E k i) = E *ᵥ a) :
    (U - 1) * E - E * (L * (U - 1) * E) = 0 := by
  choose a ha using h
  have e1 : (U - 1) * E = E * (Matrix.of a)ᵀ := by
    ext k i
    exact congr_fun (ha i) k
  rw [Matrix.mul_assoc, e1, ← Matrix.mul_assoc L, hL, Matrix.one_mul, sub_self]

theorem vec_resid {L : Matrix (Fin r) (Fin n) R} {E : Matrix (Fin n) (Fin r) R} (hL : L * E = 1)
    {U : Matrix (Fin n) (Fin n) R} {z : Fin n → R} {a : Fin r → R} (h : (U - 1) *ᵥ z = E *ᵥ a) :
    (U - 1) *ᵥ z - E *ᵥ ((L * (U - 1)) *ᵥ z) = 0 := by
  have e2 : L *ᵥ (E *ᵥ a) = a := by rw [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec, h, e2, sub_self]

theorem cols_resid_map {S : Type} [CommRing S] (f : R →+* S) (L : Matrix (Fin r) (Fin n) R)
    (E : Matrix (Fin n) (Fin r) R) (U : Matrix (Fin n) (Fin n) R) :
    ((U - 1) * E - E * (L * (U - 1) * E)).map f =
      (U.map f - 1) * E.map f - E.map f * (L.map f * (U.map f - 1) * E.map f) := by
  have hm : (U - 1).map f = U.map f - 1 := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hm]

theorem vec_resid_map {S : Type} [CommRing S] (f : R →+* S) (L : Matrix (Fin r) (Fin n) R)
    (E : Matrix (Fin n) (Fin r) R) (U : Matrix (Fin n) (Fin n) R) (z : Fin n → R) :
    (fun i => f ((((U - 1) *ᵥ z - E *ᵥ ((L * (U - 1)) *ᵥ z) : Fin n → R)) i)) =
      (U.map f - 1) *ᵥ (fun i => f (z i)) - E.map f *ᵥ ((L.map f * (U.map f - 1)) *ᵥ (fun i => f (z i))) := by
  have hm : (U - 1).map f = U.map f - 1 := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
  rw [← hm, ← Matrix.map_mul, mulVec_map, mulVec_map, mulVec_map]
  funext i
  simp only [Pi.sub_apply, map_sub]

theorem cols_of_resid {M : Matrix (Fin n) (Fin n) R} {E : Matrix (Fin n) (Fin r) R} {T : Matrix (Fin r) (Fin r) R}
    (h : (M - 1) * E - E * T = 0) : M * E = E + E * T := by
  rw [sub_eq_zero, Matrix.sub_mul, Matrix.one_mul, sub_eq_iff_eq_add'] at h
  exact h

theorem vec_of_resid {M : Matrix (Fin n) (Fin n) R} {E : Matrix (Fin n) (Fin r) R} {z : Fin n → R} {b : Fin r → R}
    (h : (M - 1) *ᵥ z - E *ᵥ b = 0) : M *ᵥ z = z + E *ᵥ b := by
  rw [sub_eq_zero, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_iff_eq_add'] at h
  exact h

theorem coordSum_one (c : Fin r → R) (L : Matrix (Fin r) (Fin n) R) (E : Matrix (Fin n) (Fin r) R) (z : Fin n → R) :
    coordSum c L E z 1 = 0 := by
  simp [coordSum, superSum]

end Alg

theorem coordSum_flag {n r : ℕ} (c : Fin r → ℂ) {L : Matrix (Fin r) (Fin n) ℂ} {e : Matrix (Fin n) (Fin r) ℂ}
    (hL : L * e = 1) (z : Fin n → ℂ) (u : Matrix (Fin n) (Fin n) ℂ) (a : Fin r → Fin r → ℂ)
    (ha : ∀ j : Fin r, (u - 1) *ᵥ GlobalTheory.RealBessel.flagVec e z j.succ = e *ᵥ a j) :
    coordSum c L e z u = ∑ j, c j * a j j := by
  have key : ∀ j : Fin r, (L * (u - 1)) *ᵥ GlobalTheory.RealBessel.flagVec e z j.succ = a j := by
    intro j
    rw [← Matrix.mulVec_mulVec, ha j, Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]
  have hT : ∀ i j : Fin r, j.1 = i.1 + 1 → (L * (u - 1) * e : Matrix (Fin r) (Fin r) ℂ) i j = a i i := by
    intro i j hij
    have hf : GlobalTheory.RealBessel.flagVec e z i.succ = fun k => e k j := by
      have : i.succ = Fin.castSucc j := Fin.ext (by simp [hij])
      rw [this, GlobalTheory.RealBessel.flagVec, Fin.snoc_castSucc]
    have := congr_fun (key i) i
    rw [hf] at this
    rw [← this, Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct]
  have hb : ∀ i : Fin r, i.1 + 1 = r → ((L * (u - 1)) *ᵥ z) i = a i i := by
    intro i hi
    have hf : GlobalTheory.RealBessel.flagVec e z i.succ = z := by
      have : i.succ = Fin.last r := Fin.ext (by simp [hi])
      rw [this, GlobalTheory.RealBessel.flagVec, Fin.snoc_last]
    have := congr_fun (key i) i
    rwa [hf] at this
  have hrow : ∀ i : Fin r, (∑ j : Fin r, if j.1 = i.1 + 1 then c i * (L * (u - 1) * e : Matrix (Fin r) (Fin r) ℂ) i j else 0) =
      if i.1 + 1 < r then c i * a i i else 0 := by
    intro i
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨i.1 + 1, h⟩]
      · rw [if_pos rfl, hT i ⟨i.1 + 1, h⟩ rfl]
      · intro j _ hj
        rw [if_neg]
        intro h'
        exact hj (Fin.ext h')
      · intro h'; exact absurd (Finset.mem_univ _) h'
    · refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg]
      intro h'
      have := j.2
      omega
  unfold coordSum superSum
  simp only [hrow]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := i.2
  by_cases h : i.1 + 1 < r
  · rw [if_pos h, if_neg (by omega), add_zero]
  · rw [if_neg h, if_pos (by omega), zero_add, hb i (by omega)]

variable {D : D7}

theorem mat_eq_zero (θ : InfFam D) (hθ : IsInfFam θ) {m k : ℕ} (Y : Matrix (Fin m) (Fin k) (AE D))
    (h1 : Y.map (finPart D) = 0) (h2 : ∀ ρ, Y.map ((θ ρ).comp (infPart D)) = 0) : Y = 0 := by
  ext i j
  refine (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.2 _ (fun ρ => ?_) ?_
  · exact congr_fun (congr_fun (h2 ρ) i) j
  · exact congr_fun (congr_fun h1 i) j

theorem vec_eq_zero (θ : InfFam D) (hθ : IsInfFam θ) {m : ℕ} (Y : Fin m → AE D)
    (h1 : (fun i => finPart D (Y i)) = 0) (h2 : ∀ ρ, (fun i => (θ ρ).comp (infPart D) (Y i)) = 0) : Y = 0 := by
  funext i
  refine (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.2 _ (fun ρ => ?_) ?_
  · exact congr_fun (h2 ρ) i
  · exact congr_fun h1 i

theorem comp_incA (θ : InfFam D) (hθ : IsInfFam θ) (ρ : D.what₂.Tau) :
    ((θ ρ).comp (infPart D)).comp (incA D) = tauE D ρ :=
  RingHom.ext fun x => (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.1 x ρ

end GlobalTheory.BesselCoords

namespace GlobalTheory.BesselCoords

open GlobalTheory.BesselChar


set_option maxHeartbeats 1000000 in
theorem besChar_atTau_coords : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesDat A B ι) (τ : D.what₂.Tau) (u : Matrix (Fin B.rank) (Fin B.rank) ℂ),
  u ∈ GlobalTheory.RealBessel.unipRad (gramAt D B τ) (d.e.map (tauE D τ)) →
  ∀ a : Fin d.ρ → Fin d.ρ → ℂ, (∀ j : Fin d.ρ, (u - 1) *ᵥ GlobalTheory.RealBessel.flagVec (d.e.map (tauE D τ)) (fun k => tauE D τ (d.z k)) j.succ = d.e.map (tauE D τ) *ᵥ a j) →
  ∃ t : AE D, finPart D t = 0 ∧ (∀ ρ, ρ ≠ τ → θ ρ (infPart D t) = 0) ∧ θ τ (infPart D t) = ∑ j, tauE D τ (d.c j) * a j j ∧
    besChar ψ d (atTau θ B τ u) = ψ (Algebra.trace (AF D.host.F) (AE D) t) := by
  intro D θ hθ ψ A B ι d τ u hu a ha
  obtain ⟨hgC, hgτ, hgρ⟩ := GlobalTheory.PointAtPlaceHom.atTau_spec hθ B τ hu.1
  obtain ⟨L, hL⟩ := exists_leftInv d.e d.e_iso.1
  have hfin : (Formalism.L2.Theta.mt B (atTau θ B τ u)).map (finPart D) = 1 := GlobalTheory.StripBorel.mt_map_fin hgC
  have hinf : ∀ ρ, (Formalism.L2.Theta.mt B (atTau θ B τ u)).map ((θ ρ).comp (infPart D)) =
      infMat D.sp.cm.sig B.gram (θ ρ) (atTau θ B τ u) := fun ρ => rfl
  have hmap : ∀ ρ {m k : ℕ} (X : Matrix (Fin m) (Fin k) D.host.E),
      (X.map (incA D)).map ((θ ρ).comp (infPart D)) = X.map (tauE D ρ) := by
    intro ρ m k X
    rw [Matrix.map_map, ← RingHom.coe_comp, comp_incA θ hθ ρ]
  have hvec : ∀ ρ {m : ℕ} (x : Fin m → D.host.E),
      (fun i => ((θ ρ).comp (infPart D)) (incA D (x i))) = fun i => tauE D ρ (x i) := by
    intro ρ m x
    funext i
    exact (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.1 (x i) ρ
  have hL' := map_leftInv (incA D) hL
  have hLτ := map_leftInv (tauE D τ) hL

  have hperp : ((d.e.map (tauE D τ))ᴴ * gramAt D B τ) *ᵥ (fun k => tauE D τ (d.z k)) = 0 := by
    have h0 := mulVec_map (tauE D τ) (perpMat B d.e) d.z
    rw [d.z_perpE] at h0
    have hm : (perpMat B d.e).map (tauE D τ) = (d.e.map (tauE D τ))ᴴ * gramAt D B τ := by
      rw [perpMat, Matrix.map_mul]
      refine congrArg₂ (· * ·) ?_ rfl
      ext i j
      simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
      exact GlobalTheory.Mem.Isom.tauE_sig D τ _
    rw [hm] at h0
    rw [h0]
    funext i
    exact map_zero _
  have h1 : Formalism.L2.Theta.mt B (atTau θ B τ u) * d.e.map (incA D) = d.e.map (incA D) +
      d.e.map (incA D) * (L.map (incA D) * (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1) * d.e.map (incA D)) := by
    have hK : (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1) * d.e.map (incA D) - d.e.map (incA D) *
        (L.map (incA D) * (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1) * d.e.map (incA D)) = 0 := by
      refine mat_eq_zero θ hθ _ ?_ ?_
      · rw [cols_resid_map, hfin]; simp
      · intro ρ
        rw [cols_resid_map, hinf, hmap, hmap]
        by_cases hρ : ρ = τ
        · subst hρ
          rw [hgτ]
          exact cols_resid (map_leftInv (tauE D ρ) hL) fun i => by
            obtain ⟨a, -, h⟩ := hu.2.1 i
            exact ⟨a, h⟩
        · rw [hgρ ρ hρ]; simp
    exact cols_of_resid hK
  have h2 : Formalism.L2.Theta.mt B (atTau θ B τ u) *ᵥ ratV d.z = ratV d.z +
      d.e.map (incA D) *ᵥ ((L.map (incA D) * (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1)) *ᵥ ratV d.z) := by
    have hK : (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1) *ᵥ ratV d.z - d.e.map (incA D) *ᵥ
        ((L.map (incA D) * (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1)) *ᵥ ratV d.z) = 0 := by
      refine vec_eq_zero θ hθ _ ?_ ?_
      · refine (vec_resid_map (finPart D) _ _ _ _).trans ?_
        rw [hfin]
        simp only [sub_self, Matrix.zero_mulVec, Matrix.mul_zero, Matrix.mulVec_zero]
      · intro ρ
        refine (vec_resid_map ((θ ρ).comp (infPart D)) _ _ _ _).trans ?_
        rw [hinf, hmap, hmap]
        have hz : (fun i => ((θ ρ).comp (infPart D)) (ratV d.z i)) = fun i => tauE D ρ (d.z i) := hvec ρ d.z
        rw [hz]
        by_cases hρ : ρ = τ
        · subst hρ
          rw [hgτ]
          obtain ⟨b, hb⟩ := hu.2.2 _ hperp
          exact vec_resid (map_leftInv (tauE D ρ) hL) hb
        · rw [hgρ ρ hρ]
          simp only [sub_self, Matrix.zero_mulVec, Matrix.mul_zero, Matrix.mulVec_zero]
    exact vec_of_resid hK
  refine ⟨coordSum (fun i => incA D (d.c i)) (L.map (incA D)) (d.e.map (incA D)) (ratV d.z)
    (Formalism.L2.Theta.mt B (atTau θ B τ u)), ?_, ?_, ?_, ?_⟩
  · rw [← coordSum_map, hfin, coordSum_one]
  · intro ρ hρ
    show ((θ ρ).comp (infPart D)) _ = 0
    rw [← coordSum_map, hinf, hgρ ρ hρ, coordSum_one]
  · show ((θ τ).comp (infPart D)) _ = _
    rw [← coordSum_map, hinf, hgτ, hmap, hmap, hvec τ d.c]
    have hz : (fun i => ((θ τ).comp (infPart D)) (ratV d.z i)) = fun i => tauE D τ (d.z i) := hvec τ d.z
    rw [hz]
    exact coordSum_flag _ hLτ _ u a ha
  · exact besChar_eq ψ d _ _ _ h1 h2

end GlobalTheory.BesselCoords
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentreEigenThetaFunctionFiniteSumFockPolynomials
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CenFockGen

open GlobalTheory.SeeSaw

theorem isFockVacAt_heisO_fin {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D}
    (hθ : IsInfFam θ) {S T : HSp D} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) (hv : IsFockVacAt (heisO ψ S T) θ τ J f)
    {u : WO S T} (hu : u.map (infPart D) = 0) : IsFockVacAt (heisO ψ S T) θ τ J (heisO ψ S T u f) := by
  have h := GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hψ.1 hθ f hf τ J hv Unit Finset.univ (fun _ => u) (fun _ => 1)
    (fun _ _ => hu)
  simpa using h

theorem heisO_pureTensorO_fin {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D}
    (hθ : IsInfFam θ) {S T : HSp D} (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {u : WO S T} (hu : u.map (infPart D) = 0)
    {x : WO S T → ℂ} (hx : IsThetaFunO ψ S T x) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    heisO ψ S T u (pureTensorO ψ θ S T sS sT BS BT x P) = pureTensorO ψ θ S T sS sT BS BT (heisO ψ S T u x) P := by
  classical
  have h := GlobalTheory.FiniteHeisComb.sum_heisO_pureTensorO D ψ θ S T hψ hθ sS BS sT BT (Finsupp.single u 1)
    (fun v hv => by
      rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hv
      rw [hv]; exact hu) x hx P
  simpa [Finsupp.sum_single_index] using h

theorem comb_smul' {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : WO S T →₀ ℂ) (r : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (r • f) = r • comb ψ S T c f := by
  funext w
  simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem theta_comb {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {c : WO S T →₀ ℂ}
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (comb ψ S T c f) :=
  Finset.sum_induction _ (IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add) GlobalTheory.OrientedHeis.theta_zero
    fun u _ => GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf u)

theorem exists_defData {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : GlobalTheory.Grid.Node D} {νS νT : ℕ}
    {PS PT : D.what₂.Tau → SPar} (hS : S.Is νS 0 PS) (hT : T.Is νT 0 PT) {a : GlobalTheory.Grid.ArrT S T}
    {χS χT : (AE D)ˣ →* Circle} (ha : a.Is ψ θ false χS χT) :
    ∃ (x : DefSp S.V) (y : DefSp T.V) (k : KerDat S.V T.V), x.Is ∧ y.Is ∧ k.Is ψ θ x y ∧ x.s = cart S.M ∧
      y.s = cart T.M ∧ x.B = onb S.M ∧ y.B = onb T.M ∧ k.om = a.ω ∧ k.vac = a.vac := by
  obtain ⟨vS⟩ := GlobalTheory.Unf.VolExist.nonempty_vol S.V
  obtain ⟨vT⟩ := GlobalTheory.Unf.VolExist.nonempty_vol T.V
  have pS : S.V.IsPosDef := fun τ => by rw [hS.sig τ, hS.rank, Nat.sub_zero]
  have pT : T.V.IsPosDef := fun τ => by rw [hT.sig τ, hT.rank, Nat.sub_zero]
  let x : DefSp S.V := ⟨cart S.M, onb S.M, S.Λ, vS⟩
  let y : DefSp T.V := ⟨cart T.M, onb T.M, T.Λ, vT⟩
  have hx : x.Is := GlobalTheory.SeeSawCompare.defSp_is hS.sigOK pS S.M x rfl rfl
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D S.V S.β S.Λ 1 hS.frame)
  have hy : y.Is := GlobalTheory.SeeSawCompare.defSp_is hT.sigOK pT T.M y rfl rfl
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D T.V T.β T.Λ 1 hT.frame)
  let k : KerDat S.V T.V := ⟨a.ω, a.vac, 0⟩
  have hk : k.Is ψ θ x y :=
    ⟨⟨χS, χT, (GlobalTheory.Grid.isWeil_false ψ S.V T.V χS χT a.ω).1 ha.weil⟩, ha.vac, fun u hu => (Finsupp.mem_support_iff.1 hu Finsupp.zero_apply).elim⟩
  exact ⟨x, y, k, hx, hy, hk, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem cenFock_fin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : GlobalTheory.Grid.Node D) (νS νT : ℕ) (PS PT : D.what₂.Tau → SPar), S.Is νS 0 PS → T.Is νT 0 PT → ∀ (a : GlobalTheory.Grid.ArrT S T) (χS χT : (AE D)ˣ →* Circle), a.Is ψ θ false χS χT → ∀ (χ : GA D S.V → ℂ) (f : WO S.V T.V → ℂ), IsThetaFunO ψ S.V T.V f → (∀ z ∈ GinfC S.V, z ∈ Subgroup.center (GA D S.V) → a.ω (z, 1) f = χ z • f) → ∃ (k : ℕ) (g : Fin k → WO S.V T.V → ℂ) (p : Fin k → GlobalTheory.Grid.Pol S T), (∀ l, GlobalTheory.Grid.IsFinVec ψ θ false S T (g l)) ∧ f = ∑ l, GlobalTheory.Grid.fock ψ θ false S T (g l) (p l) := by
  intro D ψ θ hθ S T νS νT PS PT hS hT a χS χT ha χ f hf hχ
  classical
  obtain ⟨x, y, k, hx, hy, hk, hxs, hys, hxB, hyB, hkom, hkvac⟩ := exists_defData hS hT ha
  have hstd : IsStdChar D ψ (-1) := hk.vac.1
  obtain ⟨χS', χT', hW⟩ := hk.weil
  obtain ⟨Wf, -, hWf⟩ := GlobalTheory.SeeSaw.CenFockPf.cenFock D ψ θ hθ S.V T.V x y hx hy k hk χ
  obtain ⟨n, u, c, hu, hc, hlat, hsum⟩ :=
    GlobalTheory.T.orientedTheta_eq_finite_heisenbergTranslates_vacua D ψ θ S.V T.V x.s y.s x.L y.L k.vac hx.sd hy.sd hk.vac f hf
  have hg : ∀ i, ∃ P, comb ψ S.V T.V (c i) f = pureTensorO ψ θ S.V T.V x.s y.s x.B y.B k.vac P := by
    intro i
    have he : ∀ z ∈ GinfC S.V, z ∈ Subgroup.center (GA D S.V) →
        k.om (z, 1) (comb ψ S.V T.V (c i) f) = χ z • comb ψ S.V T.V (c i) f := by
      intro z hz hzc
      rw [GlobalTheory.SeeSaw.RealComm.om_comb D ψ S.V T.V χS' χT' k.om hW z hz (c i) (hc i) f hf, hkom, hχ z hz hzc,
        comb_smul']
    obtain ⟨P, -, hP⟩ := hWf _ (theta_comb hstd hf) (hlat i) he
    exact ⟨P, hP⟩
  choose P hP using hg
  have hvth : IsThetaFunO ψ S.V T.V a.vac := hkvac ▸ hk.vac.2.theta
  refine ⟨n, fun i => heisO ψ S.V T.V (u i) a.vac, P, fun i => ⟨GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hstd hvth (u i),
    fun τ => isFockVacAt_heisO_fin hstd hθ hvth τ _ (ha.vac.2.fock τ) (hu i)⟩, ?_⟩
  refine hsum.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [hP i, heisO_pureTensorO_fin hstd hθ _ _ _ _ (hu i) hk.vac.2.theta, hxs, hys, hxB, hyB, hkvac]
  rfl

end GlobalTheory.CenFockGen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnMemLatticeIffIdealStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.ChiGrid
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.column_mem_lattice_iff_ideal : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε), ε ≠ 0 → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D) (q : Fin c) (b : AE D), (fun k => b * incA D (d.a k q)) ∈ GlobalTheory.FinPl.latV B (d.lat Λ 𝔟) (· = v) ↔ b ∈ GlobalTheory.SeeSaw.idV (𝔟 q) v := by
  first | exact @GlobalTheory.UnitaryEmbeddingColumns.mem_latV_iff | exact GlobalTheory.UnitaryEmbeddingColumns.mem_latV_iff | (intros; apply GlobalTheory.UnitaryEmbeddingColumns.mem_latV_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjCharacterEqProdSymmetricEdgeCharactersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjCharacter_eq_prod_symmetricEdge_characters_alt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∃ (ψ' : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (a : ∀ PP : Pl D.host.E, Fin D.R.r → Fin D.R.r → (kP PP)ˣ), IsGenericPsi R.Pg ψ' ∧ ∀ κ : GA D (Yc D 0), finE (Yc D 0) κ ∈ St β → ((iotaX X h).toMulEquiv κ).2 ∈ X.K2 → star (X.chi2 ((iotaX X h).toMulEquiv κ).2) = ∏ PP ∈ R.Pg, ψ' PP (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then (a PP i j : kP PP) * ((upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) : GL (Fin D.R.r) (kP PP)).val i j) else 0) := by
  first | exact @GlobalTheory.SeeConjChar.conjCharacter_eq_prod_symmetricEdge_characters | exact GlobalTheory.SeeConjChar.conjCharacter_eq_prod_symmetricEdge_characters | (intros; apply GlobalTheory.SeeConjChar.conjCharacter_eq_prod_symmetricEdge_characters <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanPairNegativeSymplecticPairingStatement
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archimedean_pair_negative_symplectic_pairing : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (B : Base F E) {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → 0 < n → 0 < d →
    ∀ (ε' : InfinitePlace F → ℤˣ) (w : InfinitePlace F), ε' w = -1 →
    ∃ u u' : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u ∧ At (evI F) u' ∧
      (∀ w', u'.map (piInf (B.emb w')) =
        (((ε' w' : ℤ) : ℂ) * Complex.I) • (X.θ w' * u.map (piInf (B.emb w')) * (W.θ w')ᵀ)) ∧
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (evI F (GlobalTheory.WeilM.symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) u u')) < 0 := by
  first | exact @GlobalTheory.WrongSignPair.exists_neg_pair | exact GlobalTheory.WrongSignPair.exists_neg_pair | (intros; apply GlobalTheory.WrongSignPair.exists_neg_pair <;> assumption)
end

