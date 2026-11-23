module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0911
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0920
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Formalism.LocalToGlobal.Divisibility.InertPartitionLePartF
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0925
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFormsDifferentialClosed
section
open GlobalTheory GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR.StabD

variable {K : Type} [Field K]

theorem dK_unit (u : Kˣ) : dK (u : K) = (u : K) • dlog u := by
  rw [dlog, smul_smul, Units.val_inv_eq_inv_val, mul_inv_cancel₀ u.ne_zero, one_smul]

theorem dlog_mul (u w : Kˣ) : dlog (u * w) = dlog u + dlog w := by
  simp only [dlog, Units.val_inv_eq_inv_val, Units.val_mul, dK, Derivation.leibniz, smul_add, smul_smul]
  rw [add_comm]
  congr 1
  · congr 1; field_simp
  · congr 1; field_simp

theorem dlog_one : dlog (1 : Kˣ) = 0 := by simp [dlog]

theorem dlog_inv (u : Kˣ) : dlog u⁻¹ = -dlog u := by
  have h := dlog_mul u⁻¹ u
  rw [inv_mul_cancel, dlog_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem dlog_pow (u : Kˣ) (m : ℕ) : dlog (u ^ m) = (m : K) • dlog u := by
  induction m with
  | zero => simp [dlog_one]
  | succ m ih => rw [pow_succ, dlog_mul, ih, Nat.cast_succ, add_smul, one_smul]

theorem dlog_prod {ι : Type} (s : Finset ι) (f : ι → Kˣ) : dlog (∏ i ∈ s, f i) = ∑ i ∈ s, dlog (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dlog_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, dlog_mul, ih]

theorem dDR_dlog (u : Kˣ) : CechDR.dDR ℤ K (CechDR.ι1 (dlog u)) = 0 := by
  have hD : dK ((u⁻¹ : Kˣ) : K) = -(((u⁻¹ : Kˣ) : K) * ((u⁻¹ : Kˣ) : K)) • dK (u : K) := by
    rw [dK_unit, dlog_inv, dlog, smul_neg, smul_smul, neg_smul]
  rw [dlog, map_smul, CechDR.dDR_smul, CechDR.dDR_D, smul_zero, add_zero]
  change CechDR.ι1 (dK ((u⁻¹ : Kˣ) : K)) * CechDR.ι1 (dK (u : K)) = 0
  rw [hD, map_smul, smul_mul_assoc, ExteriorAlgebra.ι_sq_zero, smul_zero]

theorem dDR_frame {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (i : Fin n) :
    CechDR.dDR ℤ K (CechDR.ι1 (frame x J i)) = 0 := by
  unfold frame
  split_ifs
  · exact dDR_dlog _
  · exact CechDR.dDR_D _

theorem dDR_ιMulti (q : ℕ) (v : Fin q → Ω[K⁄ℤ]) (hv : ∀ i, CechDR.dDR ℤ K (CechDR.ι1 (v i)) = 0) :
    CechDR.dDR ℤ K (ExteriorAlgebra.ιMulti K q v) = 0 := by
  induction q with
  | zero =>
    rw [ExteriorAlgebra.ιMulti_zero_apply, ← map_one (algebraMap K (abelian₂ K)), CechDR.dDR_algebraMap]
    simp
  | succ q ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, CechDR.dDR_mul]
    change _ * CechDR.dDR ℤ K _ + CechDR.dDR ℤ K (CechDR.ι1 (v 0)) * _ = 0
    rw [ih (Matrix.vecTail v) (fun i => hv _), hv 0, mul_zero, zero_mul, add_zero]

theorem dK_mem_frame (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (T : Kˣ) (r : Fin n → ℕ)
    (hx : AlgChart A x) (hT : dlog T = ∑ j ∈ J, (r j : K) • dlog (x j)) (c : K) (hc : c * (T : K) ∈ A) :
    ∃ d : Fin n → K, (∀ i, d i * (T : K) ∈ A) ∧ dK c = ∑ i, d i • frame x J i := by
  classical
  set a := c * (T : K) with ha
  obtain ⟨cc, hcc, hDa⟩ := hx.deriv a hc
  let e : Fin n → K := fun i => if i ∈ J then cc i * (x i : K) - a * (r i : K) else cc i
  have he : ∀ i, e i ∈ A := by
    intro i
    simp only [e]
    split_ifs
    · exact sub_mem (mul_mem (hcc i) (hx.mem i)) (mul_mem hc (natCast_mem A _))
    · exact hcc i
  have hT0 : (T : K) ≠ 0 := T.ne_zero
  refine ⟨fun i => (T : K)⁻¹ * e i, fun i => ?_, ?_⟩
  · rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hT0, one_mul]; exact he i
  have hsum : ∑ i, e i • frame x J i = dK a - a • ∑ j ∈ J, (r j : K) • dlog (x j) := by
    have hpt : ∀ i, e i • frame x J i =
        cc i • dK (x i : K) - (if i ∈ J then (a * (r i : K)) • dlog (x i) else 0) := by
      intro i
      simp only [e, frame]
      split_ifs
      · rw [sub_smul, mul_smul, ← dK_unit]
      · rw [sub_zero]
    rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_sub_distrib, ← hDa, Finset.sum_ite_mem,
      Finset.univ_inter, Finset.smul_sum]
    simp only [smul_smul]
  have hlead : dK a = c • dK (T : K) + (T : K) • dK c := Derivation.leibniz _ _ _
  have hTc : (T : K) • dK c = dK a - a • dlog T := by
    rw [hlead, dK_unit, smul_smul, ← ha]; abel
  calc dK c = (T : K)⁻¹ • ((T : K) • dK c) := by rw [smul_smul, inv_mul_cancel₀ hT0, one_smul]
    _ = _ := by
      rw [hTc, hT, ← hsum, Finset.smul_sum]
      simp only [smul_smul]

theorem dlog_twist (p : ℕ) [CharP K p] {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ)
    (r : Fin n → ℕ) : dlog (t ^ p * ∏ j ∈ J, x j ^ r j) = ∑ j ∈ J, (r j : K) • dlog (x j) := by
  rw [dlog_mul, dlog_pow, CharP.cast_eq_zero, zero_smul, zero_add, dlog_prod]
  simp only [dlog_pow]

end GlobalTheory.LogDR.StabD


open GlobalTheory.LogDR.StabD in
theorem GlobalTheory.LogDR.extD_mem_chartForms_twist : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (r : Fin n → ℕ), AlgChart A x → ∀ q, ∀ η ∈ chartForms A x J (t ^ p * ∏ j ∈ J, x j ^ r j) q, extD K η ∈ chartForms A x J (t ^ p * ∏ j ∈ J, x j ^ r j) (q + 1) := by
  intro K _ p _ _ A n x J t r hx q η hη
  unfold chartForms spanForms at hη ⊢
  induction hη using AddSubgroup.closure_induction with
  | mem η hη =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hη
    obtain ⟨d, hd, hDc⟩ := dK_mem_frame A x J _ r hx (dlog_twist p x J t r) c hc
    rw [extD_apply, CechDR.dDR_smul, dDR_ιMulti q v (fun i => by
      obtain ⟨k, hk⟩ := hv i; rw [← hk]; exact dDR_frame x J k), smul_zero, add_zero]
    change CechDR.ι1 (dK c) * _ ∈ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hDc, map_sum, Finset.sum_mul]
    refine sum_mem fun i _ => AddSubgroup.subset_closure ?_
    refine ⟨d i, hd i, Fin.cons (frame x J i) v, fun k => ?_, ?_⟩
    · refine Fin.cases ?_ (fun k => ?_) k
      · exact ⟨i, rfl⟩
      · rw [Fin.cons_succ]; exact hv k
    · rw [ExteriorAlgebra.ιMulti_succ_apply, map_smul, smul_mul_assoc]
      rfl
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [(extD K).map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactConjCharpolyBoundedDenominatorsAwayP
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.AwayPDen

theorem continuous_charpoly_coeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem charpoly_den_bounded : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf), IsCompact Ω → ∃ D : ℕ, 0 < D ∧ ∀ (g : G.GAf) (y : G.C) (x : (AfP p ⊗[ℚ] G.C)ˣ), g ∈ Ω → (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C) = (x : AfP p ⊗[ℚ] G.C) * inC G (AfP p) y * ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) → ∀ i, ∃ k : ℕ, ∃ a : ℤ, ((D * p ^ k : ℕ) : ℚ) * (LinearMap.mulLeft ℚ y).charpoly.coeff i = a := by
  intro p _ G Ω hΩ
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  set d := Module.finrank ℚ G.C
  let φ : G.GAf → AfP p ⊗[ℚ] G.C := fun g => ((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)
  have hφ : Continuous φ := Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)
  let F : ℕ → AfP p ⊗[ℚ] G.C → AfP p := fun i a => (LevelExists.mulMatAlg (AfP p) G.C a).charpoly.coeff i
  have hF : ∀ i, Continuous (F i) := fun i =>
    (continuous_charpoly_coeff d i).comp
      (IsModuleTopology.continuous_of_linearMap (LevelExists.mulMatAlg (AfP p) G.C).toLinearMap)
  let S : Set (AfP p) := ⋃ i ∈ Finset.range (d + 1), (F i ∘ φ) '' Ω
  have hS : IsCompact S := (Finset.range (d + 1)).isCompact_biUnion fun i _ => hΩ.image ((hF i).comp hφ)
  obtain ⟨D, hD0, hD⟩ := GlobalTheory.T.exists_common_pos_denominator_of_isCompact_finiteAdeleAway p S hS
  refine ⟨D, hD0, fun g y x hg hx i => ?_⟩
  by_cases hi : i ≤ d
  · have hmem : F i (φ g) ∈ S :=
      Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.lt_succ_of_le hi))) ⟨g, hg, rfl⟩
    have hval : F i (φ g) = algebraMap ℚ (AfP p) ((LinearMap.mulLeft ℚ y).charpoly.coeff i) := by
      show (LevelExists.mulMatAlg (AfP p) G.C (φ g)).charpoly.coeff i = _
      rw [show φ g = _ from hx]
      have := GlobalTheory.T.charpoly_tensorLeftMul_conj_one_tmul (AfP p) G.C x y
      simp only [inC] at *
      rw [show ((Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] AfP p ⊗[ℚ] G.C) : G.C →+* AfP p ⊗[ℚ] G.C) y = 1 ⊗ₜ[ℚ] y from rfl]
      rw [this, Polynomial.coeff_map]
    have h2 := hD _ hmem
    rw [hval] at h2
    have h3 : algebraMap ℚ (AfP p) ((D : ℚ) * (LinearMap.mulLeft ℚ y).charpoly.coeff i) ∈ LevelExists.intAfP p := by
      rw [map_mul, map_natCast]; exact h2
    obtain ⟨k, a, ha⟩ := GlobalTheory.T.exists_primePow_mul_eq_int_of_integral_finiteAdeleAway p _ h3
    exact ⟨k, a, by rw [← ha]; push_cast; ring⟩
  · refine ⟨0, 0, ?_⟩
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [LinearMap.charpoly_natDegree]; omega)]
    simp

end GlobalTheory.AwayPDen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactFiniteAdelesAwayPBoundedDenominators
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.DenAwayCpt

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum GlobalTheory.DenAway

theorem exists_nat_mul_integral_of_isCompact : ∀ (p : ℕ) [Fact p.Prime] (Q : Set (AfP p)), IsCompact Q →
    ∃ D : ℕ, 0 < D ∧ ∀ a ∈ Q, ∀ v : AwayP p, AfP.eval v ((D : AfP p) * a) ∈ v.1.adicCompletionIntegers ℚ := by
  intro p _ Q hQ
  choose m hm0 hm using fun a : AfP p => exists_nat_adele a
  obtain ⟨t, ht⟩ := hQ.elim_finite_subcover
    (fun a => (fun x => (m a : AfP p) * x) ⁻¹' intAfP p)
    (fun a => (isOpen_intAfP p).preimage (continuous_const_mul _))
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hm x⟩)
  refine ⟨∏ a ∈ t, m a, Finset.prod_pos (fun a _ => hm0 a), fun x hx v => ?_⟩
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (ht hx)
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m ha
  have hxa' : (m a : AfP p) * x ∈ intAfP p := hxa
  have e : ((∏ a ∈ t, m a : ℕ) : AfP p) * x = (k : AfP p) * ((m a : AfP p) * x) := by
    rw [hk, Nat.cast_mul]; ring
  rw [e, eval_natCast_mul]
  exact mul_mem (natCast_mem v.1 k) (hxa' v)

end GlobalTheory.DenAwayCpt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsPartsDistinctTypesOrthogonal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.Div

open scoped ComplexOrder


open Formalism.IndefR.Cx.GroupActionMatrices Formalism.IndefR.Cx.EigenprojectionMatrices Formalism.IndefR.Cx.OrthogonalPartDecomposition Formalism.L2.DIV.CyclotomicLifting in
theorem csum_eigSum_orth {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I : Type}
    {B : BlockDat K G Pl0} {ℓ : Lvl K G} {v : InfinitePlace K} {s : ℕ} {op : I → Module.End K B.S.Forms}
    (h : BlockHyp B ℓ v s) (hO : OkOp B op) {C C' : (I → K) → Prop} (hCC : ∀ x, C' x → ¬ C x) {f g : B.S.Forms}
    (hf : f ∈ Formalism.L2.Col.eigSum op C) (hg : g ∈ Formalism.L2.Col.eigSum op C') :
    B.S.csum (f : B.S.Cl → B.S.V) (g : B.S.Cl → B.S.V) = 0 := by
  classical
  have hA : (B.S.H.map v.embedding).PosDef := h.ok.hpos v
  have hHh : B.S.Hᴴ = B.S.H := FinitelyNonzeroLinear.herm_of_pos h.conj (h.ok.hpos v)
  have hadj : ∀ i, ∃ i', B.S.H.map v.embedding * (oM B op i).map v.embedding =
      ((oM B op i').map v.embedding)ᴴ * B.S.H.map v.embedding := by
    intro i
    obtain ⟨i', hi'⟩ := oM_adj hO i
    have h2 : B.S.H * oM B op i = (oM B op i')ᴴ * B.S.H := by
      have := congrArg Matrix.conjTranspose hi'
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHh] at this
      exact this
    refine ⟨i', ?_⟩
    rw [← Matrix.map_mul, h2, Matrix.map_mul, map_conjTranspose_of_mem_cmMax v.embedding _ (hO.rat i')]
  have hc : Formalism.L2.Col.PairComm (linF fun i => (oM B op i).map v.embedding) := fun i j =>
    linF_commute (by rw [← Matrix.map_mul, ← Matrix.map_mul, oM_comm hO.comm])
  have hs : Formalism.L2.Col.SplitOver (linF fun i => (oM B op i).map v.embedding) := fun i =>
    Module.End.iSup_maxGenEigenspace_eq_top _
  have hmem : ∀ {S : (I → K) → Prop} {z : B.S.Forms}, z ∈ Formalism.L2.Col.eigSum op S →
      (fun a => v.embedding (B.S.basis.equivFun z a)) ∈ Formalism.L2.Col.eigSum (linF fun i => (oM B op i).map v.embedding)
        (fun w => ∃ x, S x ∧ w = fun i => v.embedding (x i)) := by
    intro S z hz
    have h1 : B.S.basis.equivFun z ∈ Formalism.L2.Col.eigSum (fun i => Matrix.toLin' (oM B op i)) S := by
      have := eigSum_le_comap_of (B.S.basis.equivFun : B.S.Forms →ₗ[K] (Fin B.S.dim → K)) op
        (fun i => Matrix.toLin' (oM B op i)) (fun i f => by rw [Matrix.toLin'_apply]; exact equivFun_oM i f) _ hz
      simpa [Submodule.mem_comap] using this
    exact emb_mem_eigSum v.embedding (oM B op) S h1
  have hCC' : ∀ w, (fun w => ∃ x, C' x ∧ w = fun i => v.embedding (x i)) w →
      ¬ (fun w => ∃ x, C x ∧ w = fun i => v.embedding (x i)) w := by
    rintro w ⟨x', hx', rfl⟩ ⟨x, hx, e⟩
    have : x' = x := funext fun i => v.embedding.injective (by simpa using congrFun e i)
    subst this
    exact hCC x' hx' hx
  have key := cx_eig_orth (fun i => (oM B op i).map v.embedding) (B.S.H.map v.embedding) hA hadj hc hs hCC' (hmem hf) (hmem hg)
  have hform0 : hform B.S.H (B.S.basis.equivFun f) (B.S.basis.equivFun g) = 0 := by
    apply v.embedding.injective
    rw [map_zero, ← key, RationalHermitianForm.hform_eq_dot, ← emb_mulVec v.embedding B.S.H]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sum, map_mul, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h.conj]
    rfl
  rw [hform_eq_csum, CSD.I_apply, CSD.I_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at hform0
  exact hform0

end GlobalTheory.Div

namespace GlobalTheory.Div


set_option maxHeartbeats 1000000 in
theorem inner_jX_csum {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hM : R.IsModels) (t : A.fam.base.Tup)
    (x y : (A.fam.R t).S.Forms) :
    Formalism.IndefR.Links.cj (twAt D.what₂.embLL A.v0) (inner ℂ (R.jX t x) (R.jX t y)) =
      A.v0.embedding ((A.fam.R t).S.csum ((x : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V)
        ((y : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V)) := by
  rw [(hM.HX t).2.2, hM.jX, hM.jX, R.emb0]
  congr 1
  exact Formalism.IndefR.Bridge.ClassPres.isom_holds (R.B.R t).pres x y

theorem inner_jX_zero {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hM : R.IsModels) (t : A.fam.base.Tup)
    (x y : (A.fam.R t).S.Forms)
    (h : (A.fam.R t).S.csum ((x : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V)
        ((y : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V) = 0) :
    inner ℂ (R.jX t x) (R.jX t y) = 0 := by
  have key := inner_jX_csum R hM t x y
  have h1 : Formalism.IndefR.Links.cj (twAt D.what₂.embLL A.v0) (inner ℂ (R.jX t x) (R.jX t y)) = 0 :=
    key.trans ((congrArg (⇑A.v0.embedding) h).trans (map_zero A.v0.embedding))
  exact (map_eq_zero (Formalism.IndefR.Links.cj (twAt D.what₂.embLL A.v0))).1 h1

end GlobalTheory.Div

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Div.parts_orth_complex : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → ∀ p q : A3.fam3.base3.Ix, p ≠ q → ∀ x ∈ Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)), ∀ y ∈ Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum q.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)), ⟪x, y⟫_ℂ = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hH p q hpq x hx y hy
  have hok := hOk.ok2.what₂ A3.A.μ0
  have hO := okOp_opAll hok (hOk.what₂ A3.A.μ0) (hH A3.A.μ0).1 (hH A3.A.μ0).2
  have hSS : ∀ z, (A3.rowI A3.A.μ0).HasRes3 q.1 z → ¬ (A3.rowI A3.A.μ0).HasRes3 p.1 z := fun z hq =>
    (A3.rowI A3.A.μ0).excl3 ((A3.rowI A3.A.μ0).diffAt_of_mem_ixFin3 q.2 p.2 fun e => hpq (Subtype.ext e).symm) z hq
  have hblk : BlockHyp (A3.A.fam.R A3.A.μ0) (A3.A.fam.lvl F.P0 F.ψ0) A3.A.fam.v0 s := ⟨hOk.ok2.conj, hOk.ok2.irr, hok⟩
  have hgen : ∀ f ∈ (A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1, ∀ g ∈ (A3.rowI A3.A.μ0).inertTypeEigenspaceSum q.1,
      ⟪R.jX A3.A.μ0 f, R.jX A3.A.μ0 g⟫_ℂ = 0 := by
    intro f hf g hg
    have h0 := GlobalTheory.Div.csum_eigSum_orth hblk hO hSS hf hg
    exact GlobalTheory.Div.inner_jX_zero R.toRealDat hC.base.models A3.A.μ0 f g h0
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨f, hf, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨g, hg, rfl⟩ := hb
      exact hgen f hf g hg
    | zero => simp
    | add u w _ _ hu hw => rw [inner_add_right, hu, hw, add_zero]
    | smul c u _ hu => rw [inner_smul_right, hu, mul_zero]
  | zero => simp
  | add u w _ _ hu hw => rw [inner_add_left, hu, hw, add_zero]
  | smul c u _ hu => rw [inner_smul_left, hu, mul_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompositeCutOperatorsProductLocalCellsMirabolic
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.CutProd

open GlobalTheory.JSW.Cut

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}

theorem lr_loc_of_mem_mirS {S : Finset (HeightOneSpectrum (𝓞 E))} {p : GA E (m + 1)} (hp : p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m))
    (w : HeightOneSpectrum (𝓞 E)) :
    GlobalTheory.JSW.KirFin.lr (GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p) = GlobalTheory.JSW.KirFin.lr 1 := by
  funext j
  have h := hp.2 j
  simp only [GlobalTheory.JSW.KirFin.lr]
  show ((pLoc E w).comp (pFin E)) ((p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j) = _
  rw [h]
  split_ifs with hj <;> simp [hj, Matrix.one_apply, eq_comm]

theorem exists_cut_prod (ψ : ∀ w : HeightOneSpectrum (𝓞 E), AddChar (w.adicCompletion E) ℂ)
    (hψ : ∀ w x, ψ w x = (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w x)) : ℂ)) (K : Subgroup (GL (Fin (m + 1)) (Af E)))
    (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E)))
    (z : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)) (S : Finset (HeightOneSpectrum (𝓞 E))) :
    (∀ w ∈ S, ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) →
    (∀ w ∈ S, Cuts (ψ w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))
      (cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1}) →
    ∃ T : GA E (m + 1) →₀ ℂ, (∀ h ∈ T.support, h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S ∧ GeneralLinearGroup.map (pInf E) h = 1) ∧
      ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) →
        (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) →
        ∀ y : GA E (m + 1), (∀ w ∈ S, GlobalTheory.JSW.KirFin.lr (GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y) =
          GlobalTheory.JSW.KirFin.lr 1) →
        GlobalTheory.JSW.Cut.act T W y = {x : GA E (m + 1) | ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈
          cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))}.indicator W y := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro _ _
    refine ⟨Finsupp.single 1 1, fun h hh => ?_, fun W _ _ y _ => ?_⟩
    · have h1 : h = 1 := Finset.mem_singleton.1 (Finsupp.support_single_subset hh)
      subst h1
      exact ⟨fun v _ => map_one _, map_one _⟩
    · simp
  | insert w S hw ih =>
    intro hK hC
    obtain ⟨T₁, hT₁s, hT₁⟩ := ih (fun v hv => hK v (Finset.mem_insert_of_mem hv))
      (fun v hv => hC v (Finset.mem_insert_of_mem hv))
    obtain ⟨T₂, hT₂s, hT₂⟩ := GlobalTheory.T.localCutOperator_transfer_adelicWhittaker E m w (ψ w) (hψ w) K (U w) (hK w (Finset.mem_insert_self _ _))
      (cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1}
      (hC w (Finset.mem_insert_self _ _))
    refine ⟨comp T₁ T₂, fun k hk => ?_, fun W hN hKW y hy => ?_⟩
    · obtain ⟨a, ha, b, hb, rfl⟩ := mem_support_comp hk
      obtain ⟨g, rfl⟩ := hT₂s b hb
      have hb' := (GlobalTheory.JSW.WhitModel.loc_mem_supS (insert w S) w g).2 (Or.inl (Finset.mem_insert_self _ _))
      refine ⟨fun v hv => ?_, ?_⟩
      · rw [map_mul, (hT₁s a ha).1 v (fun h => hv (Finset.mem_insert_of_mem h)), hb' v hv, one_mul]
      · rw [map_mul, (hT₁s a ha).2, pInf_finGL, one_mul]
    · have hyh : ∀ h ∈ T₁.support, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (y * h) =
          GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y := fun h hh => by
        rw [map_mul, (hT₁s h hh).1 w hw, mul_one]
      have hyS := hT₁ W hN hKW y (fun v hv => hy v (Finset.mem_insert_of_mem hv))
      have hyw := hy w (Finset.mem_insert_self _ _)
      rw [act_comp]
      by_cases hyc : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y ∈
          cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))
      · rw [act_congr T₁ (f' := W) fun k hk => ?_, hyS]
        · simp only [Set.indicator, Set.mem_setOf_eq, Finset.forall_mem_insert, hyc, true_and]
        · rw [hT₂ W hN hKW (y * k) (by rw [hyh k hk]; exact hyw), Set.indicator_of_mem]
          rw [Set.mem_setOf_eq, hyh k hk]; exact hyc
      · rw [act_congr T₁ (f' := 0) fun k hk => ?_]
        · simp only [Set.indicator, Set.mem_setOf_eq, Finset.forall_mem_insert, hyc, false_and, if_false]
          unfold GlobalTheory.JSW.Cut.act; simp
        · rw [hT₂ W hN hKW (y * k) (by rw [hyh k hk]; exact hyw), Set.indicator_of_notMem]
          · rfl
          · rw [Set.mem_setOf_eq, hyh k hk]; exact hyc

end GlobalTheory.JSW.CutProd

theorem _root_.GlobalTheory.JSW.CutProd.cut_prod_mirS : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (ψ : ∀ w : HeightOneSpectrum (𝓞 E), AddChar (w.adicCompletion E) ℂ), (∀ w x, ψ w x = (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w x)) : ℂ)) → ∀ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))) (z : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)), (∀ w ∈ S, ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) → (∀ w ∈ S, GlobalTheory.JSW.Cut.Cuts (ψ w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) (GlobalTheory.JSW.Cut.cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1}) → ∃ T : GA E (m + 1) →₀ ℂ, (∀ h ∈ T.support, h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S ∧ GeneralLinearGroup.map (pInf E) h = 1) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.Cut.act T W p = {x : GA E (m + 1) | ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈ GlobalTheory.JSW.Cut.cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))}.indicator W p := by
  intro E _ _ _ m S ψ hψ K U z hK hC
  obtain ⟨T, hTs, hT⟩ := GlobalTheory.JSW.CutProd.exists_cut_prod ψ hψ K U z S hK hC
  exact ⟨T, hTs, fun W hN hKW p hp => hT W hN hKW p fun w _ => GlobalTheory.JSW.CutProd.lr_loc_of_mem_mirS hp w⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePlaceLiesOver
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_place_lies_over : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (ψ : G.F →+* PadicAlgCl p), ¬ LiesOver G.Kq G.u ψ → LiesOver G.Kq G.u (ψ.comp (IsCMField.complexConj G.F : G.F →+* G.F)) := by
  first | (exact @GlobalTheory.StabFinOver.liesOver_comp_complexConj_of_not_liesOver) | (exact GlobalTheory.StabFinOver.liesOver_comp_complexConj_of_not_liesOver) | (intros; apply GlobalTheory.StabFinOver.liesOver_comp_complexConj_of_not_liesOver  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCharpolyCoeffMulLeftFiniteAdelesAwayPStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_charpoly_coeff_mulLeft_finiteAdeles_awayP : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (k : ℕ), Continuous fun g : G.GAf => (LinearMap.charpoly (LinearMap.mulLeft (AfP p) (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C))).coeff k := by
  first | (exact @GlobalTheory.charpoly_coeff_continuous_GAf) | (exact GlobalTheory.charpoly_coeff_continuous_GAf) | (intros; apply GlobalTheory.charpoly_coeff_continuous_GAf  <;> assumption)
end

