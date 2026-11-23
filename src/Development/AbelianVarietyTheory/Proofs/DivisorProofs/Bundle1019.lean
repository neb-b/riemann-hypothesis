module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0002
public import Formalism.LocalToGlobal.GlobalTheory.GL6.BwAValIntegralNonneg
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0895
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0994
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0873
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryLocallyCompactHausdorff
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

namespace GlobalTheory.AdelicUnitaryTop

theorem lcsc_UA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
    LocallyCompactSpace (UA σ J) ∧ SecondCountableTopology (UA σ J) ∧ T2Space (UA σ J) := by
  intro F E _ _ _ _ _ σ n J
  haveI := locallyCompact_adele F
  haveI := secondCountable_adele F
  haveI := t2Space_adeleRing_numberField F
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (Fin n) (AE F E)) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin n) (AE F E)) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : T2Space (GL (Fin n) (AE F E)) := Units.isEmbedding_embedProduct.t2Space
  have hσ : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hc : IsClosed (UG (cA σ) (incM F J) : Set (GL (Fin n) (AE F E))) := by
    have hv : Continuous fun g : GL (Fin n) (AE F E) => (g : Matrix (Fin n) (Fin n) (AE F E)) :=
      Units.continuous_val
    exact isClosed_eq ((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul
      (hv.matrix_map hσ)) continuous_const
  exact ⟨hc.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    hc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology,
    inferInstanceAs (T2Space (UG (cA σ) (incM F J)))⟩

end GlobalTheory.AdelicUnitaryTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgChainBStable
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial TensorProduct

namespace GlobalTheory.ChainStab

theorem hw_rowHom (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    ∃ μ : Fin r → ℕ, IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) (Formalism.GradedWeylDivisibility.hw R hn ν) μ := by
  unfold Formalism.GradedWeylDivisibility.hw
  exact ⟨_, IsWeightedHomogeneous.prod _ _ _ fun s _ => (Formalism.GradedWeylDivisibility.lpMinor_rowHom R _ _ _).pow _⟩

theorem homZ_of_homN {R : Type} [CommRing R] {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) R) (μ : Fin r → ℕ)
    (h : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) f μ) :
    IsWeightedHomogeneous (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_wZ r n) f (fun i => (μ i : ℤ)) := by
  intro m hm
  rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_weight_cast, h hm]

theorem applyWord_homZ {R : Type} [CommRing R] {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) R) (μ : Fin r → ℤ)
    (hf : IsWeightedHomogeneous (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_wZ r n) f μ) (w : List (Fin r × Fin r × ℕ)) :
    ∃ μ' : Fin r → ℤ, IsWeightedHomogeneous (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_wZ r n) (Formalism.GradedWeylDivisibility.applyWord R w f) μ' := by
  induction w with
  | nil => exact ⟨μ, hf⟩
  | cons x w ih =>
    obtain ⟨μ', h⟩ := ih
    exact ⟨_, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_G_of_homog x.1 x.2.1 _ μ' h x.2.2⟩

theorem comp_of_homZ {R : Type} [CommRing R] {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) R) (μ : Fin r → ℤ)
    (hf : IsWeightedHomogeneous (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_wZ r n) f μ) (m : Fin r → ℕ) :
    weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m f = f ∨
      weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m f = 0 := by
  classical
  by_cases hg : f = 0
  · right; rw [hg, map_zero]
  · obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.1 hg
    have hN : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) f (Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) m0) := by
      intro d hd
      have h1 := hf hd
      have h2 := hf hm0
      rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_weight_cast] at h1 h2
      funext i
      exact_mod_cast congrFun (h1.trans h2.symm) i
    rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 hN)]
    split_ifs
    · left; rfl
    · right; rfl

theorem weyl_comp_mem (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (m : Fin r → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν) :
    weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
  obtain ⟨μ0, h0⟩ := hw_rowHom R hn ν
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨μ, hμ⟩ := applyWord_homZ _ _ (homZ_of_homN _ _ h0) w
    rcases comp_of_homZ _ μ hμ m with h | h <;> rw [h]
    · exact Submodule.subset_span ⟨w, rfl⟩
    · exact Submodule.zero_mem _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem tprod_mem_tensSub {O : Type} [CommRing O] {ι : Type} {A : ι → Type} [∀ i, AddCommGroup (A i)]
    [∀ i, Module O (A i)] (B : ∀ i, Submodule O (A i)) (x : ∀ i, A i) (hx : ∀ i, x i ∈ B i) :
    PiTensorProduct.tprod O x ∈ tensSub B :=
  LinearMap.mem_range.2 ⟨PiTensorProduct.tprod O (fun i => ⟨x i, hx i⟩), by rw [PiTensorProduct.map_tprod]; rfl⟩

theorem map_mem_tensSub {O : Type} [CommRing O] {ι : Type} {A : ι → Type} [∀ i, AddCommGroup (A i)]
    [∀ i, Module O (A i)] (B : ∀ i, Submodule O (A i)) (f : ∀ i, A i →ₗ[O] A i)
    (hf : ∀ i, ∀ x ∈ B i, f i x ∈ B i) (y : ⨂[O] i, A i) (hy : y ∈ tensSub B) :
    PiTensorProduct.map f y ∈ tensSub B := by
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hy
  refine LinearMap.mem_range.2 ⟨PiTensorProduct.map (fun i => (f i).restrict (hf i)) z, ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
  rfl

variable {O : Type} [CommRing O] {N : ℕ} {ι : Type} [DecidableEq ι] {lam : ι → ℕ → ℕ}

theorem grp_stab (s : Finset ι) (g : ι → GL (Fin N) O) :
    ∀ y ∈ tensSub (chainB (deltaIn O N lam) s), grp O N lam g y ∈ tensSub (chainB (deltaIn O N lam) s) := by
  intro y hy
  have h1 : grp O N lam g = PiTensorProduct.map
      (fun i => Formalism.UG.dualWeylRep O N N (res N (lam i)) (g i)) := rfl
  rw [h1]
  refine map_mem_tensSub _ _ (fun i x hx => ?_) y hy
  unfold chainB at hx ⊢
  split_ifs at hx ⊢ with hi
  · exact Submodule.mem_top
  · exact Formalism.UG.P.weyl_module_GL_stable O N N le_rfl (res N (lam i)) (g i) x.1 hx

theorem proj_stab (s : Finset ι) (τ : ι) (w : Fin N → ℕ) (a : Module.End O (NablaT O N lam))
    (ha : IsProj O N lam τ w a) :
    ∀ y ∈ tensSub (chainB (deltaIn O N lam) s), a y ∈ tensSub (chainB (deltaIn O N lam) s) := by
  intro y hy
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hy
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c f =>
    rw [map_smul, PiTensorProduct.map_tprod, map_smul]
    refine Submodule.smul_mem _ c ?_
    let x : ∀ i, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam i)) := fun i => (f i : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam i)))
    have hc := Formalism.GradedWeylDivisibility.dualWeylRowGraded O N N (res N (lam τ)) w _ (x τ).2
    change a (PiTensorProduct.tprod O x) ∈ _
    rw [ha x ⟨_, hc⟩ rfl]
    apply tprod_mem_tensSub
    intro i
    by_cases hi : i = τ
    · subst hi
      rw [Function.update_self]
      have hf := (f i).2
      unfold chainB at hf ⊢
      split_ifs at hf ⊢ with hs
      · exact Submodule.mem_top
      · exact weyl_comp_mem O le_rfl (res N (lam i)) w _ hf
    · rw [Function.update_of_ne hi]
      exact (f i).2
  | add y₁ y₂ h₁ h₂ =>
    rw [map_add (f := _), map_add (f := _)]
    exact Submodule.add_mem _ (h₁ (LinearMap.mem_range_self _ _)) (h₂ (LinearMap.mem_range_self _ _))

end GlobalTheory.ChainStab

namespace GlobalTheory.ExpFrame

open GlobalTheory.ChainStab

theorem alg_chainB_stable : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (s : Finset ι) (a : alg O N lam),
    ∀ x ∈ tensSub (chainB (Formalism.CohomologicalDescent.DepthNonnegative.deltaIn O N lam) s), a • x ∈ tensSub (chainB (Formalism.CohomologicalDescent.DepthNonnegative.deltaIn O N lam) s) := by
  intro O _ _ _ _ N ι _ _ lam s a
  let L := tensSub (chainB (Formalism.CohomologicalDescent.DepthNonnegative.deltaIn O N lam) s)
  let St : Subalgebra O (Module.End O (NablaT O N lam)) :=
    { carrier := {f | ∀ x ∈ L, f x ∈ L}
      mul_mem' := fun ha hb x hx => ha _ (hb x hx)
      add_mem' := fun ha hb x hx => L.add_mem (ha x hx) (hb x hx)
      algebraMap_mem' := fun c x hx => by
        rw [Module.algebraMap_end_apply]; exact L.smul_mem c hx }
  have hle : alg O N lam ≤ St := Algebra.adjoin_le (by
    rintro f (⟨g, rfl⟩ | ⟨τ, w, hf⟩)
    · exact grp_stab s g
    · exact proj_stab s τ w f hf)
  intro x hx
  exact hle a.2 x hx

end GlobalTheory.ExpFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgEqOfLeRightStabiliser
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

theorem avg_eq_of_le_rStab : ∀ (H : Type) [Group H] (u : H → ℂ) (S : Subgroup H), S ≤ rStab u → S.index ≠ 0 →
    avg u = (S.index : ℂ)⁻¹ * ∑ᶠ q : H ⧸ S, u q.out := by
  intro H _ u S hS hi
  haveI : S.FiniteIndex := ⟨hi⟩
  haveI : (rStab u).FiniteIndex := Subgroup.finiteIndex_of_le hS
  have hRi : (rStab u).index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hu : ∀ x : H, u ((QuotientGroup.mk x : H ⧸ rStab u).out) = u x := by
    intro x
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (rStab u) x
    rw [hk]
    exact k.2 x
  let e := Subgroup.quotientEquivProdOfLE hS
  have he : ∀ q : H ⧸ S, ((e q).1 : H ⧸ rStab u) = QuotientGroup.mk q.out := by
    intro q
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  haveI : Fintype (H ⧸ S) := Fintype.ofFinite _
  haveI : Fintype (H ⧸ rStab u) := Fintype.ofFinite _
  haveI : Finite ((rStab u) ⧸ S.subgroupOf (rStab u)) := by
    have : Finite ((H ⧸ rStab u) × (rStab u) ⧸ S.subgroupOf (rStab u)) := Finite.of_equiv _ e
    exact Finite.prod_right (H ⧸ rStab u)
  haveI : Fintype ((rStab u) ⧸ S.subgroupOf (rStab u)) := Fintype.ofFinite _
  have hsum : ∑ᶠ q : H ⧸ S, u q.out =
      (S.relIndex (rStab u) : ℂ) * ∑ᶠ p : H ⧸ rStab u, u p.out := by
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    have h1 : ∀ q : H ⧸ S, u q.out = (fun p : (H ⧸ rStab u) × ((rStab u) ⧸ S.subgroupOf (rStab u)) =>
        u p.1.out) (e q) := by
      intro q
      simp only
      rw [he q, hu]
    rw [Finset.sum_congr rfl (fun q _ => h1 q), Equiv.sum_comp e (fun p => u p.1.out),
      Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    congr 1
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  rw [avg, hsum, ← Subgroup.relIndex_mul_index hS]
  have h2 : (S.relIndex (rStab u) : ℂ) ≠ 0 := by
    have : S.relIndex (rStab u) ≠ 0 := by
      intro h0; apply hi; rw [← Subgroup.relIndex_mul_index hS, h0, zero_mul]
    exact_mod_cast this
  have h3 : ((rStab u).index : ℂ) ≠ 0 := by exact_mod_cast hRi
  push_cast
  field_simp

end GlobalTheory.BCT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeFixedCentraliserAlg
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical


open GlobalTheory.FinClsLoc.BaseChangeCent in
theorem GlobalTheory.FinClsLoc.baseChange_fixedCentraliser_alg :
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β Y : G.Cˣ) (L : Type) [Ring L] [Algebra ℚ L] (ι : L →ₐ[ℚ] G.C),
    Function.Injective ι →
    (∀ c : G.C, c ∈ Set.range ι ↔ Commute c (Y : G.C) ∧ (β : G.C) * sh G c * ((β⁻¹ : G.Cˣ) : G.C) = c) →
    ∀ (K : Type) [Field K] [Algebra ℚ K],
      Function.Injective (Algebra.TensorProduct.map (AlgHom.id K K) ι) ∧
      ∀ x : K ⊗[ℚ] G.C, x ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id K K) ι) ↔
        Commute x (inC G K (Y : G.C)) ∧
          inC G K (β : G.C) * (starT G.star K x).unop * inC G K ((β⁻¹ : G.Cˣ) : G.C) = x := by
  intro p _ G β Y L _ _ ι hinj hrange K _ _
  have hmap : ∀ z, Algebra.TensorProduct.map (AlgHom.id K K) ι z = (ι.toLinearMap.lTensor K) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul k l => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hex : Function.Exact ι.toLinearMap (phi G β Y ((β⁻¹ : G.Cˣ) : G.C)) := by
    intro c
    change _ ↔ c ∈ Set.range ι
    rw [phi_apply, hrange c, Prod.mk_eq_zero, sub_eq_zero, sub_eq_zero]
    rfl
  have hex' := Module.Flat.lTensor_exact K hex
  refine ⟨?_, ?_⟩
  · have := Module.Flat.lTensor_preserves_injective_linearMap (M := K) ι.toLinearMap hinj
    intro a b hab
    apply this
    rw [← hmap, ← hmap, hab]
  · intro x
    have e1 : x ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id K K) ι) ↔
        x ∈ Set.range (ι.toLinearMap.lTensor K) := by
      constructor <;> rintro ⟨z, rfl⟩ <;> exact ⟨z, by rw [hmap]⟩
    rw [e1, ← hex' x, ← (TensorProduct.prodRight ℚ ℚ K G.C G.C).map_eq_zero_iff, lTensor_phi,
      Prod.mk_eq_zero, sub_eq_zero, sub_eq_zero]
    exact and_congr Iff.rfl Iff.rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeLevelFamilyIff
section
noncomputable section

open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

def tens {G H : Type} (f : G → ℂ) (g : H → ℂ) : G × H → ℂ := fun y => f y.1 * g y.2

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def geomSt2 (a b : ℕ) (S : Set (Pl E)) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
    (φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) : ℂ :=
  ∑ᶠ p ∈ {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E b ∧ IsCoprime p.1 p.2},
    kap p.1 * kap p.2 * chW l₁ p.1 * chW l₂ p.2 * ∏ᶠ w ∈ S, stTw2 a b w (atPl w p.1) (atPl w p.2) (φ w)

end GlobalTheory.BCT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnipotentMemUpperUnipotent
section
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul.UnipPlaced

variable {R : Type} [CommRing R]

theorem mul_apply_succ {n : ℕ} {X Y : GL (Fin n) R} (hX : X ∈ unipB R (Fin n)) (hY : Y ∈ unipB R (Fin n))
    {a a' : Fin n} (h : a'.val = a.val + 1) :
    ((X * Y : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a a' =
      (X : Matrix (Fin n) (Fin n) R) a a' + (Y : Matrix (Fin n) (Fin n) R) a a' := by
  rw [mem_unipB] at hX hY
  have hne : a ≠ a' := fun e => by have := congrArg Fin.val e; omega
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_add_of_mem a a' (Finset.mem_univ _) (Finset.mem_univ _) hne]
  · rw [hX.2 a, hY.2 a', one_mul, mul_one, add_comm]
  · intro c _ hc
    have h1 := Fin.val_injective.ne hc.1
    have h2 := Fin.val_injective.ne hc.2
    by_cases hca : c < a
    · rw [hX.1 a c hca, zero_mul]
    · have : a' < c := by rw [Fin.lt_iff_val_lt_val] at hca ⊢; omega
      rw [hY.1 c a' this, mul_zero]

end GlobalTheory.GamMul.UnipPlaced

namespace GlobalTheory.GamMul.UnipPlaced

variable {R : Type} [CommRing R]

theorem superDiag_mul_unip {n : ℕ} {u v : GL (Fin n) R} (hu : u ∈ unipB R (Fin n)) (hv : v ∈ unipB R (Fin n)) :
    superDiag (u * v) = superDiag u + superDiag v := by
  simp only [superDiag, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj =>
    mul_apply_succ hu hv (Finset.mem_filter.1 hj).2

end GlobalTheory.GamMul.UnipPlaced
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardKerIntegralCombinationEndoLePow
section
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.OEndDegree

theorem card_ker_le : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : Over (Sp k)) [GrpObj A] (act : OAct (𝓞 E) A) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (d : ℕ) (a : Fin d → 𝓞 E), ∃ C : ℕ, ∀ (n : Fin d → ℤ) (K : ℕ), (∀ i, (n i).natAbs ≤ K) → ∑ i, n i • a i ≠ 0 → Finite {x : 𝟙_ (Over (Sp k)) ⟶ A // x ≫ act.act (∑ i, n i • a i) = 1} ∧ Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ≫ act.act (∑ i, n i • a i) = 1} ≤ C * K ^ (2 * g) := by
  intro E _ _ k _ _ _ A _ act g hB hg d a
  haveI := hB.comm
  haveI : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  haveI : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  obtain ⟨H, m, s, c, hH, hs, hc, hsec⟩ := _root_.GlobalTheory.OEndDegree.exists_effective_bound E k A act g hB hg d a
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.degree_le_of_pull_le_pow k A.left A.hom g hg H m s hH hs
  refine ⟨C * c ^ g, fun n K hn hb => ?_⟩
  have hK : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with rfl | h
    · exfalso; apply hb
      refine Finset.sum_eq_zero fun i _ => ?_
      have := hn i
      rw [Nat.le_zero, Int.natAbs_eq_zero] at this
      rw [this, zero_smul]
    · exact h
  obtain ⟨hfin, het, hker⟩ := _root_.GlobalTheory.OActFinEt.finite_etale_act E k A act g hB hg _ hb
  refine ⟨hker, ?_⟩
  have hrank := GlobalTheory.finrank_eq_card_kernel_points_of_etale k A hB (act.act (∑ i, n i • a i))
  have hφ : (act.act (∑ i, n i • a i)).left ≫ A.hom = A.hom := Over.w _
  have hq : 1 ≤ c * K ^ 2 := Nat.one_le_iff_ne_zero.2 (mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))
  have h := hC (act.act (∑ i, n i • a i)).left hφ _ (c * K ^ 2) hq hrank (hsec n K hK hn)
  calc _ ≤ C * (c * K ^ 2) ^ g := h
    _ = C * c ^ g * K ^ (2 * g) := by ring

end GlobalTheory.OEndDegree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionConjugationInvolutiveFixedField
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

namespace GlobalTheory.CMConjInvol

theorem cm_conj_invol_fixed : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → (∀ x, σ (σ x) = x) ∧ ∀ x, σ x = x → ∃ f : F, algebraMap F E f = x :=
  fun _ _ _ _ _ _ _ _ h => ⟨GlobalTheory.HermLineZeros.conj_invol h, GlobalTheory.HermLineZeros.exists_of_fixed h⟩

end GlobalTheory.CMConjInvol
end

