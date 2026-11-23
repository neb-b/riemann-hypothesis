module

public import Mathlib
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0022
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0019
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0029
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0025
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ChartMatrices
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
open scoped Matrix

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

section Pt

variable {C O : Type} [Field C] [CommRing O] [Algebra O C] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {κ : O} {N : ℕ}
  {V Ω' : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω']

theorem pt_swap (P : HTPoint C O c κ N V Ω') (x y : V) : P.e x y = -P.e y x := by
  have h := P.alt (x + y)
  simp only [map_add (f := _), LinearMap.add_apply, P.alt, zero_add, add_zero] at h
  linear_combination h

theorem pt_tate (P : HTPoint C O c κ N V Ω') (m : Ix E N) :
    P.tate (dl m) = P.ρ (RingOfIntegers.basis E m.2) (P.t m.1) :=
  PositivityTheory.HtPt.Gd.tate_single P m.1 _

theorem pt_matrices {v : Valuation C NNReal} (hv : v.Integers O) (P : HTPoint C O c κ N V Ω') {g : ℕ}
    (bo : Basis (Fin g) O P.om) :
    ∃ (Hm : Matrix (Fin g) (Ix E N) O) (Eg : Matrix (Ix E N) (Ix E N) O),
      Fintype.card (Ix E N) = g + g ∧ Egᵀ = -Eg ∧
      (∃ Ei : Matrix (Ix E N) (Ix E N) O, Ei * Eg = 1 ∧ Hm * Ei * Hmᵀ = 0) ∧
      (∀ m m', algebraMap O C (Eg m m') = P.e (P.tate (dl m)) (P.tate (dl m'))) ∧
      ∀ m, ∃ h : P.ht (P.tate (dl m)) ∈ P.om, ∀ k, Hm k m = bo.repr ⟨_, h⟩ k := by
  classical
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI := PositivityTheory.HtPt.Gb.isFractionRing_of_integers hv
  haveI : P.om.IsFullLattice C := P.om_lat
  have hinj := hv.hom_inj
  have hsp : ⊤ ≤ Submodule.span C (Set.range fun q : Ix E N =>
      P.ρ (RingOfIntegers.basis E q.2) (P.t q.1)) := by
    rw [← Submodule.span_span_of_tower O C, ← P.free.2.2, P.free.2.1]
  let B : Basis (Ix E N) C V := Basis.mk P.free.1 hsp
  have hBt : ∀ m, P.tate (dl m) = B m := fun m => by rw [pt_tate, Basis.mk_apply]
  have hT : P.T = Submodule.span O (Set.range B) := by rw [Basis.coe_mk, ← P.free.2.2]
  have hB : ∀ q, B q ∈ P.T := fun q => by
    rw [hT]
    exact Submodule.subset_span ⟨q, rfl⟩
  haveI : FiniteDimensional C V := Module.Finite.of_basis B
  have hnd : ∀ x, (∀ y, P.e x y = 0) → x = 0 := fun x hx =>
    P.nondeg x fun y => by rw [pt_swap, hx, neg_zero]
  have hei : Function.Injective (P.e : V →ₗ[C] Module.Dual C V) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    exact hnd x fun y => by rw [hx]; rfl
  have hes := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq).symm).1 hei
  have hE : ∀ m m', ∃ r : O, algebraMap O C r = P.e (B m) (B m') := fun m m' => by
    have := hB m'
    rw [← P.perfect] at this
    exact this _ (hB m)
  choose Eg hEg using hE
  choose w hw using fun m => hes (B.coord m)
  have hwT : ∀ m, w m ∈ P.T := fun m => by
    rw [← P.perfect]
    intro x hx
    rw [pt_swap, hw]
    refine neg_mem ?_
    rw [hT] at hx
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hx
    refine ⟨a m, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smul_of_tower, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    rw [Finset.sum_eq_single m (fun b _ hb => by simp [hb]) (by simp)]
    simp [Algebra.smul_def]
  choose Ei hEi using fun m => (Submodule.mem_span_range_iff_exists_fun O).1 (hT ▸ hwT m)
  let bC := bo.extendOfIsFullLattice C
  have hbC_apply (j : Fin g) : bC j = (bo j : Ω') :=
    Basis.extendOfIsFullLattice_apply C bo j
  have hbC : ∀ (y : P.om) k, bC.repr (y : Ω') k = algebraMap O C (bo.repr y k) := fun y k => by
    have e : (y : Ω') = ∑ j, algebraMap O C (bo.repr y j) • bC j := by
      calc
        (y : Ω') = ((∑ j, bo.repr y j • bo j : P.om) : Ω') :=
          congrArg Subtype.val (bo.sum_repr y).symm
        _ = _ := by simp only [Submodule.coe_sum, Submodule.coe_smul, algebraMap_smul, hbC_apply]
    rw [e, bC.repr_sum_self]
  let Hm : Matrix (Fin g) (Ix E N) O := fun k m => bo.repr ⟨P.ht (B m), P.ht_mem _ (hB m)⟩ k
  have hHm : ∀ k m, algebraMap O C (Hm k m) = bC.repr (P.ht (B m)) k := fun k m =>
    (hbC ⟨_, P.ht_mem _ (hB m)⟩ k).symm
  refine ⟨Hm, Matrix.of Eg, ?_, ?_, ⟨Matrix.of Ei, ?_, ?_⟩, fun m m' => by rw [hBt, hBt]; exact hEg m m',
    fun m => ⟨by rw [hBt]; exact P.ht_mem _ (hB m), fun k => by simp only [Hm, hBt]⟩⟩
  · have hsurj : LinearMap.range P.ht = ⊤ := by
      rw [eq_top_iff, ← bC.span_eq, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      obtain ⟨x, -, hx⟩ := P.κ_mem _ (bo k).2
      refine ⟨(algebraMap O C κ)⁻¹ • x, ?_⟩
      rw [map_smul, hx, ← algebraMap_smul C κ, inv_smul_smul₀ P.κ_ne]
      exact (hbC_apply k).symm
    have h1 := LinearMap.finrank_range_add_finrank_ker P.ht
    rw [hsurj, finrank_top, finrank_eq_card_basis bC, finrank_eq_card_basis B, Fintype.card_fin] at h1
    have horth : LinearMap.BilinForm.orthogonal P.e (LinearMap.ker P.ht) = LinearMap.ker P.ht := by
      ext x
      rw [LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.mem_ker, P.lagr]
      refine forall_congr' fun y => ?_
      rw [LinearMap.mem_ker]
      refine imp_congr_right fun _ => ?_
      change P.e y x = 0 ↔ _
      rw [pt_swap P y x, neg_eq_zero]
    have h2 := LinearMap.BilinForm.finrank_orthogonal (B := P.e) ⟨hnd, P.nondeg⟩ (LinearMap.ker P.ht)
    rw [horth, finrank_eq_card_basis B] at h2
    omega
  · ext m m'
    apply hinj
    simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.of_apply, map_neg, hEg]
    exact pt_swap P _ _
  · ext m m'
    apply hinj
    have h := congrArg (fun f : Module.Dual C V => f (B m')) (hw m)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← hEi m, map_sum, LinearMap.sum_apply, LinearMap.map_smul_of_tower, LinearMap.smul_apply,
      Basis.coord_apply, Basis.repr_self, ← hEg] at h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum]
    simp only [Matrix.of_apply, map_mul, ← Algebra.smul_def]
    rw [h, Matrix.one_apply, Finsupp.single_apply]
    by_cases hm : m = m'
    · simp [hm]
    · simp [hm, Ne.symm hm]
  · ext k k'
    apply hinj
    let x : V := ∑ m, algebraMap O C (Hm k m) • w m
    have hx : P.e x = (bC.coord k) ∘ₗ P.ht := by
      refine B.ext fun m => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [x, map_sum, map_smul, hw, LinearMap.sum_apply, LinearMap.smul_apply, Basis.coord_apply,
        Basis.repr_self, LinearMap.comp_apply, Finsupp.single_apply]
      rw [Finset.sum_eq_single m (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp [hHm]
    have h0 : P.ht x = 0 := (P.lagr x).2 fun y hy => by rw [hx, LinearMap.comp_apply, hy, map_zero]
    have h1 := congrArg (fun z => bC.repr z k') h0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [x, ← hEi, map_sum, map_smul, LinearMap.map_smul_of_tower, Finsupp.coe_finsetSum, Finset.sum_apply,
      map_zero, Finsupp.coe_zero, Pi.zero_apply] at h1
    rw [Matrix.zero_apply, map_zero, ← h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, map_sum, map_mul, Finset.sum_mul,
        Finsupp.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    refine Finset.sum_congr rfl fun m' _ => ?_
    rw [hHm k' m', ← algebraMap_smul C (Ei m m'), map_smul, Finsupp.smul_apply, smul_eq_mul, mul_assoc]

end Pt

theorem chart_matrices {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    {E : Type} [Field E] [NumberField E] {c : E ≃+* E} {p R N : ℕ} (hR : 1 ≤ R)
    {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω)
    {C O : Type} [Field C] [CommRing O] [Algebra O C] [Algebra A O] {κ : O}
    {V Ω' : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
    [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω']
    {v : Valuation C NNReal} (hv : v.Integers O) (P : HTPoint C O c κ N V Ω')
    (ι₀ : D.om →ₛₗ[algebraMap A O] Ω') (hr : D.ReducesTo (algebraMap A O) P ι₀) :
    ∃ (g : ℕ) (io : D.om →ₛₗ[algebraMap A O] (Fin g → O)) (Hm : Matrix (Fin g) (Ix E N) O)
      (Eg : Matrix (Ix E N) (Ix E N) O),
      Submodule.span O (Set.range io) = ⊤ ∧
      (∀ f : D.om →ₛₗ[algebraMap A O] C, ∃ ev : (Fin g → C) →ₗ[C] C,
        ∀ u, ev (fun k => algebraMap O C (io u k)) = f u) ∧
      Fintype.card (Ix E N) = g + g ∧ Egᵀ = -Eg ∧
      (∃ Ei : Matrix (Ix E N) (Ix E N) O, Ei * Eg = 1 ∧ Hm * Ei * Hmᵀ = 0) ∧
      (∀ m m', Eg m m' - ((D.e (dl m) (dl m')).val : O) ∈ Ideal.span {(p : O)}) ∧
      ∀ m k, Hm k m - io ⟨D.h (dl m), D.h_mem _⟩ k ∈ Ideal.span {(p : O)} := by
  classical
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI := PositivityTheory.HtPt.Gd.free_of_fg hv P.om P.om_lat.fg
  haveI : Module.Finite O P.om := Module.Finite.iff_fg.2 P.om_lat.fg
  let bo := Module.finBasis O P.om
  have hmem : ∀ u, ι₀ u ∈ P.om := fun u => by
    rw [← hr.span_eq]
    exact Submodule.subset_span ⟨u, rfl⟩
  let ι₁ : D.om →ₛₗ[algebraMap A O] P.om := ι₀.codRestrict P.om hmem
  let io : D.om →ₛₗ[algebraMap A O] (Fin _ → O) := bo.equivFun.toLinearMap.comp ι₁
  have hio : ∀ u k, io u k = bo.repr ⟨ι₀ u, hmem u⟩ k := fun _ _ => rfl
  obtain ⟨Hm, Eg, h1, h2, h3, h4, h5⟩ := pt_matrices hv P bo
  obtain ⟨j, hj, hjr, hjι⟩ := PositivityTheory.HtPt.Gb.bc_iso A K Ω D.om C v O hv Ω' P.om ι₀
    D.om_lat D.om_proj P.om_lat hr.span_eq hr.rank_eq
  have hpR : ∀ z : O, (p : O) ^ R * z ∈ Ideal.span {(p : O)} := fun z =>
    Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ hR)
  refine ⟨_, io, Hm, Eg, ?_, fun f => ?_, h1, h2, h3, fun m m' => ?_, fun m k => ?_⟩
  · have h6 : Submodule.span O (Set.range ι₁) = ⊤ := by
      apply Submodule.map_injective_of_injective P.om.injective_subtype
      rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
      exact hr.span_eq
    have : Set.range io = bo.equivFun.toLinearMap '' Set.range ι₁ := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, h6, Submodule.map_top, LinearEquiv.range]
  · obtain ⟨jf, hjf, -⟩ := PositivityTheory.HtPt.Gb.exists_lift f
    let e : (O ⊗[A] D.om) ≃ₗ[O] P.om := (LinearEquiv.ofInjective j hj).trans (LinearEquiv.ofEq _ _ hjr)
    have he : ∀ u, e (1 ⊗ₜ u) = ⟨ι₀ u, hmem u⟩ := fun u => Subtype.ext (hjι u)
    refine ⟨Fintype.linearCombination C fun k => jf (e.symm (bo k)), fun u => ?_⟩
    rw [Fintype.linearCombination_apply, ← hjf, ← e.symm_apply_apply (1 ⊗ₜ u), he]
    conv_rhs => rw [← bo.sum_repr ⟨ι₀ u, hmem u⟩]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hio, algebraMap_smul]
  · obtain ⟨z, hz⟩ := hr.e_eq (dl m) (dl m')
    rw [hv.hom_inj ((h4 m m').trans hz), add_sub_cancel_left]
    exact hpR z
  · obtain ⟨h, hk⟩ := h5 m
    obtain ⟨y, hy, hz⟩ := hr.ht_eq (dl m)
    have : (⟨ι₀ ⟨D.h (dl m), D.h_mem _⟩, hmem _⟩ : P.om) = ⟨_, h⟩ + (p : O) ^ R • ⟨y, hy⟩ := by
      apply Subtype.ext
      rw [Submodule.coe_add, Submodule.coe_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
      exact hz
    rw [hk, hio, this, map_add (f := _), map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, sub_add_cancel_left]
    exact neg_mem (hpR _)

end PositivityTheory.Xgn.TestGroupPoint
end
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.HodgeCharacterGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.Xgn.HodgeCharacterGeneric

open Polynomial GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.HT.LatBasic TensorProduct

variable {E : Type} [Field E] [NumberField E] {K : Type} [Field K] [CharZero K]

theorem sum_emb [Fintype (E →+* K)] (h : Nat.card (E →+* K) = Module.finrank ℚ E) (x : E) :
    ∑ s : E →+* K, s x = algebraMap ℚ K (Algebra.trace ℚ E x) := by
  classical
  letI : CharZero (AlgebraicClosure K) :=
    charZero_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective
  let f : (E →+* K) → (E →ₐ[ℚ] AlgebraicClosure K) := fun s =>
    ((algebraMap K (AlgebraicClosure K)).comp s).toRatAlgHom
  have hf : Function.Injective f := by
    intro s t hst
    ext y
    have := congrArg (fun g : E →ₐ[ℚ] AlgebraicClosure K => g y) hst
    exact (algebraMap K (AlgebraicClosure K)).injective this
  have hcard : Fintype.card (E →+* K) = Fintype.card (E →ₐ[ℚ] AlgebraicClosure K) := by
    rw [AlgHom.card, ← h, Nat.card_eq_fintype_card]
  have hb : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩
  apply (algebraMap K (AlgebraicClosure K)).injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  calc ∑ s : E →+* K, algebraMap K (AlgebraicClosure K) (s x) = ∑ s, f s x := rfl
    _ = ∑ σ : E →ₐ[ℚ] AlgebraicClosure K, σ x := hb.sum_comp (fun σ => σ x)
    _ = algebraMap ℚ (AlgebraicClosure K) (Algebra.trace ℚ E x) :=
        (trace_eq_sum_embeddings (AlgebraicClosure K) (x := x)).symm
    _ = _ := by simp [eq_ratCast]

variable {V : Type} [AddCommGroup V] [Module K V]

theorem sum_eigProj [Fintype (E →+* K)] (h : Nat.card (E →+* K) = Module.finrank ℚ E)
    (ρ : 𝓞 E →+* Module.End K V) : ∑ s, eigProj ρ s = 1 := by
  classical
  set b := RingOfIntegers.basis E with hb
  have h1 : (1 : E) = ∑ j, ((b.repr 1 j : ℤ) : E) * integralBasis E j := by
    have := congrArg (algebraMap (𝓞 E) E) (b.sum_repr 1)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [integralBasis_apply, map_sum, zsmul_eq_mul] using this.symm
  have hrep : ∀ k, Algebra.trace ℚ E (dualInt E k) = ((b.repr 1 k : ℤ) : ℚ) := by
    intro k
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← mul_one (dualInt E k), h1, Finset.mul_sum, map_sum]
    simp_rw [mul_left_comm (dualInt E _), ← zsmul_eq_mul, map_zsmul, trace_dualInt]
    simp
  simp only [eigProj]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, sum_emb h, hrep]
  calc ∑ k, algebraMap ℚ K ((b.repr 1 k : ℤ) : ℚ) • ρ (b k) = ρ (∑ k, b.repr 1 k • b k) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_zsmul, map_intCast, Int.cast_smul_eq_zsmul]
    _ = 1 := by rw [b.sum_repr, map_one]

theorem isInternal [Fintype (E →+* K)] [DecidableEq (E →+* K)] (h : Nat.card (E →+* K) = Module.finrank ℚ E)
    (ρ : 𝓞 E →+* Module.End K V) : DirectSum.IsInternal (HT.eigSp ρ) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · intro s
    rw [Submodule.disjoint_def]
    intro x hx hy
    have hk : (⨆ j, ⨆ (_ : j ≠ s), HT.eigSp ρ j) ≤ LinearMap.ker (eigProj ρ s) :=
      iSup₂_le fun j hj y hy => eigProj_of_ne hj.symm hy
    rw [← eigProj_of_mem hx]
    exact hk hy
  · rw [eq_top_iff]
    intro x _
    have : x = ∑ s, eigProj ρ s x := by
      rw [← LinearMap.sum_apply, sum_eigProj h]; rfl
    rw [this]
    exact Submodule.sum_mem _ fun s _ => Submodule.mem_iSup_of_mem s (eigProj_mem ρ s x)

theorem charpoly_eq [Fintype (E →+* K)] [FiniteDimensional K V]
    (h : Nat.card (E →+* K) = Module.finrank ℚ E) (ρ : 𝓞 E →+* Module.End K V) :
    (∀ a : 𝓞 E, (ρ a).charpoly =
      ∏ s : E →+* K, (X - Polynomial.C (s (a : E))) ^ Module.finrank K (HT.eigSp ρ s)) ∧
    ∑ s : E →+* K, Module.finrank K (HT.eigSp ρ s) = Module.finrank K V := by
  classical
  let b := (isInternal h ρ).collectedBasis fun s => Module.finBasis K (HT.eigSp ρ s)
  have hb : ∀ i, b i ∈ HT.eigSp ρ i.1 := fun i => (isInternal h ρ).collectedBasis_mem _ i
  refine ⟨fun a => ?_, ?_⟩
  · have hm : LinearMap.toMatrix b b (ρ a) = Matrix.diagonal fun i => i.1 (a : E) := by
      ext i j
      rw [LinearMap.toMatrix_apply, mem_eigSp.1 (hb j) a, map_smul, b.repr_self, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Finsupp.single_apply, Ne.symm hij]
    rw [← LinearMap.charpoly_toMatrix _ b, hm, Matrix.charpoly_diagonal, Fintype.prod_sigma]
    simp
  · rw [Module.finrank_eq_card_basis b]
    simp

theorem reg_ne (σ : E →+* K) : eigProj (regAct K E) σ 1 ≠ 0 := by
  classical
  intro h0
  have hne : Nonempty (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    have := sum_dualInt_mul (E := E)
    simp [Finset.univ_eq_empty] at this
  obtain ⟨k⟩ := hne
  simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, regAct_basis] at h0
  have hk := Fintype.linearIndependent_iff.mp
    (Algebra.TensorProduct.basis K (RingOfIntegers.basis E)).linearIndependent _ h0 k
  have hd : dualInt E k = 0 := by
    rw [← map_zero σ] at hk
    exact σ.injective hk
  have ht := trace_dualInt (E := E) k k
  simp [hd] at ht

theorem charpoly_lmul [Fintype (E →+* K)] (h : Nat.card (E →+* K) = Module.finrank ℚ E) (a : 𝓞 E) :
    (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K) =
      ∏ s : E →+* K, (X - Polynomial.C (s (a : E))) := by
  classical
  have hfr : Module.finrank K (K ⊗[ℤ] 𝓞 E) = Module.finrank ℚ E := by
    rw [Module.finrank_baseChange, RingOfIntegers.rank]
  obtain ⟨hc, hs⟩ := charpoly_eq h (regAct K E)
  have hpos : ∀ s : E →+* K, 1 ≤ Module.finrank K (HT.eigSp (regAct K E) s) := fun s =>
    Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨_, eigProj_mem _ s 1⟩, fun h0 => reg_ne s (congrArg Subtype.val h0)⟩
  have hone : ∀ s, Module.finrank K (HT.eigSp (regAct K E) s) = 1 := by
    by_contra hn
    push_neg at hn
    obtain ⟨t, ht⟩ := hn
    have hlt : ∑ _s : E →+* K, 1 < ∑ s, Module.finrank K (HT.eigSp (regAct K E) s) :=
      Finset.sum_lt_sum (fun s _ => hpos s)
        ⟨t, Finset.mem_univ _, lt_of_le_of_ne (hpos t) (Ne.symm ht)⟩
    rw [hs, hfr, ← h, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hlt
    simp [Nat.card_eq_fintype_card] at hlt
  have hbc : regAct K E a = (Algebra.lmul ℤ (𝓞 E) a).baseChange K := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext c y
    simp [regAct]
  rw [← algebraMap_int_eq, ← LinearMap.charpoly_baseChange, ← hbc, hc a]
  simp [hone]

theorem charpoly_rhoH {O : Type} [CommRing O] [StarRing O] {d : ℕ} (B : Germ.FB K d O) (a : O) :
    (rhoH B a).charpoly = (rho B a).charpoly * (rho B (star a)).charpoly := by
  classical
  let b := (Pi.basisFun K (Fin d)).prod (Pi.basisFun K (Fin d))
  have hM : LinearMap.toMatrix b b (rhoH B a) =
      Matrix.fromBlocks (rho B a) 0 (-Matrix.transpose (bil (B.ad a) 1 1))
        (Matrix.transpose (rho B (star a))) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [b, LinearMap.toMatrix_apply, rhoH, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  rw [← LinearMap.charpoly_toMatrix (rhoH B a) b, hM, Matrix.charpoly_fromBlocks_zero₁₂,
    Matrix.charpoly_transpose]

end PositivityTheory.Xgn.HodgeCharacterGeneric

theorem PositivityTheory.Xgn.hodge_character_generic : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (K : Type) [Field K] [CharZero K] (d r : ℕ) (B : Germ.FB K d (𝓞 E)) (ρ : 𝓞 E →+* Module.End K (Fin d → K)), (∀ a v, ρ a v = (rho B a).mulVec v) → Nat.card (E →+* K) = Module.finrank ℚ E → (∀ s s' : E →+* K, (∀ a : 𝓞 E, s' (a : E) = s ((star a : 𝓞 E) : E)) → Module.finrank K (HT.eigSp ρ s) + Module.finrank K (HT.eigSp ρ s') = r) → HChar B r := by
  classical
  intro E _ _ _ K _ _ d r B ρ hρ h hdim
  have hinj : ∀ s : E →+* K,
      Function.Injective (s.comp ((algebraMap (𝓞 E) E).comp (starRingEnd (𝓞 E)))) :=
    fun s x y hxy => star_injective (IsFractionRing.injective (𝓞 E) E (s.injective hxy))
  let φ : (E →+* K) → (E →+* K) := fun s => IsFractionRing.lift (hinj s)
  have hφ : ∀ s (x : 𝓞 E), φ s (algebraMap (𝓞 E) E x) = s (algebraMap (𝓞 E) E (star x)) :=
    fun s x => IsFractionRing.lift_algebraMap (hinj s) x
  have hφφ : ∀ s, φ (φ s) = s := fun s =>
    IsFractionRing.ringHom_ext (A := 𝓞 E) fun x => by rw [hφ, hφ, star_star]
  have hbij : Function.Bijective φ := Function.Involutive.bijective hφφ
  have hsum : ∀ s, Module.finrank K (HT.eigSp ρ s) + Module.finrank K (HT.eigSp ρ (φ s)) = r :=
    fun s => hdim s (φ s) fun a => hφ s a
  have hrho : ∀ a, (rho B a).charpoly = (ρ a).charpoly := by
    intro a
    rw [← Matrix.charpoly_toLin']
    congr 1
    exact LinearMap.ext fun v => by rw [Matrix.toLin'_apply, hρ]
  obtain ⟨hc, -⟩ := PositivityTheory.Xgn.HodgeCharacterGeneric.charpoly_eq h ρ
  intro a
  rw [PositivityTheory.Xgn.HodgeCharacterGeneric.charpoly_rhoH, hrho, hrho, hc, hc,
    PositivityTheory.Xgn.HodgeCharacterGeneric.charpoly_lmul h, ← Finset.prod_pow]
  have h2 : ∏ s : E →+* K, (Polynomial.X - Polynomial.C (s ((star a : 𝓞 E) : E))) ^
        Module.finrank K (HT.eigSp ρ s) =
      ∏ s : E →+* K, (Polynomial.X - Polynomial.C (s (a : E))) ^
        Module.finrank K (HT.eigSp ρ (φ s)) := by
    symm
    refine Fintype.prod_bijective φ hbij _ _ fun s => ?_
    have := hφ s (star a)
    rw [star_star] at this
    simp only [this]
  rw [h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [← pow_add, hsum s]
end

