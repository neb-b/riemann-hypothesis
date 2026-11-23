module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0028
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsProperIntegralModel
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializesOfSpecializes
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar TopologicalSpace

theorem isOpen_of_isClosed_of_generizing {α : Type*} [TopologicalSpace α] [NoetherianSpace α] [QuasiSober α]
    (S : Set α) (hc : IsClosed S) (hs : ∀ x y : α, x ⤳ y → y ∈ S → x ∈ S) : IsOpen S := by
  have hfin : (irreducibleComponents α).Finite := NoetherianSpace.finite_irreducibleComponents
  have hT : IsClosed (⋃₀ {C ∈ irreducibleComponents α | Disjoint C S}) := by
    rw [Set.sUnion_eq_biUnion]
    exact (hfin.subset fun C (h : C ∈ {C ∈ irreducibleComponents α | Disjoint C S}) => h.1).isClosed_biUnion
      fun C h => isClosed_of_mem_irreducibleComponents C h.1
  have e : Sᶜ = ⋃₀ {C ∈ irreducibleComponents α | Disjoint C S} := by
    ext x
    constructor
    · intro hx
      refine ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents x, ?_⟩,
        mem_irreducibleComponent⟩
      rw [Set.disjoint_left]
      intro s hsC hsS
      have hC := isIrreducible_irreducibleComponent (x := x)
      have hcl : IsClosed (irreducibleComponent x) := isClosed_irreducibleComponent
      obtain ⟨c, hcg⟩ := QuasiSober.sober hC hcl
      have hcs : c ∈ S := hs c s (hcg.specializes hsC) hsS
      exact hx (hc.closure_subset_iff.2 (Set.singleton_subset_iff.2 hcs) (by
        rw [hcg.def]; exact mem_irreducibleComponent))
    · rintro ⟨C, ⟨-, hd⟩, hx⟩ hxS
      exact Set.disjoint_left.1 hd hx hxS
  rw [← isClosed_compl_iff, e]
  exact hT

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem genPt_specializes_of_specializes (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) {p y : X}
    (hp : genPt ξ ⤳ p) (hy : y ⤳ p) : genPt ξ ⤳ y := by
  haveI := CptInh.dom ξ h ⟨p, hp⟩
  haveI : IsDomain (X.presheaf.stalk p) := this
  obtain ⟨a, ha⟩ : genPt ξ ∈ Set.range (X.fromSpecStalk p) := by
    rwa [Scheme.range_fromSpecStalk]
  obtain ⟨b, hb⟩ : y ∈ Set.range (X.fromSpecStalk p) := by
    rwa [Scheme.range_fromSpecStalk]
  let o : Spec (CommRingCat.of (X.presheaf.stalk p)) :=
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (X.presheaf.stalk p))
  have hoc : ∀ c : Spec (CommRingCat.of (X.presheaf.stalk p)), o ⤳ c := fun c =>
    (PrimeSpectrum.le_iff_specializes (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (X.presheaf.stalk p)) c).1 bot_le
  have h1 : X.fromSpecStalk p o ⤳ genPt ξ := by
    rw [← ha]; exact (hoc a).map (X.fromSpecStalk p).continuous
  have h2 : X.fromSpecStalk p o ⤳ y := by
    rw [← hb]; exact (hoc b).map (X.fromSpecStalk p).continuous
  rwa [CptInh.nogen ξ h _ h1] at h2

theorem isOpen_closure_genPt (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X] (h : IsCptGen ξ) :
    IsOpen (closure {genPt ξ}) := by
  rw [isOpen_iff_forall_mem_open]
  intro p hp
  obtain ⟨W, hpW⟩ : ∃ W : X.affineOpens, p ∈ W.1 := by
    obtain ⟨W, hW, hpW, -⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := ⊤) trivial
    exact ⟨⟨W, hW⟩, hpW⟩
  haveI : IsNoetherianRing Γ(X, W.1) := IsLocallyNoetherian.component_noetherian W
  haveI : NoetherianSpace (W.1 : X.Opens) := noetherianSpace_of_isAffineOpen W.1 W.2
  haveI : QuasiSober (W.1 : X.Opens) := inferInstanceAs (QuasiSober (W.1 : X.Opens).toScheme)
  have ho : IsOpen (Subtype.val ⁻¹' (closure {genPt ξ}) : Set (W.1 : X.Opens)) :=
    isOpen_of_isClosed_of_generizing _ (isClosed_closure.preimage continuous_subtype_val)
      fun x y hxy hy => by
        have hy' : genPt ξ ⤳ y.1 := specializes_iff_mem_closure.2 hy
        exact specializes_iff_mem_closure.1
          (genPt_specializes_of_specializes ξ h hy' (hxy.map continuous_subtype_val))
  refine ⟨Subtype.val '' (Subtype.val ⁻¹' (closure {genPt ξ}) : Set (W.1 : X.Opens)), ?_,
    W.1.isOpen.isOpenMap_subtype_val _ ho, ⟨⟨p, hpW⟩, hp, rfl⟩⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hx

theorem cpt_open_integral : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    [IsLocallyNoetherian X], IsCptGen ξ → ∃ U : X.Opens, (∀ q : X, q ∈ U ↔ genPt ξ ⤳ q) ∧
      IsClosed (U : Set X) ∧ IsIntegral U.toScheme := by
  intro X Ω _ ξ _ h
  let U : X.Opens := ⟨closure {genPt ξ}, isOpen_closure_genPt ξ h⟩
  have hU : ∀ q : X, q ∈ U ↔ genPt ξ ⤳ q := fun q => specializes_iff_mem_closure.symm
  refine ⟨U, hU, isClosed_closure, ?_⟩
  haveI : IrreducibleSpace U.toScheme :=
    Subtype.irreducibleSpace (isIrreducible_singleton (x := genPt ξ)).closure
  haveI : ∀ x : U.toScheme, _root_.IsReduced (U.toScheme.presheaf.stalk x) := fun x => by
    haveI := CptInh.dom ξ h ⟨U.ι x, (hU _).1 x.2⟩
    have e := (asIso (U.ι.stalkMap x)).commRingCatIsoToRingEquiv
    exact isReduced_of_injective e.symm.toRingHom e.symm.injective
  haveI : IsReduced U.toScheme := isReduced_of_isReduced_stalk _
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagFieldChange
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.GenericColumns

theorem det_eq_one {K : Type*} [Field K] {n : ℕ} (u : Matrix (Fin n) (Fin n) K)
    (h1 : ∀ k, u k k = 1) (h0 : ∀ l k, l < k → u l k = 0) : u.det = 1 := by
  rw [Matrix.det_of_lowerTriangular u (fun i j hij => h0 _ _ hij)]
  simp [h1]

theorem linearIndependent_cols {K M : Type*} [Field K] [AddCommGroup M] [Module K M] {n : ℕ}
    (u : Matrix (Fin n) (Fin n) K) (h1 : ∀ k, u k k = 1) (h0 : ∀ l k, l < k → u l k = 0)
    (v : Fin n → M) (hv : LinearIndependent K v) :
    LinearIndependent K fun k => ∑ l, u l k • v l := by
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro g hg
  have hz : ∀ l, ∑ k, u l k * g k = 0 := by
    apply hv (fun l => ∑ k, u l k * g k)
    rw [← hg]
    simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by rw [mul_comm]
  have hm : u.mulVec g = 0 := funext hz
  have hg0 := Matrix.eq_zero_of_mulVec_eq_zero (by rw [det_eq_one u h1 h0]; exact one_ne_zero) hm
  intro i
  exact congrFun hg0 i

theorem span_cols {K M : Type*} [Field K] [AddCommGroup M] [Module K M] {n : ℕ}
    (u : Matrix (Fin n) (Fin n) K) (h1 : ∀ k, u k k = 1) (h0 : ∀ l k, l < k → u l k = 0)
    (v : Fin n → M) :
    Submodule.span K (Set.range fun k => ∑ l, u l k • v l) = Submodule.span K (Set.range v) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨m, rfl⟩
    have hu : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv u (by rw [det_eq_one u h1 h0]; exact isUnit_one)
    have hvm : v m = ∑ k, u⁻¹ k m • ∑ l, u l k • v l := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      have hl : ∀ l, ∑ k, (u⁻¹ k m * u l k) • v l = (if l = m then (1 : K) else 0) • v l := by
        intro l
        rw [← Finset.sum_smul]
        congr 1
        have := congrFun (congrFun hu l) m
        rw [Matrix.mul_apply, Matrix.one_apply] at this
        rw [← this]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      simp [hl]
    show v m ∈ _
    rw [hvm]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem genU_diag (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) (k : Fin (r s)) :
    genU Ω r s k k = 1 := by
  simp [genU]

theorem genU_zero (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) (l k : Fin (r s)) (h : l < k) :
    genU Ω r s l k = 0 := by
  have h1 : ¬ k < l := not_lt.2 h.le
  have h2 : l ≠ k := h.ne
  simp [genU, h1, h2]

theorem genU_gen (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (q : GenIx r) :
    genU Ω r q.1 q.2.1.1 q.2.1.2 =
      algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q) := by
  obtain ⟨s, ⟨⟨l, k⟩, h⟩⟩ := q
  exact dif_pos h

theorem algebraicIndependent_gen (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) :
    AlgebraicIndependent Ω (fun q : GenIx r =>
      algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q)) :=
  (MvPolynomial.algebraicIndependent_X (GenIx r) Ω).map'
    (f := IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r))
    (IsFractionRing.injective _ _)

theorem algebraicIndependent_comp {Ω₀ Ω K I : Type} [Field Ω₀] [Field Ω] [Field K] [Algebra Ω K]
    (fn : Ω₀ →+* Ω) {x : I → K} (hx : AlgebraicIndependent Ω x) :
    letI := ((algebraMap Ω K).comp fn).toAlgebra;
    AlgebraicIndependent Ω₀ x := by
  letI a1 : Algebra Ω₀ Ω := fn.toAlgebra
  letI a2 : Algebra Ω₀ K := ((algebraMap Ω K).comp fn).toAlgebra
  haveI : IsScalarTower Ω₀ Ω K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact hx.restrictScalars (R := Ω₀) (K := Ω) fn.injective

theorem adjoin_entries {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] (fn : Ω₀ →+* Ω) {S : Type} (r : S → ℕ) :
    letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra;
    IntermediateField.adjoin Ω₀
        (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => genU Ω r q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin Ω₀ (Set.range fun q : GenIx r =>
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q)) := by
  letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨⟨s, l, k⟩, rfl⟩
    show genU Ω r s l k ∈ _
    by_cases h : k < l
    · have := genU_gen Ω r ⟨s, ⟨(l, k), h⟩⟩
      exact this ▸ IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩
    · by_cases e : l = k
      · subst e
        rw [genU_diag]
        exact one_mem _
      · rw [genU_zero Ω r s l k (lt_of_le_of_ne (not_lt.1 h) e)]
        exact zero_mem _
  · refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨q, rfl⟩
    show algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q) ∈ _
    rw [← genU_gen]
    exact IntermediateField.subset_adjoin _ _ ⟨⟨q.1, q.2.1.1, q.2.1.2⟩, rfl⟩

theorem isGenericFlag_columns : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (fn : Ω₀ →+* Ω) (S : Type) (r : S → ℕ) (d : ℕ), 0 < d → (letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra; Module.finrank (IntermediateField.adjoin Ω₀ (Set.range fun q : GenIx r => algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q))) (GenField Ω r) = d) → ∀ (E₀ E' : Type) [AddCommGroup E₀] [Module Ω₀ E₀] [AddCommGroup E'] [Module (GenField Ω r) E'] (j : E₀ →+ E') (V₀ : S → Submodule Ω₀ E₀) (c : ∀ s, Fin (r s) → E₀), (∀ s, LinearIndependent Ω₀ (c s) ∧ Submodule.span Ω₀ (Set.range (c s)) = V₀ s) → (∀ (a : Ω₀) e, j (a • e) = algebraMap Ω (GenField Ω r) (fn a) • j e) → (∀ s, LinearIndependent (GenField Ω r) fun k => j (c s k)) → (∀ s, Submodule.span (GenField Ω r) (Set.range fun k => ∑ l, genU Ω r s l k • j (c s l)) = Submodule.span (GenField Ω r) (Set.range fun k => j (c s k))) ∧ (letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra; IsGenericFlag (Ω' := GenField Ω r) j V₀ (fun s k => ∑ l, genU Ω r s l k • j (c s l)) d) := by
  intro Ω₀ Ω _ _ fn S r d hd hdeg E₀ E' _ _ _ _ j V₀ c hc hj hli
  refine ⟨fun s => span_cols _ (genU_diag Ω r s) (genU_zero Ω r s) _, ?_⟩
  letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra
  refine ⟨c, genU Ω r, hc, hj, hli,
    fun s => linearIndependent_cols _ (genU_diag Ω r s) (genU_zero Ω r s) _ (hli s),
    genU_diag Ω r, genU_zero Ω r, fun _ _ => rfl, ?_, hd, ?_⟩
  · have h := algebraicIndependent_comp fn (algebraicIndependent_gen Ω r)
    have he : (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} =>
        genU Ω r q.1 q.2.1.1 q.2.1.2) = fun q : GenIx r =>
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q) :=
      funext (genU_gen Ω r)
    rw [he]
    exact h
  · rw [adjoin_entries fn r]
    exact hdeg

end GlobalTheory.CompanionTheory.Ar.FlagBun.GenericColumns
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagOverGenericField
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {S : Type} {r : S → ℕ}

theorem genU_diag (s : S) (k : Fin (r s)) : genU Ω r s k k = 1 := by
  simp [genU]

theorem genU_above (s : S) (l k : Fin (r s)) (h : l < k) : genU Ω r s l k = 0 := by
  have h1 : ¬ k < l := not_lt.mpr h.le
  simp [genU, h1, h.ne]

theorem genU_below (s : S) (l k : Fin (r s)) (h : k < l) :
    genU Ω r s l k = algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r)
      (MvPolynomial.X ⟨s, ⟨(l, k), h⟩⟩) := by
  simp only [genU, dif_pos h]

theorem genU_det (s : S) : (genU Ω r s).det = 1 := by
  have hlow : (genU Ω r s).IsLowerTriangular := by
    intro i j hij
    exact genU_above s i j (by simpa using hij)
  rw [Matrix.det_of_isLowerTriangular _ hlow]
  exact Finset.prod_eq_one fun i _ => genU_diag s i

theorem genField_adjoin_eq_top :
    IntermediateField.adjoin Ω
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => genU Ω r q.1 q.2.1 q.2.2) = ⊤ := by
  set K := IntermediateField.adjoin Ω
    (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => genU Ω r q.1 q.2.1 q.2.2) with hK
  have hX : ∀ i : GenIx r,
      algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X i) ∈ K := by
    intro i
    obtain ⟨s, ⟨⟨l, k⟩, h⟩⟩ := i
    apply IntermediateField.subset_adjoin
    exact ⟨⟨s, (l, k)⟩, genU_below s l k h⟩
  have hP : ∀ p : MvPolynomial (GenIx r) Ω,
      algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) p ∈ K := by
    intro p
    refine MvPolynomial.induction_on
      (motive := fun p => algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) p ∈ K) p ?_ ?_ ?_
    · intro a
      have h1 := IsScalarTower.algebraMap_apply Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r) a
      rw [MvPolynomial.algebraMap_eq] at h1
      rw [← h1]
      exact IntermediateField.algebraMap_mem K a
    · intro p q hp hq
      rw [map_add (f := _)]
      exact add_mem hp hq
    · intro p n hp
      rw [map_mul]
      exact mul_mem hp (hX n)
  refine eq_top_iff.mpr fun z _ => ?_
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (GenIx r) Ω) z
  exact div_mem (hP a) (hP b)

theorem linearIndependent_one_tmul {ι : Type} {v : ι → E} (hv : LinearIndependent Ω v) :
    LinearIndependent (GenField Ω r)
      fun k => TensorProduct.mk Ω (GenField Ω r) E 1 (v k) := by
  simpa only [TensorProduct.mk_apply] using
    Module.Flat.linearIndependent_one_tmul (S := GenField Ω r) hv

theorem genB_linearIndependent (c : ∀ s, Fin (r s) → E) (s : S)
    (h : LinearIndependent (GenField Ω r)
      fun k => TensorProduct.mk Ω (GenField Ω r) E 1 (c s k)) :
    LinearIndependent (GenField Ω r) (genB (Ω := Ω) c s) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg
  have hz : ∀ l, ∑ k, genU Ω r s l k * g k = 0 := by
    refine h (fun l => ∑ k, genU Ω r s l k * g k) ?_
    rw [← hg]
    simp only [genB, Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by rw [mul_comm]
  have hv : Matrix.mulVec (genU Ω r s) g = 0 := by
    ext l
    exact hz l
  have hU : IsUnit (genU Ω r s).det := by
    rw [genU_det]
    exact isUnit_one
  have hg0 : g = 0 := by
    calc g = Matrix.mulVec ((genU Ω r s)⁻¹ * genU Ω r s) g := by
          rw [Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec]
      _ = Matrix.mulVec (genU Ω r s)⁻¹ (Matrix.mulVec (genU Ω r s) g) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hv, Matrix.mulVec_zero]
  intro k
  simp [hg0]

theorem genB_isGenericFlag : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (S : Type)
    (r : S → ℕ) (V : S → Submodule Ω E) (c : ∀ s, Fin (r s) → E),
    (∀ s, LinearIndependent Ω (c s) ∧ Submodule.span Ω (Set.range (c s)) = V s) →
    IsGenericFlag (Ω' := GenField Ω r) (TensorProduct.mk Ω (GenField Ω r) E 1).toAddMonoidHom V (genB c) 1 := by
  intro Ω hΩ E hE hEm S r V c hc
  unfold IsGenericFlag
  have hli : ∀ σ, LinearIndependent (GenField Ω r)
      fun k => TensorProduct.mk Ω (GenField Ω r) E 1 (c σ k) :=
    fun σ => linearIndependent_one_tmul (r := r) (hc σ).1
  refine ⟨c, genU Ω r, hc, ?_, fun σ => hli σ, fun σ => genB_linearIndependent c σ (hli σ),
    fun σ k => genU_diag σ k, fun σ l k h => genU_above σ l k h, fun σ i => rfl, ?_, Nat.one_pos, ?_⟩
  · intro a e
    simp only [LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply]
    rw [TensorProduct.tmul_smul, algebraMap_smul]
  · have hai : AlgebraicIndependent Ω (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} =>
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q)) :=
      (MvPolynomial.algebraicIndependent_X (GenIx r) Ω).map'
        (f := IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r))
        (IsFractionRing.injective (MvPolynomial (GenIx r) Ω) (GenField Ω r))
    have hfam : (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} =>
        genU Ω r q.1 q.2.1.1 q.2.1.2) =
        fun q => algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q) :=
      funext fun q => genU_below q.1 q.2.1.1 q.2.1.2 q.2.2
    rw [hfam]
    exact hai
  · rw [genField_adjoin_eq_top]
    exact IntermediateField.finrank_top

end GlobalTheory.CompanionTheory.Ar.FlagBun
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermStalkClosedPointToBaseChange
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.PullReg

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {Ω' : Type} [Field Ω']

theorem germ_stalkClosedPointTo_baseChange (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω →+* Ω')
    (ζ : Spec (CommRingCat.of Ω') ⟶ X) (hζ : ζ = Spec.map (CommRingCat.ofHom i) ≫ ξ) (U : X.Opens)
    (hU : ζ (IsLocalRing.closedPoint (CommRingCat.of Ω')) ∈ U) (hU' : genPt ξ ∈ U) :
    X.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo ζ =
      X.presheaf.germ U (genPt ξ) hU' ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i := by
  have e : ζ = Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫
      X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω)) := by
    rw [hζ, Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have hl : IsLocalHom (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i).hom := by
    refine ⟨fun a ha => ?_⟩
    have h1 : IsUnit (i ((Scheme.stalkClosedPointTo ξ).hom a)) := ha
    have h2 : IsUnit ((Scheme.stalkClosedPointTo ξ).hom a : Ω) :=
      isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at h1
    exact isUnit_of_map_unit (Scheme.stalkClosedPointTo ξ).hom a h2
  subst e
  exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk _ U hU

theorem stalkMap_comp_genMap {X' : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'} (hD : Dominates ξ' ξ f i)
    (p' : Cpt ξ') (h : genPt ξ ⤳ f p'.1) (s : X.presheaf.stalk (f p'.1)) :
    genMap ξ' p' ((f.stalkMap p'.1).hom s) = i (genMap ξ ⟨f p'.1, h⟩ s) := by
  have key : f.stalkMap p'.1 ≫ X'.presheaf.stalkSpecializes p'.2 ≫ Scheme.stalkClosedPointTo ξ' =
      X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i := by
    refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
    have hg : genPt ξ ∈ U := h.mem_open U.2 hU
    have hg' : (ξ' ≫ f) (IsLocalRing.closedPoint (CommRingCat.of Ω')) ∈ U := by
      have : (ξ' ≫ f) (IsLocalRing.closedPoint (CommRingCat.of Ω')) = genPt ξ :=
        (Scheme.Hom.comp_apply ξ' f _).trans hD.map_genPt
      rw [this]; exact hg
    have e := germ_stalkClosedPointTo_baseChange ξ i (ξ' ≫ f) hD U hg' hg
    rw [Scheme.stalkClosedPointTo_comp] at e
    have e3 : f.stalkMap p'.1 ≫ X'.presheaf.stalkSpecializes p'.2 ≫ Scheme.stalkClosedPointTo ξ' =
        X.presheaf.stalkSpecializes (p'.2.map f.continuous) ≫ f.stalkMap (genPt ξ') ≫
          Scheme.stalkClosedPointTo ξ' :=
      (Scheme.Hom.stalkSpecializes_stalkMap_assoc f _ _ p'.2 _).symm
    rw [e3, TopCat.Presheaf.germ_stalkSpecializes_assoc, TopCat.Presheaf.germ_stalkSpecializes_assoc]
    exact e
  exact congrArg (fun φ => φ.hom s) key

end GlobalTheory.CompanionTheory.Ar.Flat.PullReg

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem pull_reg_and_gen : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0})
    (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'),
    Dominates ξ' ξ f i → ∀ p' : Cpt ξ', ∃ h : genPt ξ ⤳ f p'.1,
      (∀ a ∈ regAt ξ ⟨f p'.1, h⟩, i a ∈ regAt ξ' p') ∧
        ∀ (L : Lat ξ Ω) (t : Ω), L.IsGenAt ⟨f p'.1, h⟩ t →
          (L.pull ξ' f i.toAddMonoidHom).IsGenAt p' (i t) := by
  intro X Ω _ ξ X' Ω' _ ξ' f i hD p'
  have h := hD.specializes p'
  have hreg : ∀ a ∈ regAt ξ ⟨f p'.1, h⟩, i a ∈ regAt ξ' p' := by
    rintro _ ⟨s, rfl⟩
    exact ⟨_, PullReg.stalkMap_comp_genMap hD p' h s⟩
  refine ⟨h, hreg, fun L t ht => ⟨(map_ne_zero i).2 ht.1, ?_⟩⟩
  rw [Lat.pull_apply L hD]
  have hL : L ⟨f p'.1, hD.specializes p'⟩ = Submodule.span (regAt ξ ⟨f p'.1, h⟩) {t} := ht.2
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    have he' : e ∈ Submodule.span (regAt ξ ⟨f p'.1, h⟩) {t} := by
      rw [← hL]; exact he
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 he'
    refine Submodule.mem_span_singleton.2 ⟨⟨i r, hreg _ r.2⟩, ?_⟩
    show i (r : Ω) * i t = i ((r : Ω) * t)
    rw [map_mul]
  · rw [Submodule.span_singleton_le_iff_mem]
    refine Submodule.subset_span ⟨t, ?_, rfl⟩
    show t ∈ (L ⟨f p'.1, hD.specializes p'⟩ : Set Ω)
    rw [hL]
    exact Submodule.mem_span_singleton_self t

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalIndexAtSinglePlaceStatement
section
open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_index_at_single_place : ∀ (L : Type) [Field L] [NumberField L] (W : Type) [AddCommGroup W] [Module (𝓞 L) W] (v : FinitePlace L) (A B : Submodule (𝓞 L) W), B ≤ A → B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0 → (∀ w : FinitePlace L, w ≠ v → locAt w A = locAt w B) → (locAt v B).toAddSubgroup.relIndex (locAt v A).toAddSubgroup = B.toAddSubgroup.relIndex A.toAddSubgroup := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.LocIndex.relIndex_locAt | exact GlobalTheory.CompanionTheory.Ar.Cusp.LocIndex.relIndex_locAt | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.LocIndex.relIndex_locAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModelNonempty
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem nonempty_pModel_of_chart : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ]
    (x : κ → Ω), (∃ c, x c ≠ 0 ∧ ∀ a : Ω, ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, a = u / v) →
    Nonempty (PModel o x) := by
  intro o _ Ω _ _ κ _ x ⟨c, hc, h⟩
  have h' : ∀ a : Ω, ∃ g ∈ Algebra.adjoin o (Set.range fun j => x j / x c),
      ∃ k ∈ Algebra.adjoin o (Set.range fun j => x j / x c), k ≠ 0 ∧ a = g / k := by
    intro a
    obtain ⟨u, hu, v, hv, rfl⟩ := h a
    by_cases hv0 : v = 0
    · exact ⟨0, zero_mem _, 1, one_mem _, one_ne_zero, by simp [hv0]⟩
    · exact ⟨u, hu, v, hv, hv0, rfl⟩
  obtain ⟨X, ξ, s, tie, all, -, -, hover⟩ := _root_.GlobalTheory.CompanionTheory.Ar.exists_cl_scheme Ω o κ x c hc h'
  exact ⟨{ X := X, ξ := ξ, s := s, hover := hover, all := all, tie := tie }⟩

end GlobalTheory.CompanionTheory.Ar
end

