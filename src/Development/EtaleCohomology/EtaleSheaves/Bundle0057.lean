module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0048
public import Development.EtaleCohomology.EtaleSheaves.Bundle0050

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafLocalExtendPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafLocalExtendPf

lemma specMap_comp_fromSpecStalkOfMem {C : Scheme.{0}} (U : C.Opens) {x y : C} (h : x ⤳ y)
    (hyU : y ∈ U) (hxU : x ∈ U) :
    Spec.map (C.presheaf.stalkSpecializes h) ≫ U.fromSpecStalkOfMem y hyU =
      U.fromSpecStalkOfMem x hxU := by
  rw [← cancel_mono U.ι]
  simp only [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

lemma existence_of_isProper {X S : Scheme.{0}} (p : X ⟶ S) [IsProper p] :
    ValuativeCriterion.Existence p := by
  have : (ValuativeCriterion.Existence ⊓ @QuasiCompact) p := by
    rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
  exact this.1

theorem LeafLocalExtend_of : LateralTheory.E.LeafExtendCut.LeafLocalExtend := by
  intro C X S _ sC p _ x y hx h hv hfr ψ hψ
  have hdom : IsDomain (C.presheaf.stalk y) := inferInstance
  let alg : Algebra (C.presheaf.stalk y) (C.presheaf.stalk x) :=
    (C.presheaf.stalkSpecializes h).hom.toAlgebra
  let fld : Field (C.presheaf.stalk x) := IsFractionRing.toField (C.presheaf.stalk y)
  have hsq : CommSq ψ (Spec.map (C.presheaf.stalkSpecializes h)) p (C.fromSpecStalk y ≫ sC) :=
    ⟨by rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, hψ]⟩
  let sq : ValuativeCommSq p :=
    @ValuativeCommSq.mk _ _ p (C.presheaf.stalk y) _ hdom hv (C.presheaf.stalk x) fld alg hfr
      ψ (C.fromSpecStalk y ≫ sC) hsq
  obtain ⟨⟨l, hl1, hl2⟩⟩ := (existence_of_isProper p sq).exists_lift
  change Spec.map (C.presheaf.stalkSpecializes h) ≫ l = ψ at hl1
  change l ≫ p = C.fromSpecStalk y ≫ sC at hl2
  obtain ⟨U, hyU, f, hf1, hf2⟩ := spread_out_of_isGermInjective' sC p l hl2
  have hxU : x ∈ U := h.mem_open U.2 hyU
  refine ⟨U, hyU, hxU, f, ?_, hf2⟩
  rw [← hl1, hf1, ← Category.assoc, specMap_comp_fromSpecStalkOfMem U h hyU hxU]

end LateralTheory.E.LeafLocalExtendPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafNegPf
section
noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafNegPf

theorem chains_isZero (R : Type) [CommRing R] (E : Spc) (n : ℤ) (hn : 0 < n) :
    IsZero (((chains R).obj E).X n) := by
  change IsZero ((((chainsN R).obj E).extend ComplexShape.embeddingDownNat).X n)
  apply HomologicalComplex.isZero_extend_X
  intro i
  change -(i : ℤ) ≠ n
  omega

theorem res_isZero (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (hn : n < 0) :
    IsZero ((res R F).X n) := by
  unfold res
  exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)

theorem cone_isZero (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (p : ℤ) (hp : 0 < p) :
    IsZero ((mappingCone ((chains R).map f)).X p) := by
  rw [IsZero.iff_id_eq_zero]
  apply mappingCone.ext_from _ (p + 1) p rfl
  · exact (chains_isZero R U (p + 1) (by omega)).eq_of_src _ _
  · exact (chains_isZero R E p hp).eq_of_src _ _

theorem cochain_eq_zero (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (m : ℤ) (hm : m < 0)
    (z : Cochain (mappingCone ((chains R).map f)) (res R F) m) : z = 0 := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  rw [Cochain.zero_v]
  by_cases hq : q < 0
  · exact (res_isZero R F q hq).eq_of_tgt _ _
  · exact (cone_isZero R f p (by omega)).eq_of_src _ _

theorem LeafNeg_of : LateralTheory.E.LeafDegCut.LeafNeg := by
  intro R _ U E f F m hm
  constructor
  intro a b
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective b
  have hx : x = y := by
    ext1
    rw [cochain_eq_zero R f F m hm (x : Cochain _ _ m), cochain_eq_zero R f F m hm (y : Cochain _ _ m)]
  rw [hx]

end LateralTheory.E.LeafNegPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafNormalModelPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafNormalModelPf

def intCl (Ω : Type) {L : Type} [Field Ω] [Field L] [Algebra Ω L] (u : L) : Subalgebra Ω L :=
  (integralClosure (Algebra.adjoin Ω {u}) L).restrictScalars Ω

theorem intCl_subset {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {u : L} (V : ValuationSubring L)
    (hΩ : ∀ a : Ω, algebraMap Ω L a ∈ V) (hu : u ∈ V) : (intCl Ω u : Set L) ⊆ V := by
  intro x hx
  let V' : Subalgebra Ω L := { V.toSubring with algebraMap_mem' := hΩ }
  have hle : Algebra.adjoin Ω {u} ≤ V' := Algebra.adjoin_le (Set.singleton_subset_iff.2 hu)
  obtain ⟨p, hp, hpx⟩ := (hx : IsIntegral (Algebra.adjoin Ω {u}) x)
  let f : Algebra.adjoin Ω {u} →+* V :=
    { toFun := fun y => ⟨y.1, hle y.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hint : IsIntegral V x := ⟨p.map f, hp.map f, by rw [Polynomial.eval₂_map]; exact hpx⟩
  obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := L)).1 hint
  exact y.2

theorem valuation_covers {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (u : L) (V : ValuationSubring L)
    (hΩ : ∀ a : Ω, algebraMap Ω L a ∈ V) : (intCl Ω u : Set L) ⊆ V ∨ (intCl Ω u⁻¹ : Set L) ⊆ V := by
  rcases V.mem_or_inv_mem u with h | h
  · exact Or.inl (intCl_subset V hΩ h)
  · exact Or.inr (intCl_subset V hΩ h)

theorem transcendental_inv {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {u : L}
    (hu : Transcendental Ω u) : Transcendental Ω u⁻¹ := by
  intro h
  apply hu
  simpa using h.inv

theorem adjoin_inv_eq {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (u : L) :
    IntermediateField.adjoin Ω {u⁻¹} = IntermediateField.adjoin Ω {u} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self Ω u)
  · rw [IntermediateField.adjoin_simple_le_iff]
    simpa using inv_mem (IntermediateField.mem_adjoin_simple_self Ω u⁻¹)

theorem ne_zero_of_transcendental {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {u : L}
    (hu : Transcendental Ω u) : u ≠ 0 := by
  rintro rfl
  exact hu isAlgebraic_zero

theorem self_mem_intCl {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (u : L) : u ∈ intCl Ω u :=
  isIntegral_algebraMap (x := (⟨u, Algebra.subset_adjoin (Set.mem_singleton u)⟩ : Algebra.adjoin Ω {u}))

def LeafIntClosureAlg : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (u : L),
  Transcendental Ω u → FiniteDimensional (IntermediateField.adjoin Ω {u}) L →
    Algebra.FiniteType Ω (intCl Ω u) ∧ IsIntegrallyClosed (intCl Ω u) ∧ ringKrullDim (intCl Ω u) = 1 ∧
      IsFractionRing (intCl Ω u) L

def LeafIntClosureLoc : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (u : L),
  Transcendental Ω u → FiniteDimensional (IntermediateField.adjoin Ω {u}) L →
    Algebra.adjoin Ω ((intCl Ω u : Set L) ∪ {u⁻¹}) = Algebra.adjoin Ω ((intCl Ω u⁻¹ : Set L) ∪ {u})

def LeafGlueProper : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L),
  u ≠ 0 → u ∈ A → u⁻¹ ∈ B → Algebra.FiniteType Ω A → Algebra.FiniteType Ω B →
  IsIntegrallyClosed A → IsIntegrallyClosed B → ringKrullDim A = 1 → ringKrullDim B = 1 →
  IsFractionRing A L → IsFractionRing B L →
  Algebra.adjoin Ω ((A : Set L) ∪ {u⁻¹}) = Algebra.adjoin Ω ((B : Set L) ∪ {u}) →
  (∀ V : ValuationSubring L, (∀ a : Ω, algebraMap Ω L a ∈ V) → (A : Set L) ⊆ V ∨ (B : Set L) ⊆ V) →
    ∃ (C0 : Scheme.{0}) (c0 : C0 ⟶ Sp Ω) (x : C0) (ψ : Spec (C0.presheaf.stalk x) ⟶ Sp L),
      IsIntegral C0 ∧ IsProper c0 ∧ (∀ y : C0, IsIntegrallyClosed (C0.presheaf.stalk y)) ∧
      topologicalKrullDim C0 = 1 ∧ IsGenericPoint x (⊤ : Set C0) ∧
      ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω L)) = C0.fromSpecStalk x ≫ c0

theorem adjoin_le_of_shift {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {u : L} (hu : u ≠ 0)
    (h : ∀ x ∈ intCl Ω u, ∃ n : ℕ, x * u⁻¹ ^ n ∈ intCl Ω u⁻¹) :
    Algebra.adjoin Ω ((intCl Ω u : Set L) ∪ {u⁻¹}) ≤ Algebra.adjoin Ω ((intCl Ω u⁻¹ : Set L) ∪ {u}) := by
  rw [Algebra.adjoin_le_iff]
  rintro x (hx | hx)
  · obtain ⟨n, hn⟩ := h x hx
    have : x = x * u⁻¹ ^ n * u ^ n := by
      rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hu, one_pow, mul_one]
    rw [this]
    have h1 : x * u⁻¹ ^ n ∈ Algebra.adjoin Ω ((intCl Ω u⁻¹ : Set L) ∪ {u}) :=
      Algebra.subset_adjoin (Set.mem_union_left _ hn)
    have h2 : u ∈ Algebra.adjoin Ω ((intCl Ω u⁻¹ : Set L) ∪ {u}) :=
      Algebra.subset_adjoin (Set.mem_union_right _ rfl)
    exact mul_mem h1 (pow_mem h2 n)
  · rw [Set.mem_singleton_iff.1 hx]
    exact Algebra.subset_adjoin (Set.mem_union_left _ (self_mem_intCl u⁻¹))

def LeafIntShift : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (u : L), u ≠ 0 →
  ∀ x ∈ intCl Ω u, ∃ n : ℕ, x * u⁻¹ ^ n ∈ intCl Ω u⁻¹

theorem LeafIntClosureLoc_of (h : LeafIntShift) : LeafIntClosureLoc := by
  intro Ω L _ _ _ u hu _
  have hu0 := ne_zero_of_transcendental hu
  apply le_antisymm (adjoin_le_of_shift hu0 (h Ω L u hu0))
  have h' := adjoin_le_of_shift (inv_ne_zero hu0) (by simpa using h Ω L u⁻¹ (inv_ne_zero hu0))
  simpa using h'

theorem shift_mem {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {u : L} (hu : u ≠ 0) (c : L)
    (hc : c ∈ Algebra.adjoin Ω {u}) : ∃ N : ℕ, ∀ m, N ≤ m → c * u⁻¹ ^ m ∈ Algebra.adjoin Ω {u⁻¹} := by
  have hinv : u⁻¹ ∈ Algebra.adjoin Ω {u⁻¹} := Algebra.subset_adjoin (Set.mem_singleton _)
  induction hc using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.1 hx]
    refine ⟨1, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [pow_add, pow_one, ← mul_assoc, mul_inv_cancel₀ hu, one_mul]
    exact pow_mem hinv k
  | algebraMap a =>
    exact ⟨0, fun m _ => mul_mem (Subalgebra.algebraMap_mem _ a) (pow_mem hinv m)⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨N1, h1⟩ := ihx
    obtain ⟨N2, h2⟩ := ihy
    refine ⟨max N1 N2, fun m hm => ?_⟩
    rw [add_mul]
    exact add_mem (h1 m (le_trans (le_max_left _ _) hm)) (h2 m (le_trans (le_max_right _ _) hm))
  | mul x y _ _ ihx ihy =>
    obtain ⟨N1, h1⟩ := ihx
    obtain ⟨N2, h2⟩ := ihy
    refine ⟨N1 + N2, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    have : x * y * u⁻¹ ^ (N1 + N2 + k) = (x * u⁻¹ ^ N1) * (y * u⁻¹ ^ (N2 + k)) := by ring
    rw [this]
    exact mul_mem (h1 N1 le_rfl) (h2 _ (Nat.le_add_right _ _))

theorem integral_closure_polynomial_elem_mul_inv_pow_mem_inv_closure : LeafIntShift := by
  intro Ω L _ _ _ u hu x hx
  classical
  obtain ⟨p, hpm, hpx⟩ := (hx : IsIntegral (Algebra.adjoin Ω {u}) x)
  have hN : ∀ c : Algebra.adjoin Ω {u}, ∃ N : ℕ, ∀ m, N ≤ m → (c : L) * u⁻¹ ^ m ∈ Algebra.adjoin Ω {u⁻¹} :=
    fun c => shift_mem hu c c.2
  choose Nf hNf using hN
  set p' := p.map (algebraMap (Algebra.adjoin Ω {u}) L) with hp'
  have hpm' : p'.Monic := hpm.map _
  have hdeg : p'.natDegree = p.natDegree := hpm.natDegree_map _
  set N := (Finset.range (p.natDegree + 1)).sup (fun i => Nf (p.coeff i)) with hNdef
  set r : L := u⁻¹ ^ N
  refine ⟨N, ?_⟩
  show IsIntegral (Algebra.adjoin Ω {u⁻¹}) (x * u⁻¹ ^ N)
  have hroot : (p'.scaleRoots r).eval (r * x) = 0 := by
    have h0 : p'.eval₂ (RingHom.id L) x = 0 := by
      rw [hp', Polynomial.eval₂_map]; exact hpx
    have h := Polynomial.scaleRoots_eval₂_mul (p := p') (RingHom.id L) x r
    rw [h0, mul_zero] at h
    exact h
  have hmon : (p'.scaleRoots r).Monic := (Polynomial.monic_scaleRoots_iff r).2 hpm'
  have hlift : p'.scaleRoots r ∈ Polynomial.lifts (algebraMap (Algebra.adjoin Ω {u⁻¹}) L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_scaleRoots, hp', Polynomial.coeff_map]
    rcases lt_or_ge i p.natDegree with hi | hi
    · have hle : Nf (p.coeff i) ≤ N * (p'.natDegree - i) := by
        have h1 : Nf (p.coeff i) ≤ N :=
          Finset.le_sup (f := fun i => Nf (p.coeff i)) (Finset.mem_range.2 (by omega))
        have h2 : 1 ≤ p'.natDegree - i := by omega
        nlinarith
      have := hNf (p.coeff i) _ hle
      rw [← pow_mul] at *
      exact ⟨⟨_, this⟩, rfl⟩
    · have he : p'.natDegree - i = 0 := by omega
      rw [he, pow_zero, mul_one]
      rcases eq_or_lt_of_le hi with h | h
      · rw [← h, hpm.coeff_natDegree, map_one]; exact ⟨1, map_one _⟩
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h, map_zero]; exact ⟨0, map_zero _⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hmon
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.eval_map, hq, mul_comm]
  exact hroot

theorem LeafNormalModel_of (hA : LeafIntClosureAlg) (hC : LeafGlueProper) :
    LateralTheory.E.LeafModelCurveCut.ExistsNormalProperCurveModel := by
  intro Ω L _ _ _ u hu hfin
  have hu' := transcendental_inv hu
  have hfin' : FiniteDimensional (IntermediateField.adjoin Ω {u⁻¹}) L := by
    rw [adjoin_inv_eq (Ω := Ω) u]; exact hfin
  obtain ⟨a1, a2, a3, a4⟩ := hA Ω L u hu hfin
  obtain ⟨b1, b2, b3, b4⟩ := hA Ω L u⁻¹ hu' hfin'
  exact hC Ω L (intCl Ω u) (intCl Ω u⁻¹) u (ne_zero_of_transcendental hu) (self_mem_intCl u)
    (self_mem_intCl u⁻¹) a1 b1 a2 b2 a3 b3 a4 b4
    (LeafIntClosureLoc_of integral_closure_polynomial_elem_mul_inv_pow_mem_inv_closure Ω L u hu hfin) (fun V hΩ => valuation_covers u V hΩ)

end LateralTheory.E.LeafNormalModelPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSmoothOfNormalPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafSmoothOfNormalPf

def LeafStalkSmoothClosed : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω)
  [IsIntegral C], LocallyOfFiniteType c → (∀ y : C, IsIntegrallyClosed (C.presheaf.stalk y)) →
    topologicalKrullDim C = 1 → ∀ y : C, y ≠ genericPoint C → (c.stalkMap y).hom.FormallySmooth

def LeafRelDimOne : Prop := ∀ (Ω : Type) [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω),
  IsIntegral C → Smooth c → topologicalKrullDim C = 1 → SmoothOfRelativeDimension 1 c

theorem smooth_of_stalks (Ω : Type) [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω) [LocallyOfFiniteType c]
    (h : ∀ y : C, (c.stalkMap y).hom.FormallySmooth) : Smooth c := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  exact top_le_iff.mp fun y _ => h y

theorem stalk_smooth_all (hA : LeafStalkSmoothClosed) (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}}
    (c : C ⟶ Sp Ω) (hC : IsIntegral C) (hc : LocallyOfFiniteType c)
    (hn : ∀ y : C, IsIntegrallyClosed (C.presheaf.stalk y)) (hd : topologicalKrullDim C = 1) (y : C) :
    (c.stalkMap y).hom.FormallySmooth := by
  by_cases hy : y = genericPoint C
  · subst hy
    exact c.genericPoint_mem_smoothLocus_of_perfectField
  · exact hA Ω c hc hn hd y hy

theorem LeafSmoothOfNormal_of (hA : LeafStalkSmoothClosed) (hB : LeafRelDimOne) :
    LateralTheory.E.LeafModelCurveCut.LeafSmoothOfNormal := by
  intro Ω _ _ C c hC hc hn hd
  have hs : Smooth c := smooth_of_stalks Ω c (stalk_smooth_all hA Ω c hC hc hn hd)
  exact hB Ω c hC hs hd

end LateralTheory.E.LeafSmoothOfNormalPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTensUPPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.E.LeafTensUPPf
open LateralTheory.E.LeafTwTensExPf
open Classical

variable {R : Type} [CommRing R] {I J K : Cx R}

theorem lift_lo (μ : Pair I J K) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    μ.lift U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b)) = μ.mul U s t w h a b := by
  simp [Pair.lift, lo]

theorem lift_nat (μ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    ((K.X w).obj.map g.op).hom ∘ₗ μ.lift U w = μ.lift V w ∘ₗ Tens.res g w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply]
  have e := tres_tmul I J g w ⟨(s, t), h⟩ a b
  change Sec.res g (μ.lift U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b))) = μ.lift V w (Tens.res g w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b)))
  rw [e]
  change Sec.res g (μ.lift U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b))) = μ.lift V w (lo I J ⟨(s, t), h⟩ (Sec.res g a ⊗ₜ Sec.res g b))
  rw [lift_lo, lift_lo, μ.nat]

theorem lift_d (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) :
    ((K.d w (w + 1)).hom.app (op U)).hom ∘ₗ μ.lift U w = μ.lift U (w + 1) ∘ₗ dT I J U w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply]
  change Sec.map (K.d w (w + 1)) (μ.lift U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b))) =
    μ.lift U (w + 1) (dT I J U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b)))
  rw [dT_tmul, map_add (f := _), map_zsmul, lift_lo, lift_lo, lift_lo, μ.leibniz, Units.smul_def]

def liftP (μ : Pair I J K) (w : ℤ) : TP I J w ⟶ (K.X w).obj where
  app U := ModuleCat.ofHom (μ.lift U.unop w)
  naturality _ _ g := ModuleCat.hom_ext (lift_nat μ g.unop w).symm

theorem tensorPresheafLift_comm (μ : Pair I J K) (w : ℤ) :
    liftP μ w ≫ (K.d w (w + 1)).hom = dTP I J w ≫ liftP μ (w + 1) := by
  ext U : 2
  exact ModuleCat.hom_ext (lift_d μ U.unop w)

theorem etale_tensor_presheaf_lift_is_local_iso {T : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (w : ℤ) :
    Scheme.etaleTopology.{0}.W (liftP τ w) := by
  have : Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (liftP τ w) := ⟨fun {U} y => by
    obtain ⟨S, hS, hP⟩ := hτ.1 U w y
    refine Scheme.etaleTopology.{0}.superset_covering ?_ hS
    intro V g hg
    obtain ⟨x, hx⟩ := hP V g hg
    exact ⟨x, hx⟩⟩
  have : Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (liftP τ w) := ⟨fun {X} x y hxy => by
    let x' : Tens I J X.unop w := x
    let y' : Tens I J X.unop w := y
    have hxy' : τ.lift X.unop w x' = τ.lift X.unop w y' := hxy
    have h0 : τ.lift X.unop w (x' - y') = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr hxy'
    obtain ⟨S, hS, hP⟩ := hτ.2 X.unop w (x' - y') h0
    refine Scheme.etaleTopology.{0}.superset_covering ?_ hS
    intro V g hg
    have h1 : Tens.res g w (x' - y') = 0 := hP V g hg
    rw [map_sub, sub_eq_zero] at h1
    exact h1⟩
  exact GrothendieckTopology.W_of_isLocallyBijective _ _

theorem etale_tensor_pairing_universal_property_holds : LateralTheory.E.LeafPairExtPf2.LeafTensUP := by
  intro R _ I J T K τ hτ μ
  have hb : ∀ w, Function.Bijective (fun g : (T.X w).obj ⟶ (K.X w).obj => liftP τ w ≫ g) :=
    fun w => etale_tensor_presheaf_lift_is_local_iso τ hτ w _ (K.X w).property
  choose u0 hu0' using fun w => (hb w).2 (liftP μ w)
  have hu0 : ∀ w, liftP τ w ≫ u0 w = liftP μ w := hu0'
  let u : T ⟶ K :=
    { f := fun w => ⟨u0 w⟩
      comm' := by
        rintro i j rfl
        apply Sheaf.hom_ext
        change u0 i ≫ (K.d i (i + 1)).hom = (T.d i (i + 1)).hom ≫ u0 (i + 1)
        have key : liftP τ i ≫ (u0 i ≫ (K.d i (i + 1)).hom) = liftP τ i ≫ ((T.d i (i + 1)).hom ≫ u0 (i + 1)) := by
          rw [← Category.assoc, ← Category.assoc, hu0, tensorPresheafLift_comm, tensorPresheafLift_comm, Category.assoc, hu0]
        exact (etale_tensor_presheaf_lift_is_local_iso τ hτ i _ (K.X (i + 1)).property).1 key }
  refine ⟨u, fun U s t w h a b => ?_⟩
  have e := congrArg (fun f => (f.app (op U)).hom (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b))) (hu0 w)
  simp only at e
  rw [← lift_lo τ, ← lift_lo μ]
  exact e

end LateralTheory.E.LeafTensUPPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafVanStalk
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafVan0Pf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

abbrev prS {Y B W S : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (s : S ⟶ B) : pullback (pullback.snd p s ≫ s) ι ⟶ pullback p s :=
  pullback.fst _ _

def LeafVanStalk : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (U : B.Etale) (m : ℤ),
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ U.left), SH A →
    Subsingleton (Hrel (ZMod q) (sch.map (prS p ι (t ≫ U.hom))) (tw q i) m)) →
  ∀ y : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m, Cov U (fun U' a => rY q i p ι a m y = 0)

def LeafVanW : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (A : Type) [CommRing A] (s : Sp A ⟶ B), SH A → (∃ x : Sp A, (∀ z : Sp A, z ⤳ x) ∧ s x ∈ Set.range ι) →
  ∀ m : ℤ, Subsingleton (Hrel (ZMod q) (sch.map (prS p ι s)) (tw q i) m)

def LeafVanV : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y S : Scheme.{0}} (ι : W ⟶ B) (p : Y ⟶ B) (s : S ⟶ B),
  (∀ x : S, s x ∉ Set.range ι) → ∀ m : ℤ, Subsingleton (Ht q (sch.obj (pullback p s)) m i) →
  Subsingleton (Hrel (ZMod q) (sch.map (prS p ι s)) (tw q i) m)

theorem LeafVan0_of (hS : LeafVanStalk) (hW : LeafVanW) (hV : LeafVanV) : LeafVan0 := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 b ι _ V hV' p g1 g2 hp _ _ hSHV U m hm y
  refine hS hH q k hq i b ι p hp U m ?_ y
  intro A _ t hA
  obtain ⟨hHen, _⟩ := hA
  by_cases hx : (t ≫ U.hom) (IsLocalRing.closedPoint A) ∈ Set.range ι
  · exact hW hH q k hq i b ι p hp A (t ≫ U.hom) ⟨hHen, ‹_›⟩
      ⟨IsLocalRing.closedPoint A, fun z => IsLocalRing.specializes_closedPoint z, hx⟩ m
  · have hall : ∀ z : Sp A, (t ≫ U.hom) z ∈ (V : Set B) := by
      intro z
      have hz : (t ≫ U.hom) z ⤳ (t ≫ U.hom) (IsLocalRing.closedPoint A) :=
        (IsLocalRing.specializes_closedPoint z).map (t ≫ U.hom).continuous
      have hxV : (t ≫ U.hom) (IsLocalRing.closedPoint A) ∈ (V : Set B) := by rw [hV']; exact hx
      exact hz.mem_open V.isOpen hxV
    have hrange : Set.range (t ≫ U.hom : Sp A ⟶ B) ⊆ (V : Set B) := by rintro _ ⟨z, rfl⟩; exact hall z
    have hmiss : ∀ z : Sp A, (t ≫ U.hom) z ∉ Set.range ι := by
      intro z hz; have := hall z; rw [hV'] at this; exact this hz
    exact hV hH q i ι p (t ≫ U.hom) hmiss m ((hSHV A (t ≫ U.hom) ⟨hHen, ‹_›⟩ hrange).1 m (by omega))

end LateralTheory.E.LeafVan0Pf
end
end

