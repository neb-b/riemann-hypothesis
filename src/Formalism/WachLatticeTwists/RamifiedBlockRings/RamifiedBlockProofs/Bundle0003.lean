module

public import Formalism.WachLatticeTwists.RamifiedBlockRings.LemmaFiveThreeAnyResidueField
public import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.Bundle0002
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.Bundle0004
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0001
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.Bundle0001

@[expose] public section

-- bundled from Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.BigRes
section
open Finset Classical Polynomial

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG

theorem exists_irreducible_big (k : Type) [Field k] [Finite k] (N : ℕ) :
    ∃ f : k[X], f.Monic ∧ Irreducible f ∧ (N : Cardinal) < Cardinal.mk (AdjoinRoot f) := by
  classical
  haveI hKinf : Infinite (AlgebraicClosure k) := by
    first
    | exact inferInstance
    | exact IsAlgClosed.instInfinite
  obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq (AlgebraicClosure k) (N + 1)
  haveI hfd : FiniteDimensional k (IntermediateField.adjoin k (S : Set (AlgebraicClosure k))) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  haveI : Finite (IntermediateField.adjoin k (S : Set (AlgebraicClosure k))) :=
    Module.finite_of_finite k
  obtain ⟨α, hα⟩ : ∃ α : IntermediateField.adjoin k (S : Set (AlgebraicClosure k)),
      IntermediateField.adjoin k {α} = ⊤ := by
    first
    | exact Field.exists_primitive_element_of_finite_top k _
    | exact Field.exists_primitive_element k _
  have hint : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  refine ⟨minpoly k α, minpoly.monic hint, minpoly.irreducible hint, ?_⟩
  have e1 : Cardinal.mk (AdjoinRoot (minpoly k α)) =
      Cardinal.mk (IntermediateField.adjoin k {α}) :=
    Cardinal.mk_congr (IntermediateField.adjoinRootEquivAdjoin k hint).toEquiv
  rw [e1, hα]
  rw [Cardinal.mk_congr IntermediateField.topEquiv.toEquiv]
  have hSF : ∀ x ∈ S, x ∈ IntermediateField.adjoin k (S : Set (AlgebraicClosure k)) :=
    fun x hx => IntermediateField.subset_adjoin k _ hx
  have hle : (S.card : Cardinal) ≤
      Cardinal.mk (IntermediateField.adjoin k (S : Set (AlgebraicClosure k))) := by
    have hinj : Function.Injective
        (fun x : S => (⟨x, hSF x x.2⟩ : IntermediateField.adjoin k (S : Set (AlgebraicClosure k)))) :=
      fun a b h => Subtype.ext (by have h' := congrArg Subtype.val h; exact h')
    simpa using Cardinal.mk_le_of_injective hinj
  rw [hS] at hle
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self N) hle

theorem unram_ext (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (f : O[X])
    (hf : f.Monic) (hirr : Irreducible (f.map (IsLocalRing.residue O))) :
    ∃ (_ : IsDomain (AdjoinRoot f)) (_ : IsDiscreteValuationRing (AdjoinRoot f)),
      Module.Free O (AdjoinRoot f) ∧ Module.Finite O (AdjoinRoot f) ∧
      (∀ y : O, IsDiscreteValuationRing.addVal (AdjoinRoot f) (algebraMap O (AdjoinRoot f) y) =
        IsDiscreteValuationRing.addVal O y) ∧
      Cardinal.mk (IsLocalRing.ResidueField (AdjoinRoot f)) =
        Cardinal.mk (AdjoinRoot (f.map (IsLocalRing.residue O))) := by
  let A := AdjoinRoot f
  let res := IsLocalRing.residue O
  let fb := f.map res
  have : Fact (Irreducible fb) := ⟨hirr⟩
  let F := AdjoinRoot fb
  have hfirr : Irreducible f := hf.irreducible_of_irreducible_map res f hirr
  have hdom : IsDomain A := AdjoinRoot.isDomain_of_prime hfirr.prime
  let pb := AdjoinRoot.powerBasis' hf
  have hfree : Module.Free O A := Module.Free.of_basis pb.basis
  have hfin : Module.Finite O A := pb.finite
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let ψ : A →+* F := AdjoinRoot.lift ((AdjoinRoot.of fb).comp res) (AdjoinRoot.root fb) (by
    rw [← Polynomial.eval₂_map, AdjoinRoot.eval₂_root])
  have hψmk : ∀ p : O[X], ψ (AdjoinRoot.mk f p) = AdjoinRoot.mk fb (p.map res) := by
    intro p
    rw [AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.aeval_eq]
    rfl
  have hres : Function.Surjective res := IsLocalRing.residue_surjective
  have hψs : Function.Surjective ψ := by
    intro z
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    obtain ⟨q, rfl⟩ := Polynomial.map_surjective res hres p
    exact ⟨AdjoinRoot.mk f q, hψmk q⟩
  let ϖ' : A := algebraMap O A ϖ
  have hker : RingHom.ker ψ = Ideal.span {ϖ'} := by
    apply le_antisymm
    · intro a ha
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
      rw [RingHom.mem_ker, hψmk, AdjoinRoot.mk_eq_zero] at ha
      obtain ⟨qb, hqb⟩ := ha
      obtain ⟨q, rfl⟩ := Polynomial.map_surjective res hres qb
      have h1 : (p - f * q).map res = 0 := by
        rw [Polynomial.map_sub, Polynomial.map_mul, hqb, sub_self]
      have h2 : C ϖ ∣ p - f * q := by
        rw [Polynomial.C_dvd_iff_dvd_coeff]
        intro i
        have h3 : res ((p - f * q).coeff i) = 0 := by
          rw [← Polynomial.coeff_map, h1, Polynomial.coeff_zero]
        rw [IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at h3
        exact h3
      obtain ⟨h, hh⟩ := h2
      rw [Ideal.mem_span_singleton]
      refine ⟨AdjoinRoot.mk f h, ?_⟩
      have h4 : AdjoinRoot.mk f p = AdjoinRoot.mk f (p - f * q) := by
        rw [map_sub, map_mul, AdjoinRoot.mk_self, zero_mul, sub_zero]
      rw [h4, hh, map_mul, AdjoinRoot.mk_C]
      rfl
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
      show ψ (AdjoinRoot.of f ϖ) = 0
      rw [AdjoinRoot.lift_of]
      show AdjoinRoot.of fb (res ϖ) = 0
      rw [(IsLocalRing.residue_eq_zero_iff ϖ).mpr hϖ.not_isUnit, map_zero]
  have hmaxk : (RingHom.ker ψ).IsMaximal := RingHom.ker_isMaximal_of_surjective ψ hψs
  have hloc : IsLocalRing A := by
    refine IsLocalRing.of_unique_max_ideal ⟨RingHom.ker ψ, hmaxk, fun M hM => ?_⟩
    letI : Module.Finite O A := hfin
    have h1 : (M.comap (algebraMap O A)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap O A)
        (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) M
    have h2 : ϖ ∈ M.comap (algebraMap O A) := by
      rw [IsLocalRing.eq_maximalIdeal h1]
      exact hϖ.not_isUnit
    have h3 : RingHom.ker ψ ≤ M := by
      rw [hker, Ideal.span_singleton_le_iff_mem]
      exact h2
    exact (hmaxk.eq_of_le hM.ne_top h3).symm
  have hmA : IsLocalRing.maximalIdeal A = Ideal.span {ϖ'} := by
    rw [← hker]
    exact (IsLocalRing.eq_maximalIdeal hmaxk).symm
  have hinj : Function.Injective (algebraMap O A) := FaithfulSMul.algebraMap_injective O A
  have hnf : ¬ IsField A := fun h =>
    IsDiscreteValuationRing.not_isField O (isField_of_isIntegral_of_isField hinj h)
  have hpr : (IsLocalRing.maximalIdeal A).IsPrincipal := ⟨⟨ϖ', hmA⟩⟩
  have hdvr : IsDiscreteValuationRing A := ((IsDiscreteValuationRing.TFAE A hnf).out 1 5).mpr hpr
  have hϖ' : Irreducible ϖ' := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ').mpr hmA
  refine ⟨hdom, hdvr, hfree, hfin, ?_, ?_⟩
  · obtain ⟨e, he⟩ := exists_ramification O A hinj
    have h1 := he ϖ
    rw [IsDiscreteValuationRing.addVal_uniformizer hϖ, mul_one] at h1
    have h2 : IsDiscreteValuationRing.addVal A ϖ' = 1 := IsDiscreteValuationRing.addVal_uniformizer hϖ'
    have h3 : (e : ℕ∞) = 1 := h1.symm.trans h2
    intro y
    rw [he y, h3, one_mul]
  · have e1 : (A ⧸ IsLocalRing.maximalIdeal A) ≃+* (A ⧸ RingHom.ker ψ) :=
      Ideal.quotEquivOfEq (by rw [hmA, hker])
    exact (e1.trans (RingHom.quotientKerEquivOfSurjective hψs)).toEquiv.cardinal_eq

theorem bigResidueExt : StatBigResidueExt := by
  intro O _ _ _ N
  by_cases hk : Finite (IsLocalRing.ResidueField O)
  · obtain ⟨g, hgm, hgi, hgN⟩ := exists_irreducible_big (IsLocalRing.ResidueField O) N
    have hlift : g ∈ Polynomial.lifts (IsLocalRing.residue O) :=
      (Polynomial.mem_lifts _).2 (Polynomial.map_surjective _ IsLocalRing.residue_surjective g)
    obtain ⟨f, hfmap, -, hfm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hgm
    rw [← hfmap] at hgi hgN
    obtain ⟨h1, h2, hfree, hfin, hval, hcard⟩ := unram_ext O f hfm hgi
    exact ⟨AdjoinRoot f, inferInstance, h1, h2, inferInstance, hfree, hfin, hval,
      lt_of_lt_of_eq hgN hcard.symm⟩
  · have hinf : Infinite (IsLocalRing.ResidueField O) := not_finite_iff_infinite.mp hk
    refine ⟨O, inferInstance, inferInstance, inferInstance, Algebra.id O, inferInstance,
      inferInstance, fun y => rfl, ?_⟩
    exact lt_of_lt_of_le (Cardinal.natCast_lt_aleph0 (n := N)) (Cardinal.aleph0_le_mk _)

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

-- bundled from Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.BurnsideMat
section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem burnsideMat : StatBurnsideMat := by
  intro k _ n _ _ _ G _ ρ hρ
  obtain ⟨hirr, hcom⟩ := hρ
  let A := MonoidAlgebra k G
  let V := n → k
  let L : A →ₐ[k] Matrix n n k := MonoidAlgebra.lift k (Matrix n n k) G ρ
  let φ : A →ₐ[k] Module.End k V := (Matrix.toLinAlgEquiv' : Matrix n n k ≃ₐ[k] _).toAlgHom.comp L
  letI : Module A V := Module.compHom V φ.toRingHom
  have hact : ∀ (a : A) (v : V), a • v = (L a).mulVec v := fun a v => rfl
  haveI : IsScalarTower k A V := ⟨fun c a v => by
    rw [hact, hact, map_smul, Matrix.smul_mulVec]⟩
  have hof : ∀ g, L (MonoidAlgebra.of k G g) = ρ g := fun g => MonoidAlgebra.lift_of ρ g
  have hS : IsSimpleModule A V := by
    haveI : Nontrivial (Submodule A V) := by
      refine ⟨⊥, ⊤, fun h => ?_⟩
      have : (⊤ : Submodule A V) = ⊥ := h.symm
      have h2 : (fun _ : n => (1 : k)) ∈ (⊤ : Submodule A V) := Submodule.mem_top
      rw [this, Submodule.mem_bot] at h2
      exact one_ne_zero (congrFun h2 (Classical.arbitrary n))
    suffices hso : IsSimpleOrder (Submodule A V) from @IsSimpleModule.mk _ _ _ _ _ hso
    refine ⟨fun W => ?_⟩
    rcases hirr (W.restrictScalars k) (fun g v hv => by
      have := W.smul_mem (MonoidAlgebra.of k G g) hv
      rw [hact, hof] at this
      exact this) with h | h
    · left; exact (Submodule.restrictScalars_eq_bot_iff k A V).mp h
    · right; exact (Submodule.restrictScalars_eq_top_iff k A V).mp h
  have hsc : ∀ ψ : V →ₗ[A] V, ∃ c : k, ∀ v, ψ v = c • v := by
    intro ψ
    let M : Matrix n n k := LinearMap.toMatrix' (ψ.restrictScalars k)
    have hM : ∀ v, M.mulVec v = ψ v := fun v => by
      have := LinearMap.toMatrix'_mulVec (ψ.restrictScalars k) v
      simpa [M] using this
    obtain ⟨c, hc⟩ := hcom M (fun g => by
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun v => ?_
      simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
      rw [hM, hM, ← hof, ← hact, ← hact, map_smul])
    refine ⟨c, fun v => ?_⟩
    rw [← hM, hc, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hsurj := burnside k A V hS hsc
  refine eq_top_iff.mpr fun B _ => ?_
  obtain ⟨a, ha⟩ := hsurj (Matrix.toLin' B)
  have hB : B = L a := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun ha v
    simp only [Matrix.toLin'_apply]
    rw [← hact]
    exact this.symm
  rw [hB]
  exact MonoidAlgebra.induction_on (motive := fun a => L a ∈ Submodule.span k (Set.range ρ)) a
    (fun g => by rw [hof]; exact Submodule.subset_span ⟨g, rfl⟩)
    (fun f g hf hg => by rw [map_add (f := _)]; exact Submodule.add_mem _ hf hg)
    (fun c f hf => by rw [map_smul]; exact Submodule.smul_mem _ _ hf)

theorem ontoSpan : StatOntoSpan := by
  first | exact UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan .. | (apply UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan <;> assumption) | (intros; apply UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan <;> assumption) | (apply @UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan <;> assumption) | (apply @UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan <;> first | assumption | infer_instance)

theorem noeth : StatNoeth := by
  intro O _ _ _ X' _ d _ _ R' hint
  let L : (X' → d → d → O) →ₗ[O] (X' → Matrix d d (FractionRing O)) :=
    { toFun := fun F x' => Matrix.of fun i j => algebraMap O (FractionRing O) (F x' i j)
      map_add' := fun F F' => by funext x'; ext i j; simp
      map_smul' := fun c F => by funext x'; ext i j; simp [Algebra.smul_def] }
  have hle : Subalgebra.toSubmodule R' ≤ LinearMap.range L := by
    intro a ha
    choose F hF using hint a ha
    exact ⟨F, by funext x'; ext i j; exact hF x' i j⟩
  haveI : IsNoetherian O (LinearMap.range L) := inferInstance
  haveI h1 : IsNoetherian O (Subalgebra.toSubmodule R') := isNoetherian_of_le hle
  haveI h2 : IsNoetherian O R' := h1
  exact isNoetherian_of_tower O h2

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

-- bundled from Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.KerEqOfFactor
section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem relMap_mul {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M] {l m n : Type*} [Fintype l]
    [Fintype m] [Fintype n] (C : Matrix l m O) (B : Matrix m n O) (v : n → M) :
    relMap O M (C * B) v = relMap O M C (relMap O M B v) := by
  ext i
  simp only [relMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply, Finset.sum_smul,
    Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

theorem ker_eq_of_factor {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M] {m n : Type*}
    [Fintype m] [Fintype n] (A : Matrix m n O) (B : Matrix n n O) (C : Matrix m n O)
    (C' : Matrix n m O) (h1 : A = C * B) (h2 : B = C' * A) :
    LinearMap.ker (relMap O M A) = LinearMap.ker (relMap O M B) := by
  ext v
  simp only [LinearMap.mem_ker]
  constructor
  · intro hv
    rw [h2, relMap_mul, hv, map_zero]
  · intro hv
    rw [h1, relMap_mul, hv, map_zero]

private theorem sum_extend_embedding_zero_eq_sum {α β M : Type*} [Fintype α] [Fintype β] [AddCommMonoid M]
    (f : α ↪ β) (φ : α → M) : ∑ l, Function.extend f φ 0 l = ∑ j, φ j := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map f)), Finset.sum_map]
  · simp only [Function.Embedding.coeFn_mk, f.injective.extend_apply]
  · intro l _ hl
    rw [Function.extend_apply']
    · rfl
    · rintro ⟨j, rfl⟩
      exact hl (Finset.mem_map_of_mem _ (Finset.mem_univ j))

theorem exists_square {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {m n : Type}
    [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n O) :
    ∃ (B : Matrix n n O) (C : Matrix m n O) (C' : Matrix n m O), A = C * B ∧ B = C' * A := by
  classical
  obtain ⟨k, b⟩ := Submodule.basisOfPid (Pi.basisFun O n) (Submodule.span O (Set.range A))
  have hk : Fintype.card (Fin k) ≤ Fintype.card n := by
    have h := Submodule.finrank_le (Submodule.span O (Set.range A))
    rw [Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card] at h
    exact h
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hk
  have hA : ∀ i, A i ∈ Submodule.span O (Set.range A) := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hb : ∀ j, ∃ w : m → O, ∑ i, w i • A i = (b j : n → O) := fun j =>
    (Submodule.mem_span_range_iff_exists_fun O).1 (b j).2
  choose w hw using hb
  refine ⟨Function.extend f (fun j => (b j : n → O)) 0,
    fun i => Function.extend f (fun j => b.repr ⟨A i, hA i⟩ j) 0,
    Function.extend f w 0, ?_, ?_⟩
  · ext i c
    erw [Matrix.mul_apply]
    have hterm : ∀ l, Function.extend f (fun j => b.repr ⟨A i, hA i⟩ j) 0 l *
        Function.extend f (fun j => (b j : n → O)) 0 l c =
        Function.extend f (fun j => b.repr ⟨A i, hA i⟩ j * (b j : n → O) c) 0 l := by
      intro l
      by_cases hl : ∃ j, f j = l
      · obtain ⟨j, rfl⟩ := hl
        simp only [f.injective.extend_apply]
      · simp only [Function.extend_apply' _ _ _ hl, Pi.zero_apply, zero_mul]
    simp_rw [hterm]
    rw [sum_extend_embedding_zero_eq_sum]
    have h := congrArg (fun x : Submodule.span O (Set.range A) => (x : n → O) c)
      (b.sum_repr ⟨A i, hA i⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h
    exact h.symm
  · ext l c
    erw [Matrix.mul_apply]
    by_cases hl : ∃ j, f j = l
    · obtain ⟨j, rfl⟩ := hl
      simp only [f.injective.extend_apply]
      have h := congrFun (hw j) c
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
      exact h.symm
    · simp [Function.extend_apply' _ _ _ hl]

theorem kerBc : StatKerBc := by
  intro O O' _ _ _ _ _ _ _ e he m n _ _ _ A
  obtain ⟨B, C, C', h1, h2⟩ := exists_square A
  let j : O →+* O' := algebraMap O O'
  have h1' : A.map j = C.map j * B.map j := by rw [← Matrix.map_mul, ← h1]
  have h2' : B.map j = C'.map j * A.map j := by rw [← Matrix.map_mul, ← h2]
  rw [ker_eq_of_factor A B C C' h1 h2, ker_eq_of_factor (A.map j) (B.map j) (C.map j) (C'.map j) h1' h2']
  have e1 := lenKer O n B
  have e2 := lenKer O' n (B.map j)
  unfold matQ at e1 e2
  rw [e1, e2, ← he]
  congr 1
  exact (RingHom.map_det j B).symm

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

-- bundled from Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.Normal
section
open Module

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

section Normal

variable {O : Type*} [CommRing O] {r : Type} [Fintype r] [DecidableEq r]

theorem free_of_isCompl [IsLocalRing O] (p q : Submodule O (r → O)) (h : IsCompl p q) :
    Module.Free O p ∧ Module.Finite O p := by
  have hsurj : Function.Surjective (Submodule.linearProjOfIsCompl p q h) :=
    fun x => ⟨(x : r → O), Submodule.linearProjOfIsCompl_apply_left h x⟩
  have hfin : Module.Finite O p := Module.Finite.of_surjective _ hsurj
  haveI : Module.Projective O p :=
    Module.Projective.of_split p.subtype (Submodule.linearProjOfIsCompl p q h)
      (LinearMap.ext fun x => Submodule.linearProjOfIsCompl_apply_left h x)
  haveI : Module.FinitePresentation O p := by
    first
    | infer_instance
    | exact Module.finitePresentation_of_projective _ _
    | exact Module.finitePresentation_of_projective
  exact ⟨Module.free_of_flat_of_isLocalRing, hfin⟩

theorem idem_normal_form [IsLocalRing O] (e : Matrix r r O) (he : IsIdempotentElem e) :
    ∃ (P Q : Matrix r r O) (d : r → O), (∀ j, d j = 0 ∨ d j = 1) ∧ P * Q = 1 ∧ Q * P = 1 ∧
      e = P * Matrix.diagonal d * Q := by
  classical
  let E : (r → O) →ₗ[O] (r → O) := Matrix.toLin' e
  have hE : IsIdempotentElem E := by
    have h : E * E = E := by rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, he.eq]
    exact h
  have hC : IsCompl (LinearMap.range E) (LinearMap.ker E) := LinearMap.IsIdempotentElem.isCompl hE
  obtain ⟨_, _⟩ := free_of_isCompl _ _ hC
  obtain ⟨_, _⟩ := free_of_isCompl _ _ hC.symm
  let bR := Module.Free.chooseBasis O (LinearMap.range E)
  let bK := Module.Free.chooseBasis O (LinearMap.ker E)
  let B := (bR.prod bK).map (Submodule.prodEquivOfIsCompl _ _ hC)
  let σ := B.indexEquiv (Pi.basisFun O r)
  let B' := B.reindex σ
  have key : ∀ j, E (B' j) = (if (σ.symm j).isLeft then 1 else 0 : O) • B' j := by
    intro j
    simp only [B', Module.Basis.reindex_apply]
    rcases σ.symm j with a | b
    · have hm : (B (Sum.inl a)) ∈ LinearMap.range E := by
        simp [B, Module.Basis.prod_apply]
      simpa using ((LinearMap.IsIdempotentElem.mem_range_iff hE).mp hm)
    · have hm : (B (Sum.inr b)) ∈ LinearMap.ker E := by
        simp [B, Module.Basis.prod_apply]
      simpa using hm
  refine ⟨(Pi.basisFun O r).toMatrix B', B'.toMatrix (Pi.basisFun O r),
    fun j => if (σ.symm j).isLeft then 1 else 0, fun j => by dsimp only; split_ifs <;> simp,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _, ?_⟩
  have hEP : e * (Pi.basisFun O r).toMatrix B' = (Pi.basisFun O r).toMatrix B' *
      Matrix.diagonal (fun j => if (σ.symm j).isLeft then 1 else 0) := by
    ext i j
    rw [Matrix.mul_diagonal]
    have := congrFun (key j) i
    simp only [E, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.smul_apply,
      smul_eq_mul] at this
    simp only [Matrix.mul_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [this, mul_comm]
  calc e = e * ((Pi.basisFun O r).toMatrix B' * B'.toMatrix (Pi.basisFun O r)) := by
        rw [Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, hEP]

theorem rank_map_conj {F : Type*} [Field F] (f : O →+* F) (P Q : Matrix r r O) (d : r → O)
    (hd : ∀ j, d j = 0 ∨ d j = 1) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    ((P * Matrix.diagonal d * Q).map f).rank = Nat.card {j // d j = 1} := by
  classical
  haveI : Nontrivial O := f.domain_nontrivial
  have hmap : (P * Matrix.diagonal d * Q).map f = P.map f * Matrix.diagonal (fun j => f (d j)) * Q.map f := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero f)]
  have h1 : P.map f * Q.map f = 1 := by
    simpa [Matrix.map_mul] using congrArg (fun M => M.map f) hPQ
  have h2 : Q.map f * P.map f = 1 := by
    simpa [Matrix.map_mul] using congrArg (fun M => M.map f) hQP
  have hPu : IsUnit (P.map f).det := Matrix.isUnit_det_of_right_inverse h1
  have hQu : IsUnit (Q.map f).det := Matrix.isUnit_det_of_right_inverse h2
  rw [hmap, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQu, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hPu,
    Matrix.rank_diagonal, Nat.card_eq_fintype_card]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight fun j => by rcases hd j with h | h <;> simp [h]


end Normal


end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

