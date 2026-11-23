module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.EtaleCohomology.EtaleSheaves.Bundle0039
public import Development.EtaleCohomology.TateTwists.Bundle0016

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafFibreFieldPf
section
open AlgebraicGeometry CategoryTheory Topology

namespace LateralTheory.E.LeafFibreFieldPf

open Cardinal IntermediateField in
theorem alg_part (k K : Type) [Field k] [Field K] [Algebra k K] (S : Finset K)
    (hgen : IntermediateField.adjoin k (S : Set K) = ⊤) (d : ℕ) (hd : Algebra.trdeg k K = d + 1) :
    ∃ (F : IntermediateField k K) (s : Finset F) (t : K), s.card ≤ d ∧
      Algebra.IsAlgebraic (IntermediateField.adjoin k (s : Set F)) F ∧ Transcendental F t ∧
      FiniteDimensional (IntermediateField.adjoin F {t}) K := by
  classical
  obtain ⟨B, hB⟩ := exists_isTranscendenceBasis k K
  have hcard : #B = ((d + 1 : ℕ) : Cardinal) := by
    rw [hB.cardinalMk_eq_trdeg, hd]; push_cast; rfl
  obtain ⟨T, hTB, hTc⟩ := Cardinal.mk_set_eq_nat_iff_finset.mp hcard
  obtain ⟨a, haT⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
  set T' := T.erase a with hT'
  let F : IntermediateField k K := IntermediateField.adjoin k (T' : Set K)
  let sF : Finset F := T'.attach.image fun x => ⟨x.1, IntermediateField.subset_adjoin k _ x.2⟩
  have hsF : (F.val '' (sF : Set F)) = (T' : Set K) := by
    ext y; simp [sF]; intro h; exact IntermediateField.subset_adjoin k _ (Finset.mem_coe.mpr h)
  refine ⟨F, sF, a, ?_, ?_, ?_, ?_⟩
  · refine (Finset.card_image_le).trans ?_
    rw [Finset.card_attach, Finset.card_erase_of_mem haT, hTc]; simp
  · have hmem : ∀ y : F, y ∈ IntermediateField.adjoin k (sF : Set F) := by
      intro y
      have : (y : K) ∈ (IntermediateField.adjoin k (sF : Set F)).map F.val := by
        rw [IntermediateField.adjoin_map, hsF]; exact y.2
      rw [← SetLike.mem_coe, IntermediateField.coe_map] at this
      obtain ⟨z, hz, hzy⟩ := this
      have : z = y := Subtype.ext hzy
      exact this ▸ hz
    exact ⟨fun y => by
      have := isAlgebraic_algebraMap (R := IntermediateField.adjoin k (sF : Set F)) (A := F) ⟨y, hmem y⟩
      exact this⟩
  · have hind := hB.1
    have hnot : (⟨a, hTB ▸ haT⟩ : B) ∉ {i : B | (i : K) ≠ a} := by simp
    have htr := hind.transcendental_adjoin hnot
    have himg : (Subtype.val '' {i : B | (i : K) ≠ a}) = (T' : Set K) := by
      ext y; simp only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_right,
        exists_eq_right, hT', Finset.coe_erase, Set.mem_diff, Set.mem_singleton_iff, ← hTB]
      tauto
    rw [himg, ← IntermediateField.transcendental_adjoin_iff] at htr
    exact htr
  ·
    set L := IntermediateField.adjoin F {a} with hL
    have hBT : (B : Set K) = (T : Set K) := hTB.symm
    have halgB := hB.isAlgebraic_field
    rw [Subtype.range_coe] at halgB
    set E := IntermediateField.adjoin k B with hE
    have hEL : ∀ x ∈ E, x ∈ L := by
      intro x hx
      have hle : E ≤ L.restrictScalars k := by
        rw [hE, IntermediateField.adjoin_le_iff]
        intro b hb
        rw [← hTB] at hb
        by_cases hba : b = a
        · subst hba; exact IntermediateField.mem_adjoin_simple_self F b
        · have hbF : b ∈ F := IntermediateField.subset_adjoin k _ (by simp [hT', hba, hb])
          exact (IntermediateField.algebraMap_mem L (⟨b, hbF⟩ : F))
      exact hle hx
    let g : E →+* L :=
      { toFun := fun x => ⟨x.1, hEL x.1 x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
        map_zero' := rfl, map_add' := fun _ _ => rfl }
    let _ : Algebra E L := g.toAlgebra
    have : IsScalarTower E L K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hint : ∀ x : K, IsIntegral L x := fun x =>
      ((halgB.isAlgebraic x).extendScalars g.injective).isIntegral
    have hfd := IntermediateField.finiteDimensional_adjoin (K := L) (S := (S : Set K)) (fun x _ => hint x)
    have htop : IntermediateField.adjoin L (S : Set K) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : x ∈ IntermediateField.adjoin k (S : Set K) := hgen ▸ trivial
      let M : IntermediateField k K :=
        { carrier := (IntermediateField.adjoin L (S : Set K) : Set K)
          mul_mem' := fun ha hb => (IntermediateField.adjoin L (S : Set K)).mul_mem ha hb
          add_mem' := fun ha hb => (IntermediateField.adjoin L (S : Set K)).add_mem ha hb
          inv_mem' := fun _ hx => (IntermediateField.adjoin L (S : Set K)).inv_mem hx
          algebraMap_mem' := fun c => by
            have h1 := IntermediateField.algebraMap_mem (IntermediateField.adjoin L (S : Set K))
              (⟨algebraMap F K (algebraMap k F c), IntermediateField.algebraMap_mem L _⟩ : L)
            rw [IsScalarTower.algebraMap_apply k F K]
            exact h1 }
      have hle : IntermediateField.adjoin k (S : Set K) ≤ M := by
        rw [IntermediateField.adjoin_le_iff]
        intro y hy
        show y ∈ (IntermediateField.adjoin L (S : Set K) : Set K)
        exact IntermediateField.subset_adjoin L _ hy
      exact (hle hx : x ∈ (IntermediateField.adjoin L (S : Set K) : Set K))
    rw [htop] at hfd
    exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := L) (E := K)).toLinearEquiv

theorem gen_top (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    ∃ S : Finset (FractionRing A), IntermediateField.adjoin k (S : Set (FractionRing A)) = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := (‹Algebra.FiniteType k A›).out
  refine ⟨s.image (algebraMap A (FractionRing A)), ?_⟩
  have hA : ∀ a : A, algebraMap A (FractionRing A) a ∈
      IntermediateField.adjoin k ((s.image (algebraMap A (FractionRing A)) : Finset _) : Set (FractionRing A)) := by
    intro a
    have ha : a ∈ Algebra.adjoin k (s : Set A) := hs ▸ Algebra.mem_top
    have h1 : algebraMap A (FractionRing A) a ∈ (Algebra.adjoin k (s : Set A)).map (IsScalarTower.toAlgHom k A (FractionRing A)) :=
      Subalgebra.mem_map.mpr ⟨a, ha, rfl⟩
    rw [AlgHom.map_adjoin] at h1
    refine IntermediateField.algebra_adjoin_le_adjoin k _ ?_
    simpa [Finset.coe_image] using h1
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  exact div_mem (hA a) (hA b)

theorem dimX_eq (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] (e : ℕ)
    (he : letI := (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p)).hom.toAlgebra
      Algebra.trdeg k X.functionField = e) :
    topologicalKrullDim X = e := by
  have h := GlobalTheory.topologicalKrullDim_eq_of_forall_exists_isOpen (Z := (Set.univ : Set X))
    ⟨genericPoint X, trivial⟩ (d := (e : WithBot ℕ∞)) (fun x _ => by
      obtain ⟨A, _, _, _, _, _, j, _, hx, -, htr⟩ := GlobalTheory.exists_affine_chart_trdeg_eq p x
      refine ⟨Set.range j, j.isOpenEmbedding.isOpen_range, hx, ?_⟩
      rw [Set.inter_univ, GlobalTheory.topologicalKrullDim_eq_of_isEmbedding j.isOpenEmbedding.isEmbedding rfl]
      have hA := GlobalTheory.ringKrullDim_eq_of_trdeg_eq k A (htr.trans he)
      rw [← hA]
      exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A)
  rw [← h]
  exact (GlobalTheory.topologicalKrullDim_eq_of_isEmbedding (e := (id : X → X)) IsEmbedding.id (Set.range_id)).symm

theorem LeafFibreField_of : LateralTheory.E.LeafCurveVCut.LeafFibreField := by
  intro k _ X _ p _ hd
  letI := (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p)).hom.toAlgebra
  obtain ⟨A, _, _, _, _, _, j, _, hx, hj, htr⟩ := GlobalTheory.exists_affine_chart_trdeg_eq p (genericPoint X)
  obtain ⟨e, -, he2⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k A
  have hdim := dimX_eq k p e (htr.symm.trans he2)
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := by
    cases e with
    | zero => rw [hdim] at hd; simp at hd
    | succ d => exact ⟨d, rfl⟩
  have : Algebra.IsAlgebraic A (FractionRing A) := IsLocalization.isAlgebraic _ (nonZeroDivisors A)
  have htrK : Algebra.trdeg k (FractionRing A) = d + 1 := by
    rw [GlobalTheory.trdeg_eq_of_isAlgebraic_top k A (FractionRing A), he2]; push_cast; rfl
  obtain ⟨S, hS⟩ := gen_top k A
  obtain ⟨F, s, t, hs, halg, ht, hfin⟩ := alg_part k (FractionRing A) S hS d htrK
  refine ⟨F, inferInstance, inferInstance, FractionRing A, inferInstance, inferInstance, d, s, t,
    Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))) ≫ j, ?_, hs, halg, ht, hfin, ?_, ?_⟩
  · rw [hdim]; exact_mod_cast Nat.lt_succ_self d
  · rw [Category.assoc, hj, ← Spec.map_comp]
    congr 1
  · obtain ⟨q, hq⟩ := hx
    obtain ⟨pt⟩ : Nonempty (Spec (.of (FractionRing A))) := inferInstance
    refine ⟨pt, ?_⟩
    have hz : (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))) pt ⤳ q := by
      refine (PrimeSpectrum.le_iff_specializes _ _).mp ?_
      show Ideal.comap (algebraMap A (FractionRing A)) pt.asIdeal ≤ q.asIdeal
      have hbot : pt.asIdeal = ⊥ := by
        rcases Ideal.eq_bot_or_top pt.asIdeal with h | h
        · exact h
        · exact absurd h pt.isPrime.ne_top
      intro a ha
      rw [Ideal.mem_comap, hbot, Ideal.mem_bot] at ha
      rw [(IsFractionRing.injective A (FractionRing A)) (ha.trans (map_zero _).symm)]
      exact zero_mem _
    have h1 := hz.map j.continuous
    rw [hq] at h1
    have h2 := (genericPoint_spec X).specializes
      (Set.mem_univ (j ((Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))) pt)))
    rw [Scheme.Hom.comp_apply]
    exact (h1.antisymm h2).eq

end LateralTheory.E.LeafFibreFieldPf
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTrdegDimPf
section
namespace LateralTheory.E.LeafTrdegDimPf

open Algebra

theorem trdeg_le_card (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F)
    (h : Algebra.IsAlgebraic (IntermediateField.adjoin k (s : Set F)) F) :
    Algebra.trdeg k F ≤ (s.card : Cardinal) := by
  have : Algebra.IsAlgebraic (Algebra.adjoin k (s : Set F)) F :=
    ⟨fun x => IntermediateField.isAlgebraic_adjoin_iff.1 (h.isAlgebraic x)⟩
  obtain ⟨t, hts, hb⟩ := exists_isTranscendenceBasis_subset (R := k) (A := F) (s : Set F)
  rw [← hb.cardinalMk_eq_trdeg]
  calc Cardinal.mk t ≤ Cardinal.mk (s : Set F) := Cardinal.mk_le_mk_of_subset hts
    _ = (s.card : Cardinal) := by simp

theorem LeafTrdegDim_of : LateralTheory.E.LeafCurveVCut.LeafTrdegDim := by
  intro k F Ω _ _ _ _ _ _ _ _ n s hs hF R hR
  have hFT : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType R).1 hR
  obtain ⟨d, hd1, hd2⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k R
  have h1 : Algebra.trdeg k R ≤ Algebra.trdeg k Ω :=
    trdeg_le_of_injective R.val Subtype.val_injective
  have h2 : Algebra.trdeg k Ω = Algebra.trdeg k F := GlobalTheory.trdeg_eq_of_isAlgebraic_top k F Ω
  have h3 := trdeg_le_card k F s hF
  have hdn : (d : Cardinal) ≤ (n : Cardinal) := by
    rw [← hd2]
    exact h1.trans (h2 ▸ h3.trans (by exact_mod_cast hs))
  have : d ≤ n := by exact_mod_cast hdn
  rw [hd1]
  exact_mod_cast this

end LateralTheory.E.LeafTrdegDimPf
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTwInjPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.LeafTwSecPf

namespace LateralTheory.E.LeafTwInjPf

theorem prim_field {q : ℕ} [NeZero q] {A : Type} [CommRing A] {K : Type} [Field K] (π : A →+* K)
    (ξ : Prim q A) : IsPrimitiveRoot (π ξ.1) q := by
  have hq : (q : K) ≠ 0 := by simpa using (ξ.2.1.map π).ne_zero
  haveI : NeZero (q : K) := ⟨hq⟩
  rw [← Polynomial.isRoot_cyclotomic_iff]
  have h := Polynomial.aeval_algHom_apply π.toIntAlgHom ξ.1 (Polynomial.cyclotomic q ℤ)
  rw [ξ.2.2, map_zero] at h
  rw [Polynomial.IsRoot, ← Polynomial.map_cyclotomic q (Int.castRingHom K), Polynomial.eval_map]
  rw [Polynomial.aeval_def, algebraMap_int_eq] at h
  exact h

theorem pow_val_eq {q : ℕ} [NeZero q] {K : Type} [Field K] {μ : K} (hμ : IsPrimitiveRoot μ q) (m n : ℕ) :
    μ ^ m = μ ^ n ↔ (m : ZMod q) = n := by
  have hf : IsOfFinOrder μ := isOfFinOrder_iff_pow_eq_one.2 ⟨q, NeZero.pos q, hμ.pow_eq_one⟩
  rw [hf.pow_eq_pow_iff_modEq, ← hμ.eq_orderOf, ZMod.natCast_eq_natCast_iff]

theorem key {q : ℕ} [NeZero q] {A : Type} [CommRing A] [Nontrivial A] (i : ℤ) (ζ : Prim q A)
    (c : ULift.{1} (ZMod q))
    (h : c • (Submodule.Quotient.mk (p := twRel q i A) (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))) = 0) :
    c = 0 := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  let π : A →+* A ⧸ m := Ideal.Quotient.mk m
  have hμ := prim_field π ζ
  have hex : ∀ ξ : Prim q A, ∃ u : (ZMod q)ˣ, π ξ.1 = π ζ.1 ^ (u : ZMod q).val := by
    intro ξ
    obtain ⟨j, hj, hj'⟩ := hμ.eq_pow_of_pow_eq_one (prim_field π ξ).pow_eq_one
    have cop : j.Coprime q := (hμ.pow_iff_coprime (NeZero.pos q) j).1 (hj' ▸ prim_field π ξ)
    refine ⟨ZMod.unitOfCoprime j cop, ?_⟩
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hj, hj']
  have uniq : ∀ u w : (ZMod q)ˣ, π ζ.1 ^ (u : ZMod q).val = π ζ.1 ^ (w : ZMod q).val → u = w := by
    intro u w huw
    rw [pow_val_eq hμ, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at huw
    exact Units.ext huw
  choose e he using hex
  have hmul : ∀ (ζ' ξ : Prim q A) (b : (ZMod q)ˣ), ξ.1 = ζ'.1 ^ (b : ZMod q).val → e ξ = e ζ' * b := by
    intro ζ' ξ b hb
    apply uniq
    rw [← he ξ, hb, map_pow, he ζ', ← pow_mul, pow_val_eq hμ]
    push_cast
    simp [ZMod.natCast_zmod_val]
  have h1 : e ζ = 1 := by
    apply uniq
    rw [← he ζ]
    conv_lhs => rw [← pow_one (π ζ.1)]
    rw [pow_val_eq hμ]
    simp [ZMod.natCast_zmod_val]
  let f := Finsupp.linearCombination (ULift.{1} (ZMod q))
    (fun ξ : Prim q A => (ULift.up (((e ξ) ^ i : (ZMod q)ˣ) : ZMod q) : ULift.{1} (ZMod q)))
  have hker : twRel q i A ≤ LinearMap.ker f := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨ζ', ξ, b, hb, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, f, Finsupp.linearCombination_single,
      hmul ζ' ξ b hb, mul_zpow, sub_eq_zero]
    apply ULift.ext
    simp [mul_comm]
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
  have h2 := hker h
  rw [LinearMap.mem_ker, map_smul] at h2
  have h3 : (ULift.up (1 : ZMod q) : ULift.{1} (ZMod q)) = 1 := rfl
  simpa [f, Finsupp.linearCombination_single, h1, h3] using h2

theorem aux {q : ℕ} [NeZero q] {A : Type} [CommRing A] [Nontrivial A] (i : ℤ) (ζ : Prim q A)
    (x y : ULift.{1} (ZMod q))
    (h : x • (Submodule.Quotient.mk (p := twRel q i A) (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))) =
      y • (Submodule.Quotient.mk (p := twRel q i A) (Finsupp.single ζ (1 : ULift.{1} (ZMod q))))) : x = y :=
  sub_eq_zero.1 (key i ζ (x - y) (by rw [sub_smul, sub_eq_zero]; exact h))

theorem LeafTwInj_of : LeafTwInj := by
  intro q _ B _ ζ k
  refine ⟨fun {X} x y h => ?_⟩
  change ULift.{1} (ZMod q) at x y
  by_cases hX : Nonempty X.unop.left
  · haveI : Nontrivial Γ(X.unop.left, ⊤) := by
      obtain ⟨p⟩ := hX
      exact RingHom.domain_nontrivial (X.unop.left.presheaf.germ ⊤ p trivial).hom
    have h0 : x • gen ζ k X.unop = y • gen ζ k X.unop := h
    have hxy : x = y := aux (A := Γ(X.unop.left, ⊤)) k _ x y h0
    subst hxy
    rw [Presheaf.equalizerSieve_self_eq_top]
    exact GrothendieckTopology.top_mem _ _
  · haveI : IsEmpty X.unop.left := not_nonempty_iff.1 hX
    rw [GrothendieckTopology.mem_over_iff]
    refine GrothendieckTopology.superset_covering _ bot_le ?_
    first
      | exact Scheme.bot_mem_grothendieckTopology _
      | exact bot_mem_grothendieckTopology _
      | exact AlgebraicGeometry.Scheme.bot_mem_grothendieckTopology (P := @Etale) _

end LateralTheory.E.LeafTwInjPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTwSurjPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.LeafTwSecPf

namespace LateralTheory.E.LeafTwSurjPf

variable {q : ℕ} {B : Type} [CommRing B] (ζ : Prim q B) (k : ℤ)

theorem mem_add {U : Over (Spec (CommRingCat.of B))} (s t : ToType ((Pr q k _).obj (op U)))
    (hs : Presheaf.imageSieve (cmap ζ k) s ∈ Scheme.etaleTopology.over _ U)
    (ht : Presheaf.imageSieve (cmap ζ k) t ∈ Scheme.etaleTopology.over _ U) :
    Presheaf.imageSieve (cmap ζ k) (s + t) ∈ Scheme.etaleTopology.over _ U := by
  refine GrothendieckTopology.superset_covering _ ?_ (GrothendieckTopology.intersection_covering _ hs ht)
  rintro V f ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  exact ⟨a + b, by rw [map_add (f := _), ha, hb, map_add (f := _)]⟩

theorem mem_smul {U : Over (Spec (CommRingCat.of B))} (c : ULift.{1} (ZMod q)) (s : ToType ((Pr q k _).obj (op U)))
    (hs : Presheaf.imageSieve (cmap ζ k) s ∈ Scheme.etaleTopology.over _ U) :
    Presheaf.imageSieve (cmap ζ k) (c • s) ∈ Scheme.etaleTopology.over _ U := by
  refine GrothendieckTopology.superset_covering _ ?_ hs
  rintro V f ⟨a, ha⟩
  exact ⟨c • a, by rw [map_smul, ha, map_smul]⟩

theorem mem_zero {U : Over (Spec (CommRingCat.of B))} :
    Presheaf.imageSieve (cmap ζ k) (0 : ToType ((Pr q k _).obj (op U))) ∈ Scheme.etaleTopology.over _ U := by
  refine GrothendieckTopology.superset_covering _ ?_ (GrothendieckTopology.top_mem _ U)
  rintro V f -
  exact ⟨0, by rw [map_zero, map_zero]⟩

theorem rel_single {A : Type} [CommRing A] (ζ' ξ : Prim q A) (a : (ZMod q)ˣ) (h : ξ.1 = ζ'.1 ^ (a : ZMod q).val) :
    Submodule.Quotient.mk (p := twRel q k A) (Finsupp.single ξ 1) =
      (ULift.up ((a ^ k : (ZMod q)ˣ) : ZMod q)) • Submodule.Quotient.mk (p := twRel q k A) (Finsupp.single ζ' 1) := by
  have hm : Finsupp.single ξ 1 - Finsupp.single ζ' (ULift.up ((a ^ k : (ZMod q)ˣ) : ZMod q)) ∈ twRel q k A :=
    Submodule.subset_span ⟨ζ', ξ, a, h, rfl⟩
  rw [← Submodule.Quotient.mk_smul, Finsupp.smul_single, Submodule.Quotient.eq]
  convert hm using 3
  first | rfl | (ext1; simp)

theorem rel_map {A A' : Type} [CommRing A] [CommRing A'] (φ : Prim q A → Prim q A') (ζ' ξ : Prim q A)
    (a : (ZMod q)ˣ) (h : (φ ξ).1 = (φ ζ').1 ^ (a : ZMod q).val) :
    Submodule.Quotient.mk (p := twRel q k A') (Finsupp.mapDomain φ (Finsupp.single ξ 1)) =
      (ULift.up ((a ^ k : (ZMod q)ˣ) : ZMod q)) •
        Submodule.Quotient.mk (p := twRel q k A') (Finsupp.mapDomain φ (Finsupp.single ζ' 1)) := by
  rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single]
  exact rel_single k _ _ a h

theorem mem_single [NeZero q] (U : Over (Spec (CommRingCat.of B))) (ξ : Prim q Γ(U.left, ⊤)) :
    Presheaf.imageSieve (cmap ζ k)
      (Submodule.Quotient.mk (p := twRel q k Γ(U.left, ⊤)) (Finsupp.single ξ 1) : ToType ((Pr q k _).obj (op U)))
      ∈ Scheme.etaleTopology.over _ U := by
  obtain ⟨S, hS, hP⟩ := LateralTheory.EtaleFoundations.PrimLocPf.part2 q U.left (Prim.map (ρ U) ζ) ξ
  rw [GrothendieckTopology.mem_over_iff]
  refine GrothendieckTopology.superset_covering _ ?_ hS
  intro W g hg
  rw [Sieve.overEquiv_iff]
  obtain ⟨a, ha⟩ := hP W g hg
  refine ⟨ULift.up ((a ^ k : (ZMod q)ˣ) : ZMod q), ?_⟩
  change LinearMap.toSpanSingleton _ _ (gen ζ k (Over.mk (g ≫ U.hom))) (ULift.up ((a ^ k : (ZMod q)ˣ) : ZMod q)) =
    ((Pr q k _).map (Over.homMk g : Over.mk (g ≫ U.hom) ⟶ U).op).hom
      (Submodule.Quotient.mk (p := twRel q k Γ(U.left, ⊤)) (Finsupp.single ξ 1))
  rw [LinearMap.toSpanSingleton_apply, ← gen_map ζ k (Over.homMk g : Over.mk (g ≫ U.hom) ⟶ U)]
  exact (rel_map k _ _ _ a ha).symm

end LateralTheory.E.LeafTwSurjPf

namespace LateralTheory.E.LeafTwSecPf

theorem LeafTwSurj_of : LeafTwSurj := by
  intro q _ B _ ζ k
  constructor
  intro U s
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (twRel q k Γ(U.left, ⊤)) s
  induction x using Finsupp.induction_linear with
  | zero => exact LateralTheory.E.LeafTwSurjPf.mem_zero ζ k
  | add f g hf hg =>
    rw [Submodule.Quotient.mk_add]
    exact LateralTheory.E.LeafTwSurjPf.mem_add ζ k _ _ hf hg
  | single ξ c =>
    have h : Finsupp.single ξ c = c • Finsupp.single ξ (1 : ULift.{1} (ZMod q)) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h, Submodule.Quotient.mk_smul]
    exact LateralTheory.E.LeafTwSurjPf.mem_smul ζ k c _ (LateralTheory.E.LeafTwSurjPf.mem_single ζ k U ξ)

end LateralTheory.E.LeafTwSecPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafUnitActPfAug
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitActPfAug

def sumC (q : ℕ) (A : Type) [CommRing A] : (Prim q A →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Finsupp.linearCombination _ (fun _ => 1)

theorem twRel_zero_le (q : ℕ) (A : Type) [CommRing A] : twRel q 0 A ≤ LinearMap.ker (sumC q A) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, -, rfl⟩
  simp [sumC]
  exact sub_self _

def aug (q : ℕ) (A : Type) [CommRing A] :
    ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 A) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  (twRel q 0 A).liftQ (sumC q A) (twRel_zero_le q A)

theorem aug_mk_single (q : ℕ) {A : Type} [CommRing A] (ζ : Prim q A) :
    aug q A (Submodule.Quotient.mk (Finsupp.single ζ 1)) = 1 := by
  simp [aug, sumC]

theorem aug_map (q : ℕ) {A B : CommRingCat.{0}} (f : A ⟶ B) (x : (twF q 0).obj A) :
    aug q B (((twF q 0).map f).hom x) = aug q A x := by
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    change aug q B (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) y)) = aug q A (Submodule.Quotient.mk y)
    simp only [aug, Submodule.liftQ_apply, sumC]
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add u v hu hv => simp [Finsupp.mapDomain_add, hu, hv]
    | single p c => simp [Finsupp.mapDomain_single]

end LateralTheory.E.LeafUnitActPfAug

namespace LateralTheory.E.LeafUnitActPfAug
open LateralTheory.E.CupProductRingLaws

theorem etale_tate_twist_zero_section_locally_lifts_to_ring_value (q : ℕ) {U : Scheme.{0}} (a : Sec (tw q 0) U) :
    Loc U (fun V g => ∃ x : (twF q 0).obj Γ(V, ⊤), Sec.res g a = ofRings.sec (twF q 0) V x) := by
  refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology.{0}
    (toSheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ twF q 0)) (U := op U) a, fun V g ⟨t, ht⟩ => ⟨t, ht.symm⟩⟩

theorem etale_tate_twist_zero_sections_eq_locally_of_sheafified_eq (q : ℕ) {U : Scheme.{0}} (x y : (twF q 0).obj Γ(U, ⊤))
    (h : ofRings.sec (twF q 0) U x = ofRings.sec (twF q 0) U y) :
    Loc U (fun V g => ((twF q 0).map g.appTop).hom x = ((twF q 0).map g.appTop).hom y) := by
  refine ⟨_, Presheaf.equalizerSieve_mem Scheme.etaleTopology.{0}
    (toSheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ twF q 0)) (X := op U) x y h, fun V g hg => hg⟩

end LateralTheory.E.LeafUnitActPfAug
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LocSecPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LocSecPf

abbrev pt (R : Type) [CommRing R] (X : Scheme.{0}) : Cx R :=
  (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj ((free R).obj (yoneda.obj X))

def LocSecA : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F : Shv R) (n : ℤ),
  Nonempty (H R (sch.obj X) F n ≃+ CohomologyClass (pt R X) (res R F) n)

def LocSecB : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F : Shv R) (n : ℤ),
  Nonempty (CohomologyClass (pt R X) (res R F) n ≃+ (LateralTheory.E.LeafLocPf.secCx F X).homology n)

theorem LocSec_of (hA : LocSecA) (hB : LocSecB) : LateralTheory.E.LeafLocPf.LocSec := by
  intro _ R _ X F n
  obtain ⟨a⟩ := hA R X F n
  obtain ⟨b⟩ := hB R X F n
  exact ⟨a.trans b⟩

end LateralTheory.E.LocSecPf
end
end

