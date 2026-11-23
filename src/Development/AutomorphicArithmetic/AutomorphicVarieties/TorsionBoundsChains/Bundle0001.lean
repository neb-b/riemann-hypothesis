module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0061

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.CardStep
section
open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.cardStep :
    ∀ (A B C : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (f : A →+ B) (g : B →+ C)
      (a c : ℕ), Function.Exact f g → CardLe A a → CardLe C c → CardLe B (a * c) := by
  intro A B C _ _ _ f g a c hex hA hC
  obtain ⟨hAf, ha⟩ := hA
  obtain ⟨hCf, hc⟩ := hC
  have hker : g.ker = f.range := AddMonoidHom.exact_iff.mp hex
  have h1 : Nat.card g.ker ≤ Nat.card A := by
    rw [hker]
    exact Nat.card_le_card_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have h2 : g.ker.index ≤ Nat.card C := by
    rw [AddSubgroup.index_ker]
    exact Finite.card_subtype_le _
  haveI hfin1 : Finite g.ker := by
    rw [hker]
    exact Finite.of_surjective _ f.rangeRestrict_surjective
  have hpos1 : 0 < Nat.card g.ker := Nat.card_pos
  have hpos2 : 0 < g.ker.index := by
    rw [AddSubgroup.index_ker]
    exact Nat.card_pos
  have hcard := AddSubgroup.card_mul_index g.ker
  refine ⟨Nat.finite_of_card_ne_zero (by rw [← hcard]; positivity), ?_⟩
  rw [← hcard]
  exact Nat.mul_le_mul (h1.trans ha) (h2.trans hc)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.DetNatAbsLeProdL1Norms
section
open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.det_natAbs_le_prod_l1_norms :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ),
      M.det.natAbs ≤ ∏ i, ∑ k, (M i k).natAbs := by
  intro ι _ _ M
  have key : |M.det| ≤ ∏ i, ∑ k, |M i k| := by
    rw [← Matrix.det_transpose, Matrix.det_apply]
    let e : Equiv.Perm ι ↪ (ι → ι) := ⟨fun σ => ⇑σ, DFunLike.coe_injective⟩
    calc |∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, M.transpose (σ i) i|
        ≤ ∑ σ : Equiv.Perm ι, |Equiv.Perm.sign σ • ∏ i, M.transpose (σ i) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ σ : Equiv.Perm ι, ∏ i, |M i (σ i)| := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
            simp [h, Finset.abs_prod, Matrix.transpose_apply]
      _ = ∑ f ∈ (Finset.univ : Finset (Equiv.Perm ι)).map e, ∏ i, |M i (f i)| := by
          rw [Finset.sum_map]
          rfl
      _ ≤ ∑ f : ι → ι, ∏ i, |M i (f i)| :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun f _ _ => Finset.prod_nonneg fun i _ => abs_nonneg _)
      _ = ∏ i, ∑ k, |M i k| := (Fintype.prod_sum (fun i k => |M i k|)).symm
  have h2 : ((M.det.natAbs : ℕ) : ℤ) ≤ ((∏ i, ∑ k, (M i k).natAbs : ℕ) : ℤ) := by
    push_cast
    simpa [Int.natCast_natAbs] using key
  exact_mod_cast h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FullEnum
section
open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.fullEnum :
    ∀ (ι : Type) [Finite ι] (b : Set (ι →₀ ℤ)), LinearIndepOn ℤ id b →
      (∀ k : ι, ∃ n : ℤ, n ≠ 0 ∧ n • Finsupp.single k (1 : ℤ) ∈ Submodule.span ℤ b) →
      ∃ v : ι → (ι →₀ ℤ), LinearIndependent ℤ v ∧ Set.range v = b := by
  intro ι _ b hb hn
  have hli : LinearIndependent ℤ (fun x : b => (x : ι →₀ ℤ)) := hb
  haveI : Finite b := hli.finite
  classical
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite b
  have h1 : Fintype.card b ≤ Fintype.card ι := by
    have := hli.fintype_card_le_finrank
    rwa [Module.finrank_finsupp_self] at this
  choose n hn0 hmem using hn
  have hind : LinearIndependent ℤ (fun k : ι => n k • Finsupp.single k (1 : ℤ)) := by
    rw [linearIndependent_iff']
    intro s c hs i hi
    have := congrArg (fun f : ι →₀ ℤ => f i) hs
    simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
      Finsupp.coe_zero, Pi.zero_apply] at this
    rw [Finset.sum_eq_single i] at this
    · simp only [if_true, mul_one] at this
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h (hn0 i)
    · intro j _ hj
      simp [hj]
    · intro h
      exact absurd hi h
  let w : ι → Submodule.span ℤ b := fun k => ⟨n k • Finsupp.single k (1 : ℤ), hmem k⟩
  have hw : LinearIndependent ℤ w :=
    LinearIndependent.of_comp (Submodule.span ℤ b).subtype hind
  have h2 : Fintype.card ι ≤ Fintype.card b := by
    have := hw.fintype_card_le_finrank
    rw [finrank_span_set_eq_card hb, Set.toFinset_card] at this
    convert this
  let e : ι ≃ b := Fintype.equivOfCardEq (le_antisymm h2 h1)
  refine ⟨fun k => (e k : ι →₀ ℤ), hli.comp e e.injective, ?_⟩
  ext y
  constructor
  · rintro ⟨k, rfl⟩
    exact (e k).2
  · intro hy
    exact ⟨e.symm ⟨y, hy⟩, by simp⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.GroupHomologyLongExact
section
open CategoryTheory UpperTheory.V.KH

private theorem group_homology_long_exact (k G : Type) [CommRing k] [Group G] (A B C : Rep k G)
    (f : A ⟶ B) (g : B ⟶ C) (hf : Function.Injective f.hom) (hfg : Function.Exact f.hom g.hom)
    (hg : Function.Surjective g.hom) (j : ℕ) :
      (∃ (u : groupHomology A j →+ groupHomology B j) (v : groupHomology B j →+ groupHomology C j),
        Function.Exact u v) ∧
      (∃ (u : groupHomology B (j + 1) →+ groupHomology C (j + 1))
        (v : groupHomology C (j + 1) →+ groupHomology A j), Function.Exact u v) := by
  have h0 : f ≫ g = 0 := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact hfg.apply_apply_eq_zero x
  let X : ShortComplex (Rep k G) := ShortComplex.mk f g h0
  have hex : X.Exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful X (forget₂ (Rep k G) (ModuleCat k))]
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hfg
  have hX : X.ShortExact :=
    ShortComplex.ShortExact.mk' hex ((Rep.mono_iff_injective f).2 hf)
      ((Rep.epi_iff_surjective g).2 hg)
  have h2 := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (groupHomology.mapShortComplex₂_exact hX j)
  have h3 := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (groupHomology.mapShortComplex₃_exact hX (i := j + 1) (j := j) rfl)
  exact ⟨⟨(groupHomology.mapShortComplex₂ X j).f.hom.toAddMonoidHom,
      (groupHomology.mapShortComplex₂ X j).g.hom.toAddMonoidHom, h2⟩,
    ⟨(groupHomology.mapShortComplex₃ hX (i := j + 1) (j := j) rfl).f.hom.toAddMonoidHom,
      (groupHomology.mapShortComplex₃ hX (i := j + 1) (j := j) rfl).g.hom.toAddMonoidHom, h3⟩⟩

theorem UpperTheory.V.KH.les :
    ∀ (G : Type) [Group G] (A B C : Rep ℤ G) (f : A ⟶ B) (g : B ⟶ C),
      Function.Injective f.hom → Function.Exact f.hom g.hom → Function.Surjective g.hom → ∀ j : ℕ,
      (∃ (u : groupHomology A j →+ groupHomology B j) (v : groupHomology B j →+ groupHomology C j),
        Function.Exact u v) ∧
      (∃ (u : groupHomology B (j + 1) →+ groupHomology C (j + 1))
        (v : groupHomology C (j + 1) →+ groupHomology A j), Function.Exact u v) := by
  intro G _ A B C f g hf hfg hg j
  exact group_homology_long_exact ℤ G A B C f g hf hfg hg j
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.ImageRep
section
open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.imageRep :
    ∀ (G : Type) [Group G] (C B M : Rep ℤ G) (d : C ⟶ B) (e : B ⟶ M), Function.Exact d.hom e.hom →
      ∃ (K : Rep ℤ G) (p : C ⟶ K) (i : K ⟶ B), Function.Surjective p.hom ∧ Function.Injective i.hom ∧
        (∀ x, i.hom (p.hom x) = d.hom x) ∧ Function.Exact i.hom e.hom := by
  intro G _ C B M d e h
  have hs : Function.Surjective (Abelian.factorThruImage d).hom :=
    (Rep.epi_iff_surjective _).1 inferInstance
  have hi : Function.Injective (Abelian.image.ι d).hom :=
    (Rep.mono_iff_injective _).1 inferInstance
  have hc : ∀ x, (Abelian.image.ι d).hom ((Abelian.factorThruImage d).hom x) = d.hom x := by
    intro x
    have := congrArg (fun f : C ⟶ B => f.hom x) (Abelian.image.fac d)
    simpa using this
  refine ⟨Abelian.image d, Abelian.factorThruImage d, Abelian.image.ι d, hs, hi, hc, ?_⟩
  intro y
  rw [h y]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, hc x⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := hs z
    exact ⟨x, (hc x).symm⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.IndPerm
section
open CategoryTheory UpperTheory.V.KH

open Representation in
private theorem indV_mk_mul {k G : Type} [CommRing k] [Group G] (S : Subgroup G) (s : S) (h : G)
    (a : k) :
    IndV.mk S.subtype (Representation.trivial k S k) (s.1 * h) a =
      IndV.mk S.subtype (Representation.trivial k S k) h a := by
  have := Coinvariants.mk_self_apply
    (Representation.tprod ((leftRegular k G).comp S.subtype) (Representation.trivial k S k)) s
    (MonoidAlgebra.single h (1 : k) ⊗ₜ[k] a)
  simpa [ofMulAction_single] using this

open Representation in
private noncomputable def fwd (k G X : Type) [CommRing k] [Group G] [MulAction G X] (x : X) :
    IndV (MulAction.stabilizer G x).subtype
      (Representation.trivial k (MulAction.stabilizer G x) k) →ₗ[k] (X →₀ k) :=
  Representation.Coinvariants.lift _
    (TensorProduct.lift <| (Finsupp.lift _ _ _ fun h : G => Finsupp.lsingle (h⁻¹ • x)) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)
    fun g ↦ by
      ext h : 4
      have hg : (g : G)⁻¹ • x = x := (g⁻¹).2
      simp [mul_smul, hg]

open Representation in
private theorem fwd_mk (k G X : Type) [CommRing k] [Group G] [MulAction G X] (x : X) (h : G)
    (a : k) :
    fwd k G X x (IndV.mk _ _ h a) = Finsupp.single (h⁻¹ • x) a := by
  simp [fwd]

private theorem induced_trivial_iso_permutation (k G X : Type) [CommRing k] [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X] (x : X) (σ : Representation k G (X →₀ k))
    (hσ : ∀ g y c, σ g (Finsupp.single y c) = Finsupp.single (g • y) c) :
    Nonempty (Rep.ind (MulAction.stabilizer G x).subtype
      (Rep.trivial k (MulAction.stabilizer G x) k) ≅ Rep.of σ) := by
  choose c hc using fun y : X => MulAction.exists_smul_eq G x y
  let bwd : (X →₀ k) →ₗ[k] Representation.IndV (MulAction.stabilizer G x).subtype
      (Representation.trivial k (MulAction.stabilizer G x) k) :=
    Finsupp.lsum k fun y => Representation.IndV.mk _ _ (c y)⁻¹
  have hb : ∀ y a, bwd (Finsupp.single y a) = Representation.IndV.mk _ _ (c y)⁻¹ a := by
    intro y a
    simp [bwd]
  have h1 : fwd k G X x ∘ₗ bwd = LinearMap.id := by
    refine Finsupp.lhom_ext fun y a => ?_
    rw [LinearMap.comp_apply, hb, fwd_mk, inv_inv, hc]
    rfl
  have h2 : bwd ∘ₗ fwd k G X x = LinearMap.id := by
    refine Representation.IndV.hom_ext _ _ fun h => LinearMap.ext fun a => ?_
    show bwd (fwd k G X x (Representation.IndV.mk _ _ h a)) = Representation.IndV.mk _ _ h a
    rw [fwd_mk, hb]
    have hs : h * c (h⁻¹ • x) ∈ MulAction.stabilizer G x := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, hc, smul_inv_smul]
    have := indV_mk_mul (MulAction.stabilizer G x) ⟨_, hs⟩ (c (h⁻¹ • x))⁻¹ a
    simp only [mul_inv_cancel_right] at this
    exact this.symm
  let e : Representation.IndV (MulAction.stabilizer G x).subtype
      (Representation.trivial k (MulAction.stabilizer G x) k) ≃ₗ[k] (X →₀ k) :=
    LinearEquiv.ofLinear (fwd k G X x) bwd h1 h2
  refine ⟨Rep.mkIso (Representation.Equiv.mk e fun g => ?_)⟩
  refine Representation.IndV.hom_ext _ _ fun h => LinearMap.ext fun a => ?_
  show fwd k G X x (Representation.ind _ _ g (Representation.IndV.mk _ _ h a)) =
    σ g (fwd k G X x (Representation.IndV.mk _ _ h a))
  rw [Representation.ind_mk, fwd_mk, fwd_mk, hσ, mul_inv_rev, inv_inv, mul_smul]

theorem UpperTheory.V.KH.indPerm :
    ∀ (G X : Type) [Group G] [MulAction G X] [MulAction.IsPretransitive G X] (x : X),
      Nonempty (Rep.ind (MulAction.stabilizer G x).subtype
        (Rep.trivial ℤ (MulAction.stabilizer G x) ℤ) ≅ permRep G X) := by
  intro G X _ _ _ x
  exact induced_trivial_iso_permutation ℤ G X x (perm G X) perm_single
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.KerOrb
section
open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.kerOrb :
    ∀ (G X : Type) [Group G] [MulAction G X],
      LinearMap.ker (Finsupp.lmapDomain ℤ ℤ
        (Quotient.mk (MulAction.orbitRel G X) : X → MulAction.orbitRel.Quotient G X)) =
      Representation.Coinvariants.ker (perm G X) := by
  intro G X _ _
  set q : X → MulAction.orbitRel.Quotient G X := Quotient.mk (MulAction.orbitRel G X) with hq
  set K := Representation.Coinvariants.ker (perm G X) with hK
  apply le_antisymm
  · intro f hf
    rw [LinearMap.mem_ker, Finsupp.lmapDomain_apply] at hf
    let r : X → X := fun x => Quotient.out (q x)
    have hstep : ∀ f : X →₀ ℤ, f - Finsupp.mapDomain r f ∈ K := by
      intro f
      induction f using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb =>
        rw [Finsupp.mapDomain_add]
        have := K.add_mem ha hb
        convert this using 1
        abel
      | single x c =>
        rw [Finsupp.mapDomain_single]
        have hx : (MulAction.orbitRel G X) (r x) x := Quotient.mk_out (s := MulAction.orbitRel G X) x
        obtain ⟨g, hg⟩ := hx
        have hg' : g • x = r x := hg
        have hmem := Representation.Coinvariants.mem_ker_of_eq (ρ := perm G X) g
          (Finsupp.single x c) _ rfl
        have hneg := K.neg_mem hmem
        convert hneg using 1
        rw [perm_single, hg']
        abel
    have h0 : Finsupp.mapDomain r f = 0 := by
      have : r = (fun c => Quotient.out c) ∘ q := rfl
      rw [this, Finsupp.mapDomain_comp, hf, Finsupp.mapDomain_zero]
    have := hstep f
    rwa [h0, sub_zero] at this
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨g, v⟩, rfl⟩
    change Finsupp.lmapDomain ℤ ℤ q ((perm G X) g v - v) = 0
    rw [map_sub, perm_apply, Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply,
      ← Finsupp.mapDomain_comp]
    have : q ∘ (fun x => g • x) = q := by
      funext x
      exact Quotient.sound ⟨g, rfl⟩
    rw [this, sub_self]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.L1MapDomainLeAndL1FaceDSingleLe
section
open CategoryTheory UpperTheory.V.KH

private theorem l1_eq_sum {X : Type} (f : X →₀ ℤ) (s : Finset X) (h : f.support ⊆ s) :
    l1 f = ∑ x ∈ s, (f x).natAbs := by
  unfold l1
  exact Finsupp.sum_of_support_subset f h _ (fun _ _ => by simp)

private theorem l1_add_le {X : Type} (f g : X →₀ ℤ) : l1 (f + g) ≤ l1 f + l1 g := by
  classical
  have hs : (f + g).support ⊆ f.support ∪ g.support := Finsupp.support_add
  rw [l1_eq_sum (f + g) _ hs, l1_eq_sum f (f.support ∪ g.support) Finset.subset_union_left,
    l1_eq_sum g (f.support ∪ g.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun x _ => by
    simpa using Int.natAbs_add_le (f x) (g x)

private theorem l1_single {X : Type} (x : X) (c : ℤ) : l1 (Finsupp.single x c) = c.natAbs := by
  unfold l1
  exact Finsupp.sum_single_index (by simp)

private theorem l1_sum_le {X ι : Type} (s : Finset ι) (F : ι → X →₀ ℤ) :
    l1 (∑ i ∈ s, F i) ≤ ∑ i ∈ s, l1 (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (l1_add_le _ _).trans (Nat.add_le_add_left ih _)

theorem UpperTheory.V.KH.l1_mapDomain_le_and_l1_faceD_single_le :
    (∀ (X Y : Type) (φ : X → Y) (f : X →₀ ℤ), l1 (Finsupp.mapDomain φ f) ≤ l1 f) ∧
    (∀ (Y X : Type) (k : ℕ) (face : Fin k → Y → X) (y : Y),
      l1 (faceD face (Finsupp.single y 1)) ≤ k) := by
  refine ⟨fun X Y φ f => ?_, fun Y X k face y => ?_⟩
  · have h : Finsupp.mapDomain φ f = ∑ x ∈ f.support, Finsupp.single (φ x) (f x) := rfl
    rw [h]
    refine (l1_sum_le _ _).trans (le_of_eq ?_)
    simp only [l1_single]
    rfl
  · rw [faceD_single]
    refine (l1_sum_le _ _).trans (le_of_eq ?_)
    simp [Finsupp.smul_single, l1_single, Int.natAbs_pow]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.MapNsmul
section
open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.mapNsmul :
    ∀ (G : Type) [Group G] (A B : Rep ℤ G) (f : A ⟶ B) (g : B ⟶ A) (n j : ℕ),
      (∀ a, g.hom (f.hom a) = n • a) → Subsingleton (groupHomology B j) →
      ∀ z : groupHomology A j, n • z = 0 := by
  intro G _ A B f g n j h hB z
  have hc : groupHomology.chainsMap (MonoidHom.id G) (f ≫ g) =
      n • 𝟙 (groupHomology.inhomogeneousChains A) := by
    ext i : 1
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun c => ?_
    refine Finsupp.ext fun y => ?_
    simp [h]
  have hm : groupHomology.map (MonoidHom.id G) (f ≫ g) j = n • 𝟙 (groupHomology A j) := by
    simp only [groupHomology.map, hc]
    change (HomologicalComplex.homologyFunctor _ _ j).map _ = _
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
    rfl
  have e1 : (groupHomology.map (MonoidHom.id G) (f ≫ g) j).hom z = n • z := by
    rw [hm]
    rfl
  rw [← e1, groupHomology.map_id_comp]
  have e2 : (groupHomology.map (MonoidHom.id G) f j).hom z = 0 :=
    Subsingleton.elim (α := groupHomology B j) _ _
  simp [e2]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.MaxIndep
section
open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.maxIndep :
    ∀ (M : Type) [AddCommGroup M] [IsAddTorsionFree M] (s t : Set M), s ⊆ t →
      LinearIndepOn ℤ id s → ∃ b : Set M, s ⊆ b ∧ b ⊆ t ∧ LinearIndepOn ℤ id b ∧
        ∀ x ∈ t, ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ Submodule.span ℤ b := by
  intro M _ _ s t hst hs
  let S : Set (Set M) := {b | s ⊆ b ∧ b ⊆ t ∧ LinearIndepOn ℤ id b}
  obtain ⟨m, hsm, hmax⟩ := zorn_subset_nonempty S (by
    intro c hcS hc hne
    refine ⟨⋃₀ c, ⟨?_, ?_, ?_⟩, fun b hb => Set.subset_sUnion_of_mem hb⟩
    · obtain ⟨b, hb⟩ := hne
      exact (hcS hb).1.trans (Set.subset_sUnion_of_mem hb)
    · exact Set.sUnion_subset fun b hb => (hcS hb).2.1
    · exact linearIndepOn_sUnion_of_directed hc.directedOn fun b hb => (hcS hb).2.2)
    s ⟨subset_rfl, hst, hs⟩
  obtain ⟨-, hmt, hmi⟩ := hmax.prop
  refine ⟨m, hsm, hmt, hmi, fun x hx => ?_⟩
  by_cases hxm : x ∈ m
  · exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span hxm⟩
  have hdep : ¬ LinearIndepOn ℤ id (insert x m) := by
    intro hi
    have he := hmax.eq_of_subset
      ⟨hsm.trans (Set.subset_insert _ _), Set.insert_subset hx hmt, hi⟩ (Set.subset_insert _ _)
    exact hxm (he ▸ Set.mem_insert x m)
  rw [linearIndepOn_iff] at hdep
  push_neg at hdep
  obtain ⟨l, hl, hl0, hlne⟩ := hdep
  have hl' : Finsupp.erase x l ∈ Finsupp.supported ℤ ℤ m := by
    rw [Finsupp.mem_supported] at hl ⊢
    intro y hy
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hy
    have hyx : y ≠ x := by
      rintro rfl
      exact hy (by simp)
    rw [Finsupp.erase_ne hyx] at hy
    exact (hl (Finsupp.mem_support_iff.mpr hy)).resolve_left hyx
  have hsum : l x • x + Finsupp.linearCombination ℤ id (Finsupp.erase x l) = 0 := by
    have h1 := congrArg (Finsupp.linearCombination ℤ id) (Finsupp.single_add_erase x l)
    rw [map_add (f := _), Finsupp.linearCombination_single, hl0] at h1
    simpa using h1
  have hxne : l x ≠ 0 := by
    intro h0
    apply hlne
    have he : Finsupp.erase x l = l := by
      ext y
      by_cases hy : y = x
      · subst hy
        simp [h0]
      · simp [Finsupp.erase_ne hy]
    rw [← he]
    apply (linearIndepOn_iff.mp hmi) _ hl'
    rw [h0, zero_smul, zero_add] at hsum
    exact hsum
  refine ⟨l x, hxne, ?_⟩
  have hmem : Finsupp.linearCombination ℤ id (Finsupp.erase x l) ∈ Submodule.span ℤ m := by
    have h2 := (Finsupp.mem_span_image_iff_linearCombination ℤ (v := id) (s := m)).mpr ⟨_, hl', rfl⟩
    simpa using h2
  rw [eq_neg_of_add_eq_zero_left hsum]
  exact Submodule.neg_mem _ hmem
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.TorsStep
section
open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.torsStep :
    ∀ (A B C : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (f : A →+ B) (g : B →+ C)
      (a c : ℕ), Function.Exact f g → CardLe A a → TorsLe C c → TorsLe B (a * c) :=
  _root_.UpperTheory.Reformulated.B.Qf15.torsStep
end

