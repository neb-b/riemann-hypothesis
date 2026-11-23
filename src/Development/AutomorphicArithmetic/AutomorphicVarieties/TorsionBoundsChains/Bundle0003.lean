module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.IndexLe
section
open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.indexLe :
    ∀ (ι : Type) [Finite ι] (v : ι → (ι →₀ ℤ)) (b : ℕ), LinearIndependent ℤ v → (∀ i, l1 (v i) ≤ b) →
      CardLe ((ι →₀ ℤ) ⧸ Submodule.span ℤ (Set.range v)) (b ^ Nat.card ι) := by
  intro ι _ v b hv hb
  classical
  haveI := Fintype.ofFinite ι
  set N := Submodule.span ℤ (Set.range v)
  let bE : Module.Basis ι ℤ (ι →₀ ℤ) := Finsupp.basisSingleOne
  let bN : Module.Basis ι ℤ N := Module.Basis.span hv
  have hfin : Finite ((ι →₀ ℤ) ⧸ N) := by
    apply Submodule.finiteQuotientOfFreeOfRankEq
    rw [Module.finrank_eq_card_basis bN, Module.finrank_eq_card_basis bE]
  refine ⟨hfin, ?_⟩
  rw [← Submodule.natAbs_det_basis_change bE N bN]
  have hcoe : ((↑) ∘ bN : ι → (ι →₀ ℤ)) = v := by
    funext i
    exact congrArg Subtype.val (Module.Basis.span_apply hv i)
  rw [hcoe, Module.Basis.det_apply, ← Matrix.det_transpose]
  refine (det_natAbs_le_prod_l1_norms ι _).trans ?_
  have hrow : ∀ i, ∑ k, ((bE.toMatrix v).transpose i k).natAbs = l1 (v i) := by
    intro i
    simp only [Matrix.transpose_apply, Module.Basis.toMatrix_apply, bE, Finsupp.basisSingleOne_repr,
      LinearEquiv.refl_apply, l1]
    rw [Finsupp.sum_fintype]
    simp
  simp_rw [hrow]
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  exact Finset.prod_le_pow_card _ _ _ (fun i _ => hb i)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.QuotientsEquivOfKerEq
section
open CategoryTheory UpperTheory.V.KH

private theorem UpperTheory.V.KH.quotients_equiv_of_ker_eq {A B C : Type} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (a : A →+ B) (b : A →+ C) (ha : Function.Surjective a)
    (hb : Function.Surjective b) (h : a.ker = b.ker) : Nonempty (B ≃+ C) :=
  ⟨(QuotientAddGroup.quotientKerEquivOfSurjective a ha).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq h).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective b hb))⟩

private theorem UpperTheory.V.KH.hZero_push {R G : Type} [CommRing R] [Group G] (N M : Rep.{0} R G) (e : N ⟶ M) (x : N)
    (hx : x ∈ Representation.Coinvariants.ker N.ρ) :
    e.hom x ∈ Representation.Coinvariants.ker M.ρ := by
  have := (Representation.Coinvariants.mk_eq_zero N.ρ).2 hx
  rw [← Representation.Coinvariants.mk_eq_zero, ← Representation.Coinvariants.map_mk, this,
    map_zero]

private theorem UpperTheory.V.KH.hZero_lift {R G : Type} [CommRing R] [Group G] (N M : Rep.{0} R G) (e : N ⟶ M)
    (he : Function.Surjective e.hom) (y : M)
    (hy : y ∈ Representation.Coinvariants.ker M.ρ) :
    ∃ x ∈ Representation.Coinvariants.ker N.ρ, e.hom x = y := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨g, v⟩, rfl⟩ := hy
    obtain ⟨u, rfl⟩ := he v
    exact ⟨N.ρ g u - u, Representation.Coinvariants.sub_mem_ker g u, by
      rw [map_sub, Rep.hom_comm_apply]⟩
  | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨u, hu, rfl⟩ := ha
    obtain ⟨v, hv, rfl⟩ := hb
    exact ⟨u + v, Submodule.add_mem _ hu hv, map_add _ _ _⟩
  | smul c a _ ha =>
    obtain ⟨u, hu, rfl⟩ := ha
    exact ⟨_, Submodule.smul_mem _ c hu, map_smul e.hom c u⟩

private theorem UpperTheory.V.KH.hZero_gen {R G : Type} [CommRing R] [Group G] (N M : Rep.{0} R G)
    (e : N ⟶ M) (he : Function.Surjective e.hom) :
    ∃ a : N →+ groupHomology M 0, Function.Surjective a ∧
      ∀ f, a f = 0 ↔ ∃ x ∈ Representation.Coinvariants.ker N.ρ, e.hom (f - x) = 0 := by
  let ψ : groupHomology M 0 ≃ₗ[R] M.ρ.Coinvariants := (groupHomology.H0Iso M).toLinearEquiv
  let a : N →ₗ[R] groupHomology M 0 :=
    ψ.symm.toLinearMap ∘ₗ Representation.Coinvariants.mk M.ρ ∘ₗ e.hom.toLinearMap
  refine ⟨a.toAddMonoidHom, ψ.symm.surjective.comp
    ((Representation.Coinvariants.mk_surjective M.ρ).comp he), fun f => ?_⟩
  have h1 : a.toAddMonoidHom f = 0 ↔ e.hom f ∈ Representation.Coinvariants.ker M.ρ :=
    ψ.symm.map_eq_zero_iff.trans (Representation.Coinvariants.mk_eq_zero M.ρ)
  rw [h1]
  constructor
  · intro h
    obtain ⟨k, hk, hkf⟩ := hZero_lift N M e he _ h
    exact ⟨k, hk, by rw [map_sub, hkf, sub_self]⟩
  · rintro ⟨x, hx, h⟩
    rw [map_sub, sub_eq_zero] at h
    rw [h]
    exact hZero_push N M e x hx

theorem UpperTheory.V.KH.hZero :
    ∀ (G X : Type) [Group G] [MulAction G X] (M : Rep ℤ G) (e : permRep G X ⟶ M) (S : Set (X →₀ ℤ)),
      Function.Surjective e.hom → (∀ f : X →₀ ℤ, e.hom f = 0 ↔ f ∈ Submodule.span ℤ S) →
      Nonempty (groupHomology M 0 ≃+ ((MulAction.orbitRel.Quotient G X →₀ ℤ) ⧸
        Submodule.span ℤ (Finsupp.mapDomain
          (Quotient.mk (MulAction.orbitRel G X) : X → MulAction.orbitRel.Quotient G X) '' S))) := by
  intro G X _ _ M e S he hS
  set q : X → MulAction.orbitRel.Quotient G X := Quotient.mk (MulAction.orbitRel G X) with hq
  let L : (X →₀ ℤ) →ₗ[ℤ] (MulAction.orbitRel.Quotient G X →₀ ℤ) := Finsupp.lmapDomain ℤ ℤ q
  have hL : LinearMap.ker L = Representation.Coinvariants.ker (perm G X) := kerOrb G X
  have hsp : Submodule.span ℤ (Finsupp.mapDomain q '' S) = (Submodule.span ℤ S).map L :=
    (Submodule.map_span L S).symm
  rw [hsp]
  obtain ⟨a, ha, hak⟩ := hZero_gen (permRep G X) M e he
  let a' : (X →₀ ℤ) →+ groupHomology M 0 := a
  have hak' : ∀ f : X →₀ ℤ, a' f = 0 ↔
      ∃ x ∈ LinearMap.ker L, f - x ∈ Submodule.span ℤ S := by
    intro f
    rw [hL]
    simp only [← hS]
    exact hak f
  let b : (X →₀ ℤ) →+ (_ ⧸ (Submodule.span ℤ S).map L) :=
    (((Submodule.span ℤ S).map L).mkQ ∘ₗ L).toAddMonoidHom
  have hb : Function.Surjective b :=
    (Submodule.mkQ_surjective _).comp (Finsupp.mapDomain_surjective Quotient.mk_surjective)
  have hab : a'.ker = b.ker := by
    ext f
    have h2 : f ∈ b.ker ↔ L f ∈ (Submodule.span ℤ S).map L :=
      Submodule.Quotient.mk_eq_zero _
    rw [AddMonoidHom.mem_ker, hak', h2]
    constructor
    · rintro ⟨k, hk, h⟩
      exact ⟨f - k, h, by rw [map_sub, LinearMap.mem_ker.1 hk, sub_zero]⟩
    · rintro ⟨s, hs, hsf⟩
      exact ⟨f - s, by rw [LinearMap.mem_ker, map_sub, hsf, sub_self],
        by rwa [sub_sub_cancel]⟩
  obtain ⟨φ⟩ := quotients_equiv_of_ker_eq a' b ha hb hab
  exact ⟨φ⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Shapiro
section
open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.shapiro :
    ∀ (G X : Type) [Group G] [MulAction G X] [MulAction.IsPretransitive G X] (x : X) (n : ℕ),
      Nonempty (groupHomology (permRep G X) n ≃+ HZ (MulAction.stabilizer G x) n) := by
  intro G X _ _ _ x n
  classical
  obtain ⟨e⟩ := indPerm G X x
  let i1 := (groupHomology.functor ℤ G n).mapIso e.symm
  let i2 := groupHomology.indIso (MulAction.stabilizer G x) (Rep.trivial ℤ (MulAction.stabilizer G x) ℤ) n
  exact ⟨(i1 ≪≫ i2).toLinearEquiv.toAddEquiv⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.TupExact
section
open CategoryTheory UpperTheory.V.KH

private noncomputable abbrev UpperTheory.V.KH.tupJ {A : Type} (s : Set A) : (s →₀ ℤ) →ₗ[ℤ] (A →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (Subtype.val : s → A)

private theorem UpperTheory.V.KH.tupJ_inj {A : Type} (s : Set A) : Function.Injective (tupJ s) :=
  Finsupp.mapDomain_injective Subtype.val_injective

private theorem UpperTheory.V.KH.tupJ_mem {A : Type} (s : Set A) (c : s →₀ ℤ) :
    tupJ s c ∈ Finsupp.supported ℤ ℤ s := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | single x c =>
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    exact Finsupp.single_mem_supported ℤ _ x.2

private theorem UpperTheory.V.KH.tupJ_surj {A : Type} (s : Set A) (b : A →₀ ℤ)
    (hb : b ∈ Finsupp.supported ℤ ℤ s) : ∃ c, tupJ s c = b := by
  have : Finsupp.supported ℤ ℤ s ≤ LinearMap.range (tupJ s) := by
    rw [Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨Finsupp.single ⟨x, hx⟩ 1, by simp [Finsupp.lmapDomain_apply]⟩
  exact this hb

private theorem UpperTheory.V.KH.tupJ_faceD {I : Type} (S : ∀ n, Set (Fin n → I))
    (hF : UpperTheory.V.ConeExtensionAcyclic.FaceClosed S) (n : ℕ) (c : S (n + 1) →₀ ℤ) :
    tupJ (S n) (faceD (fun (i : Fin (n + 1)) (t : S (n + 1)) =>
      (⟨t.1 ∘ i.succAbove, hF n t.1 t.2 i⟩ : S n)) c) =
      UpperTheory.V.ConeExtensionAcyclic.bd I n (tupJ (S (n + 1)) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single x c =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [faceD_single, map_sum, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      UpperTheory.V.ConeExtensionAcyclic.bd, Finsupp.linearCombination_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, smul_comm c,
      Finsupp.smul_single_one]

private theorem UpperTheory.V.KH.bd_zero_tupJ {I : Type} (s : Set (Fin (0 + 1) → I)) (c : s →₀ ℤ) :
    UpperTheory.V.ConeExtensionAcyclic.bd I 0 (tupJ s c) = Finsupp.single default (aug s c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb, Finsupp.single_add]
  | single x c =>
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      UpperTheory.V.ConeExtensionAcyclic.bd, Finsupp.linearCombination_single, aug_single]
    rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, pow_zero, one_smul,
      Finsupp.smul_single_one]
    congr 1
    exact Subsingleton.elim _ _

theorem UpperTheory.V.KH.tupExact :
    ∀ (I : Type) (S : ∀ n, Set (Fin n → I)) (hF : UpperTheory.V.ConeExtensionAcyclic.FaceClosed S), (S 0).Nonempty →
      UpperTheory.V.ConeExtensionAcyclic.Acyc S → ∀ m : ℕ,
      FaceExactTo (fun p => S (p + 1))
        (fun p i t => ⟨t.1 ∘ i.succAbove, hF (p + 1) t.1 t.2 i⟩) m := by
  intro I S hF h0 hA m
  obtain ⟨t0, ht0⟩ := h0
  have hdef : (default : Fin 0 → I) ∈ S 0 := by
    rwa [Subsingleton.elim (default : Fin 0 → I) t0]
  refine ⟨fun z => ?_, fun c => ⟨fun hc => ?_, ?_⟩, fun p _ c => ⟨fun hc => ?_, ?_⟩⟩
  · obtain ⟨b, hb, hbz⟩ := hA.1 (Finsupp.single default z) (Finsupp.single_mem_supported ℤ _ hdef)
    obtain ⟨c, rfl⟩ := tupJ_surj _ b hb
    exact ⟨c, Finsupp.single_injective _ ((bd_zero_tupJ (S (0 + 1)) c).symm.trans hbz)⟩
  · obtain ⟨b, hb, hbz⟩ := hA.2 0 (tupJ _ c) (tupJ_mem _ c) (by
      rw [bd_zero_tupJ, hc, Finsupp.single_zero])
    obtain ⟨d, rfl⟩ := tupJ_surj _ b hb
    exact ⟨d, tupJ_inj _ ((tupJ_faceD S hF (0 + 1) d).trans hbz)⟩
  · rintro ⟨d, rfl⟩
    apply Finsupp.single_injective (default : Fin 0 → I)
    have h1 := bd_zero_tupJ (S (0 + 1)) (faceD (fun (i : Fin (0 + 1 + 1)) (t : S (0 + 1 + 1)) =>
      (⟨t.1 ∘ i.succAbove, hF (0 + 1) t.1 t.2 i⟩ : S (0 + 1))) d)
    rw [tupJ_faceD S hF (0 + 1) d, UpperTheory.V.ConeExtensionAcyclic.bd_bd] at h1
    exact h1.symm.trans (Finsupp.single_zero _).symm
  · obtain ⟨b, hb, hbz⟩ := hA.2 (p + 1) (tupJ _ c) (tupJ_mem _ c) (by
      rw [← tupJ_faceD S hF (p + 1) c]
      exact (congrArg (tupJ (S (p + 1))) hc).trans (map_zero _))
    obtain ⟨d, rfl⟩ := tupJ_surj _ b hb
    exact ⟨d, tupJ_inj _ ((tupJ_faceD S hF (p + 1 + 1) d).trans hbz)⟩
  · rintro ⟨d, rfl⟩
    apply tupJ_inj (S (p + 1))
    refine (tupJ_faceD S hF (p + 1) _).trans ?_
    refine (congrArg (UpperTheory.V.ConeExtensionAcyclic.bd I (p + 1)) (tupJ_faceD S hF (p + 1 + 1) d)).trans ?_
    rw [UpperTheory.V.ConeExtensionAcyclic.bd_bd, map_zero]
end

