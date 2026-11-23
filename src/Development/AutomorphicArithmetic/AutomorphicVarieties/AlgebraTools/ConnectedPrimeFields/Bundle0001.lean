module

public import Mathlib
public import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.Bridge
section
open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem UpperTheory.V.AlgebraTools.Conn.etaleCohomology_simplicialCochain_representation_step {R : Type} [CommRing R] (a I : Ideal R) :
    IsConnected (PrimeSpectrum.zeroLocus (a : Set R) \ PrimeSpectrum.zeroLocus (I : Set R)) ↔
    IsConnected ((PrimeSpectrum.zeroLocus
      ((I.map (Ideal.Quotient.mk a) : Ideal (R ⧸ a)) : Set (R ⧸ a)))ᶜ :
        Set (PrimeSpectrum (R ⧸ a))) := by
  have hs : Function.Surjective (Ideal.Quotient.mk a) := Ideal.Quotient.mk_surjective
  have hemb := PrimeSpectrum.isClosedEmbedding_comap_of_surjective (R ⧸ a) (Ideal.Quotient.mk a) hs
  have hr := range_comap_of_surjective (R ⧸ a) (Ideal.Quotient.mk a) hs
  rw [Ideal.mk_ker] at hr
  have hpre : (PrimeSpectrum.zeroLocus
      ((I.map (Ideal.Quotient.mk a) : Ideal (R ⧸ a)) : Set (R ⧸ a))) =
      PrimeSpectrum.comap (Ideal.Quotient.mk a) ⁻¹' PrimeSpectrum.zeroLocus (I : Set R) := by
    ext p
    simp only [PrimeSpectrum.mem_zeroLocus, Set.mem_preimage, SetLike.coe_subset_coe,
      PrimeSpectrum.comap_asIdeal]
    exact Ideal.map_le_iff_le_comap
  have him : PrimeSpectrum.comap (Ideal.Quotient.mk a) '' ((PrimeSpectrum.zeroLocus
      ((I.map (Ideal.Quotient.mk a) : Ideal (R ⧸ a)) : Set (R ⧸ a)))ᶜ) =
      PrimeSpectrum.zeroLocus (a : Set R) \ PrimeSpectrum.zeroLocus (I : Set R) := by
    rw [hpre, ← Set.preimage_compl, Set.image_preimage_eq_inter_range, hr, Set.diff_eq,
      Set.inter_comm]
  rw [← him]
  unfold IsConnected
  rw [Set.image_nonempty, hemb.isInducing.isPreconnected_image]

theorem UpperTheory.V.AlgebraTools.Conn.bridge :
    ∀ {R : Type} [CommRing R] (a : Ideal R) (k : WithBot ℕ∞), ConnOn a k ↔ ReciprocityTheory.CA.ConnInDim (R ⧸ a) k := by
  intro R _ a k
  constructor
  · intro h J hJ
    have hs : Function.Surjective (Ideal.Quotient.mk a) := Ideal.Quotient.mk_surjective
    have hle : a ≤ J.comap (Ideal.Quotient.mk a) := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact J.zero_mem
    have hJ' : (J.comap (Ideal.Quotient.mk a)).map (Ideal.Quotient.mk a) = J :=
      Ideal.map_comap_of_surjective _ hs J
    rw [← hJ'] at hJ ⊢
    rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle)] at hJ
    exact (etaleCohomology_simplicialCochain_representation_step a _).mp (h _ hle hJ)
  · intro h I hle hI
    rw [← ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle)] at hI
    exact (etaleCohomology_simplicialCochain_representation_step a I).mpr (h _ hI)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.CmFree
section
open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.cmFree :
    ∀ {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B] [Module.Finite A B]
      [Module.Free A B], ReciprocityTheory.CA.IsCM A → ReciprocityTheory.CA.IsCM B := by
  intro A B _ _ _ _ _ _ _ h
  obtain ⟨hN, n, hdim, rs, hlen, hmem, hreg⟩ := h
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have hm : (maximalIdeal B).comap (algebraMap A B) = maximalIdeal A :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal B))
  refine ⟨IsNoetherianRing.of_finite A B, n, ?_, rs.map (algebraMap A B), by simpa using hlen, ?_,
    hreg.of_faithfullyFlat⟩
  · rw [← hdim]
    exact ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj
  · intro r hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    have := hmem a ha
    rw [← hm] at this
    exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.DimLeOfForall
section
open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem dim_le_of_forall {R : Type} [CommRing R] (I : Ideal R) (d : WithBot ℕ∞)
    (h : ∀ P : Ideal R, P.IsPrime → I ≤ P → ∃ J : Ideal R, J ≤ P ∧ ringKrullDim (R ⧸ J) ≤ d) :
    ringKrullDim (R ⧸ I) ≤ d := by
  rw [ringKrullDim_quotient]
  unfold Order.krullDim
  apply iSup_le
  intro l
  obtain ⟨J, hJP, hJd⟩ := h l.head.1.asIdeal l.head.1.isPrime l.head.2
  rw [ringKrullDim_quotient] at hJd
  let l' : LTSeries (PrimeSpectrum.zeroLocus (J : Set R)) :=
    { length := l.length
      toFun := fun i => ⟨(l i).1, fun r hr => (l.monotone (Fin.zero_le i)) (hJP hr)⟩
      step := fun i => l.step i }
  exact le_trans (le_iSup (fun p : LTSeries (PrimeSpectrum.zeroLocus (J : Set R)) => (p.length : WithBot ℕ∞)) l') hJd

theorem UpperTheory.V.AlgebraTools.Conn.chain :
    ∀ {R : Type} [CommRing R] [IsNoetherianRing R] (a : Ideal R) (k : WithBot ℕ∞), ConnOn a k →
      ∀ p ∈ a.minimalPrimes, ∀ q ∈ a.minimalPrimes,
        Relation.ReflTransGen (fun x y : Ideal R => x ∈ a.minimalPrimes ∧ y ∈ a.minimalPrimes ∧ ReciprocityTheory.CA.Linked R k x y) p q := by
  intro R _ _ a k hconn p hp q hq
  classical
  let rel : Ideal R → Ideal R → Prop := fun x y =>
    x ∈ a.minimalPrimes ∧ y ∈ a.minimalPrimes ∧ ReciprocityTheory.CA.Linked R k x y
  change Relation.ReflTransGen rel p q
  by_contra hpq
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing R a
  obtain ⟨K, hK⟩ : ∃ K : Finset (Ideal R),
      ∀ x, x ∈ K ↔ x ∈ a.minimalPrimes ∧ Relation.ReflTransGen rel p x :=
    ⟨hfin.toFinset.filter (fun x => Relation.ReflTransGen rel p x), fun x => by
      rw [Finset.mem_filter, Set.Finite.mem_toFinset]⟩
  obtain ⟨L, hL⟩ : ∃ L : Finset (Ideal R),
      ∀ x, x ∈ L ↔ x ∈ a.minimalPrimes ∧ ¬ Relation.ReflTransGen rel p x :=
    ⟨hfin.toFinset.filter (fun x => ¬ Relation.ReflTransGen rel p x), fun x => by
      rw [Finset.mem_filter, Set.Finite.mem_toFinset]⟩
  have hpK : p ∈ K := (hK p).mpr ⟨hp, Relation.ReflTransGen.refl⟩
  have hqL : q ∈ L := (hL q).mpr ⟨hq, hpq⟩
  obtain ⟨g, hg⟩ : ∃ g : Ideal R × Ideal R → WithBot ℕ∞,
      ∀ xy, g xy = ringKrullDim (R ⧸ (xy.1 ⊔ xy.2)) := ⟨_, fun _ => rfl⟩
  have hnl : ∀ x ∈ K, ∀ y ∈ L, g (x, y) < k := by
    intro x hx y hy
    obtain ⟨hxM, hpx⟩ := (hK x).mp hx
    obtain ⟨hyM, hpy⟩ := (hL y).mp hy
    rw [hg]
    by_contra hle
    exact hpy (hpx.tail ⟨hxM, hyM, not_lt.mp hle⟩)
  have hk : ⊥ < k := lt_of_le_of_lt bot_le (hnl p hpK q hqL)
  obtain ⟨J1, hJ1⟩ : ∃ J1 : Ideal R, J1 = K.inf id := ⟨_, rfl⟩
  obtain ⟨J2, hJ2⟩ : ∃ J2 : Ideal R, J2 = L.inf id := ⟨_, rfl⟩
  have haJ1 : a ≤ J1 := hJ1 ▸ Finset.le_inf (fun x hx => ((hK x).mp hx).1.1.2)
  have haI : a ≤ J1 ⊔ J2 := le_sup_of_le_left haJ1
  have hdim : ringKrullDim (R ⧸ (J1 ⊔ J2)) < k := by
    have hd : ringKrullDim (R ⧸ (J1 ⊔ J2)) ≤ (K ×ˢ L).sup g := by
      apply dim_le_of_forall
      intro P hP hIP
      obtain ⟨x, hx, hxP⟩ :=
        (Ideal.IsPrime.inf_le' (s := K) (f := id) hP).mp (hJ1 ▸ le_sup_left.trans hIP)
      obtain ⟨y, hy, hyP⟩ :=
        (Ideal.IsPrime.inf_le' (s := L) (f := id) hP).mp (hJ2 ▸ le_sup_right.trans hIP)
      refine ⟨x ⊔ y, sup_le hxP hyP, ?_⟩
      have hle : g (x, y) ≤ (K ×ˢ L).sup g := Finset.le_sup (Finset.mem_product.mpr ⟨hx, hy⟩)
      rw [hg] at hle
      exact hle
    refine lt_of_le_of_lt hd ((Finset.sup_lt_iff hk).mpr ?_)
    intro xy hxy
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hxy
    exact hnl _ h1 _ h2
  have mz : ∀ (J : Ideal R) (z : PrimeSpectrum R),
      z ∈ PrimeSpectrum.zeroLocus (J : Set R) ↔ J ≤ z.asIdeal := fun J z => by
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  have hJ2p : ¬ J2 ≤ p := by
    intro h
    rw [hJ2] at h
    obtain ⟨y, hy, hyp⟩ := (Ideal.IsPrime.inf_le' (s := L) (f := id) hp.1.1).mp h
    have hyM := ((hL y).mp hy).1
    have hyeq : y = p := le_antisymm hyp (hp.2 hyM.1 hyp)
    exact ((hL y).mp hy).2 (hyeq ▸ Relation.ReflTransGen.refl)
  have hJ1q : ¬ J1 ≤ q := by
    intro h
    rw [hJ1] at h
    obtain ⟨x, hx, hxq⟩ := (Ideal.IsPrime.inf_le' (s := K) (f := id) hq.1.1).mp h
    have hxM := ((hK x).mp hx).1
    have hxeq : x = q := le_antisymm hxq (hq.2 hxM.1 hxq)
    exact hpq (hxeq ▸ ((hK x).mp hx).2)
  obtain ⟨z, hzS, hzu, hzv⟩ := (hconn (J1 ⊔ J2) haI hdim).isPreconnected
    (PrimeSpectrum.zeroLocus (J2 : Set R))ᶜ (PrimeSpectrum.zeroLocus (J1 : Set R))ᶜ
    (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
    (by
      rintro z ⟨_, hzI⟩
      by_contra hz
      simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hz
      exact hzI ((mz _ z).mpr (sup_le ((mz J1 z).mp hz.2) ((mz J2 z).mp hz.1))))
    ⟨⟨p, hp.1.1⟩, ⟨(mz a _).mpr hp.1.2, fun h => hJ2p (le_sup_right.trans ((mz _ _).mp h))⟩,
      fun h => hJ2p ((mz J2 _).mp h)⟩
    ⟨⟨q, hq.1.1⟩, ⟨(mz a _).mpr hq.1.2, fun h => hJ1q (le_sup_left.trans ((mz _ _).mp h))⟩,
      fun h => hJ1q ((mz J1 _).mp h)⟩
  obtain ⟨m, hm, hmz⟩ := Ideal.exists_minimalPrimes_le ((mz a z).mp hzS.1)
  by_cases hpm : Relation.ReflTransGen rel p m
  · refine hzv ((mz J1 z).mpr ?_)
    rw [hJ1]
    exact (Finset.inf_le (f := id) ((hK m).mpr ⟨hm, hpm⟩)).trans hmz
  · refine hzu ((mz J2 z).mpr ?_)
    rw [hJ2]
    exact (Finset.inf_le (f := id) ((hL m).mpr ⟨hm, hpm⟩)).trans hmz
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.DvrBase
section
open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.dvrBase :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O], IsBase O := by
  intro O _ _ _ _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  haveI : Nontrivial (QuotSMulTop ϖ O) := by
    open Pointwise in
    refine Submodule.Quotient.nontrivial_iff.mpr ?_
    intro h
    have h1 : (1 : O) ∈ ϖ • (⊤ : Submodule O O) := by rw [h]; exact Submodule.mem_top
    obtain ⟨x, -, hx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one x (by simpa [smul_eq_mul] using hx))
  refine ⟨inferInstance, inferInstance, ⟨inferInstance, 1, ?_, [ϖ], rfl, ?_, ?_⟩, inferInstance⟩
  · rw [IsDiscreteValuationRing.ringKrullDim_eq_one]; rfl
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
  · rw [RingTheory.Sequence.isRegular_cons_iff]
    refine ⟨fun a b hab => mul_left_cancel₀ hϖ.ne_zero (by simpa [smul_eq_mul] using hab), ?_⟩
    exact RingTheory.Sequence.IsRegular.nil _ _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.FormsAR
section
open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem formsAR_embed {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.IsTorsionFree R M] :
    ∃ (ι : Type) (_ : Fintype ι) (f : M →ₗ[R] (ι → R)), Function.Injective f := by
  classical
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  obtain ⟨I, indepI, hI⟩ := exists_maximal_linearIndepOn R s
  have indepI' : LinearIndependent R (fun x : I => s x) := indepI
  let N := Submodule.span R (Set.range fun x : I => s x)
  let b : Module.Basis I R N := Module.Basis.span indepI'
  have exists_a : ∀ i, ∃ a : R, a ≠ 0 ∧ a • s i ∈ N := by
    intro i
    by_cases hi : i ∈ I
    · refine ⟨1, one_ne_zero, ?_⟩
      rw [one_smul]
      exact Submodule.subset_span (Set.mem_range_self (⟨i, hi⟩ : I))
    · obtain ⟨a, ha, ha'⟩ := hI i hi
      refine ⟨a, ha, ?_⟩
      rwa [Set.image_eq_range s I] at ha'
  choose a ha ha' using exists_a
  have hA : (∏ i, a i) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    exact fun i _ => ha i
  let φ : M →ₗ[R] M := LinearMap.lsmul R M (∏ i, a i)
  have hφ : Function.Injective φ := LinearMap.ker_eq_bot.mp (LinearMap.ker_lsmul hA)
  have hle : LinearMap.range φ ≤ N := by
    suffices ∀ i, φ (s i) ∈ N by
      rw [LinearMap.range_eq_map, ← hs, Submodule.map_span_le]
      rintro _ ⟨i, rfl⟩
      apply this
    intro i
    have h1 := N.smul_mem (∏ j ∈ {i}ᶜ, a j) (ha' i)
    rw [← mul_smul, ← Fintype.prod_eq_prod_compl_mul i] at h1
    exact h1
  refine ⟨I, inferInstance,
    b.equivFun.toLinearMap ∘ₗ φ.codRestrict N (fun x => hle ⟨x, rfl⟩), ?_⟩
  intro x y h
  have h2 := b.equivFun.injective h
  exact hφ (congrArg Subtype.val h2)

private theorem formsAR_pi {R ι : Type} [CommRing R] [Fintype ι] (J : Ideal R) (x : ι → R)
    (hx : ∀ i, x i ∈ J) : x ∈ J • (⊤ : Submodule R (ι → R)) := by
  classical
  have : x = ∑ i, x i • (Pi.single i (1 : R) : ι → R) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) trivial

theorem UpperTheory.V.AlgebraTools.Conn.formsAR :
    ∀ {A M : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
      [Module.IsTorsionFree A M] (I : Ideal A), ∃ k : ℕ, ∀ (n : ℕ) (m : M),
        (∀ l : Module.Dual A M, l m ∈ I ^ (n + k)) → m ∈ I ^ n • (⊤ : Submodule A M) := by
  intro A M _ _ _ _ _ _ _ I
  obtain ⟨ι, _, f, hf⟩ := formsAR_embed (R := A) (M := M)
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range f)
  refine ⟨k, fun n m hm => ?_⟩
  have h1 : f m ∈ I ^ (n + k) • (⊤ : Submodule A (ι → A)) ⊓ LinearMap.range f :=
    ⟨formsAR_pi _ _ fun i => hm ((LinearMap.proj i) ∘ₗ f), ⟨m, rfl⟩⟩
  rw [hk (n + k) (Nat.le_add_left k n), Nat.add_sub_cancel] at h1
  have h2 : f m ∈ I ^ n • LinearMap.range f := Submodule.smul_mono le_rfl inf_le_right h1
  rw [LinearMap.range_eq_map, ← Submodule.map_smul''] at h2
  obtain ⟨y, hy, hym⟩ := h2
  rw [← hf hym]
  exact hy
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.Imports
section
open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.level :
    ∀ {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (J : Ideal A) (u v : A) (b c : Ideal R), Reg2 J u v → b * c ≤ J.map (algebraMap A R) →
      algebraMap A R u ∈ b ⊔ c → algebraMap A R v ∈ b ⊔ c → ∀ l : Module.Dual A R,
        ∃ a : A, ∀ (y : A) (β γ : R), β ∈ b → γ ∈ c → algebraMap A R y = β + γ → l β - y * a ∈ J := by
  intro A R _ _ _ J u v b c hreg hbc hu hv l
  have hl : ∀ x ∈ J.map (algebraMap A R), ∀ r : R, l (r * x) ∈ J := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      intro r
      rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
      exact J.mul_mem_right _ hj
    | zero => intro r; simp
    | add x y _ _ hx hy => intro r; rw [mul_add, map_add (f := _)]; exact J.add_mem (hx r) (hy r)
    | smul s x _ hx => intro r; rw [smul_eq_mul, ← mul_assoc]; exact hx _
  have key : ∀ (y y' : A) (β γ β' γ' : R), β ∈ b → γ ∈ c → β' ∈ b → γ' ∈ c →
      algebraMap A R y = β + γ → algebraMap A R y' = β' + γ' → y' * l β - y * l β' ∈ J := by
    intro y y' β γ β' γ' hβ hγ hβ' hγ' hy hy'
    have h1 : algebraMap A R y' * β - algebraMap A R y * β' ∈ J.map (algebraMap A R) := by
      apply hbc
      have e : algebraMap A R y' * β - algebraMap A R y * β' = β * γ' - β' * γ := by
        rw [hy, hy']; ring
      rw [e]
      exact Ideal.sub_mem _ (Ideal.mul_mem_mul hβ hγ') (Ideal.mul_mem_mul hβ' hγ)
    have h2 := hl _ h1 1
    rwa [one_mul, map_sub, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul,
      smul_eq_mul, smul_eq_mul] at h2
  obtain ⟨βu, hβu, γu, hγu, hu'⟩ := Submodule.mem_sup.mp hu
  obtain ⟨βv, hβv, γv, hγv, hv'⟩ := Submodule.mem_sup.mp hv
  have k := key u v βu γu βv γv hβu hγu hβv hγv hu'.symm hv'.symm
  have hm : v * l βu ∈ J ⊔ Ideal.span {u} := by
    have e : v * l βu = (v * l βu - u * l βv) + u * l βv := by ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mem_sup_left k)
      (Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨l βv, mul_comm _ _⟩))
  obtain ⟨j, hj, s, hs, hjs⟩ := Submodule.mem_sup.mp (hreg.2 _ hm)
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hs
  refine ⟨a, fun y β γ hβ hγ hy => hreg.1 _ ?_⟩
  have k2 := key y u β γ βu γu hβ hγ hβu hγu hy hu'.symm
  have e : u * (l β - y * a) = (u * l β - y * l βu) + y * j := by
    rw [← hjs]; ring
  rw [e]
  exact J.add_mem k2 (J.mul_mem_left _ hj)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.LatticeDuality
section
open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.bidual :
    ∀ {A M : Type} [CommRing A] [IsDomain A] [AddCommGroup M] [Module A M] [Module.Finite A M]
      (a : Module.Dual A (Module.Dual A M)), ∃ (d : A) (r : M), d ≠ 0 ∧ ∀ l : Module.Dual A M, l r = d * a l := by
  intro A M _ _ _ _ _ a
  classical
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule A M).FG)
  let K := FractionRing A
  let ψ : Module.Dual A M → Option S → K := fun l o =>
    o.elim (algebraMap A K (a l)) (fun i => algebraMap A K (l (i : M)))
  have hψs : ∀ (p : A) l o, ψ (p • l) o = algebraMap A K p * ψ l o := by
    intro p l o
    cases o <;> simp [ψ]
  have hψa : ∀ l m o, ψ (l + m) o = ψ l o + ψ m o := by
    intro l m o
    cases o <;> simp [ψ]
  have hψ0 : ∀ o, ψ 0 o = 0 := by
    intro o
    cases o <;> simp [ψ]
  let v : Option S → K := fun j => if none = j then 1 else 0
  have key : ∀ w ∈ Submodule.span K (Set.range ψ),
      ∃ s : A, s ≠ 0 ∧ ∃ l, ∀ o, algebraMap A K s * w o = ψ l o := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      exact ⟨1, one_ne_zero, l, fun o => by simp⟩
    | zero =>
      exact ⟨1, one_ne_zero, 0, fun o => by simp [hψ0]⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, l, hl⟩ := hx
      obtain ⟨t, ht, m, hm⟩ := hy
      refine ⟨s * t, mul_ne_zero hs ht, t • l + s • m, fun o => ?_⟩
      rw [hψa, hψs, hψs, ← hl o, ← hm o, Pi.add_apply, map_mul]
      ring
    | smul c x _ hx =>
      obtain ⟨s, hs, l, hl⟩ := hx
      obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := A) c
      have hq0 : algebraMap A K q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
      have hc : algebraMap A K q * (algebraMap A K p / algebraMap A K q) = algebraMap A K p :=
        mul_div_cancel₀ _ hq0
      refine ⟨q * s, mul_ne_zero (nonZeroDivisors.ne_zero hq) hs, p • l, fun o => ?_⟩
      rw [hψs, ← hl o, Pi.smul_apply, smul_eq_mul, map_mul]
      linear_combination (algebraMap A K s * x o) * hc
  have hv : v ∉ Submodule.span K (Set.range ψ) := by
    intro hmem
    obtain ⟨s, hs, l, hl⟩ := key v hmem
    have hl0 : l = 0 := by
      apply LinearMap.ext_on hS
      intro i hi
      have h := hl (some ⟨i, hi⟩)
      simp [v, ψ] at h
      rw [LinearMap.zero_apply]
      exact IsFractionRing.injective A K (by rw [map_zero]; exact h.symm)
    subst hl0
    have h := hl none
    simp [v, ψ] at h
    exact hs h
  obtain ⟨f, hf, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  have hf0 : ∀ l, f (ψ l) = 0 := by
    intro l
    have h : f (ψ l) ∈ (Submodule.span K (Set.range ψ)).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨l, rfl⟩)
    rw [hfW] at h
    exact (Submodule.mem_bot K).mp h
  let c : Option S → K := fun o => f (fun j => if o = j then 1 else 0)
  obtain ⟨Dn, hDc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A) c
  choose b hb using hDc
  have hD0 : algebraMap A K (Dn : A) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors Dn.2
  have hmain : ∀ l : Module.Dual A M, b none * a l + ∑ i : S, b (some i) * l i = 0 := by
    intro l
    have e : ∑ o, ψ l o * c o = 0 := by
      have h := hf0 l
      rw [LinearMap.pi_apply_eq_sum_univ f (ψ l)] at h
      simpa [c, smul_eq_mul] using h
    apply IsFractionRing.injective A K
    rw [map_zero]
    calc algebraMap A K (b none * a l + ∑ i : S, b (some i) * l i)
        = algebraMap A K (Dn : A) * ∑ o, ψ l o * c o := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [Fintype.sum_option, mul_add, Finset.mul_sum, map_add (f := _), map_mul, map_sum]
          congr 1
          · rw [hb, Algebra.smul_def]
            simp only [ψ, Option.elim_none]
            ring
          · refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [map_mul, hb, Algebra.smul_def]
            simp only [ψ, Option.elim_some]
            ring
      _ = 0 := by rw [e, mul_zero]
  refine ⟨b none, -(∑ i : S, b (some i) • (i : M)), ?_, ?_⟩
  · intro h0
    have h := hb none
    rw [h0, map_zero, Algebra.smul_def] at h
    exact hf ((mul_eq_zero.mp h.symm).resolve_left hD0)
  · intro l
    have h := hmain l
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_neg, map_sum]
    simp only [map_smul, smul_eq_mul]
    linear_combination -h
end

