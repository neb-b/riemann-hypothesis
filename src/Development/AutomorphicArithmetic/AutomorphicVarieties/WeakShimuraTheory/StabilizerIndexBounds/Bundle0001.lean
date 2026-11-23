module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.SelfTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.CardDvdOfPartitionEqualSize
section
open IsLocalRing Polynomial Matrix UpperTheory.V

theorem UpperTheory.V.Ws.card_dvd_of_partition_equal_size :
    ∀ (ι Q : Type) [Finite ι] (T : Q → Set ι) (d : ℕ), (∀ q, (T q).ncard = d) → (∀ i, ∃! q, i ∈ T q) →
      Nat.card Q ∣ Nat.card ι := by
  intro ι Q _ T d hT hu
  classical
  choose f hf hf' using hu
  have hfib : ∀ q, T q = {i | f i = q} := by
    intro q
    ext i
    constructor
    · intro h
      exact (hf' i q h).symm
    · intro h
      rw [Set.mem_setOf_eq] at h
      rw [← h]
      exact hf i
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : IsEmpty ι := ⟨fun i => by
      have h := hT (f i)
      rw [Set.ncard_eq_zero (Set.toFinite _)] at h
      have hi : i ∈ T (f i) := hf i
      rw [h] at hi
      simp at hi⟩
    rw [Nat.card_of_isEmpty (α := ι)]
    exact dvd_zero _
  · have hne : ∀ q, (T q).Nonempty := fun q =>
      Set.nonempty_of_ncard_ne_zero (by rw [hT q]; omega)
    choose g hg using hne
    have ginj : Function.Injective g := by
      intro q q' h
      calc q = f (g q) := hf' _ _ (hg q)
        _ = f (g q') := by rw [h]
        _ = q' := (hf' _ _ (hg q')).symm
    haveI : Finite Q := Finite.of_injective g ginj
    letI : Fintype Q := Fintype.ofFinite Q
    have hc : ∀ q, Nat.card {x // f x = q} = d := fun q => by
      rw [← hT q, hfib q, ← Nat.card_coe_set_eq]
      rfl
    have key : Nat.card ι = Nat.card Q * d := by
      rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
      simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
    rw [key]
    exact dvd_mul_right _ _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.CharpolyFlag
section
open IsLocalRing Polynomial Matrix UpperTheory.V

private theorem chi_map_ofRep {n : ℕ} {A K G : Type} [CommRing A] [CommRing K] [Group G] (f : A →+* K)
    (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    ((W.GDet.ofRep ρ).map f).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly.map f := by
  letI : Algebra A K[X] := ((algebraMap K K[X]).comp f).toAlgebra
  rw [← Matrix.charpoly_map]
  change (W.GDet.repAlg ρ K[X] _).det = (Matrix.charmatrix _).det
  congr 1
  ext i j : 1
  have h : ∀ a, algebraMap A K[X] a = C (f a) := fun _ => rfl
  by_cases hij : i = j
  · subst hij
    simp [W.GDet.repAlg, h]
  · simp [W.GDet.repAlg, h, hij]

private theorem charpoly_flag {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k)
    (κ : Fin n → H →* kˣ) (h : W.HasFlag r κ) (s : H) :
    (W.mat r s).charpoly = ∏ i, ((X : Polynomial k) - C ((κ i s : kˣ) : k)) := by
  obtain ⟨g, hg⟩ := h
  have h1 := Matrix.charpoly_units_conj g (W.mat r s)
  have h2 : ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular id :=
    fun i j hij => (hg s).1 i j hij
  have h3 := Matrix.charpoly_of_upperTriangular _ h2
  rw [← h1]
  simp only [Units.val_mul, Matrix.coe_units_inv] at h3
  refine h3.trans ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  have h4 := (hg s).2 i
  simp only [Units.val_mul, Matrix.coe_units_inv] at h4
  rw [h4]

theorem UpperTheory.V.Ws.h4Cp :
    ∀ (l : ℕ) [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ)
      (r : W.Resid F O n) (x : W.Point r),
      (∀ g, (W.mat x.ρ g).charpoly.map (PowerSeries.constantCoeff : x.A →+* x.K) =
        ∏ i, ((X : Polynomial x.K) - C (algebraMap (ResidueField O) x.K ((r.chib i g : (ResidueField O)ˣ) : ResidueField O)))) ∧
      ∀ v g, (W.mat x.ρ (F.φ v g)).charpoly = ∏ i, ((X : Polynomial x.A) - C ((x.ψ v i g : x.Aˣ) : x.A)) := by
  intro l _ F O _ _ _ n r x
  refine ⟨fun g => ?_, fun v g => ?_⟩
  · have h := congrArg (fun D => W.GDet.chi D (MonoidAlgebra.single g 1)) x.red
    simp only [W.Resid.Dbar, chi_map_ofRep] at h
    rw [h]
    change (Matrix.diagonal _).charpoly.map _ = _
    rw [Matrix.charpoly_diagonal, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  · apply Polynomial.map_injective (algebraMap x.A x.Fr) (IsFractionRing.injective x.A x.Fr)
    rw [← Matrix.charpoly_map, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    exact charpoly_flag _ _ (x.flag v) g
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.ExistsMemOpenInterSubgroupOfCosetwiseFiniteIndex
section
open IsLocalRing Polynomial Matrix UpperTheory.V

theorem UpperTheory.V.Ws.exists_mem_open_inter_subgroup_of_cosetwise_finiteIndex :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
      (Z : Subgroup G) (P : G → Prop), (∀ V : Subgroup Z, V.FiniteIndex → ∀ σ : Z, ∃ g ∈ V, P (σ * g : Z)) →
      ∀ U : Set G, IsOpen U → (U ∩ (Z : Set G)).Nonempty → ∃ σ ∈ U ∩ (Z : Set G), P σ := by
  intro G _ _ _ _ _ Z P h U hU hne
  obtain ⟨σ, hσU, hσZ⟩ := hne
  have hW : IsOpen ((fun x : G => σ * x) ⁻¹' U) := hU.preimage (continuous_const.mul continuous_id)
  have h1 : (1 : G) ∈ ((fun x : G => σ * x) ⁻¹' U) := by simpa using hσU
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW h1
  have hfi : (N.toSubgroup).FiniteIndex := by
    have := Subgroup.quotient_finite_of_isOpen N.toSubgroup N.isOpen
    exact Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨g, hg, hP⟩ := h (N.toSubgroup.subgroupOf Z) inferInstance ⟨σ, hσZ⟩
  refine ⟨_, ⟨?_, ((⟨σ, hσZ⟩ : Z) * g).2⟩, hP⟩
  exact hN (show (g : G) ∈ N.toSubgroup from hg)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.ExistsSignTwistCharpolyOfNotIrreducibleRestricti
section
open IsLocalRing Polynomial Matrix UpperTheory.V

private theorem quadratic_twist_charpoly_eq {K G : Type} [Field K] [Group G] (h2 : (2 : K) ≠ 0)
    (r : G →* Matrix (Fin 4) (Fin 4) K) (S : Subgroup G) (φ : G →* Kˣ)
    (e : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) (h1 : φ ≠ 1) (hS : S ≤ φ.ker) (hsq : ∀ g, φ g * φ g = 1)
    (he : ∀ g v, r g *ᵥ e v = (φ g : K) • e (r g *ᵥ v)) :
    ∃ η : G →* ℤˣ, η ≠ 1 ∧ S ≤ η.ker ∧
      ∀ g, (r g).charpoly = ((((η g : ℤˣ) : ℤ) : K) • r g).charpoly := by
  classical
  let ι : ℤˣ →* Kˣ := Units.map (Int.castRingHom K).toMonoidHom
  have hι : ∀ u : ℤˣ, ((ι u : Kˣ) : K) = ((u : ℤ) : K) := fun u => rfl
  have hneg : (-1 : K) ≠ 1 := by
    intro h
    apply h2
    linear_combination -h
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro u hu
    rcases Int.units_eq_one_or u with h | h
    · exact h
    · exfalso
      have := congrArg Units.val hu
      rw [hι, h] at this
      apply hneg
      simpa using this
  have hex : ∀ g, ∃ u : ℤˣ, ι u = φ g := by
    intro g
    have h : (φ g : K) * (φ g : K) = 1 := by
      rw [← Units.val_mul, hsq, Units.val_one]
    rcases mul_self_eq_one_iff.mp h with h | h
    · exact ⟨1, Units.ext (by rw [hι, h]; simp)⟩
    · exact ⟨-1, Units.ext (by rw [hι, h]; simp)⟩
  choose η hη using hex
  let η' : G →* ℤˣ := MonoidHom.mk' η (fun a b => hinj (by rw [map_mul, hη, hη, hη, map_mul]))
  have hη' : ∀ g, η' g = η g := fun g => rfl
  refine ⟨η', ?_, ?_, ?_⟩
  · intro h
    apply h1
    ext1 g
    rw [← hη, ← hη', h]
    simp
  · intro g hg
    rw [MonoidHom.mem_ker]
    apply hinj
    rw [hη', hη, map_one]
    exact hS hg
  · intro g
    rw [hη', ← hι, hη]
    have hc : e.conj (Matrix.toLin' ((φ g : K) • r g)) = Matrix.toLin' (r g) := by
      apply LinearMap.ext
      intro v
      obtain ⟨w, rfl⟩ := e.surjective v
      rw [LinearEquiv.conj_apply_apply, e.symm_apply_apply, Matrix.toLin'_apply,
        Matrix.toLin'_apply, he, Matrix.smul_mulVec, map_smul]
    rw [← Matrix.charpoly_toLin', ← hc, LinearEquiv.charpoly_conj, Matrix.charpoly_toLin']

theorem UpperTheory.V.Ws.exists_sign_twist_charpoly_of_not_irreducible_restriction :
    ∀ (K G : Type) [Field K] [IsAlgClosed K] [Group G], (2 : K) ≠ 0 → ∀ r : G →* Matrix (Fin 4) (Fin 4) K, U3.MatIrr ⊤ r →
      ∀ S : Subgroup G, commutator G ≤ S → S.index ∣ 4 → ¬ U3.MatIrr S r →
      ∃ η : G →* ℤˣ, η ≠ 1 ∧ S ≤ η.ker ∧ ∀ g, (r g).charpoly = ((((η g : ℤˣ) : ℤ) : K) • r g).charpoly := by
  intro K G _ _ _ h2 r hirr S hcomm hidx hred
  have hab : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ S := fun a b =>
    hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
  haveI hN : S.Normal := ⟨fun n hn g => by
    have := S.mul_mem (hab g n) hn
    simpa using this⟩
  have h4 : ((4 : ℕ) : K) ≠ 0 := by
    have : ((4 : ℕ) : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  obtain ⟨m, hm⟩ := hidx
  have hiK : (S.index : K) ≠ 0 := by
    intro h
    apply h4
    rw [hm, Nat.cast_mul, h, zero_mul]
  have hfi : S.FiniteIndex := ⟨fun h => hiK (by rw [h, Nat.cast_zero])⟩
  let ρ : Representation K G (Fin 4 → K) :=
    (Matrix.toLinAlgEquiv' (R := K) (n := Fin 4)).toMonoidHom.comp r
  have hρ : ∀ g v, ρ g v = r g *ᵥ v := fun g v => Matrix.toLinAlgEquiv'_apply _ _
  unfold U3.MatIrr at hirr hred
  push Not at hred
  obtain ⟨φ, e, h1, hS, he⟩ := UpperTheory.V.Pr.T.selfTwist ρ S hfi hiK hab
    (fun W hW => hirr W (fun g _ v hv => hρ g v ▸ hW g v hv))
    (by
      obtain ⟨W, hW, hb, ht⟩ := hred
      exact ⟨W, fun g hg v hv => (hρ g v).symm ▸ hW g hg v hv, hb, ht⟩)
  simp only [hρ] at he
  by_cases hsq : ∀ g, φ g * φ g = 1
  · exact quadratic_twist_charpoly_eq h2 r S φ e h1 hS hsq he
  · refine quadratic_twist_charpoly_eq h2 r S (φ * φ) (e.trans e) ?_ ?_ ?_ ?_
    · intro h
      apply hsq
      intro g
      exact DFunLike.congr_fun h g
    · intro g hg
      have : φ g = 1 := hS hg
      rw [MonoidHom.mem_ker, MonoidHom.mul_apply, this, one_mul]
    · intro g
      have h : φ (g ^ S.index) = 1 := hS (S.pow_index_mem g)
      have h' : φ g ^ 4 = 1 := by rw [hm, pow_mul, ← map_pow, h, one_pow]
      rw [MonoidHom.mul_apply, ← h']
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    · intro g v
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, he, he, map_smul, smul_smul,
        MonoidHom.mul_apply, Units.val_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.InvariantSubmoduleEqSpanEigenbasisOfSeparable
section
open IsLocalRing Polynomial Matrix UpperTheory.V

private theorem exists_eigenbasis_of_separable_charpoly {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hA : A.charpoly.Separable) :
    ∃ (b : Module.Basis (Fin n) K (Fin n → K)) (l : Fin n → K), Function.Injective l ∧
      ∀ i, A *ᵥ b i = l i • b i := by
  classical
  have hnd : A.charpoly.roots.Nodup := Polynomial.nodup_roots hA
  have hcard : A.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, ← (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  let e : A.charpoly.roots.toFinset ≃ Fin n := Finset.equivFinOfCardEq hcard
  let l : Fin n → K := fun i => (e.symm i : K)
  have hl : Function.Injective l := fun i j h => e.symm.injective (Subtype.ext h)
  have hev : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' A) (l i) := by
    intro i
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
    have := (e.symm i).2
    rw [Multiset.mem_toFinset] at this
    exact Polynomial.isRoot_of_mem_roots this
  choose v hv using fun i => (hev i).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' A) l hl v hv
  have hsp : Submodule.span K (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [Module.finrank_fintype_fun_eq_card])
  refine ⟨Module.Basis.mk hli hsp.ge, l, hl, fun i => ?_⟩
  rw [Module.Basis.mk_apply]
  have := (hv i).apply_eq_smul
  rwa [Matrix.toLin'_apply] at this

theorem UpperTheory.V.Ws.invariant_submodule_eq_span_eigenbasis_of_separable :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (n : ℕ) (M : Matrix (Fin n) (Fin n) K), M.charpoly.Separable →
      ∃ b : Module.Basis (Fin n) K (Fin n → K), ∀ W : Submodule K (Fin n → K), (∀ v ∈ W, M *ᵥ v ∈ W) →
        W = Submodule.span K (b '' {i | b i ∈ W}) := by
  classical
  intro K _ _ n M hM
  obtain ⟨b, l, hl, hb⟩ := exists_eigenbasis_of_separable_charpoly M hM
  refine ⟨b, fun W hW => le_antisymm ?_ ?_⟩
  · have hcomm : ∀ x : Fin n → K, b.equivFun.symm (diagonal l *ᵥ x) = M *ᵥ b.equivFun.symm x := by
      intro x
      rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply, Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mulVec_smul, hb, mulVec_diagonal, smul_smul, mul_comm]
    have key := UpperTheory.V.AlgebraTools.coordSub K (Fin n) l
      (fun i j h => (sub_ne_zero.mpr (fun h' => h (hl h'))).isUnit)
      (W.comap b.equivFun.symm.toLinearMap)
      (fun w hw => by
        rw [Submodule.mem_comap, LinearEquiv.coe_coe] at hw ⊢
        rw [hcomm]
        exact hW _ hw)
    intro v hv
    have h1 : ∀ i, b.repr v i • b i ∈ W := by
      intro i
      have h2 := key (b.equivFun v) (by
        rw [Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]; exact hv) i
      rw [Submodule.mem_comap, LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply,
        Finset.sum_eq_single i (fun j _ h => by rw [Pi.single_eq_of_ne h, zero_smul])
          (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, Module.Basis.equivFun_apply] at h2
      exact h2
    rw [← b.sum_repr v]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases h : b.repr v i = 0
    · rw [h, zero_smul]; exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, (W.smul_mem_iff h).mp (h1 i), rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact hi
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.PowSep
section
open IsLocalRing Polynomial Matrix UpperTheory.V

theorem UpperTheory.V.Ws.charpoly_pow_separable_of_eigenvalue_ratios_not_finOrder :
    ∀ (K : Type) [Field K] (n : ℕ) (M : Matrix (Fin n) (Fin n) K) (a : Fin n → Kˣ), M.charpoly = ∏ i, (X - C (a i : K)) →
      (∀ i j, i ≠ j → ¬ IsOfFinOrder (a i / a j)) → ∀ d : ℕ, 0 < d → (M ^ d).charpoly.Separable := by
  intro K _ n M a hM ha d hd
  have hinj : Function.Injective (fun i => (a i : K) ^ d) := by
    intro i j hij
    by_contra hne
    apply ha i j hne
    rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨d, hd, ?_⟩
    rw [div_pow, div_eq_one]
    apply Units.ext
    simpa using hij
  have hroot : ∀ i, (M ^ d).charpoly.IsRoot ((a i : K) ^ d) := by
    intro i
    rw [← Matrix.mem_spectrum_iff_isRoot_charpoly]
    apply spectrum.pow_mem_pow
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, hM, Polynomial.IsRoot, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hdvd : (∏ i, (X - C ((a i : K) ^ d))) ∣ (M ^ d).charpoly := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact Polynomial.pairwise_coprime_X_sub_C hinj hij
    · intro i _
      exact Polynomial.dvd_iff_isRoot.2 (hroot i)
  have hmon : (∏ i, (X - C ((a i : K) ^ d))).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)
  have heq : (M ^ d).charpoly = ∏ i, (X - C ((a i : K) ^ d)) := by
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon (Matrix.charpoly_monic _) hdvd
    rw [Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ]
  rw [heq]
  exact Polynomial.separable_prod_X_sub_C_iff.2 hinj
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.SignCharEqOneOfCyclotomicSubOneNotIsUnit
section
open IsLocalRing Polynomial Matrix UpperTheory.V

private theorem UpperTheory.V.Ws.tendsto_pow_prime_pow_one (l : ℕ) [Fact l.Prime] (x : ℤ_[l]) (hx : ¬ IsUnit (x - 1)) :
    Filter.Tendsto (fun n : ℕ => x ^ l ^ n) Filter.atTop (nhds 1) := by
  have hd : (l : ℤ_[l]) ∣ x - 1 :=
    (PadicInt.norm_lt_one_iff_dvd _).mp (PadicInt.mem_nonunits.mp (mem_nonunits_iff.mpr hx))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ n : ℕ, ‖x ^ l ^ n - 1‖ ≤ ((l : ℝ)⁻¹) ^ (n + 1) := by
    intro n
    obtain ⟨c, hc⟩ := dvd_sub_pow_of_dvd_sub hd n
    rw [one_pow] at hc
    rw [hc, norm_mul, norm_pow, PadicInt.norm_p]
    calc _ ≤ (l : ℝ)⁻¹ ^ (n + 1) * 1 :=
          mul_le_mul_of_nonneg_left (PadicInt.norm_le_one c) (by positivity)
      _ = _ := mul_one _
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have h0 : Filter.Tendsto (fun n : ℕ => ((l : ℝ)⁻¹) ^ (n + 1)) Filter.atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (l : ℝ)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ hl)
    exact this.comp (Filter.tendsto_add_atTop_nat 1)
  exact squeeze_zero (fun n => norm_nonneg _) hb h0

theorem UpperTheory.V.Ws.sign_char_eq_one_of_cyclotomic_sub_one_not_isUnit :
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
      (ε : G →* ℤ_[l]ˣ), Continuous ε → ∀ η : G →* ℤˣ, IsOpen (η.ker : Set G) → ε.ker ≤ η.ker →
      ∀ g, ¬ IsUnit ((ε g : ℤ_[l]) - 1) → η g = 1 := by
  intro l _ hl2 G _ _ _ _ ε hε η hopen hker g hg
  rcases Int.units_eq_one_or (η g) with h | h
  · exact h
  exfalso
  have hodd : Odd l := (Fact.out : l.Prime).odd_of_ne_two hl2
  let C : Set G := ((η.ker : Set G))ᶜ
  have hCc : IsCompact C := (isClosed_compl_iff.mpr hopen).isCompact
  let f : G → ℤ_[l] := fun h => (ε h : ℤ_[l])
  have hf : Continuous f := Units.continuous_val.comp hε
  have hK : IsClosed (f '' C) := (hCc.image hf).isClosed
  have hmem : ∀ n : ℕ, f (g ^ l ^ n) ∈ f '' C := by
    intro n
    refine ⟨g ^ l ^ n, ?_, rfl⟩
    show g ^ l ^ n ∉ η.ker
    rw [MonoidHom.mem_ker, map_pow, h, (hodd.pow).neg_one_pow]
    decide
  have hlim : Filter.Tendsto (fun n : ℕ => f (g ^ l ^ n)) Filter.atTop (nhds 1) := by
    have := tendsto_pow_prime_pow_one l (ε g : ℤ_[l]) hg
    refine this.congr fun n => ?_
    simp [f, map_pow]
  have h1 : (1 : ℤ_[l]) ∈ f '' C := hK.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)
  obtain ⟨k, hkC, hk1⟩ := h1
  apply hkC
  apply hker
  rw [MonoidHom.mem_ker]
  exact Units.ext hk1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.StabClosed
section
open IsLocalRing Polynomial Matrix UpperTheory.V

theorem UpperTheory.V.Ws.isClosed_setOf_matrix_stabilizes_submodule :
    ∀ (G κ : Type) [TopologicalSpace G] [Field κ] (n : ℕ) (a : G → Matrix (Fin n) (Fin n) κ), Pr.LinClosed a →
      ∀ W : Submodule κ (Fin n → κ), IsClosed {g | ∀ v ∈ W, a g *ᵥ v ∈ W} := by
  intro G κ _ _ n a ha W
  have hset : {g | ∀ v ∈ W, a g *ᵥ v ∈ W} =
      ⋂ v ∈ W, ⋂ φ ∈ W.dualAnnihilator, {g | φ (a g *ᵥ v) = 0} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h v hv φ hφ
      exact (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).mpr (h v hv) φ hφ
    · intro h v hv
      exact (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).mp (fun φ hφ => h v hv φ hφ)
  rw [hset]
  refine isClosed_biInter fun v _ => isClosed_biInter fun φ _ => ?_
  let f : Matrix (Fin n) (Fin n) κ →ₗ[κ] κ :=
    { toFun := fun M => φ (M *ᵥ v)
      map_add' := by
        intro M N
        simp [Matrix.add_mulVec]
      map_smul' := by
        intro c M
        simp only [Matrix.smul_mulVec, map_smul, smul_eq_mul, RingHom.id_apply] }
  exact ha f
end

