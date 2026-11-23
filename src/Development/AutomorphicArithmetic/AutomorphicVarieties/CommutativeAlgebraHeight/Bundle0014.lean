module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0011
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.LocDim
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DChKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CplCm
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

theorem UpperTheory.V.CA.cpl_cm :
    ∀ (S R : Type) [CommRing S] [IsLocalRing S] [CommRing R] [IsLocalRing R] [Algebra S R], IsCplAt (maximalIdeal S) R → IsCM S → IsCM R ∧ DimFormula R ∧ DimFormula S ∧ ringKrullDim R = ringKrullDim S := by
  intro S R _ _ _ _ _ hR hS
  haveI : IsNoetherianRing S := hS.1
  haveI : IsNoetherianRing R := hR.noeth
  haveI : Module.Flat S R := (c3a (maximalIdeal S) hR).1
  have hdim : ringKrullDim R = ringKrullDim S := by
    have h := (c3c (maximalIdeal S) hR).1 ⊥
    rw [Ideal.map_bot] at h
    unfold dimAt at h
    rw [Ideal.map_bot] at h
    have hu : (maximalIdeal S).primeCompl ≤ IsUnit.submonoid S := fun x hx =>
      IsLocalRing.notMem_maximalIdeal.mp hx
    have e : S ≃+* Localization.AtPrime (maximalIdeal S) :=
      (IsLocalization.atUnits S (maximalIdeal S).primeCompl hu).toRingEquiv
    rw [← ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R), h,
      ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _), ringKrullDim_eq_of_ringEquiv e.symm]
  have hcomap : Ideal.comap (algebraMap S R) (maximalIdeal R) = maximalIdeal S := by
    simpa using hR.comap_pow 1
  have hRCM : IsCM R := by
    obtain ⟨-, n, hn, rs, hlen, hmem, hreg⟩ := hS
    have hmem' : ∀ r ∈ rs.map (algebraMap S R), r ∈ maximalIdeal R := by
      intro r hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      have : a ∈ Ideal.comap (algebraMap S R) (maximalIdeal R) := by
        rw [hcomap]
        exact hmem a ha
      exact this
    refine ⟨inferInstance, n, hdim.trans hn, rs.map (algebraMap S R), by simp [hlen], hmem', ?_⟩
    exact (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem').mpr
      hreg.toIsWeaklyRegular.of_flat
  exact ⟨hRCM, fun p _ => hRCM.height_add_ringKrullDim_quotient p,
    fun p _ => hS.height_add_ringKrullDim_quotient p, hdim⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DClosed
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem map_nat {n : ℕ} {A A' G B B' : Type} [CommRing A] [CommRing A'] [Group G] (D : GDet n A G)
    [CommRing B] [CommRing B'] [Algebra A B] [Algebra A' B'] (f : A →+* A') (φ : B →+* B')
    (hφ : ∀ a, φ (algebraMap A B a) = algebraMap A' B' (f a)) (x : MonoidAlgebra B G) :
    (D.map f).D B' (MonoidAlgebra.mapRingHom G φ x) = φ (D.D B x) := by
  letI : Algebra A B' := ((algebraMap A' B').comp f).toAlgebra
  exact D.nat B B' { φ with commutes' := hφ } x

private theorem mapR_comp {A B C G : Type} [CommRing A] [CommRing B] [CommRing C] [Group G]
    (f : A →+* B) (g : B →+* C) (x : MonoidAlgebra A G) :
    MonoidAlgebra.mapRingHom G g (MonoidAlgebra.mapRingHom G f x) = MonoidAlgebra.mapRingHom G (g.comp f) x := by
  ext a; simp

private theorem kills_map {n : ℕ} {A A' G : Type} [CommRing A] [CommRing A'] [Group G] (D : GDet n A G)
    (f : A →+* A') (z : MonoidAlgebra A G) (hz : D.Kills z) :
    (D.map f).Kills (MonoidAlgebra.mapRingHom G f z) := by
  intro B _ _ h
  letI : Algebra A B := ((algebraMap A' B).comp f).toAlgebra
  rw [mapR_comp]
  exact hz B h

theorem UpperTheory.V.CA.d_closed :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (I : Ideal A) [IsHausdorff I A], D.IsCont I → ∀ Z : Set (MonoidAlgebra A G), (∀ z ∈ Z, D.Kills z) → ∀ y ∈ closureIdeal I Z, D.Kills y := by
  intro n A G _ _ D _ _ _ _ I _ hD Z hZ y hy
  have key : ∀ N : ℕ, (D.map (Ideal.Quotient.mk (I ^ N))).Kills
      (MonoidAlgebra.mapRingHom G (Ideal.Quotient.mk (I ^ N)) y) := by
    intro N
    obtain ⟨H, hH⟩ := exists_openNormalSubgroup_kills_of_groupDetLaw_isCont D I hD N
    have hiff : ∀ x, x ∈ (D.map (Ideal.Quotient.mk (I ^ N))).toDet.ker ↔
        (D.map (Ideal.Quotient.mk (I ^ N))).Kills x := fun x =>
      (d_ker _ x).1.trans (d_toDet _ x).2.2.2
    have hy' := (TwoSidedIdeal.mem_iInf _).1 ((TwoSidedIdeal.mem_iInf _).1 hy N) H
    have hle : TwoSidedIdeal.span
        (Z ∪ {z | ∃ a ∈ I ^ N, z = MonoidAlgebra.single 1 a} ∪ {z | ∃ h ∈ H, z = MonoidAlgebra.single h 1 - 1}) ≤
        TwoSidedIdeal.comap (MonoidAlgebra.mapRingHom G (Ideal.Quotient.mk (I ^ N)))
          (D.map (Ideal.Quotient.mk (I ^ N))).toDet.ker := by
      rw [TwoSidedIdeal.span_le]
      rintro z ((hz | ⟨a, ha, rfl⟩) | ⟨h, hh, rfl⟩)
      · rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap, hiff]
        exact kills_map D _ z (hZ z hz)
      · rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap, MonoidAlgebra.mapRingHom_single,
          Ideal.Quotient.eq_zero_iff_mem.2 ha, MonoidAlgebra.single_zero]
        exact TwoSidedIdeal.zero_mem _
      · rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap, hiff, map_sub, map_one, MonoidAlgebra.mapRingHom_single,
          map_one]
        exact hH h hh
    exact (hiff _).1 ((TwoSidedIdeal.mem_comap _).1 (hle hy'))
  have key2 : ∀ (k : ℕ) (h : MonoidAlgebra (MvPolynomial (Fin k) A) G),
      D.D (MvPolynomial (Fin k) A)
        (1 + h * MonoidAlgebra.mapRingHom G (algebraMap A (MvPolynomial (Fin k) A)) y) = 1 := by
    intro k h
    rw [← sub_eq_zero]
    refine MvPolynomial.ext _ _ fun β => ?_
    rw [MvPolynomial.coeff_zero]
    refine IsHausdorff.haus (inferInstance : IsHausdorff I A) _ fun N => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq_zero_iff_mem, ← MvPolynomial.coeff_map,
      map_sub, map_one]
    have h1 := map_nat D (Ideal.Quotient.mk (I ^ N))
      (MvPolynomial.map (σ := Fin k) (Ideal.Quotient.mk (I ^ N))) (fun a => by simp)
      (1 + h * MonoidAlgebra.mapRingHom G (algebraMap A (MvPolynomial (Fin k) A)) y)
    have h2 := key N (MvPolynomial (Fin k) (A ⧸ I ^ N))
      (MonoidAlgebra.mapRingHom G (MvPolynomial.map (σ := Fin k) (Ideal.Quotient.mk (I ^ N))) h)
    have h3 : (MvPolynomial.map (σ := Fin k) (Ideal.Quotient.mk (I ^ N))).comp
        (algebraMap A (MvPolynomial (Fin k) A)) =
        (algebraMap (A ⧸ I ^ N) (MvPolynomial (Fin k) (A ⧸ I ^ N))).comp (Ideal.Quotient.mk (I ^ N)) :=
      RingHom.ext fun a => by simp
    rw [map_add (f := _), map_one, map_mul, mapR_comp, h3, ← mapR_comp, h2] at h1
    rw [← h1, sub_self, MvPolynomial.coeff_zero]
    rfl
  refine (d_toDet D y).2.2.2.1 (d_kills_poly D.toDet y Set.univ Submodule.span_univ fun k h _ => ?_)
  change D.D _ (ofT A G _ _) = 1
  rw [map_add (f := _), map_one, map_mul, ofT_tmul, one_smul]
  exact key2 k _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DFaithfulSs
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem fss_scalar {k E M : Type} [Field k] [IsAlgClosed k] [Ring E] [Algebra k E] [AddCommGroup M]
    [Module k M] [Module E M] [IsScalarTower k E M] [IsSimpleModule E M]
    (h : ∀ x : E, ∃ p : k[X], p.Monic ∧ aeval x p = 0) (φ : Module.End E M) : ∃ c : k, ∀ v, φ v = c • v := by
  haveI := IsSimpleModule.nontrivial E M
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  obtain ⟨r, hr⟩ := IsSimpleModule.toSpanSingleton_surjective E hv (φ v)
  replace hr : r • v = φ v := hr
  obtain ⟨p, hp, hp0⟩ := h r
  by_contra hne
  push Not at hne
  have key : ∀ s : Multiset k, aeval r (s.map fun a => X - C a).prod • v ≠ 0 := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simpa using hv
    | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, mul_comm, map_mul, mul_smul]
      set q := aeval r (s.map fun a => X - C a).prod
      let ψ : Module.End E M := φ - a • (1 : Module.End E M)
      have h1 : aeval r (X - C a) • v = ψ v := by simp [ψ, sub_smul, hr]
      rw [h1, ← map_smul]
      rcases LinearMap.bijective_or_eq_zero ψ with hb | hb
      · exact fun h0 => ih (hb.1 (h0.trans (map_zero ψ).symm))
      · obtain ⟨w, hw⟩ := hne a
        have := LinearMap.congr_fun hb w
        simp only [ψ, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, LinearMap.zero_apply] at this
        exact absurd (sub_eq_zero.1 this) hw
  have := key p.roots
  rw [← (IsAlgClosed.splits p).eq_prod_roots_of_monic hp, hp0, zero_smul] at this
  exact this rfl

private theorem fss_fin {n : ℕ} {k E M : Type} [Field k] [IsAlgClosed k] [Ring E] [Algebra k E] [AddCommGroup M]
    [Module k M] [Module E M] [IsScalarTower k E M] [IsSimpleModule E M]
    (h : ∀ x : E, ∃ p : k[X], p.Monic ∧ p.natDegree ≤ n ∧ aeval x p = 0) : Module.Finite k M := by
  classical
  let b := Module.Basis.ofVectorSpace k M
  rcases finite_or_infinite (Module.Basis.ofVectorSpaceIndex k M) with hf | hf
  · exact Module.Finite.of_basis b
  exfalso
  let e := Infinite.natEmbedding (Module.Basis.ofVectorSpaceIndex k M)
  let f : M →ₗ[k] M := b.constr k fun i => b (e (Function.invFun e i + 1))
  have hfe : ∀ i, f (b (e i)) = b (e (i + 1)) := fun i => by
    simp only [f, Module.Basis.constr_basis]
    rw [Function.leftInverse_invFun e.injective i]
  let F : Module.End (Module.End E M) M :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun φ v => by
        obtain ⟨c, hc⟩ := fss_scalar (k := k) (fun x => (h x).imp fun p hp => ⟨hp.1, hp.2.2⟩) φ
        simp [hc] }
  obtain ⟨r, hr⟩ := jacobson_density F ((Finset.range n).image fun i => b (e i))
  have hr' : ∀ i ≤ n, r ^ i • b (e 0) = b (e i) := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', mul_smul, ih (by omega), ← hfe]
      exact (hr _ (Finset.mem_image_of_mem _ (Finset.mem_range.2 (by omega)))).symm
  obtain ⟨p, hp, hpn, hp0⟩ := h r
  have h1 : ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • b (e i) = 0 := by
    have := congrArg (· • b (e 0)) hp0
    simp only [aeval_eq_sum_range, zero_smul, Finset.sum_smul, smul_assoc] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hr' i (by have := Finset.mem_range.1 hi; omega)]
  have h2 := linearIndependent_iff'.1 (b.linearIndependent.comp e e.injective) _ _ h1 p.natDegree (by simp)
  rw [hp.coeff_natDegree] at h2
  exact one_ne_zero h2

private theorem fss_count {n : ℕ} {k E : Type} [Field k] [IsAlgClosed k] [Ring E] [Algebra k E]
    (h : ∀ x : E, ∃ p : k[X], p.Monic ∧ p.natDegree ≤ n ∧ aeval x p = 0) (m : ℕ → Ideal E)
    (hm : ∀ i, IsCoatom (m i)) (hinj : Function.Injective fun i => Module.annihilator E (E ⧸ m i)) : False := by
  classical
  haveI : ∀ i, IsSimpleModule E (E ⧸ m i) := fun i => isSimpleModule_iff_isCoatom.2 (hm i)
  let a : ℕ ↪ k := Infinite.natEmbedding k
  let M := ∀ i : Fin (n + 1), E ⧸ m i
  have hz : ∀ (φ : Module.End E M) (i j : Fin (n + 1)) (x : E ⧸ m i), i ≠ j → φ (Pi.single i x) j = 0 := by
    intro φ i j x hij
    rcases LinearMap.bijective_or_eq_zero ((LinearMap.proj j).comp (φ.comp
      (LinearMap.single E (fun i : Fin (n + 1) => E ⧸ m i) i))) with hb | hb
    · exact absurd (Fin.ext (hinj (LinearEquiv.ofBijective _ hb).annihilator_eq)) hij
    · exact LinearMap.congr_fun hb x
  let F : Module.End (Module.End E M) M :=
    { toFun := fun v j => algebraMap k E (a j) • v j
      map_add' := fun v w => funext fun j => smul_add _ _ _
      map_smul' := fun φ v => funext fun j => by
        have h1 : ∀ w : M, φ w j = φ (Pi.single j (w j)) j := fun w => by
          set_option synthInstance.maxHeartbeats 100000 in
            conv_lhs => rw [← Finset.univ_sum_single w, map_sum, Finset.sum_apply]
          exact Finset.sum_eq_single j (fun i _ hi => hz φ i j _ hi) (by simp)
        change algebraMap k E (a j) • φ v j = φ (fun j => algebraMap k E (a j) • v j) j
        rw [h1 v, h1 (fun j => algebraMap k E (a j) • v j), Pi.single_smul, map_smul]
        rfl }
  obtain ⟨r, hr⟩ := jacobson_density F {fun i => Submodule.Quotient.mk 1}
  replace hr := hr _ (Finset.mem_singleton_self _)
  obtain ⟨p, hp, hpn, hp0⟩ := h r
  have hroot : ∀ j : Fin (n + 1), p.eval (a j) = 0 := by
    intro j
    set v : E ⧸ m j := Submodule.Quotient.mk 1 with hv
    have h1 : r • v = a j • v := by
      rw [← algebraMap_smul E (a j) v]
      exact (congrFun hr j).symm
    have h2 : ∀ i : ℕ, r ^ i • v = a j ^ i • v := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => rw [pow_succ, mul_smul, h1, smul_comm, ih, smul_smul, pow_succ']
    have h3 : aeval r p • v = p.eval (a j) • v := by
      simp only [aeval_eq_sum_range, eval_eq_sum_range, Finset.sum_smul, smul_assoc, h2, mul_smul]
    rw [hp0, zero_smul] at h3
    refine (smul_eq_zero.1 h3.symm).resolve_right fun h0 => (hm j).1 ?_
    exact (Ideal.eq_top_iff_one _).2 ((Submodule.Quotient.mk_eq_zero _).1 h0)
  refine hp.ne_zero (eq_zero_of_natDegree_lt_card_of_eval_eq_zero p (f := fun j : Fin (n + 1) => a j)
    (fun i j hij => Fin.ext (a.injective hij)) hroot ?_)
  simp only [Fintype.card_fin]
  omega

private theorem fss_alg {n : ℕ} {k E : Type} [Field k] [IsAlgClosed k] [Ring E] [Algebra k E]
    (h : ∀ x : E, ∃ p : k[X], p.Monic ∧ p.natDegree ≤ n ∧ aeval x p = 0) (hj : Ring.jacobson E = ⊥) :
    Module.Finite k E := by
  let S : Set (Ideal E) := {P | ∃ m : Ideal E, IsCoatom m ∧ Module.annihilator E (E ⧸ m) = P}
  have hS : ∀ P : S, ∃ m : Ideal E, IsCoatom m ∧ Module.annihilator E (E ⧸ m) = P := fun P => P.2
  choose m hm hm' using hS
  haveI : Finite S := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    let e := Infinite.natEmbedding S
    refine fss_count h (fun i => m (e i)) (fun i => hm _) fun i j hij => e.injective (Subtype.ext ?_)
    rw [← hm', ← hm']
    exact hij
  haveI : ∀ P, IsSimpleModule E (E ⧸ m P) := fun i => isSimpleModule_iff_isCoatom.2 (hm i)
  haveI : ∀ P, Module.Finite k (E ⧸ m P) := fun i => fss_fin h
  let f : E →ₗ[k] ∀ P : S, Module.End k (E ⧸ m P) :=
    LinearMap.pi fun P => (Algebra.lsmul k k (E ⧸ m P) (A := E)).toLinearMap
  refine Module.Finite.of_injective f ((injective_iff_map_eq_zero f).2 fun x hx => ?_)
  rw [← Ideal.mem_bot, ← hj]
  refine Submodule.mem_sInf.2 fun I hI => ?_
  have h1 : x ∈ Module.annihilator E (E ⧸ m ⟨_, I, hI, rfl⟩) :=
    Module.mem_annihilator.2 fun v => LinearMap.congr_fun (congrFun hx ⟨_, I, hI, rfl⟩) v
  rw [hm'] at h1
  have h2 := Module.mem_annihilator.1 h1 (Submodule.Quotient.mk 1)
  rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one] at h2
  exact (Submodule.Quotient.mk_eq_zero _).1 h2

theorem UpperTheory.V.CA.d_faithful_ss :
    ∀ {n : ℕ} {k E : Type} [Field k] [IsAlgClosed k] [Ring E] [Algebra k E] (D : Det n k E), D.ker = ⊥ → Module.Finite k E ∧ IsSemisimpleRing E := by
  intro n k E _ _ _ _ D hD
  have hCH : D.IsCH := le_bot_iff.1 (hD ▸ d_ch_ker D)
  have hj : Ring.jacobson E = ⊥ := by
    refine le_bot_iff.1 fun x hx => ?_
    have h1 := (d_ker _ _).1.1 ((d_rad D hCH x).2 hx)
    have h2 : D.Kills x := by
      intro S _ _ y
      letI : Algebra (ResidueField k) S :=
        (Ideal.Quotient.lift (maximalIdeal k) (algebraMap k S) fun a ha => by
          rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at ha
          rw [ha, map_zero]).toAlgebra
      haveI : IsScalarTower k (ResidueField k) S := .of_algebraMap_eq fun _ => rfl
      obtain ⟨z, rfl⟩ : ∃ z, Det.cancel k E (ResidueField k) S z = y := by
        induction y with
        | tmul s e => exact ⟨s ⊗ₜ (1 ⊗ₜ e), by simp [Det.cancel_tmul]⟩
        | add a b ha hb =>
          obtain ⟨a, rfl⟩ := ha
          obtain ⟨b, rfl⟩ := hb
          exact ⟨a + b, map_add _ _ _⟩
      have h3 := h1 S z
      rw [(d_bc D (ResidueField k)).1] at h3
      simpa [Det.cancel_tmul] using h3
    have h4 := (d_ker D x).1.2 h2
    rw [hD] at h4
    simpa using h4
  haveI := fss_alg (n := n) (k := k) (E := E)
    (fun x => ⟨D.chi x, (d_chi D x).2.2.2.2.1, (d_chi D x).2.2.2.2.2.1, ((d_chS D k).2.2 hCH).2 x⟩) hj
  haveI : IsArtinianRing E := IsArtinianRing.of_finite k E
  exact ⟨inferInstance, IsArtinianRing.isSemisimpleRing_iff_jacobson.2 hj⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_gext :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (D' : GDet n A G), (∀ (g : G) (i : ℕ), 1 ≤ i → i ≤ n → D.lam i (MonoidAlgebra.single g 1) = D'.lam i (MonoidAlgebra.single g 1)) → D = D' := by
  intro n A G _ _ D D' h
  have key : D.toDet = D'.toDet := by
    refine d_ext D.toDet D'.toDet (MonoidHom.mrange (MonoidAlgebra.of A G)) ?_ ?_
    · rw [eq_top_iff]
      rintro x -
      induction x using MonoidAlgebra.induction_linear with
      | zero => exact zero_mem _
      | add a b ha hb => exact add_mem ha hb
      | single g r =>
        have : MonoidAlgebra.single g r = r • MonoidAlgebra.single g (1 : A) := by simp
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
    · rintro x ⟨g, rfl⟩ i h1 h2
      rw [(d_toDet D _).2.1, (d_toDet D' _).2.1]
      exact h g i h1 h2
  rw [← GDet.ofDet_toDet D, key, GDet.ofDet_toDet]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmaDet
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem chi_congr {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D D' : Det n A E) (y : E)
    (h : ∀ (B : Type) [CommRing B] [Algebra A B] (b : B), D.D B (1 + b ⊗ₜ y) = D'.D B (1 + b ⊗ₜ y)) :
    D.chi y = D'.chi y := by
  let L := Localization.Away (X : A[X])
  have hinj : Function.Injective (algebraMap A[X] L) :=
    IsLocalization.injective L (M := Submonoid.powers (X : A[X]))
      (by
        rintro _ ⟨k, rfl⟩
        exact pow_mem monic_X.mem_nonZeroDivisors k)
  apply hinj
  have key : ∀ D₀ : Det n A E, algebraMap A[X] L (D₀.chi y) =
      algebraMap A[X] L X ^ n * D₀.D L (1 + (-IsLocalization.Away.invSelf (S := L) (X : A[X])) ⊗ₜ y) := by
    intro D₀
    have h1 := D₀.nat A[X] L (IsScalarTower.toAlgHom A A[X] L) (X ⊗ₜ 1 - 1 ⊗ₜ y)
    rw [← D₀.homog]
    refine h1.symm.trans ?_
    congr 1
    rw [smul_add, smul_tmul', smul_eq_mul, mul_neg, IsLocalization.Away.mul_invSelf, neg_tmul,
      Algebra.TensorProduct.one_def, smul_tmul', smul_eq_mul, mul_one, ← sub_eq_add_neg]
    simp
  rw [key, key, h]

private theorem chi_one {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) :
    D.chi 1 = (X - 1) ^ n := by
  have := D.homog A[X] (X - 1) 1
  rw [map_one, mul_one] at this
  rw [← this, Det.chi, ← sub_tmul, Algebra.TensorProduct.one_def, smul_tmul', smul_eq_mul, mul_one]

private theorem chi_zero {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) :
    D.chi 0 = X ^ n := by
  have := D.homog A[X] X 1
  rw [map_one, mul_one] at this
  rw [← this, Det.chi, tmul_zero, sub_zero, Algebra.TensorProduct.one_def, smul_tmul', smul_eq_mul, mul_one]

private theorem ev_one_add {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : E)
    (h : D.D A[X] (1 + X ⊗ₜ e) = 1 + X) (B : Type) [CommRing B] [Algebra A B] (b : B) :
    D.D B (1 + b ⊗ₜ e) = 1 + b := by
  have := D.nat A[X] B (aeval b) (1 + X ⊗ₜ e)
  rw [h] at this
  simpa using this

private theorem det_one_add_single {n : ℕ} {B : Type} [CommRing B] (i : Fin n) (b : B) :
    (1 + Matrix.single i i b).det = 1 + b := by
  rw [← Matrix.diagonal_single, ← Matrix.diagonal_one, Matrix.diagonal_add, Matrix.det_diagonal,
    Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

private noncomputable def rS {n : ℕ} {A E S : Type} [CommRing A] [Ring E] [Algebra A E] [CommRing S] [Algebra A S]
    (r : E →ₐ[A] Matrix (Fin n) (Fin n) S) : S ⊗[A] E →ₐ[S] Matrix (Fin n) (Fin n) S :=
  Algebra.TensorProduct.lift (Algebra.ofId S _) r fun s _ => Algebra.commute_algebraMap_left s _

private theorem rS_tmul {n : ℕ} {A E S : Type} [CommRing A] [Ring E] [Algebra A E] [CommRing S] [Algebra A S]
    (r : E →ₐ[A] Matrix (Fin n) (Fin n) S) (s : S) (x : E) : rS r (s ⊗ₜ x) = s • r x :=
  (Algebra.TensorProduct.lift_tmul _ _ _ s x).trans (Algebra.smul_def _ _).symm

private def adapted {n : ℕ} {E : Type} [Ring E] (e : Fin n → E) (he : ∀ i, IsIdempotentElem (e i)) : Submonoid E where
  carrier := {x | x = 1 ∨ ∃ i j, e i * x * e j = x}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro x y (rfl | ⟨i, j, hx⟩) hy
    · simpa using hy
    rcases hy with rfl | ⟨k, l, hy⟩
    · exact Or.inr ⟨i, j, by simpa using hx⟩
    have h1 : e i * x = x := by rw [← hx, ← mul_assoc, ← mul_assoc, (he i).eq]
    have h2 : y * e l = y := by rw [← hy, mul_assoc, (he l).eq]
    exact Or.inr ⟨i, l, by rw [← mul_assoc, h1, mul_assoc, h2]⟩

theorem UpperTheory.V.CA.d_gma_det :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : Fin n → E), D.IsCH → CompleteOrthogonalIdempotents e → (∀ i, D.D A[X] (1 + X ⊗ₜ e i) = 1 + X) → ∀ (S : Type) [CommRing S] [Algebra A S] (r : E →ₐ[A] Matrix (Fin n) (Fin n) S), (∀ i, r (e i) = Matrix.single i i 1) → ∀ (T : Type) [CommRing T] [Algebra A T] [Algebra S T] [IsScalarTower A S T] {ι : Type} [Fintype ι] (t : ι → T) (x : ι → E), D.D T (∑ a, t a ⊗ₜ x a) = (∑ a, t a • (r (x a)).map (algebraMap S T)).det := by
  intro n A E _ _ _ D e hCH he h1 S _ _ r hr T _ _ _ _ ι _ t x
  have hrep : ∀ (B : Type) [CommRing B] [Algebra S B] (y : B ⊗[S] (S ⊗[A] E)),
      (Det.ofRep (Fintype.card_fin n) (rS r)).D B y = (Det.repS (rS r) B y).det := fun _ _ _ _ => rfl
  have main : D.baseChange S = Det.ofRep (Fintype.card_fin n) (rS r) := by
    refine d_ext _ _ ((adapted e he.idem).map
      (Algebra.TensorProduct.includeRight : E →ₐ[A] S ⊗[A] E).toMonoidHom) ?_ ?_
    · rw [eq_top_iff]
      rintro y -
      induction y with
      | add a b ha hb => exact add_mem ha hb
      | tmul s z =>
        have hz : z = ∑ i, ∑ j, e i * z * e j := by
          simp only [← Finset.mul_sum, he.complete, mul_one, ← Finset.sum_mul, one_mul]
        have hs : s ⊗ₜ[A] z = s • ((1 : S) ⊗ₜ[A] z) := by rw [smul_tmul', smul_eq_mul, mul_one]
        rw [hs, hz]
        refine Submodule.smul_mem _ _ ?_
        simp only [tmul_sum]
        refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.subset_span ?_
        refine ⟨e i * z * e j, Or.inr ⟨i, j, ?_⟩, rfl⟩
        rw [← mul_assoc, ← mul_assoc, (he.idem i).eq, mul_assoc, (he.idem j).eq]
    · rintro _ ⟨z, hz, rfl⟩ k hk1 hkn
      change (D.baseChange S).lam k ((1 : S) ⊗ₜ[A] z) = Det.lam _ k ((1 : S) ⊗ₜ[A] z)
      rcases hz with rfl | ⟨i, j, hz⟩
      · rw [← Algebra.TensorProduct.one_def, Det.lam, Det.lam, chi_one, chi_one]
      by_cases hij : i = j
      · subst hij
        have hc := (d_corner D (e i) hCH (he.idem i) (h1 i) (hk1.trans hkn)).1 z
        rw [hz] at hc
        generalize D.tr (e i * z) = a at hc
        subst hc
        rw [Det.lam, Det.lam, chi_congr (D.baseChange S) (Det.ofRep (Fintype.card_fin n) (rS r))]
        intro B _ _ b
        letI : Algebra A B := ((algebraMap S B).comp (algebraMap A S)).toAlgebra
        haveI : IsScalarTower A S B := .of_algebraMap_eq fun _ => rfl
        rw [(d_bc D S).1 B, hrep, map_add (f := _), map_add (Det.repS _ _), map_one, map_one (Det.repS _ _),
          Det.cancel_tmul, Det.repS_tmul, rS_tmul, map_one, mul_one, ← smul_tmul, ev_one_add D _ (h1 i), map_smul, hr, one_smul,
          ← det_one_add_single i (a • b)]
        congr 2
        ext p q
        simp only [Matrix.single_apply, Matrix.smul_apply, Matrix.map_apply]
        split_ifs
        · rw [Algebra.smul_def, Algebra.smul_def a, mul_one, smul_eq_mul, mul_comm]; rfl
        · simp
      · have h0 : ∀ D₀ : Det n S (S ⊗[A] E), D₀.lam k ((1 : S) ⊗ₜ[A] z) = D₀.lam k 0 := by
          intro D₀
          have e1 : (1 : S) ⊗ₜ[A] z = ((1 : S) ⊗ₜ[A] (e i * z)) * ((1 : S) ⊗ₜ[A] e j) := by
            rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hz]
          rw [e1, (d_tr D₀).2.1, Algebra.TensorProduct.tmul_mul_tmul, ← mul_assoc, he.ortho (Ne.symm hij),
            zero_mul, tmul_zero]
        rw [h0, h0, Det.lam, Det.lam, chi_zero, chi_zero]
  have h2 := (d_bc D S).1 T (∑ a, t a ⊗ₜ ((1 : S) ⊗ₜ[A] x a))
  rw [main, hrep] at h2
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Det.cancel_tmul, Det.repS_tmul, rS_tmul, map_one, mul_one, one_smul] at h2
  exact h2.symm
end

