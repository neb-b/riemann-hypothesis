module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RegularLocalRegularSequence.ExistsIsRegularOfListEqMaximalIdeal
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.Nakayama
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0069

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.AevalNat
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section

variable {n : ℕ} {A G : Type} [CommRing A] [Group G]

private noncomputable def pol (D : GDet n A G) (s : Finset G) : MvPolynomial s A :=
  D.D _ (∑ a : s, MonoidAlgebra.single (a : G) (MvPolynomial.X a))

private theorem pol_homog (D : GDet n A G) (s : Finset G) : (pol D s).IsHomogeneous n := by
  have h := (d_poly D.toDet (fun a : s => (MonoidAlgebra.single (a : G) 1 : MonoidAlgebra A G))).1
  have h2 : D.toDet.poly (fun a : s => (MonoidAlgebra.single (a : G) 1 : MonoidAlgebra A G)) = pol D s := by
    change D.D _ (ofT A G _ _) = D.D _ _
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Det.gen, map_sum, ofT_tmul]
  rwa [h2] at h

private theorem nat' (D : GDet n A G) {A' : Type} [CommRing A'] (f : A →+* A') {S S' : Type} [CommRing S]
    [Algebra A S] [CommRing S'] [Algebra A' S'] (φ : S →+* S')
    (h : ∀ a, φ (algebraMap A S a) = algebraMap A' S' (f a)) (y : MonoidAlgebra S G) :
    (D.map f).D S' (MonoidAlgebra.mapRingHom G φ y) = φ (D.D S y) :=
  letI : Algebra A S' := ((algebraMap A' S').comp f).toAlgebra
  D.nat S S' { φ with commutes' := h } y

private theorem pol_map (D : GDet n A G) {A' : Type} [CommRing A'] (f : A →+* A') (s : Finset G) :
    pol (D.map f) s = MvPolynomial.map f (pol D s) := by
  rw [pol, pol, ← nat' D f (MvPolynomial.map f) (by simp)]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum]

private theorem sum_single {S : Type} [CommRing S] (s : Finset G) (y : MonoidAlgebra S G)
    (hy : y.coeff.support ⊆ s) : ∑ a : s, MonoidAlgebra.single (a : G) (y.coeff a) = y := by
  classical
  rw [Finset.sum_coe_sort s (fun a => MonoidAlgebra.single a (y.coeff a))]
  ext g
  simp only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.1 fun h' => h (hy h')).symm

private theorem pol_eval (D : GDet n A G) (s : Finset G) {S : Type} [CommRing S] [Algebra A S]
    (y : MonoidAlgebra S G) (hy : y.coeff.support ⊆ s) :
    D.D S y = MvPolynomial.aeval (fun a : s => y.coeff a) (pol D s) := by
  rw [pol, ← D.nat]
  congr 1
  conv_lhs => rw [← sum_single s y hy]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum]

private theorem aeval_nat {σ A' : Type} [CommRing A'] (f : A →+* A') {S S' : Type} [CommRing S]
    [Algebra A S] [CommRing S'] [Algebra A' S'] (φ : S →+* S')
    (h : ∀ a, φ (algebraMap A S a) = algebraMap A' S' (f a)) (c : σ → S) (p : MvPolynomial σ A) :
    φ (MvPolynomial.aeval c p) = MvPolynomial.aeval (fun a => φ (c a)) (MvPolynomial.map f p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [h]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.map_X]

private theorem supp_map {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (y : MonoidAlgebra S G) :
    (MonoidAlgebra.mapRingHom G φ y).coeff.support ⊆ y.coeff.support := by
  intro g hg
  rw [Finsupp.mem_support_iff] at hg ⊢
  intro h
  apply hg
  simp [h]

private theorem sep (I : Ideal A) [IsAdicComplete I A] {σ : Type} {p q : MvPolynomial σ A}
    (h : ∀ N : ℕ, MvPolynomial.map (Ideal.Quotient.mk (I ^ N)) p = MvPolynomial.map (Ideal.Quotient.mk (I ^ N)) q) :
    p = q := by
  ext m
  refine sub_eq_zero.1 (IsHausdorff.haus (I := I) inferInstance _ fun N => ?_)
  have := congrArg (AddMonoidAlgebra.coeff · m) (h N)
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map, Ideal.Quotient.eq] at this
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact this

private theorem lim0 (I : Ideal A) [IsAdicComplete I A] (c : ∀ N : ℕ, A ⧸ I ^ N)
    (h : ∀ (N M : ℕ) (h : M ≤ N), Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (c N) = c M) :
    ∃ a : A, ∀ N, Ideal.Quotient.mk (I ^ N) a = c N := by
  choose f hf using fun N => Ideal.Quotient.mk_surjective (c N)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) inferInstance (f := f) (fun {m k} hmk => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq, hf, ← h k m hmk, ← hf k,
      Ideal.Quotient.factor_mk])
  refine ⟨L, fun N => ?_⟩
  have := hL N
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq, hf] at this
  exact this.symm

private theorem lim1 (I : Ideal A) [IsAdicComplete I A] {σ : Type} [Finite σ]
    (c : ∀ N : ℕ, MvPolynomial σ (A ⧸ I ^ N)) (hc : ∀ N, (c N).IsHomogeneous n)
    (h : ∀ (N M : ℕ) (h : M ≤ N),
      MvPolynomial.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right h)) (c N) = c M) :
    ∃ p : MvPolynomial σ A, ∀ N, MvPolynomial.map (Ideal.Quotient.mk (I ^ N)) p = c N := by
  classical
  choose a ha using fun m : σ →₀ ℕ => lim0 I (fun N => (c N).coeff m) fun N M hle => by
    rw [← h N M hle, MvPolynomial.coeff_map]
  refine ⟨∑ m ∈ (Finsupp.finite_of_degree_le (σ := σ) n).toFinset, MvPolynomial.monomial m (a m), fun N => ?_⟩
  ext m
  simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · exact ha m N
  · rw [map_zero, (hc N).coeff_eq_zero]
    intro hd
    exact hm (by simp [hd])

private theorem lift_ex {S : Type} [CommRing S] [Algebra A S] (y : MonoidAlgebra S G) :
    ∃ y' : MonoidAlgebra (MvPolynomial S A) G, y'.coeff.support ⊆ y.coeff.support ∧
      MonoidAlgebra.mapRingHom G ((MvPolynomial.aeval id : MvPolynomial S A →ₐ[A] S) : MvPolynomial S A →+* S) y' = y := by
  classical
  refine ⟨∑ a : y.coeff.support, MonoidAlgebra.single (a : G) (MvPolynomial.X (y.coeff a)), ?_, ?_⟩
  · intro g hg
    by_contra h
    rw [Finsupp.mem_support_iff] at hg
    apply hg
    simp only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun a _ => Finsupp.single_eq_of_ne ?_
    rintro rfl
    exact h a.2
  · conv_rhs => rw [← sum_single _ y le_rfl]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]

end

theorem UpperTheory.V.CA.u_lim :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (I : Ideal A) [IsAdicComplete I A] (Ds : ∀ N : ℕ, GDet n (A ⧸ I ^ N) G), (∀ (N M : ℕ) (h : M ≤ N), (Ds N).map (Ideal.Quotient.factor (Ideal.pow_le_pow_right h)) = Ds M) → ∃! D : GDet n A G, ∀ N, D.map (Ideal.Quotient.mk (I ^ N)) = Ds N := by
  intro n A G _ _ I _ Ds hDs
  choose P hP using fun s : Finset G => lim1 I (fun N => pol (Ds N) s) (fun N => pol_homog _ s)
    fun N M h => by rw [← pol_map, hDs N M h]
  have red : ∀ (N : ℕ) (s : Finset G) {S S' : Type} [CommRing S] [Algebra A S] [CommRing S'] [Algebra (A ⧸ I ^ N) S']
      (φ : S →+* S') (_ : ∀ a, φ (algebraMap A S a) = algebraMap _ S' (Ideal.Quotient.mk (I ^ N) a))
      (y : MonoidAlgebra S G), y.coeff.support ⊆ s →
      φ (MvPolynomial.aeval (fun a : s => y.coeff a) (P s)) = (Ds N).D S' (MonoidAlgebra.mapRingHom G φ y) := by
    intro N s S S' _ _ _ _ φ h y hy
    rw [aeval_nat _ φ h, hP, pol_eval _ s _ ((supp_map φ y).trans hy)]
    simp
  have red' : ∀ (N : ℕ) (s : Finset G) {σ : Type} (y : MonoidAlgebra (MvPolynomial σ A) G), y.coeff.support ⊆ s →
      MvPolynomial.map (Ideal.Quotient.mk (I ^ N)) (MvPolynomial.aeval (fun a : s => y.coeff a) (P s)) =
        (Ds N).D _ (MonoidAlgebra.mapRingHom G (MvPolynomial.map (Ideal.Quotient.mk (I ^ N))) y) :=
    fun N s σ y hy => red N s _ (by simp) y hy
  have nat : ∀ (s : Finset G) {S S' : Type} [CommRing S] [Algebra A S] [CommRing S'] [Algebra A S']
      (φ : S →ₐ[A] S') (y : MonoidAlgebra S G),
      MvPolynomial.aeval (fun a : s => (MonoidAlgebra.mapRingHom G (φ : S →+* S') y).coeff a) (P s) =
        φ (MvPolynomial.aeval (fun a : s => y.coeff a) (P s)) := by
    intro s S S' _ _ _ _ φ y
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    simp
  have indep : ∀ (s : Finset G) {S : Type} [CommRing S] [Algebra A S] (y : MonoidAlgebra S G),
      y.coeff.support ⊆ s → MvPolynomial.aeval (fun a : y.coeff.support => y.coeff a) (P _) =
        MvPolynomial.aeval (fun a : s => y.coeff a) (P s) := by
    intro s S _ _ y hy
    obtain ⟨y', h1, h2⟩ := lift_ex (A := A) y
    have e1 := nat s (MvPolynomial.aeval id) y'
    have e2 := nat y.coeff.support (MvPolynomial.aeval id) y'
    rw [h2] at e1 e2
    rw [e1, e2]
    congr 1
    exact sep I fun N => by rw [red' N _ _ h1, red' N _ _ (h1.trans hy)]
  let E : ∀ (S : Type) [CommRing S] [Algebra A S], MonoidAlgebra S G → S :=
    fun S _ _ y => MvPolynomial.aeval (fun a : y.coeff.support => y.coeff a) (P _)
  have Enat : ∀ (S S' : Type) [CommRing S] [Algebra A S] [CommRing S'] [Algebra A S']
      (φ : S →ₐ[A] S') (y : MonoidAlgebra S G), E S' (MonoidAlgebra.mapRingHom G (φ : S →+* S') y) = φ (E S y) :=
    fun S S' _ _ _ _ φ y => (indep _ _ (supp_map _ y)).trans (nat _ φ y)
  have Ered : ∀ (N : ℕ) {σ : Type} (y : MonoidAlgebra (MvPolynomial σ A) G),
      MvPolynomial.map (Ideal.Quotient.mk (I ^ N)) (E _ y) =
        (Ds N).D _ (MonoidAlgebra.mapRingHom G (MvPolynomial.map (Ideal.Quotient.mk (I ^ N))) y) :=
    fun N σ y => red' N _ y le_rfl
  have Eone : ∀ (S : Type) [CommRing S] [Algebra A S], E S 1 = 1 := by
    intro S _ _
    have h1 : E (MvPolynomial S A) 1 = 1 := sep I fun N => by simp only [Ered, map_one]
    have := Enat _ S (MvPolynomial.aeval id) 1
    rwa [h1, map_one, map_one] at this
  have Emul : ∀ (S : Type) [CommRing S] [Algebra A S] (x y), E S (x * y) = E S x * E S y := by
    intro S _ _ x y
    obtain ⟨x', -, rfl⟩ := lift_ex (A := A) x
    obtain ⟨y', -, rfl⟩ := lift_ex (A := A) y
    rw [← map_mul, Enat, Enat, Enat, ← map_mul]
    congr 1
    exact sep I fun N => by simp only [Ered, map_mul]
  have Ehom : ∀ (S : Type) [CommRing S] [Algebra A S] (b : S) (x), E S (b • x) = b ^ n * E S x := by
    intro S _ _ b x
    obtain ⟨x', -, rfl⟩ := lift_ex (A := A) x
    have h1 : E _ ((MvPolynomial.X b : MvPolynomial S A) • x') = MvPolynomial.X b ^ n * E _ x' :=
      sep I fun N => by
        rw [map_mul, map_pow, Ered, Ered, ← (Ds N).homog]
        congr 1
        ext1
        ext1
        simp
    have h2 := Enat _ S (MvPolynomial.aeval id) ((MvPolynomial.X b : MvPolynomial S A) • x')
    rw [h1, map_mul, map_pow, MvPolynomial.aeval_X, ← Enat] at h2
    refine Eq.trans ?_ h2
    congr 1
    ext g
    simp
  refine ⟨⟨fun S _ _ => ⟨⟨E S, Eone S⟩, Emul S⟩, Enat, Ehom⟩, fun N => ?_, ?_⟩
  · ext B _ _ y
    letI : Algebra A B := ((algebraMap (A ⧸ I ^ N) B).comp (Ideal.Quotient.mk (I ^ N))).toAlgebra
    have := red N _ (RingHom.id B) (fun _ => rfl) y le_rfl
    refine Eq.trans this ?_
    congr 1
    ext g
    simp
  · intro D hD
    ext B _ _ y
    have : pol D y.coeff.support = P _ := sep I fun N => by rw [hP, ← pol_map, hD]
    rw [pol_eval D _ y le_rfl, this]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.BaseChangeResidueSurjective
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem base_change_residue_surjective (O' R T : Type) [CommRing O'] [IsLocalRing O'] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [CommRing T] [Algebra O' T] [Algebra R T]
    [Module.Finite R T] (φ : T →+* ResidueField O') (hφ : ∀ a, φ (algebraMap O' T a) = residue O' a)
    (hm : ∀ r ∈ maximalIdeal R, φ (algebraMap R T r) = 0)
    (hs : ∀ x : T, ∃ a : O', x - algebraMap O' T a ∈ (maximalIdeal R).map (algebraMap R T)) :
    IsCO O' T := by
  have hJ : (maximalIdeal R).map (algebraMap R T) ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Ideal.jacobson, Submodule.mem_sInf]
    rintro P ⟨-, hP⟩
    have h1 : Ideal.comap (algebraMap R T) P = maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) P)
    rw [← Ideal.mem_comap, h1]
    exact hr
  haveI : Nontrivial T := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h2 := congrArg φ h
    rw [map_zero, map_one] at h2
    exact zero_ne_one h2
  have key : ∀ (u y : T), IsUnit u → y ∈ Ideal.jacobson (⊥ : Ideal T) → IsUnit (u + y) := by
    intro u y hu hy
    obtain ⟨v, rfl⟩ := hu
    have h3 := (Ideal.mem_jacobson_bot.mp hy) ↑v⁻¹
    have e : (v : T) + y = v * (y * ↑v⁻¹ + 1) := by
      rw [mul_add, mul_one, mul_comm y, ← mul_assoc, Units.mul_inv, one_mul, add_comm]
    rw [e]
    exact v.isUnit.mul h3
  haveI : IsLocalRing T := by
    refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
    obtain ⟨a, ha⟩ := hs x
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with h | h
    · left
      have h4 := key _ _ (h.map (algebraMap O' T)) (hJ ha)
      rwa [add_sub_cancel] at h4
    · right
      have h4 := key _ _ (h.map (algebraMap O' T)) (hJ (neg_mem ha))
      convert h4 using 1
      rw [map_sub, map_one]
      ring
  have hR : IsCL R R := by
    refine ⟨inferInstance, inferInstance, ?_, ?_⟩
    · rw [Algebra.algebraMap_self]
      infer_instance
    · infer_instance
  have hT : IsCL R T := cl_fin R R T hR
  haveI : IsNoetherianRing T := hT.noeth
  refine ⟨hT.complete, ?_, ?_⟩
  · refine ⟨fun a ha => ?_⟩
    have h5 := ha.map φ
    rw [hφ] at h5
    exact (IsLocalRing.residue_ne_zero_iff_isUnit a).mp h5.ne_zero
  · intro x
    obtain ⟨a, ha⟩ := hs x
    refine ⟨a, ?_⟩
    have h6 : (maximalIdeal R).map (algebraMap R T) ≤ maximalIdeal T := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have h7 := hu.map φ
      rw [hm r hr] at h7
      exact not_isUnit_zero h7
    exact h6 ha

theorem UpperTheory.V.CA.cl_bc :
    ∀ (O O' R : Type) [CommRing O] [IsLocalRing O] [CommRing O'] [IsLocalRing O'] [Algebra O O'] [Module.Finite O O'] [IsLocalHom (algebraMap O O')] [CommRing R] [Algebra O R] [IsCO O R], IsCO O' (TensorProduct O O' R) := by
  intro O O' R _ _ _ _ _ _ _ _ _ _
  letI : Algebra R (TensorProduct O O' R) := Algebra.TensorProduct.rightAlgebra
  have hR : ∀ r : R, algebraMap R (TensorProduct O O' R) r = 1 ⊗ₜ r := fun r => rfl
  have hL : ∀ x : O', algebraMap O' (TensorProduct O O' R) x = x ⊗ₜ 1 := fun x => rfl
  haveI : Module.Finite R (TensorProduct O O' R) := by
    let c := Algebra.TensorProduct.comm O R O'
    let e : TensorProduct O R O' →ₗ[R] TensorProduct O O' R :=
      { toFun := c
        map_add' := map_add c
        map_smul' := fun r y => by
          rw [Algebra.smul_def, Algebra.smul_def, map_mul]
          congr 1 }
    exact Module.Finite.of_surjective e c.surjective
  haveI : IsNoetherianRing R := inferInstance
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  let f : O' →ₐ[O] ResidueField O' := IsScalarTower.toAlgHom O O' (ResidueField O')
  let g : R →ₐ[O] ResidueField O' :=
    (IsScalarTower.toAlgHom O (ResidueField O) (ResidueField O')).comp (res O R)
  let φ : TensorProduct O O' R →+* ResidueField O' := (Algebra.TensorProduct.productMap f g).toRingHom
  refine base_change_residue_surjective O' R (TensorProduct O O' R) φ ?_ ?_ ?_
  · intro a
    simp [φ, f, g]
  · intro r hr
    have h1 : res O R r = 0 := (res_eq_zero_iff O R r).mpr hr
    show Algebra.TensorProduct.productMap f g (algebraMap R (TensorProduct O O' R) r) = 0
    rw [hR, Algebra.TensorProduct.productMap_apply_tmul]
    simp [g, h1]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul o r =>
      obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) r
      refine ⟨algebraMap O O' c * o, ?_⟩
      have e2 : o ⊗ₜ[O] r - algebraMap O' (TensorProduct O O' R) (algebraMap O O' c * o) =
          algebraMap O' (TensorProduct O O' R) o * algebraMap R (TensorProduct O O' R) (r - algebraMap O R c) := by
        rw [hR, hL, hL, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.tmul_sub,
          ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
      rw [e2]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hc)
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a + b, ?_⟩
      have e3 : x + y - algebraMap O' (TensorProduct O O' R) (a + b) =
          (x - algebraMap O' (TensorProduct O O' R) a) + (y - algebraMap O' (TensorProduct O O' R) b) := by
        rw [map_add (f := _)]
        ring
      rw [e3]
      exact add_mem ha hb
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CmOfRegular
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem cm_of_regular (A : Type) [CommRing A] [IsRegularLocalRing A] : ReciprocityTheory.CA.IsCM A := by
  obtain ⟨xs, hspan, hlen, hreg⟩ :=
    PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.exists_isRegular_ofList_eq_maximalIdeal A
  refine ⟨inferInstance, xs.length, hlen.symm, xs, rfl, fun r hr => ?_, hreg⟩
  rw [← hspan]
  exact Ideal.subset_span hr

theorem UpperTheory.V.CA.cl_cm :
    (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (d : ℕ), IsCM (MvPowerSeries (Fin d) O) ∧ ringKrullDim (MvPowerSeries (Fin d) O) = (d + 1 : ℕ)) ∧ ∀ (k : Type) [Field k] (d : ℕ), IsCM (MvPowerSeries (Fin d) k) ∧ ringKrullDim (MvPowerSeries (Fin d) k) = d := by
  refine ⟨fun O _ _ _ _ d => ⟨?_, ?_⟩, fun k _ d => ⟨?_, ?_⟩⟩
  · haveI : IsRegularLocalRing (MvPowerSeries (Fin d) O) :=
      GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries O (Fin d)
    exact cm_of_regular _
  · rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one,
      Nat.card_eq_fintype_card, Fintype.card_fin, add_comm]
    push_cast
    rfl
  · haveI : IsRegularLocalRing (MvPowerSeries (Fin d) k) :=
      GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin d)
    exact cm_of_regular _
  · rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CplUniq
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem cu_uniq {C R : Type} [CommRing C] [CommRing R] [Algebra C R] [IsLocalRing R] {x : Ideal C}
    (h : IsCplAt x R) {T : Type} [CommRing T] (J : Ideal T) [IsAdicComplete J T] (F G : R →+* T)
    (e : F.comp (algebraMap C R) = G.comp (algebraMap C R))
    (hF : maximalIdeal R ≤ J.comap F) (hG : maximalIdeal R ≤ J.comap G) : F = G := by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' J
  intro n r
  obtain ⟨c, hc⟩ := h.dense n r
  have h1 : F (r - algebraMap C R c) ∈ J ^ n :=
    Ideal.le_comap_pow F n (Ideal.pow_right_mono hF n hc)
  have h2 : G (r - algebraMap C R c) ∈ J ^ n :=
    Ideal.le_comap_pow G n (Ideal.pow_right_mono hG n hc)
  have h3 : F (algebraMap C R c) = G (algebraMap C R c) := RingHom.congr_fun e c
  rw [Ideal.Quotient.eq]
  have := sub_mem h1 h2
  rw [map_sub, map_sub, h3] at this
  simpa using this

private theorem cu_ex {C R : Type} [CommRing C] [CommRing R] [Algebra C R] [IsLocalRing R] {x : Ideal C}
    (h : IsCplAt x R) {T : Type} [CommRing T] (J : Ideal T) [IsAdicComplete J T] (f : C →+* T)
    (hf : x ≤ J.comap f) :
    ∃ F : R →+* T, F.comp (algebraMap C R) = f ∧ maximalIdeal R ≤ J.comap F :=
  _root_.UpperTheory.Reformulated.B.LevelOfCongruence.cu_ex h J f hf

private theorem cu_le {C R : Type} [CommRing C] [CommRing R] [Algebra C R] [IsLocalRing R] {x : Ideal C}
    (h : IsCplAt x R) : x ≤ (maximalIdeal R).comap (algebraMap C R) := by
  have := h.comap_pow 1
  rw [pow_one, pow_one] at this
  exact this.ge

private theorem cu_map {C R : Type} [CommRing C] [CommRing R] [Algebra C R] [IsLocalRing R] {x : Ideal C}
    (h : IsCplAt x R) : x.map (algebraMap C R) = maximalIdeal R := by
  haveI := h.noeth
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 (cu_le h)) ?_
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal R) (IsNoetherian.noetherian _)
    (maximalIdeal_le_jacobson _) fun r hr => ?_
  obtain ⟨c, hc⟩ := h.dense 2 r
  have h1 : algebraMap C R c ∈ maximalIdeal R := by
    have := sub_mem hr (Ideal.pow_le_self two_ne_zero hc)
    simpa using this
  have h2 : c ∈ x := by
    have := h.comap_pow 1
    rw [pow_one, pow_one] at this
    rw [← this]; exact h1
  have h3 : r = algebraMap C R c + (r - algebraMap C R c) := by ring
  rw [h3]
  refine Submodule.add_mem_sup (Ideal.mem_map_of_mem _ h2) ?_
  rw [smul_eq_mul, ← pow_two]
  exact hc

private theorem cu_equiv {C R S : Type} [CommRing C] [CommRing R] [Algebra C R] [IsLocalRing R]
    [CommRing S] [Algebra C S] [IsLocalRing S] {x : Ideal C}
    (h : IsCplAt x R) (h' : IsCplAt x S) : Nonempty (R ≃ₐ[C] S) := by
  haveI := h.complete
  haveI := h'.complete
  obtain ⟨F, hF1, hF2⟩ := cu_ex h (maximalIdeal S) (algebraMap C S) (cu_le h')
  obtain ⟨G, hG1, hG2⟩ := cu_ex h' (maximalIdeal R) (algebraMap C R) (cu_le h)
  have e1 : G.comp F = RingHom.id R :=
    cu_uniq h (maximalIdeal R) _ _ (by rw [RingHom.comp_assoc, hF1, hG1, RingHom.id_comp])
      (fun r hr => hG2 (hF2 hr)) (fun r hr => hr)
  have e2 : F.comp G = RingHom.id S :=
    cu_uniq h' (maximalIdeal S) _ _ (by rw [RingHom.comp_assoc, hG1, hF1, RingHom.id_comp])
      (fun r hr => hF2 (hG2 hr)) (fun r hr => hr)
  exact ⟨AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom F G e2 e1) fun c => RingHom.congr_fun hF1 c⟩

theorem UpperTheory.V.CA.cpl_uniq :
    ∀ {C R : Type} [CommRing C] [IsNoetherianRing C] [CommRing R] [Algebra C R] [IsLocalRing R] (x : Ideal C) [x.IsMaximal], IsCplAt x R → (∀ (T : Type) [CommRing T] (J : Ideal T) [IsAdicComplete J T] (f : C →+* T), x ≤ J.comap f → ∃! F : R →+* T, F.comp (algebraMap C R) = f ∧ maximalIdeal R ≤ J.comap F) ∧ Nonempty (R ≃ₐ[C] Cpl x) ∧ x.map (algebraMap C R) = maximalIdeal R := by
  intro C R _ _ _ _ _ x _ h
  refine ⟨fun T _ J _ f hf => ?_, ?_, cu_map h⟩
  · obtain ⟨F, hF⟩ := cu_ex h J f hf
    exact ⟨F, hF, fun G hG => cu_uniq h J G F (hG.1.trans hF.1.symm) hG.2 hF.2⟩
  · obtain ⟨_, h'⟩ := cpl_is C x
    exact cu_equiv h h'
end

