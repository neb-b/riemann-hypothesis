module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0004
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.Data.Finset.NoncommProd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DProd
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section

variable {n : ℕ} {A ι : Type} [CommRing A] [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ i, Ring (E i)]
  [∀ i, Algebra A (E i)]

private theorem UpperTheory.V.CA.prod_piRight_apply (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] (∀ i, E i)) (i : ι) :
    Algebra.TensorProduct.piRight A S S E y i =
      Algebra.TensorProduct.map (AlgHom.id S S) (Pi.evalAlgHom A E i) y := by
  induction y with
  | tmul s y => simp
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]

private theorem UpperTheory.V.CA.prod_piRight_map (S T : Type) [CommRing S] [Algebra A S] [CommRing T] [Algebra A T]
    (f : S →ₐ[A] T) (y : S ⊗[A] (∀ i, E i)) (i : ι) :
    Algebra.TensorProduct.piRight A T T E (Algebra.TensorProduct.map f (AlgHom.id A _) y) i =
      Algebra.TensorProduct.map f (AlgHom.id A _) (Algebra.TensorProduct.piRight A S S E y i) := by
  induction y with
  | tmul s y => simp
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]

private theorem UpperTheory.V.CA.prod_single_smul (S : Type) [CommRing S] [Algebra A S] (b : S) (i : ι) :
    (Algebra.TensorProduct.piRight A S S E).symm (Pi.mulSingle i (b • (1 : S ⊗[A] E i))) =
      1 + (b - 1) ⊗ₜ[A] (Pi.single i 1 : ∀ i, E i) := by
  rw [AlgEquiv.symm_apply_eq]
  funext j
  rw [map_add (f := _), map_one, Pi.add_apply, Pi.one_apply, Algebra.TensorProduct.piRight_tmul]
  by_cases h : j = i
  · subst h
    simp only [Pi.mulSingle_eq_same, Pi.single_eq_same]
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      ← TensorProduct.add_tmul, add_sub_cancel]
  · simp [Pi.mulSingle_eq_of_ne h, Pi.single_eq_of_ne h]

private noncomputable def UpperTheory.V.CA.prodFactor (D : Det n A (∀ i, E i)) (i : ι) (r : ℕ)
    (hr : D.D A[X] (1 + X ⊗ₜ (Pi.single i 1 : ∀ i, E i)) = (1 + X) ^ r) : Det r A (E i) where
  D S _ _ := (D.D S).comp ((Algebra.TensorProduct.piRight A S S E).symm.toAlgHom.toMonoidHom.comp
    (MonoidHom.mulSingle (fun j => S ⊗[A] E j) i))
  nat S T _ _ _ _ f x := by
    change D.D T ((Algebra.TensorProduct.piRight A T T E).symm (Pi.mulSingle i _)) =
      f (D.D S ((Algebra.TensorProduct.piRight A S S E).symm (Pi.mulSingle i x)))
    rw [← D.nat]
    congr 1
    rw [AlgEquiv.symm_apply_eq]
    funext j
    rw [prod_piRight_map, AlgEquiv.apply_symm_apply]
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  homog S _ _ b x := by
    have h1 : b • x = (b • (1 : S ⊗[A] E i)) * x := by rw [smul_mul_assoc, one_mul]
    rw [h1, map_mul]
    congr 1
    change D.D S ((Algebra.TensorProduct.piRight A S S E).symm (Pi.mulSingle i _)) = _
    rw [prod_single_smul]
    have h2 := D.nat A[X] S (Polynomial.aeval (b - 1)) (1 + X ⊗ₜ (Pi.single i 1 : ∀ i, E i))
    rw [hr] at h2
    simpa using h2

end

theorem UpperTheory.V.CA.d_prod :
    ∀ {n : ℕ} {A ι : Type} [CommRing A] [IsLocalRing A] [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ i, Ring (E i)] [∀ i, Algebra A (E i)] (D : Det n A (∀ i, E i)), ∃ (m : ι → ℕ) (Ds : ∀ i, Det (m i) A (E i)), ∑ i, m i = n ∧ ∀ (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] (∀ i, E i)), D.D S y = ∏ i, ((Ds i).pull (Pi.evalAlgHom A E i)).D S y := by
  intro n A ι _ _ _ _ E _ _ D
  have hid : ∀ i, IsIdempotentElem (Pi.single i 1 : ∀ i, E i) := by
    intro i
    show _ * _ = _
    rw [← Pi.single_mul, one_mul]
  choose r hrle hr using fun i => d_idem_rank D (Pi.single i 1 : ∀ i, E i) (hid i)
  have hpull : ∀ (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] (∀ i, E i)) (i : ι),
      ((prodFactor E D i (r i) (hr i)).pull (Pi.evalAlgHom A E i)).D S y
        = D.D S ((Algebra.TensorProduct.piRight A S S E).symm
            (Pi.mulSingle i (Algebra.TensorProduct.piRight A S S E y i))) := by
    intro S _ _ y i
    rw [prod_piRight_apply]
    rfl
  have hprod : ∀ (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] (∀ i, E i)),
      D.D S y = ∏ i, ((prodFactor E D i (r i) (hr i)).pull (Pi.evalAlgHom A E i)).D S y := by
    intro S _ _ y
    simp only [hpull]
    let g : (∀ j, S ⊗[A] E j) →* S :=
      (D.D S).comp (Algebra.TensorProduct.piRight A S S E).symm.toAlgHom.toMonoidHom
    have hg : ∀ x, g x = D.D S ((Algebra.TensorProduct.piRight A S S E).symm x) := fun x => rfl
    calc D.D S y = g (Algebra.TensorProduct.piRight A S S E y) := by
          rw [hg, AlgEquiv.symm_apply_apply]
      _ = g (Finset.univ.noncommProd
            (fun i => Pi.mulSingle i (Algebra.TensorProduct.piRight A S S E y i))
            fun i _ j _ _ => Pi.mulSingle_apply_commute _ i j) := by
          rw [Finset.noncommProd_mulSingle]
      _ = ∏ i, g (Pi.mulSingle i (Algebra.TensorProduct.piRight A S S E y i)) :=
          (Finset.map_noncommProd _ _ _ g).trans (Finset.noncommProd_eq_prod _ _)
      _ = _ := by simp only [hg]
  refine ⟨r, fun i => prodFactor E D i (r i) (hr i), ?_, hprod⟩
  have h := hprod A[X] ((X : A[X]) • 1)
  simp only [Det.homog, map_one, mul_one] at h
  rw [Finset.prod_pow_eq_pow_sum] at h
  have h' := congrArg Polynomial.natDegree h
  simpa [Polynomial.natDegree_X_pow] using h'.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FNil
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem idempotent_sandwich_list_prod_eq_of_kernel {k E : Type} [Field k] [Ring E] [Algebra k E] {n : ℕ}
    (π : E →ₐ[k] (Fin n → k)) (e g g' : E) (hg : g = e + g')
    (hJ : ∀ z, π z = 0 → e * z * e = 0) (t : List E) :
    ∀ a, π a = 0 → e * a * (g * (t.map (· * g)).prod) = e * a * (g' * (t.map (· * g')).prod) := by
  induction t with
  | nil =>
    intro a ha
    simp only [List.map_nil, List.prod_nil, mul_one]
    rw [hg, mul_add, hJ a ha, zero_add]
  | cons z s ih =>
    intro a ha
    simp only [List.map_cons, List.prod_cons]
    have hmem : π (a * g' * z) = 0 := by simp [map_mul, ha]
    calc e * a * (g * (z * g * (s.map (· * g)).prod))
        = (e * a * g) * (z * (g * (s.map (· * g)).prod)) := by simp only [mul_assoc]
      _ = (e * a * e + e * a * g') * (z * (g * (s.map (· * g)).prod)) := by rw [← mul_add, ← hg]
      _ = e * (a * g' * z) * (g * (s.map (· * g)).prod) := by
          rw [hJ a ha, zero_add]; simp only [mul_assoc]
      _ = e * (a * g' * z) * (g' * (s.map (· * g')).prod) := ih _ hmem
      _ = e * a * (g' * (z * g' * (s.map (· * g')).prod)) := by simp only [mul_assoc]

theorem UpperTheory.V.CA.f_nil :
    ∀ {n : ℕ} {k E : Type} [Field k] [Ring E] [Algebra k E] (e : Fin n → E) (π : E →ₐ[k] (Fin n → k)), CompleteOrthogonalIdempotents e → (∀ i, π (e i) = Pi.single i 1) → (∀ i x, ∃ a : k, e i * x * e i = a • e i) → (∀ x, π x = 0 ↔ ∀ i, e i * x * e i = 0) ∧ ∀ x : Fin n → E, (∀ s, π (x s) = 0) → (List.ofFn x).prod = 0 := by
  intro n k E _ _ _ e π he hπ hsc
  have hJ : ∀ z, π z = 0 → ∀ i, e i * z * e i = 0 := by
    intro z hz i
    obtain ⟨a, ha⟩ := hsc i z
    have ha0 : a = 0 := by
      simpa [map_mul, hz, hπ] using (congrFun (congrArg π ha) i).symm
    rw [ha, ha0, zero_smul]
  refine ⟨fun x => ⟨fun hz i => hJ x hz i, fun h => ?_⟩, fun x hx => ?_⟩
  · funext i
    have h2 := congrFun (congrArg π (h i)) i
    simpa [map_mul, hπ] using h2
  · obtain ⟨F, hF⟩ : ∃ F : Finset (Fin n) → E, ∀ T, F T = ∑ i ∈ T, e i := ⟨_, fun _ => rfl⟩
    have D : ∀ (m : ℕ) (T : Finset (Fin n)), T.card = m → ∀ t : List E, (∀ y ∈ t, π y = 0) →
        m ≤ t.length → F T * (t.map (· * F T)).prod = 0 := by
      intro m
      induction m with
      | zero =>
        intro T hT t _ _
        rw [Finset.card_eq_zero] at hT
        subst hT
        simp [hF]
      | succ m ih =>
        intro T hT t ht hlen
        cases t with
        | nil => simp at hlen
        | cons y s =>
          rw [show F T * ((y :: s).map (· * F T)).prod =
              ∑ i ∈ T, e i * ((y :: s).map (· * F T)).prod by rw [hF T, Finset.sum_mul]]
          apply Finset.sum_eq_zero
          intro i hi
          simp only [List.map_cons, List.prod_cons]
          rw [show e i * (y * F T * (s.map (· * F T)).prod) =
              e i * y * (F T * (s.map (· * F T)).prod) by simp only [mul_assoc]]
          have hsplit : F T = e i + F (T.erase i) := by
            rw [hF, hF, Finset.add_sum_erase T e hi]
          rw [idempotent_sandwich_list_prod_eq_of_kernel π (e i) (F T) (F (T.erase i)) hsplit (fun z hz => hJ z hz i) s y
            (ht y (by simp))]
          rw [ih (T.erase i) (by rw [Finset.card_erase_of_mem hi, hT]; rfl) s
            (fun z hz => ht z (by simp [hz])) (by simp at hlen; omega), mul_zero]
    have key := D n Finset.univ (by simp) (List.ofFn x)
      (by
        intro y hy
        rw [List.mem_ofFn] at hy
        obtain ⟨s, rfl⟩ := hy
        exact hx s)
      (by simp)
    have h1 : F Finset.univ = 1 := by rw [hF]; exact he.complete
    rw [h1, one_mul, show (fun y : E => y * 1) = id from funext mul_one, List.map_id] at key
    exact key
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GammaOneGammaZeroHomogeneousCocyclesFinite
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem module_finite_z1_padicInt (l : ℕ) [Fact l.Prime] {k G : Type} [Field k] [Finite k] [CharP k l] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (χ ψ : G →* kˣ) (hΦ : PhiCond (Γ := G) l)
    (hχ : IsOpen (χ.ker : Set G)) (hψ : IsOpen (ψ.ker : Set G)) : Finite (Z1 χ ψ) := by
  classical
  letI := ZMod.algebra k l
  haveI : Module.Finite (ZMod l) k := Module.Finite.of_finite
  let N : Subgroup G := χ.ker ⊓ ψ.ker
  have hNo : IsOpen (N : Set G) := by
    show IsOpen ((χ.ker ⊓ ψ.ker : Subgroup G) : Set G)
    rw [Subgroup.coe_inf]
    exact hχ.inter hψ
  haveI : Finite (G ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNo
  haveI := hΦ N hNo
  let b := Module.finBasis (ZMod l) k
  have mem : ∀ a ∈ Z1 χ ψ, IsLocallyConstant a ∧
      ∀ g h : G, a (g * h) = (χ g : k) * a h + a g * (ψ h : k) := fun a ha => ha
  have hadd : ∀ a ∈ Z1 χ ψ, ∀ x y : N, a ((x : G) * (y : G)) = a x + a y := by
    intro a ha x y
    have hx : χ (x : G) = 1 := MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp x.2).1
    have hy : ψ (y : G) = 1 := MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp y.2).2
    rw [(mem a ha).2, hx, hy]
    simp [add_comm]
  let φ : ∀ a ∈ Z1 χ ψ, Fin (Module.finrank (ZMod l) k) → (N →* Multiplicative (ZMod l)) :=
    fun a ha i => MonoidHom.mk' (fun x => Multiplicative.ofAdd (b.repr (a x) i)) (by
      intro x y
      simp [hadd a ha x y, ofAdd_add])
  have hφo : ∀ a (ha : a ∈ Z1 χ ψ) i, IsOpen ((φ a ha i).ker : Set N) := by
    intro a ha i
    have hlc : IsLocallyConstant (fun x : N => b.repr (a x) i) :=
      ((mem a ha).1.comp_continuous continuous_subtype_val).comp (fun y => b.repr y i)
    have e : ((φ a ha i).ker : Set N) = {x | (fun x : N => b.repr (a x) i) x = 0} := by
      ext x
      simp [φ, MonoidHom.mem_ker]
    rw [e]
    exact hlc.isOpen_fiber 0
  let F : Z1 χ ψ → (G ⧸ N → k) ×
      (Fin (Module.finrank (ZMod l) k) → {φ : N →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set N)}) :=
    fun a => (fun q => (a : G → k) q.out, fun i => ⟨φ a a.2 i, hφo a a.2 i⟩)
  refine Finite.of_injective F ?_
  rintro ⟨a, ha⟩ ⟨a', ha'⟩ h
  simp only [F, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hN' : ∀ x : N, a x = a' x := by
    intro x
    apply b.repr.injective
    ext i
    exact congrArg (fun f => Multiplicative.toAdd ((f i).1 x)) h2
  apply Subtype.ext
  funext g
  obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N g
  have e1 : a (QuotientGroup.mk g : G ⧸ N).out = a' (QuotientGroup.mk g : G ⧸ N).out := congrFun h1 _
  have hg : g = (QuotientGroup.mk g : G ⧸ N).out * ((n⁻¹ : N) : G) := by
    rw [hn]; simp [mul_assoc]
  show a g = a' g
  rw [hg, (mem a ha).2, (mem a' ha').2, hN' n⁻¹, e1]

theorem UpperTheory.V.CA.exists_multFree_of_phiCond_of_injective_chars :
    ∀ (l : ℕ) [Fact l.Prime] {n : ℕ} {k G : Type} [Field k] [Finite k] [CharP k l] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (χ : Fin n → G →* kˣ), PhiCond (Γ := G) l → (∀ i, IsOpen ((χ i).ker : Set G)) → Function.Injective χ → ∃ h, MultFree χ h := by
  intro l _ n k G _ _ _ _ _ _ _ _ χ hΦ hopen hinj
  refine ⟨∑ i, ∑ j, Module.finrank k (Z1 (χ i) (χ j)), hopen, hinj, fun i j _ => ?_⟩
  haveI := module_finite_z1_padicInt l (χ i) (χ j) hΦ (hopen i) (hopen j)
  refine ⟨inferInstance, ?_⟩
  calc Module.finrank k (Z1 (χ i) (χ j)) ≤ ∑ j', Module.finrank k (Z1 (χ i) (χ j')) :=
        Finset.single_le_sum (f := fun j' => Module.finrank k (Z1 (χ i) (χ j')))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', Module.finrank k (Z1 (χ i') (χ j')) :=
        Finset.single_le_sum (f := fun i' => ∑ j', Module.finrank k (Z1 (χ i') (χ j')))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HomTwo
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem hom_two {n : ℕ} {A : Type} [CommRing A] (P : MvPolynomial (Fin 2) A) (hP : P.IsHomogeneous n) :
    ∃ c : ℕ → A, ∀ (S : Type) [CommRing S] [Algebra A S] (s t : S),
      MvPolynomial.aeval ![s, t] P = ∑ i ∈ Finset.range (n + 1), algebraMap A S (c i) * s ^ (n - i) * t ^ i := by
  classical
  have hd : ∀ d ∈ P.support, d 0 + d 1 = n := fun d hd => by
    have h := hP (MvPolynomial.mem_support_iff.1 hd)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
    simpa [Fin.sum_univ_two] using h
  refine ⟨fun i => ∑ d ∈ P.support with d 1 = i, P.coeff d, fun S _ _ s t => ?_⟩
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
    ← Finset.sum_fiberwise_of_maps_to (t := Finset.range (n + 1)) (g := fun d => d 1)
      (fun d h => by have := hd d h; simp only [Finset.mem_range]; omega)]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d h => ?_
  rw [Finset.mem_filter] at h
  have h0 : d 0 = n - i := by have := hd d h.1; have := h.2; omega
  simp [Fin.prod_univ_two, h0, h.2, mul_assoc]

private theorem lam_two {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (x : E)
    (S : Type) [CommRing S] [Algebra A S] (s t : S) :
    D.D S (s ⊗ₜ 1 + t ⊗ₜ x) = ∑ i ∈ Finset.range (n + 1), algebraMap A S (D.lam i x) * s ^ (n - i) * t ^ i := by
  obtain ⟨h1, h2⟩ := d_poly D ![1, x]
  obtain ⟨c, hc⟩ := hom_two _ h1
  have key : ∀ (S : Type) [CommRing S] [Algebra A S] (s t : S),
      D.D S (s ⊗ₜ 1 + t ⊗ₜ x) = ∑ i ∈ Finset.range (n + 1), algebraMap A S (c i) * s ^ (n - i) * t ^ i := by
    intro S _ _ s t
    rw [← hc, ← h2]
    simp [Fin.sum_univ_two]
  have hl : ∀ j ∈ Finset.range (n + 1), D.lam j x = c j := by
    intro j hj
    have hj' : j ≤ n := by simpa [Nat.lt_succ_iff] using hj
    have hchi : D.chi x = ∑ i ∈ Finset.range (n + 1), C ((-1) ^ i * c i) * X ^ (n - i) := by
      rw [Det.chi, sub_eq_add_neg, ← neg_tmul, key]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_mul, map_pow, map_neg,
        map_one]
      ring
    rw [Det.lam, hchi, finsetSum_coeff, Finset.sum_eq_single j]
    · rw [coeff_C_mul_X_pow, if_pos rfl, ← mul_assoc, ← mul_pow]; simp
    · intro i hi hij
      have : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
      rw [coeff_C_mul_X_pow, if_neg (by omega)]
    · intro h; exact absurd hj h
  rw [key]
  exact Finset.sum_congr rfl fun i hi => by rw [hl i hi]

theorem UpperTheory.V.CA.d_chi :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (x : E), D.lam 0 x = 1 ∧ D.chi x = ∑ i ∈ Finset.range (n + 1), C ((-1) ^ i * D.lam i x) * X ^ (n - i) ∧ D.D A[X] (1 + X ⊗ₜ x) = ∑ i ∈ Finset.range (n + 1), C (D.lam i x) * X ^ i ∧ D.lam n x = D.val x ∧ (D.chi x).Monic ∧ (D.chi x).natDegree ≤ n ∧ ∀ (a : A) (i : ℕ), i ≤ n → D.lam i (a • x) = a ^ i * D.lam i x := by
  intro n A E _ _ _ D x
  have h0 : D.lam 0 x = 1 := by
    have h := lam_two D x A 1 0
    rw [zero_tmul, add_zero, ← Algebra.TensorProduct.one_def, map_one, Finset.sum_range_succ'] at h
    simpa using h.symm
  have hchi : D.chi x = ∑ i ∈ Finset.range (n + 1), C ((-1) ^ i * D.lam i x) * X ^ (n - i) := by
    conv_lhs => rw [Det.chi, sub_eq_add_neg, ← neg_tmul, lam_two]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_mul, map_pow, map_neg,
      map_one]
    ring
  have h1 : ∀ y : E, D.D A[X] (1 + X ⊗ₜ y) = ∑ i ∈ Finset.range (n + 1), C (D.lam i y) * X ^ i := by
    intro y
    rw [Algebra.TensorProduct.one_def, lam_two]
    simp
  have hdeg : (D.chi x).natDegree ≤ n := by
    rw [hchi]
    refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le _ _)
  refine ⟨h0, hchi, h1 x, ?_, ?_, hdeg, ?_⟩
  · have h := lam_two D x A 0 1
    rw [zero_tmul, zero_add, Finset.sum_range_succ, Finset.sum_eq_zero (fun i hi => by
      have : n - i ≠ 0 := by rw [Finset.mem_range] at hi; omega
      simp [this])] at h
    change _ = D.D A (1 ⊗ₜ x)
    rw [h]; simp
  · refine monic_of_natDegree_le_of_coeff_eq_one n hdeg ?_
    simpa [Det.lam] using h0
  · intro a j hj
    have h := h1 (a • x)
    rw [← smul_tmul, Algebra.TensorProduct.one_def, lam_two] at h
    have h' : ∑ i ∈ Finset.range (n + 1), C (a ^ i * D.lam i x) * X ^ i =
        ∑ i ∈ Finset.range (n + 1), C (D.lam i (a • x)) * X ^ i := by
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_mul, map_pow,
        smul_eq_C_mul]
      ring
    have h2 := congrArg (fun p => p.coeff j) h'
    simp only [finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff, hj,
      if_true] at h2
    exact h2.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.PairMap
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem adic_map {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {Γ : Type} [TopologicalSpace Γ] {a : Γ → R}
    (ha : AdicCont (maximalIdeal R) a) : AdicCont (maximalIdeal R') fun g => f (a g) := fun N => by
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show f y ∈ maximalIdeal R'
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hy
  exact (ha N).comp (Ideal.quotientMap _ (f : R →+* R') hle)

private theorem star_single {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (g : F.G₀) :
    F.star O R n (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single (F.conj g)⁻¹ ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R) := by
  simp only [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, one_smul]
  rfl

theorem UpperTheory.V.CA.pair_map :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] [Algebra ℤ_[l] O] {n : ℕ} (r : Resid F O n) {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (p : Pair r R) (f : R →ₐ[O] R'), ∃ p' : Pair r R', p.Maps (f : R →+* R') p'.D p'.ψ := by
  intro l _ F O _ _ _ _ _ _ _ n r R R' _ _ _ _ _ _ p f
  have hl : ∀ i y, (p.D.map (f : R →+* R')).lam i (MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') y) = f (p.D.lam i y) :=
    fun i y => ((d_gmap p.D).2.2.1 (f : R →+* R') y).2 i
  have h1 : ∀ g : F.G₀, MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single g 1 := fun g => by rw [MonoidAlgebra.mapRingHom_single, map_one]
  refine ⟨{ D := p.D.map (f : R →+* R'), ψ := fun v i => pushCh (f : R →+* R') (p.ψ v i),
            cont := ?_, red := ?_, psi := ?_, P := ?_, Ord := ?_, I := ?_ }, rfl, fun _ _ => rfl⟩
  · intro i
    have := adic_map f (p.cont i)
    simpa only [← hl, h1] using this
  · rw [(d_gmap p.D).2.1, ← p.red]
    congr 1
    ext x
    exact res_map f x
  · intro v i
    refine ⟨adic_map f (p.psi v i).cont, fun g => (res_map f _).trans ((p.psi v i).red g), fun g => ?_⟩
    change f (p.ψ v i g : R) = _
    rw [(p.psi v i).mu g, f.commutes]
  · intro i g
    have hs : F.star O R' n (MonoidAlgebra.single g 1) =
        MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') (F.star O R n (MonoidAlgebra.single g 1)) := by
      rw [star_single, star_single, MonoidAlgebra.mapRingHom_single]
      congr 1
      have he : F.eps O R' g = Units.map ((f : R →+* R') : R →* R') (F.eps O R g) :=
        Units.ext (f.commutes _).symm
      rw [he, ← map_zpow]
      rfl
    rw [hs, hl, p.P, ← hl, h1]
  · intro v g h
    have ho : MonoidAlgebra.single h 1 * F.oEl v (fun i => pushCh (f : R →+* R') (p.ψ v i)) g =
        MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') (MonoidAlgebra.single h 1 * F.oEl v (p.ψ v) g) := by
      rw [map_mul, h1, GFrame.oEl, GFrame.oEl, map_list_prod, List.map_ofFn]
      congr 3
      funext i
      simp only [Function.comp_apply, map_sub, MonoidAlgebra.mapRingHom_single, map_one]
      rfl
    have := p.Ord v g h
    rw [GDet.tr] at this ⊢
    rw [ho, hl, this, map_zero]
  · intro u g hg h
    have ho : (MonoidAlgebra.single h 1 * (MonoidAlgebra.single g 1 - 1) : MonoidAlgebra R' F.G₀) =
        MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') (MonoidAlgebra.single h 1 * (MonoidAlgebra.single g 1 - 1)) := by
      rw [map_mul, map_sub, h1, h1, map_one]
    have := p.I u g hg h
    rw [GDet.tr] at this ⊢
    rw [ho, hl, this, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UPoly
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem aeval_mul_homog {n : ℕ} {A G S : Type} [CommRing A] [CommRing S] [Algebra A S]
    {P : MvPolynomial G A} (hP : P.IsHomogeneous n) (b : S) (x : G → S) :
    MvPolynomial.aeval (fun g => b * x g) P = b ^ n * MvPolynomial.aeval x P :=
  _root_.UpperTheory.Reformulated.B.Qk4.aeval_mul_homog hP b x

theorem UpperTheory.V.CA.u_poly :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] [Fintype G] [DecidableEq G] (P : MvPolynomial G A), P.IsHomogeneous n → MvPolynomial.eval (Pi.single 1 1) P = 1 → MvPolynomial.aeval (fun g : G => ∑ a : G, (MvPolynomial.X (Sum.inl a) * MvPolynomial.X (Sum.inr (a⁻¹ * g)) : MvPolynomial (G ⊕ G) A)) P = MvPolynomial.rename Sum.inl P * MvPolynomial.rename Sum.inr P → ∃ D : GDet n A G, ∀ (S : Type) [CommRing S] [Algebra A S] (y : MonoidAlgebra S G), D.D S y = MvPolynomial.aeval (fun g => y.coeff g) P := by
  intro n A G _ _ _ _ P hP h1 hm
  refine ⟨⟨fun S _ _ => ⟨⟨fun y => MvPolynomial.aeval (fun g => y.coeff g) P, ?_⟩, ?_⟩, ?_, ?_⟩, fun S _ _ y => rfl⟩
  · have h : (fun g => (1 : MonoidAlgebra S G).coeff g) =
        fun g => Algebra.ofId A S ((Pi.single 1 1 : G → A) g) := by
      funext g
      by_cases hg : g = 1
      · subst hg; simp [MonoidAlgebra.one_def]
      · simp [MonoidAlgebra.one_def, hg]
    rw [h, ← MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_eq_eval, h1, map_one]
  · intro x y
    have h := congrArg (MvPolynomial.aeval (R := A) (Sum.elim (fun g => x.coeff g) (fun g => y.coeff g))) hm
    rw [map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_rename, MvPolynomial.comp_aeval_apply] at h
    refine Eq.trans ?_ h
    change MvPolynomial.aeval _ P = _
    congr 2
    funext g
    rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype] <;> simp
  · intro S T _ _ _ _ f x
    change MvPolynomial.aeval _ P = f (MvPolynomial.aeval _ P)
    rw [MvPolynomial.comp_aeval_apply]
    congr 2
  · intro S _ _ b x
    change MvPolynomial.aeval _ P = b ^ n * (MvPolynomial.aeval _ P)
    rw [← aeval_mul_homog hP]
    congr 2
end

