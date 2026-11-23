module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.ChiApi
section
open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.chiApi :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (y : MonoidAlgebra A G),
    D.lam 0 y = 1 ∧ D.lam n y = D.D A y ∧ (D.chi y).Monic ∧ (D.chi y).natDegree ≤ n ∧
    D.chi y = ∑ i ∈ Finset.range (n + 1), C ((-1) ^ i * D.lam i y) * X ^ (n - i) := by
  intro n A G _ _ D y
  have hsum : D.chi y = ∑ i ∈ Finset.range (n + 1), C ((-1) ^ i * D.lam i y) * X ^ (n - i) := by
    have key := UpperTheory.V.AlgebraTools.Det.expand D y (Polynomial A) X (-1)
    have h1 : MonoidAlgebra.single 1 (X : Polynomial A) +
        (-1 : Polynomial A) • (MonoidAlgebra.mapRingHom G (algebraMap A (Polynomial A))) y =
        MonoidAlgebra.single 1 X - (MonoidAlgebra.mapRingHom G C) y := by
      rw [neg_one_smul, ← sub_eq_add_neg, Polynomial.algebraMap_eq]
    rw [h1] at key
    unfold UpperTheory.V.W.GDet.chi
    rw [key]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.algebraMap_eq, C_mul, C_pow, C_neg, C_1]
    ring
  have h0 : D.lam 0 y = 1 := by
    have key := UpperTheory.V.AlgebraTools.Det.expand D y A 1 0
    rw [zero_smul, add_zero, ← MonoidAlgebra.one_def, map_one] at key
    rw [Finset.sum_eq_single 0] at key
    · simpa using key.symm
    · intro b _ hb
      simp [zero_pow hb]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h
  have hn : D.lam n y = D.D A y := by
    have key := UpperTheory.V.AlgebraTools.Det.expand D y A 0 1
    rw [Finset.sum_eq_single n] at key
    · simp only [MonoidAlgebra.single_zero, zero_add, one_smul, Nat.sub_self, pow_zero, one_pow,
        mul_one, Algebra.algebraMap_self, RingHom.id_apply] at key
      rw [← key]
      congr 1
      ext g
      simp [MonoidAlgebra.mapRingHom]
    · intro b hb hbn
      have : n - b ≠ 0 := by
        have := Finset.mem_range.mp hb
        omega
      simp [zero_pow this]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h
  have hdeg : (D.chi y).natDegree ≤ n := by
    rw [hsum]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    omega
  have hcoeff : (D.chi y).coeff n = 1 := by
    rw [hsum, Polynomial.finsetSum_coeff, Finset.sum_eq_single 0]
    · simp [h0]
    · intro b hb hb0
      have : n ≠ n - b := by
        have := Finset.mem_range.mp hb
        omega
      rw [Polynomial.coeff_C_mul_X_pow, if_neg this]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h
  exact ⟨h0, hn, Polynomial.monic_of_natDegree_le_of_coeff_eq_one n hdeg hcoeff, hdeg, hsum⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Descend
section
open Polynomial UpperTheory.V.W

private theorem exists_isCompact_preimage_eq_of_isLimit_of_isAffineHom {n : ℕ} {A G : Type} [CommRing A] [Group G] {A' : Type} [CommRing A']
    (ι : A →+* A') (D' : GDet n A' G)
    (hc : ∀ (m : ℕ) (g : Fin m → G) (β : Fin m →₀ ℕ),
      AddMonoidAlgebra.coeff (D'.D (MvPolynomial (Fin m) A') (GDet.gen fun j => MonoidAlgebra.single (g j) 1)) β ∈ ι.range)
    (σ : Type) (x : MonoidAlgebra (MvPolynomial σ A) G) :
    D'.D (MvPolynomial σ A') (MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) x) ∈ Set.range (MvPolynomial.map ι) := by
  obtain ⟨m, g, b, rfl⟩ := UpperTheory.V.AlgebraTools.Det.genSpan (A := A) (G := G) (MvPolynomial σ A) x
  have hP : D'.D (MvPolynomial (Fin m) A') (GDet.gen fun j => MonoidAlgebra.single (g j) 1) ∈ Set.range (MvPolynomial.map ι) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc'
    obtain ⟨β, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc'
    exact hc m g β
  obtain ⟨Q, hQ⟩ := hP
  have key := UpperTheory.V.AlgebraTools.Det.genEval D' (MvPolynomial σ A') m (fun j => MonoidAlgebra.single (g j) 1) (fun j => MvPolynomial.map ι (b j))
  refine ⟨MvPolynomial.aeval b Q, ?_⟩
  have hx : MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) (∑ j, b j • MonoidAlgebra.mapRingHom G (algebraMap A (MvPolynomial σ A)) (MonoidAlgebra.single (g j) 1)) = ∑ j, (MvPolynomial.map ι (b j)) • MonoidAlgebra.mapRingHom G (algebraMap A' (MvPolynomial σ A')) (MonoidAlgebra.single (g j) 1) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, MonoidAlgebra.mapRingHom_single]
  rw [hx, key, ← hQ, MvPolynomial.map_aeval]
  simp [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  rw [MvPolynomial.bind₁, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  rfl

private theorem mapRingHom_gdet_gen_single_eq_gen_single {A G : Type} [CommRing A] [Group G] {A' : Type} [CommRing A'] (ι : A →+* A')
    (m : ℕ) (g : Fin m → G) :
    MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) (GDet.gen (A := A) fun j => MonoidAlgebra.single (g j) 1) =
      GDet.gen (A := A') fun j => MonoidAlgebra.single (g j) 1 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [GDet.gen, map_sum, MonoidAlgebra.mapRingHom_single]

theorem UpperTheory.V.AlgebraTools.Det.descend :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] {A' : Type} [CommRing A'] (ι : A →+* A') (D' : GDet n A' G), Function.Injective ι →
    (∀ (m : ℕ) (g : Fin m → G) (β : Fin m →₀ ℕ),
      AddMonoidAlgebra.coeff (D'.D (MvPolynomial (Fin m) A') (GDet.gen fun j => MonoidAlgebra.single (g j) 1)) β ∈ ι.range) →
    ∃! D : GDet n A G, D.map ι = D' := by
  intro n A G _ _ A' _ ι D' hι hc
  have hr := fun σ x => exists_isCompact_preimage_eq_of_isLimit_of_isAffineHom ι D' hc σ x
  have hinj : ∀ σ : Type, Function.Injective (MvPolynomial.map (σ := σ) ι) :=
    fun σ => MvPolynomial.map_injective ι hι
  let d : (σ : Type) → MonoidAlgebra (MvPolynomial σ A) G →* MvPolynomial σ A := fun σ =>
    { toFun := fun x => Classical.choose (hr σ x)
      map_one' := hinj σ (by rw [Classical.choose_spec (hr σ 1), map_one, map_one, map_one])
      map_mul' := fun x y => hinj σ (by
        rw [Classical.choose_spec (hr σ (x * y)), map_mul, map_mul, map_mul,
          Classical.choose_spec (hr σ x), Classical.choose_spec (hr σ y)]) }
  have hd : ∀ σ x, MvPolynomial.map ι (d σ x) =
      D'.D (MvPolynomial σ A') (MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) x) :=
    fun σ x => Classical.choose_spec (hr σ x)
  have hnat : ∀ (σ τ : Type) (f : MvPolynomial σ A →ₐ[A] MvPolynomial τ A) (x : MonoidAlgebra (MvPolynomial σ A) G),
      d τ (MonoidAlgebra.mapRingHom G (f : MvPolynomial σ A →+* MvPolynomial τ A) x) = f (d σ x) := by
    intro σ τ f x
    apply hinj τ
    let f' : MvPolynomial σ A' →ₐ[A'] MvPolynomial τ A' :=
      MvPolynomial.aeval fun i => MvPolynomial.map ι (f (MvPolynomial.X i))
    have hf : (MvPolynomial.map ι).comp (f : MvPolynomial σ A →+* MvPolynomial τ A) =
        (f' : MvPolynomial σ A' →+* MvPolynomial τ A').comp (MvPolynomial.map ι) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        have ha := f.commutes a
        simp only [MvPolynomial.algebraMap_eq] at ha
        simp [f', ha]
      · intro i
        simp [f']
    have e1 : MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) (MonoidAlgebra.mapRingHom G (f : MvPolynomial σ A →+* MvPolynomial τ A) x) =
        MonoidAlgebra.mapRingHom G (f' : MvPolynomial σ A' →+* MvPolynomial τ A') (MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) x) := by
      rw [← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp, hf, MonoidAlgebra.mapRingHom_comp, RingHom.comp_apply]
    rw [hd, e1, D'.nat (MvPolynomial σ A') (MvPolynomial τ A') f', ← hd]
    exact (RingHom.congr_fun hf _).symm
  have hhom : ∀ (σ : Type) (b : MvPolynomial σ A) (x : MonoidAlgebra (MvPolynomial σ A) G),
      d σ (b • x) = b ^ n * d σ x := by
    intro σ b x
    apply hinj σ
    have hs : MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) (b • x) =
        MvPolynomial.map ι b • MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) x := by
      ext g
      simp [MonoidAlgebra.mapRingHom_apply]
    rw [hd, map_mul, map_pow, hd, hs, D'.homog]
  obtain ⟨D, hD⟩ := UpperTheory.V.AlgebraTools.Det.extendPoly d hnat hhom
  have hex : D.map ι = D' := by
    apply UpperTheory.V.AlgebraTools.Det.extGen
    intro m g
    rw [← mapRingHom_gdet_gen_single_eq_gen_single ι m g, (UpperTheory.V.AlgebraTools.Det.mapApi D ι).2.2.2.1 (Fin m), hD, hd]
  refine ⟨D, hex, fun D2 h2 => ?_⟩
  exact (UpperTheory.V.AlgebraTools.Det.injTest (X := Unit) (fun _ => A') (fun _ => ι)
    (fun a ha => hι (by rw [ha (), map_zero])) ).1 D2 D (fun _ => by rw [h2, hex])
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.KerTest
section
open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.kerTest :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] {X : Type} (K : X → Type) [∀ x, CommRing (K x)] (f : ∀ x, A →+* K x)
    (ρ : ∀ x, G →* Matrix (Fin n) (Fin n) (K x)) (D : GDet n A G),
    (∀ a, (∀ x, f x a = 0) → a = 0) → (∀ x, D.map (f x) = GDet.ofRep (ρ x)) →
    ∀ y : MonoidAlgebra A G, (∀ x, GDet.repAlg (ρ x) (K x) (MonoidAlgebra.mapRingHom G (f x) y) = 0) → D.Kills y := by
  intro n A G _ _ X K _ f ρ D hf hD y hy
  refine (UpperTheory.V.AlgebraTools.Det.injTest K f hf).2 D y fun x => ?_
  rw [hD x]
  exact (UpperTheory.V.AlgebraTools.Det.repApi (ρ x)).2.2.2.2.1 _ (hy x)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.KillsLam
section
open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.killsLam :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (y : MonoidAlgebra A G), D.Kills y →
    ∀ (h : MonoidAlgebra A G) (i : ℕ), 1 ≤ i → i ≤ n → D.lam i (h * y) = 0 := by
  intro n A G _ _ D y hy h i hi1 hin
  have key := UpperTheory.V.AlgebraTools.Det.expand D (h * y) (Polynomial A) 1 Polynomial.X
  have hk := hy (Polynomial A)
    ((Polynomial.X : Polynomial A) • MonoidAlgebra.mapRingHom G (algebraMap A (Polynomial A)) h)
  have heq : MonoidAlgebra.single 1 (1 : Polynomial A) +
      (Polynomial.X : Polynomial A) • (MonoidAlgebra.mapRingHom G (algebraMap A (Polynomial A))) (h * y) =
      1 + ((Polynomial.X : Polynomial A) • MonoidAlgebra.mapRingHom G (algebraMap A (Polynomial A)) h) *
        (MonoidAlgebra.mapRingHom G (algebraMap A (Polynomial A))) y := by
    rw [map_mul, smul_mul_assoc, MonoidAlgebra.one_def]
  rw [heq, hk] at key
  have hc := congrArg (fun p : Polynomial A => p.coeff i) key
  simp only [one_pow, mul_one, Polynomial.algebraMap_eq, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] at hc
  rw [Finset.sum_ite_eq] at hc
  have hmem : i ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hi0 : i ≠ 0 := by omega
  simp only [hmem, if_true, hi0, if_false] at hc
  exact hc.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.PolarInj
section
open Polynomial Matrix UpperTheory.V UpperTheory.V.W

private theorem star_mapRingHom_eq_mapRingHom_star {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (B B' : Type) [CommRing B] [CommRing B'] [Algebra O B] [Algebra O B'] (n : ℕ) (φ : B →+* B') (hφ : φ.comp (algebraMap O B) = algebraMap O B') (y : MonoidAlgebra B F.G₀) :
    F.star O B' n (MonoidAlgebra.mapRingHom F.G₀ φ y) = MonoidAlgebra.mapRingHom F.G₀ φ (F.star O B n y) := by
  have h1 : ∀ (u : Bˣ) (k : ℤ), φ ((u ^ k : Bˣ) : B) = ((Units.map (φ : B →* B') u ^ k : B'ˣ) : B') := by
    intro u k
    rw [← map_zpow]
    rfl
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp [GFrame.star]
  | add a b ha hb =>
    simp only [map_add (f := _), GFrame.star, MulOpposite.unop_add] at *
    rw [ha, hb]
  | single g b =>
    simp only [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, GFrame.eps, MonoidAlgebra.mapRingHom_single]
    simp
    rw [h1]
    congr 3
    ext
    simp [← hφ]

theorem UpperTheory.V.AlgebraTools.Det.polarInj :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (D : GDet n R F.G₀) {X : Type} (K : X → Type) [∀ x, CommRing (K x)] [∀ x, Algebra O (K x)] (f : ∀ x, R →ₐ[O] K x),
    (∀ a, (∀ x, f x a = 0) → a = 0) → (∀ x, F.IsPolar O (D.map (f x : R →+* K x))) → F.IsPolar O D := by
  intro l _ F O _ _ R _ _ n D X K _ _ f hf h
  intro B _ _ _ _ y
  classical
  let u : MonoidAlgebra (MvPolynomial F.G₀ R) F.G₀ := y.coeff.support.sum fun g => MonoidAlgebra.single g (MvPolynomial.X g)
  let ev : MvPolynomial F.G₀ R →ₐ[R] B := MvPolynomial.aeval fun g => y.coeff g
  have hev : MonoidAlgebra.mapRingHom F.G₀ (ev : MvPolynomial F.G₀ R →+* B) u = y := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [u, map_sum, MonoidAlgebra.mapRingHom_single]
    simp only [ev, AlgHom.coe_toRingHom, MvPolynomial.aeval_X]
    exact y.sum_single
  have hevO : (ev : MvPolynomial F.G₀ R →+* B).comp (algebraMap O (MvPolynomial F.G₀ R)) = algebraMap O B := by
    ext o
    simp [ev, MvPolynomial.algebraMap_eq, IsScalarTower.algebraMap_apply O R B]
  have key : D.D _ (F.star O _ n u) = D.D _ u := by
    rw [← sub_eq_zero]
    ext m
    rw [MvPolynomial.coeff_zero]
    apply hf
    intro x
    letI : Algebra R (MvPolynomial F.G₀ (K x)) := ((algebraMap (K x) (MvPolynomial F.G₀ (K x))).comp (f x : R →+* K x)).toAlgebra
    let φ : MvPolynomial F.G₀ R →ₐ[R] MvPolynomial F.G₀ (K x) := MvPolynomial.aeval MvPolynomial.X
    have hφ : (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)) = MvPolynomial.map (f x : R →+* K x) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [φ, RingHom.algebraMap_toAlgebra, MvPolynomial.algebraMap_eq]
      · intro i
        simp [φ]
    have hφO : (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)).comp (algebraMap O (MvPolynomial F.G₀ R)) = algebraMap O (MvPolynomial F.G₀ (K x)) := by
      rw [hφ]
      refine RingHom.ext fun o => ?_
      rw [RingHom.comp_apply, MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_apply, MvPolynomial.map_C]
      congr 1
      exact (f x).commutes o
    have hz : MvPolynomial.map (f x : R →+* K x) (D.D _ (F.star O _ n u) - D.D _ u) = 0 := by
      rw [← hφ, map_sub, sub_eq_zero]
      have hx := h x (MvPolynomial F.G₀ (K x)) (MonoidAlgebra.mapRingHom F.G₀ (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)) u)
      rw [star_mapRingHom_eq_mapRingHom_star F O _ _ n _ hφO] at hx
      change D.D _ (MonoidAlgebra.mapRingHom F.G₀ (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)) (F.star O _ n u)) = D.D _ (MonoidAlgebra.mapRingHom F.G₀ (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)) u) at hx
      rw [D.nat _ _ φ, D.nat _ _ φ] at hx
      exact hx
    have hc := congrArg (AddMonoidAlgebra.coeff · m) hz
    rw [MvPolynomial.coeff_map] at hc
    simpa using hc
  rw [← hev, star_mapRingHom_eq_mapRingHom_star F O _ _ n _ hevO, D.nat _ _ ev, D.nat _ _ ev, key]
end

