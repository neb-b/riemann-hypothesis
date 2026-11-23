module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.IrrOpen

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Expand
section
open Polynomial UpperTheory.V.W

private theorem hom_two {A : Type} [CommRing A] {n : ℕ} (P : MvPolynomial (Fin 2) A) (hP : P.IsHomogeneous n) :
    ∃ c : ℕ → A, ∀ (B : Type) [CommRing B] [Algebra A B] (s t : B),
      MvPolynomial.aeval ![s, t] P = ∑ i ∈ Finset.range (n + 1), algebraMap A B (c i) * s ^ (n - i) * t ^ i := by
  classical
  let e : ℕ → (Fin 2 →₀ ℕ) := fun i => Finsupp.single 0 (n - i) + Finsupp.single 1 i
  refine ⟨fun i => P.coeff (e i), ?_⟩
  intro B _ _ s t
  have hF : ∀ d : Fin 2 →₀ ℕ, MvPolynomial.aeval ![s, t] (MvPolynomial.monomial d (P.coeff d)) =
      algebraMap A B (P.coeff d) * s ^ (d 0) * t ^ (d 1) := by
    intro d
    rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
    simp [mul_assoc]
  conv_lhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp_rw [hF]
  have hinj : Set.InjOn e (Finset.range (n + 1)) := by
    intro i _ j _ h
    have := congrArg (fun f => f 1) h
    simpa [e] using this
  have hR : ∑ i ∈ Finset.range (n + 1), algebraMap A B (P.coeff (e i)) * s ^ (n - i) * t ^ i =
      ∑ d ∈ (Finset.range (n + 1)).image e, algebraMap A B (P.coeff d) * s ^ (d 0) * t ^ (d 1) := by
    rw [Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [e]
  rw [hR]
  apply Finset.sum_subset
  · intro d hd
    rw [Finset.mem_image]
    have hdeg := hP (MvPolynomial.mem_support_iff.mp hd)
    have h2 : d 0 + d 1 = n := by
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using hdeg
    refine ⟨d 1, Finset.mem_range.mpr (by omega), ?_⟩
    ext j
    fin_cases j <;> simp [e] <;> omega
  · intro d _ hd
    have h0 : P.coeff d = 0 := by simpa [MvPolynomial.mem_support_iff] using hd
    simp [h0]

theorem UpperTheory.V.AlgebraTools.Det.expand :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (y : MonoidAlgebra A G) (B : Type) [CommRing B] [Algebra A B] (s t : B),
    D.D B (MonoidAlgebra.single 1 s + t • MonoidAlgebra.mapRingHom G (algebraMap A B) y) =
    ∑ i ∈ Finset.range (n + 1), algebraMap A B (D.lam i y) * s ^ (n - i) * t ^ i := by
  intro n A G _ _ D y B _ _ s t
  let y2 : Fin 2 → MonoidAlgebra A G := ![1, y]
  have genEval (B : Type) [CommRing B] [Algebra A B] (m : ℕ)
      (y : Fin m → MonoidAlgebra A G) (b : Fin m → B) :
      D.D B (∑ j, b j • MonoidAlgebra.mapRingHom G (algebraMap A B) (y j)) =
        MvPolynomial.aeval b (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) := by
    rw [← D.nat (MvPolynomial (Fin m) A) B (MvPolynomial.aeval b)]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GDet.gen, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ext g
    simp [MonoidAlgebra.mapRingHom]
  have coeff_scale {m : ℕ} (P : MvPolynomial (Fin m) A) (s : Fin m →₀ ℕ) :
      AddMonoidAlgebra.coeff ((MvPolynomial.aeval (fun j => (X * C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X])) P).coeff s.degree) s =
        AddMonoidAlgebra.coeff P s := by
    induction P using MvPolynomial.induction_on' with
    | monomial u a =>
      have h : MvPolynomial.aeval (fun j => (X * C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X]))
          (MvPolynomial.monomial u a) = C (MvPolynomial.monomial u a) * X ^ u.degree := by
        rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq, Finsupp.prod, Finsupp.prod,
          show u.degree = ∑ i ∈ u.support, u i from rfl]
        simp only [mul_pow, Finset.prod_mul_distrib, ← C_pow, ← map_prod, Finset.prod_pow_eq_pow_sum,
          Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, map_mul]
        ring
      rw [h, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial_apply, MvPolynomial.coeff_monomial]
      split_ifs with h1 h2 h2
      · rw [MvPolynomial.coeff_monomial, if_pos h2]
      · rw [MvPolynomial.coeff_monomial, if_neg h2]
      · exact absurd (congrArg Finsupp.degree h2) h1
      · simp
    | add p q hp hq =>
      rw [map_add (f := _), Polynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, MvPolynomial.coeff_add]
  have hP : (D.D (MvPolynomial (Fin 2) A) (GDet.gen y2)).IsHomogeneous n := by
    let m := 2
    let y := y2
    have hφ : (MvPolynomial.aeval (fun j => (C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X]))) =
        (Polynomial.CAlgHom : MvPolynomial (Fin m) A →ₐ[A] (MvPolynomial (Fin m) A)[X]) :=
      MvPolynomial.algHom_ext fun i => by
        change MvPolynomial.aeval _ (MvPolynomial.X i) = Polynomial.C (MvPolynomial.X i)
        simp
    have hC : MvPolynomial.aeval (fun j => (C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X]))
        (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) = C (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) := by
      rw [hφ]
      rfl
    have key : MvPolynomial.aeval (fun j => (X * C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X]))
        (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) = X ^ n * C (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) := by
      rw [← genEval _ m y, ← hC, ← genEval _ m y, ← D.homog,
        Finset.smul_sum]
      simp only [mul_smul]
    intro d hd
    have h1 := coeff_scale (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) d
    rw [key, mul_comm, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial] at h1
    have hw : Finsupp.weight 1 d = d.degree := by
      simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one]
      rfl
    rw [hw]
    by_contra hne
    simp [Finsupp.single_apply, Ne.symm hne] at h1
    exact hd h1.symm
  obtain ⟨c, hc⟩ := hom_two _ hP
  have hev : ∀ (B : Type) [CommRing B] [Algebra A B] (s t : B),
      D.D B (MonoidAlgebra.single 1 s + t • MonoidAlgebra.mapRingHom G (algebraMap A B) y) =
        ∑ i ∈ Finset.range (n + 1), algebraMap A B (c i) * s ^ (n - i) * t ^ i := by
    intro B _ _ s t
    rw [← hc B s t, ← genEval B 2 y2 ![s, t]]
    congr 1
    rw [Fin.sum_univ_two]
    simp [y2, MonoidAlgebra.one_def, MonoidAlgebra.smul_single']
  have hlam : ∀ i ∈ Finset.range (n + 1), D.lam i y = c i := by
    intro i hi
    have hchi : D.chi y = ∑ j ∈ Finset.range (n + 1), Polynomial.C (c j * (-1) ^ j) * X ^ (n - j) := by
      have h := hev A[X] X (-1)
      rw [neg_one_smul, ← sub_eq_add_neg, Polynomial.algebraMap_eq] at h
      unfold GDet.chi
      rw [h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_pow, map_neg, map_one]
      ring
    unfold GDet.lam
    rw [hchi, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, mul_left_comm, ← mul_pow, neg_one_mul, neg_neg, one_pow, mul_one]
    · intro j hj hji
      rw [if_neg]
      intro h
      apply hji
      have := Finset.mem_range.mp hi
      have := Finset.mem_range.mp hj
      omega
    · intro h
      exact absurd hi h
  rw [hev B s t]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hlam i hi]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.FormRep
section
open Polynomial Matrix UpperTheory.V UpperTheory.V.W

private theorem repAlg_single {G R : Type} [Group G] [CommRing R] {a : ℕ} (ρ : G →* Matrix (Fin a) (Fin a) R)
    (B : Type) [CommRing B] [Algebra R B] (g : G) (b : B) :
    GDet.repAlg ρ B (MonoidAlgebra.single g b) = b • (ρ g).map (algebraMap R B) := by
  simp [GDet.repAlg]

private theorem UpperTheory.V.AlgebraTools.Det.eps_zpow_algebraMap_eq {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O]
    [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (B : Type) [CommRing B] [Algebra R B]
    [Algebra O B] [IsScalarTower O R B] (g : F.G₀) (k : ℤ) :
    ((F.eps O B g ^ k : Bˣ) : B) = algebraMap R B ((F.eps O R g ^ k : Rˣ) : R) := by
  have e : F.eps O B g = Units.map (algebraMap R B : R →* B) (F.eps O R g) := by
    ext
    simp [GFrame.eps, IsScalarTower.algebraMap_apply O R B]
  rw [e, ← map_zpow]
  rfl

theorem UpperTheory.V.AlgebraTools.Det.formRep :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) {a : ℕ} (r : F.G₀ →* GL (Fin a) R) (P : GL (Fin a) R), F.IsForm O n r P →
    (∀ (B : Type) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower O R B] (y : MonoidAlgebra B F.G₀),
      (GDet.repAlg (mat r) B y)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) =
        (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * GDet.repAlg (mat r) B (F.star O B n y)) ∧
    (∀ y, GDet.repAlg (mat r) R y = 0 → GDet.repAlg (mat r) R (F.star O R n y) = 0) ∧
    ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower O R B] (y : MonoidAlgebra B F.G₀),
      (GDet.ofRep (mat r)).D B (F.star O B n y) = (GDet.ofRep (mat r)).D B y := by
  intro l _ F O _ _ R _ _ n a r P hP
  have h1 : ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower O R B] (y : MonoidAlgebra B F.G₀),
      (GDet.repAlg (mat r) B y)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) =
        (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * GDet.repAlg (mat r) B (F.star O B n y) := by
    intro B _ _ _ _ y
    let ρ' : F.G₀ →* Matrix (Fin a) (Fin a) B := (algebraMap R B).mapMatrix.toMonoidHom.comp (mat r)
    have hρ : ∀ g, (mat r g).map (algebraMap R B) = ρ' g := fun g => rfl
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp [GFrame.star]
    | add x z hx hz =>
      rw [(UpperTheory.V.AlgebraTools.Det.starApi F O B n).2.2.1, map_add (f := _), map_add (f := _), Matrix.transpose_add, Matrix.add_mul,
        Matrix.mul_add, hx, hz]
    | single g b =>
      have hs : F.star O B n (MonoidAlgebra.single g b) =
          MonoidAlgebra.single (F.conj g)⁻¹ (b * ((F.eps O B g ^ (1 - (n:ℤ)) : Bˣ) : B)) := by
        simp [GFrame.star, GFrame.starOp]
      rw [hs, repAlg_single, repAlg_single, hρ, hρ, UpperTheory.V.AlgebraTools.Det.eps_zpow_algebraMap_eq F O R B]
      have hF : (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * ρ' (F.conj g) =
          algebraMap R B ((F.eps O R g ^ (1 - (n:ℤ)) : Rˣ) : R) • (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) := by
        have := congrArg (fun M : Matrix (Fin a) (Fin a) R => M.map (algebraMap R B)) (hP g)
        have h' : (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * ρ' (F.conj g) =
            ((((F.eps O R g ^ (1 - (n:ℤ)) : Rˣ) : R)) • (P : Matrix (Fin a) (Fin a) R)).map (algebraMap R B) := by
          simpa [Matrix.map_mul, Matrix.transpose_map, ρ'] using this
        rw [h']
        ext i j
        simp
      have hinv : ρ' (F.conj g) * ρ' (F.conj g)⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      have key : (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) =
          algebraMap R B ((F.eps O R g ^ (1 - (n:ℤ)) : Rˣ) : R) •
            ((P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * ρ' (F.conj g)⁻¹) := by
        calc (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B)
            = (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * (ρ' (F.conj g) * ρ' (F.conj g)⁻¹) := by
              rw [hinv, Matrix.mul_one]
          _ = (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * ρ' (F.conj g) * ρ' (F.conj g)⁻¹ := by
              simp only [Matrix.mul_assoc]
          _ = _ := by rw [hF, Matrix.smul_mul]
      rw [Matrix.transpose_smul, Matrix.smul_mul, key, Matrix.mul_smul, smul_smul]
  have hu : ∀ (B : Type) [CommRing B] [Algebra R B],
      IsUnit ((P : Matrix (Fin a) (Fin a) R).map (algebraMap R B)) := by
    intro B _ _
    exact (P.isUnit.map (algebraMap R B).mapMatrix)
  refine ⟨h1, ?_, ?_⟩
  · intro y hy
    have := h1 R y
    rw [hy, Matrix.transpose_zero, Matrix.zero_mul] at this
    obtain ⟨u, hu'⟩ := hu R
    have h2 := congrArg (fun M => (↑u⁻¹ : Matrix (Fin a) (Fin a) R) * M) this
    simp only [← hu', Matrix.mul_zero, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at h2
    exact h2.symm
  · intro B _ _ _ _ y
    have := congrArg Matrix.det (h1 B y)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_comm] at this
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp (hu B)
    exact (hd.mul_left_cancel this).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.InjTest
section
open Polynomial UpperTheory.V.W

private theorem injTest_mvInj {A : Type} [CommRing A] {X : Type} (K : X → Type) [∀ x, CommRing (K x)]
    (f : ∀ x, A →+* K x) (hf : ∀ a, (∀ x, f x a = 0) → a = 0) {σ : Type} (P Q : MvPolynomial σ A)
    (h : ∀ x, MvPolynomial.map (f x) P = MvPolynomial.map (f x) Q) : P = Q := by
  ext β
  rw [← sub_eq_zero]
  refine hf _ fun x => ?_
  have := congrArg (AddMonoidAlgebra.coeff · β) (h x)
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map] at this
  rw [map_sub, this, sub_self]

private theorem injTest_smul {R S G : Type} [CommRing R] [CommRing S] [Group G] (φ : R →+* S) (r : R)
    (z : MonoidAlgebra R G) :
    MonoidAlgebra.mapRingHom G φ (r • z) = φ r • MonoidAlgebra.mapRingHom G φ z := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [smul_add, map_add (f := _), ha, hb]
  | single g s => simp

private theorem injTest_comp {R S T G : Type} [CommRing R] [CommRing S] [CommRing T] [Group G]
    (φ : R →+* S) (ψ : S →+* T) (z : MonoidAlgebra R G) :
    MonoidAlgebra.mapRingHom G ψ (MonoidAlgebra.mapRingHom G φ z) = MonoidAlgebra.mapRingHom G (ψ.comp φ) z := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g s => simp

theorem UpperTheory.V.AlgebraTools.Det.injTest :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] {X : Type} (K : X → Type) [∀ x, CommRing (K x)] (f : ∀ x, A →+* K x),
    (∀ a, (∀ x, f x a = 0) → a = 0) →
    (∀ D D' : GDet n A G, (∀ x, D.map (f x) = D'.map (f x)) → D = D') ∧
    (∀ (D : GDet n A G) (y : MonoidAlgebra A G), (∀ x, (D.map (f x)).Kills (MonoidAlgebra.mapRingHom G (f x) y)) → D.Kills y) := by
  intro n A G _ _ X K _ f hf
  have mapEval (D : GDet n A G) (x : X) {σ : Type} (z : MonoidAlgebra (MvPolynomial σ A) G) :
      (D.map (f x)).D (MvPolynomial σ (K x)) (MonoidAlgebra.mapRingHom G (MvPolynomial.map (f x)) z) =
        MvPolynomial.map (f x) (D.D (MvPolynomial σ A) z) := by
    let : Algebra A (MvPolynomial σ (K x)) := ((algebraMap (K x) (MvPolynomial σ (K x))).comp (f x)).toAlgebra
    exact D.nat _ _ { MvPolynomial.map (f x) with commutes' := fun a => MvPolynomial.map_C (f x) a } z
  have evalGen (B : Type) [CommRing B] [Algebra A B] {m : ℕ} (g : Fin m → G) (b : Fin m → B) :
      MonoidAlgebra.mapRingHom G (MvPolynomial.aeval b : MvPolynomial (Fin m) A →ₐ[A] B)
          (GDet.gen fun j => MonoidAlgebra.single (g j) (1 : A)) =
        ∑ j, b j • MonoidAlgebra.mapRingHom G (algebraMap A B) (MonoidAlgebra.single (g j) 1) := by
    simp only [GDet.gen, map_sum, injTest_smul, RingHom.coe_coe, MvPolynomial.aeval_X]
    simp
  refine ⟨fun D D' h => ?_, fun D y h => ?_⟩
  · apply GDet.ext
    intro B _ _ w
    obtain ⟨m, g, b, rfl⟩ := UpperTheory.V.AlgebraTools.Det.genSpan (A := A) B w
    let z := GDet.gen fun j => MonoidAlgebra.single (g j) (1 : A)
    have hz : D.D (MvPolynomial (Fin m) A) z = D'.D (MvPolynomial (Fin m) A) z := by
      refine injTest_mvInj K f hf _ _ fun x => ?_
      rw [← mapEval D x z, ← mapEval D' x z, h x]
    rw [← evalGen B g b, D.nat, D'.nat, hz]
  · intro B _ _ w
    obtain ⟨m, g, b, rfl⟩ := UpperTheory.V.AlgebraTools.Det.genSpan (A := A) B w
    set z : MonoidAlgebra (MvPolynomial (Fin m) A) G :=
      1 + GDet.gen (fun j => MonoidAlgebra.single (g j) (1 : A)) * MonoidAlgebra.mapRingHom G MvPolynomial.C y with hz
    have h1 : D.D (MvPolynomial (Fin m) A) z = 1 := by
      refine injTest_mvInj K f hf _ _ fun x => ?_
      rw [← mapEval D x z, map_one, hz, map_add, map_one, map_mul, injTest_comp]
      have e : (MvPolynomial.map (f x) : MvPolynomial (Fin m) A →+* _).comp MvPolynomial.C =
          (algebraMap (K x) (MvPolynomial (Fin m) (K x))).comp (f x) := by
        ext a : 1
        simp
      rw [e, ← injTest_comp]
      exact h x _ _
    have h2 := D.nat _ B (MvPolynomial.aeval b) z
    have e : ((MvPolynomial.aeval b : MvPolynomial (Fin m) A →ₐ[A] B) : MvPolynomial (Fin m) A →+* B).comp
        MvPolynomial.C = algebraMap A B := by
      ext a : 1
      simp
    rw [h1, map_one, hz, map_add, map_one, map_mul, injTest_comp, e, evalGen] at h2
    exact h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.IrrOpenDet
section
open Polynomial Matrix UpperTheory.V UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.irrOpenDet :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (H : Subgroup G),
    ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (φ : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (p : PrimeSpectrum A),
        p.asIdeal = RingHom.ker φ → D.map φ = GDet.ofRep ρ → (p ∈ U ↔ U3.MatIrr H ρ) := by
  intro n A G _ _ D H
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨Set.univ, isOpen_univ, ?_⟩
    intro K _ _ φ ρ p _ _
    rw [UpperTheory.V.AlgebraTools.Det.matIrrIff H ρ]
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => Set.mem_univ _⟩
  · obtain ⟨U, hU, h⟩ := UpperTheory.V.AlgebraTools.Det.irrOpen (ι := Fin n)
      (fun h : H => D.tr (MonoidAlgebra.single (h : G) 1))
    refine ⟨U, hU, ?_⟩
    intro K _ _ φ ρ p hp hD
    rw [UpperTheory.V.AlgebraTools.Det.matIrrIff H ρ]
    refine h K φ (ρ.comp H.subtype) p hp ?_
    intro g
    have hmap : (D.map φ).chi (MonoidAlgebra.single (g : G) 1) =
        (D.chi (MonoidAlgebra.single (g : G) 1)).map φ := by
      let : Algebra A K[X] := ((algebraMap K K[X]).comp φ).toAlgebra
      let f : A[X] →ₐ[A] K[X] :=
        { Polynomial.mapRingHom φ with
          commutes' := fun a => by
            change Polynomial.mapRingHom φ (algebraMap A A[X] a) = algebraMap K K[X] (φ a)
            simp [Polynomial.algebraMap_eq] }
      change D.D K[X] (MonoidAlgebra.single 1 X -
        MonoidAlgebra.mapRingHom G C (MonoidAlgebra.single (g : G) 1)) = f (D.chi _)
      rw [GDet.chi, ← D.nat A[X] K[X] f]
      congr 1
      simp [f]
    have hrep : (GDet.ofRep ρ).chi (MonoidAlgebra.single (g : G) 1) = (ρ g).charpoly := by
      change (GDet.repAlg ρ K[X] (MonoidAlgebra.single 1 X -
        MonoidAlgebra.mapRingHom G C (MonoidAlgebra.single (g : G) 1))).det = _
      rw [map_sub, MonoidAlgebra.mapRingHom_single, map_one, Matrix.charpoly]
      simp only [GDet.repAlg, MonoidAlgebra.lift_single, MonoidHom.comp_apply,
        map_one, one_smul, Polynomial.algebraMap_eq]
      rw [Matrix.charmatrix, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
      rfl
    rw [hD, hrep] at hmap
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    change (ρ g).trace = φ (D.lam 1 _)
    rw [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin, hmap, Polynomial.coeff_map]
    simp [GDet.lam]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.OElRep
section
open Polynomial Matrix UpperTheory.V UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.oElRep :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (r : F.G₀ →* GL (Fin n) R) (v : F.Vl) (ψ : Fin n → F.Gv v →* Rˣ), HasFlag (r.comp (F.φ v)) ψ →
    ∀ g, GDet.repAlg (mat r) R (F.oEl v ψ g) = 0 := by
  intro l _ F O _ _ R _ _ n r v ψ h g
  rw [← (UpperTheory.V.AlgebraTools.Det.flagRel _ _ h).2 g, GFrame.oEl, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp [GDet.repAlg, mat, MonoidAlgebra.lift_single]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.StarDet
section
open Polynomial Matrix UpperTheory.V UpperTheory.V.W

private theorem star_mapRingHom_algHom_eq {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (B B' : Type) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower O R B] [CommRing B'] [Algebra R B'] [Algebra O B'] [IsScalarTower O R B'] (f : B →ₐ[R] B') (x : MonoidAlgebra B F.G₀) : F.star O B' n (MonoidAlgebra.mapRingHom F.G₀ (f : B →+* B') x) = MonoidAlgebra.mapRingHom F.G₀ (f : B →+* B') (F.star O B n x) := by
  have he : ∀ g : F.G₀, Units.map (f : B →* B') (F.eps O B g) = F.eps O B' g := by
    intro g
    ext
    simp [GFrame.eps, pushCh, IsScalarTower.algebraMap_apply O R B, IsScalarTower.algebraMap_apply O R B']
  have hs : ∀ (C : Type) [CommRing C] [Algebra O C] (g : F.G₀) (b : C), F.star O C n (MonoidAlgebra.single g b) = MonoidAlgebra.single (F.conj g)⁻¹ (b * ↑(F.eps O C g ^ (1 - (n:ℤ)))) := by
    intro C _ _ g b
    simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, MonoidAlgebra.smul_single']
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp [GFrame.star]
  | add x y hx hy => simp only [map_add (f := _)] at hx hy ⊢; simp [GFrame.star, map_add (f := _)] at hx hy ⊢; rw [hx, hy]
  | single g b =>
    rw [MonoidAlgebra.mapRingHom_single, hs, hs, MonoidAlgebra.mapRingHom_single, map_mul, ← he g, ← map_zpow]
    rfl

theorem UpperTheory.V.AlgebraTools.Det.starDet :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (D : GDet n R F.G₀), ∃ D' : GDet n R F.G₀,
    ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower O R B] (y : MonoidAlgebra B F.G₀), D'.D B y = D.D B (F.star O B n y) := by
  intro l _ F O _ _ R _ _ n D
  let E : ∀ (B : Type) [CommRing B] [Algebra R B], MonoidAlgebra B F.G₀ →* B := fun B _ _ =>
    letI : Algebra O B := ((algebraMap R B).comp (algebraMap O R)).toAlgebra
    { toFun := fun y => D.D B (F.star O B n y)
      map_one' := by simp [GFrame.star]
      map_mul' := fun x y => by
        have hm : F.star O B n (x * y) = F.star O B n y * F.star O B n x := by simp [GFrame.star, map_mul]
        simp only [hm, map_mul, mul_comm] }
  have hE : ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower O R B] (y : MonoidAlgebra B F.G₀), E B y = D.D B (F.star O B n y) := by
    intro B _ _ iO _ y
    have hi : ((algebraMap R B).comp (algebraMap O R)).toAlgebra = iO :=
      Algebra.algebra_ext _ _ (fun r => (IsScalarTower.algebraMap_apply O R B r).symm)
    subst hi
    rfl
  refine ⟨{ D := E, nat := ?_, homog := ?_ }, fun B _ _ _ _ y => hE B y⟩
  · intro B B' _ _ _ _ f x
    letI : Algebra O B := ((algebraMap R B).comp (algebraMap O R)).toAlgebra
    haveI : IsScalarTower O R B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI : Algebra O B' := ((algebraMap R B').comp (algebraMap O R)).toAlgebra
    haveI : IsScalarTower O R B' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    rw [hE B', hE B, star_mapRingHom_algHom_eq F O R n B B' f x, D.nat]
  · intro B _ _ b x
    letI : Algebra O B := ((algebraMap R B).comp (algebraMap O R)).toAlgebra
    haveI : IsScalarTower O R B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hsm : F.star O B n (b • x) = b • F.star O B n x := by simp [GFrame.star, map_smul]
    rw [hE B, hE B, hsm, D.homog]
end

