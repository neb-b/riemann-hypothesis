module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbitt
public import Mathlib.RepresentationTheory.Semisimple
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0001
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.BnRepLin
section
open Polynomial Matrix UpperTheory.V.W

private noncomputable def UpperTheory.V.AlgebraTools.Det.bnRep_lin {n : ℕ} {K G : Type} [Field K] [Group G]
    (ρ : G →* Matrix (Fin n) (Fin n) K) : Representation K G (Fin n → K) where
  toFun g := Matrix.toLin' (ρ g)
  map_one' := by rw [map_one, Matrix.toLin'_one]; rfl
  map_mul' g h := by rw [map_mul, Matrix.toLin'_mul]; rfl

private theorem UpperTheory.V.AlgebraTools.Det.bnRep_ss {n : ℕ} {K G : Type} [Field K] [Group G]
    (ρ : G →* Matrix (Fin n) (Fin n) K)
    (h : ∀ W : Submodule K (Fin n → K), (∀ g, ∀ v ∈ W, ρ g *ᵥ v ∈ W) →
      ∃ W', (∀ g, ∀ v ∈ W', ρ g *ᵥ v ∈ W') ∧ IsCompl W W') :
    IsSemisimpleModule (MonoidAlgebra K G) (UpperTheory.V.AlgebraTools.Det.bnRep_lin ρ).asModule := by
  rw [← Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  refine ⟨fun W => ?_⟩
  obtain ⟨W', hW', hc⟩ := h W.toSubmodule (fun g v hv => W.apply_mem_toSubmodule g hv)
  refine ⟨⟨W', fun g v hv => hW' g v hv⟩, ?_, ?_⟩
  · rw [disjoint_iff]
    exact Subrepresentation.toSubmodule_injective hc.inf_eq_bot
  · rw [codisjoint_iff]
    exact Subrepresentation.toSubmodule_injective hc.sup_eq_top

theorem UpperTheory.V.AlgebraTools.Det.bnRep :
    ∀ {n : ℕ} {K G : Type} [Field K] [Group G] (ρ ρ' : G →* Matrix (Fin n) (Fin n) K),
    (∀ W : Submodule K (Fin n → K), (∀ g, ∀ v ∈ W, ρ g *ᵥ v ∈ W) → ∃ W', (∀ g, ∀ v ∈ W', ρ g *ᵥ v ∈ W') ∧ IsCompl W W') →
    (∀ W : Submodule K (Fin n → K), (∀ g, ∀ v ∈ W, ρ' g *ᵥ v ∈ W) → ∃ W', (∀ g, ∀ v ∈ W', ρ' g *ᵥ v ∈ W') ∧ IsCompl W W') →
    (∀ g, (ρ g).charpoly = (ρ' g).charpoly) → ∃ P : GL (Fin n) K, ∀ g, (P : Matrix (Fin n) (Fin n) K) * ρ' g = ρ g * P := by
  intro n K G _ _ ρ ρ' h h' hc
  obtain ⟨e, he⟩ := Formalism.IrreducibleCountingLemmas.Z.brauer_nesbitt K G (Fin n → K) (Fin n → K)
    (UpperTheory.V.AlgebraTools.Det.bnRep_lin ρ') (UpperTheory.V.AlgebraTools.Det.bnRep_lin ρ)
    (UpperTheory.V.AlgebraTools.Det.bnRep_ss ρ' h') (UpperTheory.V.AlgebraTools.Det.bnRep_ss ρ h) (fun g => by
      show (Matrix.toLin' (ρ' g)).charpoly = (Matrix.toLin' (ρ g)).charpoly
      rw [Matrix.charpoly_toLin', Matrix.charpoly_toLin']
      exact (hc g).symm)
  have h1 : LinearMap.toMatrix' (e.symm : (Fin n → K) →ₗ[K] (Fin n → K)) *
      LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)) = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    simp
  have h2 : LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)) *
      LinearMap.toMatrix' (e.symm : (Fin n → K) →ₗ[K] (Fin n → K)) = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    simp
  refine ⟨⟨_, _, h2, h1⟩, fun g => ?_⟩
  show LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)) * ρ' g =
    ρ g * LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K))
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  exact he g
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.ExtGen
section
open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.extGen :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D D' : GDet n A G),
    (∀ (m : ℕ) (g : Fin m → G), D.D (MvPolynomial (Fin m) A) (GDet.gen fun j => MonoidAlgebra.single (g j) 1) =
      D'.D (MvPolynomial (Fin m) A) (GDet.gen fun j => MonoidAlgebra.single (g j) 1)) → D = D' := by
  intro n A G _ _ D D' h
  refine GDet.ext fun B _ _ x => ?_
  obtain ⟨m, g, b, rfl⟩ := UpperTheory.V.AlgebraTools.Det.genSpan (A := A) B x
  rw [UpperTheory.V.AlgebraTools.Det.genEval D B m (fun j => MonoidAlgebra.single (g j) 1) b,
    UpperTheory.V.AlgebraTools.Det.genEval D' B m (fun j => MonoidAlgebra.single (g j) 1) b, h]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.ExtendPoly
section
open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.extendPoly :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (d : ∀ σ : Type, MonoidAlgebra (MvPolynomial σ A) G →* MvPolynomial σ A),
    (∀ (σ τ : Type) (f : MvPolynomial σ A →ₐ[A] MvPolynomial τ A) (x : MonoidAlgebra (MvPolynomial σ A) G),
      d τ (MonoidAlgebra.mapRingHom G (f : MvPolynomial σ A →+* MvPolynomial τ A) x) = f (d σ x)) →
    (∀ (σ : Type) (b : MvPolynomial σ A) (x : MonoidAlgebra (MvPolynomial σ A) G), d σ (b • x) = b ^ n * d σ x) →
    ∃ D : GDet n A G, ∀ (σ : Type) (x : MonoidAlgebra (MvPolynomial σ A) G), D.D (MvPolynomial σ A) x = d σ x := by
  intro n A G _ _ d hnat hhom
  have hsurj : ∀ (B : Type) [CommRing B] [Algebra A B],
      Function.Surjective (MonoidAlgebra.mapRingHom G
        ((MvPolynomial.aeval id : MvPolynomial B A →ₐ[A] B) : MvPolynomial B A →+* B)) := by
    intro B _ _
    rw [MonoidAlgebra.coe_mapRingHom]
    refine MonoidAlgebra.map_surjective _ ?_
    intro b
    exact ⟨MvPolynomial.X b, by simp⟩
  have spec : ∀ (B : Type) [CommRing B] [Algebra A B] (y : MonoidAlgebra B G),
      MonoidAlgebra.mapRingHom G
        ((MvPolynomial.aeval id : MvPolynomial B A →ₐ[A] B) : MvPolynomial B A →+* B)
        (hsurj B y).choose = y :=
    fun B _ _ y => (hsurj B y).choose_spec
  have ind : ∀ (B : Type) [CommRing B] [Algebra A B] (x x' : MonoidAlgebra (MvPolynomial B A) G),
      MonoidAlgebra.mapRingHom G
          ((MvPolynomial.aeval id : MvPolynomial B A →ₐ[A] B) : MvPolynomial B A →+* B) x =
        MonoidAlgebra.mapRingHom G
          ((MvPolynomial.aeval id : MvPolynomial B A →ₐ[A] B) : MvPolynomial B A →+* B) x' →
      MvPolynomial.aeval id (d B x) = MvPolynomial.aeval id (d B x') :=
    fun B _ _ x x' h => UpperTheory.V.AlgebraTools.Det.liftIndep d hnat B B B _ _ x x' h
  refine ⟨⟨fun B _ _ =>
    { toFun := fun y => MvPolynomial.aeval id (d B (hsurj B y).choose)
      map_one' := ?_
      map_mul' := ?_ }, ?_, ?_⟩, ?_⟩
  · show MvPolynomial.aeval id (d B (hsurj B 1).choose) = 1
    rw [ind B _ 1 (by rw [spec, map_one]), map_one, map_one]
  · intro y y'
    show MvPolynomial.aeval id (d B (hsurj B (y * y')).choose) =
      MvPolynomial.aeval id (d B (hsurj B y).choose) * MvPolynomial.aeval id (d B (hsurj B y').choose)
    rw [ind B _ ((hsurj B y).choose * (hsurj B y').choose) (by rw [spec, map_mul, spec, spec]),
      map_mul, map_mul]
  · intro B B' _ _ _ _ f y
    have h := UpperTheory.V.AlgebraTools.Det.liftIndep d hnat B' B' B (MvPolynomial.aeval id)
      (f.comp (MvPolynomial.aeval id)) (hsurj B' (MonoidAlgebra.mapRingHom G (f : B →+* B') y)).choose
      (hsurj B y).choose (by
        rw [spec]
        conv_lhs => rw [← spec B y]
        rw [← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp]
        rfl)
    exact h
  · intro B _ _ b y
    show MvPolynomial.aeval id (d B (hsurj B (b • y)).choose) =
      b ^ n * MvPolynomial.aeval id (d B (hsurj B y).choose)
    rw [ind B _ (MvPolynomial.X b • (hsurj B y).choose) (by
        rw [spec]
        conv_lhs => rw [← spec B y]
        ext m
        rw [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_mapRingHom,
          MonoidAlgebra.coeff_mapRingHom,
          MonoidAlgebra.coeff_smul_apply (MvPolynomial.X b : MvPolynomial B A) (hsurj B y).choose m]
        simp [smul_eq_mul]), hhom, map_mul, map_pow, MvPolynomial.aeval_X, id]
  · intro σ x
    show MvPolynomial.aeval id (d (MvPolynomial σ A) (hsurj (MvPolynomial σ A) x).choose) = d σ x
    have h := UpperTheory.V.AlgebraTools.Det.liftIndep d hnat (MvPolynomial σ A) (MvPolynomial σ A) σ
      (MvPolynomial.aeval id) (AlgHom.id A _) _ x (by rw [spec])
    simpa using h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.FlagRel
section
open Polynomial Matrix UpperTheory.V UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.flagRel :
    ∀ {k H : Type} [CommRing k] [Group H] {n : ℕ} (r : H →* GL (Fin n) k) (κ : Fin n → H →* kˣ), HasFlag r κ →
    (∀ s, (mat r s).charpoly = ∏ j, (X - C (κ j s : k))) ∧
    ∀ g : Fin n → H, (List.ofFn fun j => mat r (g j) - (κ j (g j) : k) • (1 : Matrix (Fin n) (Fin n) k)).prod = 0 := by
  intro k H _ _ n r κ ⟨P, hP⟩
  have hm : ∀ s, mat r s = (r s : Matrix (Fin n) (Fin n) k) := fun _ => rfl
  constructor
  · intro s
    have h1 : ((P * r s * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly = (mat r s).charpoly := by
      rw [hm, Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]
    have h2 : ((P * r s * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular id :=
      fun i j hij => (hP s).1 i j hij
    rw [← h1, Matrix.charpoly_of_upperTriangular _ h2]
    exact Finset.prod_congr rfl fun i _ => by rw [← (hP s).2 i]
  · intro g
    let W : ℕ → Submodule k (Fin n → k) := fun j =>
      { carrier := {v | ∀ i : Fin n, j ≤ i.val → ((P : Matrix (Fin n) (Fin n) k) *ᵥ v) i = 0}
        add_mem' := fun {a b} ha hb i hi => by
          rw [Matrix.mulVec_add, Pi.add_apply, ha i hi, hb i hi, add_zero]
        zero_mem' := fun i _ => by simp
        smul_mem' := fun c a ha i hi => by
          rw [Matrix.mulVec_smul, Pi.smul_apply, ha i hi, smul_zero] }
    have hW : ∀ j v, v ∈ W j ↔ ∀ i : Fin n, j ≤ i.val → ((P : Matrix (Fin n) (Fin n) k) *ᵥ v) i = 0 :=
      fun _ _ => Iff.rfl
    have key := UpperTheory.V.AlgebraTools.Det.flagKill n W
      (fun j => Matrix.toLinAlgEquiv' (mat r (g j) - (κ j (g j) : k) • (1 : Matrix (Fin n) (Fin n) k))) ?_ ?_ ?_
    · apply (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).injective
      rw [map_list_prod, map_zero, List.map_ofFn]
      exact key
    · rw [eq_bot_iff]
      intro v hv
      have h0 : (P : Matrix (Fin n) (Fin n) k) *ᵥ v = 0 := funext fun i => (hW 0 v).1 hv i (Nat.zero_le _)
      have : v = ((P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ ((P : Matrix (Fin n) (Fin n) k) *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      rw [Submodule.mem_bot, this, h0, Matrix.mulVec_zero]
    · rw [eq_top_iff]
      intro v _
      exact (hW n v).2 fun i hi => absurd i.2 (not_lt.2 hi)
    · intro j v hv
      rw [hW] at hv ⊢
      intro i hi
      have e : (P : Matrix (Fin n) (Fin n) k) *ᵥ
          (Matrix.toLinAlgEquiv' (mat r (g j) - (κ j (g j) : k) • (1 : Matrix (Fin n) (Fin n) k)) v) =
          ((P * r (g j) * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ ((P : Matrix (Fin n) (Fin n) k) *ᵥ v)
            - (κ j (g j) : k) • ((P : Matrix (Fin n) (Fin n) k) *ᵥ v) := by
        rw [Matrix.toLinAlgEquiv'_apply, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
          Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hm, Units.val_mul, Units.val_mul,
          Units.inv_mul_cancel_right]
      rw [e, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_eq_zero]
      generalize (P : Matrix (Fin n) (Fin n) k) *ᵥ v = w at hv ⊢
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
      · rcases eq_or_lt_of_le hi with h | h
        · have : j = i := Fin.ext h
          subst this
          rw [← (hP (g j)).2 j]
        · rw [hv i h, mul_zero, mul_zero]
      · intro b _ hb
        rcases lt_or_gt_of_ne hb with h | h
        · have := (hP (g j)).1 i b h
          rw [this, zero_mul]
        · rw [hv b (by have : i.val < b.val := h; omega), mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.GenHomog
section
open Polynomial UpperTheory.V.W

private theorem coeff_scale {A : Type} [CommRing A] {m : ℕ} (P : MvPolynomial (Fin m) A) (s : Fin m →₀ ℕ) :
    AddMonoidAlgebra.coeff ((MvPolynomial.aeval (fun j => (X * C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X])) P).coeff s.degree)
      s
      = AddMonoidAlgebra.coeff P s := by
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

theorem UpperTheory.V.AlgebraTools.Det.genHomog :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (m : ℕ) (y : Fin m → MonoidAlgebra A G),
    (D.D (MvPolynomial (Fin m) A) (GDet.gen y)).IsHomogeneous n := by
  intro n A G _ _ D m y
  have hφ : (MvPolynomial.aeval (fun j => (C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X]))) =
      (Polynomial.CAlgHom : MvPolynomial (Fin m) A →ₐ[A] (MvPolynomial (Fin m) A)[X]) :=
    MvPolynomial.algHom_ext fun i => by
      change _ = Polynomial.C (MvPolynomial.X i)
      simp
  have hC : MvPolynomial.aeval (fun j => (C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X]))
      (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) = C (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) := by
    rw [hφ]
    rfl
  have hgen (B : Type) [CommRing B] [Algebra A B] (b : Fin m → B) :
      D.D B (∑ j, b j • MonoidAlgebra.mapRingHom G (algebraMap A B) (y j)) =
        MvPolynomial.aeval b (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) := by
    rw [← D.nat (MvPolynomial (Fin m) A) B (MvPolynomial.aeval b)]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GDet.gen, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ext g
    simp [MonoidAlgebra.mapRingHom]
  have key : MvPolynomial.aeval (fun j => (X * C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X]))
      (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) = X ^ n * C (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) := by
    rw [← hgen _, ← hC, ← hgen _, ← D.homog,
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
  simp [hne] at h1
  exact hd h1.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.IsContIff
section
open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.isContIff :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace G] (I : Ideal A), IsAdic I → ∀ D : GDet n A G,
    D.IsCont I ↔ ∀ i ≤ n, Continuous fun g : G => D.lam i (MonoidAlgebra.single g 1) := by
  intro n A G _ _ _ _ _ I hI D
  unfold GDet.IsCont
  simp only [UpperTheory.V.AlgebraTools.Det.adicContIff I hI]
  constructor
  · intro h i _
    exact h i
  · intro h i
    by_cases hi : i ≤ n
    · exact h i hi
    · have heq : (fun g : G => D.lam i (MonoidAlgebra.single g 1)) =
          fun g => (-1) ^ (i + n) * D.lam n (MonoidAlgebra.single g 1) := by
        funext g
        unfold GDet.lam
        rw [Nat.sub_eq_zero_of_le (not_le.mp hi).le, Nat.sub_self, ← mul_assoc, ← pow_add, add_assoc,
          ← two_mul, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
      rw [heq]
      exact continuous_const.mul (h n le_rfl)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MatIrrIff
section
open Polynomial Matrix UpperTheory.V UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.matIrrIff :
    ∀ {K G : Type} [Field K] [IsAlgClosed K] [Group G] {n : ℕ} (H : Subgroup G) (ρ : G →* Matrix (Fin n) (Fin n) K),
    U3.MatIrr H ρ ↔ Submodule.span K (Set.range fun h : H => ρ h) = ⊤ := by
  intro K G _ _ _ n H ρ
  have h := UpperTheory.V.AlgebraTools.Det.irrIffSpan (K := K) (ρ.comp H.subtype)
  refine Iff.trans ?_ h
  constructor
  · intro h1 N hN; exact h1 N fun g hg v hv => hN ⟨g, hg⟩ v hv
  · intro h1 N hN; exact h1 N fun g v hv => hN g g.2 v hv
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepCont
section
open Polynomial UpperTheory.V.W

private theorem UpperTheory.V.AlgebraTools.Det.cont_charpoly_coeff {n : ℕ} {K : Type} [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] (i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem UpperTheory.V.AlgebraTools.Det.repCont :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace G] (ρ : G →* Matrix (Fin n) (Fin n) A),
    Continuous ρ → ∀ i, Continuous fun g : G => (GDet.ofRep ρ).lam i (MonoidAlgebra.single g 1) := by
  intro n A G _ _ _ _ _ ρ hρ i
  have h : (fun g : G => (GDet.ofRep ρ).lam i (MonoidAlgebra.single g 1))
      = fun g => (-1) ^ i * (ρ g).charpoly.coeff (n - i) := by
    funext g
    rw [GDet.lam, (UpperTheory.V.AlgebraTools.Det.repApi ρ).2.1]
  rw [h]
  exact continuous_const.mul ((UpperTheory.V.AlgebraTools.Det.cont_charpoly_coeff (n - i)).comp hρ)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.StarApi
section
open Polynomial Matrix UpperTheory.V UpperTheory.V.W

section
variable {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R]
  [Algebra O R] (n : ℕ)

private theorem star_add' (y z : MonoidAlgebra R F.G₀) :
    F.star O R n (y + z) = F.star O R n y + F.star O R n z := by
  simp [GFrame.star]

private theorem star_zero' : F.star O R n 0 = 0 := by
  simp [GFrame.star]

end

private theorem star_single_eq_single_conj_inv_mul_eps_zpow {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (g : F.G₀) (r : R) :
    F.star O R n (MonoidAlgebra.single g r) =
      MonoidAlgebra.single (F.conj g)⁻¹ (r * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
  simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]

private theorem conjO_conjO_unimodular_class_representatives {l : ℕ} [Fact l.Prime] (F : GFrame l) (g : F.G₀) : F.conj (F.conj g) = g := by
  have hc : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right F.c_sq
  apply Subtype.ext
  simp [GFrame.conj, hc, ← mul_assoc, F.c_sq]
  rw [mul_assoc, F.c_sq, mul_one]

private theorem eps_conj' {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (g : F.G₀) : F.eps O R (F.conj g) = F.eps O R g := by
  simp [GFrame.eps, GFrame.conj]

private theorem algHom_eps_zpow_eq {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (R' : Type) [CommRing R'] [Algebra O R'] (f : R →ₐ[O] R')
    (g : F.G₀) (k : ℤ) :
    f ((F.eps O R g ^ k : Rˣ) : R) = ((F.eps O R' g ^ k : R'ˣ) : R') := by
  have h : Units.map (f : R →* R') (F.eps O R g) = F.eps O R' g := by
    ext
    simp [GFrame.eps, pushCh]
  rw [← h, ← map_zpow (Units.map (f : R →* R')), Units.coe_map]
  rfl

theorem UpperTheory.V.AlgebraTools.Det.starApi :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ),
    (∀ y z, F.star O R n (y * z) = F.star O R n z * F.star O R n y) ∧ F.star O R n 1 = 1 ∧
    (∀ y z, F.star O R n (y + z) = F.star O R n y + F.star O R n z) ∧ (∀ (a : R) y, F.star O R n (a • y) = a • F.star O R n y) ∧
    (∀ y, F.star O R n (F.star O R n y) = y) ∧
    ∀ (R' : Type) [CommRing R'] [Algebra O R'] (f : R →ₐ[O] R') (y : MonoidAlgebra R F.G₀),
      F.star O R' n (MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') y) = MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') (F.star O R n y) := by
  intro l _ F O _ _ R _ _ n
  refine ⟨?_, ?_, star_add' F O R n, ?_, ?_, ?_⟩
  · intro y z
    simp only [GFrame.star, map_mul, MulOpposite.unop_mul]
  · simp [GFrame.star, map_one]
  · intro a y
    simp only [GFrame.star, map_smul, MulOpposite.unop_smul]
  · intro y
    induction y using MonoidAlgebra.induction_linear
    next => simp [star_zero']
    next y z hy hz => rw [star_add', star_add', hy, hz]
    next g r =>
      simp only [star_single_eq_single_conj_inv_mul_eps_zpow, map_inv, inv_inv, conjO_conjO_unimodular_class_representatives, eps_conj', _root_.inv_zpow]
      rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  · intro R' _ _ f y
    induction y using MonoidAlgebra.induction_linear
    next => simp [star_zero']
    next y z hy hz => rw [map_add (f := _), star_add', star_add', map_add (f := _), hy, hz]
    next g r =>
      simp only [star_single_eq_single_conj_inv_mul_eps_zpow, MonoidAlgebra.mapRingHom_single, RingHom.coe_coe, map_mul]
      rw [algHom_eps_zpow_eq]
end

