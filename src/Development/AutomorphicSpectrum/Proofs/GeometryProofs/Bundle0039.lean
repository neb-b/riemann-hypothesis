module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0035
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0029
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0025
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0010
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0011

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitOfSumEqOne
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

def kMinor {F : Type} [CommRing F] {n r : ℕ} (A : Matrix (Fin n) (Fin r) F) (k : ℕ) (hk : k ≤ r)
    (I : Fin k → Fin n) : F :=
  (A.submatrix I (Fin.castLE hk)).det

theorem stepMinor_eq_kMinor {F : Type} [CommRing F] {n r : ℕ} (A : Matrix (Fin n) (Fin r) F) (i : Fin r)
    (J : Fin ((i : ℕ) + 1) → Fin n) : stepMinor A i J = kMinor A ((i : ℕ) + 1) i.2 J := rfl

def NormAt {F : Type} [Field F] (O : Subring F) {n r : ℕ} (Y : Matrix (Fin n) (Fin r) F) (k : ℕ) (hk : k ≤ r)
    (I : Fin k → Fin n) : Prop :=
  kMinor Y k hk I ≠ 0 ∧ ∀ I' : Fin k → Fin n, kMinor Y k hk I' / kMinor Y k hk I ∈ O

theorem normAt_zero {F : Type} [Field F] (O : Subring F) {n r : ℕ} (Y : Matrix (Fin n) (Fin r) F)
    (I : Fin 0 → Fin n) : NormAt O Y 0 (Nat.zero_le r) I := by
  refine ⟨by simp [kMinor], fun I' => ?_⟩
  simpa [kMinor] using O.one_mem

theorem det_mul_expand {F : Type} [CommRing F] {k r : ℕ} (A : Matrix (Fin k) (Fin r) F)
    (B : Matrix (Fin r) (Fin k) F) :
    (A * B).det = ∑ f : Fin k → Fin r, (∏ a, A a (f a)) * (B.submatrix f id).det :=
  _root_.UpperTheory.Reformulated.B.DetMulExpand.det_mul_expand A B

theorem kMinor_mul_expand {F : Type} [CommRing F] {n m r : ℕ} (A : Matrix (Fin n) (Fin m) F)
    (B : Matrix (Fin m) (Fin r) F) (k : ℕ) (hk : k ≤ r) (J : Fin k → Fin n) :
    kMinor (A * B) k hk J = ∑ I : Fin k → Fin m, (∏ a, A (J a) (I a)) * kMinor B k hk I := by
  unfold kMinor
  have : (A * B).submatrix J (Fin.castLE hk) = A.submatrix J id * B.submatrix id (Fin.castLE hk) := by
    ext a b
    simp [Matrix.mul_apply]
  rw [this, det_mul_expand]
  rfl

theorem kMinor_mul_div_mem {F : Type} [Field F] (D : Subring F) {n m r : ℕ} (A : Matrix (Fin n) (Fin m) F)
    (B : Matrix (Fin m) (Fin r) F) (k : ℕ) (hk : k ≤ r) (c : F) (hA : ∀ a b, A a b ∈ D)
    (hB : ∀ I, kMinor B k hk I / c ∈ D) (J : Fin k → Fin n) : kMinor (A * B) k hk J / c ∈ D := by
  rw [kMinor_mul_expand, Finset.sum_div]
  refine D.sum_mem fun I _ => ?_
  rw [mul_div_assoc]
  exact D.mul_mem (D.prod_mem fun a _ => hA _ _) (hB I)

theorem exists_unit_of_sum_eq_one {F : Type} [Field F] (O : Subring F) [IsLocalRing O] {ι : Type}
    (s : Finset ι) (a : ι → F) (ha : ∀ i ∈ s, a i ∈ O) (h1 : ∑ i ∈ s, a i = 1) :
    ∃ i ∈ s, a i ≠ 0 ∧ (a i)⁻¹ ∈ O := by
  classical
  by_contra hcon
  push_neg at hcon
  have key : ∀ t : Finset ι, t ⊆ s → ∃ h : ∑ i ∈ t, a i ∈ O, (⟨_, h⟩ : O) ∈ IsLocalRing.maximalIdeal O := by
    intro t
    induction t using Finset.cons_induction with
    | empty => intro _; exact ⟨by simp, Ideal.zero_mem _⟩
    | cons i t hi ih =>
      intro hts
      rw [Finset.cons_eq_insert, Finset.insert_subset_iff] at hts
      obtain ⟨h2, h3⟩ := ih hts.2
      have h4 : a i ∈ O := ha i hts.1
      have h5 : (⟨a i, h4⟩ : O) ∈ IsLocalRing.maximalIdeal O := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        obtain ⟨v, hv⟩ := hu.exists_right_inv
        have hv' : a i * (v : F) = 1 := congrArg Subtype.val hv
        have h0 : a i ≠ 0 := left_ne_zero_of_mul_eq_one hv'
        refine hcon i hts.1 h0 ?_
        rw [eq_comm.1 (eq_inv_of_mul_eq_one_right hv')]
        exact v.2
      rw [Finset.sum_cons]
      refine ⟨O.add_mem h4 h2, ?_⟩
      exact Ideal.add_mem _ h5 h3
  obtain ⟨h, hm⟩ := key s subset_rfl
  have : (⟨∑ i ∈ s, a i, h⟩ : O) = 1 := Subtype.ext h1
  rw [this] at hm
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 hm)

theorem kMinor_mul_upper {F : Type} [CommRing F] {n r : ℕ} (A : Matrix (Fin n) (Fin r) F)
    (C : Matrix (Fin r) (Fin r) F) (hC : ∀ l k, k < l → C l k = 0) (k : ℕ) (hk : k ≤ r) (I : Fin k → Fin n) :
    kMinor (A * C) k hk I = kMinor A k hk I * kMinor C k hk (Fin.castLE hk) := by
  unfold kMinor
  rw [← Matrix.det_mul]
  congr 1
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Finset.sum_of_injOn (Fin.castLE hk) (Fin.castLE_injective hk).injOn (fun _ _ => Finset.mem_univ _)
    (fun j _ hj => ?_) (fun _ _ => rfl)
  have hjk : (Fin.castLE hk b) < j := by
    rw [Fin.lt_def]
    by_contra hlt
    have hjk' : (j : ℕ) < k := by
      have := b.2
      simp only [Fin.val_castLE] at hlt
      omega
    exact hj ⟨⟨j, hjk'⟩, by simp, by ext; simp⟩
  rw [hC _ _ hjk, mul_zero]

theorem kMinor_lower_lead {F : Type} [CommRing F] {r : ℕ} (L : Matrix (Fin r) (Fin r) F)
    (h0 : ∀ l k, l < k → L l k = 0) (h1 : ∀ l, L l l = 1) (k : ℕ) (hk : k ≤ r) :
    kMinor L k hk (Fin.castLE hk) = 1 := by
  unfold kMinor
  rw [Matrix.det_of_lowerTriangular]
  · simp [h1]
  · intro a b hab
    exact h0 _ _ (by simpa using hab)

def lastRow {r : ℕ} (k l : Fin r) : Fin ((k : ℕ) + 1) → Fin r := fun a =>
  if h : (a : ℕ) = k then l else ⟨a, by have := a.2; have := k.2; omega⟩

theorem kMinor_lower_lastRow {F : Type} [CommRing F] {r : ℕ} (L : Matrix (Fin r) (Fin r) F)
    (h0 : ∀ l k, l < k → L l k = 0) (h1 : ∀ l, L l l = 1) (k l : Fin r) (hkl : k < l) :
    kMinor L ((k : ℕ) + 1) k.2 (lastRow k l) = L l k := by
  unfold kMinor
  rw [Matrix.det_of_lowerTriangular, Fin.prod_univ_castSucc]
  · have e1 : ∀ a : Fin (k : ℕ), (L.submatrix (lastRow k l) (Fin.castLE k.2)) a.castSucc a.castSucc = 1 := by
      intro a
      have : lastRow k l a.castSucc = Fin.castLE k.2 a.castSucc := by
        have := a.2
        ext
        simp [lastRow, Nat.ne_of_lt this]
      simp [this, h1]
    have e2 : (L.submatrix (lastRow k l) (Fin.castLE k.2)) (Fin.last _) (Fin.last _) = L l k := by
      have a1 : lastRow k l (Fin.last _) = l := by simp [lastRow]
      have a2 : Fin.castLE k.2 (Fin.last (k : ℕ)) = k := by ext; simp
      simp [a1, a2]
    rw [Finset.prod_congr rfl (fun a _ => e1 a), e2]
    simp
  · intro a b hab
    have hab' : a < b := by simpa using hab
    have hb := b.2
    have ha : (a : ℕ) ≠ k := by
      have : (a : ℕ) < b := hab'
      omega
    simp only [Matrix.submatrix_apply, lastRow, dif_neg ha]
    exact h0 _ _ (by rw [Fin.lt_def]; simpa using hab')

theorem exists_normAt {F : Type} [Field F] (O : Subring F) [IsLocalRing O] {n r : ℕ}
    (A : Matrix (Fin n) (Fin r) F) (N : Matrix (Fin r) (Fin n) F) (hA : ∀ a b, A a b ∈ O)
    (hN : ∀ a b, N a b ∈ O) (hNA : N * A = 1) (Y : Matrix (Fin r) (Fin r) F) (k : ℕ) (hk : k ≤ r)
    (J : Fin k → Fin n) (hJ : NormAt O (A * Y) k hk J) : ∃ I, NormAt O Y k hk I := by
  obtain ⟨hP, hr⟩ := hJ
  set P := kMinor (A * Y) k hk J with hPdef
  have hY : Y = N * (A * Y) := by rw [← Matrix.mul_assoc, hNA, Matrix.one_mul]
  have hyO : ∀ I, kMinor Y k hk I / P ∈ O := fun I => by
    rw [hY]
    exact kMinor_mul_div_mem O N (A * Y) k hk P hN hr I
  have h1 : ∑ I : Fin k → Fin r, (∏ a, A (J a) (I a)) * (kMinor Y k hk I / P) = 1 := by
    have : P = ∑ I : Fin k → Fin r, (∏ a, A (J a) (I a)) * kMinor Y k hk I := kMinor_mul_expand A Y k hk J
    simp only [← mul_div_assoc]
    rw [← Finset.sum_div, ← this, div_self hP]
  obtain ⟨I, -, hne, hinv⟩ := exists_unit_of_sum_eq_one O Finset.univ _
    (fun I _ => O.mul_mem (O.prod_mem fun a _ => hA _ _) (hyO I)) h1
  have hc : (∏ a, A (J a) (I a)) ≠ 0 := left_ne_zero_of_mul hne
  have hd : kMinor Y k hk I / P ≠ 0 := right_ne_zero_of_mul hne
  have hy : kMinor Y k hk I ≠ 0 := fun h => hd (by rw [h, zero_div])
  refine ⟨I, hy, fun I' => ?_⟩
  have e : kMinor Y k hk I' / kMinor Y k hk I =
      (kMinor Y k hk I' / P) * ((∏ a, A (J a) (I a)) * ((∏ a, A (J a) (I a)) * (kMinor Y k hk I / P))⁻¹) := by
    field_simp
  rw [e]
  exact O.mul_mem (hyO I') (O.mul_mem (O.prod_mem fun a _ => hA _ _) hinv)

theorem kMinor_mem {F : Type} [CommRing F] (D : Subring F) {n r : ℕ} (A : Matrix (Fin n) (Fin r) F)
    (hA : ∀ a b, A a b ∈ D) (k : ℕ) (hk : k ≤ r) (I : Fin k → Fin n) : kMinor A k hk I ∈ D := by
  unfold kMinor
  rw [Matrix.det_apply']
  refine D.sum_mem fun σ _ => D.mul_mem (intCast_mem D _) (D.prod_mem fun a _ => hA _ _)

theorem ratio_eq_kMinor {F : Type} [Field F] {r : ℕ} (Y C V : Matrix (Fin r) (Fin r) F)
    (hC : ∀ l k, k < l → C l k = 0) (hV0 : ∀ l k, l < k → V l k = 0) (hV1 : ∀ l, V l l = 1)
    (h : Y * C = V) (k : ℕ) (hk : k ≤ r) (I : Fin k → Fin r) (h0 : kMinor Y k hk (Fin.castLE hk) ≠ 0) :
    kMinor Y k hk I / kMinor Y k hk (Fin.castLE hk) = kMinor V k hk I := by
  have h1 := kMinor_lower_lead V hV0 hV1 k hk
  rw [← h, kMinor_mul_upper Y C hC] at h1
  rw [← h, kMinor_mul_upper Y C hC, div_eq_iff h0]
  linear_combination (-(kMinor Y k hk I)) * h1

theorem entries_mem {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] (Fd : IntermediateField Ω K) {r : ℕ}
    (T' : Matrix (Fin r) (Fin r) Ω) (hT : T'.det ≠ 0) (u C V : Matrix (Fin r) (Fin r) K)
    (hu0 : ∀ l k, l < k → u l k = 0) (hu1 : ∀ l, u l l = 1) (hC : ∀ l k, k < l → C l k = 0)
    (hV0 : ∀ l k, l < k → V l k = 0) (hV1 : ∀ l, V l l = 1)
    (h : T'.map (algebraMap Ω K) * u * C = V) (hF : ∀ l k, V l k ∈ Fd) (l k : Fin r) (hkl : k < l) :
    u l k ∈ Fd := by
  have hdet : IsUnit T'.det := isUnit_iff_ne_zero.2 hT
  have hTi : (T'⁻¹).map (algebraMap Ω K) * T'.map (algebraMap Ω K) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  set Q := (T'⁻¹).map (algebraMap Ω K) * V with hQ
  have hQ' : u * C = Q := by
    rw [hQ, ← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hTi, Matrix.one_mul]
  have hQF : ∀ a b, Q a b ∈ Fd := fun a b => by
    rw [hQ, Matrix.mul_apply]
    exact sum_mem fun j _ => mul_mem (Fd.algebraMap_mem _) (hF _ _)
  have hk : (k : ℕ) + 1 ≤ r := k.2
  have h1 := kMinor_lower_lead V hV0 hV1 _ hk
  rw [← h, kMinor_mul_upper _ C hC] at h1
  have hc : kMinor C _ hk (Fin.castLE hk) ≠ 0 := right_ne_zero_of_mul_eq_one h1
  have h2 := kMinor_mul_upper u C hC _ hk (lastRow k l)
  have h3 := kMinor_mul_upper u C hC _ hk (Fin.castLE hk)
  rw [kMinor_lower_lastRow u hu0 hu1 k l hkl, hQ'] at h2
  rw [kMinor_lower_lead u hu0 hu1, hQ', _root_.one_mul] at h3
  have e : u l k = kMinor Q _ hk (lastRow k l) / kMinor Q _ hk (Fin.castLE hk) := by
    rw [h2, h3, mul_div_assoc, div_self hc, mul_one]
  rw [e]
  exact div_mem (kMinor_mem Fd.toSubalgebra.toSubring Q hQF _ hk _) (kMinor_mem Fd.toSubalgebra.toSubring Q hQF _ hk _)

theorem genU_zero (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) (l k : Fin (r s)) (h : l < k) :
    genU Ω r s l k = 0 := by
  unfold genU
  rw [dif_neg (not_lt.2 h.le), if_neg h.ne]

theorem genU_one (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) (l : Fin (r s)) :
    genU Ω r s l l = 1 := by
  unfold genU
  simp

theorem genU_gen (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (q : GenIx r) :
    genU Ω r q.1 q.2.1.1 q.2.1.2 = algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q) := by
  unfold genU
  rw [dite_eq_left q.2.2]
  rfl

theorem genU_indep (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) :
    AlgebraicIndependent Ω (fun q : GenIx r =>
      algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q)) :=
  (MvPolynomial.algebraicIndependent_X (GenIx r) Ω).map'
    (f := IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r))
    (IsFractionRing.injective _ _)

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HenselianQuasiFiniteFinitePart
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem exists_isFinite_open_of_henselian : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f], ∃ U : X.Opens, IsFinite (U.ι ≫ f) ∧ ∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U := by
  intro R _ _ X f _ _ _ _
  refine ⟨GlobalTheory.finitePart f, GlobalTheory.isFinite_finitePart f, fun x hx => ?_⟩
  exact GlobalTheory.mem_finitePart_of_eq_closedPoint f x hx

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalBaseChange
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange

theorem valAt_comp_top {B : Type} [CommRing B] {X Y : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (f : X ⟶ Y)
    (s : Γ(Y, ⊤)) : valAt (x ≫ f) ⊤ le_top s = valAt x ⊤ le_top (f.appTop.hom s) := by
  unfold valAt
  congr 1

theorem valAt_spec_map {B C : Type} [CommRing B] [CommRing C] {X : Scheme.{0}} (ψ : B →+* C)
    (y : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    valAt (Spec.map (CommRingCat.ofHom ψ) ≫ y) ⊤ le_top s = ψ (valAt y ⊤ le_top s) := by
  rw [valAt_comp_top]
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  have := congrArg (fun φ => φ.hom (y.appTop.hom s)) h
  simp only [CommRingCat.comp_apply] at this
  exact this

abbrev qmap {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (N : ℕ) :
    R ⧸ Ideal.span {(N : R)} →+* R' ⧸ Ideal.span {(N : R')} :=
  Ideal.quotientMap (Ideal.span {(N : R')}) (algebraMap R R')
    (Ideal.span_le.2 (by
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      simp only [SetLike.mem_coe, Ideal.mem_comap, map_natCast]
      exact Ideal.subset_span rfl))

end GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange


open GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange in
theorem GlobalTheory.CompanionTheory.Ar.BT.QFGroup.isHT_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Γ'.IsTorsionAlong G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) N (F ≫ i) → ∀ (L' : Type) [AddCommGroup L'] [Module R' L'] (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) L') (β : L →+ L'), (∀ e, (M'.pt (β e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M.pt e).left) → Submodule.span R' (Set.range β) = ⊤ → ∀ (χ : T →* Rˣ) (w : Module.Dual R L) (w' : Module.Dual R' L'), (∀ e, w' (β e) = algebraMap R R' (w e)) → Γ.IsHT i M N χ w → Γ'.IsHT (F ≫ i) M' N ((Units.map (algebraMap R R' : R →* R')).comp χ) w' := by
  intro R _ _ T _ _ Γ S G _ _ x N i hi L _ _ M R' _ _ _ Γ' F hF hi' L' _ _ M' β hβ hspan χ w w' hw hHT
  obtain ⟨s, hs, hv⟩ := hHT
  have hs' : Γ'.HasValues (F.appTop.hom s)
      (fun t => (((Units.map (algebraMap R R' : R →* R')).comp χ t : R'ˣ) : R')) := by
    obtain ⟨B, instB, ib, j, j', σ, hj, hji, hj'i, -, hσj, hσj'⟩ := hF.pts
    intro t
    have hb : valAt (σ t) ⊤ le_top s = ib (χ t) := by
      apply hj
      rw [← GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange.valAt_spec_map, hσj, hs t, ← RingHom.comp_apply, hji]
    show valAt (Γ'.pt t).left ⊤ le_top (F.appTop.hom s) = _
    rw [← GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange.valAt_comp_top, ← hσj', GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange.valAt_spec_map, hb, ← RingHom.comp_apply, hj'i]
    simp
  obtain ⟨l', hl'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.HTLinear.char_on_tangent_linear R' T Γ' S G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) N (F ≫ i) hi'
    L' M' ((Units.map (algebraMap R R' : R →* R')).comp χ) (F.appTop.hom s) hs'
  have key : ∀ e, l' (β e) = Ideal.Quotient.mk (Ideal.span {(N : R')}) (w' (β e)) := by
    intro e
    obtain ⟨v, hv1, hv2, hv3⟩ := hv e
    have hc : (Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange.qmap (R := R) (R' := R') N))) ≫ v) ≫ Γ.G.hom =
        Spec.map (CommRingCat.ofHom ((algebraMap (R' ⧸ Ideal.span {(N : R')})
          (DualNumber (R' ⧸ Ideal.span {(N : R')}))).comp (Ideal.Quotient.mk _))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
      rw [Category.assoc, hv1, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext r
      all_goals simp [GlobalTheory.CompanionTheory.Ar.dualMap, GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange.qmap, Ideal.quotientMap_mk, TrivSqZeroExt.algebraMap_eq_inl]
    set v'' := hF.cart.lift _ _ hc with hv''
    have h1 := hF.cart.lift_fst _ _ hc
    have h2 := hF.cart.lift_snd _ _ hc
    rw [← hv''] at h1 h2
    have h3 : v'' ≫ F ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R')})))) ≫
        (M'.pt (β e)).left := by
      rw [← Category.assoc, h1, Category.assoc, hv2, hβ e, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
        ← Spec.map_comp]
      congr 2
      ext a
      all_goals simp [GlobalTheory.CompanionTheory.Ar.dualMap, GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange.qmap, Ideal.quotientMap_mk, TrivSqZeroExt.algebraMap_eq_inl]
    have h4 := hl' (β e) v'' ⟨h2, h3⟩
    rw [← GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange.valAt_comp_top, h1, GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange.valAt_spec_map, hv3] at h4
    have h5 := congrArg TrivSqZeroExt.snd h4
    simp only [GlobalTheory.CompanionTheory.Ar.dualMap, GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange.qmap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inr, zero_add, add_zero, Ideal.quotientMap_mk] at h5
    rw [← h5, hw]
  have heq : l' = (Ideal.Quotient.mkₐ R' (Ideal.span {(N : R')})).toLinearMap.comp w' :=
    LinearMap.ext_on_range hspan (fun e => by simpa using key e)
  refine ⟨F.appTop.hom s, hs', fun e' => ?_⟩
  obtain ⟨v', ⟨hv'1, hv'2⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.TanLift.tangent_mod_torsion R' T Γ' S G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) N
    (F ≫ i) hi' L' M' e'
  refine ⟨v', hv'1, hv'2, ?_⟩
  rw [hl' e' v' ⟨hv'1, hv'2⟩, heq]
  simp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateLatticeLeOmega
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HtHoriz

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
  {E : Type} [AddCommGroup E] [Module Ω E] {R : Type} [CommRing R] {L : Type} [AddCommGroup L] [Module R L]

theorem map_add_of_compat (M : LieModel G ξ E) {x : Spec (CommRingCat.of R) ⟶ X} {k : R →+* Ω}
    (hx : Spec.map (CommRingCat.ofHom k) ≫ x = ξ) (M₀ : LieModel G x L) (j : L → E)
    (hj : ∀ e, (M.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ (M₀.pt e).left)
    (a b : L) : j (a + b) = j a + j b := by
  have key : ∀ e, M.pt (j e) = LieCarrier.epsHom k x ξ hx ≫ M₀.pt e :=
    fun e => Over.OverMorphism.ext (hj e)
  apply M.inj
  rw [M.add, key, key, key, M₀.add, MonObj.comp_mul]

theorem map_smul_of_compat (M : LieModel G ξ E) {x : Spec (CommRingCat.of R) ⟶ X} {k : R →+* Ω}
    (M₀ : LieModel G x L) (j : L → E)
    (hj : ∀ e, (M.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ (M₀.pt e).left)
    (c : R) (e : L) : j (c • e) = k c • j e := by
  apply M.inj
  apply Over.OverMorphism.ext
  rw [hj, M₀.smul, M.smul, hj, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, LieCarrier.dualMap_epsMul]

theorem isHT_add_natCast_smul {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : BT.QFGroup R T)
    {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {i : Γ.G.left ⟶ G.left}
    {L : Type} [AddCommGroup L] [Module R L] {M : LieModel G x L} {N : ℕ} {χ : T →* Rˣ}
    {w : Module.Dual R L} (h : Γ.IsHT i M N χ w) (u : Module.Dual R L) :
    Γ.IsHT i M N χ (w + (N : R) • u) := by
  obtain ⟨s, hs, h⟩ := h
  refine ⟨s, hs, fun e => ?_⟩
  obtain ⟨v, h1, h2, h3⟩ := h e
  refine ⟨v, h1, h2, h3.trans ?_⟩
  congr 2
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  exact ⟨-u e, by simp⟩

theorem natCast_smul_isHTFormOver (M : LieModel G ξ E) (N : ℕ) {x : Spec (CommRingCat.of R) ⟶ X} {k : R →+* Ω}
    (hx : Spec.map (CommRingCat.ofHom k) ≫ x = ξ) (hk : Function.Injective k) (h : M.IsHTFormOver N x k 0)
    (w : Module.Dual Ω E)
    (hw : ∀ (e : E) (v : epsAt x ⟶ G), IsTanAt G x v →
      (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ v.left → w e ∈ k.range) :
    M.IsHTFormOver N x k ((N : Ω) • w) := by
  obtain ⟨hd, T, _, Γ, i, L, _, _, M₀, j, χ, w₀, ht, hj, hHT, h0⟩ := h
  have hreg : ∀ e, ∃ r, k r = w (j e) := fun e => hw (j e) (M₀.pt e) (M₀.tan e) (hj e)
  choose f hf using hreg
  let u : Module.Dual R L :=
    { toFun := f
      map_add' := fun a b => hk (by rw [map_add (f := _), hf, hf, hf, map_add_of_compat M hx M₀ j hj, map_add (f := _)])
      map_smul' := fun c e => hk (by
        simp only [RingHom.id_apply, smul_eq_mul, map_mul]
        rw [hf, hf, map_smul_of_compat M M₀ j hj, map_smul, smul_eq_mul]) }
  refine ⟨hd, T, _, Γ, i, L, _, _, M₀, j, χ, w₀ + (N : R) • u, ht, hj, isHT_add_natCast_smul Γ hHT u, fun e => ?_⟩
  have h1 : k (w₀ e) = 0 := (h0 e).symm
  have h2 : k (u e) = w (j e) := hf e
  simp [h1, h2]

end GlobalTheory.CompanionTheory.Ar.HtHoriz

namespace GlobalTheory.CompanionTheory.Ar

theorem htLat_le_omLat_and_smul_mem : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G]
    [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (N : ℕ) (p : Cpt ξ),
    IsCptGen ξ → Smooth G.hom → M.htLat N p ≤ M.omLat p ∧
      (M.IsHTFormAt N p 0 → ∀ w ∈ M.omLat p, (N : Ω) • w ∈ M.htLat N p) := by
  intro X Ω _ ξ G _ _ V _ _ M N p hξ _
  refine ⟨?_, ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro w ⟨_, T, _, Γ, i, L, _, _, M₀, j, χ, w₀, -, hj, -, hw⟩ e he
    obtain ⟨v, hv, hev⟩ := ((lieLat_carrier X G Ω ξ V M p).1 e).1 he
    obtain ⟨e₀, rfl⟩ := M₀.onto v hv
    have : j e₀ = e := M.inj (Over.OverMorphism.ext ((hj e₀).trans hev.symm))
    subst this
    exact ⟨w₀ e₀, (hw e₀).symm⟩
  · intro h w hw
    exact Submodule.subset_span (HtHoriz.natCast_smul_isHTFormOver M N (LieCarrier.genMap_fromSpecStalk p) (hξ.inj p) h w
      fun e v hv hev => hw e (Submodule.subset_span ⟨v, hv, hev⟩))

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralClosureFinite
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem finite_integralClosure_of_essFiniteType_int : ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra.EssFiniteType ℤ A] (K : Type) [Field K] [Algebra A K] [IsFractionRing A K] (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L], Module.Finite A (integralClosure A L) :=
  @PositivityTheory.HtPt.Mb.fin_closure

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsCentreChart
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem join_points_charts : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ κ' : Type) (x : κ → Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (i : Ω →+* Ω') (w : κ' → Ω') (M' : PModel o (joinCo i x w)), (∀ a : o, i (algebraMap o Ω a) = algebraMap o Ω' a) → ∀ p' : Cpt M'.ξ, p' ∈ ctrSet o x i M'.ξ ∧ ∃ l, InChart M'.ξ w l p' :=
  @PositivityTheory.HtPt.Mb.join_charts

end GlobalTheory.CompanionTheory.Ar
end

