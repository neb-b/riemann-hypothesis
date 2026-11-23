module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0183
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUnifOfParts
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0188
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarisedOfVeryDenseFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.DensePol

theorem dense_of_veryDense {R : Type} [CommRing R] {P : Set (Ideal R)} (h : VeryDense P) :
    Dense {p : Sp R | PrimeSpectrum.asIdeal (R := R) p ∈ P} := by
  refine (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).dense_iff.2 ?_
  rintro _ ⟨f, rfl⟩ ⟨q, hq⟩
  obtain ⟨p, hp, hp', -, hf⟩ := h q.asIdeal f q.isPrime hq
  exact ⟨⟨p, hp'⟩, hf, hp⟩

theorem mem_range_spMap {R K : Type} [CommRing R] [Field K] (x : R →+* K) (p : Sp R)
    (h : RingHom.ker x = PrimeSpectrum.asIdeal (R := R) p) : p ∈ Set.range (spMap x) := by
  refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), ?_⟩
  apply PrimeSpectrum.ext
  rw [← h]
  rfl

theorem basis_pow {G : Type} [CommGroup G] {r k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0) (y : Fin r → G)
    (hy : ∀ i, y i ^ (k * l) = 1)
    (h : ∀ z : G, z ^ (k * l) = 1 → ∃! c : Fin r → ZMod (k * l), ∏ i, y i ^ (c i).val = z)
    (z : G) (hz : z ^ k = 1) : ∃! c : Fin r → ZMod k, ∏ i, (y i ^ l) ^ (c i).val = z := by
  haveI : NeZero k := ⟨hk⟩
  have red : ∀ e : Fin r → ℕ, ∏ i, y i ^ ((e i : ZMod (k * l))).val = ∏ i, y i ^ e i := fun e =>
    Finset.prod_congr rfl fun i _ => by rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (hy i)]
  have tor : ∀ e : Fin r → ℕ, (∏ i, y i ^ e i) ^ (k * l) = 1 := fun e => by
    rw [← Finset.prod_pow]
    exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]
  have inj : ∀ e e' : Fin r → ℕ, ∏ i, y i ^ e i = ∏ i, y i ^ e' i → ∀ i, e i ≡ e' i [MOD k * l] := by
    intro e e' he i
    have := (h _ (tor e)).unique (y₁ := fun i => (e i : ZMod (k * l))) (y₂ := fun i => (e' i : ZMod (k * l)))
      (red e) ((red e').trans he.symm)
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 (congrFun this i)
  obtain ⟨c, hc, -⟩ := h z (by rw [pow_mul, hz, one_pow])
  have hd : ∀ i, l ∣ (c i).val := fun i => by
    have := inj (fun i => k * (c i).val) (fun _ => 0) (by
      simp only [pow_zero, Finset.prod_const_one]
      rw [← hz, ← hc, ← Finset.prod_pow]
      exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul, mul_comm]) i
    exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hk) ((Nat.modEq_zero_iff_dvd).1 this)
  choose d hd using hd
  refine ⟨fun i => (d i : ZMod k), ?_, fun c' hc' => funext fun i => ?_⟩
  · rw [← hc]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (by rw [← pow_mul, mul_comm, hy]), hd, pow_mul]
  · have := inj (fun i => l * (c' i).val) (fun i => l * d i) (by
      simp only [pow_mul, ← hd]
      rw [hc, ← hc']) i
    rw [mul_comm k l] at this
    have h2 := Nat.ModEq.mul_left_cancel' hl this
    rw [← (ZMod.natCast_eq_natCast_iff _ _ _).2 h2, ZMod.natCast_zmod_val]

variable {S S' : Scheme.{0}}

theorem basis_pow_linComb {A T : Over S} [GrpObj A] [IsCommMonObj A] {r k l N : ℕ} (hN : N = k * l) (hN0 : N ≠ 0)
    (u : T ⟶ Out.baseOver S) (y : Fin r → (Out.baseOver S ⟶ A)) (hy : ∀ i, y i ^ N = 1)
    (h : ∀ z : T ⟶ A, z ^ N = 1 → ∃! c : Fin r → ZMod N, Out.linComb (fun i => u ≫ y i) (fun i => (c i).val) = z)
    (z : T ⟶ A) (hz : z ^ k = 1) :
    ∃! c : Fin r → ZMod k, Out.linComb (fun i => u ≫ y i ^ l) (fun i => (c i).val) = z := by
  subst hN
  simp only [Out.linComb, List.prod_ofFn, MonObj.comp_pow] at h ⊢
  exact basis_pow (left_ne_zero_of_mul hN0) (right_ne_zero_of_mul hN0) _
    (fun i => by rw [← MonObj.comp_pow, hy, MonObj.comp_one]) h z hz

variable {A : Over S'} {Z : Over S} {x : S' ⟶ S} {φ : A.left ⟶ Z.left}

theorem comp_eq_pushPt (w : φ ≫ Z.hom = A.hom ≫ x) {a : Out.baseOver S' ⟶ A} {s : Out.baseOver S ⟶ Z}
    (h : a.left ≫ φ = x ≫ s.left) {T : Over S'} (u : T ⟶ Out.baseOver S')
    (t : Over.mk (T.hom ≫ x) ⟶ Out.baseOver S) : t ≫ s = pushPt w (u ≫ a) := by
  apply Over.OverMorphism.ext
  have h1 : t.left = T.hom ≫ x := by simpa using Over.w t
  have h2 : u.left = T.hom := by simpa using Over.w u
  change t.left ≫ s.left = (u.left ≫ a.left) ≫ φ
  rw [h1, h2, Category.assoc, Category.assoc, h]

theorem basis_push [GrpObj A] [GrpObj Z] (hφ : IsGrpPullback A Z x φ) {r k : ℕ}
    {a : Fin r → (Out.baseOver S' ⟶ A)} {s : Fin r → (Out.baseOver S ⟶ Z)}
    (h : ∀ i, (a i).left ≫ φ = x ≫ (s i).left) {T : Over S'} (u : T ⟶ Out.baseOver S')
    (t : Over.mk (T.hom ≫ x) ⟶ Out.baseOver S)
    (hb : ∀ z : T ⟶ A, z ^ k = 1 → ∃! c : Fin r → ZMod k, Out.linComb (fun i => u ≫ a i) (fun i => (c i).val) = z)
    (z : Over.mk (T.hom ≫ x) ⟶ Z) (hz : z ^ k = 1) :
    ∃! c : Fin r → ZMod k, Out.linComb (fun i => t ≫ s i) (fun i => (c i).val) = z := by
  have inj : Function.Injective (pushHom hφ T) := fun y y' e =>
    Over.OverMorphism.ext (hφ.1.hom_ext (congrArg (fun z => z.left) e) ((Over.w y).trans (Over.w y').symm))
  obtain ⟨z, rfl⟩ := GrpDense.pushPt_surjective hφ.1 T z
  change pushHom hφ T z ^ k = 1 at hz
  rw [← map_pow, map_eq_one_iff _ inj] at hz
  have key : ∀ e : Fin r → ℕ, Out.linComb (fun i => t ≫ s i) e =
      pushHom hφ T (Out.linComb (fun i => u ≫ a i) e) := fun e => by
    simp only [Out.linComb, map_list_prod, List.map_ofFn]
    congr 2
    funext i
    rw [comp_eq_pushPt hφ.1.w (h i) u t]
    change (pushHom hφ T (u ≫ a i)) ^ e i = pushHom hφ T ((u ≫ a i) ^ e i)
    exact (map_pow (pushHom hφ T) _ _).symm
  simp only [key]
  change ∃! c : Fin r → ZMod k, _ = pushHom hφ T z
  simp only [inj.eq_iff]
  exact hb z hz

theorem lab_single {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
    (t : TObj g k J b s) (i : Fin (2 * g)) : t.lab (Pi.single i 1) = t.pt i := by
  have := t.ab.comm
  rw [TObj.lab, Out.linComb, List.prod_ofFn, Finset.prod_eq_single i]
  · rw [Pi.single_eq_same, ← Nat.cast_one, ZMod.val_natCast, ← pow_eq_pow_mod _ (t.torsion i), pow_one]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, ZMod.val_zero, pow_zero]
  · simp

theorem lab_zero {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
    (t : TObj g k J b s) : t.lab 0 = 1 := by
  have := t.ab.comm
  rw [TObj.lab, Out.linComb, List.prod_ofFn]
  simp

theorem one_left {A : Over S} [GrpObj A] : (1 : Out.baseOver S ⟶ A).left = (η[A]).left :=
  Category.id_comp _

end GlobalTheory.DensePol

namespace GlobalTheory

open DensePol

theorem exists_polAV_of_veryDense_fibres :
    Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (I : Ideal (MvPolynomial (Ix g ((n ^ j) ^ 2)) R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R) (m : Z ⊗ Z ⟶ Z) (F : Option J → (Z ⟶ Z)), VeryDense (objPrimes b Mat κ β v) → (ProjRep I Z.hom M th ∧ SmoothOfRelativeDimension g Z.hom ∧ GeometricallyConnected Z.hom ∧ (∀ h, SecCoord M th (sc h).left (p h))) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ φ : t'.A.left ⟶ Z.left, (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ φ₂ : (t'.A ⊗ t'.A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[t'.A]).left ≫ φ) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), t'.Shape Mat κ → (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ i : Option J, φ ≫ (F i).left = (i.elim (𝟙 t'.A)⁻¹ t'.act : t'.A ⟶ t'.A).left ≫ φ) → ∃ (P : Out.PolAV (Sp R)) (act : J → (P.A ⟶ P.A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ P.A)), (P.g = g ∧ (∀ i, IsMonHom (act i)) ∧ (∀ i, Q i ^ (n ^ j) = 1) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ P.A), y ^ (n ^ j) = 1 → ∃! c : Ix g (n ^ j), Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp R)) ≫ Q i) (fun i => (c i).val) = y)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ ψ : t'.A.left ⟶ P.A.left, (IsGrpPullback t'.A P.A (spMap x) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ (n ^ j)).left ≫ ψ = (spMap x) ≫ (Q i).left) := by
  intro hL hL2 g J _ Mat κ n hn hodd
  refine ⟨2, fun j hj o _ b R _ _ _ β v Z I M th sc p m F hVD ⟨hrep, hsm, hgc, _⟩ hfib hm hF => ?_⟩
  have hn0 : n ≠ 0 := hn.ne_zero
  have hN0 : n ^ j ≠ 0 := pow_ne_zero _ hn0
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ hN0⟩
  have hun : IsUnit (n : R) := by
    have := b.unit.map β
    rw [map_natCast, Nat.cast_pow, Nat.cast_pow, isUnit_pow_iff two_ne_zero, isUnit_pow_iff (by omega)] at this
    exact this
  obtain ⟨-, hpr, hamp⟩ := GlobalTheory.ZM.projRep_projective_ample R _ I Z M th hrep
  have hD := dense_of_veryDense hVD
  have hs : Smooth Z.hom := SmoothOfRelativeDimension.smooth g _
  have s1 : Smooth (Out.baseOver (Sp R)).hom := inferInstanceAs (Smooth (𝟙 _))
  have h0 : ∀ {K : Type} [Field K] {x : R →+* K} (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β))
      {φ : t'.A.left ⟶ Z.left}, (∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) →
      (1 : Out.baseOver _ ⟶ t'.A).left ≫ φ = spMap x ≫ (sc 0).left := fun t' φ h => by
    have := h 0
    rwa [lab_zero, one_pow] at this
  have h1 : ∀ {K : Type} [Field K] {x : R →+* K} (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β))
      {φ : t'.A.left ⟶ Z.left}, (∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) →
      ∀ i, (t'.pt i ^ n ^ j).left ≫ φ = spMap x ≫ (sc (Pi.single i 1)).left := fun t' φ h i => by
    have := h (Pi.single i 1)
    rwa [lab_single] at this
  obtain ⟨_, -, hη, -, hab, hgp⟩ := grpObj_of_dense_fibres R Z m (F none) (sc 0) _ hD hs hpr hgc (by
    rintro q ⟨K, _, _, x, t', hx, hsh, hth⟩
    obtain ⟨φ, hφ⟩ := hfib K x t' hsh hth
    refine ⟨K, inferInstance, spMap x, t'.A, inferInstance, φ, mem_range_spMap x q hx, t'.ab.comm, hφ.1,
      hm K x t' φ hφ, ?_, ?_⟩
    · have := hF K x t' φ hsh hφ none
      rwa [Option.elim, Hom.inv_def, Category.id_comp] at this
    · rw [← one_left, h0 t' hφ.2.2.2])
  have := hab.comm
  have hhom : ∀ i, IsMonHom (F (some i)) := fun i => hL.rigidity _ Z Z hab hab _ (by
    rw [hη]
    refine FibreGrp.hom_ext_of_fibres (X := Out.baseOver (Sp R)) hD ?_
    rintro q ⟨K, _, _, x, t', hx, hsh, hth⟩
    obtain ⟨φ, hφ⟩ := hfib K x t' hsh hth
    refine ⟨_, spMap x, mem_range_spMap x q hx, fun T t => ?_⟩
    rw [← Category.assoc, comp_eq_pushPt hφ.1.w (h0 t' hφ.2.2.2) (toUnit T) t]
    have := t'.hom i
    have e : (toUnit T ≫ (1 : Out.baseOver _ ⟶ t'.A)) ≫ t'.act i = toUnit T ≫ (1 : Out.baseOver _ ⟶ t'.A) := by
      rw [Category.assoc, MonObj.one_comp]
    apply Over.OverMorphism.ext
    change (_ ≫ φ) ≫ (F (some i)).left = _ ≫ φ
    rw [Category.assoc, hF K x t' φ hsh hφ (some i), ← Category.assoc, ← Over.comp_left]
    exact congrArg (fun z => z.left ≫ φ) e)
  have htor : ∀ {K : Type} [Field K] {x : R →+* K} (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (i),
      (t'.pt i ^ n ^ j) ^ n ^ j = 1 := fun t' i => by
    have e : n ^ j * n ^ j = (n ^ j) ^ 2 := (pow_two _).symm
    rw [← pow_mul (t'.pt i), e, t'.torsion]
  have hQ : ∀ i, sc (Pi.single i 1) ^ n ^ j = 1 := fun i => by
    refine FibreGrp.hom_ext_of_fibres (X := Out.baseOver (Sp R)) hD ?_
    rintro q ⟨K, _, _, x, t', hx, hsh, hth⟩
    obtain ⟨φ, hφ⟩ := hfib K x t' hsh hth
    refine ⟨_, spMap x, mem_range_spMap x q hx, fun T t => ?_⟩
    rw [MonObj.comp_pow, MonObj.comp_one, comp_eq_pushPt hφ.1.w (h1 t' hφ.2.2.2 i) (toUnit T) t]
    change pushHom (hgp _ _ _ φ hφ.1 (hm K x t' φ hφ)) T _ ^ _ = 1
    rw [← map_pow]
    erw [← MonObj.comp_pow]
    rw [htor]
    erw [MonObj.comp_one]
    rw [map_one]
  have hB := torsion_basis_of_dense (Sp R) Z (n ^ j) (2 * g) (fun i => sc (Pi.single i 1)) _ hab
    (Nat.pos_of_ne_zero hN0) (by
      have := (hun.pow j).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      simpa using this) hQ hD (by
      rintro q ⟨K, _, _, x, t', hx, hsh, hth⟩
      obtain ⟨φ, hφ⟩ := hfib K x t' hsh hth
      have := t'.ab.comm
      refine ⟨K, inferInstance, inferInstance, 𝟙 _ ≫ spMap x, by simpa using mem_range_spMap x q hx, ?_⟩
      exact basis_push (hgp _ _ _ φ hφ.1 (hm K x t' φ hφ)) (h1 t' hφ.2.2.2) (T := Over.mk (𝟙 _)) _ _
        (basis_pow_linComb (pow_two _) (NeZero.ne _) _ t'.pt t'.torsion (t'.bij K (𝟙 _))))
  have hj2 : n ^ j = n ^ 2 * n ^ (j - 2) := by rw [← pow_add]; congr 1; omega
  obtain ⟨L, l1, l2, l3, l4, l5, l6⟩ := _root_.GlobalTheory.MulDescent.exists_polarisation_of_veryDense hL hL2 R Z g (n ^ 2) M _
    (fun i => (sc (Pi.single i 1) ^ n ^ (j - 2) : Out.baseOver (Sp R) ⟶ Z)) hab hsm hodd.pow
    (by simpa using hun.pow 2) hrep.1 hamp hVD
    (fun i => by
      have e : n ^ (j - 2) * n ^ 2 = n ^ j := by rw [mul_comm, ← hj2]
      have : (sc (Pi.single i 1) ^ n ^ (j - 2)) ^ n ^ 2 = 1 := by rw [← pow_mul, e, hQ]
      exact this)
    (fun K _ _ x => basis_pow_linComb hj2 hN0 _ _ hQ (hB K x))
    (by
      rintro q ⟨K, _, _, x, t', hx, hsh, hth⟩
      obtain ⟨φ, hφ⟩ := hfib K x t' hsh hth
      exact ⟨K, inferInstance, inferInstance, x, t'.pol, φ, hx, hgp _ _ _ φ hφ.1 (hm K x t' φ hφ), hφ.2.2.1⟩)
  refine ⟨{ A := Z, isAb := hab, g := g, smoothDim := hsm, L := L, isLB := l1, rigid := l2, sym := l3,
            ample := l4, ktriv := l5 }, fun i => F (some i), fun i => sc (Pi.single i 1),
    ⟨rfl, hhom, hQ, hB⟩, fun K _ _ x t' hsh hth => ?_⟩
  obtain ⟨φ, hφ⟩ := hfib K x t' hsh hth
  have hg := hgp _ _ _ φ hφ.1 (hm K x t' φ hφ)
  exact ⟨φ, hg, l6 K x t'.pol φ hg hφ.2.2.1, fun i => (hF K x t' φ hsh hφ (some i)).symm, h1 t' hφ.2.2.2⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelFamilyLocalisedCyclotomicIntegers
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.SiegelRingChange

noncomputable section
namespace GlobalTheory.SiegelFamilyBaseChange

theorem pb_iff {h k : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
    {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''} {c : SiegPre h k ζ s}
    {c' : SiegPre h k ζ' s'} {f : S' ⟶ S} (H : SiegPB c' c f) (c'' : SiegPre h k ζ'' s'') (f' : S'' ⟶ S') :
    SiegPB c'' c' f' ↔ SiegPB c'' c (f' ≫ f) :=
  (GlobalTheory.SiegelPullComp.id_comp_cancel h k B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f').2 H

theorem quasiCompact_of_isQProjOver {o : Type} [CommRing o] {X : Scheme.{0}} {f : X ⟶ Sp o} (h : IsQProjOver f) :
    QuasiCompact f := by
  obtain ⟨N, i, -, hi, rfl⟩ := h
  have : IsProper (PSpace.str o N) := isProper_str o N
  infer_instance

theorem injective_of_isAlgebraic {o O : Type} [CommRing o] [IsDomain o] [CommRing O] [CharZero O]
    (ha : Algebra.IsAlgebraic ℤ o) (ψ : o →+* O) : Function.Injective ψ := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  refine Ideal.comap_ne_bot_of_algebraic_mem (I := RingHom.ker ψ) hx0 hx (ha.1 x) ?_
  rw [eq_bot_iff]
  intro n hn
  simpa [Ideal.mem_comap, RingHom.mem_ker] using hn

theorem dense_generic {o O : Type} [CommRing o] [CommRing O] [IsDomain O] (ψ : o →+* O)
    (hψ : Function.Injective ψ) : Dense {x : Sp O | (spMap ψ x).asIdeal = ⊥} := by
  let x₀ : PrimeSpectrum O := ⟨⊥, Ideal.isPrime_bot⟩
  have hx₀ : Dense ({x₀} : Set (PrimeSpectrum O)) := by
    rw [dense_iff_closure_eq, PrimeSpectrum.closure_singleton]
    simp [x₀]
  refine Dense.mono (s₁ := ({x₀} : Set (Sp O))) ?_ hx₀
  rintro x rfl
  exact Ideal.comap_bot_of_injective ψ hψ

variable {h k : ℕ} {o B : Type} [CommRing o] [CommRing B] {ζ : o} {ζ' : B}

theorem rep_baseChange (F : SFam h k ζ) (j : o →+* B) (hj : j ζ = ζ')
    (U : SiegPre h k ζ' (pullback.snd F.s (spMap j))) (hU : SiegPB U F.univ (pullback.fst F.s (spMap j)))
    {S : Scheme.{0}} (s' : S ⟶ Sp B) (c : SiegPre h k ζ' s') (hr : IsReduced S)
    (hd : Dense {x : S | ((s' ≫ spMap j) x).asIdeal = ⊥}) (hp : c.Principal) :
    ∃ f : S ⟶ pullback F.s (spMap j), f ≫ pullback.snd F.s (spMap j) = s' ∧ SiegPB c U f := by
  obtain ⟨g, hg, H⟩ := F.rep S _ (down j hj c) hr hd hp
  refine ⟨pullback.lift g s' hg, pullback.lift_snd _ _ _, (pb_iff hU c _).2 ?_⟩
  rw [pullback.lift_fst]
  exact H

theorem inj_baseChange (F : SFam h k ζ) (j : o →+* B) (hj : j ζ = ζ')
    (U : SiegPre h k ζ' (pullback.snd F.s (spMap j))) (hU : SiegPB U F.univ (pullback.fst F.s (spMap j)))
    {R : Type} [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ pullback F.s (spMap j)) (s' : Sp R ⟶ Sp B)
    (c : SiegPre h k ζ' s') (e : x ≫ pullback.snd F.s (spMap j) = y ≫ pullback.snd F.s (spMap j))
    (hx : SiegPB c U x) (hy : SiegPB c U y) : x = y := by
  refine pullback.hom_ext ?_ e
  refine F.inj R _ _ _ (down j hj c) ?_ ((pb_iff hU c _).1 hx) ((pb_iff hU c _).1 hy)
  simp only [Category.assoc, pullback.condition]
  rw [reassoc_of% e]

theorem exists_siegelFamily : Out.Laws → Out.Laws2 → ∀ (h k p : ℕ) (o : Type) [CommRing o] (ζ : o) (j : o →+* ZP p k), Odd k → 3 ≤ k → p.Prime → Function.Injective j → j ζ = zetaZP p k → (∀ (K : Type) [Field K] (y : Sp (DualNumber K) ⟶ Sp (ZP p k)), y = constPt y) → Algebra.IsAlgebraic ℤ o → SFam h k ζ → ∃ Ag : SiegelFamily h p k, SRep Ag := by
  intro L₁ L₂ h k p o _ ζ j hodd hk hpp hinj hj hc ha F
  have hpull := siegPre_pull_ringChange h k o (ZP p k) ζ (zetaZP p k) j F.X (pullback F.s (spMap j)) F.s
    (pullback.snd F.s (spMap j)) (pullback.fst F.s (spMap j)) hj pullback.condition
  obtain ⟨U, hU⟩ := hpull.1 F.univ
  have hUp : U.Principal := hpull.2.1 _ _ hU F.princ
  have := F.smooth
  have := F.isSeparated
  have := quasiCompact_of_isQProjOver F.qproj
  have : IsDomain o := hinj.isDomain j
  have hsm : SmoothOfRelativeDimension (h * (h + 1) / 2) (pullback.snd F.s (spMap j)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) F.smooth
  refine ⟨⟨pullback F.s (spMap j), pullback.snd F.s (spMap j), hsm, inferInstance, U, hUp, ?_, ?_⟩,
    (inferInstance : IsSeparated (pullback.snd F.s (spMap j))), ?_⟩
  · intro C O _ _ _ _ _ _ _ _ hO hpn β c hgen hsp
    have hp : c.Principal := _root_.GlobalTheory.PrincipalIntegral.principal_of_generic_of_ample_special L₁ L₂ h k hodd hk _ _ C O hO p hpp hpn β c hgen hsp
    have : IsDomain O := hO.1.isDomain (algebraMap O C)
    have : CharZero O := RingHom.charZero (algebraMap O C)
    refine rep_baseChange F j hj U hU _ c inferInstance ?_ hp
    rw [← spMap_comp']
    exact dense_generic _ (injective_of_isAlgebraic ha _)
  · intro K _ x c h₁ h₂
    refine inj_baseChange F j hj U hU x _ _ c ?_ h₁ h₂
    rw [hc K (x ≫ _)]
    simp only [constPt, Category.assoc]
  · intro S s' c hr hd hp
    refine rep_baseChange F j hj U hU s' c hr (hd.mono fun x hx => ?_) hp
    have hx' : (s' x).asIdeal = ⊥ := hx
    change ((s' x).asIdeal).comap j = ⊥
    rw [hx']
    exact Ideal.comap_bot_of_injective j hinj

end GlobalTheory.SiegelFamilyBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUniformisationOfAbelianVarietyUniformisati
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem familyUnif_of_thetaUnif : ThetaUnifAV → Out.Laws → N1c := fun hU hL =>
  GlobalTheory.familyUnif_of_parts GlobalTheory.datum_exists_period
    (GlobalTheory.PointUnif.exists_uniformisation_at_point_closed hU hL) (GlobalTheory.Moduli.exists_point_of_isPeriod hU hL) (GlobalTheory.UnifPoint.point_eq_iff_isometry_closed hU hL)
    (GlobalTheory.exists_local_period_lift hU hL) (_root_.GlobalTheory.isHolTo_point_and_exp_of_isHolPeriods hU hL)
    (GlobalTheory.FiniteClasses.finite_image_of_locally_constant_on_holomorphic_families GlobalTheory.SubfieldChart.exists_holomorphic_chart)
    (GlobalTheory.exists_thetaFrame_family hU hL)
    (GlobalTheory.SimMult.exists_sim_trivial_of_mult GlobalTheory.SimAlg.sim_group GlobalTheory.exists_sim_lift)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyCmModuliOfDeeperLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory.ZM

theorem moduli_of_deeper_level : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (Moduli D l₂) → Nonempty (Moduli D l) := by
  intro L L2 hT E _ _ _ H D l l₂ hD hl ⟨Xo₂⟩
  obtain ⟨Q⟩ := _root_.GlobalTheory.nonempty_levelQuot L L2 hT E H D l l₂ Xo₂ hD hl
  exact ⟨{ X := Q.X, s := Q.s, qproj := Q.qproj, smooth := Q.smooth, univ := Q.univ,
           rep := _root_.GlobalTheory.levelQuot_represents L L2 E H D l l₂ Xo₂ Q hD hl,
           unram := _root_.GlobalTheory.levelQuot_unram L L2 E H D l l₂ Xo₂ Q hD hl }⟩
end GlobalTheory.ZM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TwistAmpleBundleTranslationBundleIsoTranslateStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_ampleBundle_translationBundle_iso_translate : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (y : 𝟙_ (Over (Sp K)) ⟶ P.A), M.IsLB → Out.RelAmple P.A M → ∃ x : 𝟙_ (Over (Sp K)) ⟶ P.A, LBIso (LB.div M (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, ((toUnit P.A ≫ y) * 𝟙 P.A).left] ![1, -1])) (M.pull ((toUnit P.A ≫ x) * 𝟙 P.A).left) := by
  first | exact @GlobalTheory.TwistIsTranslate.twist_iso_translate | exact GlobalTheory.TwistIsTranslate.twist_iso_translate | (intros; apply GlobalTheory.TwistIsTranslate.twist_iso_translate <;> assumption)
end

