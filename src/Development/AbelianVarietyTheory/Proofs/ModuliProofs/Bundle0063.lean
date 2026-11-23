module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.NearBuild

variable {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {R R' : Type} [CommRing R] [CommRing R']

abbrev loc (f : R) : R →+* Localization.Away f := algebraMap R (Localization.Away f)

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (x : B →+* C) (y : A →+* B) :
    spMap (x.comp y) = spMap x ≫ spMap y := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

section
variable (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ)
  (β : o →+* R) (v : Ix g (N' ^ 2) → R)

def Good {K : Type} [Field K] (x : R →+* K) {s : Sp K ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) : Prop :=
  s = spMap x ≫ spMap β ∧ t.Shape Mat κ ∧ t.HasTh (𝟙 _) (fun a => x (v a))

def Den (q₀ : Ideal R) : Prop := DenseP (objPrimes b Mat κ β v) ∧ q₀ ∈ objPrimes b Mat κ β v

def Concl : Prop :=
  ∃ t : TObj g (N' ^ 2) J b (spMap β), t.HasTh (𝟙 _) v ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t' : TObj g (N' ^ 2) J b s),
      Good b Mat κ β v x t' → TMap t' t (spMap x)

def NearC (q₀ : Ideal R) : Prop :=
  ∃ f : R, f ∉ q₀ ∧ Concl b Mat κ ((loc f).comp β) (fun a => loc f (v a))

def FibData (m : ℕ) (p : Ix g (N' ^ 2) → Ix g (N' ^ 2) → R) {Hh : Type} (hh : Hh → Ix g (N' ^ 2)) (Q : Polynomial ℚ)
    (d : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s),
    Good b Mat κ β v x t →
    ∃ (σ : Ix g (N' ^ 2) → LB.Sec (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 _))))
      (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) K)), t.Emb m (Over.mk (𝟙 _)) σ ∧
      ProjRep I (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ ∧ (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) ∧
      CutBy I Q d (fun h a => x (p (hh h) a)) ∧
      ∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ N')).left (fun a => x (p h a))
end

def Fib {b : TBase o (N' ^ 2)} (m : ℕ) {Z : Over (Sp R)} (M : LB Z.left) (th : Ix g (N' ^ 2) → M.Sec)
    (sc : Ix g (N' ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) {K : Type} [Field K] (x : R →+* K) {s : Sp K ⟶ Sp o}
    (t : TObj g (N' ^ 2) J b s) (φ : t.A.left ⟶ Z.left) : Prop :=
  IsPullback φ t.A.hom Z.hom (spMap x) ∧
    (∃ σ, t.Emb m (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t.A).left)
      (w : Ix g (N' ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ φ) w) ∧
    LBIso (lbPow t.L (m ^ 2)) (M.pull φ) ∧ ∀ h, (t.lab h ^ N').left ≫ φ = spMap x ≫ (sc h).left

section
variable (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ)
  (β : o →+* R) (v : Ix g (N' ^ 2) → R) (m : ℕ) {Z : Over (Sp R)} (M : LB Z.left) (th : Ix g (N' ^ 2) → M.Sec)
  (sc : Ix g (N' ^ 2) → (Out.baseOver (Sp R) ⟶ Z))

def Fam : Prop :=
  (∃ (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) R)) (p : Ix g (N' ^ 2) → Ix g (N' ^ 2) → R),
    ProjRep I Z.hom M th ∧ ∀ h, SecCoord M th (sc h).left (p h)) ∧ Flat Z.hom ∧
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s),
    Good b Mat κ β v x t → ∃ φ, Fib m M th sc x t φ

def AddOk (ρ : R →+* R') {Z' : Over (Sp R')} (π : Z'.left ⟶ Z.left) (mu : Z' ⊗ Z' ⟶ Z') : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R' →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s)
    (φ : t.A.left ⟶ Z'.left), Good b Mat κ β v (x.comp ρ) t → Fib m M th sc (x.comp ρ) t (φ ≫ π) →
    φ ≫ Z'.hom = t.A.hom ≫ spMap x →
    ∀ φ₂ : (t.A ⊗ t.A).left ⟶ (Z' ⊗ Z').left, IsSquare φ φ₂ → φ₂ ≫ mu.left = (μ[t.A]).left ≫ φ

def EndOk (ρ : R →+* R') {Z' : Over (Sp R')} (π : Z'.left ⟶ Z.left) (i : Option J) (F : Z' ⟶ Z') : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R' →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s)
    (φ : t.A.left ⟶ Z'.left), Good b Mat κ β v (x.comp ρ) t → Fib m M th sc (x.comp ρ) t (φ ≫ π) →
    φ ≫ Z'.hom = t.A.hom ≫ spMap x →
    φ ≫ F.left = (i.elim (𝟙 t.A)⁻¹ t.act : t.A ⟶ t.A).left ≫ φ

def AddAt (mu : Z ⊗ Z ⟶ Z) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s)
    (φ : t.A.left ⟶ Z.left), Good b Mat κ β v x t → Fib m M th sc x t φ →
    ∀ φ₂ : (t.A ⊗ t.A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ mu.left = (μ[t.A]).left ≫ φ

def EndAt (i : Option J) (F : Z ⟶ Z) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s)
    (φ : t.A.left ⟶ Z.left), Good b Mat κ β v x t → Fib m M th sc x t φ →
    φ ≫ F.left = (i.elim (𝟙 t.A)⁻¹ t.act : t.A ⟶ t.A).left ≫ φ
end

def Lab (k : ℕ) {S : Scheme.{0}} (A : Over S) [GrpObj A] (act : J → (A ⟶ A))
    (Q : Fin (2 * g) → (Out.baseOver S ⟶ A)) : Prop :=
  (∀ i, IsMonHom (act i)) ∧ (∀ i, Q i ^ k = 1) ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A), y ^ k = 1 →
      ∃! c : Ix g k, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ Q i)
        (fun i => (c i).val) = y

def GLies {b : TBase o (N' ^ 2)} {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (act : J → (A ⟶ A))
    (Q : Fin (2 * g) → (Out.baseOver S ⟶ A)) (y : S' ⟶ S) {s : S' ⟶ Sp o} (t : TObj g (N' ^ 2) J b s)
    (ψ : t.A.left ⟶ A.left) : Prop :=
  IsGrpPullback t.A A y ψ ∧ (∀ i, (t.act i).left ≫ ψ = ψ ≫ (act i).left) ∧
    ∀ i, (t.pt i ^ N').left ≫ ψ = y ≫ (Q i).left

section
variable (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ)
  (β : o →+* R) (v : Ix g (N' ^ 2) → R)

def GrpFam (m : ℕ) (A : Over (Sp R)) [GrpObj A] (M : LB A.left) (act : J → (A ⟶ A))
    (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)) : Prop :=
  IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧ M.IsLB ∧ Out.RelAmple A M ∧ Lab N' A act Q ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s),
      Good b Mat κ β v x t → ∃ ψ, GLies A act Q (spMap x) t ψ ∧ LBIso (lbPow t.L (m ^ 2)) (M.pull ψ)

def PolFam (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A))
    (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)) : Prop :=
  IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧ L.IsLB ∧ Out.Rigidified A L ∧ Out.Sym A L ∧
    Out.RelAmple A L ∧ Lab N' A act Q ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s),
      Good b Mat κ β v x t → ∃ ψ, GLies A act Q (spMap x) t ψ ∧ LBIso t.L (L.pull ψ)

variable {b Mat κ β v}

theorem good_comp (ρ : R →+* R') {K : Type} [Field K] (x : R' →+* K) {s : Sp K ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) :
    Good b Mat κ (ρ.comp β) (fun a => ρ (v a)) x t ↔ Good b Mat κ β v (x.comp ρ) t := by
  simp only [Good, spMap_comp, Category.assoc, RingHom.comp_apply]

theorem mem_objPrimes {q : Ideal R} : q ∈ objPrimes b Mat κ β v ↔
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s),
      RingHom.ker x = q ∧ Good b Mat κ β v x t := by
  constructor
  · rintro ⟨K, hF, hA, x, t, hk, hs, hth⟩
    exact ⟨K, hF, hA, x, _, t, hk, rfl, hs, hth⟩
  · rintro ⟨K, hF, hA, x, s, t, hk, ⟨rfl, hs, hth⟩⟩
    exact ⟨K, hF, hA, x, t, hk, hs, hth⟩

theorem isPrime_of_mem {q : Ideal R} (h : q ∈ objPrimes b Mat κ β v) : q.IsPrime := by
  obtain ⟨K, hF, -, x, -, rfl, -⟩ := h
  exact RingHom.ker_isPrime x

theorem exists_mem_loc {q : Ideal R} (h : q ∈ objPrimes b Mat κ β v) {f : R} (hf : f ∉ q) :
    ∃ q₁ ∈ objPrimes b Mat κ ((loc f).comp β) (fun a => loc f (v a)), q₁.comap (loc f) = q := by
  obtain ⟨K, hF, hA, x, s, t, hk, hg⟩ := mem_objPrimes.1 h
  have hu : IsUnit (x f) := by
    refine isUnit_iff_ne_zero.2 fun h0 => hf ?_
    rw [← hk]
    exact h0
  let y : Localization.Away f →+* K := IsLocalization.Away.lift f hu
  have hy : y.comp (loc f) = x := IsLocalization.Away.lift_comp f hu
  refine ⟨RingHom.ker y, mem_objPrimes.2 ⟨K, hF, hA, y, s, t, rfl, ?_⟩, ?_⟩
  · rw [good_comp, hy]
    exact hg
  · rw [RingHom.comap_ker, hy, hk]

theorem densePrimes_localization (h : DenseP (objPrimes b Mat κ β v)) (f : R) :
    DenseP (objPrimes b Mat κ ((loc f).comp β) (fun a => loc f (v a))) := by
  intro g hg
  obtain ⟨⟨a, c⟩, hc⟩ := IsLocalization.surj (Submonoid.powers f) g
  have hfa : f * a = 0 := by
    apply h
    intro p hp _
    by_cases hfp : f ∈ p
    · exact p.mul_mem_right a hfp
    · obtain ⟨q₁, hq₁, hcomap⟩ := exists_mem_loc hp hfp
      have hgq : g ∈ q₁ := hg q₁ hq₁ (isPrime_of_mem hq₁)
      have haq : algebraMap R (Localization.Away f) a ∈ q₁ := by
        rw [← hc]
        exact q₁.mul_mem_right _ hgq
      have : a ∈ p := by
        rw [← hcomap]
        exact haq
      exact p.mul_mem_left f this
  have hloc : algebraMap R (Localization.Away f) a = 0 := by
    have h1 := congrArg (algebraMap R (Localization.Away f)) hfa
    rw [map_mul, map_zero] at h1
    exact (IsLocalization.Away.algebraMap_isUnit f).mul_right_eq_zero.1 h1
  have hcu : IsUnit (algebraMap R (Localization.Away f) (c : R)) :=
    IsLocalization.map_units (Localization.Away f) c
  simp only at hc
  rw [hloc] at hc
  exact hcu.mul_left_eq_zero.1 hc

theorem Den.loc {q₀ : Ideal R} (h : Den b Mat κ β v q₀) {f : R} (hf : f ∉ q₀) :
    ∃ q₁, Den b Mat κ ((loc f).comp β) (fun a => loc f (v a)) q₁ ∧ q₁.comap (loc f) = q₀ := by
  obtain ⟨q₁, hq₁, hcomap⟩ := exists_mem_loc h.2 hf
  exact ⟨q₁, ⟨densePrimes_localization h.1 f, hq₁⟩, hcomap⟩

theorem FibData.comp {m : ℕ} {p : Ix g (N' ^ 2) → Ix g (N' ^ 2) → R} {Hh : Type} {hh : Hh → Ix g (N' ^ 2)}
    {Q : Polynomial ℚ} {d : ℕ} (h : FibData b Mat κ β v m p hh Q d) (ρ : R →+* R') :
    FibData b Mat κ (ρ.comp β) (fun a => ρ (v a)) m (fun c a => ρ (p c a)) hh Q d := by
  intro K _ _ x s t hg
  exact h K (x.comp ρ) s t ((good_comp ρ x t).1 hg)

theorem dense_of_denseP {P : Set (Ideal R)} (h : DenseP P) : Dense {p : Sp R | p.asIdeal ∈ P} := by
  have hv : PrimeSpectrum.vanishingIdeal {p : PrimeSpectrum R | p.asIdeal ∈ P} = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_bot]
    refine h a fun p hp hpr => ?_
    exact (PrimeSpectrum.mem_vanishingIdeal _ _).1 ha ⟨p, hpr⟩ hp
  have hc : closure {p : PrimeSpectrum R | p.asIdeal ∈ P} = Set.univ := by
    rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hv]
    simp
  exact dense_iff_closure_eq.2 hc
end

end GlobalTheory.ZM.NearBuild
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAdaptedLieBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.AdaptedBasis

private theorem isSemisimple_ringOfIntegers_action {E K V : Type} [Field E] [NumberField E] [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] (r : 𝓞 E →+* Module.End K V) (a : 𝓞 E) : (r a).IsSemisimple := by
  have hi : IsIntegral ℤ a := RingOfIntegers.isIntegral a
  have hq : minpoly ℚ (algebraMap (𝓞 E) E a) = (minpoly ℤ a).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions ℚ E hi
  have hsep : (minpoly ℚ (algebraMap (𝓞 E) E a)).Separable := Algebra.IsSeparable.isSeparable ℚ _
  rw [hq] at hsep
  have hK := hsep.map (f := algebraMap ℚ K)
  rw [Polynomial.map_map,
    show (algebraMap ℚ K).comp (algebraMap ℤ ℚ) = algebraMap ℤ K from RingHom.ext_int _ _] at hK
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hK.squarefree ?_
  rw [Polynomial.aeval_map_algebraMap]
  have hz := Polynomial.aeval_algHom_apply r.toIntAlgHom a (minpoly ℤ a)
  rw [minpoly.aeval, map_zero] at hz
  exact hz

private theorem exists_ringHom_eq_eigenvalue {R K V : Type} [CommRing R] [Field K] [AddCommGroup V] [Module K V]
    (r : R →+* Module.End K V) {v : V} (hv : v ≠ 0) (χ : R → K) (h : ∀ a, r a v = χ a • v) :
    ∃ t : R →+* K, ∀ a, t a = χ a := by
  have inj : Function.Injective fun c : K => c • v := smul_left_injective K hv
  refine ⟨{ toFun := χ
            map_one' := inj ?_
            map_mul' := fun a b => inj ?_
            map_zero' := inj ?_
            map_add' := fun a b => inj ?_ }, fun _ => rfl⟩
  · show χ 1 • v = (1 : K) • v
    rw [← h, map_one, Module.End.one_apply, one_smul]
  · show χ (a * b) • v = (χ a * χ b) • v
    rw [← h, map_mul, Module.End.mul_apply, h b, map_smul, h a, smul_smul, mul_comm]
  · show χ 0 • v = (0 : K) • v
    rw [← h, map_zero, LinearMap.zero_apply, zero_smul]
  · show χ (a + b) • v = (χ a + χ b) • v
    rw [← h, map_add (f := _), LinearMap.add_apply, h a, h b, add_smul]

theorem exists_eigenbasis {E K V : Type} [Field E] [NumberField E] [Field K] [IsAlgClosed K] [CharZero K]
    [AddCommGroup V] [Module K V] [Module.Finite K V] (r : 𝓞 E →+* Module.End K V) :
    ∃ (g : ℕ) (b : Module.Basis (Fin g) K V) (ty : Fin g → (𝓞 E →+* K)), ∀ a j, r a (b j) = ty j a • b j := by
  classical
  have hc : ∀ a c : 𝓞 E, Commute (r a) (r c) := fun a c => by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
  have hmaps : ∀ (a c : 𝓞 E) (z : K),
      Set.MapsTo (r a) ((r c).maxGenEigenspace z) ((r c).maxGenEigenspace z) :=
    fun a c z => Module.End.mapsTo_maxGenEigenspace_of_comm (hc c a) z
  let W : (𝓞 E → K) → Submodule K V := fun χ => ⨅ a, (r a).maxGenEigenspace (χ a)
  have hint : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun a => r a) hmaps)
      (Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo (fun a => r a) hmaps
        fun a => Module.End.iSup_maxGenEigenspace_eq_top (r a))
  let B := hint.collectedBasis fun χ => Module.finBasis K (W χ)
  have : Finite (Σ χ, Fin (Module.finrank K (W χ))) := Module.Finite.finite_basis B
  let _ : Fintype (Σ χ, Fin (Module.finrank K (W χ))) := Fintype.ofFinite _
  have heig : ∀ s : (Σ χ, Fin (Module.finrank K (W χ))), ∀ a, r a (B s) = s.1 a • B s := by
    intro s a
    have hm : B s ∈ W s.1 := hint.collectedBasis_mem _ s
    have hm' : B s ∈ (r a).maxGenEigenspace (s.1 a) := (Submodule.mem_iInf _).1 hm a
    rw [(isSemisimple_ringOfIntegers_action r a).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at hm'
    exact Module.End.mem_eigenspace_iff.1 hm'
  choose t ht using fun s : (Σ χ, Fin (Module.finrank K (W χ))) =>
    exists_ringHom_eq_eigenvalue r (B.ne_zero s) s.1 (heig s)
  let e := Fintype.equivFin (Σ χ, Fin (Module.finrank K (W χ)))
  refine ⟨Fintype.card _, B.reindex e, fun j => t (e.symm j), fun a j => ?_⟩
  rw [Module.Basis.reindex_apply, ht, heig]

open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD tvec tmap IsUnivChart)

variable {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] {n : ℕ}
  {x : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)


include hx in
theorem exists_tangent_action {O : Type} [CommRing O] (act : OAct O G) :
    ∃ r : O →+* Module.End k (Fin n → k), ∀ a c, tvec (x := x) (r a c) = tvec (x := x) c ≫ act.act a := by
  have : ∀ a, IsMonHom (act.act a) := act.hom
  have hadd : ∀ a c, Chart.tmap hx (act.act (a + c)) = Chart.tmap hx (act.act a) + Chart.tmap hx (act.act c) :=
    fun a c => LinearMap.ext fun v => Chart.tvec_inj hx (by
      rw [LinearMap.add_apply, Chart.tvec_add hx, Chart.tvec_tmap, Chart.tvec_tmap, Chart.tvec_tmap, act.add,
        MonObj.comp_mul])
  refine ⟨{ toFun := fun a => Chart.tmap hx (act.act a)
            map_one' := ?_
            map_mul' := fun a c => ?_
            map_zero' := ?_
            map_add' := hadd }, fun a c => Chart.tvec_tmap hx _ c⟩
  · refine LinearMap.ext fun v => Chart.tvec_inj hx ?_
    show tvec (x := x) (Chart.tmap hx (act.act 1) v) = tvec (x := x) v
    rw [Chart.tvec_tmap, act.one, Category.comp_id]
  · refine LinearMap.ext fun v => Chart.tvec_inj hx ?_
    show tvec (x := x) (Chart.tmap hx (act.act (a * c)) v) =
      tvec (x := x) (Chart.tmap hx (act.act a) (Chart.tmap hx (act.act c) v))
    rw [Chart.tvec_tmap, Chart.tvec_tmap, Chart.tvec_tmap, mul_comm a c, act.mul, Category.assoc]
  · have h00 := hadd 0 0
    rw [add_zero] at h00
    show Chart.tmap hx (act.act 0) = 0
    exact add_left_cancel (by rw [add_zero]; exact h00.symm :
      Chart.tmap hx (act.act 0) + Chart.tmap hx (act.act 0) = Chart.tmap hx (act.act 0) + 0)

private theorem tvec_sum' {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] {n : ℕ}
    {x : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin n) m) ⟶ G} (hx : IsUnivChart G n x) :
    ∀ {N : ℕ} (f : Fin N → Fin n → k), (List.ofFn fun i => tvec (x := x) (f i)).prod = tvec (x := x) (∑ i, f i) := by
  have h0 : tvec (x := x) 0 = 1 := by
    have h := Chart.tvec_add hx (0 : Fin n → k) 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  intro N f
  induction N with
  | zero => simp [h0]
  | succ N ih => rw [List.ofFn_succ, List.prod_cons, ih (fun i => f i.succ), Fin.sum_univ_succ, Chart.tvec_add hx]


include hx in
theorem isLieComb_tvec_iff {N : ℕ} (b : Fin N → Fin n → k) (c : Fin n → k) (d : Fin N → k) :
    IsLieComb d (fun i => tvec (x := x) (b i)) (tvec (x := x) c) ↔ c = ∑ i, d i • b i := by
  unfold IsLieComb
  have hs : ∀ i, tvec (x := x) (d i • b i) = Chart.spMap (scaleD (d i)) ≫ tvec (x := x) (b i) :=
    fun i => Chart.tvec_smul hx (d i) (b i)
  constructor
  · rintro ⟨u, hu, hw⟩
    have hu' : u = fun i => tvec (x := x) (d i • b i) := by
      funext i
      apply Over.OverMorphism.ext
      rw [hu i, hs i, Over.comp_left]
      all_goals rfl
    subst hu'
    rw [tvec_sum' hx] at hw
    exact Chart.tvec_inj hx hw
  · rintro rfl
    refine ⟨fun i => tvec (x := x) (d i • b i), fun i => ?_, (tvec_sum' hx _).symm⟩
    show (tvec (x := x) (d i • b i)).left = spMap (epsScaleR (d i)) ≫ (tvec (x := x) (b i)).left
    rw [hs i, Over.comp_left]
    all_goals rfl

end GlobalTheory.AdaptedBasis


open ReciprocityTheory.ChartRestriction.G.Chart (tvec) in
theorem GlobalTheory.exists_adapted_lieBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (act : OAct (𝓞 E) G) (ρ : K), Smooth G.hom → DetCond D act (𝟙 (Sp K)) ρ → ∃ (g : ℕ) (v : Fin g → (epsR K ⟶ G)) (ty : Fin g → (𝓞 E →+* K)), IsLieBasis v ∧ (∀ τ : 𝓞 E →+* K, (τ H.rt = ρ → Nat.card {i // ty i = τ} = D.p) ∧ (τ H.rt ≠ ρ → Nat.card {i // ty i = τ} = D.q)) ∧ ∀ a j, IsLieComb (fun i => Matrix.diagonal (fun i => ty i a) i j) v (v j ≫ act.act a) := by
  intro E _ _ _ H D K _ _ _ G _ _ act ρ hsm hdet
  unfold DetCond at hdet
  obtain ⟨n, x, hx⟩ := Chart.univChartLoc G
  obtain ⟨r, hr⟩ := GlobalTheory.AdaptedBasis.exists_tangent_action hx act
  obtain ⟨g, b, ty, hb⟩ := GlobalTheory.AdaptedBasis.exists_eigenbasis (E := E) r
  have : ∀ a, IsMonHom (act.act a) := act.hom
  have hT : ∀ w : epsR K ⟶ G, IsTangent w ↔ Chart.IsTan w := by
    intro w
    unfold IsTangent Chart.IsTan
    have e1 : (Chart.spMap (Chart.fstD K)).left = spMap (TrivSqZeroExt.fstHom K K K).toRingHom := rfl
    have e2 : (Chart.sp (R₀ := K) K).hom = 𝟙 _ := by
      first
      | rfl
      | (unfold Chart.sp; simp)
      | (simp [Chart.sp, Algebra.id.map_eq_id])
    constructor
    · intro h
      apply Over.OverMorphism.ext
      rw [Over.comp_left, Chart.one_left', e1, h, e2, Category.id_comp]
    · intro h
      have h' := congrArg Over.Hom.left h
      rw [Over.comp_left, Chart.one_left', e1, e2, Category.id_comp] at h'
      exact h'
  have hcomb : ∀ a j, IsLieComb (fun i => Matrix.diagonal (fun i => ty i a) i j)
      (fun i => tvec (x := x) (b i)) (tvec (x := x) (b j) ≫ act.act a) := by
    intro a j
    rw [← hr, hb, GlobalTheory.AdaptedBasis.isLieComb_tvec_iff hx]
    simp [Matrix.diagonal_apply, ite_smul]
  have hex : ∀ w : epsR K ⟶ G, Chart.IsTan w → ∃ c, w = tvec (x := x) c := by
    intro w hw
    exact ⟨Chart.tcoord hx w hw, Chart.tcoord_spec hx w hw⟩
  have hbasis : IsLieBasis (fun i => tvec (x := x) (b i)) := by
    unfold IsLieBasis
    refine ⟨fun i => (hT _).2 (Chart.isTan_tvec hx (b i)), fun w hw => ?_⟩
    obtain ⟨c, rfl⟩ := hex w ((hT w).1 hw)
    refine ⟨fun i => b.repr c i, ?_, fun e he => ?_⟩
    · show IsLieComb (fun i => b.repr c i) (fun i => tvec (x := x) (b i)) (tvec (x := x) c)
      rw [GlobalTheory.AdaptedBasis.isLieComb_tvec_iff hx]
      exact (b.sum_repr c).symm
    · have he' : IsLieComb e (fun i => tvec (x := x) (b i)) (tvec (x := x) c) := he
      rw [GlobalTheory.AdaptedBasis.isLieComb_tvec_iff hx] at he'
      funext i
      rw [he', b.repr_sum_self]
  have heig : ∀ i a, ((fun i => tvec (x := x) (b i)) i ≫ act.act a).left =
      spMap (epsScale (ty i a)) ≫ ((fun i => tvec (x := x) (b i)) i).left := by
    intro i a
    show (tvec (x := x) (b i) ≫ act.act a).left = spMap (epsScale (ty i a)) ≫ (tvec (x := x) (b i)).left
    rw [← hr, hb, Chart.tvec_smul hx, Over.comp_left]
    all_goals rfl
  have hmult := GlobalTheory.lieMult_of_eigenbasis K (𝓞 E) G act g _ ty hsm hbasis heig
  refine ⟨g, fun i => tvec (x := x) (b i), ty, hbasis, fun τ => ⟨fun h1 => ?_, fun h2 => ?_⟩, hcomb⟩
  · exact ((GlobalTheory.DetExtend.lieMult_iff_finrank act hx τ _).1 (hmult τ)).symm.trans
      ((GlobalTheory.DetExtend.lieMult_iff_finrank act hx τ _).1 ((hdet τ).1 h1))
  · exact ((GlobalTheory.DetExtend.lieMult_iff_finrank act hx τ _).1 (hmult τ)).symm.trans
      ((GlobalTheory.DetExtend.lieMult_iff_finrank act hx τ _).1 ((hdet τ).2 h2))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelWithOddPrimeFirstNumber
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem exists_prime_level :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H), ∃ n : ℕ, n.Prime ∧ Odd n ∧
      ∀ A₀ : ℕ, 0 < A₀ → ∃ l₀ l₂ : Level H, l₀.M = n ∧ l₀.A = A₀ ∧ l₀.Dvd l₂ ∧ l.Dvd l₂ := by
  intro E _ _ _ H l
  have hM1 : l.M ≠ 1 := by have := l.three_le; omega
  obtain ⟨n, hn, hnM⟩ := Nat.exists_prime_and_dvd hM1
  have hodd : Odd n := Odd.of_dvd_nat l.odd hnM
  have h3 : 3 ≤ n := by
    have h2 := hn.two_le
    rcases hodd with ⟨k, hk⟩
    omega
  refine ⟨n, hn, hodd, fun A₀ hA₀ => ?_⟩
  have hmap : (l.Mb ⊔ Ideal.span {(n : 𝓞 E)}).map (H.bar : 𝓞 E →+* 𝓞 E) =
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ⊔ Ideal.span {(n : 𝓞 E)} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast]
  have hMn : Ideal.span {(l.M : 𝓞 E)} ≤ Ideal.span {(n : 𝓞 E)} :=
    Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast hnM)
  refine ⟨⟨n, h3, hodd, l.Mb ⊔ Ideal.span {(n : 𝓞 E)}, ?_, ?_, ?_, A₀, hA₀⟩,
    ⟨l.M, l.three_le, l.odd, l.Mb, l.fromK, l.prod, l.coprime, Nat.lcm l.A A₀, Nat.lcm_pos l.A_pos hA₀⟩,
    rfl, rfl, ⟨hnM, le_sup_left, Nat.dvd_lcm_right _ _⟩, ⟨dvd_rfl, le_rfl, Nat.dvd_lcm_left _ _⟩⟩
  · apply le_antisymm
    · apply sup_le
      · refine l.fromK.le.trans (Ideal.span_mono ?_)
        intro a ha
        exact ⟨Ideal.mem_sup_left ha.1, ha.2⟩
      · refine Ideal.span_mono ?_
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        subst ha
        exact ⟨Ideal.mem_sup_right (Ideal.mem_span_singleton_self _), natCast_mem _ _⟩
    · exact Ideal.span_le.2 fun a ha => ha.1
  · rw [hmap, Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup, l.prod]
    set N : Ideal (𝓞 E) := Ideal.span {(n : 𝓞 E)}
    apply le_antisymm
    · refine sup_le (sup_le hMn ?_) (sup_le ?_ ?_) <;>
        first | exact Ideal.mul_le_left | exact Ideal.mul_le_right
    · calc N = N * (l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) := by rw [l.coprime, Ideal.mul_top]
        _ = l.Mb * N ⊔ N * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [Ideal.mul_sup, mul_comm N l.Mb]
        _ ≤ _ := sup_le (le_sup_right.trans le_sup_left) (le_sup_left.trans le_sup_right)
  · rw [hmap, eq_top_iff, ← l.coprime]
    exact sup_le_sup le_sup_left le_sup_left

end GlobalTheory.ZM
end

