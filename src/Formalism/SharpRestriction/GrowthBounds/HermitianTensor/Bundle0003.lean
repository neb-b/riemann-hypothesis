module

public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TieDefs
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0002
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle0007
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle0013
public import Formalism.PolynomialDimension.Bundle0004

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CoeffSumMonomialLinear
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def midI (r : ℕ) (j : Fin r) : Fin (r + 1 + 1) := j.castSucc.succ

def midOf {r : ℕ} (t : Fin (r + 1 + 1)) : Option (Fin r) :=
  if h : 0 < t.val ∧ t.val < r + 1 then some ⟨t.val - 1, by omega⟩ else none

def subY (A : Type) [CommRing A] (r : ℕ) :
    MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A →ₐ[A]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A) :=
  aeval fun v => match midOf v.2 with
    | some j => ∑ i : Fin r, C (X (i, j)) * X (v.1, midI r i)
    | none => X v

def sub2 (K : Type) [Field K] (r : ℕ) :
    MvPolynomial (Bool × (Fin (r + 1 + 1) × Fin (r + 1 + 1))) K →ₐ[K]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K) :=
  aeval fun w => map (blockEmb K (k := r) (n := r) w.1).toRingHom (subY K r (X w.2))

theorem coeff_sum_monomial_linear {K B σ : Type} [Field K] [CommRing B] [Algebra K B] (L : B →ₗ[K] K) (f : MvPolynomial σ B)
    (u : σ →₀ ℕ) : AddMonoidAlgebra.coeff (∑ u' ∈ f.support, monomial u' (L (AddMonoidAlgebra.coeff f u'))) u = L (AddMonoidAlgebra.coeff f u) := by
  classical
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with hu
  · rfl
  · have h0 : AddMonoidAlgebra.coeff f u = 0 := by simpa [mem_support_iff] using hu
    rw [h0, map_zero]

def lcoef {K B σ : Type} [Field K] [CommRing B] [Algebra K B] (L : B →ₗ[K] K) :
    MvPolynomial σ B →ₗ[K] MvPolynomial σ K where
  toFun f := ∑ u ∈ f.support, monomial u (L (AddMonoidAlgebra.coeff f u))
  map_add' f g := by
    ext u
    simp only [AddMonoidAlgebra.coeff_add (R := K), Finsupp.add_apply, coeff_sum_monomial_linear]
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add]
  map_smul' c f := by
    ext u
    rw [RingHom.id_apply, coeff_smul, coeff_sum_monomial_linear, coeff_sum_monomial_linear, coeff_smul, map_smul]

theorem coeff_lcoef {K B σ : Type} [Field K] [CommRing B] [Algebra K B] (L : B →ₗ[K] K) (f : MvPolynomial σ B)
    (u : σ →₀ ℕ) : AddMonoidAlgebra.coeff (lcoef L f) u = L (AddMonoidAlgebra.coeff f u) :=
  coeff_sum_monomial_linear L f u

def lamOf (K : Type) [Field K] (r : ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K) :
    MvPolynomial (Bool × (Fin (r + 1 + 1) × Fin (r + 1 + 1))) K →ₗ[K] MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K :=
  lcoef L ∘ₗ (sub2 K r).toLinearMap

def detY (A : Type) [CommRing A] (r : ℕ) : MvPolynomial (Fin r × Fin r) A :=
  Matrix.det (fun i j : Fin r => (X (i, j) : MvPolynomial (Fin r × Fin r) A))

def resY (A : Type) [CommRing A] (r : ℕ) (s : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A) :
    MvPolynomial (Fin r × Fin r) A :=
  eval (idPoint (MvPolynomial (Fin r × Fin r) A) (r + 1 + 1) (r + 1 + 1)) (subY A r s)

def RowA {K : Type} [CommRing K] {k n : ℕ} (a : Fin k) (f : MvPolynomial (Fin k × Fin n) K) (d : ℕ) : Prop :=
  ∀ u, AddMonoidAlgebra.coeff f u ≠ 0 → rowDeg u a = d

def shapeC {r : ℕ} (c : ℕ) (β : Fin r → ℕ) : Fin (r + 1 + 1) → ℕ :=
  fun t => if t = 0 then c else match midOf t with
    | some j => β j
    | none => 0

def PhInv (K : Type) [Field K] (r N : ℕ) (α α' : Fin r → ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K) : Prop :=
  ∀ l : Matrix (Fin r) (Fin r) K, IsUnit l.det → ∀ f ∈ dualWeyl K r r α, ∀ f' ∈ dualWeyl K r r α',
    L (blockEmb K true (rowAct K l f) * blockEmb K false (rowAct K l f')) =
      l.det ^ N * L (blockEmb K true f * blockEmb K false f')

def QPh : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (r : ℕ), 1 ≤ r → ∀ (a c N : ℕ) (α : Fin r → ℕ), Antitone α → (∀ i, α i ≤ N) →
    (∀ i j, α i ≤ α j + c) → c ≤ 8 * a →
    ∃ L : MvPolynomial (Bool × (Fin r × Fin r)) R.Kf →ₗ[R.Kf] R.Kf,
      PhInv R.Kf r N α (fun i => N - α i.rev) L ∧
      (∀ f ∈ intO R.O r α, ∀ f' ∈ intO R.O r (fun i => N - α i.rev),
        L (blockEmb R.Kf true f * blockEmb R.Kf false f') ∈ Set.range (algebraMap R.O R.Kf)) ∧
      ∃ (nb : ℕ) (u u' : Fin nb → MvPolynomial (Fin r × Fin r) R.Kf) (ka : Fin nb → ℕ),
        (nb : ℚ) = weylDim r (fun j => (α j : ℤ)) ∧ (∀ b, ka b ≤ ⌈kappaOneExponent p a (r + 1)⌉₊) ∧
        (∀ b, u b ∈ intO R.O r α) ∧ (∀ a', u' a' ∈ intO R.O r (fun i => N - α i.rev)) ∧
        ∀ a' b, L (blockEmb R.Kf true (u b) * blockEmb R.Kf false (u' a')) = if a' = b then (p : R.Kf) ^ ka b else 0

def SubCoeffP : Prop :=
  ∀ (A : Type) [CommRing A] (r : ℕ) (ν : Fin (r + 1 + 1) → ℕ) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A),
    v ∈ dualWeyl A (r + 1 + 1) (r + 1 + 1) ν → ∀ u, AddMonoidAlgebra.coeff (subY A r v) u ∈ dualWeyl A r r (fun j => ν (midI r j))

def SubMapP : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (r : ℕ) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A),
    subY B r (map φ v) = map (map φ) (subY A r v)

def SubRowP : Prop :=
  ∀ (A : Type) [CommRing A] (r : ℕ) (a : Fin (r + 1 + 1)) (d : ℕ) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A),
    RowA a v d → RowA a (subY A r v) d

def LamCoeffP : Prop :=
  ∀ (K : Type) [Field K] (r : ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K)
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) (u : Fin (r + 1 + 1) × Fin (r + 1 + 1) →₀ ℕ),
    AddMonoidAlgebra.coeff (lamOf K r L (blockEmb K true v * blockEmb K false t)) u =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal u,
        L (blockEmb K true (AddMonoidAlgebra.coeff (subY K r v) x.1) * blockEmb K false (AddMonoidAlgebra.coeff (subY K r t) x.2))

def LamEquivP : Prop :=
  ∀ (K : Type) [Field K] (r : ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K)
    (g : Matrix (Fin (r + 1 + 1)) (Fin (r + 1 + 1)) K) (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K),
    lamOf K r L (blockEmb K true (rowAct K g v) * blockEmb K false (rowAct K g t)) =
      rowAct K g (lamOf K r L (blockEmb K true v * blockEmb K false t))

def LamMulP : Prop :=
  ∀ (K : Type) [Field K] (r Q : ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K)
    (F s t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K), subY K r F = C (detY K r ^ Q) * map C F →
    lamOf K r L (blockEmb K true (F * s) * blockEmb K false t) =
      F * lcoef L (C (blockEmb K true (detY K r ^ Q)) * map (blockEmb K (k := r) (n := r) true).toRingHom (subY K r s) *
        map (blockEmb K (k := r) (n := r) false).toRingHom (subY K r t))

def LamEvalP : Prop :=
  ∀ (K : Type) [Field K] (r : ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K)
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K),
    eval (idPoint K (r + 1 + 1) (r + 1 + 1)) (lamOf K r L (blockEmb K true v * blockEmb K false t)) =
      L (blockEmb K true (resY K r v) * blockEmb K false (resY K r t))

def LamMemP : Prop :=
  ∀ (K : Type) [Field K] [Infinite K] (r N : ℕ) (ν ν' νp : Fin (r + 1 + 1) → ℕ)
    (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K),
    ν (Fin.last (r + 1)) = 0 → ν' (Fin.last (r + 1)) = 0 → νp (Fin.last (r + 1)) = 0 → νp 0 = ν 0 + ν' 0 →
    (∀ j, νp (midI r j) = N) → PhInv K r N (fun j => ν (midI r j)) (fun j => ν' (midI r j)) L →
    ∀ v ∈ dualWeyl K (r + 1 + 1) (r + 1 + 1) ν, ∀ t ∈ dualWeyl K (r + 1 + 1) (r + 1 + 1) ν',
      lamOf K r L (blockEmb K true v * blockEmb K false t) ∈ dualWeyl K (r + 1 + 1) (r + 1 + 1) νp

def SubMuP : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (r : ℕ), 1 ≤ r → ∀ (P Q : ℕ),
    ∀ F ∈ dualWeyl R.Kf (r + 1 + 1) (r + 1 + 1) (nuOf (wtPQ (r + 1) P Q)), subY R.Kf r F = C (detY R.Kf r ^ Q) * map C F

def TopLineP : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (r : ℕ), 1 ≤ r → ∀ (a b : ℕ),
    ∀ Ψ ∈ dualWeyl R.Kf (r + 1 + 1) (r + 1 + 1) (nuOf (wtPQ (r + 1) a b)), RowA 0 Ψ (a + b) → RowA (Fin.last (r + 1)) Ψ 0 →
      Ψ = C (eval (idPoint R.Kf (r + 1 + 1) (r + 1 + 1)) Ψ) * hw R.Kf (le_refl (r + 1 + 1)) (nuOf (wtPQ (r + 1) a b))

def LiftP : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] (r c : ℕ) (β : Fin r → ℕ), Antitone β → (∀ j, β j ≤ c) →
    ∀ u ∈ dualWeyl A r r β, ∃ s ∈ dualWeyl A (r + 1 + 1) (r + 1 + 1) (shapeC c β),
      RowA 0 s c ∧ RowA (Fin.last (r + 1)) s 0 ∧ resY A r s = u

def DetDivP : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] (r Q : ℕ) (β : Fin r → ℕ), 1 ≤ r → Antitone β →
    ∀ u ∈ dualWeyl A r r (fun j => β j + Q), ∃ u₀ ∈ dualWeyl A r r β, u = detY A r ^ Q * u₀

def IntCapP : Prop :=
  ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K], Function.Injective (algebraMap O K) →
    ∀ (k : ℕ) (ν : Fin k → ℕ) (F : MvPolynomial (Fin k × Fin k) K), F ∈ dualWeyl K k k ν →
      (∀ u, AddMonoidAlgebra.coeff F u ∈ Set.range (algebraMap O K)) → F ∈ intO O k ν

def HwMulP : Prop :=
  ∀ (A : Type) [CommRing A] (k : ℕ) (ν ν' : Fin k → ℕ), Antitone ν → Antitone ν' →
    hw A (le_refl k) (ν + ν') = hw A (le_refl k) ν * hw A (le_refl k) ν' ∧
    eval (idPoint A k k) (hw A (le_refl k) ν) = 1

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ExplicitMapOntoTwoLetterSpace
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Har4 Formalism.GradedWeylDivisibility MvPolynomial

theorem ta_sumToIter_rename_inr {R S₁ S₂ : Type} [CommRing R] (q : MvPolynomial S₂ R) :
    sumRingEquiv R S₁ S₂ (rename Sum.inr q) = C q := by
  induction q using MvPolynomial.induction_on with
  | C a => rw [rename_C, MvPolynomial.sumRingEquiv_C]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p n hp => rw [map_mul, map_mul, hp, rename_X, MvPolynomial.sumRingEquiv_X_inr, map_mul]

section A

variable (K : Type) [Field K] (m : ℕ)

theorem Psi_xs (f : MvPolynomial (Fin (m + 1)) K) :
    PsiXY K m (rename Sum.inl f) = blockEmb K true (rename (fun i => (i, (0 : Fin (m + 1)))) f) := by
  simp only [PsiXY, blockEmb, aeval_rename, rename_rename]
  conv_rhs => rw [← aeval_X_left_apply ((rename _) f), aeval_rename]
  rfl

theorem Psi_ys (f : MvPolynomial (Fin (m + 1)) K) :
    PsiXY K m (rename Sum.inr f) = blockEmb K false (aeval (covY K m) f) := by
  simp only [PsiXY, blockEmb, aeval_rename]
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rfl

end A

theorem explicit_map_injective : ExplicitMapInjective := by
  intro K _ m hm
  let Φ1 : PolXY K (m + 1) →ₐ[K] MvPolynomial (Fin (m + 1) ⊕ (Fin (m + 1) × Fin (m + 1))) K :=
    aeval (Sum.elim (fun i => X (Sum.inl i)) (fun i => rename Sum.inr (covY K m i)))
  let e : Fin (m + 1) ⊕ (Fin (m + 1) × Fin (m + 1)) → Bool × (Fin (m + 1) × Fin (m + 1)) :=
    Sum.elim (fun i => (true, (i, 0))) (fun v => (false, v))
  have he : Function.Injective e := by
    rintro (a | a) (b | b) h
    · simp only [e, Sum.elim_inl, Prod.mk.injEq, true_and, and_true] at h
      rw [h]
    · simp [e] at h
    · simp [e] at h
    · simp only [e, Sum.elim_inr, Prod.mk.injEq, true_and] at h
      rw [h]
  have hfac : PsiXY K m = (rename e).comp Φ1 := by
    apply algHom_ext
    rintro (i | i)
    · simp [PsiXY, Φ1, e]
    · simp only [PsiXY, Φ1, aeval_X, Sum.elim_inr, AlgHom.comp_apply, rename_rename]
      rfl
  have hφ : Function.Injective (aeval (covY K m) : MvPolynomial (Fin (m + 1)) K →ₐ[K] _) :=
    ShapeCovering.signed_minors_alg_independent K m hm
  have hcomm : (sumRingEquiv K (Fin (m + 1)) (Fin (m + 1) × Fin (m + 1))).toRingHom.comp Φ1.toRingHom =
      (map (aeval (covY K m) : MvPolynomial (Fin (m + 1)) K →ₐ[K] _).toRingHom).comp
        (sumRingEquiv K (Fin (m + 1)) (Fin (m + 1))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [Φ1, sumRingEquiv_C]
    · rintro (i | i)
      · simp [Φ1, sumRingEquiv_X_inl]
      · simp [Φ1, ta_sumToIter_rename_inr, sumRingEquiv_X_inr]
  have h1 : Function.Injective Φ1 := by
    intro f1 f2 h
    have h2 := DFunLike.congr_fun hcomm f1
    have h3 := DFunLike.congr_fun hcomm f2
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.toRingHom_eq_coe] at h2 h3
    rw [h, h3] at h2
    have h4 := map_injective _ hφ h2
    exact ((sumRingEquiv K (Fin (m + 1)) (Fin (m + 1))).injective h4).symm
  rw [hfac]
  exact (rename_injective e he).comp h1

theorem ta_isHom_prodX {A : Type} [CommRing A] {k : ℕ} (a : Fin k → ℕ) :
    (∏ i, X i ^ a i : MvPolynomial (Fin k) A).IsHomogeneous (∑ i, a i) := by
  exact IsHomogeneous.prod Finset.univ (fun i => X i ^ a i) a (fun i _ => isHomogeneous_X_pow i (a i))

theorem ta_monomial_split {K : Type} [Field K] {k : ℕ} (v : XY k →₀ ℕ) (c : K) :
    (monomial v c : PolXY K k) = c • (rename Sum.inl (∏ i : Fin k, X i ^ v (Sum.inl i)) *
      rename Sum.inr (∏ i : Fin k, X i ^ v (Sum.inr i))) := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type, map_prod, map_prod,
    smul_eq_C_mul]
  simp only [map_pow, rename_X]

theorem ta_rename_inl_hom {K : Type} [Field K] {k P : ℕ} (f : MvPolynomial (Fin k) K) (h : f.IsHomogeneous P) :
    IsWeightedHomogeneous (wXY k) (rename Sum.inl f : PolXY K k) (P, 0) := by
  classical
  intro d hd
  have hmem : d ∈ (rename Sum.inl f : PolXY K k).support := mem_support_iff.2 hd
  rw [support_rename_of_injective Sum.inl_injective, Finset.mem_image] at hmem
  obtain ⟨d', hd', rfl⟩ := hmem
  have hP := h (mem_support_iff.1 hd')
  simp only [Finsupp.weight_apply] at hP ⊢
  rw [Finsupp.sum_mapDomain_index_inj Sum.inl_injective]
  simp only [wXY, Sum.elim_inl]
  rw [← hP]
  ext
  · simp [Finsupp.sum, Prod.fst_sum]
  · simp [Finsupp.sum, Prod.snd_sum]

theorem ta_rename_inr_hom {K : Type} [Field K] {k Q : ℕ} (f : MvPolynomial (Fin k) K) (h : f.IsHomogeneous Q) :
    IsWeightedHomogeneous (wXY k) (rename Sum.inr f : PolXY K k) (0, Q) := by
  classical
  intro d hd
  have hmem : d ∈ (rename Sum.inr f : PolXY K k).support := mem_support_iff.2 hd
  rw [support_rename_of_injective Sum.inr_injective, Finset.mem_image] at hmem
  obtain ⟨d', hd', rfl⟩ := hmem
  have hQ := h (mem_support_iff.1 hd')
  simp only [Finsupp.weight_apply] at hQ ⊢
  rw [Finsupp.sum_mapDomain_index_inj Sum.inr_injective]
  simp only [wXY, Sum.elim_inr]
  rw [← hQ]
  ext
  · simp [Finsupp.sum, Prod.fst_sum]
  · simp [Finsupp.sum, Prod.snd_sum]

theorem ta_mul_mem_PolAB {K : Type} [Field K] {k P Q : ℕ} (f1 f2 : MvPolynomial (Fin k) K)
    (h1 : f1.IsHomogeneous P) (h2 : f2.IsHomogeneous Q) :
    rename Sum.inl f1 * rename Sum.inr f2 ∈ PolAB K k P Q := by
  rw [Formalism.CountingSumsFrames.Har4.mem_PolAB_iff]
  have := (ta_rename_inl_hom f1 h1).mul (ta_rename_inr_hom f2 h2)
  simpa using this

theorem ta_nuOf_vec (m P : ℕ) (hm : 1 ≤ m) : nuOf (letterWt m P true) = fun t => if t = 0 then P else 0 := by
  funext t
  unfold nuOf letterWt
  simp only [if_true]
  have hl : Fin.last m ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  rw [if_neg hl]
  split_ifs <;> simp

theorem ta_nuOf_cov (m Q : ℕ) : nuOf (letterWt m Q false) = fun t => if t = Fin.last m then 0 else Q := by
  funext t
  unfold nuOf letterWt
  simp only [Bool.false_eq_true, if_false, if_true]
  split_ifs <;> simp

theorem explicit_map_onto_two_letter_space : ExplicitMapOntoTwoLetters := by
  intro K _ m hm P Q x
  constructor
  · intro hx
    unfold twoSp tensorLat at hx
    refine Submodule.span_induction (p := fun x _ => ∃ f ∈ PolAB K (m + 1) P Q, PsiXY K m f = x) ?_
      ⟨0, Submodule.zero_mem _, map_zero _⟩ ?_ ?_ hx
    · rintro y ⟨F, hF, rfl⟩
      have ht := hF true
      have hf := hF false
      simp only [if_true, Bool.false_eq_true, if_false] at ht hf
      rw [ta_nuOf_vec m P hm] at ht
      rw [ta_nuOf_cov m Q] at hf
      obtain ⟨f1, h1, e1⟩ := (ShapeCovering.first_column_polynomials_characterize K m P (F true) hm).1 ht
      obtain ⟨f2, h2, e2⟩ := (ShapeCovering.signed_minor_polynomials_characterize K m Q (F false) hm).1 hf
      refine ⟨rename Sum.inl f1 * rename Sum.inr f2, ta_mul_mem_PolAB f1 f2 h1 h2, ?_⟩
      rw [covY_eq] at e2
      rw [map_mul, Psi_xs, Psi_ys, e1, e2, Fintype.prod_bool]
    · rintro x y _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
      exact ⟨f + g, Submodule.add_mem _ hf hg, map_add _ _ _⟩
    · rintro c x _ ⟨f, hf, rfl⟩
      exact ⟨c • f, Submodule.smul_mem _ _ hf, map_smul _ _ _⟩
  · rintro ⟨f, hf, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [f.as_sum, map_sum]
    refine Submodule.sum_mem _ fun v hv => ?_
    rw [ta_monomial_split, map_smul, map_mul, Psi_xs, Psi_ys]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine ⟨fun b : Bool => (cond b (rename (fun i : Fin (m + 1) => (i, (0 : Fin (m + 1))))
        (∏ i : Fin (m + 1), (X i : MvPolynomial (Fin (m + 1)) K) ^ v (Sum.inl i)))
      (aeval (covY K m) (∏ i : Fin (m + 1), (X i : MvPolynomial (Fin (m + 1)) K) ^ v (Sum.inr i))) :
        MvPolynomial (Fin (m + 1) × Fin (m + 1)) K), ?_, ?_⟩
    · intro b
      cases b
      · simp only [Bool.false_eq_true, if_false, cond_false]
        rw [ta_nuOf_cov m Q]
        refine (ShapeCovering.signed_minor_polynomials_characterize K m Q _ hm).2 ⟨_, ?_, rfl⟩
        have := ta_isHom_prodX (A := K) (fun i : Fin (m + 1) => v (Sum.inr i))
        rwa [show ∑ i : Fin (m + 1), v (Sum.inr i) = Q from (hf v hv).2] at this
      · simp only [if_true, cond_true]
        rw [ta_nuOf_vec m P hm]
        refine (ShapeCovering.first_column_polynomials_characterize K m P _ hm).2 ⟨_, ?_, rfl⟩
        have := ta_isHom_prodX (A := K) (fun i : Fin (m + 1) => v (Sum.inl i))
        rwa [show ∑ i : Fin (m + 1), v (Sum.inl i) = P from (hf v hv).1] at this
    · rw [Fintype.prod_bool]
      rfl

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsTwoWeightIff
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem wtPQ_eq (m a b : ℕ) (hm : 1 ≤ m) : wtPQ m a b = letterWt m a true + letterWt m b false := by
  funext i
  have hi := i.isLt
  simp only [wtPQ, letterWt, Pi.add_apply, Fin.ext_iff, Fin.val_zero, Fin.val_last, if_true, Bool.false_eq_true, if_false]
  split_ifs <;> omega

theorem wtPQ_anti (m a b : ℕ) (hm : 1 ≤ m) : Antitone (wtPQ m a b) := by
  intro i j hij
  have hij' : i.val ≤ j.val := hij
  have hi := i.isLt
  have hj := j.isLt
  simp only [wtPQ, Fin.ext_iff, Fin.val_zero, Fin.val_last]
  split_ifs <;> omega

theorem nuOf_wtPQ (m a b : ℕ) (hm : 1 ≤ m) :
    nuOf (wtPQ m a b) = nuOf (letterWt m a true) + nuOf (letterWt m b false) := by
  funext t
  have ht := t.isLt
  simp only [nuOf, wtPQ_eq m a b hm, Pi.add_apply, letterWt, Fin.ext_iff, Fin.val_zero, Fin.val_last, if_true, Bool.false_eq_true, if_false]
  split_ifs <;> omega

theorem delta_block (K : Type) [Field K] (m : ℕ) (b : Bool) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :
    deltaB K m (blockEmb K b F) = F := by
  simp [deltaB, blockEmb, rename_rename, Function.comp_def]
  exact rename_id_apply F

theorem delta_prod (K : Type) [Field K] (m : ℕ) (F : Bool → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :
    deltaB K m (∏ b, blockEmb K b (F b)) = F true * F false := by
  rw [map_prod, Fintype.prod_bool, delta_block, delta_block]

theorem mem_invariant_sections_two_weight_iff (hCO : CartanOnto) {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] [IsFractionRing O Kf] (m a b : ℕ) (hm : 1 ≤ m) (Λ : Submodule O (Fin (m + 1) → Kf))
    (hΛ : IsLattice O Λ) (y : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) :
    y ∈ H0 O m (wtPQ m a b) Λ ↔ ∃ x ∈ twoLat O m a b Λ, deltaB Kf m x = y := by
  have hA : Antitone (letterWt m a true) := by
    intro i j hij
    have hij' : i.val ≤ j.val := hij
    simp only [letterWt, if_true, Fin.ext_iff, Fin.val_zero]
    split_ifs <;> omega
  have hB : Antitone (letterWt m b false) := by
    intro i j hij
    have hij' : i.val ≤ j.val := hij
    have hi := i.isLt
    have hj := j.isLt
    simp only [letterWt, Bool.false_eq_true, if_false, Fin.ext_iff, Fin.val_last]
    split_ifs <;> omega
  have key : H0 O m (wtPQ m a b) Λ =
      Submodule.map ((deltaB Kf m).toLinearMap.restrictScalars O) (twoLat O m a b Λ) := by
    rw [wtPQ_eq m a b hm, hCO O Kf m _ _ Λ hΛ hA hB, twoLat, tensorLat, Submodule.map_span]
    congr 1
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨F, hF, G, hG, rfl⟩
      refine ⟨∏ s, blockEmb Kf s (if s = true then F else G), ⟨fun s => if s = true then F else G, ?_, rfl⟩, ?_⟩
      · intro s
        cases s <;> simpa using ‹_›
      · simp [delta_block]
    · rintro ⟨x, ⟨F, hF, rfl⟩, rfl⟩
      refine ⟨F true, by simpa using hF true, F false, by simpa using hF false, ?_⟩
      simp [delta_block]
  rw [key, Submodule.mem_map]
  exact Iff.rfl

theorem delta_twoSp (K : Type) [Field K] (m a b : ℕ) (hm : 1 ≤ m) :
    ∀ x ∈ twoSp K m a b, deltaB K m x ∈ dualWeyl K (m + 1) (m + 1) (nuOf (wtPQ m a b)) := by
  intro x hx
  rw [nuOf_wtPQ m a b hm]
  unfold twoSp tensorLat at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨F, hF, rfl⟩ := hy
    rw [delta_prod]
    have h1 := hF true
    have h2 := hF false
    simp only [eq_self_iff_true, if_true, Bool.false_eq_true, if_false] at h1 h2
    exact Formalism.GradedWeylDivisibility.dualWeyl_mul h1 h2
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add (f := _)]
    exact add_mem hy hz
  | smul c y _ hy =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hy

theorem hXY_ne_zero (K : Type) [Field K] (k : ℕ) : hXY K (k + 1) ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval (Sum.elim (fun i : Fin (k + 1) => if i = 0 then (1 : K) else 0)
    (fun i : Fin (k + 1) => if i = 0 then (1 : K) else 0))) h
  simp [hXY] at this

end Formalism.MainNotions.flipOneThree.Pf

end
end

