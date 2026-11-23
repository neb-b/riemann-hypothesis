module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0013
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
section
noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi

namespace UpperTheory.V.AlgebraTools

section Gen

variable {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]

def FinOrb (K K' : Subgroup G) (x : G) : Prop := (MulAction.orbit K (x : G ⧸ K')).Finite

def HeckePair (I : Subgroup G) : Prop := ∀ x : G, FinOrb I I x


open scoped Classical in
open Classical in
def hk2 (ρ : Representation A G M) (K K' : Subgroup G) (x : G) : fixd ρ K' →ₗ[A] fixd ρ K :=
  if h : ∀ v ∈ fixd ρ K', dc ρ K K' x v ∈ fixd ρ K then (dc ρ K K' x).restrict h else 0

def hk (ρ : Representation A G M) (I : Subgroup G) (x : G) : Module.End A (fixd ρ I) := hk2 ρ I I x

theorem fixd_anti (ρ : Representation A G M) {I K : Subgroup G} (h : I ≤ K) : fixd ρ K ≤ fixd ρ I :=
  fun _ hv u hu => hv u (h hu)

def inc (ρ : Representation A G M) {I K : Subgroup G} (h : I ≤ K) : fixd ρ K →ₗ[A] fixd ρ I :=
  Submodule.inclusion (fixd_anti ρ h)

def trc (ρ : Representation A G M) (K I : Subgroup G) : fixd ρ I →ₗ[A] fixd ρ K := hk2 ρ K I 1


variable (A)

abbrev permRep (I : Subgroup G) : Representation A G (MonoidAlgebra A (G ⧸ I)) := Representation.ofMulAction A G (G ⧸ I)

def HkAlg (I : Subgroup G) : Subalgebra A (Module.End A (fixd (permRep A I) I)) :=
  Algebra.adjoin A (Set.range (hk (permRep A I) I))

def hT (I : Subgroup G) (x : G) : HkAlg A I := ⟨hk (permRep A I) I x, Algebra.subset_adjoin ⟨x, rfl⟩⟩

structure LeviFact (I : Subgroup G) where
  Uf : Subgroup G
  Mf : Subgroup G
  Lf : Subgroup G
  M_U : ∀ m ∈ Mf, ∀ u ∈ Uf, m * u * m⁻¹ ∈ Uf
  M_L : ∀ m ∈ Mf, ∀ l ∈ Lf, m * l * m⁻¹ ∈ Lf
  uniq : ∀ u ∈ Uf, ∀ m ∈ Mf, ∀ l ∈ Lf, u * m * l = 1 → u = 1 ∧ m = 1
  fact : ∀ g ∈ I, ∃ u ∈ Uf ⊓ I, ∃ m ∈ Mf ⊓ I, ∃ l ∈ Lf ⊓ I, g = u * m * l

def LeviFact.Pos {I : Subgroup G} (F : LeviFact I) (m : G) : Prop :=
  m ∈ F.Mf ∧ (∀ u ∈ F.Uf ⊓ I, m * u * m⁻¹ ∈ I) ∧ ∀ l ∈ F.Lf ⊓ I, m⁻¹ * l * m ∈ I

def LeviFact.NormJ {I : Subgroup G} (F : LeviFact I) (m : G) : Prop :=
  ∀ j ∈ F.Mf ⊓ I, m * j * m⁻¹ ∈ I ∧ m⁻¹ * j * m ∈ I

end Gen

section Perm

variable {n : ℕ}

def invLen (w : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ w p.2 < w p.1).card

def pm (R : Type) [CommRing R] (n : ℕ) : Equiv.Perm (Fin n) →* GL (Fin n) R :=
  (Matrix.permMatrixHom (n := Fin n) (R := R)).toHomUnits

theorem pm_apply (R : Type) [CommRing R] (w : Equiv.Perm (Fin n)) (i j : Fin n) :
    (pm R n w : Matrix (Fin n) (Fin n) R) i j = if i = w j then 1 else 0 := by
  simp only [pm, MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  congr 1
  exact propext Equiv.Perm.inv_eq_iff_eq

end Perm

section GeneralLinearIntegers

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)

def unitsC (C : Subgroup 𝓀[k]ˣ) : Subgroup kˣ :=
  (C.comap (Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom)).map (Units.map (algebraMap 𝒪[k] k).toMonoidHom)

def torC (C : Subgroup 𝓀[k]ˣ) : Subgroup (Fin n → kˣ) := Subgroup.pi Set.univ fun _ => unitsC k C

def unipO : Subgroup (GL (Fin n) k) := unipB k (Fin n) ⊓ KO k (Fin n)

def iwC (C : Subgroup 𝓀[k]ˣ) : Subgroup (GL (Fin n) k) :=
  KOne k (Fin n) ⊔ unipO k n ⊔ (torC k n C).map (diagT k (Fin n))

variable {k n}

def IsUnif (x : kˣ) : Prop := ∃ p : 𝒪[k], Irreducible p ∧ algebraMap 𝒪[k] k p = x

def Dom (t : Fin n → kˣ) : Prop := ∀ i j, i ≤ j → valuation k (t i : k) ≤ valuation k (t j : k)

theorem dom_one : Dom (1 : Fin n → kˣ) := fun _ _ _ => le_rfl

def pw (x : kˣ) (a : Fin n → ℤ) : GL (Fin n) k := diagT k (Fin n) fun i => x ^ a i

def fund (n m : ℕ) : Fin n → ℤ := fun i => if (i : ℕ) < m then 1 else 0

theorem exists_isUnif : ∃ x : kˣ, IsUnif x := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have : algebraMap 𝒪[k] k p ≠ 0 := fun h => hp.ne_zero (Subtype.ext h)
  exact ⟨Units.mk0 _ this, p, hp, rfl⟩

end GeneralLinearIntegers

end UpperTheory.V.AlgebraTools
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkBern
section
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem UpperTheory.V.AlgebraTools.hkBern_reg {R : Type} [CommRing R] {n : ℕ} {a c : Fin n} (hac : a ≠ c)
    (y : MvPolynomial (Fin n) R) (h : (X a - X c) * y = 0) : y = 0 := by
  let φ : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
    aeval fun j => if j = a then X a + X c else X j
  let ψ : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
    aeval fun j => if j = a then X a - X c else X j
  have hψ : ψ.comp φ = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro j
    by_cases hj : j = a
    · simp [φ, ψ, hj, hac.symm]
    · simp [φ, ψ, hj]
  have h1 : φ (X a - X c) = X a := by simp [φ, hac.symm]
  have h2 : X a * φ y = X a * 0 := by rw [mul_zero, ← h1, ← map_mul, h, map_zero]
  have h3 : φ y = 0 := (MvPolynomial.isRegular_X (R := R) (n := a)).left h2
  have h4 := AlgHom.congr_fun hψ y
  rw [AlgHom.comp_apply, h3, map_zero, AlgHom.id_apply] at h4
  exact h4.symm

theorem UpperTheory.V.AlgebraTools.hkBern :
    ∀ (R : Type) [CommRing R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H),
      (∀ (a c : Fin n), a.val + 1 = c.val → ∀ x : MvPolynomial (Fin n) R, ∃ y : MvPolynomial (Fin n) R, (X a - X c) * y = x - rename (swap a c) x ∧
        b.T (swap a c) * b.th x = b.th (rename (swap a c) x) * b.T (swap a c) + (q - 1) • b.th (X a * y)) ∧
      ∀ z : MvPolynomial (Fin n) R, z.IsSymmetric → ∀ w, b.T w * b.th z = b.th z * b.T w := by
  intro R _ n q H _ _ b
  have main : ∀ (a c : Fin n), a.val + 1 = c.val → ∀ x : MvPolynomial (Fin n) R, ∃ y : MvPolynomial (Fin n) R,
      (X a - X c) * y = x - rename (swap a c) x ∧
        b.T (swap a c) * b.th x = b.th (rename (swap a c) x) * b.T (swap a c) + (q - 1) • b.th (X a * y) := by
    intro a c hac
    have hX : ∀ j : Fin n, ∃ y : MvPolynomial (Fin n) R,
        (X a - X c) * y = X j - rename (swap a c) (X j) ∧
        b.T (swap a c) * b.th (X j) = b.th (rename (swap a c) (X j)) * b.T (swap a c) + (q - 1) • b.th (X a * y) := by
      intro j
      by_cases ha : j = a
      · subst ha
        refine ⟨1, by simp, ?_⟩
        rw [rename_X, swap_apply_left, mul_one]
        exact b.relA j c hac
      · by_cases hc : j = c
        · subst hc
          refine ⟨-1, by simp, ?_⟩
          rw [rename_X, swap_apply_right, mul_neg, mul_one, map_neg, smul_neg, ← sub_eq_add_neg]
          exact b.relB a j hac
        · refine ⟨0, by simp [swap_apply_of_ne_of_ne ha hc], ?_⟩
          rw [rename_X, swap_apply_of_ne_of_ne ha hc, mul_zero, map_zero, smul_zero, add_zero]
          exact b.comm a c hac j ha hc
    intro x
    induction x using MvPolynomial.induction_on with
    | C r =>
      refine ⟨0, by simp, ?_⟩
      rw [rename_C, mul_zero, map_zero, smul_zero, add_zero, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
        Algebra.commutes]
    | add p p' hp hp' =>
      obtain ⟨y, h1, h2⟩ := hp
      obtain ⟨y', h1', h2'⟩ := hp'
      refine ⟨y + y', ?_, ?_⟩
      · rw [mul_add, h1, h1', map_add (f := _)]; ring
      · rw [map_add (f := _), map_add (f := _), map_add (f := _), mul_add, h2, h2', mul_add, map_add (f := _), add_mul, smul_add]; abel
    | mul_X p j hp =>
      obtain ⟨y, h1, h2⟩ := hp
      obtain ⟨y', h1', h2'⟩ := hX j
      refine ⟨y * X j + rename (swap a c) p * y', ?_, ?_⟩
      · rw [map_mul]
        linear_combination (X j) * h1 + rename (swap a c) p * h1'
      · have e : X a * (y * X j + rename (swap a c) p * y') =
            (X a * y) * X j + rename (swap a c) p * (X a * y') := by ring
        rw [e, map_add (f := _), map_mul b.th (X a * y), map_mul b.th _ (X a * y'), map_mul (rename _), map_mul b.th p,
          map_mul b.th (rename _ p), ← mul_assoc, h2, add_mul, mul_assoc, h2', mul_add, smul_add, smul_mul_assoc,
          mul_smul_comm, mul_assoc]
        abel
  refine ⟨main, fun z hz => ?_⟩
  refine UpperTheory.V.AlgebraTools.hkInd n (fun w => b.T w * b.th z = b.th z * b.T w) ?_ ?_
  · simp only [b.T_one, one_mul, mul_one]
  · intro a c hac w hw ih
    obtain ⟨y, h1, h2⟩ := main a c hac z
    have hne : a ≠ c := by
      rintro rfl
      omega
    rw [hz (swap a c)] at h1 h2
    rw [sub_self] at h1
    rw [UpperTheory.V.AlgebraTools.hkBern_reg hne y h1, mul_zero, map_zero, smul_zero, add_zero] at h2
    rw [b.T_mul a c hac w hw, mul_assoc, ih, ← mul_assoc, h2, mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InjOfSandwich
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem inj_of_sandwich {R Q F ι : Type*} [CommRing R] [AddCommGroup Q] [Module R Q]
    [AddCommGroup F] [Module R F] [Fintype ι] (g : (ι → R) →ₗ[R] Q) (f : Q →ₗ[R] F)
    (e : F ≃ₗ[R] (ι → R)) (hg : Function.Surjective g) (hf : Function.Surjective f) :
    Function.Injective f := by
  have hs : Function.Surjective (e.toLinearMap ∘ₗ f ∘ₗ g) := e.surjective.comp (hf.comp hg)
  have hi := OrzechProperty.injective_of_surjective_endomorphism _ hs
  intro a b hab
  obtain ⟨x, rfl⟩ := hg a
  obtain ⟨y, rfl⟩ := hg b
  have : x = y := hi (by simp [hab])
  rw [this]

theorem UpperTheory.V.AlgebraTools.groupRing_ker :
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ] (l : ℕ), l.Prime → (l : Λ) ∈ IsLocalRing.maximalIdeal Λ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (e : σ → ℕ) (φ : MvPowerSeries σ Λ →ₐ[Λ] MonoidAlgebra Λ (∀ s, Multiplicative (ZMod (l ^ e s)))), (∀ s : σ, φ (1 + MvPowerSeries.X s) = MonoidAlgebra.of Λ (∀ s, Multiplicative (ZMod (l ^ e s))) (Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (l ^ e s))))) → Function.Surjective φ →
      RingHom.ker φ = Ideal.span (Set.range fun s => (1 + MvPowerSeries.X s : MvPowerSeries σ Λ) ^ l ^ e s - 1) := by
  intro Λ _ _ _ _ l hl hlm σ _ _ e φ hφ hsurj
  haveI : ∀ s, NeZero (l ^ e s) := fun s => ⟨pow_ne_zero _ hl.ne_zero⟩
  set w : σ → MvPowerSeries σ Λ := fun s => (1 + MvPowerSeries.X s) ^ l ^ e s - 1 with hw
  set I : Ideal (MvPowerSeries σ Λ) := Ideal.span (Set.range w) with hI
  have hle : I ≤ RingHom.ker φ := by
    rw [hI, Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    have h1 : (Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (l ^ e s))) :
        ∀ s, Multiplicative (ZMod (l ^ e s))) ^ (l ^ e s) = 1 := by
      rw [← Pi.mulSingle_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_self, ofAdd_zero,
        Pi.mulSingle_one]
    simp only [SetLike.mem_coe, RingHom.mem_ker, hw, map_sub, map_pow, hφ, map_one]
    rw [← map_pow, h1, map_one, sub_self]
  have hwm : ∀ s, w s - MvPowerSeries.X s ^ (l ^ e s) ∈
      Ideal.map MvPowerSeries.C (IsLocalRing.maximalIdeal Λ) := by
    intro s
    obtain ⟨m, hm⟩ : ∃ m, l ^ e s = m + 1 := ⟨l ^ e s - 1, (Nat.succ_pred_eq_of_pos (pow_pos hl.pos _)).symm⟩
    have hlC : ((l : ℕ) : MvPowerSeries σ Λ) ∈ Ideal.map MvPowerSeries.C (IsLocalRing.maximalIdeal Λ) := by
      rw [← map_natCast (MvPowerSeries.C (σ := σ) (R := Λ))]
      exact Ideal.mem_map_of_mem _ hlm
    simp only [hw]
    rw [add_comm, add_pow, hm, Finset.sum_range_succ, Finset.sum_range_succ']
    have key : ∀ k ∈ Finset.range m, MvPowerSeries.X s ^ (k + 1) * (1 : MvPowerSeries σ Λ) ^ (m + 1 - (k + 1)) *
        (((m + 1).choose (k + 1) : ℕ) : MvPowerSeries σ Λ) ∈ Ideal.map MvPowerSeries.C (IsLocalRing.maximalIdeal Λ) := by
      intro k hk
      have hd : l ∣ (m + 1).choose (k + 1) := by
        rw [← hm]
        refine hl.dvd_choose_pow (Nat.succ_ne_zero k) ?_
        rw [hm]; have := Finset.mem_range.mp hk; omega
      obtain ⟨t, ht⟩ := hd
      rw [ht, Nat.cast_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hlC)
    have hsum := Ideal.sum_mem _ key
    simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one,
      Nat.sub_zero, one_mul] at hsum ⊢
    convert hsum using 1
    ring
  have hIφ : ∀ a ∈ I, φ a = 0 := fun a ha => hle ha
  refine le_antisymm ?_ hle
  have hspan := UpperTheory.V.AlgebraTools.mvPowerSeries_span_monomials Λ σ (fun s => l ^ e s) w hwm
  let ψ := Ideal.Quotient.liftₐ I φ hIφ
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨Ideal.Quotient.mk I x, rfl⟩
  let v := fun α : ((s : σ) → Fin (l ^ e s)) => Ideal.Quotient.mk I (∏ s, MvPowerSeries.X s ^ (α s : ℕ))
  have hg : Function.Surjective (Fintype.linearCombination Λ v) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact hspan
  let eqv : ((s : σ) → Fin (l ^ e s)) ≃ (∀ s, Multiplicative (ZMod (l ^ e s))) :=
    Equiv.piCongrRight fun s => (ZMod.finEquiv (l ^ e s)).toEquiv.trans Multiplicative.ofAdd
  let E : MonoidAlgebra Λ (∀ s, Multiplicative (ZMod (l ^ e s))) ≃ₗ[Λ] (((s : σ) → Fin (l ^ e s)) → Λ) :=
    (MonoidAlgebra.coeffLinearEquiv Λ).trans
      ((Finsupp.linearEquivFunOnFinite Λ Λ _).trans (LinearEquiv.funCongrLeft Λ Λ eqv))
  have hinj := inj_of_sandwich (Fintype.linearCombination Λ v) ψ.toLinearMap E hg hψs
  intro x hx
  have h0 : ψ (Ideal.Quotient.mk I x) = 0 := hx
  have : Ideal.Quotient.mk I x = 0 := hinj (by simpa using h0)
  exact Ideal.Quotient.eq_zero_iff_mem.mp this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MSpBasis
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.mSplitAlg_basis :
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (n : ℕ) (R : Type) [CommRing R] (P : κ → Polynomial R), (∀ j, (P j).Monic) → (∀ j, (P j).natDegree = n) →
      ∃ b : Module.Basis (κ → ∀ i : Fin n, Fin (n - i)) R (MSplitAlg P n), ∀ c, b c = ∏ j, ∏ i, MSplitAlg.root P n j i ^ (c j i : ℕ) := by
  intro κ _ _ n R _ P hm hd
  have hb := fun j => (UpperTheory.V.AlgebraTools.splitAlg_basis n R (P j) (hm j) (hd j)).1
  choose bj hbj using hb
  let f : ∀ j, SplitAlg (P j) n →ₐ[R] MSplitAlg P n := fun j =>
    SplitAlg.lift (P j) n (MSplitAlg.root P n j) (MSplitAlg.prod_root P n j)
  let M : (∀ j, SplitAlg (P j) n) →ₘₗ[R] MSplitAlg P n :=
    (MultilinearMap.mkPiAlgebra R κ (MSplitAlg P n)).compLinearMap (fun j => (f j).toLinearMap)
  have hM : ∀ x, M x = ∏ j, f j (x j) := fun x => by
    simp [M, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
  let ψ : (⨂[R] j, SplitAlg (P j) n) →ₐ[R] MSplitAlg P n :=
    PiTensorProduct.liftAlgHom M (by rw [hM]; simp)
      (fun x y => by rw [hM, hM, hM]; simp [Finset.prod_mul_distrib])
  have hψt : ∀ x, ψ (PiTensorProduct.tprod R x) = ∏ j, f j (x j) := fun x => by
    simp [ψ, hM]
  have hψs : ∀ j x, ψ (PiTensorProduct.singleAlgHom j x) = f j x := fun j x => by
    rw [PiTensorProduct.singleAlgHom_apply, hψt,
      Fintype.prod_eq_single j (fun k hk => by simp [Pi.mulSingle_eq_of_ne hk])]
    simp
  let φ : MSplitAlg P n →ₐ[R] (⨂[R] j, SplitAlg (P j) n) :=
    MSplitAlg.lift P n (fun j i => PiTensorProduct.singleAlgHom j (SplitAlg.root (P j) n i)) (fun j => by
      have := congrArg (Polynomial.map
        (PiTensorProduct.singleAlgHom (R := R) (A := fun j => SplitAlg (P j) n) j).toRingHom)
        (SplitAlg.prod_root (P j) n)
      simp only [Polynomial.map_prod, Polynomial.map_map, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap,
        Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, RingHom.coe_coe] at this
      exact this)
  have h1 : ψ.comp φ = AlgHom.id R (MSplitAlg P n) := MSplitAlg.hom_ext P n (fun j i => by
    simp only [AlgHom.comp_apply, AlgHom.id_apply, φ, MSplitAlg.lift_root, hψs, f, SplitAlg.lift_root])
  have h2 : φ.comp ψ = AlgHom.id R _ := PiTensorProduct.algHom_ext (fun j => SplitAlg.hom_ext (P j) n (fun i => by
    simp only [AlgHom.comp_apply, AlgHom.id_apply, hψs, f, SplitAlg.lift_root, φ, MSplitAlg.lift_root]))
  let e : MSplitAlg P n ≃ₐ[R] (⨂[R] j, SplitAlg (P j) n) := AlgEquiv.ofAlgHom φ ψ h2 h1
  refine ⟨(Basis.piTensorProduct bj).map e.symm.toLinearEquiv, fun c => ?_⟩
  rw [Module.Basis.map_apply, Basis.piTensorProduct_apply]
  show ψ _ = _
  rw [hψt]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [hbj j (c j), map_prod]
  simp only [map_pow, f, SplitAlg.lift_root]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SwapOneAlt
section
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem pair_lt {R : Type} [CommRing R] {n : ℕ} {q : R} {H : Type} [Ring H] [Algebra R H] (b : Bern n q H)
    {a c : Fin n} (h : a.val + 1 = c.val) (u : Perm (Fin n)) (hu : u⁻¹ a < u⁻¹ c) :
    (b.T (swap a c) * b.T u - q • b.T u) + (b.T (swap a c) * b.T (swap a c * u) - q • b.T (swap a c * u)) = 0 := by
  have hu : b.T (swap a c * u) = b.T (swap a c) * b.T u := b.T_mul a c h u hu
  have hsq := b.T_sq a c h
  rw [hu, ← mul_assoc, hsq, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
  module

private theorem swap_one {R : Type} [CommRing R] {n : ℕ} {q : R} {H : Type} [Ring H] [Algebra R H] (b : Bern n q H)
    {a c : Fin n} (h : a.val + 1 = c.val) : b.T (swap a c) * b.one = q • b.one := by
  have hac : a ≠ c := by
    intro e
    rw [e] at h
    omega
  have key : ∀ w : Perm (Fin n), (b.T (swap a c) * b.T w - q • b.T w)
      + (b.T (swap a c) * b.T (swap a c * w) - q • b.T (swap a c * w)) = 0 := by
    intro w
    rcases lt_or_gt_of_ne (show w⁻¹ a ≠ w⁻¹ c from fun e => hac (w⁻¹.injective e)) with hw | hw
    · exact pair_lt b h w hw
    · have hu : (swap a c * w)⁻¹ a < (swap a c * w)⁻¹ c := by
        simpa [Perm.mul_apply, mul_inv_rev, swap_inv, swap_apply_left, swap_apply_right] using hw
      have := pair_lt b h (swap a c * w) hu
      rw [← mul_assoc, swap_mul_self, one_mul] at this
      rw [add_comm]
      exact this
  have hsum : ∑ w, (b.T (swap a c) * b.T w - q • b.T w) = 0 := by
    refine Finset.sum_ninvolution (fun w => swap a c * w) key ?_ (fun _ => Finset.mem_univ _) ?_
    · intro w _ e
      apply hac
      have := congrArg (fun x : Perm (Fin n) => (x * w⁻¹) a) e
      simp [mul_assoc] at this
      exact this.symm
    · intro w
      rw [← mul_assoc, swap_mul_self, one_mul]
  unfold Bern.one
  rw [Finset.mul_sum, Finset.smul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  exact hsum

theorem UpperTheory.V.AlgebraTools.hkOne :
    ∀ (R : Type) [CommRing R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H),
      (∀ w, b.T w * b.one = q ^ invN w • b.one) ∧ b.one * b.one = poin (n := n) q • b.one := by
  intro R _ n q H _ _ b
  have hinv := UpperTheory.V.AlgebraTools.hkInv n
  have p1 : ∀ w, b.T w * b.one = q ^ invN w • b.one := by
    refine UpperTheory.V.AlgebraTools.hkInd n _ ?_ ?_
    · rw [b.T_one, one_mul]
      simp [invN, hinv.2.2.1]
    · intro a c h w hw ih
      rw [b.T_mul a c h w hw, mul_assoc, ih, mul_smul_comm, swap_one b h, smul_smul,
        (hinv.1 a c h w hw).2.2, pow_succ]
  refine ⟨p1, ?_⟩
  show (∑ w, b.T w) * b.one = _
  rw [Finset.sum_mul]
  simp_rw [p1]
  rw [← Finset.sum_smul]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ULimKer
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem exists_sum_of_mem_span_smul_top {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
    {n : ℕ} (g : Fin n → R) (x : M) (hx : x ∈ (Ideal.span (Set.range g) • ⊤ : Submodule R M)) :
    ∃ q : Fin n → M, x = ∑ c, g c • q c := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr m _
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hr
    refine ⟨fun i => c i • m, ?_⟩
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]
  · rintro x y ⟨q, rfl⟩ ⟨q', rfl⟩
    exact ⟨fun i => q i + q' i, by simp [smul_add, Finset.sum_add_distrib]⟩

theorem UpperTheory.V.AlgebraTools.ULim.mem_smul_top_iff :
    ∀ (R : Type) [CommRing R] (F : Filter ℕ), F ≤ atTop → ∀ (I : ℕ → Ideal R) (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (a : Ideal R), a.FG → Antitone I →
      ∀ p : ∀ i, M i, ULim.mk F I M p ∈ (a • ⊤ : Submodule R (ULim F I M)) ↔
        ∀ j, ∀ᶠ N in F, p N ∈ ((a ⊔ I j) • ⊤ : Submodule R (M N)) := by
  intro R _ F hF I M _ _ a ha hI p
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 ha
  have hg' : Ideal.span (Set.range g) = a := hg
  have hga : ∀ c, g c ∈ a := fun c => hg' ▸ Ideal.subset_span ⟨c, rfl⟩
  constructor
  · intro hp j
    rw [← hg'] at hp
    obtain ⟨q, hq⟩ := exists_sum_of_mem_span_smul_top g _ hp
    choose q' hq' using fun c => ULim.mk_surjective F I M (q c)
    have h0 : ULim.mk F I M (p - ∑ c, g c • q' c) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, hq]
      simp only [map_smul, hq', sub_self]
    filter_upwards [ULim.mk_eq_zero.1 h0 j] with N hN
    have h1 : (∑ c, g c • q' c) N ∈ ((a ⊔ I j) • ⊤ : Submodule R (M N)) := by
      rw [Finset.sum_apply]
      exact Submodule.sum_mem _ fun c _ =>
        Submodule.smul_mem_smul (Ideal.mem_sup_left (hga c)) Submodule.mem_top
    have h2 := Submodule.add_mem ((a ⊔ I j) • ⊤ : Submodule R (M N)) (Submodule.smul_mono_left (le_sup_right : I j ≤ a ⊔ I j) hN) h1
    simpa using h2
  · intro hp
    obtain ⟨ν, hν, hP⟩ := exists_diag F hF
      (fun j N => p N ∈ ((a ⊔ I j) • ⊤ : Submodule R (M N))) hp
    have key : ∀ N, ∃ q : Fin n → M N, p N ∈ ((a ⊔ I (ν N)) • ⊤ : Submodule R (M N)) →
        p N - ∑ c, g c • q c ∈ (I (ν N) • ⊤ : Submodule R (M N)) := by
      intro N
      by_cases h : p N ∈ ((a ⊔ I (ν N)) • ⊤ : Submodule R (M N))
      · have h' := h
        rw [Submodule.sup_smul] at h'
        obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h'
        rw [← hg'] at hy
        obtain ⟨q, hq⟩ := exists_sum_of_mem_span_smul_top g _ hy
        refine ⟨q, fun _ => ?_⟩
        rw [← hq, ← hyz, add_sub_cancel_left]
        exact hz
      · exact ⟨0, fun h' => absurd h' h⟩
    choose q hq using key
    have h0 : ULim.mk F I M (p - ∑ c, g c • fun N => q N c) = 0 := by
      refine ULim.mk_eq_zero.2 fun j => ?_
      filter_upwards [hP, hν.eventually_ge_atTop j] with N hN hj
      have := Submodule.smul_mono_left (hI hj) (hq N (hN _ le_rfl))
      simpa [Finset.sum_apply] using this
    rw [map_sub, sub_eq_zero] at h0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h0, map_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem_smul (hga c) Submodule.mem_top
end

