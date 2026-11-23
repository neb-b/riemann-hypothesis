module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteIntegralClosureCharP
section
set_option maxSynthPendingDepth 1

open scoped nonZeroDivisors

namespace GroundTheory.Heights₂.Heights.Model

theorem module_finite_of_semilinear {B R M N : Type*} [CommRing B] [CommRing R] [Algebra R B]
    [IsNoetherianRing R] [Module.Finite R B] [AddCommGroup M] [Module B M] [AddCommGroup N]
    [Module B N] [Module R N] [IsScalarTower R B N] [Module.Finite B N]
    (σ : B →+* R) (hσ : Function.Surjective σ) (φ : M →+ N) (hφ : Function.Injective φ)
    (hφσ : ∀ (b : B) (m : M), φ (b • m) = σ b • φ m) : Module.Finite B M := by
  have : Module.Finite R N := Module.Finite.trans B N
  have : IsNoetherian R N := isNoetherian_of_isNoetherianRing_of_finite R N
  let P : Submodule R N :=
    { carrier := Set.range φ
      add_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨x + y, map_add φ x y⟩
      zero_mem' := ⟨0, map_zero φ⟩
      smul_mem' := by
        rintro r _ ⟨x, rfl⟩
        obtain ⟨b, rfl⟩ := hσ r
        exact ⟨b • x, hφσ b x⟩ }
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian P : P.FG)
  have hsP : ∀ n ∈ s, ∃ m, φ m = n := fun n hn => by
    have : n ∈ P := hs ▸ Submodule.subset_span hn
    exact this
  choose! g hg using hsP
  classical
  refine ⟨⟨s.image g, ?_⟩⟩
  rw [eq_top_iff]
  rintro m -
  let Q : Submodule B M := Submodule.span B (s.image g : Set M)
  let Q' : Submodule R N :=
    { carrier := φ '' Q
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, Q.add_mem hx hy, map_add φ x y⟩
      zero_mem' := ⟨0, Q.zero_mem, map_zero φ⟩
      smul_mem' := by
        rintro r _ ⟨x, hx, rfl⟩
        obtain ⟨b, rfl⟩ := hσ r
        exact ⟨b • x, Q.smul_mem b hx, hφσ b x⟩ }
  have hsQ' : (s : Set N) ⊆ Q' := by
    intro n hn
    refine ⟨g n, Submodule.subset_span ?_, hg n hn⟩
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem g hn)
  have hPQ : P ≤ Q' := hs ▸ Submodule.span_le.mpr hsQ'
  obtain ⟨m', hm', he⟩ := hPQ (⟨m, rfl⟩ : φ m ∈ P)
  exact hφ he ▸ hm'

theorem mvPolynomial_finite_frobenius_range (p : ℕ) [Fact p.Prime] (s e : ℕ) :
    Module.Finite (iterateFrobenius (MvPolynomial (Fin s) (ZMod p)) p e).range
      (MvPolynomial (Fin s) (ZMod p)) := by
  set B := MvPolynomial (Fin s) (ZMod p)
  set R := (iterateFrobenius B p e).range
  have hpow : ∀ x : B, x ^ p ^ e ∈ R := fun x => ⟨x, by rw [iterateFrobenius_def]⟩
  have hint : Algebra.IsIntegral R B := ⟨fun x => by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero (pow_ne_zero e (Fact.out : p.Prime).ne_zero)) ?_
    have : x ^ p ^ e = algebraMap R B ⟨x ^ p ^ e, hpow x⟩ := rfl
    rw [this]
    exact isIntegral_algebraMap⟩
  have hft : Algebra.FiniteType R B := by
    refine ⟨⟨Finset.univ.image MvPolynomial.X, ?_⟩⟩
    rw [eq_top_iff]
    rintro f -
    induction f using MvPolynomial.induction_on with
    | C a =>
      have : MvPolynomial.C a = algebraMap R B ⟨MvPolynomial.C a, ⟨MvPolynomial.C a, by
        rw [iterateFrobenius_def, ← map_pow, ZMod.pow_card_pow]⟩⟩ := rfl
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
    | add f g hf hg => exact Subalgebra.add_mem _ hf hg
    | mul_X f i hf =>
      refine Subalgebra.mul_mem _ hf (Algebra.subset_adjoin ?_)
      simp
  exact Algebra.IsIntegral.finite

theorem finite_integralClosure_mvPolynomial (p : ℕ) [Fact p.Prime] (s : ℕ)
    (F : Type*) [Field F] [Algebra (MvPolynomial (Fin s) (ZMod p)) F]
    [IsFractionRing (MvPolynomial (Fin s) (ZMod p)) F]
    (L : Type*) [Field L] [Algebra F L] [FiniteDimensional F L]
    [Algebra (MvPolynomial (Fin s) (ZMod p)) L]
    [IsScalarTower (MvPolynomial (Fin s) (ZMod p)) F L] :
    Module.Finite (MvPolynomial (Fin s) (ZMod p))
      (integralClosure (MvPolynomial (Fin s) (ZMod p)) L) := by
  set B := MvPolynomial (Fin s) (ZMod p)
  have hp : p.Prime := Fact.out
  have hinjBL : Function.Injective (algebraMap B L) := by
    rw [IsScalarTower.algebraMap_eq B F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective B F)
  have : CharP L p :=
    charP_of_injective_ringHom (f := (algebraMap B L).comp MvPolynomial.C)
      (hinjBL.comp (MvPolynomial.C_injective (Fin s) (ZMod p))) p
  set Ls := separableClosure F L
  have : ExpChar Ls p := ExpChar.prime hp
  have : IsScalarTower B Ls L := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply B F L, IsScalarTower.algebraMap_apply B F Ls,
      IsScalarTower.algebraMap_apply F Ls L]
  have : IsPurelyInseparable Ls L := separableClosure.isPurelyInseparable F L
  set e := IsPurelyInseparable.exponent Ls L
  let fr : L →+* Ls := IsPurelyInseparable.iterateFrobenius Ls L p (le_refl e)
  have hfr : ∀ y, algebraMap Ls L (fr y) = y ^ p ^ e := fun y =>
    IsPurelyInseparable.algebraMap_iterateFrobenius Ls p (le_refl e) y
  have hinjLs : Function.Injective (algebraMap Ls L) := (algebraMap Ls L).injective
  have : Algebra.IsSeparable F Ls := separableClosure.isSeparable F L
  have : Module.Finite B (integralClosure B Ls) :=
    IsIntegralClosure.finite B F Ls (integralClosure B Ls)
  have := mvPolynomial_finite_frobenius_range p s e
  have hint : ∀ y : integralClosure B L, IsIntegral B (fr y) := fun y =>
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom B Ls L) hinjLs).mp (by
      rw [IsScalarTower.toAlgHom_apply, hfr]
      exact y.2.pow _)
  let φ : integralClosure B L →+ integralClosure B Ls :=
    { toFun := fun y => ⟨fr y, hint y⟩
      map_zero' := by ext; simp
      map_add' := fun y z => by ext; simp }
  refine module_finite_of_semilinear (iterateFrobenius B p e).rangeRestrict
    (iterateFrobenius B p e).rangeRestrict_surjective φ ?_ ?_
  · intro y z h
    have h' : fr y = fr z := congrArg Subtype.val h
    exact Subtype.ext (fr.injective h')
  · intro b y
    apply Subtype.ext
    apply hinjLs
    change algebraMap Ls L (fr (b • (y : L))) =
      algebraMap Ls L (((iterateFrobenius B p e b : B) • fr y))
    rw [hfr, Algebra.smul_def, Algebra.smul_def, map_mul, hfr, iterateFrobenius_def, mul_pow,
      ← map_pow, ← IsScalarTower.algebraMap_apply]

theorem finite_integralClosure_of_charP (p : ℕ) [Fact p.Prime]
    (A : Type*) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A] [CharP A p]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L] :
    Module.Finite A (integralClosure A L) := by
  let : Algebra (ZMod p) A := ZMod.algebra A p
  have : Algebra.FiniteType (ZMod p) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod p) A
  obtain ⟨s, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg (ZMod p) A
  set B := MvPolynomial (Fin s) (ZMod p)
  let : Algebra B A := g.toRingHom.toAlgebra
  have : Module.Finite B A := hgfin
  let : Algebra B K := ((algebraMap A K).comp (algebraMap B A)).toAlgebra
  let : Algebra B L := ((algebraMap A L).comp (algebraMap B A)).toAlgebra
  have : IsScalarTower B A K := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B A L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B K L := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap A L (algebraMap B A x) = algebraMap K L (algebraMap A K (algebraMap B A x))
    exact IsScalarTower.algebraMap_apply A K L _
  have hinjBK : Function.Injective (algebraMap B K) :=
    (IsFractionRing.injective A K).comp hginj
  have : FaithfulSMul B K := (faithfulSMul_iff_algebraMap_injective B K).mpr hinjBK
  let : Algebra (FractionRing B) K := FractionRing.liftAlgebra B K
  let : Algebra (FractionRing B) L :=
    ((algebraMap K L).comp (algebraMap (FractionRing B) K)).toAlgebra
  have : IsScalarTower (FractionRing B) K L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B (FractionRing B) L := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply (FractionRing B) K L,
      ← IsScalarTower.algebraMap_apply B (FractionRing B) K,
      ← IsScalarTower.algebraMap_apply B K L]
  have : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  have : FiniteDimensional (FractionRing B) K := by
    obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule B A).FG)
    let T : Set K := algebraMap A K '' t
    have hTint : ∀ x ∈ T, IsIntegral (FractionRing B) x := by
      rintro _ ⟨a, -, rfl⟩
      have : IsIntegral B (algebraMap A K a) :=
        (Algebra.IsIntegral.isIntegral a).map (IsScalarTower.toAlgHom B A K)
      exact this.tower_top
    have : Finite T := (t.finite_toSet.image _).to_subtype
    have hfd := IntermediateField.finiteDimensional_adjoin hTint
    have htop : IntermediateField.adjoin (FractionRing B) T = ⊤ := by
      rw [eq_top_iff]
      rintro x -
      have hA : ∀ a : A, algebraMap A K a ∈ IntermediateField.adjoin (FractionRing B) T := by
        intro a
        have ha : a ∈ Submodule.span B (t : Set A) := ht ▸ Submodule.mem_top
        induction ha using Submodule.span_induction with
        | mem y hy => exact IntermediateField.subset_adjoin (FractionRing B) T ⟨y, hy, rfl⟩
        | zero => simp
        | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
        | smul b y _ hy =>
          rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
            IsScalarTower.algebraMap_apply B (FractionRing B) K]
          exact mul_mem (IntermediateField.algebraMap_mem _ _) hy
      obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A) x
      exact div_mem (hA a) (hA b)
    rw [htop] at hfd
    exact (IntermediateField.topEquiv (F := FractionRing B) (E := K)).toLinearEquiv.finiteDimensional
  have : FiniteDimensional (FractionRing B) L := Module.Finite.trans K L
  have hB := finite_integralClosure_mvPolynomial p s (FractionRing B) L
  have hle : (integralClosure A L).toSubmodule.restrictScalars B ≤
      (integralClosure B L).toSubmodule := fun y hy => isIntegral_trans (R := B) (A := A) y hy
  have : IsNoetherian B (integralClosure B L).toSubmodule :=
    isNoetherian_of_isNoetherianRing_of_finite B (integralClosure B L)
  have : IsNoetherian B ((integralClosure A L).toSubmodule.restrictScalars B) :=
    isNoetherian_of_le hle
  have : Module.Finite B (integralClosure A L) :=
    Module.IsNoetherian.finite B ((integralClosure A L).toSubmodule.restrictScalars B)
  exact Module.Finite.of_restrictScalars_finite B A (integralClosure A L)

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteIntegralClosureLocal
section
set_option maxSynthPendingDepth 1

open scoped nonZeroDivisors

namespace GroundTheory.Heights₂.Heights.Model

theorem module_finite_of_forall_isMaximal {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (h : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal →
      ∃ r ∉ 𝔪, ∃ N : Submodule A M, N.FG ∧ ∀ x : M, ∃ n : ℕ, r ^ n • x ∈ N) :
    Module.Finite A M := by
  classical
  choose! r hr N hN hx using h
  set s : Set A := r '' {𝔪 | 𝔪.IsMaximal}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hr 𝔪 h𝔪 (hle (Ideal.subset_span ⟨𝔪, h𝔪, rfl⟩))
  obtain ⟨t, hts, ht⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
  have hmt : ∀ a ∈ t, ∃ 𝔪 : Ideal A, 𝔪.IsMaximal ∧ r 𝔪 = a := fun a ha => hts ha
  choose! m hm hrm using hmt
  let P : Submodule A M := ⨆ a ∈ t, N (m a)
  have hP : P.FG := Submodule.fg_biSup t _ fun a ha => hN (m a) (hm a ha)
  suffices hPt : P = ⊤ from ⟨hPt ▸ hP⟩
  rw [eq_top_iff]
  rintro x -
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem P (t : Set A) ht x ?_
  rintro ⟨a, ha⟩
  obtain ⟨n, hn⟩ := hx (m a) (hm a ha) x
  refine ⟨n, ?_⟩
  have hle : N (m a) ≤ P := le_iSup₂ (f := fun a (_ : a ∈ t) => N (m a)) a ha
  show a ^ n • x ∈ P
  rw [← hrm a ha]
  exact hle hn

theorem exists_pow_smul_mem_of_weaklyQuasiFiniteAt
    (A : Type*) [CommRing A] [IsDomain A] [CharZero A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (d : ℕ) [Algebra (MvPolynomial (Fin d) ℤ) A]
    (hinj : Function.Injective (algebraMap (MvPolynomial (Fin d) ℤ) A))
    [Algebra.FiniteType (MvPolynomial (Fin d) ℤ) A]
    (𝔪 : Ideal A) [𝔪.IsPrime] [Algebra.WeaklyQuasiFiniteAt (MvPolynomial (Fin d) ℤ) 𝔪] :
    ∃ r ∉ 𝔪, ∃ N : Submodule A (integralClosure A K), N.FG ∧
      ∀ x : integralClosure A K, ∃ n : ℕ, r ^ n • x ∈ N := by
  classical
  set C := MvPolynomial (Fin d) ℤ
  have hZ := Algebra.ZariskisMainProperty.of_finiteType_of_weaklyQuasiFiniteAt (R := C) 𝔪
  obtain ⟨r, hr𝔪, hrint, hm⟩ := Algebra.zariskisMainProperty_iff.mp hZ
  choose m hm using hm
  let _ : Algebra C K := ((algebraMap A K).comp (algebraMap C A)).toAlgebra
  have : IsScalarTower C A K := IsScalarTower.of_algebraMap_eq' rfl
  have hinjCK : Function.Injective (algebraMap C K) := (IsFractionRing.injective A K).comp hinj
  have : FaithfulSMul C K := (faithfulSMul_iff_algebraMap_injective C K).mpr hinjCK
  let _ : Algebra (FractionRing C) K := FractionRing.liftAlgebra C K
  have hr0 : algebraMap A K r ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective A K)]
    exact fun h => hr𝔪 (h ▸ 𝔪.zero_mem)
  have hintK : ∀ a : A, IsIntegral C a → IsIntegral (FractionRing C) (algebraMap A K a) :=
    fun a ha => (ha.map (IsScalarTower.toAlgHom C A K)).tower_top
  have : FiniteDimensional (FractionRing C) K := by
    obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := C) (A := A)
    let T : Set K := insert (algebraMap A K r) ((fun x => algebraMap A K (r ^ m x * x)) '' t)
    have hTint : ∀ z ∈ T, IsIntegral (FractionRing C) z := by
      rintro z (rfl | ⟨x, -, rfl⟩)
      · exact hintK r hrint
      · exact hintK _ (hm x)
    have : Finite T := ((t.finite_toSet.image _).insert _).to_subtype
    have hfd := IntermediateField.finiteDimensional_adjoin hTint
    have htop : IntermediateField.adjoin (FractionRing C) T = ⊤ := by
      rw [eq_top_iff]
      rintro z -
      have hA : ∀ a : A, algebraMap A K a ∈ IntermediateField.adjoin (FractionRing C) T := by
        intro a
        have ha : a ∈ Algebra.adjoin C (t : Set A) := ht ▸ Algebra.mem_top
        induction ha using Algebra.adjoin_induction with
        | mem x hx =>
          have hr' : algebraMap A K r ∈ IntermediateField.adjoin (FractionRing C) T :=
            IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
          have hx' : algebraMap A K (r ^ m x * x) ∈ IntermediateField.adjoin (FractionRing C) T :=
            IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ ⟨x, hx, rfl⟩)
          have : algebraMap A K x = algebraMap A K (r ^ m x * x) / algebraMap A K r ^ m x := by
            rw [map_mul, map_pow, mul_div_cancel_left₀ _ (pow_ne_zero _ hr0)]
          rw [this]
          exact div_mem hx' (pow_mem hr' _)
        | algebraMap c =>
          rw [← IsScalarTower.algebraMap_apply C A K, IsScalarTower.algebraMap_apply C (FractionRing C) K]
          exact IntermediateField.algebraMap_mem _ _
        | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
        | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
      obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A) z
      exact div_mem (hA a) (hA b)
    rw [htop] at hfd
    exact (IntermediateField.topEquiv (F := FractionRing C) (E := K)).toLinearEquiv.finiteDimensional
  have : CharZero (FractionRing C) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective C (FractionRing C))
  have : Algebra.IsSeparable (FractionRing C) K := Algebra.IsSeparable.of_integral _ _
  have : Module.Finite C (integralClosure C K) :=
    IsIntegralClosure.finite C (FractionRing C) K (integralClosure C K)
  obtain ⟨g, hg⟩ := (Module.Finite.fg_top : (⊤ : Submodule C (integralClosure C K)).FG)
  let ι : integralClosure C K → integralClosure A K := fun y => ⟨y.1, y.2.tower_top⟩
  let N : Submodule A (integralClosure A K) := Submodule.span A (ι '' g)
  have hN : ∀ y : integralClosure C K, ι y ∈ N := by
    intro y
    have hy : y ∈ Submodule.span C (g : Set (integralClosure C K)) := hg ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => exact N.zero_mem
    | add y z _ _ hy hz =>
      have : ι (y + z) = ι y + ι z := rfl
      rw [this]; exact N.add_mem hy hz
    | smul c y _ hy =>
      have : ι (c • y) = algebraMap C A c • ι y := by
        apply Subtype.ext
        change c • (y : K) = algebraMap C A c • (y : K)
        rw [Algebra.smul_def, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
      rw [this]; exact N.smul_mem _ hy
  refine ⟨r, hr𝔪, N, Submodule.fg_span (g.finite_toSet.image ι), fun x => ?_⟩
  obtain ⟨P, hPm, hPx⟩ := x.2
  set D := P.natDegree
  set M := (Finset.range (D + 1)).sup fun i => m (P.coeff i)
  let A₀ := integralClosure C A
  have hcoeff : ∀ i, IsIntegral C ((P.scaleRoots (r ^ M)).coeff i) := by
    intro i
    rw [Polynomial.coeff_scaleRoots]
    rcases lt_trichotomy i D with hi | hi | hi
    · have hmi : m (P.coeff i) ≤ M :=
        Finset.le_sup (f := fun i => m (P.coeff i)) (Finset.mem_range.mpr (by omega))
      obtain ⟨k, hk⟩ : ∃ k, D - i = k + 1 := ⟨D - i - 1, by omega⟩
      have : P.coeff i * (r ^ M) ^ (D - i) =
          (r ^ m (P.coeff i) * P.coeff i) * (r ^ (M - m (P.coeff i)) * (r ^ M) ^ k) := by
        rw [hk, pow_succ]
        rw [show (r ^ M) = r ^ m (P.coeff i) * r ^ (M - m (P.coeff i)) by
          rw [← pow_add, Nat.add_sub_cancel' hmi]]
        ring
      rw [this]
      exact (hm _).mul ((hrint.pow _).mul ((hrint.pow _).pow _))
    · rw [hi, Nat.sub_self, pow_zero, mul_one, ← Polynomial.leadingCoeff, hPm.leadingCoeff]
      exact isIntegral_one
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul]
      exact isIntegral_zero
  have hlifts : P.scaleRoots (r ^ M) ∈ Polynomial.lifts (algebraMap A₀ A) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    exact ⟨⟨_, hcoeff i⟩, rfl⟩
  have hmonic : (P.scaleRoots (r ^ M)).Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_scaleRoots,
      Polynomial.coeff_scaleRoots_natDegree, hPm.leadingCoeff]
  obtain ⟨Q, hQ, -, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hmonic
  have hint : IsIntegral C (algebraMap A K (r ^ M) * (x : K)) := by
    have h0 : Polynomial.aeval (algebraMap A K (r ^ M) * (x : K)) (P.scaleRoots (r ^ M)) = 0 :=
      Polynomial.scaleRoots_aeval_eq_zero (by rw [Polynomial.aeval_def]; exact hPx)
    have h1 : IsIntegral A₀ (algebraMap A K (r ^ M) * (x : K)) := by
      refine ⟨Q, hQm, ?_⟩
      rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap A, hQ]
      exact h0
    exact isIntegral_trans (R := C) (A := A₀) _ h1
  refine ⟨M, ?_⟩
  have : r ^ M • x = ι ⟨_, hint⟩ := by
    apply Subtype.ext
    change r ^ M • (x : K) = _
    rw [Algebra.smul_def]
  rw [this]
  exact hN _

end GroundTheory.Heights₂.Heights.Model
end

