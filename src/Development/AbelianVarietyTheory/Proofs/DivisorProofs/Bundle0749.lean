module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0726
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Formalism.MeanHeightDescent.AverageDegreeBounds.GlobalBoundRefinements
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0733
public import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0595
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConstantExponentsFinite
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder Pointwise

namespace GlobalTheory.ExponentsFinite

theorem val_le_one {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) {p s : ℕ}
    (hp : ((p : ℕ) : 𝓞 K) ∈ P.asIdeal) (hs : Nat.Coprime s p) {x : K} (hx : IsIntegral ℤ ((s : K) * x)) :
    P.valuation K x ≤ 1 := by
  have hsP : ((s : ℕ) : 𝓞 K) ∉ P.asIdeal := by
    intro h
    obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hs).map (Int.castRingHom (𝓞 K))
    simp only [eq_intCast, Int.cast_natCast] at hab
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ h) (P.asIdeal.mul_mem_left _ hp)))
  have h1 := (P.valuation_eq_one_iff_notMem (K := K)).2 hsP
  have h2 := P.valuation_le_one (K := K) (⟨_, hx⟩ : 𝓞 K)
  rw [map_natCast] at h1
  change P.valuation K ((s : K) * x) ≤ 1 at h2
  rwa [map_mul, h1, one_mul] at h2

theorem val_det_le_one {K ι Γ : Type} [Field K] [Fintype ι] [DecidableEq ι] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (f : (ι → K) →ₗ[K] (ι → K)) (hf : ∀ i j, v (f (Pi.single j 1) i) ≤ 1) :
    v (LinearMap.det f) ≤ 1 := by
  rw [← LinearMap.det_toMatrix', Matrix.det_apply']
  have : ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : K) * ∏ i, LinearMap.toMatrix' f (σ i) i ∈ v.integer := by
    refine Subring.sum_mem _ fun σ _ => Subring.mul_mem _ (intCast_mem _ _) (Subring.prod_mem _ fun i _ => ?_)
    rw [LinearMap.toMatrix'_apply]
    exact hf _ _
  exact this

theorem val_det_eq_one {K ι Γ : Type} [Field K] [Fintype ι] [DecidableEq ι] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (f : (ι → K) ≃ₗ[K] (ι → K)) (hf : ∀ i j, v (f (Pi.single j 1) i) ≤ 1)
    (hf' : ∀ i j, v (f.symm (Pi.single j 1) i) ≤ 1) :
    v (LinearMap.det (f : (ι → K) →ₗ[K] (ι → K))) = 1 := by
  have h1 := val_det_le_one v (f : (ι → K) →ₗ[K] (ι → K)) hf
  have h2 := val_det_le_one v (f.symm : (ι → K) →ₗ[K] (ι → K)) hf'
  have h3 := congrArg v (LinearEquiv.det_mul_det_symm f)
  rw [map_mul, map_one] at h3
  refine le_antisymm h1 ?_
  calc 1 = _ := h3.symm
    _ ≤ v (LinearMap.det (f : (ι → K) →ₗ[K] (ι → K))) * 1 := by gcongr
    _ = _ := mul_one _

theorem exists_den {K ι : Type} [Field K] [NumberField K] [Finite ι] (c : ι → K) :
    ∃ n : ℕ, 0 < n ∧ ∀ i, IsIntegral ℤ ((n : K) * c i) := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := K) (Finset.univ.image c)
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, fun i => ?_⟩
  have h := hy (c i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [zsmul_eq_mul] at h
  rcases Int.natAbs_eq y with h1 | h1
  · rw [h1, Int.cast_natCast] at h; exact h
  · rw [h1, Int.cast_neg, Int.cast_natCast, neg_mul] at h; simpa using h.neg

theorem exists_den_fg {K E ι κ : Type} [Field K] [NumberField K] [AddCommGroup E] [Finite ι] [Fintype κ]
    (A : Submodule ℤ E) (hA : A.FG) (g : (κ → E) →+ (ι → K)) :
    ∃ n : ℕ, 0 < n ∧ ∀ x : κ → E, (∀ a, x a ∈ A) → ∀ w, IsIntegral ℤ ((n : K) * g x w) := by
  classical
  obtain ⟨S, hS⟩ := hA
  obtain ⟨n, hn, h⟩ := exists_den (fun t : S × κ × ι => g (Pi.single t.2.1 (t.1 : E)) t.2.2)
  refine ⟨n, hn, fun x hx w => ?_⟩
  have key : ∀ a, ∀ y ∈ Submodule.span ℤ (S : Set E), IsIntegral ℤ ((n : K) * g (Pi.single a y) w) := by
    intro a y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact h (⟨y, hy⟩, a, w)
    | zero => simpa using isIntegral_zero
    | add y z _ _ hy hz => rw [Pi.single_add, map_add (f := _), Pi.add_apply, mul_add]; exact hy.add hz
    | smul c y _ hy =>
      rw [Pi.single_smul, map_zsmul, Pi.smul_apply, mul_smul_comm]; exact hy.zsmul c
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.univ_sum_single x, map_sum, Finset.sum_apply, Finset.mul_sum]
  exact IsIntegral.sum _ fun a _ => key a _ (hS ▸ hx a)

theorem one_mem (D : D7) : (1 : D.host.E) ∈ D.host.AA0 := by
  have hb : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 fun h => by
      have h3 : D.host.𝔟 ⊔ D.host.conj • D.host.𝔟 = ⊤ := D.host.𝔟_spec.2
      simp [h] at h3
  refine (FractionalIdeal.mem_inv_iff hb).2 fun y hy => ?_
  rw [one_mul]; exact FractionalIdeal.coeIdeal_le_one hy

theorem yFinite : ∀ (D : D7) (γ₀ : IsoK D) (k : KapChoice γ₀), k.YFinite := by
  classical
  intro D γ₀ k
  have hfg : ((D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).restrictScalars ℤ).FG :=
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl D.host.AA0).restrictScalars
  obtain ⟨n, hn, hnx⟩ := exists_den_fg _ hfg γ₀.g.toLinearMap.toAddMonoidHom
  obtain ⟨m, hm, hmx⟩ := exists_den
    (fun t : (Fin 4 × D.what₂.Tau) × Fin 4 => γ₀.g.symm (Pi.single t.1 1) t.2)
  refine (Set.finite_le_nat (n * m)).subset ?_
  rintro p ⟨hp, hsp, hy⟩
  by_contra hlt
  have hlt' : n * m < p := not_le.1 hlt
  have hcop : Nat.Coprime (n * m) p := (Nat.coprime_of_lt_prime (by positivity) hlt' hp).symm
  have hcn : Nat.Coprime n p := Nat.Coprime.coprime_mul_right hcop
  have hcm : Nat.Coprime m p := Nat.Coprime.coprime_mul_left hcop
  obtain ⟨h1, h2⟩ := k.gaP_at p hp hsp
  have hP := k.pp_over p hp hsp
  apply hy
  unfold KapChoice.yP ordK IsoK.detRel
  rw [val_det_eq_one]
  · simp
  · intro i j
    obtain ⟨s, hs, hsx⟩ := h1 (m • γ₀.g.symm (Pi.single j 1)) (fun a => by
      have := (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem ⟨_, hmx (j, a)⟩ (one_mem D)
      change ((m : D.host.E) * γ₀.g.symm (Pi.single j 1) a) * 1 ∈ D.host.AA0 at this
      simpa using this)
    obtain ⟨r, hr⟩ := hsx i
    refine val_le_one _ hP (Nat.Coprime.mul_left hs hcm) ?_
    have hi : IsIntegral ℤ (algebraMap (𝓞 D.host.K) D.host.K r) := r.2
    rw [hr, map_nsmul, Pi.smul_apply, nsmul_eq_mul, ← mul_assoc] at hi
    simpa using hi
  · intro i j
    obtain ⟨s, hs, hsx⟩ := h2 (Pi.single j 1) (fun w => by
      by_cases hw : w = j
      · subst hw; simp
      · simp [hw])
    have hi := hnx (s • (k.gaP p).g.symm (Pi.single j 1)) (fun a => by
      have := hsx a
      simpa using this) i
    refine val_le_one _ hP (Nat.Coprime.mul_left hcn hs) ?_
    rw [map_nsmul, Pi.smul_apply, nsmul_eq_mul, ← mul_assoc] at hi
    simpa using hi

end GlobalTheory.ExponentsFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeMovePreservingLocalParts
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory.SemilocalBasis

def awayFrom {R : Type} [CommRing R] [IsDomain R] (SB : Finset (HeightOneSpectrum R)) :
    Submonoid R where
  carrier := {s | s ≠ 0 ∧ ∀ P ∈ SB, s ∉ P.asIdeal}
  one_mem' := ⟨one_ne_zero, fun P _ h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_ne_zero ha.1 hb.1, fun P hP h =>
    (P.isPrime.mem_or_mem h).elim (ha.2 P hP) (hb.2 P hP)⟩

theorem awayFrom_le {R : Type} [CommRing R] [IsDomain R] (SB : Finset (HeightOneSpectrum R)) :
    awayFrom SB ≤ nonZeroDivisors R := fun _ h => mem_nonZeroDivisors_of_ne_zero h.1

theorem isPrincipalIdealRing_awayFrom {R : Type} [CommRing R] [IsDedekindDomain R]
    (SB : Finset (HeightOneSpectrum R)) (A : Type) [CommRing A] [IsDomain A] [Algebra R A]
    [IsLocalization (awayFrom SB) A] : IsPrincipalIdealRing A := by
  classical
  haveI : IsDedekindDomain A := IsLocalization.isDedekindDomain R (awayFrom_le SB) A
  apply IsPrincipalIdealRing.of_finite_primes
  let T : Finset (Ideal R) := insert ⊥ (SB.image (·.asIdeal))
  have hT : ∀ Q ∈ T, Q.IsPrime := by
    intro Q hQ
    rcases Finset.mem_insert.1 hQ with rfl | hQ
    · exact Ideal.isPrime_bot
    · obtain ⟨P, _, rfl⟩ := Finset.mem_image.1 hQ
      exact P.isPrime
  have hinj : Function.Injective (fun I : Ideal A => I.comap (algebraMap R A)) := by
    intro I J h
    rw [← IsLocalization.map_under (awayFrom SB) A I, ← IsLocalization.map_under (awayFrom SB) A J]
    exact congrArg _ h
  refine ((T.finite_toSet).preimage hinj.injOn).subset ?_
  intro I hI
  have hI' : I.IsPrime := hI
  have hsub : ((I.comap (algebraMap R A) : Ideal R) : Set R) ⊆ ⋃ i ∈ (T : Set (Ideal R)), ((id i : Ideal R) : Set R) := by
    intro s hs
    by_contra hn
    simp only [Set.mem_iUnion, not_exists, id] at hn
    have hS : s ∈ awayFrom SB := by
      refine ⟨fun h0 => hn ⊥ (by simp [T]) (by simp [h0]), fun P hP h => hn P.asIdeal ?_ h⟩
      exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hP))
    exact hI'.ne_top (Ideal.eq_top_of_isUnit_mem _ hs (IsLocalization.map_units A ⟨s, hS⟩))
  obtain ⟨Q, hQ, hle⟩ := (Ideal.subset_union_prime (⊥ : Ideal R) ⊥ (fun i hi _ _ => hT i hi)).1 hsub
  show I.comap (algebraMap R A) ∈ (T : Set (Ideal R))
  by_cases h0 : I.comap (algebraMap R A) = ⊥
  · rw [h0]; simp [T]
  · have hmax : (I.comap (algebraMap R A)).IsMaximal :=
      Ring.DimensionLEOne.maximalOfPrime h0 (Ideal.comap_isPrime _ _)
    rw [hmax.eq_of_le (hT Q hQ).ne_top hle]
    exact hQ

theorem exists_basis {R : Type} [CommRing R] [IsDedekindDomain R] (K : Type) [Field K]
    [Algebra R K] [IsFractionRing R K] (n : ℕ) (SB : Finset (HeightOneSpectrum R))
    (N : Submodule R (Fin n → K)) (hN : Submodule.IsFullLattice K N) :
    ∃ v : Module.Basis (Fin n) K (Fin n → K), (∀ i, v i ∈ N) ∧
      ∀ x ∈ N, ∃ s ∈ awayFrom SB, s • x ∈ Submodule.span R (Set.range v) := by
  classical
  let A : Subalgebra R K := Localization.subalgebra K (awayFrom SB) (awayFrom_le SB)
  haveI : IsLocalization (awayFrom SB) A :=
    Localization.subalgebra.isLocalization_subalgebra K (awayFrom SB) (awayFrom_le SB)
  haveI : IsPrincipalIdealRing A := isPrincipalIdealRing_awayFrom SB A
  haveI : IsFractionRing A K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (awayFrom SB) A K

  have clear : ∀ (X : Set (Fin n → K)) (x : Fin n → K), x ∈ Submodule.span A X →
      ∃ s ∈ awayFrom SB, s • x ∈ Submodule.span R X := by
    intro X x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_mem _, by simpa using Submodule.subset_span hx⟩
    | zero => exact ⟨1, one_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨t, ht, hty⟩ := hy
      refine ⟨s * t, mul_mem hs ht, ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hsx
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hty
    | smul a x _ hx =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨⟨r, t⟩, hr⟩ := IsLocalization.surj (awayFrom SB) a
      refine ⟨s * t, mul_mem hs t.2, ?_⟩
      have : (t : R) • a • x = r • x := by
        rw [← algebraMap_smul A (t : R), ← mul_smul, mul_comm, hr, algebraMap_smul]
      rw [mul_smul, this, smul_comm]
      exact Submodule.smul_mem _ _ hsx
  let M : Submodule A (Fin n → K) := Submodule.span A (N : Set (Fin n → K))
  haveI hMlat : Submodule.IsLattice K M := by
    apply Submodule.IsLattice.of_fg K
    obtain ⟨X, hX⟩ := hN.fg
    refine ⟨X, ?_⟩
    simp only [M, ← hX]
    exact (Submodule.span_span_of_tower R A _).symm
  haveI hM : Submodule.IsFullLattice K M := by
    refine ⟨?_⟩
    simp only [M]
    rw [Submodule.span_span_of_tower]
    exact hN.span_eq_top
  haveI : Module.Free A M := Submodule.IsLattice.free K M
  haveI : Module.Finite A M := Module.Finite.iff_fg.2 hM.fg
  have hrk : Module.finrank A M = n := by
    simpa using ((Submodule.IsFullLattice.finrank_eq K M).trans (Module.finrank_fintype_fun_eq_card K))
  let b : Module.Basis (Fin n) A M := Module.finBasisOfFinrankEq A M hrk
  have hb : ∀ i, ∃ s ∈ awayFrom SB, s • (b i : Fin n → K) ∈ N := by
    intro i
    obtain ⟨s, hs, h⟩ := clear _ _ (b i).2
    exact ⟨s, hs, by simpa using h⟩
  choose s hs hsb using hb
  let b' : Module.Basis (Fin n) A M :=
    b.isUnitSMul (w := fun i => algebraMap R A (s i)) (fun i => IsLocalization.map_units A ⟨s i, hs i⟩)
  have hb' : ∀ i, (b' i : Fin n → K) = s i • (b i : Fin n → K) := by
    intro i
    simp only [b', Module.Basis.isUnitSMul_apply, Submodule.coe_smul, algebraMap_smul]
    try rfl
  refine ⟨b'.extendOfIsFullLattice K, fun i => ?_, fun x hx => ?_⟩
  · rw [Module.Basis.extendOfIsFullLattice_apply, hb']
    exact hsb i
  · apply clear
    have hxM : x ∈ M := Submodule.subset_span hx
    have h1 := b'.sum_repr ⟨x, hxM⟩
    have h2 : x = ∑ i, b'.repr ⟨x, hxM⟩ i • (b' i : Fin n → K) := by
      have := congrArg Subtype.val h1
      rw [AddSubmonoidClass.coe_finsetSum] at this
      exact this.symm
    rw [h2]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, ?_⟩)
    rw [Module.Basis.extendOfIsFullLattice_apply]

theorem mem_localization_iff {R : Type} [CommRing R] {W : Type} [AddCommGroup W] [Module R W]
    (p : Ideal R) [p.IsPrime] (L : Submodule R W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s, s ∉ p ∧ s • x ∈ L := Iff.rfl

theorem stdLat_eq_span (E : Type) [Field E] (n : ℕ) :
    Formalism.L2.Col.stdLat E n = Submodule.span (𝓞 E) (Set.range (Pi.basisFun E (Fin n))) := by
  classical
  apply le_antisymm
  · intro x hx
    have hx' : ∀ i, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = x i := fun i =>
      Submodule.mem_one.1 (hx i (Set.mem_univ _))
    choose r hr using hx'
    have : x = ∑ i, r i • Pi.basisFun E (Fin n) i := by
      conv_lhs => rw [← (Pi.basisFun E (Fin n)).sum_repr x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.basisFun_repr, ← hr, algebraMap_smul]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩ j _
    rw [Pi.basisFun_apply]
    by_cases h : j = i
    · subst h
      exact Submodule.mem_one.2 ⟨1, by simp⟩
    · exact Submodule.mem_one.2 ⟨0, by simp [h]⟩

theorem exists_equiv (E : Type) [Field E] [NumberField E] (n : ℕ)
    (SB : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E n))
    (hN : Submodule.IsFullLattice E N) :
    ∃ γ : Sp E n ≃ₗ[E] Sp E n, (∀ x ∈ Formalism.L2.Col.stdLat E n, γ x ∈ N) ∧
      ∀ P ∈ SB, ∀ x, γ x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N ↔
        x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.L2.Col.stdLat E n) := by
  obtain ⟨v, hv, hgen⟩ := exists_basis E n SB N hN
  let γ : Sp E n ≃ₗ[E] Sp E n := (Pi.basisFun E (Fin n)).equiv v (Equiv.refl _)
  have key : ∀ x, x ∈ Formalism.L2.Col.stdLat E n ↔ γ x ∈ Submodule.span (𝓞 E) (Set.range v) := by
    intro x
    have hmap : (Formalism.L2.Col.stdLat E n).map ((γ.restrictScalars (𝓞 E)) : Sp E n →ₗ[𝓞 E] Sp E n)
        = Submodule.span (𝓞 E) (Set.range v) := by
      rw [stdLat_eq_span, Submodule.map_span, ← Set.range_comp]
      congr 2
      funext i
      exact (Pi.basisFun E (Fin n)).equiv_apply i v (Equiv.refl _)
    rw [← hmap]
    constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨y, hy, h⟩
      have : y = x := γ.injective h
      exact this ▸ hy
  have hle : Submodule.span (𝓞 E) (Set.range v) ≤ N := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hv i
  have hsm : ∀ (s : 𝓞 E) x, γ (s • x) = s • γ x := fun s x =>
    (γ.restrictScalars (𝓞 E)).map_smul s x
  refine ⟨γ, fun x hx => hle ((key x).1 hx), fun P hP x => ?_⟩
  rw [mem_localization_iff, mem_localization_iff]
  constructor
  · rintro ⟨s, hs, h⟩
    obtain ⟨t, ht, h'⟩ := hgen _ h
    refine ⟨t * s, fun hm => (P.isPrime.mem_or_mem hm).elim (ht.2 P hP) hs, ?_⟩
    rw [key, hsm, mul_smul]
    exact h'
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, hle ?_⟩
    rw [← hsm]
    exact (key _).1 h

end GlobalTheory.SemilocalBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFrLifts
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNorms

theorem liftFr_lifts : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (w : SG), (∀ x, d.1.liftFr w x ∈ d.1.at w.1 ↔ x ∈ stdAt E n w.1) ∧ ∀ x ∈ stdAt E n w.1, d.1.be w (d.1.liftFr w x) = redV w.1 x :=
  fun _ _ _ _ _ _ _ d w => GlobalTheory.TopStep.liftFr_spec d.2 w

end GlobalTheory.ColNorms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDivPredMemOfPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem log_div_pred_mem_of_prime {p : ℕ} (hp : p.Prime) :
    0 ≤ Real.log p / ((p : ℝ) - 1) ∧ Real.log p / ((p : ℝ) - 1) ≤ 1 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  refine ⟨div_nonneg (Real.log_nonneg (by linarith)) hpos.le, ?_⟩
  rw [div_le_one hpos]
  exact Real.log_le_sub_one_of_pos (by linarith)

end GlobalTheory.MeanTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLeLOfLeCond
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory.ColumnNormCompare.SizeRows

variable {D : D7} {large₂ : SizeData₂ D}

theorem one_le_b (s : Scale) : 1 ≤ s.b := by
  unfold Scale.b Scale.L
  have := s.one_lt_alt
  exact Real.one_le_exp (by positivity)

theorem condE_le_b (P : ParameterChoice' D large₂) : (LevelStarExponents.condE D : ℝ) ≤ large₂.sc.b := by
  have h := P.condE_le
  have hb := one_le_b large₂.sc
  have h1 : large₂.sc.b ^ ((1 : ℝ) / 2) ≤ large₂.sc.b := by
    simpa using Real.rpow_le_rpow_of_exponent_le hb (show (1 : ℝ) / 2 ≤ 1 by norm_num)
  have ht : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ large₂.t_win.1
  have hc : (LevelStarExponents.condE D : ℝ) ≤ (LevelStarExponents.condE D : ℝ) ^ 36 := by
    exact_mod_cast Nat.le_self_pow (by norm_num) _
  have h2 : (LevelStarExponents.condE D : ℝ) ^ 36 ≤ (LevelStarExponents.condE D : ℝ) ^ 36 * (D.R.t : ℝ) ^ 150 :=
    le_mul_of_one_le_right (by positivity) ht
  linarith

theorem log_le_L_of_le_cond (P : ParameterChoice' D large₂) {p : ℕ} (hp : 0 < p) (h : p ≤ LevelStarExponents.condE D) :
    Real.log p ≤ large₂.sc.L := by
  have h1 : (p : ℝ) ≤ Real.exp large₂.sc.L := le_trans (by exact_mod_cast h) (condE_le_b P)
  exact (Real.log_le_iff_le_exp (by exact_mod_cast hp)).2 h1

theorem f_mul_N_le_b (P : ParameterChoice' D large₂) (h4 : 4 * placeRankTwoOne.NN D ^ 3 ≤ large₂.etaSz) :
    (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ≤ large₂.sc.b := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hk' : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hf : (0 : ℝ) < D.R.f := by
    have : 0 < D.R.f := by
      have hn : 0 < D.R.n := D.R.ord_pos
      unfold Ranks.f
      omega
    exact_mod_cast this
  have ht := large₂.t_win.1
  have he := large₂.etaSz_pos
  have h := P.eta_le
  rw [le_div_iff₀ (by positivity)] at h
  have hN : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 3 := by
    exact_mod_cast Nat.le_self_pow (by norm_num) _
  have hN0 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 3 := by positivity
  unfold placeRankTwoOne.NN at h4
  have h5 : (D.R.N D.R.m : ℝ) ≤ large₂.etaSz := by linarith
  have h6 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3 := one_le_pow₀ ht
  have h7 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ 3 := one_le_pow₀ hk'
  calc (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) = (D.R.N D.R.m : ℝ) * (1 * D.R.f * 1) := by ring
    _ ≤ large₂.etaSz * ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3) := by gcongr
    _ ≤ _ := h

theorem eTau_tauPl (z : RPl D.R) : (D.eTau (tauPl D z) : D.R.GG) = G.plGG D z := by
  unfold tauPl
  rw [Equiv.apply_symm_apply]

theorem not_top_of (z : RPl D.R) (hz : ¬ PlaceLogThetaBounds.IsTopPl (numDatumOfParameters D large₂) z) :
    (D.eTau (tauPl D z) : D.R.GG) ∉ D.host.topPlaces := by
  rw [eTau_tauPl]
  intro h
  unfold Host.topPlaces at h
  obtain ⟨t, ht, he⟩ := Finset.mem_image.1 h
  obtain ⟨b, s⟩ := z
  cases b
  · have h1 : D.R.tau1 t = D.R.tau1 s := he
    have h2 : t = s := D.R.toFrame.tau1_injective h1
    subst h2
    exact hz ⟨rfl, ht⟩
  · have h1 : D.R.tau1 t = D.R.tau2 s := he
    exact (factPlaces D.R.toFrame).2 _ _ h1

end GlobalTheory.ColumnNormCompare.SizeRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedIsoPowerBundleRatioUnitEqOneStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalised_isoPowerBundle_ratio_unit_eq_one : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), IsAbelianScheme A → L.IsLB → M.IsLB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) (α α₂ : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)) (v : Γ(A'.left, ⊤)ˣ), IsTest A B L M t A' B' φA' φB' Φ' → ψA ≫ (snd (topS Rg) A).left = φA' → ψB ≫ (snd (topS Rg) B).left = φB' → (∀ p, α.s p = res (le_top : (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ≤ ⊤) v * α₂.s p) → RigEq L M k eA eB t Φ' ψA ψB α → RigEq L M k eA eB t Φ' ψA ψB α₂ → v = 1 := by
  first | (exact @GlobalTheory.HomFixUnit.ratio_unit_eq_one) | (exact GlobalTheory.HomFixUnit.ratio_unit_eq_one) | (intros; apply GlobalTheory.HomFixUnit.ratio_unit_eq_one  <;> assumption)
end

