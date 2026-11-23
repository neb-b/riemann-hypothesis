module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIntegersTensorEqLetterwiseProductAinf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0262
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0265
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfFrobeniusEquationCyclotomicFixed
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachInclusionPowerSeriesIntoOneTmulAinf
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Prism GlobalTheory.PrismS
open scoped Formalism.Per

namespace GlobalTheory.PrismS.IoDescent

section General

variable {Z O A : Type} [CommRing Z] [CommRing O] [CommRing A] [Algebra Z O] [Algebra Z A]

theorem exists_retraction [IsLocalRing Z] [Module.Free Z O] (p : Z)
    (hp : IsLocalRing.maximalIdeal Z = Ideal.span {p}) (hu : ¬ IsUnit (algebraMap Z O p)) :
    ∃ r : O →ₗ[Z] Z, r 1 = 1 := by
  let b := Module.Free.chooseBasis Z O
  by_cases h : ∃ i, IsUnit (b.repr 1 i)
  · obtain ⟨i, hi⟩ := h
    obtain ⟨v, hv⟩ := hi.exists_left_inv
    exact ⟨v • b.coord i, by simpa using hv⟩
  · exfalso
    apply hu
    have h1 : ∀ i, p ∣ b.repr 1 i := fun i => by
      rw [← Ideal.mem_span_singleton, ← hp, IsLocalRing.mem_maximalIdeal]
      exact fun hi => h ⟨i, hi⟩
    refine isUnit_of_dvd_one ?_
    rw [← b.linearCombination_repr 1, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Finset.dvd_sum fun i _ => ?_
    rw [Algebra.smul_def]
    exact (map_dvd _ (h1 i)).mul_right _

theorem exists_factor {W : Type} [CommRing W] (r : O →ₗ[Z] Z) (hr : r 1 = 1)
    (f : PowerSeries W →+* O ⊗[Z] A) (π : A) (hX : f PowerSeries.X = (1 : O) ⊗ₜ[Z] π)
    (hC : ∀ w, ∃ a, f (PowerSeries.C w) = (1 : O) ⊗ₜ[Z] a)
    (hs : IsHausdorff (Ideal.span {(1 : O) ⊗ₜ[Z] π}) (O ⊗[Z] A)) :
    (∀ a b : A, (1 : O) ⊗ₜ[Z] a = (1 : O) ⊗ₜ[Z] b → a = b) ∧
      ∃ io : PowerSeries W →+* A, ∀ x, f x = (1 : O) ⊗ₜ[Z] io x := by
  let p : O ⊗[Z] A →ₗ[Z] A := (TensorProduct.lid Z A).toLinearMap ∘ₗ r.rTensor A
  have hp : ∀ o a, p (o ⊗ₜ a) = r o • a := fun o a => by simp [p]
  have hp1 : ∀ a, p (1 ⊗ₜ a) = a := fun a => by rw [hp, hr, one_smul]
  let j : A →+* O ⊗[Z] A := (Algebra.TensorProduct.includeRight (R := Z) (A := O) (B := A)).toRingHom
  have hj : ∀ a, j a = (1 : O) ⊗ₜ[Z] a := fun _ => rfl
  have hpm : ∀ a y, p (j a * y) = a * p y := fun a y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul o b => rw [hj, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hp, hp, mul_smul_comm]
    | add y z hy hz => rw [mul_add, map_add (f := _), map_add (f := _), hy, hz, mul_add]
  have hinj : Function.Injective j := fun a b h => by
    rw [← hp1 a, ← hp1 b, ← hj, ← hj, h]
  have hpoly : ∀ q : Polynomial W, f (q : PowerSeries W) ∈ j.range := fun q => by
    induction q using Polynomial.induction_on' with
    | add q q' h h' => rw [Polynomial.coe_add, map_add (f := _)]; exact add_mem h h'
    | monomial n w =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C,
        Polynomial.coe_X, map_mul, map_pow]
      obtain ⟨a, ha⟩ := hC w
      exact mul_mem (RingHom.mem_range.2 ⟨a, ha.symm⟩) (pow_mem (RingHom.mem_range.2 ⟨π, hX.symm⟩) _)
  have hall : ∀ x, f x ∈ j.range := fun x => by
    refine ⟨p (f x), ?_⟩
    rw [← sub_eq_zero]
    refine hs.haus _ fun m => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    obtain ⟨x', hx'⟩ : ∃ x', x = ((PowerSeries.trunc m x : Polynomial W) : PowerSeries W) + PowerSeries.X ^ m * x' :=
      ⟨_, PowerSeries.eq_X_pow_mul_shift_add_trunc m x |>.trans (add_comm _ _)⟩
    obtain ⟨a, ha⟩ := hpoly (PowerSeries.trunc m x)
    have e : f x = j a + j (π ^ m) * f x' := by
      conv_lhs => rw [hx']
      rw [map_add (f := _), map_mul, map_pow, hX, ha, map_pow, hj]
    refine ⟨j (p (f x')) - f x', ?_⟩
    rw [e, map_add (f := _), hpm, hj a, hp1, map_add (f := _), map_mul, ← hj a, ← hj π, map_pow]
    ring
  refine ⟨fun a b h => hinj h, ?_⟩
  let e : A ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (f.codRestrict j.range hall), fun x => ?_⟩
  have := congrArg Subtype.val (e.apply_symm_apply (f.codRestrict j.range hall x))
  exact this.symm

theorem tmul_algebraMap (c : Z) :
    algebraMap O (O ⊗[Z] A) (algebraMap Z O c) = (1 : O) ⊗ₜ[Z] algebraMap Z A c := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_tmul]

theorem exists_sum {W C : Type} [CommRing W] [CommRing C] (F : W →+* O ⊗[Z] A) (θ : A →+* C) (g : W →+* C)
    {n : ℕ} (z u : Fin n → W) (hz : ∀ i, ∃ a, F (z i) = (1 : O) ⊗ₜ[Z] a ∧ θ a = g (z i))
    (hu : ∀ i, ∃ a, F (u i) = (1 : O) ⊗ₜ[Z] a ∧ θ a = g (u i)) :
    ∃ a, F (∑ i, z i * u i) = (1 : O) ⊗ₜ[Z] a ∧ θ a = g (∑ i, z i * u i) := by
  choose a a1 a2 using hz
  choose b b1 b2 using hu
  refine ⟨∑ i, a i * b i, ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum, tmul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, a1, b1, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_mul, a2, b2]

end General

variable {l : ℕ} [Fact l.Prime]

theorem εroot_pow {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) : AI.εroot s ^ l ^ s = AI.ε := by
  induction s with
  | zero => simp [LocAinf.εroot]
  | succ s ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    exact ih

theorem εroot_sub_not_unit {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) : ¬ IsUnit (AI.εroot s - 1) := by
  intro h
  have h1 := (h.pow (l ^ s)).map (PreTilt.coeff (O := OC l) (p := l) 0)
  rw [sub_pow_char_pow, εroot_pow, one_pow, map_sub, AI.ε_coeff, AI.ζ_zero, map_one, map_one,
    sub_self] at h1
  exact not_isUnit_zero h1

theorem letEmb_C {K LL : FinExt l} {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (w : WK K) :
    letEmb emb (PowerSeries.C w) = fun k => PowerSeries.C (embW (emb k) w) := by
  funext k
  rw [letEmb_apply, PowerSeries.map_C]
  rfl

theorem letEmb_X {K LL : FinExt l} {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) :
    letEmb emb PowerSeries.X = letπ := by
  funext k
  rw [letEmb_apply, PowerSeries.map_X]
  rfl

theorem letEmb_scalar {K LL : FinExt l} {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (c : ℤ_[l]) :
    letEmb emb (PowerSeries.C (algebraMap ℤ_[l] (WK K) c)) =
      algebraMap ↥(OL LL) (LetA ↥(OL LL) n) (algebraMap ℤ_[l] ↥(OL LL) c) := by
  rw [letEmb_C]
  funext k
  rw [(embW (emb k)).commutes c]
  rfl

theorem map_scalar {K LL : FinExt l} {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1))
    (φ : LetA ↥(OL LL) n →ₐ[↥(OL LL)] RA LL) (c : ℤ_[l]) :
    φ (letEmb emb (PowerSeries.C (algebraMap ℤ_[l] (WK K) c))) =
      (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] algebraMap ℤ_[l] (Ainf l) c := by
  rw [letEmb_scalar, AlgHom.commutes, tmul_algebraMap]

theorem theta_scalar (K : FinExt l) (c : ℤ_[l]) :
    Formalism.Per.θ l (algebraMap ℤ_[l] (Ainf l) c) = intToOC K (algebraMap ℤ_[l] ↥(OL K) c) :=
  Subtype.ext ((GlobalTheory.UnramIdem.ringHom_eq ((Formalism.Per.θ l).comp (algebraMap ℤ_[l] (Ainf l))) c).trans
    (GlobalTheory.UnramIdem.ringHom_eq ((intToOC K).comp (algebraMap ℤ_[l] ↥(OL K))) c).symm)

theorem exists_span (K : FinExt l) (w : WK K) : ∃ (n : ℕ) (z : Fin n → ℤ_[l]) (u : Fin n → WK K),
    (∀ i, ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ ((u i : ↥(K0 K)) : Om l) ^ m = 1) ∧
      w = ∑ i, algebraMap ℤ_[l] (WK K) (z i) * u i := by
  obtain ⟨n, z, ω, hω, hsum⟩ := GlobalTheory.UnramSpan.exists_sum_rootsOfUnity l K ((w : ↥(K0 K)) : Om l)
    (w : ↥(K0 K)).2 (norm_le_one_of_mem_OL (unr K) w)
  choose h0 m hm hl h1 using hω
  refine ⟨n, z, fun i => ⟨⟨ω i, h0 i⟩, IsIntegral.of_pow (hm i) (by
    rw [show (⟨ω i, h0 i⟩ : ↥(K0 K)) ^ m i = 1 from Subtype.ext (h1 i)]; exact isIntegral_one)⟩,
    fun i => ⟨m i, hm i, hl i, h1 i⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  rw [hsum]
  push_cast
  rfl

theorem exists_const {K LL : FinExt l} {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1))
    (φ : LetA ↥(OL LL) n →ₐ[↥(OL LL)] RA LL)
    (hI : ∀ (c : ↥(K0 K)) (m : ℕ), 0 < m → ¬ l ∣ m → (c : Om l) ^ m = 1 → ∀ xb : OCb l,
      IsTiltOf (c : Om l) m xb → ∀ o : ZMod n → ↥(OL LL), (∀ i, ((o i : ↥(OL LL)) : ↥LL.1) = emb i c) →
      φ (fun i => PowerSeries.C (o i)) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l xb) (w : WK K) :
    ∃ a : Ainf l, φ (letEmb emb (PowerSeries.C w)) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] a ∧
      Formalism.Per.θ l a = intToOC (unr K) w := by
  obtain ⟨r, z, u, hu, rfl⟩ := exists_span K w
  refine exists_sum ((φ.toRingHom.comp (letEmb emb)).comp PowerSeries.C) (Formalism.Per.θ l)
    (intToOC (unr K)) (fun i => algebraMap ℤ_[l] (WK K) (z i)) u
    (fun i => ⟨_, map_scalar emb φ (z i), theta_scalar (unr K) (z i)⟩) (fun i => ?_)
  obtain ⟨m, hm, hl, h1⟩ := hu i
  obtain ⟨xb, hxb⟩ := GlobalTheory.MemLoc.exists_isTiltOf _ m hm hl h1
  refine ⟨WittVector.teichmuller l xb, ?_, ?_⟩
  · change φ (letEmb emb (PowerSeries.C (u i))) = _
    rw [letEmb_C]
    exact hI _ m hm hl h1 xb hxb _ (fun k => rfl)
  · apply Subtype.ext
    exact (congrArg Subtype.val (WittVector.fontaineTheta_teichmuller xb)).trans
      (GlobalTheory.MemLoc.IsTiltOf.untilt_eq hxb)

theorem exists_io {K LL : FinExt l} {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1))
    (φ : LetA ↥(OL LL) n →ₐ[↥(OL LL)] RA LL) (e : OCb l) (he : ¬ IsUnit (e - 1))
    (hπ : φ letπ = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l e - 1))
    (hC : ∀ w : WK K, ∃ a : Ainf l, φ (letEmb emb (PowerSeries.C w)) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] a ∧
      Formalism.Per.θ l a = intToOC (unr K) w) :
    ∃ io : PowerSeries (WK K) →+* Ainf l, (∀ x, φ (letEmb emb x) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] io x) ∧
      io PowerSeries.X = WittVector.teichmuller l e - 1 ∧
      ∀ w : WK K, Formalism.Per.θ l (io (PowerSeries.C w)) = intToOC (unr K) w := by
  obtain ⟨_, -, -, hu, hfree, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  obtain ⟨r, hr⟩ := exists_retraction (Z := ℤ_[l]) (O := ↥(OL LL)) (l : ℤ_[l])
    PadicInt.maximalIdeal_eq_span_p (by rwa [map_natCast])
  have hX : φ (letEmb emb PowerSeries.X) =
      (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l e - 1) := by
    rw [letEmb_X, hπ]
  obtain ⟨hinj, io, hio⟩ := exists_factor r hr (φ.toRingHom.comp (letEmb emb)) _ hX
    (fun w => (hC w).imp fun a h => h.1)
    ((GlobalTheory.HWL.TensorWitt.main l LL).2.2.2.2 e he).toIsHausdorff
  refine ⟨io, hio, hinj _ _ ((hio _).symm.trans hX), fun w => ?_⟩
  obtain ⟨a, h1, h2⟩ := hC w
  rw [hinj _ _ ((hio _).symm.trans h1), h2]

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∃ io : PowerSeries (WK K) →+* Ainf l, (∀ x, I.io (letEmb Γ.emb x) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] io x) ∧ io PowerSeries.X = WittVector.teichmuller l (AI.εroot s) - 1 ∧ ∀ w : WK K, Formalism.Per.θ l (io (PowerSeries.C w)) = intToOC (unr K) w :=
  fun _ _ _ AI _ s _ Γ _ I hI =>
    exists_io Γ.emb I.io _ (εroot_sub_not_unit AI s) I.io_π (exists_const Γ.emb I.io hI)

end GlobalTheory.PrismS.IoDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLatticeCocyclesModUniformizerPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CocycleModPow

theorem cocycles_finite (hT : Formalism.GaloisCohomology.LocalTateDualityK) (l : ℕ) [Fact l.Prime] (K : FinExt l)
    (r : ℕ) (M : Type) [AddCommGroup M] [Finite M] (a : ↥(GK K) → M →+ M) (h1 : ∀ m, a 1 m = m)
    (hmul : ∀ g h m, a (g * h) m = a g (a h m)) (hr : ∀ m : M, l ^ r • m = 0)
    (hlc : ∀ m, IsLocallyConstant fun g => a g m) :
    {c : ↥(GK K) → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.Finite := by
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let _ : TopologicalSpace M := ⊥
  have _ : DiscreteTopology M := ⟨rfl⟩
  have hr' : ∀ m : M, l ^ (r + 1) • m = 0 := fun m => by
    rw [pow_succ', mul_smul, hr, smul_zero]
  have _ : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ (r + 1))) M) := ⟨AddCommGroup.zmodModule hr'⟩
  let φ : ↥(GK K) ≃* Formalism.GaloisCohomology.GK l K.1 := IntermediateField.fixingSubgroupEquiv K.1
  have hφ : Continuous φ ∧ Continuous φ.symm :=
    GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  let rho : Representation (ZMod (l ^ (r + 1))) (Formalism.GaloisCohomology.GK l K.1) M :=
    GlobalTheory.CocycleCount.repOfAction _ (fun g => a (φ.symm g)) (fun m => by rw [map_one, h1])
      (fun g h m => by rw [map_mul, hmul])
  have ha : ∀ (g : Formalism.GaloisCohomology.GK l K.1) (m : M), (rho g : M →ₗ[ZMod (l ^ (r + 1))] M) m = a (φ.symm g) m := fun _ _ => rfl
  have hrho : ReciprocityTheory.Gal.ContAction rho := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    exact (hlc m).continuous.comp hφ.2
  have hH := (_root_.GlobalTheory.finite_H1_H2_of_localTateDuality hT l K.1 hK (r + 1) M rho (Nat.succ_pos r) hrho).1
  have hZ := GlobalTheory.CocycleCount.card_cocycles_mul_invariants_discrete _ _ M rho hrho
  have hH1 : 0 < Nat.card (ReciprocityTheory.Gal.H1 rho) := Nat.card_pos
  have hM : 0 < Nat.card M := Nat.card_pos
  have hfin : Finite (ReciprocityTheory.Gal.Z1 rho) := by
    refine Nat.finite_of_card_ne_zero fun h0 => ?_
    rw [h0, zero_mul] at hZ
    exact (Nat.mul_pos hH1 hM).ne hZ
  let E : ↥{c : ↥(GK K) → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)} →
      ↥(ReciprocityTheory.Gal.Z1 rho) :=
    fun c => ⟨fun g => c.1 (φ.symm g), c.2.1.continuous.comp hφ.2, fun g h => by
        beta_reduce
        rw [ha, map_mul, c.2.2]⟩
  refine Set.finite_coe_iff.1 (Finite.of_injective E fun c c' h => Subtype.ext (funext fun g => ?_))
  have := congrFun (congrArg Subtype.val h) (φ g)
  simpa only [E, φ.symm_apply_apply] using this

theorem dvd_and_finite (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (hO : GoodO (Qp := ℚ_[l]) LL O)
    (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ) :
    ϖ ^ n ∣ ((l : ℕ) : O) ^ n ∧ Finite (O ⧸ Ideal.span {ϖ ^ n}) := by
  obtain ⟨-, -, hfin, hcomp⟩ := GlobalTheory.T.coefficient_ring_integers_compact_adic_properties l LL O hO
  obtain ⟨⟨hdom, hdvr, -⟩, -⟩ := hO
  have hnu : ¬ IsUnit ((l : ℕ) : O) := fun hu => by
    have htop : Ideal.span {((l : ℕ) : O)} = ⊤ := Ideal.span_singleton_eq_top.2 hu
    have hH : IsHausdorff (Ideal.span {((l : ℕ) : O)}) O := hcomp.toIsHausdorff
    have h1 : (1 : O) = 0 := hH.haus 1 fun k => by
      rw [htop, SModEq.zero]
      simp [Ideal.top_pow]
    exact one_ne_zero h1
  have hdvd : ϖ ∣ ((l : ℕ) : O) := by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
    exact hnu
  have hd : ϖ ^ n ∣ ((l : ℕ) : O) ^ n := pow_dvd_pow_of_dvd hdvd n
  refine ⟨hd, ?_⟩
  have := hfin n
  exact Finite.of_surjective _
    (Ideal.Quotient.factor_surjective (Ideal.span_singleton_le_span_singleton.2 hd))

theorem finite_Z1Q : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (n : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)), (quotientCocycles LA _ hI : Set (↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T))).Finite := by
  intro hT l _ K LL _ _ _ O _ _ hO A LA ϖ hϖ n hI
  obtain ⟨hd, hfin⟩ := dvd_and_finite l LL O hO ϖ hϖ n
  have hring : IsTopologicalRing LL := hO.2.2.2.1
  have hopen : IsOpen (LA.T : Set A.V) :=
    GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hO.2.2.2.2 LA.T LA.fg LA.span
  obtain ⟨⟨hdom, hdvr, hfrac⟩, -⟩ := hO
  have hTfin : Module.Finite O ↥LA.T := Module.Finite.iff_fg.2 LA.fg
  have hQ : Finite (↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)) := by
    have : Module.Finite (O ⧸ Ideal.span {ϖ ^ n})
        (↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)) :=
      Module.Finite.of_restrictScalars_finite O _ _
    exact Module.finite_of_finite (O ⧸ Ideal.span {ϖ ^ n})
  have hmem : ∀ t : ↥LA.T, ϖ ^ n • t ∈ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T) := fun t =>
    Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  have hc : algebraMap O LL (ϖ ^ n) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact pow_ne_zero _ hϖ.ne_zero
  haveI := IsModuleTopology.topologicalAddGroup LL A.V
  refine cocycles_finite hT l K n _ (fun g => (actQ LA _ hI g).toAddMonoidHom) ?_ ?_ ?_ ?_
  · intro m
    induction m using Submodule.Quotient.induction_on with
    | H x =>
      change Submodule.Quotient.mk (actT LA 1 x) = _
      congr 1
      apply Subtype.ext
      change A.ρ 1 x = x
      simp
  · intro g h m
    induction m using Submodule.Quotient.induction_on with
    | H x =>
      change Submodule.Quotient.mk (actT LA (g * h) x) =
        Submodule.Quotient.mk (actT LA g (actT LA h x))
      congr 1
      apply Subtype.ext
      change A.ρ (g * h) x = A.ρ g (A.ρ h x)
      simp
  · intro m
    induction m using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨b, hb⟩ := hd
      rw [← Nat.cast_smul_eq_nsmul O, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        Nat.cast_pow, hb, mul_smul]
      exact hmem _
  · intro m
    induction m using Submodule.Quotient.induction_on with
    | H x =>
      rw [IsLocallyConstant.iff_eventually_eq]
      intro g₀
      have hcont : Continuous fun g : ↥(GK K) =>
          (algebraMap O LL (ϖ ^ n))⁻¹ • (A.ρ g x - A.ρ g₀ x) :=
        ((A.cont x).sub continuous_const).const_smul _
      have hev := (hopen.preimage hcont).mem_nhds (x := g₀) (by simp)
      filter_upwards [hev] with g hg
      change Submodule.Quotient.mk (actT LA g x) = Submodule.Quotient.mk (actT LA g₀ x)
      rw [Submodule.Quotient.eq]
      convert hmem ⟨_, hg⟩ using 1
      apply Subtype.ext
      change A.ρ g x - A.ρ g₀ x = ϖ ^ n • ((algebraMap O LL (ϖ ^ n))⁻¹ • (A.ρ g x - A.ρ g₀ x))
      rw [← algebraMap_smul LL (ϖ ^ n), smul_smul, mul_inv_cancel₀ hc, one_smul]

end GlobalTheory.CocycleModPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalTwoCocycleMultipleNotCoboundary
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

namespace GlobalTheory.TateNat

theorem free_inj : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] {G : Type} [Group G] [TopologicalSpace G] (χ : G →* ℤ_[p]ˣ) (c : G × G → ℤ_[p]), (∀ r, GlobalTheory.TateTop.Gen χ r c) → ∀ (φ : ℤ_[p] →+* O) (ε : G →* Oˣ), (∀ g, ((ε g : Oˣ) : O) = φ (χ g : ℤ_[p])) → ∀ (ϖ : O), Irreducible ϖ → (p : O) ∈ IsLocalRing.maximalIdeal O → (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) → ∀ (a : O) (f : G → O), Continuous f → (∀ g h : G, d1 (twist ε O) f (g, h) = a * φ (c (g, h))) → a = 0 := by
  intro p _ O _ _ _ _ _ _ G _ _ χ c hgen φ ε hεφ ϖ hϖ hp hopen a f hf hd
  have key : ∀ n : ℕ, a ∈ (powSub (M := O) ϖ n : Submodule O O) := by
    intro n
    set N : Submodule O O := powSub (M := O) ϖ n with hN
    letI : Module ℤ_[p] (O ⧸ N) := Module.compHom (O ⧸ N) φ
    have hs : ∀ (t : ℤ_[p]) (x : O), t • (Submodule.Quotient.mk x : O ⧸ N) =
        Submodule.Quotient.mk (φ t * x) := fun t x => by
      show (φ t) • (Submodule.Quotient.mk x : O ⧸ N) = _
      rw [← Submodule.Quotient.mk_smul, smul_eq_mul]
    haveI : Finite (O ⧸ N) := AddSubgroup.quotient_finite_of_isOpen N.toAddSubgroup (hopen n)
    have hM : ∀ m : O ⧸ N, (p : ℤ_[p]) ^ n • m = 0 := by
      intro m
      induction m using Submodule.Quotient.induction_on with
      | H x =>
        rw [hs, Submodule.Quotient.mk_eq_zero, map_pow, map_natCast]
        rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hp
        obtain ⟨u, hu⟩ := hp
        refine mem_powSub.2 ⟨u ^ n * x, ?_⟩
        rw [hu, smul_eq_mul, mul_pow]
        ring
    have hlc : IsLocallyConstant (fun g => (Submodule.Quotient.mk (f g) : O ⧸ N)) := by
      intro s
      have ho : IsOpen ((Submodule.Quotient.mk : O → O ⧸ N) ⁻¹' s) := by
        rw [isOpen_iff_forall_mem_open]
        intro x hx
        refine ⟨(fun y => y - x) ⁻¹' (N : Set O), fun y hy => ?_,
          (hopen n).preimage (continuous_id.sub continuous_const), ?_⟩
        · have e : (Submodule.Quotient.mk y : O ⧸ N) = Submodule.Quotient.mk x :=
            (Submodule.Quotient.eq N).2 hy
          show (Submodule.Quotient.mk y : O ⧸ N) ∈ s
          rw [e]
          exact hx
        · show x - x ∈ N
          rw [sub_self]
          exact N.zero_mem
      exact ho.preimage hf
    have h3 := ((hgen n) (O ⧸ N) hM).2.2 (Submodule.Quotient.mk a)
      (fun g => Submodule.Quotient.mk (f g)) hlc fun q => by
        obtain ⟨g, h⟩ := q
        have e := hd g h
        simp only [d1_apply] at e
        change (ε g : O) • f h - f (g * h) + f g = a * φ (c (g, h)) at e
        rw [smul_eq_mul, hεφ] at e
        simp only [GlobalTheory.TateTop.cob, hs]
        rw [← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add]
        congr 1
        linear_combination -e
    exact (Submodule.Quotient.mk_eq_zero N).1 h3
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal O)
    (IsLocalRing.maximalIdeal.isMaximal O).ne_top
  have hmem : a ∈ ⨅ i, (IsLocalRing.maximalIdeal O) ^ i := by
    refine Submodule.mem_iInf _ |>.2 fun i => ?_
    obtain ⟨y, hy⟩ := mem_powSub.1 (key i)
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← hy, smul_eq_mul]
    exact dvd_mul_right _ _
  rw [hbot] at hmem
  exact (Submodule.mem_bot O).1 hmem

end GlobalTheory.TateNat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisGroupFixedFieldBaseChangeLocalField
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem baseChange_fixedField :
    ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (A : Subgroup (L ≃ₐ[K] L)), ∃ j : (L ≃ₐ[↥(IntermediateField.fixedField A)] L) →* (L ≃ₐ[K] L), Function.Injective j ∧ j.range = A ∧ (∀ σ x, j σ x = σ x) ∧ ∀ i : ℤ, lowerRamificationGroup ↥(IntermediateField.fixedField A) L i = (lowerRamificationGroup K L i).comap j := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ A
  refine ⟨AlgEquiv.restrictScalarsHom K, AlgEquiv.restrictScalarsHom_injective K, ?_, ?_, ?_⟩
  · rw [GroundTheory.LocalField.range_restrictScalarsHom, IntermediateField.fixingSubgroup_fixedField]
  · intro σ x
    rfl
  · intro i
    exact (lowerRamificationGroup_comap_restrictScalars (IntermediateField.fixedField A) i).symm

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodEigSumSupComplEigSumEqTop
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

namespace GlobalTheory.EtaJoin

theorem eigSum_good_sup_compl_eq_top : ∀ (D : D7) (i : D.nd.Loc), ZRat D (D.nd.mu i) (D.nd.j i) → SpecPr D i →
    D.nd.eigSum i ↑(D.nd.Zgood i) ⊔ D.nd.eigSum i (↑(D.nd.Zgood i))ᶜ = ⊤ := by
  intro D i hZ hS
  rw [eq_top_iff, ← D.nd.prMt_span i, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  have hy : y ∈ ratSub D (D.nd.mu i) (D.nd.j i) (Idx.Z0 D (D.nd.mu i) (D.nd.j i)) ⊔
      ratSub D (D.nd.mu i) (D.nd.j i) (Idx.Z0 D (D.nd.mu i) (D.nd.j i))ᗮ := by
    unfold ZRat at hZ
    rw [hZ]; exact Submodule.mem_top
  obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.1 hy
  rw [map_add (f := _)]
  exact Submodule.add_mem_sup (hS.1 u hu) (hS.2 u' hu')

end GlobalTheory.EtaJoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfFrobeniusEquationCyclotomicFixedStatement
section
set_option synthInstance.maxHeartbeats 400000
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_range_of_frobeniusEquation_cyclotomicFixed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))) (E : EtSit P AI K s LL h W) (ι : Type) [Fintype ι] (M : ι → ι → W.EE) (c : ι → W.EE) (w : ι → RW LL), (∀ g : ↥(GK K), W.resΓ g = 1 → ∀ i, AI.gRW LL (g : GQ l) (w i) = w i) → (∀ i, w i = ∑ j, E.tie.ioE (M i j) * φRW LL (w j) + E.tie.ioE (c i)) → ∀ i, ∃ e : W.EE, E.tie.ioE e = w i := by
  first | exact @GlobalTheory.FrobDescent.mem_range_of_fixed | exact GlobalTheory.FrobDescent.mem_range_of_fixed | (intros; apply GlobalTheory.FrobDescent.mem_range_of_fixed <;> assumption)
end

