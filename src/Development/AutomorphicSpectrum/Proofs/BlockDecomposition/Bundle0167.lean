module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0038
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0160
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UntiltAdicComplete
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0164
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0156
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0135
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0158
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0118
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0117
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0107
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.CechAugRowU
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0163
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0165
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueIdempotentLiftTilt
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem existsUnique_idempotent_sharp {l : ℕ} [Fact l.Prime] (A : PAlg l) (e : A.U)
    (he : IsIdempotentElem e) : ∃! e₀ : A.A, IsIdempotentElem e₀ ∧ A.sharp e₀ = e := by
  obtain ⟨hsurj, hker⟩ := sharp_map_surjective_ker A
  haveI hcA : IsAdicComplete (Ideal.span {A.pi ^ 1}) A.A := by
    rw [pow_one]; exact A.compl
  haveI hcA' : IsAdicComplete (Ideal.span {A.pi}) A.A := A.compl
  haveI hcU : IsAdicComplete (Ideal.span {(l : A.U)}) A.U := _root_.GlobalTheory.CompanionTheory.Untilt.isAdicComplete_U A
  have hmemker : ∀ x y : A.A, A.aToU1 x = A.aToU1 y →
      Ideal.Quotient.mk (Ideal.span {A.pi ^ 1}) x = Ideal.Quotient.mk _ y := by
    intro x y h
    apply Ideal.Quotient.eq.2
    rw [pow_one, ← hker, RingHom.mem_ker, map_sub, h, sub_self]
  have hsharp_idem : ∀ x : A.A, IsIdempotentElem x → IsIdempotentElem (A.sharp x) := fun x hx =>
    hx.map A.sharp
  have hU := GlobalTheory.CompanionTheory.IdemLift.existsUnique_idempotent_lift (l : A.U) 1 one_ne_zero
    (Ideal.Quotient.mk _ e) (he.map (Ideal.Quotient.mk _))
  obtain ⟨a, ha⟩ := hsurj (Ideal.Quotient.mk _ e)
  have haid : IsIdempotentElem (Ideal.Quotient.mk (Ideal.span {A.pi ^ 1}) a) := by
    have : A.aToU1 (a * a) = A.aToU1 a := by
      rw [map_mul, ha]
      exact congrArg _ he |>.trans rfl
    have h2 := hmemker _ _ this
    rw [map_mul] at h2
    exact h2
  obtain ⟨e₀, ⟨he₀, hmk⟩, huniq⟩ := GlobalTheory.CompanionTheory.IdemLift.existsUnique_idempotent_lift A.pi 1 one_ne_zero
    (Ideal.Quotient.mk _ a) haid
  have hcong : ∀ x y : A.A, Ideal.Quotient.mk (Ideal.span {A.pi ^ 1}) x = Ideal.Quotient.mk _ y →
      A.aToU1 x = A.aToU1 y := by
    intro x y h
    have h3 := Ideal.Quotient.eq.1 h
    rw [pow_one, ← hker, RingHom.mem_ker, map_sub] at h3
    exact sub_eq_zero.1 h3
  refine ⟨e₀, ⟨he₀, ?_⟩, ?_⟩
  · refine hU.unique ⟨hsharp_idem _ he₀, ?_⟩ ⟨he, rfl⟩
    rw [← A.sharpMap_eq, hcong _ _ hmk, ha]
  · rintro e₁ ⟨he₁, hs₁⟩
    refine huniq e₁ ⟨he₁, ?_⟩
    rw [← hmk]
    apply hmemker
    have hs₀ : A.sharp e₀ = e := hU.unique ⟨hsharp_idem _ he₀, by
      rw [← A.sharpMap_eq, hcong _ _ hmk, ha]⟩ ⟨he, rfl⟩
    rw [A.sharpMap_eq, A.sharpMap_eq, hs₁, hs₀]

end GlobalTheory.CompanionTheory.Untilt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplitRangeIsoOfIntervalStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_split_range_iso_of_interval : ∀ {O A G : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing G] [Algebra O G] [Module.Flat O G]
    {I : Ideal A} (γ : DividedPowers I) (m : ℕ) (S : GrSplit O γ m) (u v : ℕ)
    {M : Fin m → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module O (M i)] {M' : Type} [AddCommGroup M']
    (θ : ∀ i : Fin m, u ≤ (i : ℕ) → (i : ℕ) < v → (G ≃ₗ[O] M i))
    (h0 : ∀ i : Fin m, ¬ (u ≤ (i : ℕ) ∧ (i : ℕ) < v) → Subsingleton (M i))
    (π : ((pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G)) : Ideal (A ⊗[O] G)) →+ M'),
    Function.Surjective π →
    (∀ x, π x = 0 ↔ x.1 ∈ (pdP γ v).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G))) →
    ∀ f : ∀ i, S.N i → M i → M', (∀ i n, f i n 0 = 0) →
    (∀ (i : Fin m) n x (hu : u ≤ (i : ℕ)) (hv : (i : ℕ) < v) hx, f i n (θ i hu hv x) = π ⟨S.ν i n ⊗ₜ x, hx⟩) →
    Tens O f := by
  first | exact @GlobalTheory.CompanionTheory.GrPiece.main | exact GlobalTheory.CompanionTheory.GrPiece.main | (intros; apply GlobalTheory.CompanionTheory.GrPiece.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitOfIsUnitSharpStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_of_isUnit_sharp' : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (a : A.A), IsUnit (A.sharp a) → IsUnit a := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.isUnit_of_isUnit_sharp | exact GlobalTheory.CompanionTheory.Untilt.isUnit_of_isUnit_sharp | (intros; apply GlobalTheory.CompanionTheory.Untilt.isUnit_of_isUnit_sharp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpMapCongruenceProperties
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem sharp_sub_mem_span_l_iff {l : ℕ} [Fact l.Prime] (A : PAlg l) (a b : A.A) :
    A.sharp a - A.sharp b ∈ Ideal.span {(l : A.U)} ↔ a - b ∈ Ideal.span {A.pi} := by
  have key : ∀ x y : A.U, (Ideal.Quotient.mk (Ideal.span {(l : A.U) ^ 1}) x =
      Ideal.Quotient.mk (Ideal.span {(l : A.U) ^ 1}) y) ↔ x - y ∈ Ideal.span {(l : A.U)} := by
    intro x y
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, pow_one]
  rw [← (GlobalTheory.CompanionTheory.Untilt.sharp_map_surjective_ker A).2, RingHom.mem_ker, map_sub, sub_eq_zero,
    CrystallineSemistableComparison.PAlg.sharpMap_eq, CrystallineSemistableComparison.PAlg.sharpMap_eq]
  exact (key _ _).symm

theorem idem_pow {R : Type*} [CommRing R] {x : R} (h : IsIdempotentElem x) {k : ℕ} (hk : k ≠ 0) :
    x ^ k = x := by
  cases k with
  | zero => exact absurd rfl hk
  | succ n =>
    induction n with
    | zero => simp
    | succ m ih => rw [pow_succ, ih (Nat.succ_ne_zero _), h.eq]

private theorem eq_zero_of_isIdempotentElem_of_mem_span_prime {l : ℕ} [Fact l.Prime] (A : PAlg l) {w : A.U}
    (hw : IsIdempotentElem w) (hl : w ∈ Ideal.span {(l : A.U)}) : w = 0 := by
  apply IsHausdorff.haus (GlobalTheory.CompanionTheory.Untilt.isAdicComplete_U A).toIsHausdorff w
  intro n
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
  cases n with
  | zero => simp
  | succ m =>
    have hp := Ideal.pow_mem_pow hl (m + 1)
    rwa [idem_pow hw (Nat.succ_ne_zero m)] at hp

theorem sharp_one_sub {l : ℕ} [Fact l.Prime] (A : PAlg l) (e : A.A) (he : IsIdempotentElem e) :
    A.sharp (1 - e) = 1 - A.sharp e := by
  have h0 : A.sharp 0 = 0 := by
    apply eq_zero_of_isIdempotentElem_of_mem_span_prime A
    · show A.sharp 0 * A.sharp 0 = A.sharp 0
      rw [← map_mul, mul_zero]
    · rw [Ideal.mem_span_singleton]
      refine ⟨A.sharp 0, ?_⟩
      rw [← CrystallineSemistableComparison.PAlg.sharp_pi A, ← map_mul A.sharp, mul_zero]
  have hu : IsIdempotentElem (A.sharp e) := by
    show A.sharp e * A.sharp e = A.sharp e
    rw [← map_mul, he.eq]
  have hv : IsIdempotentElem (A.sharp (1 - e)) := by
    have h1e : (1 - e) * (1 - e) = 1 - e := by linear_combination he.eq
    show A.sharp (1 - e) * A.sharp (1 - e) = A.sharp (1 - e)
    rw [← map_mul, h1e]
  have huv : A.sharp e * A.sharp (1 - e) = 0 := by
    rw [← map_mul, mul_sub, mul_one, he.eq, sub_self, h0]
  have hw : IsIdempotentElem (1 - A.sharp e - A.sharp (1 - e)) := by
    show (1 - A.sharp e - A.sharp (1 - e)) * (1 - A.sharp e - A.sharp (1 - e)) =
      1 - A.sharp e - A.sharp (1 - e)
    linear_combination hu.eq + hv.eq + 2 * huv
  have hl : 1 - A.sharp e - A.sharp (1 - e) ∈ Ideal.span {(l : A.U)} := by
    have h1 : A.aToU1 1 - A.aToU1 e - A.aToU1 (1 - e) = 0 := by
      rw [← map_sub, sub_self]
    rw [CrystallineSemistableComparison.PAlg.sharpMap_eq, CrystallineSemistableComparison.PAlg.sharpMap_eq, CrystallineSemistableComparison.PAlg.sharpMap_eq, map_one] at h1
    have h2 : Ideal.Quotient.mk (Ideal.span {(l : A.U) ^ 1}) (1 - A.sharp e - A.sharp (1 - e)) = 0 := by
      rw [map_sub, map_sub]
      exact h1
    rw [Ideal.Quotient.eq_zero_iff_mem, pow_one] at h2
    exact h2
  have hw0 := eq_zero_of_isIdempotentElem_of_mem_span_prime A hw hl
  linear_combination -hw0

theorem sharp_congruences : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l),
    (∀ (a b : A.A) (n : ℕ), a - b ∈ Ideal.span {A.pi} →
      A.sharp (a ^ l ^ n) - A.sharp (b ^ l ^ n) ∈ Ideal.span {(l : A.U) ^ (n + 1)}) ∧
    (∀ a b : A.A, A.sharp a - A.sharp b ∈ Ideal.span {(l : A.U)} ↔ a - b ∈ Ideal.span {A.pi}) ∧
    ∀ e : A.A, IsIdempotentElem e → A.sharp (1 - e) = 1 - A.sharp e := by
  intro l _ A
  refine ⟨?_, fun a b => sharp_sub_mem_span_l_iff A a b, fun e he => sharp_one_sub A e he⟩
  intro a b n hab
  have h1 : A.sharp a - A.sharp b ∈ Ideal.span {(l : A.U)} := (sharp_sub_mem_span_l_iff A a b).mpr hab
  rw [Ideal.mem_span_singleton] at h1 ⊢
  rw [map_pow, map_pow]
  exact dvd_sub_pow_of_dvd_sub h1 n

end GlobalTheory.CompanionTheory.Untilt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StableCoverCechVanishing
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GlobSt

section St
variable {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}
  (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens)

theorem st_single_rel (α : ι) ⦃T T' : Thick (nlFun γ p X q κ)⦄ (φ : T ⟶ T') (h : St Q {U α} T)
    (h' : ∃ β, St Q {U β} T') : St Q {U α} T' := by
  obtain ⟨-, V, hV, hi⟩ := h
  obtain ⟨β, hQ, -⟩ := h'
  rw [Set.mem_singleton_iff] at hV
  subst hV
  exact ⟨hQ, _, rfl, _root_.GlobalTheory.CompanionTheory.ThickPt.inU_map _ φ hi⟩

theorem st_single_union : (fun T => ∃ α, St Q {U α} T) = St Q (Set.range U) := by
  funext T
  refine propext ⟨?_, ?_⟩
  · rintro ⟨α, hQ, V, hV, hi⟩
    rw [Set.mem_singleton_iff] at hV
    subst hV
    exact ⟨hQ, _, ⟨α, rfl⟩, hi⟩
  · rintro ⟨hQ, V, ⟨α, rfl⟩, hi⟩
    exact ⟨α, hQ, _, rfl, hi⟩

theorem st_single_capS (S : Finset ι) (hS : S.Nonempty) :
    capS (fun α => St Q {U α}) S = St Q {⨅ α ∈ S, U α} := by
  funext T
  refine propext ⟨fun h => ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hS
    refine ⟨(h a ha).1, _, rfl, (_root_.GlobalTheory.CompanionTheory.Thick.inU_iInf_finset U S T).2 fun α hα => ?_⟩
    obtain ⟨-, V, hV, hi⟩ := h α hα
    rw [Set.mem_singleton_iff] at hV
    subst hV
    exact hi
  · rintro ⟨hQ, V, hV, hi⟩ α hα
    rw [Set.mem_singleton_iff] at hV
    subst hV
    exact ⟨hQ, _, rfl, (_root_.GlobalTheory.CompanionTheory.Thick.inU_iInf_finset U S T).1 hi α hα⟩

end St

theorem tens_congr {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C C' : Type 1} [Category.{0} C]
    [Category.{0} C'] (G : C' ⥤ C) {ι : Type} [DecidableEq ι] (N : ι → Type) [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] (F : ι → (C ⥤ ModuleCat.{0} R)) (F' : C' ⥤ ModuleCat.{0} R')
    (τ : ∀ i, N i → ∀ T : C', (F i).obj (G.obj T) →ₛₗ[σ] F'.obj T) (hτ : ∀ i n {T T' : C'} (φ : T ⟶ T') x,
      τ i n T' (((F i).map (G.map φ)).hom x) = (F'.map φ).hom (τ i n T x))
    {U₁ U₂ : ObjectProperty C} {V₁ V₂ : ObjectProperty C'} (e : U₁ = U₂) (e' : V₁ = V₂)
    (h₁ : ∀ T, V₁ T → U₁ (G.obj T)) (h₂ : ∀ T, V₂ T → U₂ (G.obj T)) (j : ℕ)
    (H : Tens R (N := N) (M := fun i => HU (F i) U₁ j) (M' := HU F' V₁ j)
      fun i n x => (morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) h₁).pull j x) :
    Tens R (N := N) (M := fun i => HU (F i) U₂ j) (M' := HU F' V₂ j)
      fun i n x => (morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) h₂).pull j x := by
  subst e e'
  exact H

theorem glob_st : (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {Λ : Type} [CommRing Λ]
    (F : Thick (nlFun γ p X q κ) ⥤ ModuleCat.{0} Λ) (Q : ObjectProperty (Thick (nlFun γ p X q κ)))
    {ι : Type} [Fintype ι] (U : ι → X.Opens) (s : ℕ),
    ((∀ S : Finset ι, S.Nonempty → ∀ j < s, Subsingleton (HU F (St Q {⨅ α ∈ S, U α}) j)) →
      ∀ j < s, Subsingleton (HU F (St Q (Set.range U)) j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j, Subsingleton (HU F (St Q {⨅ α ∈ S, U α}) j)) →
      ∀ j, Subsingleton (HU F (St Q (Set.range U)) j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j > s, Subsingleton (HU F (St Q {⨅ α ∈ S, U α}) j)) →
      ∀ j, s + Fintype.card ι ≤ j → Subsingleton (HU F (St Q (Set.range U)) j))) ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {Λ : Type} [CommRing Λ]
    (F : Thick (nlFun γ p X q κ) ⥤ ModuleCat.{0} Λ) (Q : ObjectProperty (Thick (nlFun γ p X q κ)))
    {ι : Type} (U : ι → X.Opens) (𝒮 : Serre.{1} Λ) (n : ℕ),
    (∀ a b, a + b = n → 𝒮.P ((CrystallineSemistableComparison.Pb.cechH F (fun α => St Q {U α}) b).cx.H a)) → 𝒮.P (HU F (St Q (Set.range U)) n)) ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}
    {O' : Type} [CommRing O'] {R' : Type} [CommRing R'] {I' : Ideal R'} {γ' : DividedPowers I'} {p' : ℕ}
    {X' : Scheme.{0}} {q' : X' ⟶ Spec (CommRingCat.of O')} {κ' : O' →+* R' ⧸ I'}
    {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {σ : Λ →+* Λ'}
    (G : Thick (nlFun γ' p' X' q' κ') ⥤ Thick (nlFun γ p X q κ)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ι → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module Λ (N i)] [∀ i, Module.Flat Λ (N i)]
    (F : ι → (Thick (nlFun γ p X q κ) ⥤ ModuleCat.{0} Λ)) (F' : Thick (nlFun γ' p' X' q' κ') ⥤ ModuleCat.{0} Λ')
    (τ : ∀ i, N i → ∀ T, (F i).obj (G.obj T) →ₛₗ[σ] F'.obj T) (hτ : ∀ i n {T T'} (φ : T ⟶ T') x,
      τ i n T' (((F i).map (G.map φ)).hom x) = (F'.map φ).hom (τ i n T x))
    (hadd : ∀ i n n' T x, τ i (n + n') T x = τ i n T x + τ i n' T x) (hsm : ∀ i (r : Λ) n T x, τ i (r • n) T x = σ r • τ i n T x)
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (Q' : ObjectProperty (Thick (nlFun γ' p' X' q' κ')))
    {A : Type} [Fintype A] (U : A → X.Opens) (U' : A → X'.Opens) (h : ∀ α T, St Q' {U' α} T → St Q {U α} (G.obj T))
    (hS : ∀ (S : Finset A) T, St Q' {⨅ α ∈ S, U' α} T → St Q {⨅ α ∈ S, U α} (G.obj T))
    (hR : ∀ T, St Q' (Set.range U') T → St Q (Set.range U) (G.obj T)),
    (∀ S : Finset A, S.Nonempty → ∀ j, Tens Λ (N := N) (M := fun i => HU (F i) (St Q {⨅ α ∈ S, U α}) j)
      (M' := HU F' (St Q' {⨅ α ∈ S, U' α}) j)
      fun i n x => (morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) (hS S)).pull j x) →
    ∀ j, Tens Λ (N := N) (M := fun i => HU (F i) (St Q (Set.range U)) j) (M' := HU F' (St Q' (Set.range U')) j)
      fun i n x => (morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) hR).pull j x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro O _ R _ I γ p X q κ Λ _ F Q ι _ U s
    have key := GlobalTheory.CompanionTheory.GlobRel.glob_van_rel F (fun α => St Q {U α}) (st_single_rel Q U) s
    rw [st_single_union Q U] at key
    obtain ⟨k1, k2, k3⟩ := key
    refine ⟨fun H => k1 fun S hS => ?_, fun H => k2 fun S hS => ?_, fun H => k3 fun S hS => ?_⟩ <;>
      · rw [st_single_capS Q U S hS]
        exact H S hS
  · intro O _ R _ I γ p X q κ Λ _ F Q ι U 𝒮 n H
    have key := GlobalTheory.CompanionTheory.CosieveRel.serre_union F (fun α => St Q {U α}) (st_single_rel Q U) 𝒮 n H
    rw [st_single_union Q U] at key
    exact key
  · intro O _ R _ I γ p X q κ O' _ R' _ I' γ' p' X' q' κ' Λ Λ' _ _ σ G ι _ _ N _ _ _ F F' τ hτ hadd hsm Q Q' A _ U U' h hS hR H j
    refine tens_congr G N F F' τ hτ (st_single_union Q U) (st_single_union Q' U') (fun T ⟨α, hα⟩ => ⟨α, h α T hα⟩) hR j
      (GlobalTheory.CompanionTheory.CosieveRel.base_change_rel G N F F' τ hτ hadd hsm (fun α => St Q {U α}) (fun α => St Q' {U' α})
        (st_single_rel Q U) (st_single_rel Q' U') h (fun S hne j => ?_) j)
    exact tens_congr G N F F' τ hτ (st_single_capS Q U S hne).symm (st_single_capS Q' U' S hne).symm (hS S) _ j (H S hne j)

end GlobalTheory.CompanionTheory.GlobSt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupremumTwistingOpensEqTop
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeCover

attribute [local instance] MvPolynomial.gradedAlgebra

theorem main : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} (D : E.LineData X) (N : ℕ)
    (i : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace R N), IsTautologicalLineAt D N i → sSup (𝒱D D) = ⊤ := by
  intro R _ X D N i h
  obtain ⟨-, s, hs, -⟩ := h
  rw [eq_top_iff]
  intro x _
  obtain ⟨j, hj⟩ := GlobalTheory.ProjSpace.exists_mem_chart R N (i x)
  haveI : IsOpenImmersion (chart R N j) := by
    unfold chart
    infer_instance
  have hmem : (pullback.fst i (chart R N j)).opensRange ∈ 𝒱D D :=
    ⟨(pullback.fst i (chart R N j)).isoOpensRange.inv ≫ s j, by
      rw [Category.assoc, hs, Scheme.Hom.isoOpensRange_inv_comp]⟩
  refine TopologicalSpace.Opens.mem_sSup.2 ⟨_, hmem, ?_⟩
  have e : (chart R N j).opensRange = GlobalTheory.ProjSpace.chart R N j := Proj.opensRange_awayι _ _ _ _
  have hr : i x ∈ ((chart R N j).opensRange : Set _) := by
    rw [e]
    exact hj
  rw [Scheme.Hom.coe_opensRange] at hr
  show x ∈ ((pullback.fst i (chart R N j)).opensRange : Set X)
  rw [Scheme.Hom.coe_opensRange, Scheme.Pullback.range_fst]
  exact hr

end GlobalTheory.CompanionTheory.ConeCover
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TiltSequenceDeterminedBySharpStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_sequence_determined_by_sharp : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (a b : ℕ → A.A), (∀ i, a (i + 1) ^ l = a i) → (∀ i, b (i + 1) ^ l = b i) → (∀ i, A.sharp (a i) = A.sharp (b i)) → a = b := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.tilt_inj | exact GlobalTheory.CompanionTheory.Untilt.tilt_inj | (intros; apply GlobalTheory.CompanionTheory.Untilt.tilt_inj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistingSheafBaseChange
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeTwistingSheaf

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_chartHom {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (N : ℕ) (j : Fin (N + 1)) :
    ∃ c : ChartR R N j →+* ChartR R' N j,
      chart R' N j ≫ GlobalTheory.ProjSpace.baseChange N φ = spMap c ≫ chart R N j ∧
      ∀ k, c (ratio R N j k) = ratio R' N j k := by
  have key : ∀ (s : MvPolynomial (Fin (N + 1)) R') (_ : s = MvPolynomial.X j)
      (hd : s ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R' 1),
      ∃ ψ : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R') s →+* ChartR R' N j,
        chart R' N j = spMap ψ ≫ Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R') s hd one_pos ∧
        ∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R') (hf),
          ψ (HomogeneousLocalization.Away.mk _ hd n f hf) =
            HomogeneousLocalization.Away.mk _ (X_mem R' N j) n f hf := by
    rintro _ rfl hd
    refine ⟨RingHom.id _, ?_, fun _ _ _ => rfl⟩
    have e : spMap (RingHom.id (ChartR R' N j)) = 𝟙 _ := Spec.map_id _
    rw [e, Category.id_comp]
    rfl
  obtain ⟨ψ, h1, h2⟩ := key (GlobalTheory.ProjSpace.gradedMap N φ (MvPolynomial.X j)) (MvPolynomial.map_X φ j)
    ((GlobalTheory.ProjSpace.gradedMap N φ).2 (X_mem R N j))
  refine ⟨ψ.comp (HomogeneousLocalization.Away.map (GlobalTheory.ProjSpace.gradedMap N φ) (MvPolynomial.X j)), ?_, fun k => ?_⟩
  · rw [h1, Category.assoc, GlobalTheory.ProjSpace.baseChange, Proj.awayι_comp_map _ _ one_pos _ (X_mem R N j),
      ← Spec.map_comp_assoc]
    rfl
  · change ψ (HomogeneousLocalization.Away.map (GlobalTheory.ProjSpace.gradedMap N φ) (MvPolynomial.X j) _) = _
    rw [ratio, HomogeneousLocalization.Away.map_mk, h2]
    simp [ratio, GlobalTheory.ProjSpace.gradedMap]

theorem isTwistingSheaf_pullback {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X : Scheme.{0}} (p : X ⟶ Sp R)
    (D : E.LineData X) (hO : IsTautologicalLine p D) :
    IsTautologicalLine (pullback.snd p (spMap φ)) (D.pb (pullback.fst p (spMap φ))) := by
  obtain ⟨N, i, hi, hp, het, s, hs, hu⟩ := hO
  have H := GlobalTheory.ProjSpace.isPullback_baseChange N φ
  have hw : (pullback.fst p (spMap φ) ≫ i) ≫ PSpace.str R N = pullback.snd p (spMap φ) ≫ spMap φ := by
    rw [Category.assoc, hp]
    exact pullback.condition
  obtain ⟨i', hi1, hi2⟩ : ∃ i' : pullback p (spMap φ) ⟶ PSpace R' N,
      i' ≫ GlobalTheory.ProjSpace.baseChange N φ = pullback.fst p (spMap φ) ≫ i ∧
      i' ≫ PSpace.str R' N = pullback.snd p (spMap φ) :=
    ⟨H.lift _ _ hw, H.lift_fst _ _ hw, H.lift_snd _ _ hw⟩
  have Hl : IsPullback i' (pullback.fst p (spMap φ)) (GlobalTheory.ProjSpace.baseChange N φ) i := by
    refine IsPullback.of_right (h₁₂ := PSpace.str R' N) (v₁₃ := spMap φ) (h₂₂ := PSpace.str R N) ?_ hi1 H.flip
    rw [hi2, hp]
    exact (IsPullback.of_hasPullback p (spMap φ)).flip
  have hc : IsClosedImmersion i' :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) Hl.flip hi
  choose c hc1 hc2 using fun j => exists_chartHom φ N j
  have hm : ∀ j, (pullback.fst i' (chart R' N j) ≫ pullback.fst p (spMap φ)) ≫ i =
      (pullback.snd i' (chart R' N j) ≫ spMap (c j)) ≫ chart R N j := fun j => by
    rw [Category.assoc, Category.assoc, ← hc1, ← hi1, ← Category.assoc, pullback.condition, Category.assoc]
  let m : ∀ j, pullback i' (chart R' N j) ⟶ pullback i (chart R N j) := fun j => pullback.lift _ _ (hm j)
  have hm1 : ∀ j, m j ≫ pullback.fst i (chart R N j) =
      pullback.fst i' (chart R' N j) ≫ pullback.fst p (spMap φ) := fun j => pullback.lift_fst _ _ _
  have hm2 : ∀ j, m j ≫ pullback.snd i (chart R N j) =
      pullback.snd i' (chart R' N j) ≫ spMap (c j) := fun j => pullback.lift_snd _ _ _
  have hl : ∀ j, (m j ≫ s j) ≫ D.f = pullback.fst i' (chart R' N j) ≫ pullback.fst p (spMap φ) := fun j => by
    rw [Category.assoc, hs, hm1]
  refine ⟨N, i', hc, hi2, ?_, fun j => pullback.lift (m j ≫ s j) (pullback.fst i' (chart R' N j)) (hl j),
    fun j => pullback.lift_snd _ _ _, ?_⟩
  · change Etale (pullback.snd D.f (pullback.fst p (spMap φ)))
    infer_instance
  · intro V j k a b h
    have h₀ : (a ≫ m j) ≫ pullback.fst i (chart R N j) = (b ≫ m k) ≫ pullback.fst i (chart R N k) := by
      rw [Category.assoc, Category.assoc, hm1, hm1, ← Category.assoc, ← Category.assoc, h]
    have e := hu V j k (a ≫ m j) (b ≫ m k) h₀
    have ueq : ∀ {a₁ a₂ b₁ b₂ : V ⟶ D.Y} (_ : a₁ = a₂) (_ : b₁ = b₂) (h₁ : a₁ ≫ D.f = b₁ ≫ D.f)
        (h₂ : a₂ ≫ D.f = b₂ ≫ D.f), D.u a₁ b₁ h₁ = D.u a₂ b₂ h₂ := by
      intro a₁ a₂ b₁ b₂ ha hb h₁ h₂
      subst ha hb
      rfl
    have nat : ∀ x, (spMap (c j)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (ChartR R N j))).inv.hom x) =
        (Scheme.ΓSpecIso (CommRingCat.of (ChartR R' N j))).inv.hom (c j x) := fun x =>
      (congrArg (fun f => f.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (c j)))).symm
    have hs₂ : (a ≫ m j) ≫ pullback.snd i (chart R N j) =
        (a ≫ pullback.snd i' (chart R' N j)) ≫ spMap (c j) := by
      rw [Category.assoc, hm2, Category.assoc]
    refine (congrArg Units.val (ueq (by simp) (by simp) _ _)).trans (e.trans ?_)
    rw [hs₂, Scheme.Hom.comp_appTop]
    change (a ≫ pullback.snd i' (chart R' N j)).appTop.hom ((spMap (c j)).appTop.hom _) = _
    rw [nat, hc2]

end GlobalTheory.CompanionTheory.ConeTwistingSheaf
end

