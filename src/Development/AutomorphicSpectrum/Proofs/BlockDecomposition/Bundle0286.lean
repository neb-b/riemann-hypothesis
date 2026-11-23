module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0278
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyRestrictionBetweenStableFamilies
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.ZariskiCocycleRefinement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0233
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftClosedEmbedding
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftSectionsNonvanishing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealFiltrationSaturated
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0266
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0267
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0281
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0248

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingOperatorsKernelLift
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem exists_grSum_semilift {ι : Type} {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R')
    {A : ℤ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x)
    {N : Type} [AddCommGroup N] [Module (MvPolynomial ι R') N] (φ : ∀ n, A n →+ N)
    (hr : ∀ n (r : R) (a : A n),
      φ n (r • a) = (MvPolynomial.C (f r) : MvPolynomial ι R') • φ n a)
    (hX : ∀ i n (a : A n),
      φ (n + 1) (x i n a) = (MvPolynomial.X i : MvPolynomial ι R') • φ n a) :
    ∃ Φ : GrSum hx →+ N, (∀ n a, Φ (GrSum.of hx n a) = φ n a) ∧
      ∀ (q : MvPolynomial ι R) (u : GrSum hx), Φ (q • u) = (MvPolynomial.map f q) • Φ u := by
  letI : Module R N := Module.compHom N ((MvPolynomial.C : R' →+* MvPolynomial ι R').comp f)
  letI : Module (MvPolynomial ι R) N :=
    Module.compHom N (MvPolynomial.map f : MvPolynomial ι R →+* MvPolynomial ι R')
  haveI : IsScalarTower R (MvPolynomial ι R) N := ⟨fun r q m => by
    change (MvPolynomial.map f (r • q)) • m =
      (MvPolynomial.C (f r) : MvPolynomial ι R') • (MvPolynomial.map f q) • m
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, mul_smul]⟩
  let ψ : ∀ n, A n →ₗ[R] N := fun n =>
    { toFun := φ n, map_add' := map_add _, map_smul' := fun r a => hr n r a }
  have hψ : ∀ i n a, ψ (n + 1) (x i n a) = (MvPolynomial.X i : MvPolynomial ι R) • ψ n a := by
    intro i n a
    change φ (n + 1) (x i n a) = (MvPolynomial.map f (MvPolynomial.X i)) • φ n a
    rw [MvPolynomial.map_X]
    exact hX i n a
  refine ⟨(GrSum.lift hx ψ hψ).toAddMonoidHom, fun n a => GrSum.lift_of hx ψ hψ n a,
    fun q u => ?_⟩
  exact (GrSum.lift hx ψ hψ).map_smul q u

section Tower

variable {ι : Type} [LinearOrder ι] {R : Type} [CommRing R] {g : ℕ} {ρ : Fin g → R}
  {T : ℕ → ℤ → Finset ι → Type} [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)]
  {res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S'}
  {p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S}
  {mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S}

theorem smul_mem_Ks (H : TowerAx ρ res p mm) {e : ℕ} {t : ℤ} {S : Finset ι} (hS : S.Nonempty)
    {r : R} (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) (y : T (e + 1) t S) :
    r • y ∈ Ks p e t S := by
  rw [mem_Ks hS, map_smul]
  exact H.smul_eq_zero_of_mem hS (m := e + 1) (n := 0) (by omega) hr (by simp)

variable (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S)
  fun j t => mm j e t S)

theorem exists_mulMap (H : TowerAx ρ res p mm) {e : ℕ} {r : R}
    (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) {S : Finset ι} (hS : S.Nonempty) :
    ∃ Φ : GrSum (hc (e + 1) S) →+ H.Tot hc S,
      (∀ t y, Φ (GrSum.of (hc (e + 1) S) t y) =
        (H.ops hc S).of e t ⟨r • y, smul_mem_Ks H hS hr y⟩) ∧
      ∀ (q : MvPolynomial ι R) (u : GrSum (hc (e + 1) S)),
        Φ (q • u) = (MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial (Fin g) R) q) • Φ u := by
  let μ : ∀ t, T (e + 1) t S →+ Ks p e t S := fun t =>
    { toFun := fun y => ⟨r • y, smul_mem_Ks H hS hr y⟩
      map_zero' := Subtype.ext (smul_zero r)
      map_add' := fun a b => Subtype.ext (smul_add r a b) }
  obtain ⟨Φ, h1, h2⟩ := exists_grSum_semilift (MvPolynomial.C : R →+* MvPolynomial (Fin g) R)
    (hc (e + 1) S) (N := H.Tot hc S) (fun t => ((H.ops hc S).of e t).comp (μ t))
    (fun t c a => by
      simp only [AddMonoidHom.comp_apply]
      rw [BiOps.C_C_smul_of]
      congr 1
      exact Subtype.ext (smul_comm r c a))
    (fun j t a => by
      simp only [AddMonoidHom.comp_apply]
      rw [BiOps.X_smul_of]
      congr 1
      apply Subtype.ext
      change r • mm j (e + 1) t S a = mm j (e + 1) t S (r • a)
      rw [map_smul])
  exact ⟨Φ, h1, h2⟩

def unitIdeal (H : TowerAx ρ res p mm) (one : ∀ e (i : ι), T e 0 {i}) (i : ι)
    (Q : Submodule (MvPolynomial ι (MvPolynomial (Fin g) R)) (H.Tot hc {i})) (e : ℕ) : Ideal R where
  carrier := {r | ∃ h : r • one (e + 1) i ∈ Ks p e 0 {i},
    (H.ops hc {i}).of e 0 ⟨r • one (e + 1) i, h⟩ ∈ Q}
  add_mem' := by
    rintro a b ⟨ha, ma⟩ ⟨hb, mb⟩
    have h : (a + b) • one (e + 1) i ∈ Ks p e 0 {i} := by
      rw [add_smul]
      exact add_mem ha hb
    refine ⟨h, ?_⟩
    have e1 : (⟨(a + b) • one (e + 1) i, h⟩ : Ks p e 0 {i}) =
        ⟨a • one (e + 1) i, ha⟩ + ⟨b • one (e + 1) i, hb⟩ := Subtype.ext (add_smul a b _)
    rw [e1, map_add (f := _)]
    exact add_mem ma mb
  zero_mem' := by
    have h : (0 : R) • one (e + 1) i ∈ Ks p e 0 {i} := by
      rw [zero_smul]
      exact zero_mem _
    refine ⟨h, ?_⟩
    have e1 : (⟨(0 : R) • one (e + 1) i, h⟩ : Ks p e 0 {i}) = 0 := Subtype.ext (zero_smul R _)
    rw [e1, map_zero]
    exact zero_mem _
  smul_mem' := by
    rintro c a ⟨ha, ma⟩
    have h : (c • a) • one (e + 1) i ∈ Ks p e 0 {i} := by
      rw [smul_assoc]
      exact Submodule.smul_mem _ c ha
    refine ⟨h, ?_⟩
    have e1 : (⟨(c • a) • one (e + 1) i, h⟩ : Ks p e 0 {i}) =
        c • ⟨a • one (e + 1) i, ha⟩ := Subtype.ext (smul_assoc c a _)
    rw [e1, ← BiOps.C_C_smul_of]
    exact Q.smul_mem _ ma

theorem pow_le_unitIdeal (H : TowerAx ρ res p mm) (one : ∀ e (i : ι), T e 0 {i})
    (hone : ∀ e i, p e 0 {i} (one (e + 1) i) = one e i) (i : ι)
    (Q : Submodule (MvPolynomial ι (MvPolynomial (Fin g) R)) (H.Tot hc {i}))
    (hQ : ∀ l, (H.ops hc {i}).of 0 0 ⟨ρ l • one (0 + 1) i,
      smul_mem_Ks H (Finset.singleton_nonempty i) (by simpa using rho_mem l) _⟩ ∈ Q) (e : ℕ) :
    Ideal.span (Set.range ρ) ^ (e + 1) ≤ unitIdeal hc H one i Q e := by
  have hS : ({i} : Finset ι).Nonempty := Finset.singleton_nonempty i
  induction e with
  | zero =>
    rw [zero_add, pow_one, Ideal.span_le]
    rintro _ ⟨l, rfl⟩
    exact ⟨_, hQ l⟩
  | succ e ih =>
    rw [pow_succ, Ideal.mul_le]
    intro u hu v hv
    obtain ⟨h, hm⟩ := ih hu
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨l, rfl⟩ := hv
      have hmem : u * ρ l ∈ Ideal.span (Set.range ρ) ^ (e + 1 + 1) := by
        rw [pow_succ]
        exact Ideal.mul_mem_mul hu (rho_mem l)
      have h' := smul_mem_Ks H hS hmem (one (e + 1 + 1) i)
      refine ⟨h', ?_⟩
      have hb : p (e + 1) 0 {i} (u • one (e + 1 + 1) i) =
          ((⟨u • one (e + 1) i, h⟩ : Ks p e 0 {i}) : T (e + 1) 0 {i}) := by
        rw [map_smul, hone]
      have e1 : (⟨(u * ρ l) • one (e + 1 + 1) i, h'⟩ : Ks p (e + 1) 0 {i}) =
          (H.ops hc {i}).y l e 0 ⟨u • one (e + 1) i, h⟩ := by
        apply Subtype.ext
        change (u * ρ l) • one (e + 1 + 1) i = (H.yK l e 0 {i} ⟨u • one (e + 1) i, h⟩ : _)
        rw [H.coe_yK l hS _ _ hb, smul_smul, mul_comm]
      rw [e1, ← BiOps.C_X_smul_of]
      exact Q.smul_mem _ hm
    | zero => simpa using zero_mem (unitIdeal hc H one i Q (e + 1))
    | add a b _ _ ha hb =>
      rw [mul_add]
      exact add_mem ha hb
    | smul c a _ ha =>
      rw [smul_eq_mul, mul_left_comm]
      exact Ideal.mul_mem_left _ c ha

theorem pow_smul_add_mem {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (Q : Submodule A M)
    (x : A) {a b : M} (ha : ∃ k : ℕ, x ^ k • a ∈ Q) (hb : ∃ k : ℕ, x ^ k • b ∈ Q) :
    ∃ k : ℕ, x ^ k • (a + b) ∈ Q := by
  obtain ⟨k, hk⟩ := ha
  obtain ⟨k', hk'⟩ := hb
  refine ⟨k + k', ?_⟩
  rw [smul_add]
  refine add_mem ?_ ?_
  · rw [add_comm, pow_add, mul_smul]
    exact Q.smul_mem _ hk
  · rw [pow_add, mul_smul]
    exact Q.smul_mem _ hk'

theorem exists_pow_smul_mem (H : TowerAx ρ res p mm) (one : ∀ e (i : ι), T e 0 {i}) (i : ι)
    (hform : ∀ e t (a : T e t {i}), ∃ (k : ℕ) (q : MvPolynomial ι R) (t' : ℤ) (w : T e t' {i}),
      w ∈ Ideal.span (Set.range ρ) • (⊤ : Submodule R (T e t' {i})) ∧
      (MvPolynomial.X i : MvPolynomial ι R) ^ k • GrSum.of (hc e {i}) t a =
        q • GrSum.of (hc e {i}) 0 (one e i) + GrSum.of (hc e {i}) t' w)
    (Q : Submodule (MvPolynomial ι (MvPolynomial (Fin g) R)) (H.Tot hc {i}))
    (hQ : ∀ e r (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)),
      (H.ops hc {i}).of e 0 ⟨r • one (e + 1) i,
        smul_mem_Ks H (Finset.singleton_nonempty i) hr _⟩ ∈ Q)
    (m : H.Tot hc {i}) :
    ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k • m ∈ Q := by
  have hS : ({i} : Finset ι).Nonempty := Finset.singleton_nonempty i
  have hker : ∀ (e : ℕ) (t : ℤ) (x : T (e + 1) t {i}), x ∈ Ks p e t {i} ↔
      x ∈ Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (T (e + 1) t {i})) := by
    intro e t x
    rw [← H.ker_eq e t {i} hS, mem_Ks hS, LinearMap.mem_ker]
  induction m using (H.ops hc {i}).induction with
  | h0 => exact ⟨0, by simp⟩
  | hadd a b ha hb => exact pow_smul_add_mem Q _ ha hb
  | hof e t a =>
    obtain ⟨x, hx⟩ := a
    have hx' := (hker e t x).1 hx
    suffices hs : ∀ x ∈ Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (T (e + 1) t {i})),
        ∀ h : x ∈ Ks p e t {i}, ∃ k : ℕ,
          (MvPolynomial.X i : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k •
            (H.ops hc {i}).of e t ⟨x, h⟩ ∈ Q from hs x hx' hx
    intro x hx
    induction hx using Submodule.smul_induction_on' with
    | smul r hr y _ =>
      intro h
      obtain ⟨k, q, t', w, hw, e1⟩ := hform (e + 1) t y
      obtain ⟨Φ, hΦ1, hΦ2⟩ := exists_mulMap hc H hr hS
      have e2 := congrArg Φ e1
      rw [hΦ2, map_add (f := _), hΦ2, hΦ1, hΦ1, hΦ1, map_pow, MvPolynomial.map_X] at e2
      have hz : r • w = 0 := H.smul_eq_zero_of_mem (e := e + 1) hS (m := e + 1) (n := 1) rfl hr
        (by simpa using hw)
      have e3 : (⟨r • w, smul_mem_Ks H hS hr w⟩ : Ks p e t' {i}) = 0 := Subtype.ext hz
      rw [e3, map_zero, add_zero] at e2
      refine ⟨k, ?_⟩
      rw [show (⟨r • y, h⟩ : Ks p e t {i}) = ⟨r • y, smul_mem_Ks H hS hr y⟩ from rfl, e2]
      exact Q.smul_mem _ (hQ e r hr)
    | add a ha b hb iha ihb =>
      intro h
      have e1 : (⟨a + b, h⟩ : Ks p e t {i}) =
          ⟨a, (hker e t a).2 ha⟩ + ⟨b, (hker e t b).2 hb⟩ := rfl
      rw [e1, map_add (f := _)]
      exact pow_smul_add_mem Q _ (iha _) (ihb _)

end Tower

theorem tot_singleton_finite_up_to_X :
    ∀ (ι : Type) [LinearOrder ι] (R : Type) [CommRing R] (g : ℕ) (ρ : Fin g → R) (T : ℕ → ℤ → Finset ι → Type) [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)] (res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S') (p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S) (mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S) fun j t => mm j e t S) (H : TowerAx ρ res p mm) (one : ∀ e (i : ι), T e 0 {i}), (∀ e i, p e 0 {i} (one (e + 1) i) = one e i) → (∀ e i t (a : T e t {i}), ∃ (k : ℕ) (q : MvPolynomial ι R) (t' : ℤ) (w : T e t' {i}), w ∈ Ideal.span (Set.range ρ) • (⊤ : Submodule R (T e t' {i})) ∧ (MvPolynomial.X i : MvPolynomial ι R) ^ k • GrSum.of (hc e {i}) t a = q • GrSum.of (hc e {i}) 0 (one e i) + GrSum.of (hc e {i}) t' w) → ∀ i : ι, ∃ s : Finset (H.Tot hc {i}), ∀ m : H.Tot hc {i}, ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k • m ∈ Submodule.span (MvPolynomial ι (MvPolynomial (Fin g) R)) (s : Set (H.Tot hc {i})) := by
  intro ι _ R _ g ρ T _ _ res p mm hc H one hone hform i
  classical
  have hS : ({i} : Finset ι).Nonempty := Finset.singleton_nonempty i
  let f : Fin g → H.Tot hc {i} := fun l => (H.ops hc {i}).of 0 0 ⟨ρ l • one (0 + 1) i,
    smul_mem_Ks H hS (by simpa using rho_mem l) _⟩
  refine ⟨Finset.univ.image f, fun m => ?_⟩
  set Q := Submodule.span (MvPolynomial ι (MvPolynomial (Fin g) R))
    ((Finset.univ.image f : Finset (H.Tot hc {i})) : Set (H.Tot hc {i})) with hQdef
  have hf : ∀ l, f l ∈ Q := fun l => Submodule.subset_span (by simp)
  refine exists_pow_smul_mem hc H one i (hform · i) Q (fun e r hr => ?_) m
  obtain ⟨_, h⟩ := pow_le_unitIdeal hc H one hone i Q hf e hr
  exact h

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingOperatorsUniformCokernel
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem grSum_induction {ι R : Type*} [CommRing R] {A : ℤ → Type*} [∀ n, AddCommGroup (A n)]
    [∀ n, Module R (A n)] {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} {hx : OperatorsCommute x}
    {C : GrSum hx → Prop} (m : GrSum hx) (h0 : C 0) (hof : ∀ n a, C (GrSum.of hx n a))
    (hadd : ∀ a b, C a → C b → C (a + b)) : C m :=
  DirectSum.induction_on (β := A) (motive := C) m h0 hof hadd

section Tower

variable {ι : Type} [LinearOrder ι] {R : Type} [CommRing R] {g : ℕ} {ρ : Fin g → R}
  {T : ℕ → ℤ → Finset ι → Type} [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)]
  {res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S'}
  {p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S}
  {mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S}

namespace TowerAx

def mulKer (H : TowerAx ρ res p mm) (e : ℕ) (t : ℤ) (S : Finset ι) (hS : S.Nonempty) (r : R)
    (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) : T (e + 1) t S →ₗ[R] Ks p e t S :=
  LinearMap.codRestrict _ (r • LinearMap.id) fun y => by
    have h := Submodule.smul_mem_smul hr (Submodule.mem_top (x := y))
    rw [← H.ker_eq e t S hS] at h
    exact (mem_Ks hS).2 h

@[simp]
theorem coe_mulKer (H : TowerAx ρ res p mm) (e : ℕ) (t : ℤ) (S : Finset ι) (hS : S.Nonempty)
    (r : R) (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) (y : T (e + 1) t S) :
    (H.mulKer e t S hS r hr y : T (e + 1) t S) = r • y := rfl

variable (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S)
  fun j t => mm j e t S)

def mulTot (H : TowerAx ρ res p mm) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R)
    (A := fun t => T e t S) fun j t => mm j e t S) (e : ℕ) (S : Finset ι) (hS : S.Nonempty) (r : R)
    (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) : GrSum (hc (e + 1) S) →+ H.Tot hc S :=
  DirectSum.toAddMonoid fun t =>
    ((H.ops hc S).of e t).comp (H.mulKer e t S hS r hr).toAddMonoidHom

theorem mulTot_of (H : TowerAx ρ res p mm) (e : ℕ) (S : Finset ι) (hS : S.Nonempty) (r : R)
    (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) (t : ℤ) (y : T (e + 1) t S) :
    H.mulTot hc e S hS r hr (GrSum.of (hc (e + 1) S) t y) =
      (H.ops hc S).of e t (H.mulKer e t S hS r hr y) :=
  DirectSum.toAddMonoid_of (β := fun t => T (e + 1) t S)
    (fun t => ((H.ops hc S).of e t).comp (H.mulKer e t S hS r hr).toAddMonoidHom) t y

theorem mulTot_X_smul (H : TowerAx ρ res p mm) (e : ℕ) (S : Finset ι) (hS : S.Nonempty) (r : R)
    (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) (j : ι) (m : GrSum (hc (e + 1) S)) :
    H.mulTot hc e S hS r hr ((MvPolynomial.X j : MvPolynomial ι R) • m) =
      (MvPolynomial.X j : MvPolynomial ι (MvPolynomial (Fin g) R)) •
        H.mulTot hc e S hS r hr m := by
  induction m using grSum_induction with
  | h0 => simp
  | hof t y =>
    rw [GrSum.X_smul_of, mulTot_of, mulTot_of, BiOps.X_smul_of]
    congr 1
    apply Subtype.ext
    change r • mm j (e + 1) t S y = mm j (e + 1) t S (r • y)
    rw [map_smul]
  | hadd a b ha hb => rw [smul_add, map_add (f := _), map_add (f := _), smul_add, ha, hb]

theorem mulTot_X_pow_smul (H : TowerAx ρ res p mm) (e : ℕ) (S : Finset ι) (hS : S.Nonempty)
    (r : R) (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) (j : ι) (k : ℕ)
    (m : GrSum (hc (e + 1) S)) :
    H.mulTot hc e S hS r hr ((MvPolynomial.X j : MvPolynomial ι R) ^ k • m) =
      (MvPolynomial.X j : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k •
        H.mulTot hc e S hS r hr m := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_succ', mul_smul, mul_smul, mulTot_X_smul, ih]

theorem mulKer_res (H : TowerAx ρ res p mm) (e : ℕ) (t : ℤ) {S S' : Finset ι} (h : S ⊆ S')
    (hS : S.Nonempty) (r : R) (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) (a : T (e + 1) t S) :
    H.mulKer e t S' (hS.mono h) r hr (res (e + 1) t S S' h a) =
      H.resK e t h (H.mulKer e t S hS r hr a) := by
  apply Subtype.ext
  rw [coe_resK, coe_mulKer, coe_mulKer, map_smul]

theorem exists_X_pow_smul_mem_range (H : TowerAx ρ res p mm)
    (hyp : ∀ e S j t (b : T e t (insert j S)), S.Nonempty → ∃ (k : ℕ) (t' : ℤ) (a : T e t' S),
      GrSum.of (hc e (insert j S)) t' (res e t' S (insert j S) (Finset.subset_insert j S) a) =
        (MvPolynomial.X j : MvPolynomial ι R) ^ k • GrSum.of (hc e (insert j S)) t b)
    (S : Finset ι) (j : ι) (hS : S.Nonempty) (e : ℕ) (t : ℤ) (w : T (e + 1) t (insert j S))
    (hw : w ∈ Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (T (e + 1) t (insert j S)))) :
    ∃ (h : w ∈ Ks p e t (insert j S)) (k : ℕ),
      (MvPolynomial.X j : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k •
          (H.ops hc (insert j S)).of e t ⟨w, h⟩ ∈
        LinearMap.range (H.resTot hc S (insert j S) (Finset.subset_insert j S)) := by
  have hS' : (insert j S).Nonempty := Finset.insert_nonempty j S
  induction hw using Submodule.smul_induction_on' with
  | smul r hr y _ =>
    obtain ⟨k, t', a, hk⟩ := hyp (e + 1) S j t y hS
    refine ⟨(H.mulKer e t _ hS' r hr y).2, k, (H.ops hc S).of e t' (H.mulKer e t' S hS r hr a), ?_⟩
    have h1 := congrArg (H.mulTot hc e (insert j S) hS' r hr) hk
    rw [mulTot_X_pow_smul, mulTot_of, mulTot_of, mulKer_res H e t' (Finset.subset_insert j S) hS]
      at h1
    rw [resTot_of]
    exact h1
  | add x _ y _ hx hy =>
    obtain ⟨hx', k₁, hk₁⟩ := hx
    obtain ⟨hy', k₂, hk₂⟩ := hy
    refine ⟨add_mem hx' hy', k₁ + k₂, ?_⟩
    have hsum : (H.ops hc (insert j S)).of e t ⟨x + y, add_mem hx' hy'⟩ =
        (H.ops hc (insert j S)).of e t ⟨x, hx'⟩ + (H.ops hc (insert j S)).of e t ⟨y, hy'⟩ :=
      map_add ((H.ops hc (insert j S)).of e t) ⟨x, hx'⟩ ⟨y, hy'⟩
    rw [hsum, smul_add]
    refine add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact Submodule.smul_mem _ _ hk₁
    · rw [pow_add, mul_smul]
      exact Submodule.smul_mem _ _ hk₂

end TowerAx

end Tower

theorem tower_kernels_lift_after_X_pow : ∀ (ι : Type) [LinearOrder ι] (R : Type) [CommRing R] (g : ℕ) (ρ : Fin g → R) (T : ℕ → ℤ → Finset ι → Type) [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)] (res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S') (p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S) (mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S) fun j t => mm j e t S) (H : TowerAx ρ res p mm), (∀ e S j t (b : T e t (insert j S)), S.Nonempty → ∃ (k : ℕ) (t' : ℤ) (a : T e t' S), GrSum.of (hc e (insert j S)) t' (res e t' S (insert j S) (Finset.subset_insert j S) a) = (MvPolynomial.X j : MvPolynomial ι R) ^ k • GrSum.of (hc e (insert j S)) t b) → ∀ (S : Finset ι) (j : ι) (b : H.Tot hc (insert j S)), S.Nonempty → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k • b ∈ LinearMap.range (H.resTot hc S (insert j S) (Finset.subset_insert j S)) := by
  intro ι _ R _ g ρ T _ _ res p mm hc H hyp S j b hS
  have hS' : (insert j S).Nonempty := Finset.insert_nonempty j S
  induction b using (H.ops hc (insert j S)).induction with
  | h0 => exact ⟨0, by simp⟩
  | hof e t a =>
    have ha : (a : T (e + 1) t (insert j S)) ∈
        Ideal.span (Set.range ρ) ^ (e + 1) •
          (⊤ : Submodule R (T (e + 1) t (insert j S))) := by
      rw [← H.ker_eq e t _ hS']
      exact (mem_Ks hS').1 a.2
    obtain ⟨_, k, hk⟩ := H.exists_X_pow_smul_mem_range hc hyp S j hS e t a ha
    exact ⟨k, hk⟩
  | hadd x y hx hy =>
    obtain ⟨k₁, hk₁⟩ := hx
    obtain ⟨k₂, hk₂⟩ := hy
    refine ⟨k₁ + k₂, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact Submodule.smul_mem _ _ hk₁
    · rw [pow_add, mul_smul]
      exact Submodule.smul_mem _ _ hk₂

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueChernClassNilpotentBaseStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_chern_class_nilpotent_base : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) (D : E.LineData X) (hD : sSup (𝒱D D) = ⊤) {Λ : Type} [CommRing Λ]
    (c : Λ →+* R) (N : ℕ), (N.factorial : R) = 0 →
    ∃! x, B.IsFirstChernClassOfLineBundle (q := q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) D c N x := by
  first | exact @GlobalTheory.CompanionTheory.CrystallineChernClass.existsUnique_crystalline_chern_class | exact GlobalTheory.CompanionTheory.CrystallineChernClass.existsUnique_crystalline_chern_class | (intros; apply GlobalTheory.CompanionTheory.CrystallineChernClass.existsUnique_crystalline_chern_class <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftClosedEmbeddingStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_lift_closed_embedding : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)) (sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S)) (hsh0 : ∀ j S, S.Nonempty → sh 0 j S = GlobalTheory.LB.ofSec (s j) (D 0 S)) (hshp : ∀ e j S, S.Nonempty → red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) j S)) = SecOnR.of _ _ _ (sh e j S)) (hshu : ∀ e i S, i ∈ S → ∃ y : SecOn (pw (N e) (-(d : ℤ))) (D e S), secMulOn rfl (sh e i S) y = oneOn (N e) (add_neg_cancel (d : ℤ)) (D e S)) (hc : ∀ e S, OperatorsCommute (ι := Fin (m + 1)) (R := R) (A := fun t => Tm I Y N D (d : ℤ) e t S) fun j t => mulT I Y N D (d : ℤ) e t S (sh e j S)) (e : ℕ) (i : Fin (m + 1)) (t : ℤ) (a : Tm I Y N D (d : ℤ) e t {i}), ∃ (k : ℕ) (q : MvPolynomial (Fin (m + 1)) R) (t' : ℤ) (w : Tm I Y N D (d : ℤ) e t' {i}), w ∈ I • (⊤ : Submodule R (Tm I Y N D (d : ℤ) e t' {i})) ∧ (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) R) ^ k • GrSum.of (hc e {i}) t a = q • GrSum.of (hc e {i}) 0 (oneT I Y N D (d : ℤ) e {i}) + GrSum.of (hc e {i}) t' w := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_form_add_ideal_smul | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_form_add_ideal_smul | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_form_add_ideal_smul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftSectionsNonvanishingStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_lift_sections_nonvanishing : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)) (sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S)) (hsh0 : ∀ j S, S.Nonempty → sh 0 j S = GlobalTheory.LB.ofSec (s j) (D 0 S)) (hshp : ∀ e j S, S.Nonempty → red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) j S)) = SecOnR.of _ _ _ (sh e j S)) (hshu : ∀ e i S, i ∈ S → ∃ y : SecOn (pw (N e) (-(d : ℤ))) (D e S), secMulOn rfl (sh e i S) y = oneOn (N e) (add_neg_cancel (d : ℤ)) (D e S)) (hc : ∀ e S, OperatorsCommute (ι := Fin (m + 1)) (R := R) (A := fun t => Tm I Y N D (d : ℤ) e t S) fun j t => mulT I Y N D (d : ℤ) e t S (sh e j S)), (∀ e S j t (a : Tm I Y N D (d : ℤ) e t S), S.Nonempty → resT I Y N D (d : ℤ) hDm e t (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial (Fin (m + 1)) R) ^ k • GrSum.of (hc e S) t a = 0) ∧ (∀ e S j t (b : Tm I Y N D (d : ℤ) e t (insert j S)), S.Nonempty → ∃ (k : ℕ) (t' : ℤ) (a : Tm I Y N D (d : ℤ) e t' S), GrSum.of (hc e (insert j S)) t' (resT I Y N D (d : ℤ) hDm e t' (Finset.subset_insert j S) a) = (MvPolynomial.X j : MvPolynomial (Fin (m + 1)) R) ^ k • GrSum.of (hc e (insert j S)) t b) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.localisation_grSum | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.localisation_grSum | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.localisation_grSum <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealFiltrationSaturatedStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_ideal_filtration_saturated : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (N : ℕ)
    (L : ℕ → Ideal (MvPolynomial (Fin (N + 1)) R)),
    (∀ e, HomogIdeal (L e)) →
    (∀ e, (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤ L e) →
    (∀ e f, (∀ k, ∃ m : ℕ, X k ^ m * f ∈ L e) → f ∈ L e) →
    (∀ e, ∀ f ∈ L e, ∀ k, ∃ m : ℕ, X k ^ m * f ∈
      L (e + 1) ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) →
    ∃ n₀ : ℕ, ∀ e n, n₀ ≤ n → ∀ f ∈ L e, f.IsHomogeneous n →
      ∃ f' ∈ L (e + 1), f'.IsHomogeneous n ∧
        f - f' ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Lift.uniform_lift | exact GlobalTheory.CompanionTheory.GE.Lift.uniform_lift | (intros; apply GlobalTheory.CompanionTheory.GE.Lift.uniform_lift <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperBirationalClosedSystemStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_birational_closed_system : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsLocallyNoetherian X] (J : X.IdealSheafData) {Z : Scheme.{0}} [Z.Over (Spec (.of A))] (ψ : Z ⟶ J.subscheme), IsProper ψ → (ψ ≫ J.subschemeι) ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ (W : J.subscheme.Opens), IsIso (ψ ∣_ W) → ∀ {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → (∀ e, Killed J (S e)) → ∀ (B : Subobject ((Scheme.Modules.pullback (ψ ≫ J.subschemeι)).obj E)), (∀ e, B ⊔ powSub I _ (e + 1) = pullSys I (ψ ≫ J.subschemeι) E S e) → ∀ (V : X.affineOpens) (f : Γ(X, V)), J.subschemeι ⁻¹ᵁ X.basicOpen f ≤ W → ∀ x ∈ secs (adjKer (ψ ≫ J.subschemeι) B) V, ∃ k : ℕ, ∀ n, f ^ k • x ∈ secs (S n) V := by
  first | exact @GlobalTheory.CompanionTheory.GE.LocTors.adjKer_pow_smul_mem_secs | exact GlobalTheory.CompanionTheory.GE.LocTors.adjKer_pow_smul_mem_secs | (intros; apply GlobalTheory.CompanionTheory.GE.LocTors.adjKer_pow_smul_mem_secs <;> assumption)
end

