module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0436
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0458
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0452
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0440
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePhiModuleMapExists
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.CrysEps

theorem shift_C {K : Type} [Field K] [CharZero K] (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (h : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f)
    (k : K) : sh (PowerSeries.C k) = PowerSeries.C (PowerSeries.C k) := by
  refine PowerSeries.ext fun i => ?_
  cases i with
  | zero => simpa using h (PowerSeries.C k) 0
  | succ n =>
    have h1 := h (PowerSeries.C k) (n + 1)
    rw [Function.iterate_succ_apply, PowerSeries.derivative_C,
      PowerSeries.iterate_derivative_zero] at h1
    have h2 : ((n + 1).factorial : K⟦X⟧) ≠ 0 := by
      rw [← map_natCast (PowerSeries.C : K →+* K⟦X⟧), Ne,
        map_eq_zero_iff _ PowerSeries.C_injective]
      exact Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    rw [(mul_eq_zero.1 h1).resolve_left h2, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero n)]

theorem bc_induction {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) (p : N → Prop)
    (h0 : p 0) (hadd : ∀ y z, p y → p z → p (y + z)) (hs : ∀ (r : B) y, p y → p (r • y))
    (hu : ∀ x, p (u x)) (y : N) : p y := by
  first
  | (rename_i h_4 h_5 h_6 h_7 h_8 h_9; revert A B M N h_4 h_5 h_6 h_7 h_8 h_9 f u h p h0 hadd hs hu y; exact @_root_.GlobalTheory.BaseChangeInduction.baseChange_induction)
  | exact @_root_.GlobalTheory.BaseChangeInduction.baseChange_induction
  | exact _root_.GlobalTheory.BaseChangeInduction.baseChange_induction
  | (apply _root_.GlobalTheory.BaseChangeInduction.baseChange_induction <;> assumption)
  | (intros; apply _root_.GlobalTheory.BaseChangeInduction.baseChange_induction <;> assumption)
  | (intros; apply @_root_.GlobalTheory.BaseChangeInduction.baseChange_induction <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.BaseChangeInduction.baseChange_induction ..)

theorem exists_crystalline_epsilon_combination {l : ℕ} [Fact l.Prime] {a e : ℕ} {O K : Type} [CommRing O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [CharZero K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : Type} [CommRing R] (Q : Obj l R) (toA : Q.A → ZMod a → K⟦X⟧) {J : Type} [Fintype J] (o : J → O)
    (hspan : ∀ f : ZMod a → K⟦X⟧, (∀ τ, f τ ∈ A O K) → ∃ w : J → Q.A, ∀ τ,
      f τ = ∑ k, PowerSeries.C (algebraMap O K (o k)) * toA (w k) τ)
    (P : PhiMod O K l e a ι) (EE : FCrys l R) (c : EE.M Q →+ Vec K a ι) (hinj : Function.Injective c)
    (hmem : ∀ x, c x ∈ P.M) (hsurj : ∀ m ∈ P.M, ∃ x, c x = m)
    (hw : ∀ (w : Q.A) (x : EE.M Q), c (w • x) = fun τ i => toA w τ * c x τ i)
    (hU : ∀ o : O, ∃ U : FHom EE EE, ∀ x,
      c (U.u Q x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i)
    (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f)
    (PP : Obj l R) (p₀ p₁ : GlobalTheory.Prism.Hom Q PP) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧)
    (lam₀ lam₁ : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧))
    (hl₀ : ∀ (r : PP.A) (y : EE.M PP) τ i, lam₀ (r • y) τ i = j τ r * lam₀ y τ i)
    (hl₁ : ∀ (r : PP.A) (y : EE.M PP) τ i, lam₁ (r • y) τ i = j τ r * lam₁ y τ i)
    (ht₀ : ∀ x τ i, lam₀ (EE.tr p₀ x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i)))
    (ht₁ : ∀ x τ i, lam₁ (EE.tr p₁ x) τ i = sh (frob K l (c x (τ - 1) i))) :
    ∃ ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧, ∀ y τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ := by
  have hb : ∀ k : ι, (fun _ => Pi.single k 1 : Vec K a ι) ∈ P.M := fun k => mem_tot.2 fun τ i => by
    rcases eq_or_ne i k with rfl | h
    · simp only [Pi.single_eq_same]; exact one_mem _
    · simp only [Pi.single_eq_of_ne h]; exact zero_mem _
  choose b hb using fun k => hsurj _ (hb k)
  choose U hU using hU
  refine ⟨fun τ => Matrix.of fun i k => lam₀ (EE.tr p₁ (b k)) τ i, ?_⟩
  set ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧ := fun τ => Matrix.of fun i k => lam₀ (EE.tr p₁ (b k)) τ i with hε

  have hU₀ : ∀ o y τ i, lam₀ ((U o).u PP y) τ i =
      PowerSeries.C (PowerSeries.C (algebraMap O K o)) * lam₀ y τ i := by
    intro o y
    refine bc_induction (EE.tr_bc p₀) (fun y => ∀ τ i, lam₀ ((U o).u PP y) τ i =
      PowerSeries.C (PowerSeries.C (algebraMap O K o)) * lam₀ y τ i) ?_ ?_ ?_ ?_ y
    · intro τ i; simp
    · intro y z hy hz τ i
      simp only [map_add (f := _), Pi.add_apply, hy, hz, mul_add]
    · intro r y hy τ i
      rw [map_smul, hl₀, hl₀, hy]; ring
    · intro x τ i
      rw [(U o).u_tr, ht₀, ht₀, hU]
      simp only [map_mul, frob_C]
  have hU₁ : ∀ o x τ i, lam₁ ((U o).u PP (EE.tr p₁ x)) τ i =
      PowerSeries.C (PowerSeries.C (algebraMap O K o)) * lam₁ (EE.tr p₁ x) τ i := by
    intro o x τ i
    rw [(U o).u_tr, ht₁, ht₁, hU]
    simp only [map_mul, frob_C, shift_C sh hsh]
  have hS0 : ∀ τ, lam₀ 0 τ = ε τ *ᵥ lam₁ 0 τ := by intro τ; simp
  have hSadd : ∀ y z, (∀ τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ) → (∀ τ, lam₀ z τ = ε τ *ᵥ lam₁ z τ) →
      ∀ τ, lam₀ (y + z) τ = ε τ *ᵥ lam₁ (y + z) τ := by
    intro y z hy hz τ
    simp only [map_add (f := _), Pi.add_apply, hy, hz, Matrix.mulVec_add]
  have hSs : ∀ (r : PP.A) y, (∀ τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ) →
      ∀ τ, lam₀ (r • y) τ = ε τ *ᵥ lam₁ (r • y) τ := by
    intro r y hy τ
    have e0 : lam₀ (r • y) τ = j τ r • lam₀ y τ := funext fun i => hl₀ r y τ i
    have e1 : lam₁ (r • y) τ = j τ r • lam₁ y τ := funext fun i => hl₁ r y τ i
    rw [e0, e1, hy, Matrix.mulVec_smul]
  have hSU : ∀ o x, (∀ τ, lam₀ (EE.tr p₁ x) τ = ε τ *ᵥ lam₁ (EE.tr p₁ x) τ) →
      ∀ τ, lam₀ (EE.tr p₁ ((U o).u _ x)) τ = ε τ *ᵥ lam₁ (EE.tr p₁ ((U o).u _ x)) τ := by
    intro o x hx τ
    rw [← (U o).u_tr]
    have e0 : lam₀ ((U o).u PP (EE.tr p₁ x)) τ =
        (PowerSeries.C (PowerSeries.C (algebraMap O K o)) : K⟦X⟧⟦X⟧) • lam₀ (EE.tr p₁ x) τ :=
      funext fun i => hU₀ o _ τ i
    have e1 : lam₁ ((U o).u PP (EE.tr p₁ x)) τ =
        (PowerSeries.C (PowerSeries.C (algebraMap O K o)) : K⟦X⟧⟦X⟧) • lam₁ (EE.tr p₁ x) τ :=
      funext fun i => hU₁ o _ τ i
    rw [e0, e1, hx, Matrix.mulVec_smul]
  have hSb : ∀ k τ, lam₀ (EE.tr p₁ (b k)) τ = ε τ *ᵥ lam₁ (EE.tr p₁ (b k)) τ := by
    intro k τ
    have e1 : lam₁ (EE.tr p₁ (b k)) τ = Pi.single k 1 := funext fun i => by
      rw [ht₁, hb]
      rcases eq_or_ne i k with rfl | h
      · simp only [Pi.single_eq_same, map_one]
      · simp only [Pi.single_eq_of_ne h, map_zero]
    rw [e1, Matrix.mulVec_single_one]
    rfl
  refine bc_induction (EE.tr_bc p₁) (fun y => ∀ τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ) hS0 hSadd hSs fun x => ?_
  choose w hwx using fun i => hspan (fun τ => c x τ i) fun τ => mem_tot.1 (hmem x) τ i
  have hx : x = ∑ i, ∑ k, (U (o k)).u _ (w i k • b i) := by
    apply hinj
    funext τ i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Finset.sum_apply, hU, hw, hb]
    rw [Finset.sum_eq_single i]
    · simp only [Pi.single_eq_same, mul_one]
      exact hwx i τ
    · intro i' _ h
      simp only [Pi.single_eq_of_ne h.symm, mul_zero, Finset.sum_const_zero]
    · simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx, map_sum]
  refine Finset.sum_induction _ (fun y => ∀ τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ) hSadd hS0 fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_induction _ (fun y => ∀ τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ) hSadd hS0 fun k _ => ?_
  refine hSU _ _ ?_
  rw [LinearMap.map_smulₛₗ]
  exact hSs _ _ (hSb i)

theorem exists_eps : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), Function.Injective c → (∀ x, c x ∈ P.M) → (∀ m ∈ P.M, ∃ x, c x = m) → (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → (∀ o : O, ∃ U : FHom EE EE, ∀ x, c (U.u (ϖ.prism a) x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i) → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧), (∀ τ (x : (Wq l a)⟦X⟧), j τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ j τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) → ∀ (lam₀ lam₁ : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧)), (∀ (r : PP.A) (y : EE.M PP) τ i, lam₀ (r • y) τ i = j τ r * lam₀ y τ i) → (∀ (r : PP.A) (y : EE.M PP) τ i, lam₁ (r • y) τ i = j τ r * lam₁ y τ i) → (∀ x τ i, lam₀ (EE.tr p₀ x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → (∀ x τ i, lam₁ (EE.tr p₁ x) τ i = sh (frob K l (c x (τ - 1) i))) → ∃ ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧, ∀ y τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P EE c hinj hmem hsurj hw hU sh hsh PP p₀ p₁ j _
    lam₀ lam₁ hl₀ hl₁ ht₀ ht₁
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  refine exists_crystalline_epsilon_combination (ϖ.prism a) (fun w τ => (toAc t K w τ : K⟦X⟧)) (Module.Free.chooseBasis ℤ_[l] O) ?_
    P EE c hinj hmem hsurj hw hU sh hsh PP p₀ p₁ j lam₀ lam₁ hl₀ hl₁ ht₀ ht₁
  intro f hf
  obtain ⟨w, hw⟩ := exists_eq_sum_toAc t K (Module.Free.chooseBasis ℤ_[l] O) fun τ => ⟨f τ, hf τ⟩
  refine ⟨w, fun τ => ?_⟩
  refine (congrArg Subtype.val (congrFun hw τ)).trans ?_
  rw [Finset.sum_apply, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, Subalgebra.coe_smul, Algebra.smul_def, algebraMap_eq_C]

end GlobalTheory.BKGal.CrysEps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedPowerSeriesSubringEqGeneratorSet
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysPrism

section SdClosed

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)

theorem lTo0_atTop {w : ℕ → Wq l a} : LTo0 l w ↔ ∀ r : ℕ, ∃ N, ∀ n ≥ N, (l : Wq l a) ^ r ∣ w n := by
  simp only [LTo0, Nat.cofinite_eq_atTop, eventually_atTop]

theorem sdSet_zero : (0 : ZMod a → K⟦X⟧) ∈ SdSet t K e :=
  ⟨0, fun r => Eventually.of_forall fun _ => dvd_zero _, fun τ n => by simp⟩

theorem sdSet_one : (1 : ZMod a → K⟦X⟧) ∈ SdSet t K e := by
  refine ⟨fun n => if n = 0 then 1 else 0, lTo0_atTop.2 fun r => ⟨1, fun n hn => ?_⟩, fun τ n => ?_⟩
  · rw [if_neg (by omega)]; exact dvd_zero _
  · rw [Pi.one_apply, coeff_one]
    by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]

theorem sdSet_neg {F : ZMod a → K⟦X⟧} (hF : F ∈ SdSet t K e) : -F ∈ SdSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  refine ⟨-w, fun r => (hw r).mono fun n hn => ?_, fun τ n => ?_⟩
  · simpa using hn
  · simp [hF τ n]

theorem sdSet_add {F G : ZMod a → K⟦X⟧} (hF : F ∈ SdSet t K e) (hG : G ∈ SdSet t K e) :
    F + G ∈ SdSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  obtain ⟨w', hw', hG⟩ := hG
  refine ⟨w + w', fun r => ((hw r).and (hw' r)).mono fun n hn => ?_, fun τ n => ?_⟩
  · exact dvd_add hn.1 hn.2
  · simp [mul_add, hF τ n, hG τ n]

theorem fact_div_dvd (e i j : ℕ) : (i / e).factorial * (j / e).factorial ∣ ((i + j) / e).factorial :=
  (Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans
    (Nat.factorial_dvd_factorial (Nat.add_div_le_add_div i j e))

theorem sdSet_mul {F G : ZMod a → K⟦X⟧} (hF : F ∈ SdSet t K e) (hG : G ∈ SdSet t K e) :
    F * G ∈ SdSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  obtain ⟨w', hw', hG⟩ := hG
  let q : ℕ → ℕ → ℕ := fun i j => ((i + j) / e).factorial / ((i / e).factorial * (j / e).factorial)
  have hq : ∀ i j, ((i + j) / e).factorial = q i j * ((i / e).factorial * (j / e).factorial) := fun i j =>
    (Nat.div_mul_cancel (fact_div_dvd e i j)).symm
  refine ⟨fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, q p.1 p.2 • (w p.1 * w' p.2), ?_, fun τ n => ?_⟩
  · rw [lTo0_atTop] at hw hw' ⊢
    intro r
    obtain ⟨N, hN⟩ := hw r
    obtain ⟨N', hN'⟩ := hw' r
    refine ⟨N + N', fun n hn => Finset.dvd_sum fun p hp => ?_⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [nsmul_eq_mul]
    apply Dvd.dvd.mul_left
    by_cases h1 : N ≤ p.1
    · exact (hN _ h1).mul_right _
    · exact (hN' _ (by omega)).mul_left _
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [Pi.mul_apply, coeff_mul, Finset.mul_sum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rw [map_nsmul, map_nsmul, nsmul_eq_mul, map_mul, map_mul, ← hF τ p.1, ← hG τ p.2, ← hp, hq p.1 p.2]
      push_cast
      ring

theorem sd_sub_sdSet : ∀ F ∈ Sd t K e, F ∈ SdSet t K e := by
  let S : Subring (ZMod a → K⟦X⟧) :=
    { carrier := SdSet t K e
      zero_mem' := sdSet_zero t e
      one_mem' := sdSet_one t e
      add_mem' := fun hF hG => sdSet_add t e hF hG
      mul_mem' := fun hF hG => sdSet_mul t e hF hG
      neg_mem' := fun hF => sdSet_neg t e hF }
  intro F hF
  exact (Subring.closure_le.2 (fun x hx => hx) : Sd t K e ≤ S) hF

end SdClosed

theorem sdSet_closed : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ Sd t K e, F ∈ SdSet t K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t
  exact sd_sub_sdSet t e

end GlobalTheory.CrysPrism
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedTwoVariableSubringSubsetGeneratorSet
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysPrism

section Closed

variable {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a]

theorem LTo0_zero {ι : Type} : LTo0 l (0 : ι → Wq l a) :=
  fun _ => Eventually.of_forall fun _ => dvd_zero _

theorem LTo0_add {ι : Type} {w w' : ι → Wq l a} (h : LTo0 l w) (h' : LTo0 l w') : LTo0 l (w + w') :=
  fun r => ((h r).and (h' r)).mono fun _ hp => dvd_add hp.1 hp.2

theorem LTo0_neg {ι : Type} {w : ι → Wq l a} (h : LTo0 l w) : LTo0 l (-w) :=
  fun r => (h r).mono fun _ hp => (dvd_neg).2 hp

theorem LTo0_single : LTo0 l (fun p : ℕ × ℕ => if p = (0, 0) then (1 : Wq l a) else 0) :=
  fun _ => (eventually_cofinite_ne ((0 : ℕ), (0 : ℕ))).mono fun _ hp => by simp [hp]

theorem LTo0_conv {w w' : ℕ × ℕ → Wq l a} (h : LTo0 l w) (h' : LTo0 l w')
    (c : ℕ → ℕ → ℕ × ℕ → ℕ × ℕ → ℕ) :
    LTo0 l (fun p : ℕ × ℕ => ∑ x ∈ Finset.HasAntidiagonal.antidiagonal p.1, ∑ y ∈ Finset.HasAntidiagonal.antidiagonal p.2,
      (c p.1 p.2 x y : Wq l a) * w (x.1, y.1) * w' (x.2, y.2)) := by
  intro r
  have hB := h r
  have hB' := h' r
  rw [Filter.eventually_cofinite] at hB hB' ⊢
  refine ((hB.prod hB').image fun pq : (ℕ × ℕ) × (ℕ × ℕ) => pq.1 + pq.2).subset ?_
  rintro ⟨i, n⟩ hp
  by_contra hni
  apply hp
  refine Finset.dvd_sum fun x hx => Finset.dvd_sum fun y hy => ?_
  by_cases h1 : (l : Wq l a) ^ r ∣ w (x.1, y.1)
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h1 _) _
  by_cases h2 : (l : Wq l a) ^ r ∣ w' (x.2, y.2)
  · exact dvd_mul_of_dvd_right h2 _
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx hy
  exact (hni ⟨((x.1, y.1), (x.2, y.2)), ⟨h1, h2⟩, by simp [Prod.mk_add_mk, hx, hy]⟩).elim

variable {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)

theorem PPSet_zero : (0 : ZMod a → K⟦X⟧⟦X⟧) ∈ PPSet t K e :=
  ⟨0, LTo0_zero, fun τ i n => by simp⟩

theorem PPSet_one : (1 : ZMod a → K⟦X⟧⟦X⟧) ∈ PPSet t K e := by
  refine ⟨_, LTo0_single, fun τ i n => ?_⟩
  simp only [Pi.one_apply, coeff_one]
  by_cases hi : i = 0
  · subst hi
    by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]
  · simp [hi]

theorem PPSet_add {F G : ZMod a → K⟦X⟧⟦X⟧} (hF : F ∈ PPSet t K e) (hG : G ∈ PPSet t K e) :
    F + G ∈ PPSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  obtain ⟨w', hw', hG⟩ := hG
  refine ⟨w + w', LTo0_add hw hw', fun τ i n => ?_⟩
  simp only [Pi.add_apply, map_add (f := _), mul_add, hF, hG]

theorem PPSet_neg {F : ZMod a → K⟦X⟧⟦X⟧} (hF : F ∈ PPSet t K e) : -F ∈ PPSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  refine ⟨-w, LTo0_neg hw, fun τ i n => ?_⟩
  simp only [Pi.neg_apply, map_neg, mul_neg, hF]

theorem PPSet_mul {F G : ZMod a → K⟦X⟧⟦X⟧} (hF : F ∈ PPSet t K e) (hG : G ∈ PPSet t K e) :
    F * G ∈ PPSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  obtain ⟨w', hw', hG⟩ := hG
  let c : ℕ → ℕ → ℕ × ℕ → ℕ × ℕ → ℕ := fun i n x y =>
    (i.factorial * (n / e).factorial) /
      ((x.1.factorial * (y.1 / e).factorial) * (x.2.factorial * (y.2 / e).factorial))
  refine ⟨_, LTo0_conv hw hw' c, fun τ i n => ?_⟩
  have hc : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal i, ∀ y ∈ Finset.HasAntidiagonal.antidiagonal n,
      i.factorial * (n / e).factorial =
        c i n x y * ((x.1.factorial * (y.1 / e).factorial) * (x.2.factorial * (y.2 / e).factorial)) := by
    intro x hx y hy
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx hy
    refine (Nat.div_mul_cancel ?_).symm
    rw [mul_mul_mul_comm]
    apply mul_dvd_mul
    · rw [← hx]; exact Nat.factorial_mul_factorial_dvd_factorial_add _ _
    · exact (Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans
        (Nat.factorial_dvd_factorial (by rw [← hy]; exact Nat.add_div_le_add_div _ _ _))
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Pi.mul_apply, coeff_mul, map_sum, Finset.mul_sum, map_mul, map_natCast]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  rw [hc x hx y hy, ← hF τ x.1 y.1, ← hG τ x.2 y.2]
  push_cast
  ring

theorem PPd_subset_PPSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O),
    ∀ F ∈ PPd t K e, F ∈ PPSet t K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t F hF
  let S : Subring (ZMod a → K⟦X⟧⟦X⟧) :=
    { carrier := PPSet t K e
      mul_mem' := PPSet_mul t e
      one_mem' := PPSet_one t e
      add_mem' := PPSet_add t e
      zero_mem' := PPSet_zero t e
      neg_mem' := PPSet_neg t e }
  exact (Subring.closure_le (t := S)).2 le_rfl hF

end Closed

end GlobalTheory.CrysPrism
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinEvalNonZeroDivisorNatCastIsUnit
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalStep

theorem ED_nzd_and_natCast_isUnit : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type)
    [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e),
    (∀ y : OD l O, GlobalTheory.GalStep.ED K t ϖ * y = 0 → y = 0) ∧ ∀ n : ℕ, n ≠ 0 → IsUnit (n : OD l O) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ
  refine ⟨fun y hy => ?_, fun n hn => ?_⟩
  · have hd : ED K t ϖ = (1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) := by
      rw [ED, PiSys.iD, glue_const, Ehat, PiSys.iHat_ofAl]
      exact (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E a O K))
    set d := GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))
    have hinj : Function.Injective (LinearMap.mulLeft ℤ_[l] d) := by
      intro x z hxz
      rw [← sub_eq_zero]
      apply GlobalTheory.BKReal.HatDescent.aDp_ev_eis_mul_eq_zero (a := a) ϖ
      simp only [LinearMap.mulLeft_apply] at hxz
      rw [mul_sub, hxz, sub_self]
    have hT := Module.Flat.lTensor_preserves_injective_linearMap (M := O) _ hinj
    have hmul : ∀ z : OD l O, (LinearMap.mulLeft ℤ_[l] d).lTensor O z = ((1 : O) ⊗ₜ[ℤ_[l]] d) * z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul o β => simp [Algebra.TensorProduct.tmul_mul_tmul]
      | add x w hx hw => rw [map_add (f := _), hx, hw, mul_add]
    apply hT
    rw [hmul, map_zero, ← hd, hy]
  · obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l (Fact.out : l.Prime).one_lt.ne'
    have hmu : IsUnit (m : ℤ_[l]) :=
      PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2
        ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm))
    have hmu' : IsUnit (m : OD l O) := by
      simpa only [map_natCast] using hmu.map (algebraMap ℤ_[l] (OD l O))
    rw [Nat.cast_mul, Nat.cast_pow]
    exact (isUnit_l_OD.pow k).mul hmu'

end GlobalTheory.GalStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqBotOrTopOfSpanEqTop
section
open scoped BigOperators
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

namespace GlobalTheory.BurnsideIff

theorem eq_bot_or_top_of_span_eq_top {Γ k K : Type} [Field k] [Field K] [Algebra k K] {r : ℕ}
    (M : Γ → Matrix (Fin r) (Fin r) k) (h : Submodule.span k (Set.range M) = ⊤)
    (W : Submodule K (Fin r → K))
    (hW : ∀ g, ∀ x ∈ W, ((M g).map (algebraMap k K)).mulVec x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  first
  | (rename_i h_3 h_4 h_5; revert Γ k K h_3 h_4 h_5 r M h W hW; exact @_root_.GlobalTheory.InvariantBotOrTop.main)
  | exact @_root_.GlobalTheory.InvariantBotOrTop.main
  | exact _root_.GlobalTheory.InvariantBotOrTop.main
  | (apply _root_.GlobalTheory.InvariantBotOrTop.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.InvariantBotOrTop.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InvariantBotOrTop.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InvariantBotOrTop.main ..)

end GlobalTheory.BurnsideIff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleFunctorExactOnLatticesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleFunctor_exact_on_lattices : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsSESLat (Qp := ℚ_[l]) (O := ↥(OL LL)) ι π → Function.Injective (W.map ι) ∧ Function.Surjective (W.map π) ∧ ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x := by
  first | exact @GlobalTheory.LatExact.W_exact | exact GlobalTheory.LatExact.W_exact | (intros; apply GlobalTheory.LatExact.W_exact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBlockActionStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_block_action_of_decomposition : ∀ {Γ X O : Type} [Group Γ] [CommRing O] [IsDomain O] {n r t : ℕ} (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)) (ρ : Γ →* GL (Fin r) O) (χ : ℕ → (Γ →* Oˣ)) (π : X) (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O))), Submodule.span O (Set.range (mat ρ)) = ⊤ → IsDecomp (t := t) (rep π) ρ χ e → ∃ (ψρ : (X → Matrix (Fin n) (Fin n) O) → Matrix (Fin r) (Fin r) O) (ψχ : Fin t → (X → Matrix (Fin n) (Fin n) O) → O), (∀ a, InRing T rep a → ∀ u, e (((a π).map (toFr O)).mulVec u) = (((ψρ a).map (toFr O)).mulVec (e u).1, fun c : Fin t => toFr O (ψχ c a) * (e u).2 c)) ∧ ∀ P : Matrix (Fin r) (Fin r) O, ∃ a, InRing T rep a ∧ ψρ a = P := by
  first | exact @GlobalTheory.SpanBlockAction.exists_block_action | exact GlobalTheory.SpanBlockAction.exists_block_action | (intros; apply GlobalTheory.SpanBlockAction.exists_block_action <;> assumption)
end

