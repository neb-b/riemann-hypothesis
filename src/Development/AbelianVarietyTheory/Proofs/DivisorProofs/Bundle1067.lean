module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PolarisationOperatorApplyVariable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0833
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0214
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFormMinorProductEqProdHookProducts
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRowFock

open MvPolynomial

theorem fock_one {σ : Type} : Formalism.E.fock (1 : MvPolynomial σ ℂ) 1 = 1 := by
  simp [Formalism.E.fock, Formalism.A.mfact]

theorem fock_rename_inj {σ τ : Type} {f : σ → τ} (hf : Function.Injective f) (P P' : MvPolynomial σ ℂ) :
    Formalism.E.fock (rename f P) (rename f P') = Formalism.E.fock P P' := by
  have h := GlobalTheory.JointHarm.fock_rename_mul (g := (fun e : Empty => e.elim : Empty → τ)) hf
    (fun x => x.elim) (fun _ y => y.elim) P P' 1 1
  simpa [fock_one] using h

theorem fock_mul_of_supported {σ : Type} {A B : Set σ} (hAB : Disjoint A B) {P P' Q Q' : MvPolynomial σ ℂ}
    (hP : P ∈ supported ℂ A) (hP' : P' ∈ supported ℂ A) (hQ : Q ∈ supported ℂ B) (hQ' : Q' ∈ supported ℂ B) :
    Formalism.E.fock (P * Q) (P' * Q') = Formalism.E.fock P P' * Formalism.E.fock Q Q' := by
  rw [supported_eq_range_rename] at hP hP' hQ hQ'
  obtain ⟨P₀, rfl⟩ := (AlgHom.mem_range _).mp hP
  obtain ⟨P₁, rfl⟩ := (AlgHom.mem_range _).mp hP'
  obtain ⟨Q₀, rfl⟩ := (AlgHom.mem_range _).mp hQ
  obtain ⟨Q₁, rfl⟩ := (AlgHom.mem_range _).mp hQ'
  rw [GlobalTheory.JointHarm.fock_rename_mul Subtype.val_injective Subtype.val_injective
      (fun x y h => Set.disjoint_left.mp hAB x.2 (h ▸ y.2)),
    fock_rename_inj Subtype.val_injective, fock_rename_inj Subtype.val_injective]

theorem fock_prod_of_supported {σ ι : Type} [DecidableEq ι] (A : ι → Set σ) (hA : Pairwise fun i j => Disjoint (A i) (A j))
    (F G : ι → MvPolynomial σ ℂ) (hF : ∀ i, F i ∈ supported ℂ (A i)) (hG : ∀ i, G i ∈ supported ℂ (A i))
    (s : Finset ι) :
    Formalism.E.fock (∏ i ∈ s, F i) (∏ i ∈ s, G i) = ∏ i ∈ s, Formalism.E.fock (F i) (G i) := by
  induction s using Finset.induction_on with
  | empty => simp [fock_one]
  | insert a s ha ih =>
    have hd : Disjoint (A a) (⋃ i ∈ s, A i) :=
      Set.disjoint_iUnion₂_right.mpr fun i hi => hA (fun e => ha (e ▸ hi))
    have hmem : ∀ H : ι → MvPolynomial σ ℂ, (∀ i, H i ∈ supported ℂ (A i)) →
        ∏ i ∈ s, H i ∈ supported ℂ (⋃ i ∈ s, A i) := fun H hH =>
      Subalgebra.prod_mem _ fun i hi => supported_mono (Set.subset_biUnion_of_mem hi) (hH i)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha,
      fock_mul_of_supported hd (hF a) (hG a) (hmem F hF) (hmem G hG), ih]

theorem rename_mem_supported {σ τ : Type} (f : σ → τ) (s : Set τ) (hs : ∀ x, f x ∈ s) (P : MvPolynomial σ ℂ) :
    rename f P ∈ supported ℂ s := by
  classical
  rw [mem_supported]
  intro v hv
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp (vars_rename f P hv)
  exact hs w

variable {D : D7} {m n : ℕ}

theorem minorPlus_eq (τ : D.what₂.Tau) {p : ℕ} (hpm : p ≤ m) (hpn : p ≤ n) (i : Fin p) :
    minorPlus (D := D) (m := m) (n := n) τ (i + 1) =
      rename (fun v : Fin n × Fin p => ((τ, ⟨v.2, lt_of_lt_of_le v.2.2 hpm⟩, v.1) : FVar D m n))
        (GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.topMinor hpn i) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.topMinor, AlgHom.map_det]
  unfold minorPlus
  congr 1
  ext α β
  have := α.2
  have := β.2
  have := i.2
  simp only [Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, rename_X, varF]
  rw [dite_eq_left ⟨by omega, by omega⟩]

theorem minorMinus_eq (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) (hqn : q ≤ n) (i : Fin q) :
    minorMinus (D := D) (m := m) (n := n) τ p (i + 1) =
      rename (fun v : Fin n × Fin q => ((τ, ⟨p + v.2, by have := v.2.2; omega⟩, v.1) : FVar D m n))
        (GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.bottomMinor hqn i) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.bottomMinor, AlgHom.map_det]
  unfold minorMinus
  congr 1
  ext α β
  have := α.2
  have := β.2
  have := i.2
  simp only [Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, rename_X, varF]
  rw [dite_eq_left ⟨by omega, by omega⟩]

def embTop (τ : D.what₂.Tau) {p : ℕ} (hpm : p ≤ m) : Fin n × Fin p → FVar D m n :=
  fun v => (τ, ⟨v.2, lt_of_lt_of_le v.2.2 hpm⟩, v.1)

def embBot (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) : Fin n × Fin q → FVar D m n :=
  fun v => (τ, ⟨p + v.2, by have := v.2.2; omega⟩, v.1)

theorem embTop_injective (τ : D.what₂.Tau) {p : ℕ} (hpm : p ≤ m) : Function.Injective (embTop (n := n) τ hpm) := by
  intro x y e
  simp only [embTop, Prod.mk.injEq, Fin.mk.injEq] at e
  exact Prod.ext e.2.2 (Fin.ext e.2.1)

theorem embBot_injective (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) :
    Function.Injective (embBot (n := n) τ (q := q) hm) := by
  intro x y e
  simp only [embBot, Prod.mk.injEq, Fin.mk.injEq, add_right_inj] at e
  exact Prod.ext e.2.2 (Fin.ext e.2.1)

theorem embTop_ne_embBot (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) (x : Fin n × Fin p) (y : Fin n × Fin q) :
    embTop τ (by omega) x ≠ embBot τ hm y := by
  intro e
  simp only [embTop, embBot, Prod.mk.injEq, Fin.mk.injEq] at e
  have := x.2.2
  omega

theorem minorProduct_rename_mem_supported_place (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) (P : MvPolynomial (Fin n × Fin p) ℂ)
    (Q : MvPolynomial (Fin n × Fin q) ℂ) :
    rename (embTop τ (by omega)) P * rename (embBot τ hm) Q ∈ supported ℂ {v : FVar D m n | v.1 = τ} :=
  Subalgebra.mul_mem _ (rename_mem_supported (embTop τ (by omega)) {v : FVar D m n | v.1 = τ} (fun x => by simp [embTop]) P)
    (rename_mem_supported (embBot τ hm) {v : FVar D m n | v.1 = τ} (fun x => by simp [embBot]) Q)

theorem deltaAt_eq (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) (hpn : p ≤ n) (hqn : q ≤ n) (ap am : ℕ → ℕ) :
    deltaAt (D := D) (m := m) (n := n) τ p ap q am =
      rename (embTop τ (by omega)) (GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.delTop hpn (fun i : Fin p => ap i)) *
        rename (embBot τ hm) (GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.delBottom hqn (fun i : Fin q => am i)) := by
  unfold deltaAt GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.delTop GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.delBottom
  rw [map_prod, map_prod, Finset.prod_range, Finset.prod_range]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, minorPlus_eq τ (by omega) hpn i]
    congr 1
    try (unfold GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.nextPart; split_ifs <;> rfl)
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, minorMinus_eq τ hm hqn i]
    congr 1
    try (unfold GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.nextPart; split_ifs <;> rfl)

theorem hookOf_eq_hookProd (l : ℕ) (a : ℕ → ℕ) (ha : Antitone a) :
    (hookOf l a : ℂ) = ((GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookProd (fun i : Fin l => a i) : ℚ) : ℂ) := by
  have ha' : ∀ x y, x ≤ y → y < l → a y ≤ a x := fun x y h _ => ha h
  have hant : Antitone (fun i : Fin l => a i) := fun i j h => ha (Fin.le_iff_val_le_val.mp h)
  suffices h : (hookOf l a : ℚ) = GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookProd (fun i : Fin l => a i) by
    rw [← h]; push_cast; rfl
  rw [GlobalTheory.HookDiagram.hookOf_eq l a ha', GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookProd,
    eq_div_iff (GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookDen_pos hant).ne']
  have key := congrArg (Nat.cast : ℕ → ℚ) (GlobalTheory.LiftSizeCompare.hookProd_mul l a ha')
  push_cast [Nat.cast_prod] at key
  have hden : (∏ r ∈ Finset.range l, ∏ j ∈ Finset.Ioo r l, ((a r - a j + (j - r) : ℕ) : ℚ)) =
      GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookDen (fun i : Fin l => a i) := by
    rw [Finset.prod_range, GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookDen]
    refine Finset.prod_congr rfl fun i _ => ?_
    symm
    refine Finset.prod_bij (fun j _ => (j : ℕ)) ?_ ?_ ?_ ?_
    · intro j hj
      exact Finset.mem_Ioo.mpr ⟨Fin.lt_iff_val_lt_val.mp (Finset.mem_Ioi.mp hj), j.2⟩
    · intro j _ j' _ e
      exact Fin.ext e
    · intro b hb
      have := Finset.mem_Ioo.mp hb
      exact ⟨⟨b, this.2⟩, Finset.mem_Ioi.mpr (Fin.lt_iff_val_lt_val.mpr this.1), rfl⟩
    · intro j hj
      have hij : (i : ℕ) < j := Fin.lt_iff_val_lt_val.mp (Finset.mem_Ioi.mp hj)
      have h1 : a j ≤ a i := ha hij.le
      rw [Nat.cast_add, Nat.cast_sub h1, Nat.cast_sub hij.le]
      ring
  have hnum : (∏ r ∈ Finset.range l, (((a r + l - 1 - r).factorial : ℕ) : ℚ)) =
      ∏ i : Fin l, (((a i + (l - ((i : ℕ) + 1))).factorial : ℕ) : ℚ) := by
    rw [Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    have := i.2
    congr 3
    omega
  rw [← hden, ← hnum]
  exact_mod_cast key

theorem fock_deltaAt (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) (hpn : p ≤ n) (hqn : q ≤ n) (ap am : ℕ → ℕ)
    (hap : Antitone ap) (ham : Antitone am) :
    Formalism.E.fock (deltaAt (D := D) (m := m) (n := n) τ p ap q am) (deltaAt τ p ap q am) =
      (hookOf p ap : ℂ) * (hookOf q am : ℂ) := by
  have hp : Antitone (fun i : Fin p => ap i) := fun i j h => hap (Fin.le_iff_val_le_val.mp h)
  have hq : Antitone (fun i : Fin q => am i) := fun i j h => ham (Fin.le_iff_val_le_val.mp h)
  rw [deltaAt_eq τ hm hpn hqn, GlobalTheory.JointHarm.fock_rename_mul (embTop_injective τ _) (embBot_injective τ hm)
      (embTop_ne_embBot τ hm),
    GlobalTheory.MinorNorm.hookNorm _ _ _ _ hp, GlobalTheory.MinorNorm.hookNormBottom _ _ _ _ hq,
    hookOf_eq_hookProd _ _ hap, hookOf_eq_hookProd _ _ ham]

theorem fock_delta (D : D7) (m n : ℕ) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ)
    (h1 : ∀ τ, p τ + q τ ≤ m) (h2 : ∀ τ, p τ ≤ n ∧ q τ ≤ n) (h3 : ∀ τ, Antitone (ap τ) ∧ Antitone (am τ)) :
    Formalism.E.fock (Formalism.IndefR.Datum.delta (D := D) (m := m) (n := n) p q ap am) (Formalism.IndefR.Datum.delta p q ap am) =
      ∏ τ, ((hookOf (p τ) (ap τ) : ℂ) * (hookOf (q τ) (am τ) : ℂ)) := by
  classical
  have hmem : ∀ τ, deltaAt (D := D) (m := m) (n := n) τ (p τ) (ap τ) (q τ) (am τ) ∈
      supported ℂ {v : FVar D m n | v.1 = τ} := fun τ => by
    rw [deltaAt_eq τ (h1 τ) (h2 τ).1 (h2 τ).2]
    exact minorProduct_rename_mem_supported_place τ (h1 τ) _ _
  unfold Formalism.IndefR.Datum.delta
  rw [fock_prod_of_supported (fun τ => {v : FVar D m n | v.1 = τ})
    (fun a b hab => Set.disjoint_left.mpr fun v ha hb => hab (ha.symm.trans hb)) _ _ hmem hmem Finset.univ]
  exact Finset.prod_congr rfl fun τ _ =>
    fock_deltaAt τ (h1 τ) (h2 τ).1 (h2 τ).2 _ _ (h3 τ).1 (h3 τ).2

end GlobalTheory.LowRowFock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalDegreeDivVolumeUnitaryGroupLogBound
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow

theorem volU_ge_inv_pow_of_formalDeg (r : ℕ) (hr : 1 ≤ r) :
    (((r : ℝ) ^ r)⁻¹) ^ r ≤ ReciprocityTheory.ChartRestriction.DS.volU r := by
  unfold ReciprocityTheory.ChartRestriction.DS.volU
  have hrpos : (0 : ℝ) < (r : ℝ) ^ r := by positivity
  rw [show (((r : ℝ) ^ r)⁻¹) ^ r = ∏ _i ∈ Finset.range r, ((r : ℝ) ^ r)⁻¹ by
    rw [Finset.prod_const, Finset.card_range]]
  apply Finset.prod_le_prod₀
  · intro i _; positivity
  · intro i hi
    have hi' : i < r := Finset.mem_range.mp hi
    have hfac : (i.factorial : ℝ) ≤ (r : ℝ) ^ r := by
      have h1 : i.factorial ≤ r.factorial := Nat.factorial_le hi'.le
      have h2 : r.factorial ≤ r ^ r := Nat.factorial_le_pow r
      exact_mod_cast h1.trans h2
    have hfpos : (0 : ℝ) < (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i
    have hpi : (1 : ℝ) ≤ 2 * Real.pi ^ (i + 1) := by
      have : (1 : ℝ) ≤ Real.pi ^ (i + 1) := one_le_pow₀ (by linarith [Real.pi_gt_three])
      linarith
    calc ((r : ℝ) ^ r)⁻¹ ≤ (i.factorial : ℝ)⁻¹ := inv_anti₀ hfpos hfac
      _ = 1 / (i.factorial : ℝ) := by rw [one_div]
      _ ≤ 2 * Real.pi ^ (i + 1) / (i.factorial : ℝ) := by gcongr

theorem formalDeg_div_volU_log_bound : ∀ (r n : ℕ) (d : ℝ) (lam : Fin r → ℝ), 1 ≤ r → 3 ≤ n → 0 ≤ d → StrictAnti lam → (∀ a b, |lam a - lam b| ≤ d + n + 3) → 0 < ReciprocityTheory.ChartRestriction.DS.volU r ∧ 0 < (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|) / (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) ∧ Real.log ((∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|) / (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) / ReciprocityTheory.ChartRestriction.DS.volU r) ≤ 2 + (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2)) := by
  intro r n d lam hr hn hd hlam hbd
  set P : ℝ := ∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b| with hPdef
  set D : ℝ := ∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) with hDdef
  set V : ℝ := ReciprocityTheory.ChartRestriction.DS.volU r with hVdef
  set M : ℝ := d + n + 3 with hMdef
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hM1 : (1 : ℝ) ≤ M := by rw [hMdef]; linarith
  have hVlow := volU_ge_inv_pow_of_formalDeg r hr
  have hVpos : 0 < V := lt_of_lt_of_le (by positivity) hVlow
  have hPpos : 0 < P := by
    apply Finset.prod_pos
    intro a _
    apply Finset.prod_pos
    intro b hb
    have hab : a < b := (Finset.mem_filter.mp hb).2
    exact abs_pos.mpr (sub_ne_zero.mpr (hlam hab).ne')
  have hD1 : 1 ≤ D := by
    have : (∏ _a : Fin r, ∏ _b ∈ Finset.univ.filter (fun b : Fin r => _a < b), (1 : ℝ)) ≤ D := by
      apply Finset.prod_le_prod₀
      · intro a _; positivity
      · intro a _
        apply Finset.prod_le_prod₀
        · intro b _; positivity
        · intro b hb
          have hab : a < b := (Finset.mem_filter.mp hb).2
          have : (a : ℕ) + 1 ≤ (b : ℕ) := hab
          have : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast this
          linarith
    simpa using this
  have hDpos : 0 < D := lt_of_lt_of_le one_pos hD1
  have hPle : P ≤ M ^ (r * r) := by
    have : P ≤ ∏ _a : Fin r, M ^ r := by
      apply Finset.prod_le_prod₀
      · intro a _; exact Finset.prod_nonneg (fun b _ => abs_nonneg _)
      · intro a _
        calc (∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|)
            ≤ ∏ _b ∈ Finset.univ.filter (fun b : Fin r => a < b), M :=
              Finset.prod_le_prod₀ (fun b _ => abs_nonneg _) (fun b _ => hbd a b)
          _ = M ^ (Finset.univ.filter (fun b : Fin r => a < b)).card := Finset.prod_const _
          _ ≤ M ^ r := by
              apply pow_le_pow_right₀ hM1
              calc (Finset.univ.filter (fun b : Fin r => a < b)).card ≤ (Finset.univ : Finset (Fin r)).card :=
                    Finset.card_filter_le _ _
                _ = r := by simp
    calc P ≤ ∏ _a : Fin r, M ^ r := this
      _ = M ^ (r * r) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  have hVinv : V⁻¹ ≤ (r : ℝ) ^ (r * r) := by
    have h := inv_anti₀ (by positivity) hVlow
    rw [inv_pow, inv_inv, ← pow_mul] at h
    exact h
  have hQpos : 0 < P / D / V := by positivity
  have hQle : P / D / V ≤ (M * r) ^ (r * r) := by
    calc P / D / V ≤ P / V := by
          gcongr
          exact div_le_self hPpos.le hD1
      _ = P * V⁻¹ := div_eq_mul_inv _ _
      _ ≤ M ^ (r * r) * (r : ℝ) ^ (r * r) := by
          apply mul_le_mul hPle hVinv (by positivity) (by positivity)
      _ = (M * r) ^ (r * r) := (mul_pow _ _ _).symm
  refine ⟨hVpos, div_pos hPpos hDpos, ?_⟩
  have hsq : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hMn : M ≤ n * (d + 2) := by
    rw [hMdef]; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ n - 1) hd]
  have hr2 : (r : ℝ) ≤ 2 * Real.sqrt 2 * (r : ℝ) ^ 2 := by nlinarith
  have hX : M * r ≤ 2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2) := by
    calc M * r ≤ (n * (d + 2)) * (2 * Real.sqrt 2 * (r : ℝ) ^ 2) :=
          mul_le_mul hMn hr2 (by positivity) (by positivity)
      _ = 2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2) := by ring
  have hMr : 0 < M * r := by positivity
  calc Real.log (P / D / V) ≤ Real.log ((M * r) ^ (r * r)) := Real.log_le_log hQpos hQle
    _ = ((r * r : ℕ) : ℝ) * Real.log (M * r) := Real.log_pow _ _
    _ = (r : ℝ) ^ 2 * Real.log (M * r) := by push_cast; ring
    _ ≤ (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2)) := by
        gcongr
    _ ≤ 2 + (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2)) := by linarith

end GlobalTheory.LowRow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionFieldCoordinatesDlog
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtCoordBasis

open KaehlerDifferential

theorem kaehler_map_bijective (p : ℕ) (L : Type) [CommRing L] [Algebra (ZMod p) L] :
    Function.Bijective (KaehlerDifferential.map ℤ (ZMod p) L L) := by
  refine ⟨?_, KaehlerDifferential.map_surjective ℤ (ZMod p) L⟩
  have hsurj : Function.Surjective (algebraMap ℤ (ZMod p)) := by
    intro x
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective x
    exact ⟨m, by simp⟩
  have hs : Subsingleton Ω[ZMod p⁄ℤ] := KaehlerDifferential.subsingleton_of_surjective ℤ (ZMod p) hsurj
  have hex := KaehlerDifferential.exact_mapBaseChange_map ℤ (ZMod p) L
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (hex x).1 hx
  clear hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Subsingleton.elim b 0]
  | add y z hy hz => rw [map_add (f := _), hy, hz, add_zero]

theorem etale_coords_basis : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] (ht : ∀ j, algebraMap A L (t j) ≠ 0), IsCoord (fun j => Units.mk0 (algebraMap A L (t j)) (ht j)) ∧ ∀ f : A, ∃ c : Fin n → A, KaehlerDifferential.D ℤ L (algebraMap A L f) = ∑ j, algebraMap A L (c j) • KaehlerDifferential.D ℤ L (algebraMap A L (t j)) := by
  intro p _ A _ _ _ n t het L _ _ _ ht
  classical
  let P := MvPolynomial (Fin n) (ZMod p)
  letI : Algebra P A := (MvPolynomial.aeval t).toRingHom.toAlgebra
  haveI : IsScalarTower (ZMod p) P A :=
    .of_algebraMap_eq fun r => ((MvPolynomial.aeval t).commutes r).symm
  haveI : Algebra.Etale P A := het
  letI : Algebra (ZMod p) L := ((algebraMap A L).comp (algebraMap (ZMod p) A)).toAlgebra
  haveI : IsScalarTower (ZMod p) A L := .of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FormallyEtale A L := .of_isLocalization (nonZeroDivisors A)
  let bA : Module.Basis (Fin n) A Ω[A⁄ZMod p] :=
    ((mvPolynomialBasis (ZMod p) (Fin n)).baseChange A).map
      (tensorKaehlerEquivOfFormallyEtale (ZMod p) P A)
  have hbA : ∀ j, bA j = D (ZMod p) A (t j) := by
    intro j
    simp only [bA, Module.Basis.map_apply, Module.Basis.baseChange_apply,
      tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, mvPolynomialBasis_apply, map_D]
    have h : algebraMap P A (MvPolynomial.X j) = t j := by
      change MvPolynomial.aeval t (MvPolynomial.X j) = t j
      exact MvPolynomial.aeval_X t j
    rw [← h, ← map_D (ZMod p) (ZMod p) P A]
    exact (mapBaseChange_tmul (ZMod p) P A 1 _).trans (one_smul _ _)
  let bL : Module.Basis (Fin n) L Ω[L⁄ZMod p] :=
    (bA.baseChange L).map (tensorKaehlerEquivOfFormallyEtale (ZMod p) A L)
  have hbL : ∀ j, bL j = D (ZMod p) L (algebraMap A L (t j)) := by
    intro j
    simp only [bL, Module.Basis.map_apply, Module.Basis.baseChange_apply,
      tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, hbA, map_D]
  let e : Ω[L⁄ℤ] ≃ₗ[L] Ω[L⁄ZMod p] :=
    LinearEquiv.ofBijective (KaehlerDifferential.map ℤ (ZMod p) L L) (kaehler_map_bijective p L)
  have he : ∀ x : L, e.symm (D (ZMod p) L x) = D ℤ L x := by
    intro x
    rw [LinearEquiv.symm_apply_eq]
    exact (KaehlerDifferential.map_D ℤ (ZMod p) L L x).symm
  let b : Module.Basis (Fin n) L Ω[L⁄ℤ] := bL.map e.symm
  have hb : ∀ j, b j = D ℤ L (algebraMap A L (t j)) := by
    intro j
    simp only [b, Module.Basis.map_apply, hbL, he]
  have hfun : (fun i => dK ((Units.mk0 (algebraMap A L (t i)) (ht i) : Lˣ) : L)) = ⇑b := by
    funext i
    simp [hb, dK]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hfun]; exact b.linearIndependent
  · rw [hfun]; exact b.span_eq
  · intro f
    refine ⟨bA.repr (D (ZMod p) A f), ?_⟩
    have h1 := bA.sum_repr (D (ZMod p) A f)
    rw [← he, ← map_D (ZMod p) (ZMod p) A L]
    conv_lhs => rw [← h1]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.map_smul, hbA, map_D, ← algebraMap_smul L (bA.repr (D (ZMod p) A f) j), LinearEquiv.map_smul, he]

end GlobalTheory.EtCoordBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusTwistDivisorRecursion
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem GlobalTheory.nat_mul_div_bounds_rounded_multiples (p r m : ℕ) (hp : 0 < p) (hr : 0 < r) :
    p * (m / r) ≤ p * m / r ∧ p * m / r + 1 ≤ p * (m / r) + p := by
  have h1 : p * m = p * (m % r) + r * (p * (m / r)) := by
    conv_lhs => rw [← Nat.mod_add_div m r]
    ring
  have h2 : p * m / r = p * (m % r) / r + p * (m / r) := by
    rw [h1, Nat.add_mul_div_left _ _ hr]
  have h4 : p * (m % r) < p * r := Nat.mul_lt_mul_of_pos_left (Nat.mod_lt m hr) hp
  have h3 : p * (m % r) / r < p := (Nat.div_lt_iff_lt_mul hr).2 h4
  rw [h2]
  generalize p * (m % r) / r = q at h3 ⊢
  generalize p * (m / r) = s
  constructor <;> omega

theorem GlobalTheory.rounded_multiples_step : ∀ (X : Scheme.{0}) [IsIntegral X] (p : ℕ) {C : Type} [Fintype C] (E : C → CartierDiv X) (M Kc : CartierDiv X) (r : ℕ) (b : C → ℕ), 0 < p → 0 < r → ∀ e : ℕ, ∃ ρ : C → ℕ, (∀ c, ρ c < p) ∧ (fun e => p ^ e • (M - Kc) - ∑ c, (p ^ e * b c / r) • E c - ∑ c, E c) (e + 1) = p • (fun e => p ^ e • (M - Kc) - ∑ c, (p ^ e * b c / r) • E c - ∑ c, E c) e + ∑ c, ρ c • E c := by
  intro X _ p C _ E M Kc r b hp hr e
  have hm : ∀ c, p ^ (e + 1) * b c = p * (p ^ e * b c) := fun c => by ring
  refine ⟨fun c => p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r, ?_, ?_⟩
  · intro c
    have := GlobalTheory.nat_mul_div_bounds_rounded_multiples p r (p ^ e * b c) hp hr
    show p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r < p
    rw [hm c]
    omega
  · have hc : ∀ c, p • ((p ^ e * b c / r) • E c + E c)
        = (p ^ (e + 1) * b c / r) • E c + E c
          + (p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r) • E c := by
      intro c
      have := GlobalTheory.nat_mul_div_bounds_rounded_multiples p r (p ^ e * b c) hp hr
      have hk : p * (p ^ e * b c / r) + p
          = p ^ (e + 1) * b c / r + 1 + (p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r) := by
        rw [hm c]; omega
      rw [smul_add, ← mul_smul, ← add_smul]
      conv_lhs => rw [hk]
      rw [add_smul, add_smul, one_smul]
    have hs : p • (∑ c, (p ^ e * b c / r) • E c + ∑ c, E c)
        = ∑ c, (p ^ (e + 1) * b c / r) • E c + ∑ c, E c
          + ∑ c, (p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r) • E c := by
      rw [← Finset.sum_add_distrib, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun c _ => hc c)
    have hs' : p • (p ^ e • (M - Kc) - ∑ c, (p ^ e * b c / r) • E c - ∑ c, E c)
        = p ^ (e + 1) • (M - Kc) - p • (∑ c, (p ^ e * b c / r) • E c + ∑ c, E c) := by
      rw [pow_succ', mul_smul, smul_sub, smul_sub, smul_add]; abel
    beta_reduce
    rw [hs', hs]
    abel
end

