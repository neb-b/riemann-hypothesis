module

public import Mathlib
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGermEqGaugedFormalGroupLawExpIntegral

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CocycleIntegral
section
noncomputable section

open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

namespace GlobalTheory.GaugeCocycle

open MvPowerSeries

variable {C : Type} [Field C]

def valRing (V : VF C) : Subring C where
  carrier := {x | V.Ge 0 x}
  mul_mem' := fun ha hb => VF.Ge.mul_int ha hb
  one_mem' := VF.Ge.one
  add_mem' := fun ha hb => VF.Ge.add ha hb
  zero_mem' := VF.Ge.zero 0
  neg_mem' := fun ha => VF.Ge.neg ha

theorem intS_iff_ig (V : VF C) {σ : Type} (f : MvPowerSeries σ C) : IntS V f ↔ f ∈ Ig (valRing V) C σ := by
  constructor
  · intro hf
    let g : MvPowerSeries σ (valRing V) := fun n => ⟨coeff n f, hf n⟩
    refine RingHom.mem_range.2 ⟨g, ?_⟩
    ext n
    rw [coeff_map]
    rfl
  · intro hf n
    obtain ⟨g, rfl⟩ := RingHom.mem_range.1 hf
    rw [coeff_map]
    exact (coeff n g).2

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {d : ℕ}

omit [CharZero C] in
theorem map_self {σ : Type} (f : MvPowerSeries σ C) : MvPowerSeries.map (algebraMap C C) f = f := by
  ext n
  rw [coeff_map]
  rfl

end GlobalTheory.GaugeCocycle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenvectorOfGeneralizedEigenUnramifiedStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenvector_of_generalized_eigen_unramified : ∀ (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (κ : Type) [Fintype κ] [DecidableEq κ] (L : O →+* Matrix κ κ C), (∀ x i j, V.Ge 0 (L x i j)) → ∀ d : ℕ, 0 < d → ∀ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) → (∀ x : O, ∃ y, ε * (x ^ (V.l ^ d) - x) = (V.l : O) * y) → ∀ (ψ : O →+* C) (w : κ → C), (∀ x, V.Ge 0 (ψ x)) → (∀ x, ∃ k : ℕ, ((L x - ψ x • (1 : Matrix κ κ C)) ^ k).mulVec w = 0) → (∀ (N : ℕ) i, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (w i - (L (ε ^ (V.l ^ n))).mulVec w i)) → ∀ x, (L x).mulVec w = ψ x • w := by
  first | exact @GlobalTheory.GenEigen.eigen_of_gen_eigen | exact GlobalTheory.GenEigen.eigen_of_gen_eigen | (intros; apply GlobalTheory.GenEigen.eigen_of_gen_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralCharacterGeneralizedEigen
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.GenChar

theorem step {C : Type} [Field C] {O κ : Type} [Fintype κ] [DecidableEq κ]
    (n : O → Matrix κ κ C) (hc : ∀ x y, Commute (n x) (n y)) (w : κ → C) (hw : w ≠ 0)
    (hn : ∀ x, ∃ k : ℕ, ((n x) ^ k).mulVec w = 0) (x₀ : O) :
    ∃ u : κ → C, u ≠ 0 ∧ (∀ x, ∃ k : ℕ, ((n x) ^ k).mulVec u = 0) ∧ (n x₀).mulVec u = 0 ∧
      ∀ y, (n y).mulVec w = 0 → (n y).mulVec u = 0 := by
  classical
  have hk := Nat.find_spec (hn x₀)
  have hk0 : Nat.find (hn x₀) ≠ 0 := by
    intro h
    rw [h, pow_zero, Matrix.one_mulVec] at hk
    exact hw hk
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hlt : ¬ ((n x₀) ^ j).mulVec w = 0 := Nat.find_min (hn x₀) (by omega)
  have key : ∀ (y : O) (k : ℕ), ((n y) ^ k).mulVec w = 0 →
      ((n y) ^ k).mulVec (((n x₀) ^ j).mulVec w) = 0 := by
    intro y k h
    rw [Matrix.mulVec_mulVec, ((hc y x₀).pow_pow k j).eq, ← Matrix.mulVec_mulVec, h,
      Matrix.mulVec_zero]
  refine ⟨((n x₀) ^ j).mulVec w, hlt, fun x => ?_, ?_, fun y hy => ?_⟩
  · obtain ⟨k, h⟩ := hn x
    exact ⟨k, key x k h⟩
  · rw [Matrix.mulVec_mulVec, ← pow_succ']
    rw [hj] at hk
    exact hk
  · have := key y 1 (by rwa [pow_one])
    rwa [pow_one] at this

theorem ge_of_eigen {C : Type} [Field C] (V : VF C) {κ : Type} [Fintype κ]
    (A : Matrix κ κ C) (hA : ∀ i j, V.Ge 0 (A i j)) (c : C) (u : κ → C) (hu : u ≠ 0)
    (h : A.mulVec u = c • u) : V.Ge 0 c := by
  classical
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hu
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => V.v (u i))
    ⟨i₀, Finset.mem_univ _⟩
  have h0 : V.v (u i₀) ≠ ⊤ := by
    intro h
    exact hi₀ (by simpa using h)
  have h1 : V.v (u i) ≠ ⊤ := ne_top_of_le_ne_top h0 (hi i₀ (Finset.mem_univ _))
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp h1
  have h2 : V.Ge t (c * u i) := by
    have : c * u i = ∑ j, A i j * u j := by
      have := congrFun h i
      simpa [Matrix.mulVec, dotProduct] using this.symm
    rw [this]
    refine VF.Ge.sum fun j _ => (hA i j).mul_int ?_
    unfold VF.Ge
    rw [ht]
    exact hi j (Finset.mem_univ _)
  unfold VF.Ge at h2 ⊢
  rw [V.v.map_mul, ← ht] at h2
  induction hv : V.v c using WithTop.recTopCoe with
  | top => exact le_top
  | coe s =>
    rw [hv] at h2
    have h' : ((t : ℝ) : WithTop ℝ) ≤ ((s + t : ℝ) : WithTop ℝ) := by
      simpa [WithTop.coe_add] using h2
    have h'' : t ≤ s + t := by exact_mod_cast h'
    have : (0 : ℝ) ≤ s := by linarith
    exact_mod_cast this

theorem exists_character : ∀ (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (κ : Type) [Fintype κ] [DecidableEq κ] (L : O →+* Matrix κ κ C), (∀ x i j, V.Ge 0 (L x i j)) → ∀ (χ : O → C) (w : κ → C), w ≠ 0 → (∀ x, ∃ k : ℕ, ((L x - χ x • (1 : Matrix κ κ C)) ^ k).mulVec w = 0) → ∃ ψ : O →+* C, (∀ x, ψ x = χ x) ∧ ∀ x, V.Ge 0 (ψ x) := by
  intro C _ V O _ κ _ _ L hL χ w hw hn
  set n : O → Matrix κ κ C := fun x => L x - χ x • (1 : Matrix κ κ C) with hndef
  have hLc : ∀ x y, Commute (L x) (L y) := fun x y => (Commute.all x y).map L
  have hc : ∀ x y, Commute (n x) (n y) := fun x y =>
    ((hLc x y).sub_right ((Commute.one_right _).smul_right _)).sub_left
      ((Commute.one_left _).smul_left _)
  have heig : ∀ (x : O) (u : κ → C), (n x).mulVec u = 0 → (L x).mulVec u = χ x • u := by
    intro x u h
    simp only [hndef, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h
    exact sub_eq_zero.mp h
  have three : ∀ x y z : O, ∃ u : κ → C, u ≠ 0 ∧ (L x).mulVec u = χ x • u ∧
      (L y).mulVec u = χ y • u ∧ (L z).mulVec u = χ z • u := by
    intro x y z
    obtain ⟨u₁, h1, h1n, h1x, -⟩ := step n hc w hw hn x
    obtain ⟨u₂, h2, h2n, h2y, h2p⟩ := step n hc u₁ h1 h1n y
    obtain ⟨u₃, h3, -, h3z, h3p⟩ := step n hc u₂ h2 h2n z
    exact ⟨u₃, h3, heig _ _ (h3p _ (h2p _ h1x)), heig _ _ (h3p _ h2y), heig _ _ h3z⟩
  have h1 : χ 1 = 1 := by
    obtain ⟨u, hu, h, -, -⟩ := three 1 1 1
    rw [map_one, Matrix.one_mulVec] at h
    apply smul_left_injective C hu
    simpa using h.symm
  have h0 : χ 0 = 0 := by
    obtain ⟨u, hu, h, -, -⟩ := three 0 0 0
    rw [map_zero, Matrix.zero_mulVec] at h
    apply smul_left_injective C hu
    simpa using h.symm
  have hadd : ∀ x y, χ (x + y) = χ x + χ y := by
    intro x y
    obtain ⟨u, hu, hx, hy, h⟩ := three x y (x + y)
    rw [map_add (f := _), Matrix.add_mulVec, hx, hy, ← add_smul] at h
    exact smul_left_injective C hu h.symm
  have hmul : ∀ x y, χ (x * y) = χ x * χ y := by
    intro x y
    obtain ⟨u, hu, hx, hy, h⟩ := three x y (x * y)
    rw [map_mul, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_smul, hx, smul_smul, mul_comm (χ y)] at h
    exact smul_left_injective C hu h.symm
  refine ⟨⟨⟨⟨χ, h1⟩, hmul⟩, h0, hadd⟩, fun _ => rfl, fun x => ?_⟩
  obtain ⟨u, hu, h, -, -⟩ := three x x x
  exact ge_of_eigen V (L x) (hL x) (χ x) u hu h

end GlobalTheory.GenChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedCurveLogarithmsClosedUnderTadicLimits
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw

theorem coeff_alongCv_congr {C : Type} [Field C] {κ : Type} [Finite κ] {a b : κ → PowerSeries C}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) (hb : ∀ i, PowerSeries.constantCoeff (b i) = 0)
    (f : MvPowerSeries κ C) (m : ℕ)
    (h : ∀ i, ∀ k ≤ m, PowerSeries.coeff k (a i) = PowerSeries.coeff k (b i)) :
    PowerSeries.coeff m (alongCv a f) = PowerSeries.coeff m (alongCv b f) := by
  have hsa : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hsb : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
  have hq : ∀ i, Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ (m + 1)}) (a i) =
      Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ (m + 1)}) (b i) := by
    intro i
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
    intro k hk
    rw [map_sub, h i k (by omega), sub_self]
  have hp : ∀ e : κ →₀ ℕ, PowerSeries.coeff m (e.prod fun s n => a s ^ n) =
      PowerSeries.coeff m (e.prod fun s n => b s ^ n) := by
    intro e
    have h1 : Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ (m + 1)}) (e.prod fun s n => a s ^ n) =
        Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ (m + 1)}) (e.prod fun s n => b s ^ n) := by
      simp only [Finsupp.prod, map_prod, map_pow, hq]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at h1
    have h2 := h1 m (by omega)
    rwa [map_sub, sub_eq_zero] at h2
  show MvPowerSeries.coeff (Finsupp.single () m) (MvPowerSeries.subst a f) =
    MvPowerSeries.coeff (Finsupp.single () m) (MvPowerSeries.subst b f)
  rw [MvPowerSeries.coeff_subst hsa, MvPowerSeries.coeff_subst hsb]
  refine finsum_congr fun e => ?_
  exact congrArg (fun z => MvPowerSeries.coeff e f • z) (hp e)

theorem exists_forall_le_of_eventually {P : ℕ → ℕ → Prop} (h : ∀ m, ∃ n0, ∀ n ≥ n0, P m n) (m : ℕ) :
    ∃ n, ∀ k ≤ m, P k n := by
  choose N hN using h
  refine ⟨(Finset.range (m + 1)).sup N, fun k hk => hN k _ ?_⟩
  exact Finset.le_sup (f := N) (Finset.mem_range.2 (by omega))

theorem cv_closed_under_limits : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g (a : ℕ → ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) (b : ((κ → PowerSeries C) × (JJ I g → PowerSeries C))), (∀ n, a n ∈ Cv X V g) → (∀ m, ∃ n0, ∀ n ≥ n0, (∀ i, PowerSeries.coeff m ((a n).1 i) = PowerSeries.coeff m (b.1 i)) ∧ ∀ q, PowerSeries.coeff m ((a n).2 q) = PowerSeries.coeff m (b.2 q)) → b ∈ Cv X V g := by
  intro C _ V d _ I _ κ _ X hR g a b ha hlim
  choose γ lam hγ hlam hlg hsg using ha
  have hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := by
    intro i
    have := hR.lin i 0 (by simp)
    simpa using this
  have hslg : MvPowerSeries.HasSubst X.lg := MvPowerSeries.hasSubst_of_constantCoeff_zero hlg0
  have hsex : MvPowerSeries.HasSubst X.ex := MvPowerSeries.hasSubst_of_constantCoeff_zero hR.exc
  have hsγ : ∀ n, MvPowerSeries.HasSubst (γ n) := fun n =>
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => (hγ n i).1
  have ha0 : ∀ n i, PowerSeries.constantCoeff ((a n).1 i) = 0 := by
    intro n i
    rw [← hlg n i]
    exact MvPowerSeries.constantCoeff_subst_eq_zero (hsγ n) (fun i => (hγ n i).1) (hlg0 i)
  have hb0 : ∀ i, PowerSeries.constantCoeff (b.1 i) = 0 := by
    intro i
    obtain ⟨n, hn⟩ := hlim 0
    have := (hn n le_rfl).1 i
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
    rw [← this, ha0]
  have hsb : MvPowerSeries.HasSubst b.1 := MvPowerSeries.hasSubst_of_constantCoeff_zero hb0
  have hγeq : ∀ n i, γ n i = alongCv (a n).1 (X.ex i) := by
    intro n i
    have h1 : (a n).1 = fun j => MvPowerSeries.subst (γ n) (X.lg j) := funext fun j => (hlg n j).symm
    rw [h1]
    show γ n i = MvPowerSeries.subst (fun j => MvPowerSeries.subst (γ n) (X.lg j)) (X.ex i)
    rw [← MvPowerSeries.subst_comp_subst_apply hslg (hsγ n), hR.exlg, MvPowerSeries.subst_X (hsγ n)]
  let Γ : κ → PowerSeries C := fun i => alongCv b.1 (X.ex i)
  have hΓ0 : ∀ i, PowerSeries.constantCoeff (Γ i) = 0 := fun i =>
    MvPowerSeries.constantCoeff_subst_eq_zero hsb hb0 (hR.exc i)
  have key : ∀ m, ∃ n, (∀ i, ∀ k ≤ m, PowerSeries.coeff k (γ n i) = PowerSeries.coeff k (Γ i)) ∧
      ∀ q, PowerSeries.coeff m (lam n q) = PowerSeries.coeff m (b.2 q + alongCv Γ (X.sg (X.u (1 - g) q))) := by
    intro m
    obtain ⟨n, hn⟩ := exists_forall_le_of_eventually hlim m
    have h1 : ∀ i, ∀ k ≤ m, PowerSeries.coeff k (γ n i) = PowerSeries.coeff k (Γ i) := by
      intro i k hk
      rw [hγeq]
      exact coeff_alongCv_congr (ha0 n) hb0 _ k fun j k' hk' => (hn k' (hk'.trans hk)).1 j
    refine ⟨n, h1, fun q => ?_⟩
    rw [map_add (f := _), ← (hn m le_rfl).2 q, hsg n q, map_sub,
      coeff_alongCv_congr (fun i => (hγ n i).1) hΓ0 _ m h1, sub_add_cancel]
  refine ⟨Γ, fun q => b.2 q + alongCv Γ (X.sg (X.u (1 - g) q)), fun i => ⟨hΓ0 i, fun m => ?_⟩,
    fun q => ⟨?_, fun m => ?_⟩, fun i => ?_, fun q => by simp⟩
  · obtain ⟨n, hn, -⟩ := key m
    rw [← hn i m le_rfl]
    exact (hγ n i).2 m
  · obtain ⟨n, -, hn⟩ := key 0
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← hn q, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (hlam n q).1
  · obtain ⟨n, -, hn⟩ := key m
    rw [← hn q]
    exact (hlam n q).2 m
  · show MvPowerSeries.subst (fun j => MvPowerSeries.subst b.1 (X.ex j)) (X.lg i) = b.1 i
    rw [← MvPowerSeries.subst_comp_subst_apply hsex hsb, hR.lgex, MvPowerSeries.subst_X hsb]

end GlobalTheory.RowLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGermsIndependentOfCurveSystem
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw

theorem intGerm_indep_of_rlaw : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type)
    [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V →
    ∀ H : ∀ g, X.CartHyp V g, RawChart.IntegralGermIndependentOfSystem H := by
  intro C _ V d _ I _ κ _ X hX H S S₂ t t₂ ht ht₂
  rw [_root_.GlobalTheory.RowLaw.intGerm_eq_expInt C V d I κ X hX H S t ht, _root_.GlobalTheory.RowLaw.intGerm_eq_expInt C V d I κ X hX H S₂ t₂ ht₂]

end GlobalTheory.RowLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MemCvOfSubstXPow
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw

theorem isCv_of_subst_X_pow {C : Type} [Field C] (V : VF C) {σ : Type} {m : ℕ} (hm : 0 < m)
    (δ γ : σ → PowerSeries C) (hγ : IsCv V γ)
    (h : ∀ i, PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (δ i) = γ i) : IsCv V δ := by
  intro i
  have hc : ∀ n, PowerSeries.coeff n (δ i) = PowerSeries.coeff (m * n) (γ i) := by
    intro n
    rw [← h i, Formalism.L2.FormalSeriesBounds.coeff_subst_X_pow hm]
  refine ⟨?_, fun n => ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hc, mul_zero,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (hγ i).1
  · rw [hc]
    exact (hγ i).2 _

theorem cvRoot_alongCv_comp {C : Type} [Field C] {σ τ : Type} [Finite σ] [Finite τ] {γ : τ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) {f : σ → MvPowerSeries τ C}
    (hf : ∀ i, MvPowerSeries.constantCoeff (f i) = 0) (F : MvPowerSeries σ C) :
    alongCv (fun i => alongCv γ (f i)) F = alongCv γ (MvPowerSeries.subst f F) := by
  unfold alongCv
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hf)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ)]

theorem cvRoot_alongCv_X {C : Type} [Field C] {τ : Type} [Finite τ] {γ : τ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (i : τ) :
    alongCv γ (MvPowerSeries.X i : MvPowerSeries τ C) = γ i := by
  unfold alongCv
  exact MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ) i

theorem mem_Cv_of_subst_X_pow : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g (m : ℕ), 0 < m → ∀ a : ((κ → PowerSeries C) × (JJ I g → PowerSeries C)), ((fun i => PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (a.1 i), fun q => PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (a.2 q)) : ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) ∈ Cv X V g → a ∈ Cv X V g := by
  intro C _ V d _ I _ κ _ X H g m hm a ha
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := ha
  have hγ0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0 := fun i => (hγ i).1
  have hτ : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries C) ^ m) = 0 := by simp [hm.ne']
  have hS := PowerSeries.HasSubst.of_constantCoeff_zero' hτ
  have hlg : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := by
    intro i
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, H.lin i 0 (by simp)]
    simp
  have h1' : ∀ i, alongCv γ (X.lg i) = PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (a.1 i) := h1
  have h2' : ∀ q, PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (a.2 q) =
      lam q - alongCv γ (X.sg (X.u (1 - g) q)) := h2
  have ha0 : ∀ i, PowerSeries.constantCoeff (a.1 i) = 0 := by
    intro i
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← Formalism.L2.FormalSeriesBounds.coeff_subst_X_pow hm, ← h1' i, mul_zero,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact Formalism.L2.FormalSeriesBounds.constantCoeff_subst_zero (τ := Unit) hγ0 (hlg i)
  have hsub : ∀ i, PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (alongCv a.1 (X.ex i)) = γ i := by
    intro i
    rw [← alongCv_repar ha0 hτ]
    have : (fun i => PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (a.1 i)) =
        fun i => alongCv γ (X.lg i) := funext fun i => (h1' i).symm
    rw [this, cvRoot_alongCv_comp hγ0 hlg, H.exlg, cvRoot_alongCv_X hγ0]
  have hcv : IsCv V (fun i => alongCv a.1 (X.ex i)) := isCv_of_subst_X_pow V hm _ γ hγ hsub
  refine ⟨fun i => alongCv a.1 (X.ex i),
    fun q => a.2 q + alongCv (fun i => alongCv a.1 (X.ex i)) (X.sg (X.u (1 - g) q)), hcv,
    isCv_of_subst_X_pow V hm _ lam hlam ?_, ?_, ?_⟩
  · intro q
    rw [PowerSeries.subst_add hS, h2', ← alongCv_repar (fun i => (hcv i).1) hτ, funext hsub, sub_add_cancel]
  · intro i
    rw [cvRoot_alongCv_comp ha0 H.exc, H.lgex, cvRoot_alongCv_X ha0]
  · intro q
    simp

end GlobalTheory.RowLaw
end

