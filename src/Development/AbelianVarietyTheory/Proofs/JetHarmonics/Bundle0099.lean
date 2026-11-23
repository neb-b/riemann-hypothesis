module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0095
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorMomentTransfer

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsImagQuadOrderPairAndEvenTheta
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

noncomputable section

namespace GlobalTheory.MomOne.ThetaZero

theorem indep {d : ℕ} (hd : 0 < d) : LinearIndependent ℝ ![(1 : ℂ), wK d] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [wK] at him hre
  have ht : t = 0 := by
    rcases him with h1 | h1
    · exact h1
    · exact absurd h1 (by positivity)
  subst ht
  simp at hre
  exact ⟨hre, rfl⟩

def pair {d : ℕ} (hd : 0 < d) : PeriodPair := ⟨1, wK d, indep hd⟩

theorem isOK_pair {d : ℕ} (hd : 0 < d) : IsOK d (pair hd) := by
  intro z
  rw [PeriodPair.mem_lattice]
  simp only [pair, mul_one, InOK]
  exact ⟨fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩, fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩⟩

theorem G_eq {d : ℕ} {L : PeriodPair} (h : IsOK d L) {k : ℕ} (hk : k ≠ 0) :
    L.G (2 * k) = eis d k := by
  unfold PeriodPair.G eis
  have e1 := tsum_subtype (L.lattice : Set ℂ) (fun w : ℂ => (w ^ (2 * k))⁻¹)
  have e2 := tsum_subtype {w : ℂ | InOK d w ∧ w ≠ 0} (fun w : ℂ => 1 / w ^ (2 * k))
  refine e1.trans (Eq.trans ?_ e2.symm)
  refine tsum_congr fun w => ?_
  by_cases h0 : w = 0
  · subst h0
    simp [Set.indicator, hk]
  · have hw : w ∈ (L.lattice : Set ℂ) ↔ w ∈ {w : ℂ | InOK d w ∧ w ≠ 0} :=
      ⟨fun a => ⟨(h w).1 a, h0⟩, fun a => (h w).2 a.1⟩
    by_cases hm : w ∈ (L.lattice : Set ℂ)
    · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hw.1 hm), one_div]
    · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (hw.not.1 hm)]

def lam (d : ℕ) : AddSubgroup ℂ := AddSubgroup.closure {1, wK d}

theorem mem_lam (d : ℕ) (z : ℂ) : z ∈ lam d ↔ InOK d z := by
  rw [lam, AddSubgroup.mem_closure_pair]
  simp only [zsmul_eq_mul, mul_one, InOK]
  exact ⟨fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩, fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩⟩

theorem area_lam {d : ℕ} (hd : 0 < d) : Formalism.MainNotions.TaylorLogMetric.area (lam d) = Real.sqrt d / 2 := by
  rw [lam, GlobalTheory.TransInv.area_closure_pair (indep hd)]
  simp [wK, abs_div]

theorem thetaTranslationOperator_apply {d : ℕ} (hd : 0 < d) (x : ℂ) (F : ℂ → ℂ) (z : ℂ) :
    Formalism.MainNotions.TaylorLogMetric.U1 (lam d) x F z = U1 d x F z := by
  simp only [Formalism.MainNotions.TaylorLogMetric.U1, U1, h1, area_lam hd]
  congr 2
  push_cast
  ring

theorem thetaTranslation_comp_eq_cocycle_mul (d : ℕ) (a b : ℂ) (F : ℂ → ℂ) (z : ℂ) :
    U1 d a (U1 d b F) z =
      Complex.exp ((Real.pi : ℂ) / 2 * (h1 d b a - h1 d a b)) * U1 d (a + b) F z := by
  simp only [U1]
  rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, add_assoc z a b]
  congr 2
  simp only [h1, map_add (f := _)]
  ring

theorem half_not_mem {d : ℕ} (hd : 0 < d) (u v : ℤ) (h : ¬ (Odd u ∧ Even v)) :
    ((u : ℂ) + (v : ℂ) * wK d) / 2 + 1 / 2 ∉ lam d := by
  rw [mem_lam]
  rintro ⟨m, n, e⟩
  have := (LinearIndependent.pair_iff.1 (indep hd)) ((u + 1 - 2 * m : ℤ) : ℝ) ((v - 2 * n : ℤ) : ℝ) (by
    simp only [Complex.real_smul]
    push_cast
    linear_combination 2 * e)
  have h1 : u + 1 - 2 * m = 0 := by exact_mod_cast this.1
  have h2 : v - 2 * n = 0 := by exact_mod_cast this.2
  exact h ⟨⟨m - 1, by omega⟩, ⟨n, by omega⟩⟩

theorem normSq_eq {d : ℕ} (c : ℤ) (hc : (d : ℤ) + 1 = 8 * c) (u v : ℤ) :
    Complex.normSq ((u : ℂ) + (v : ℂ) * wK d) = ((u ^ 2 + u * v + 2 * c * v ^ 2 : ℤ) : ℝ) := by
  have hs : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  have hc' : (d : ℝ) + 1 = 8 * c := by exact_mod_cast hc
  simp [Complex.normSq_apply, wK]
  linear_combination (v : ℝ) ^ 2 / 4 * hs + (v : ℝ) ^ 2 / 4 * hc'

theorem exp_even {n : ℤ} (h : Even n) : Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ)) = 1 := by
  obtain ⟨k, rfl⟩ := h
  rw [← Complex.exp_int_mul_two_pi_mul_I k]
  congr 1
  push_cast
  ring

theorem comm_eq {d : ℕ} (hd : 0 < d) (u v : ℤ) :
    h1 d (wK d) ((u : ℂ) + (v : ℂ) * wK d) - h1 d ((u : ℂ) + (v : ℂ) * wK d) (wK d) =
      2 * u * Complex.I := by
  have hs : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  simp only [h1, wK, map_add (f := _), map_mul, map_div₀, map_intCast, map_one, Complex.conj_I,
    Complex.conj_ofReal, map_ofNat]
  push_cast
  field_simp
  ring

theorem exists_isTh {d : ℕ} (hd8 : d % 8 = 7) : ∃ θ : ℂ → ℂ, IsTh d θ := by
  have hd : 0 < d := by omega
  obtain ⟨c, hc⟩ : ∃ c : ℤ, (d : ℤ) + 1 = 8 * c := ⟨((d : ℤ) + 1) / 8, by omega⟩
  have hlat : GlobalTheory.EvenTheta.IsLat (lam d) := ⟨1, wK d, indep hd, rfl⟩
  have ht : (1 / 2 : ℂ) ∉ lam d := by
    simpa using half_not_mem hd 0 0 (by simp)
  have ht2 : 2 * (1 / 2 : ℂ) ∈ lam d := (mem_lam d _).2 ⟨1, 0, by simp⟩
  obtain ⟨b1, b2, b3, -, b5, b6⟩ := GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties (lam d) hlat (1 / 2) ht ht2
  generalize Formalism.MainNotions.GL3Theta.th0 (lam d) (1 / 2) = θ at b1 b2 b3 b5 b6
  have fix : ∀ u v : ℤ, ¬ (Odd u ∧ Even v) → U1 d ((u : ℂ) + (v : ℂ) * wK d) θ = θ := by
    intro u v h
    funext z
    rw [← thetaTranslationOperator_apply hd]
    exact b6 _ ((mem_lam d _).2 ⟨u, v, rfl⟩) (half_not_mem hd u v h) z
  refine ⟨θ, b1, b2, b3, ?_, fun z hz => ?_⟩
  · rintro x ⟨u, v, rfl⟩
    funext z
    simp only [W1]
    rw [normSq_eq c hc, Complex.ofReal_intCast]
    by_cases h : Odd u ∧ Even v
    · have f1 := fix u (v - 1) (by
        rintro ⟨-, h2⟩
        rcases h2 with ⟨a, ha⟩
        rcases h.2 with ⟨b, hb⟩
        omega)
      have f2 : U1 d (wK d) θ = θ := by simpa using fix 0 1 (by simp)
      have k := thetaTranslation_comp_eq_cocycle_mul d ((u : ℂ) + ((v - 1 : ℤ) : ℂ) * wK d) (wK d) θ z
      rw [f2, f1, comm_eq hd,
        show (u : ℂ) + ((v - 1 : ℤ) : ℂ) * wK d + wK d = (u : ℂ) + (v : ℂ) * wK d by
          push_cast; ring] at k
      have hev : Even (u ^ 2 + u * v + 2 * c * v ^ 2 - u) := by
        obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := h
        exact ⟨(2 * a + 1) * a + (2 * a + 1) * b + c * (b + b) ^ 2, by ring⟩
      have e := exp_even hev
      rw [k]
      congr 1
      rw [← one_mul (Complex.exp ((Real.pi : ℂ) / 2 * _)), ← e, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    · have hev : Even (u ^ 2 + u * v + 2 * c * v ^ 2) := by
        rcases Int.even_or_odd u with ⟨a, rfl⟩ | ⟨a, rfl⟩
        · exact ⟨2 * a ^ 2 + a * v + c * v ^ 2, by ring⟩
        · rcases Int.even_or_odd v with hv | ⟨b, rfl⟩
          · exact absurd ⟨⟨a, rfl⟩, hv⟩ h
          · exact ⟨(2 * a + 1) * (a + b + 1) + c * (2 * b + 1) ^ 2, by ring⟩
      rw [exp_even hev, one_mul, fix u v h]
  · obtain ⟨m, n, e⟩ := (mem_lam d _).1 ((b5 z).1 hz)
    exact ⟨m - 1, n, by push_cast; linear_combination e⟩

end GlobalTheory.MomOne.ThetaZero

namespace GlobalTheory.MomOne

theorem exists_pair_and_isTh : ∀ d : ℕ, d.Prime → d % 16 = 7 → (∃ L : PeriodPair, IsOK d L ∧ L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = discr d) ∧ ∃ θ : ℂ → ℂ, IsTh d θ := by
  intro d hp h
  refine ⟨⟨ThetaZero.pair hp.pos, ThetaZero.isOK_pair hp.pos, ?_⟩, ThetaZero.exists_isTh (by omega)⟩
  have h2 := ThetaZero.G_eq (ThetaZero.isOK_pair hp.pos) (k := 2) (by norm_num)
  have h3 := ThetaZero.G_eq (ThetaZero.isOK_pair hp.pos) (k := 3) (by norm_num)
  unfold discr PeriodPair.g₂ PeriodPair.g₃
  rw [← h2, ← h3]

end GlobalTheory.MomOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralExpansionsOfValuationGe
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace IntComb

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)}

theorem exists_int_of_vge (hϖ : Irreducible ϖ) {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k))} {r : ℚ}
    (hr : 0 ≤ r) (hs : VGe D (FractionRing V) (FamInt.ordVal hϖ) k α s r) :
    ∃ f : D.toPre.SecB k α,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) s
        (D.toPre.famφB α) (DegPre.famε k) f (DegPre.prB D.toPre (FractionRing V)).left 1 := by
  obtain ⟨n, a, σ, σF, hσ, hva, hsum⟩ := hs
  have hint : ∀ i, ∃ b : V, a i = algebraMap V (FractionRing V) b := fun i => by
    obtain ⟨b, hb⟩ := (FamInt.le_ordFn_iff hϖ (a i) 0).1 (le_trans (by exact_mod_cast hr) (hva i))
    exact ⟨b, by rw [hb, zpow_zero, _root_.one_mul]⟩
  choose b hb using hint
  refine ⟨FamInt.secLin (fun i => scal D.toPre.P.A.hom (b i)) σ,
    SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ => ?_⟩
  rw [SectionScalarValuation.sval_lin (fun i => scal D.toPre.P.A.hom (b i)) σ (fun _ => rfl) _ y hJ,
    SectionScalarValuation.sval_lin (fun i => gF D.toPre (FractionRing V) (a i)) σF (fun j => hsum j) (𝟙 _) y hJ]
  refine Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ?_ (SectionScalarValuation.secScal_sval (hσ i) _ y hJ)
  have e1 : gs (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y ⊤ (scal D.toPre.P.A.hom (b i)) =
      cst ((𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) ≫ D.toPre.P.A.hom) y (b i) :=
    gs_pull _ _ y ⊤ trivial _
  have e2 : gs (𝟙 _) y ⊤ (gF D.toPre (FractionRing V) (a i)) =
      cst (𝟙 _ ≫ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left) y (a i) :=
    gs_pull _ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left y ⊤ trivial _
  have e3 : (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) ≫ D.toPre.P.A.hom =
      ((𝟙 _ ≫ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left) ≫
        spMap (algebraMap (FractionRing V) (FractionRing V))) ≫ spMap (algebraMap V (FractionRing V)) := by
    rw [Category.id_comp, Category.id_comp, Category.assoc, Over.w]
    exact (Over.w (fst (TF (R := V) (FractionRing V)) D.toPre.P.A)).symm
  rw [e1, e2, e3, cst_comp, cst_comp, hb i]
  rfl

theorem integralFamily_of_min (hL : Laws) (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    {q : ℕ} (hq : 1 ≤ q) (χ : D.toPre.X) (β : D.toPre.SecB q χ) (hmin : ∀ z, Q χ ≤ Q (χ + q • z)) :
    ∃ (Φ : Fam D.toPre (FractionRing V) q) (f : ∀ α, D.toPre.SecB q α),
      (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε q) (Φ.s α)
        (D.toPre.famφB α) (DegPre.famε q) (f α) (DegPre.prB D.toPre (FractionRing V)).left 1) ∧
      f χ = β ∧ ∀ α, (∀ z, α ≠ χ + q • z) → ∀ j, (f α).f j = 0 := by
  classical
  obtain ⟨σ, hσ⟩ := FamInt.exists_pull (F := FractionRing V) β
  obtain ⟨Φ, hΦ, hΦ0⟩ := UUA.exists_fam_rep (F := FractionRing V) hL.globalFns D.tau_bimult q χ (fun a b h => by
    have h' : (q : ℤ) • a = (q : ℤ) • b := by
      rw [natCast_zsmul, natCast_zsmul]; exact add_left_cancel h
    exact smul_right_injective D.toPre.X (by omega : (q : ℤ) ≠ 0) h') σ
  have h0 : VGe D (FractionRing V) (FamInt.ordVal hϖ) q χ (Φ.s χ) 0 := by
    refine ⟨1, fun _ => 1, fun _ => β, fun _ => Φ.s χ, fun _ => hΦ ▸ hσ, fun _ => ?_, fun j => ?_⟩
    · simp
    · simp [DegPre.constBF]
  have key : ∀ α : D.toPre.X, ∃ f : D.toPre.SecB q α,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε q) (Φ.s α)
        (D.toPre.famφB α) (DegPre.famε q) f (DegPre.prB D.toPre (FractionRing V)).left 1 ∧
      (∀ h : χ = α, f = h ▸ β) ∧ ((∀ z, α ≠ χ + q • z) → ∀ j, f.f j = 0) := by
    intro α
    by_cases hα : χ = α
    · subst hα
      exact ⟨β, hΦ ▸ hσ, fun _ => rfl, fun h => absurd (by simp) (h 0)⟩
    by_cases hc : ∃ z, α = χ + q • z
    · obtain ⟨z, rfl⟩ := hc
      have H := SectionScalarValuation.fe_move hϖ hQ (FamInt.valOver_ordVal hϖ) q z χ Φ h0
      have hle := hmin z
      rw [q_shift hϖ hQ, le_add_iff_nonneg_right] at hle
      have hpos : (0 : ℤ) ≤ q * Q z + QForm.bOf D.toPre Q z χ :=
        nonneg_of_mul_nonneg_right hle (by omega)
      obtain ⟨f, h1⟩ := exists_int_of_vge hϖ (by rw [zero_add]; exact_mod_cast hpos) H
      exact ⟨f, h1, fun h => absurd h hα, fun h => absurd rfl (h z)⟩
    · refine ⟨SecOps.secZero, SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ => ?_, fun h => absurd h hα,
        fun _ _ => rfl⟩
      rw [UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _),
        UUA.sval_zero_of (hΦ0 α fun mu e => hc ⟨mu, e.symm⟩) _ y J (hJ.mem _ _)]
  choose f h1 h2 h3 using key
  exact ⟨Φ, f, h1, h2 χ rfl, h3⟩

theorem exists_min_reps (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    {q : ℕ} (hq : 1 ≤ q) : ∃ (N : ℕ) (χ : Fin N → D.toPre.X), (∀ α, ∃ i m, α = χ i + q • m) ∧
      (∀ i i', i' ≠ i → ∀ z, χ i ≠ χ i' + q • z) ∧ ∀ i z, Q (χ i) ≤ Q (χ i + q • z) := by
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul D.toPre.X q hq
  have hnn : ∀ x, 0 ≤ Q x := fun x => by
    by_cases hx : x = 0
    · rw [hx, QForm.Q_zero hϖ D hQ]
    · exact le_trans zero_le_one (QForm.Q_pos hϖ D hQ hx)
  have hm : ∀ i, ∃ m : D.toPre.X, ∀ z, Q (e i + q • m) ≤ Q (e i + q • z) := fun i => by
    refine ⟨Function.argmin (fun z : D.toPre.X => (Q (e i + q • z)).toNat), fun z => ?_⟩
    have h := Function.argmin_le (fun z : D.toPre.X => (Q (e i + q • z)).toNat) z
    have h1 := hnn (e i + q • z)
    omega
  choose m hm using hm
  refine ⟨_, fun i => e i + q • m i, fun α => ?_, fun i i' hi z h => hi ?_, fun i z => ?_⟩
  · obtain ⟨i, ⟨z, hz⟩, -⟩ := he α
    exact ⟨i, z - m i, by rw [hz, smul_sub, add_assoc, add_sub_cancel]⟩
  · exact (he (e i + q • m i)).unique ⟨m i' + z, by rw [smul_add, ← add_assoc]; exact h⟩ ⟨m i, rfl⟩
  · have := hm i (m i + z)
    rwa [smul_add, ← add_assoc] at this

variable {F : Type} [Field F] [Algebra (FractionRing V) F] {k : ℕ}

theorem sum_f {n : ℕ} (S : Finset (Fin n)) (t : Fin n → Fam D.toPre F k) (α : D.toPre.X) (j) :
    ((∑ i ∈ S, t i).s α).f j = ∑ i ∈ S, ((t i).s α).f j := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, zero_f]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_f, ih]

theorem sval_comb {n : ℕ} (c : Fin n → F) (t : Fin n → Fam D.toPre F k) (α : D.toPre.X) {Z : Scheme.{0}}
    (r : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) {J} (hJ : Good D.toPre.P.L z J) :
    sval ((∑ i, c i • t i).s α) r z J =
      ∑ i, gs r z ⊤ (scal (fst (TF (R := V) F) D.toPre.P.A).left (c i)) * sval ((t i).s α) r z J :=
  SectionScalarValuation.sval_lin (fun i => gF D.toPre F (c i)) (fun i => (t i).s α) (fun j => sum_f _ _ α j) r z hJ

end IntComb

theorem exists_integral_expansions_of_vge : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (q : ℕ), 1 ≤ q → ∀ (s : Fam D.toPre F q) (r : ℚ), (∀ χ, VGe D F v q χ (s.s χ) r) → ∃ (l : ℕ) (c : Fin l → F) (σ : Fin l → H0 U.LG.L q) (f : Fin l → ∀ α, D.toPre.SecB q α), (∀ i, ((r : ℚ) : WithTop ℚ) ≤ v (c i)) ∧ (∀ i e, U.ExpandsAt e q (σ i) (f i)) ∧ ∀ α : D.toPre.X, GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε q) (s.s α) (D.toPre.famφB α) (DegPre.famε q) (fun i => f i α) (DegPre.prB D.toPre F).left (fun i => scal (fst (TF (R := V) F) D.toPre.P.A).left (c i)) := by
  intro hL V _ _ _ ϖ hϖ D A G _ _ U Q hQ F _ _ v _ q hq s r hs
  classical
  obtain ⟨N, χ, hrep, hdis, hmin⟩ := IntComb.exists_min_reps hϖ hQ hq
  choose n a β βF hβ hva hsum using fun i => hs (χ i)
  choose Φ f hf hfβ hf0 using fun p : (Σ i : Fin N, Fin (n i)) =>
    IntComb.integralFamily_of_min hL hϖ hQ hq (χ p.1) (β p.1 p.2) (hmin p.1)
  choose σ hσ using fun p => IntegralExpansion.main hL V D A G U q hq (Φ p) (f p) (hf p)
  choose θ hθ using fun p => _root_.GlobalTheory.FamBaseChange.main hL.globalFns V _ D q (Φ p) (f p) (hf p) F
  let E := (Fintype.equivFin (Σ i : Fin N, Fin (n i))).symm
  have hst : s = ∑ x, a (E x).1 (E x).2 • θ (E x) := by
    refine fam_ext fun α => ?_
    obtain ⟨i, m, rfl⟩ := hrep α
    refine fam_eq_on_class_of_eq hL.globalFns V D.toPre F q _ _ (χ i) ?_ m
    refine sec_ext_val D.toPre.P.isLB fun y J hJ => ?_
    rw [IntComb.sval_comb _ _ _ _ _ hJ,
      SectionScalarValuation.sval_lin (fun x => gF D.toPre F (a i x)) (βF i) (fun j => hsum i j) (𝟙 _) y hJ,
      E.sum_comp (fun p => gs (𝟙 _) y ⊤ (scal (fst (TF (R := V) F) D.toPre.P.A).left (a p.1 p.2)) *
        sval ((θ p).s (χ i)) (𝟙 _) y J), Fintype.sum_sigma, Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl fun x _ => congrArg₂ (· * ·) rfl ?_
      rw [← SectionScalarValuation.secScal_sval (hβ i x) _ y hJ, ← SectionScalarValuation.secScal_sval (hθ ⟨i, x⟩ (χ i)) _ y hJ, hfβ ⟨i, x⟩]
    · refine fun i' _ hi => Finset.sum_eq_zero fun x _ => ?_
      rw [← SectionScalarValuation.secScal_sval (hθ ⟨i', x⟩ (χ i)) _ y hJ,
        UUA.sval_zero_of (hf0 ⟨i', x⟩ (χ i) (hdis i i' hi)) _ y J (hJ.mem _ _), mul_zero]
    · exact fun h => absurd (Finset.mem_univ i) h
  refine ⟨_, fun x => a (E x).1 (E x).2, fun x => σ (E x), fun x => f (E x), fun x => hva _ _,
    fun x e => hσ _ e, fun α => ?_⟩
  refine (FieldBaseChange.secLin_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_
  rw [hst, IntComb.sval_comb _ _ _ _ _ hJ]
  exact Finset.sum_congr rfl fun x _ => by rw [SectionScalarValuation.secScal_sval (hθ _ α) _ _ hJ]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupCayleyBound
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.RatioMoment

theorem iterate_bound {X M ι : Type} [MeasurableSpace X] [NormedAddCommGroup M] [Fintype ι] (μ : Measure X)
    (κ : X → ℝ) (f : M → X → ℝ) (T : ι → ι → M → M) (L : ℕ → M → Prop) (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hκ : AEMeasurable κ μ) (hf : ∀ w, AEMeasurable (f w) μ) (hf0 : ∀ w x, 0 ≤ f w x)
    (hpt : ∀ᵐ x ∂μ, ∀ w, κ x ^ 2 * f w x ≤ ∑ c, ∑ e, f (T c e w) x)
    (hL : ∀ j w, L j w → ∀ c e, L (j + 2) (T c e w))
    (hs : ∀ j w, j ≤ N → L j w → ∑ c, ∑ e, ‖T c e w‖ ^ 2 ≤ B ^ 2 * ‖w‖ ^ 2)
    (h0 : ∀ w, ∫⁻ x, ENNReal.ofReal (1 * f w x) ∂μ ≤ ENNReal.ofReal (‖w‖ ^ 2)) :
    ∀ q j, j + 2 * q ≤ N → ∀ w, L j w →
      ∫⁻ x, ENNReal.ofReal (κ x ^ (2 * q) * f w x) ∂μ ≤ ENNReal.ofReal (B ^ (2 * q) * ‖w‖ ^ 2) := by
  intro q
  induction q with
  | zero => intro j _ w _; simpa using h0 w
  | succ q ih =>
    intro j hj w hw
    have hk0 : ∀ x, 0 ≤ κ x ^ (2 * q) := fun x => by rw [pow_mul]; positivity
    have hm : ∀ v, AEMeasurable (fun x => ENNReal.ofReal (κ x ^ (2 * q) * f v x)) μ := fun v =>
      ((hκ.pow_const _).mul (hf v)).ennreal_ofReal
    calc ∫⁻ x, ENNReal.ofReal (κ x ^ (2 * (q + 1)) * f w x) ∂μ
        ≤ ∫⁻ x, ∑ c, ∑ e, ENNReal.ofReal (κ x ^ (2 * q) * f (T c e w) x) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hpt] with x hx
          have h1 : κ x ^ (2 * (q + 1)) * f w x ≤ ∑ c, ∑ e, κ x ^ (2 * q) * f (T c e w) x := by
            have := mul_le_mul_of_nonneg_left (hx w) (hk0 x)
            simp only [Finset.mul_sum] at this
            calc κ x ^ (2 * (q + 1)) * f w x = κ x ^ (2 * q) * (κ x ^ 2 * f w x) := by ring
              _ ≤ _ := this
          refine (ENNReal.ofReal_le_ofReal h1).trans (le_of_eq ?_)
          rw [ENNReal.ofReal_sum_of_nonneg
            (fun c _ => Finset.sum_nonneg fun e _ => mul_nonneg (hk0 x) (hf0 _ x))]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg (fun e _ => mul_nonneg (hk0 x) (hf0 _ x))]
      _ = ∑ c, ∑ e, ∫⁻ x, ENNReal.ofReal (κ x ^ (2 * q) * f (T c e w) x) ∂μ := by
          rw [lintegral_finsetSum' _ (fun c _ => Finset.aemeasurable_fun_sum _ fun e _ => hm _)]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [lintegral_finsetSum' _ (fun e _ => hm _)]
      _ ≤ ∑ c, ∑ e, ENNReal.ofReal (B ^ (2 * q) * ‖T c e w‖ ^ 2) :=
          Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun e _ =>
            ih (j + 2) (by omega) _ (hL j w hw c e)
      _ = ENNReal.ofReal (∑ c, ∑ e, B ^ (2 * q) * ‖T c e w‖ ^ 2) := by
          rw [ENNReal.ofReal_sum_of_nonneg
            (fun c _ => Finset.sum_nonneg fun e _ => by positivity)]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg (fun e _ => by positivity)]
      _ ≤ ENNReal.ofReal (B ^ (2 * (q + 1)) * ‖w‖ ^ 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have := mul_le_mul_of_nonneg_left (hs j w (by omega) hw) (pow_nonneg hB (2 * q))
          simp only [Finset.mul_sum] at this
          calc _ ≤ _ := this
            _ = _ := by ring

theorem ratio_moment : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) (Q : Mx k r) (E : ∀ ν, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν).smSub), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν, n1 ν ≤ q0 → (R ν).IsE Q (E ν) ∧ Formalism.REAL.GlRel (E ν)) → ∀ ν, n1 ν ≤ q0 → ∀ (j q : ℕ), j + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 → ∀ (a : Fin r) (w : (R ν).smSub), Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + ((ν : Fin (2 * r + k + 1) → ℤ) a : ℝ)) j w → ∫⁻ x, ENNReal.ofReal ((lenA k r z (Matrix.of x) a.succ / lenA k r z (Matrix.of x) a.castSucc) ^ (2 * q) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((b ^ 2) ^ (2 * q) * ‖w‖ ^ 2) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE ν hν j q hjq a w hw
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hmass := (GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν).1
  obtain ⟨hNum, hFam, hG, hSF⟩ := hS
  have hDS := hFam ν hν
  obtain ⟨hBe, hdg, -⟩ := hSF ν hν
  obtain ⟨hae, -, hlen, hl⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r _ _ (R ν) Wp z π u μW μN μG νq hDS hG
  have hMod := GlobalTheory.T.cayley_endomorphisms_modular hH k r _ _ (R ν) hNum.1 hDS Q (E ν) hQ (hE ν hν).1
  obtain ⟨⟨hbv, -⟩, hsh⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum
  have hShape := (hsh ν hν).2.1
  refine iterate_bound νq
    (fun x => lenA k r z (Matrix.of x) a.succ / lenA k r z (Matrix.of x) a.castSucc)
    (fun (v : (R ν).smSub) x => dg ν * ‖l ν ((R ν).σ (Matrix.of x) v)‖ ^ 2) (fun c e v => E ν c e v)
    (Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + (ν a : ℝ)))
    (4 * (2 * r + k + 1) ^ 2) (b ^ 2) (by positivity) ((hlen _).div (hlen _))
    (fun v => (((hl (l ν) hBe.1 v v.2).norm.aemeasurable).pow_const 2).const_mul _)
    (fun v x => by positivity) ?_
    (fun i v hv c e => GlobalTheory.lev_E_add_two _ _ _ _ _ i v hMod.1 hMod.2.1 hv c e)
    (fun i v hi hv => ?_) (fun v => hmass v v.2) q j hjq w hw
  · filter_upwards [hae] with x hx v
    have h1 := mul_le_mul_of_nonneg_left
      (GlobalTheory.T.bessel_cayley_side_bound hK k r _ _ (R ν) Wp z π u μW μN μG νq (l ν) Q (E ν) hDS hG hBe.1 hQ (hE ν hν).1
        _ hx a v) hdg.le
    simp only [Finset.mul_sum] at h1
    calc _ = _ := by ring
      _ ≤ _ := h1
  · have h1 := _root_.GlobalTheory.lev_gl_size _ _ _ _ _ k i bv b v hMod hShape hbv hi hv
    calc _ ≤ _ := h1
      _ = _ := by ring

end GlobalTheory.RatioMoment
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorMomentTransferStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_moment_transfer : Hyps → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (om : ι → ℂ) (Bm : R.H → Wp) (BI : ∀ I, (RI I).H → Wp) (β : κ → ℂ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → Function.Injective muI → TensRaw ρ R RI io pr → SideG k r z π u μW μN μG νq → IsBes R z π Bm → (∀ I, IsIsoB (RI I) z π νq (BI I) ∨ β I = 0) → (∀ I, ∀ y ∈ (RI I).sm, Bm (ev Γ R om (fun c => io I c y)) = β I • BI I y) → ∀ I, IsIsoB (RI I) z π νq (BI I) → ∀ y ∈ (RI I).sm, ∀ (a : ι → ℂ), ∀ w ∈ R.sm, ∫ x, ⟪BI I ((RI I).σ (Matrix.of x) y), Formalism.QuantumDeterminants.herm Γ (ρ (Matrix.of x) *ᵥ a) om • Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq = β I * ⟪y, ∑ c, pr I c (tm R a w c)⟫_ℂ := by
  first | exact @GlobalTheory.BesselPairing.pairing | exact GlobalTheory.BesselPairing.pairing | (intros; apply GlobalTheory.BesselPairing.pairing <;> assumption)
end

