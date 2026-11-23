module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TemperedProducts.CentredSegSqInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0334
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0642
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusJointCurve
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0341
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0340
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0338
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0220
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0137
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittChartDescendLevel
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.InUQT

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealPowPartialSegmentLtOne
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.Segment

private theorem two_mul_triangle_add_mul_eq (d l₀ l₁ : ℕ) (h₀ : 1 ≤ l₀) (h₁ : 1 ≤ l₁) :
    2 * (d * (l₀ * l₁ + l₀ * (l₀ - 1) / 2)) * (l₀ + l₁) =
      2 * (d * ((l₀ + l₁) * (l₀ + l₁ - 1) / 2)) * l₀ + d * ((l₀ + l₁) * l₀ * l₁) := by
  obtain ⟨a, rfl⟩ : ∃ a, l₀ = a + 1 := ⟨l₀ - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, l₁ = b + 1 := ⟨l₁ - 1, by omega⟩
  rw [show a + 1 + (b + 1) = a + b + 1 + 1 by ring, Nat.add_sub_cancel, Nat.add_sub_cancel]
  have hp : 2 * ((a + 1) * a / 2) = (a + 1) * a :=
    Nat.two_mul_div_two_of_even (by rw [mul_comm]; exact Nat.even_mul_succ_self a)
  have hq : 2 * ((a + b + 1 + 1) * (a + b + 1) / 2) = (a + b + 1 + 1) * (a + b + 1) :=
    Nat.two_mul_div_two_of_even (by rw [mul_comm]; exact Nat.even_mul_succ_self (a + b + 1))
  generalize (a + 1) * a / 2 = p at hp ⊢
  generalize (a + b + 1 + 1) * (a + b + 1) / 2 = q at hq ⊢
  zify at hp hq ⊢
  linear_combination ((d : ℤ) * (a + b + 1 + 1)) * hp - ((d : ℤ) * (a + 1)) * hq

theorem top_piece_exponent_lt_one : ∀ (α r : ℝ) (d l0 l1 : ℕ), 0 < α → α < 1 → 0 < r → 1 ≤ d → 1 ≤ l0 → 1 ≤ l1 →
    r ^ (l0 + l1) * α ^ (d * ((l0 + l1) * (l0 + l1 - 1) / 2)) = 1 →
    r ^ l0 * α ^ (d * (l0 * l1 + l0 * (l0 - 1) / 2)) < 1 := by
  intro α r d l0 l1 hα0 hα1 hr hd hl0 hl1 h
  have key := two_mul_triangle_add_mul_eq d l0 l1 hl0 hl1
  set T := (l0 + l1) * (l0 + l1 - 1) / 2
  set S := l0 * l1 + l0 * (l0 - 1) / 2
  have hpow : (r ^ l0 * α ^ (d * S)) ^ (2 * (l0 + l1)) = α ^ (d * ((l0 + l1) * l0 * l1)) := by
    calc (r ^ l0 * α ^ (d * S)) ^ (2 * (l0 + l1))
        = (r ^ (l0 + l1)) ^ (2 * l0) * α ^ (2 * (d * S) * (l0 + l1)) := by
          rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
          congr 2 <;> ring
      _ = (r ^ (l0 + l1) * α ^ (d * T)) ^ (2 * l0) * α ^ (d * ((l0 + l1) * l0 * l1)) := by
          rw [key, pow_add α, mul_pow (r ^ (l0 + l1)), ← pow_mul α (d * T),
            show d * T * (2 * l0) = 2 * (d * T) * l0 by ring, ← mul_assoc ((r ^ (l0 + l1)) ^ (2 * l0))]
      _ = α ^ (d * ((l0 + l1) * l0 * l1)) := by rw [h, one_pow, one_mul]
  have hlt : α ^ (d * ((l0 + l1) * l0 * l1)) < 1 :=
    pow_lt_one₀ hα0.le hα1
      (Nat.mul_pos (by omega) (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))).ne'
  by_contra hc
  push_neg at hc
  have h1 : 1 ≤ (r ^ l0 * α ^ (d * S)) ^ (2 * (l0 + l1)) := one_le_pow₀ hc
  rw [hpow] at h1
  exact absurd hlt (not_lt.mpr h1)

end GlobalTheory.CompanionTheory.Segment
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionMirabolicTwistedKernel
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.BZMirDer

theorem twKer_resM_derUnipM : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (m n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (m + 1)) k) V),
    twKer (resM k π).ρ (derUnipM k m n) (derCharM k ψ m n) = twKer π (derUnip k (m + 1) n) (derChar k ψ (m + 1) n) := by
  intro k _ _ _ _ ψ m n V _ _ π
  unfold twKer
  congr 1
  ext w
  constructor
  · rintro ⟨u, v, rfl⟩
    exact ⟨Subgroup.subgroupOfEquivOfLe (derUnip_le_Mir k m n) u, v, rfl⟩
  · rintro ⟨u, v, rfl⟩
    refine ⟨(Subgroup.subgroupOfEquivOfLe (derUnip_le_Mir k m n)).symm u, v, ?_⟩
    simp [derCharM, resM]
    rfl

end GlobalTheory.CompanionTheory.BZMirDer
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetTwoFactorSplit
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.SegJacquet

theorem exists_isTopCut_two_of_jhMult_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (Δ : Segment k) (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), Zc.LSegJacquet k → IsLSeg Δ π →
    ∀ (x : Fin 2 → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), (∀ a, 0 < (x a).1) → Zc.jm x hd π ≠ 0 →
    ∃ Γ : Fin 2 → Segment k, Zc.IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (x a).rep := by
  intro k _ _ _ _ Δ N V _ _ π hJ hπ x hd hpos hne
  by_contra hno
  exact hne ((hJ Δ π hπ 2 x hd hpos).2 hno)

end GlobalTheory.CompanionTheory.SegJacquet
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepCentralCharacter
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.ZlScalar

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prod_absPow_range (u : kˣ) (n : ℕ) :
    ∏ a ∈ Finset.range n, ((absPow k ((a : ℕ) : ℂ) u : ℂˣ) : ℂ) =
      ((absPow k (((n * (n - 1) / 2 : ℕ) : ℂ)) u : ℂˣ) : ℂ) := by
  rw [← Finset.sum_range_id]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Finset.sum_range_succ, Nat.cast_add, absPow_add, MonoidHom.mul_apply,
      Units.val_mul]

theorem prod_fin_absPow (l : ℕ) (c : ℂ) (u : kˣ) :
    ∏ a : Fin l, (c * ((absPow k ((a : ℕ) : ℂ) u : ℂˣ) : ℂ)) =
      c ^ l * ((absPow k (((l * (l - 1) / 2 : ℕ) : ℂ)) u : ℂˣ) : ℂ) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fin.prod_univ_eq_prod_range (fun a => ((absPow k ((a : ℕ) : ℂ) u : ℂˣ) : ℂ)), prod_absPow_range]

theorem smul_of_surjective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W} (f : π.IntertwiningMap σ) (hf : Function.Surjective f)
    (g : G) (C : ℂ) (h : ∀ w, π g w = C • w) (v : W) : σ g v = C • v := by
  obtain ⟨w, rfl⟩ := hf v
  rw [← map_smul, ← h w]
  exact (Representation.IntertwiningMap.isIntertwining π σ f g w).symm

theorem exists_surjective_of_isCosocle {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {π : Representation ℂ G V} (h : IsCosocle σ π) :
    ∃ f : π.IntertwiningMap σ, Function.Surjective f :=
  let ⟨_, f, hf, _⟩ := h
  ⟨f, hf⟩

theorem smul_of_isCosocle {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {π : Representation ℂ G V} (h : IsCosocle σ π)
    (g : G) (C : ℂ) (hg : ∀ w, π g w = C • w) (v : W) : σ g v = C • v :=
  let ⟨f, hf⟩ := exists_surjective_of_isCosocle h
  smul_of_surjective f hf g C hg v

theorem scalarBy_term (Δ : Segment k) (t : kˣ) (c : ℂ) (hc : Zl.ScalarBy Δ.first t c) (a : Fin Δ.len) :
    Zl.ScalarBy (Δ.term a) t (c * ((absPow k ((a : ℕ) : ℂ) (t ^ Δ.d) : ℂˣ) : ℂ)) :=
  GlobalTheory.CompanionTheory.Dblock.scalarBy_nu k Δ.first ((a : ℕ) : ℂ) t c hc

theorem scalarBy_lseg (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Δ : Segment k) (y : IrrGL (k := k)) (hy : IsLSeg Δ y.rep) (t : kˣ) (c : ℂ) (hc : Zl.ScalarBy Δ.first t c) :
    Zl.ScalarBy y t (c ^ Δ.len * ((absPow k (((Δ.len * (Δ.len - 1) / 2 : ℕ) : ℂ)) (t ^ Δ.d) : ℂˣ) : ℂ)) := by
  rcases hy with ⟨hd, hco⟩
  have key := GlobalTheory.CompanionTheory.ZCentre.prodIrr_scalar k Δ.len y.1 Δ.term hd t (fun a => c * ((absPow k ((a : ℕ) : ℂ) (t ^ Δ.d) : ℂˣ) : ℂ)) (scalarBy_term Δ t c hc)
  simp only [prod_fin_absPow] at key
  intro v
  exact smul_of_isCosocle hco (Matrix.GeneralLinearGroup.scalar (Fin y.1) t) _ key v

end GlobalTheory.CompanionTheory.ZlScalar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepCentralCharacterFormula
section
noncomputable section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.SegScalar

theorem absPow_natCast (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) : absPow k (n : ℂ) = absPow k 1 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, absPow_add, ih, pow_succ]

theorem absPow_pow_comm (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a d : ℕ) (t : kˣ) :
    (((absPow k (a : ℂ) ^ d) t : ℂˣ) : ℂ) = ((absPow k (d : ℂ) t : ℂˣ) : ℂ) ^ a := by
  rw [absPow_natCast, absPow_natCast, ← pow_mul, mul_comm a d, MonoidHom.pow_apply, MonoidHom.pow_apply, pow_mul,
    Units.val_pow_eq_pow_val]

theorem prod_mul_pow (l : ℕ) (c e : ℂ) :
    ∏ a : Fin l, (c * e ^ (a : ℕ)) = c ^ l * e ^ (l * (l - 1) / 2) := by
  rw [Fin.prod_univ_eq_prod_range (fun a => c * e ^ a) l, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_range, Finset.prod_pow_eq_pow_sum, Finset.sum_range_id]

theorem scalarBy_of_isLSeg (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Γ : Segment k) (y : IrrGL (k := k)) : IsLSeg Γ y.rep → ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy Γ.first t c →
      Zl.ScalarBy y t (c ^ Γ.len * ((absPow k (Γ.first.1 : ℂ) t : ℂˣ) : ℂ) ^ (Γ.len * (Γ.len - 1) / 2)) := by
  intro hL t c hc
  obtain ⟨hd, -, f, hf, -⟩ := hL
  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar Γ.first.2.rep.smooth Γ.first.2.rep.irr
  have hωc : ((ω t : ℂˣ) : ℂ) = c := by
    haveI := Model.nontrivial_of_isIrreducible Γ.first.2.rep.irr
    obtain ⟨w, hw⟩ := exists_ne (0 : Γ.first.2.rep.V)
    have h1 : ((ω t : ℂˣ) : ℂ) • w = c • w := (hω t w).symm.trans (hc w)
    exact smul_left_injective ℂ hw h1
  have hterm : ∀ a : Fin Γ.len, HasCentralChar (Γ.term a).rep (ω * absPow k ((a : ℕ) : ℂ) ^ Γ.first.1) :=
    fun a => UnitaryOrder.hasCentralChar_nu Γ.first hω ((a : ℕ) : ℂ)
  have hsc : ∀ v, y.rep (Matrix.GeneralLinearGroup.scalar (Fin y.1) t) v =
      (∏ a : Fin Γ.len, ((((ω * absPow k ((a : ℕ) : ℂ) ^ Γ.first.1) t : ℂˣ)) : ℂ)) • v := by
    intro v
    obtain ⟨w, rfl⟩ := hf v
    have h1 := GlobalTheory.BoundaryMaps.multiProd_scalar (stdBlocks (fun a => (Γ.term a).1) hd)
      (fun a => (Γ.term a).rep) _ hterm t w
    rw [← f.isIntertwining]
    exact (congrArg f h1).trans (map_smul f _ _)
  have h2 : ∏ a : Fin Γ.len, ((((ω * absPow k ((a : ℕ) : ℂ) ^ Γ.first.1) t : ℂˣ)) : ℂ) =
      c ^ Γ.len * ((absPow k (Γ.first.1 : ℂ) t : ℂˣ) : ℂ) ^ (Γ.len * (Γ.len - 1) / 2) := by
    rw [← prod_mul_pow]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [MonoidHom.mul_apply, Units.val_mul, hωc, absPow_pow_comm]
  rw [← h2]
  exact hsc

end GlobalTheory.CompanionTheory.SegScalar

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothOperatorFacts
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.FcSmooth

variable {n : ℕ}

theorem isSec_comb (E : KMod n) (c : ℂ) {f f' : Mat n → E.V} (h : IsSec E f) (h' : IsSec E f') :
    IsSec E (fun y => c • f y + f' y) := by
  intro g hg k
  simp only [h g hg k, h' g hg k, map_add (f := _), map_smul]

section

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)

theorem word_est (hAE : AlgEst) (hL : LgFacts) (hU : Unimod) (hR : RCalc) (hC : CalcSteps)
    (h : C₀(ℝ, ℂ)) (hh : ∀ m : ℕ, ∃ h' : C₀(ℝ, ℂ), ∀ y, h' y = (y : ℂ) ^ m * h y) :
    haveI := FiniteDimensional.complete ℂ E.V
    ∀ (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ) (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T),
      (∀ (f : Mat n → E.V) (hf : cls μ f ∈ Msob μ E.V), Sob μ f → (Ω ⟨cls μ f, hf⟩ : Lp E.V 2 μ) = cls μ (Om f)) →
      ∀ w : List (Bool × Fin n × Fin n), ∃ C : ℝ, ∀ f f' : Mat n → E.V, IsSec E f' → Sob μ f' →
        cls μ f' = F.Φ h (cls μ f) → ‖cls μ (Rw w f')‖ ≤ C * ‖cls μ f‖ := by
  haveI := FiniteDimensional.complete ℂ E.V
  intro Ω T F hΩ w
  obtain ⟨-, -, -, -, hCF, -, -, -, -, -, -, -, hOF, hIb, -⟩ := hC
  choose hm hhm using hh
  obtain ⟨C₁, hC₁⟩ := (_root_.GlobalTheory.CompanionTheory.FcSmooth.WordBd.word_bound) n μ E.V hL hU hR hAE hCF hIb w
  obtain ⟨Q, hQ⟩ := (_root_.GlobalTheory.CompanionTheory.FcSmooth.lap_sec) n E hR hOF
  choose Cj hCj using (_root_.GlobalTheory.CompanionTheory.LapSec.sectionBound) n μ E Q hL hU hR hCF hQ
  refine ⟨|C₁| * ∑ j ∈ range (w.length + 1), |Cj j| * ∑ i ∈ range (j + 1), ‖hm i‖, ?_⟩
  intro f f' hsec hS hcl
  have hsob : ∀ i, Sob μ (Om^[i] f') := by
    intro i
    induction i with
    | zero => exact hS
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact GlobalTheory.CompanionTheory.SobOpsPf.sob_Om ih
  have hit : ∀ i, cls μ (Om^[i] f') = F.Φ (hm i) (cls μ f) := by
    intro i
    induction i with
    | zero =>
      have : hm 0 = h := by ext y; simp [hhm]
      simpa [this] using hcl
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      have hmem : cls μ (Om^[i] f') ∈ Msob μ E.V := Submodule.subset_span ⟨_, hsob i, rfl⟩
      rw [← hΩ _ hmem (hsob i)]
      exact F.omega (hm i) (hm (i + 1)) (fun y => by simp only [hhm]; ring) _ _ ih
  have hn : ∀ i, ‖cls μ (Om^[i] f')‖ ≤ ‖hm i‖ * ‖cls μ f‖ := by
    intro i
    rw [hit]
    exact ((F.Φ (hm i)).le_opNorm _).trans (mul_le_mul_of_nonneg_right (F.norm_le _) (norm_nonneg _))
  have hj : ∀ j, ‖cls μ (Lap^[j] f')‖ ≤ (|Cj j| * ∑ i ∈ range (j + 1), ‖hm i‖) * ‖cls μ f‖ := by
    intro j
    have hs : ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f')‖ ≤ (∑ i ∈ range (j + 1), ‖hm i‖) * ‖cls μ f‖ := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ => hn i
    have h0 : 0 ≤ ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f')‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    calc _ ≤ Cj j * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f')‖ := hCj j f' hS hsec
      _ ≤ |Cj j| * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f')‖ :=
        mul_le_mul_of_nonneg_right (le_abs_self _) h0
      _ ≤ |Cj j| * ((∑ i ∈ range (j + 1), ‖hm i‖) * ‖cls μ f‖) :=
        mul_le_mul_of_nonneg_left hs (abs_nonneg _)
      _ = _ := by ring
  have h0 : 0 ≤ ∑ j ∈ range (w.length + 1), ‖cls μ (Lap^[j] f')‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hs : ∑ j ∈ range (w.length + 1), ‖cls μ (Lap^[j] f')‖ ≤
      (∑ j ∈ range (w.length + 1), |Cj j| * ∑ i ∈ range (j + 1), ‖hm i‖) * ‖cls μ f‖ := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => hj j
  calc _ ≤ C₁ * ∑ j ∈ range (w.length + 1), ‖cls μ (Lap^[j] f')‖ := hC₁ f' hS
    _ ≤ |C₁| * ∑ j ∈ range (w.length + 1), ‖cls μ (Lap^[j] f')‖ :=
      mul_le_mul_of_nonneg_right (le_abs_self _) h0
    _ ≤ |C₁| * ((∑ j ∈ range (w.length + 1), |Cj j| * ∑ i ∈ range (j + 1), ‖hm i‖) * ‖cls μ f‖) :=
      mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    _ = _ := by ring

end

theorem smoothOp : SmoothOp := by
  intro n _ _ μ _ E
  haveI := FiniteDimensional.complete ℂ E.V
  intro Ω T F hL hU hR hS hAE hC hΩ h hh
  have hW := word_est μ E hAE hL hU hR hC h hh Ω T F hΩ
  choose Cw hCw using hW
  obtain ⟨S, Cs, hb⟩ := GlobalTheory.CompanionTheory.CurveJ.sup_bound hS n μ
  have hkeep := (GlobalTheory.T.functional_calculus_on_sobolev) n μ E Ω T F hL hU hR hS hC hΩ h
  refine ⟨|Cs| * ∑ w ∈ S, |Cw w|, fun x hx => ?_⟩
  obtain ⟨xs, hxs, hlim⟩ := mem_closure_iff_seq_limit.1 hx
  choose fs hfS hfsec hfcl using hxs
  choose a haS hasec hacl using fun k => hkeep (fs k) (hfS k) (hfsec k)
  have hacl' : ∀ k, cls μ (a k) = F.Φ h (xs k) := fun k => by rw [hacl, hfcl]

  have hdiff : ∀ w k l, ‖cls μ (Rw w (a k)) - cls μ (Rw w (a l))‖ ≤ |Cw w| * ‖xs k - xs l‖ := by
    intro w k l
    have c1 := GlobalTheory.CompanionTheory.CurveJ.sob_comb (-1) (haS l) (haS k)
    have c2 := GlobalTheory.CompanionTheory.CurveJ.sob_comb (-1) (hfS l) (hfS k)
    have e1 : cls μ (fun y => (-1 : ℂ) • fs l y + fs k y) = xs k - xs l := by
      have := c2.2 []
      simp only [Rw, id] at this
      rw [this, hfcl, hfcl]
      simp [sub_eq_neg_add]
    have e2 : cls μ (fun y => (-1 : ℂ) • a l y + a k y) = F.Φ h (cls μ (fun y => (-1 : ℂ) • fs l y + fs k y)) := by
      have := c1.2 []
      simp only [Rw, id] at this
      rw [this, hacl', hacl', e1, map_sub]
      simp [sub_eq_neg_add]
    have b := hCw w _ _ (isSec_comb E (-1) (hasec l) (hasec k)) c1.1 e2
    rw [c1.2 w, e1] at b
    have e3 : (-1 : ℂ) • cls μ (Rw w (a l)) + cls μ (Rw w (a k)) = cls μ (Rw w (a k)) - cls μ (Rw w (a l)) := by
      simp [sub_eq_neg_add]
    rw [e3] at b
    exact b.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
  have hcs : CauchySeq xs := hlim.cauchySeq
  have hcau : ∀ w, CauchySeq fun k => cls μ (Rw w (a k)) := by
    intro w
    rw [Metric.cauchySeq_iff] at hcs ⊢
    intro ε hε
    have hpos : 0 < |Cw w| + 1 := by positivity
    obtain ⟨N, hN⟩ := hcs (ε / (|Cw w| + 1)) (div_pos hε hpos)
    refine ⟨N, fun k hk l hl => ?_⟩
    have h1 := hN k hk l hl
    rw [dist_eq_norm] at h1 ⊢
    have h2 := hdiff w k l
    rw [lt_div_iff₀ hpos] at h1
    nlinarith [norm_nonneg (xs k - xs l), abs_nonneg (Cw w)]
  obtain ⟨b, hbS, hbt, hbp⟩ := (_root_.GlobalTheory.CompanionTheory.SobComplete.sob_complete) n μ E.V hS a haS hcau
  refine ⟨b, hbS, ?_, ?_, ?_⟩
  · intro g hg k
    have hgk : g * k.1 ∈ GLs n := by
      have hk : (k.1 : Mat n).det ≠ 0 := by
        intro h0
        have := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff.1 k.2)
        rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
        exact zero_ne_one this
      show (g * k.1).det ≠ 0
      rw [Matrix.det_mul]
      exact mul_ne_zero hg hk
    have t1 := hbp _ hgk
    have t2 : Tendsto (fun j => a j (g * k.1)) atTop (𝓝 (E.ρ k⁻¹ (b g))) := by
      simp only [fun j => hasec j g hg k]
      exact ((E.ρ k⁻¹).continuous.tendsto _).comp (hbp g hg)
    exact tendsto_nhds_unique t1 t2
  · have t1 := hbt []
    simp only [Rw, id] at t1
    have t2 : Tendsto (fun k => cls μ (a k)) atTop (𝓝 (F.Φ h x)) := by
      simp only [hacl']
      exact ((F.Φ h).continuous.tendsto _).comp hlim
    exact tendsto_nhds_unique t1 t2
  · have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
    have t1 : Tendsto (fun k => ‖a k 1‖) atTop (𝓝 ‖b 1‖) := (hbp 1 h1).norm
    have t2 : Tendsto (fun k => (|Cs| * ∑ w ∈ S, |Cw w|) * ‖xs k‖) atTop (𝓝 ((|Cs| * ∑ w ∈ S, |Cw w|) * ‖x‖)) :=
      hlim.norm.const_mul _
    refine le_of_tendsto_of_tendsto' t1 t2 fun k => ?_
    have b1 := hb E.V (a k) (haS k) 1 h1
    have h0 : 0 ≤ ∑ w ∈ S, ‖cls μ (Rw w (a k))‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hs : ∑ w ∈ S, ‖cls μ (Rw w (a k))‖ ≤ (∑ w ∈ S, |Cw w|) * ‖xs k‖ := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun w _ => ?_
      have := hCw w (fs k) (a k) (hasec k) (haS k) (by rw [hacl', hfcl])
      rw [hfcl] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
    calc _ ≤ Cs * ∑ w ∈ S, ‖cls μ (Rw w (a k))‖ := b1
      _ ≤ |Cs| * ∑ w ∈ S, ‖cls μ (Rw w (a k))‖ := mul_le_mul_of_nonneg_right (le_abs_self _) h0
      _ ≤ |Cs| * ((∑ w ∈ S, |Cw w|) * ‖xs k‖) := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
      _ = _ := by ring

end GlobalTheory.CompanionTheory.FcSmooth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothRepIsSmoothFoundation
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.SmoothTransfer

theorem isSmooth_found : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → GroundTheory.Automorphic.IsSmooth π := by
  intro k _ _ _ _ N V _ _ π h
  exact h

end GlobalTheory.CompanionTheory.SmoothTransfer
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareIntegrableUnitarizable
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.SqIntUnit

theorem isUnitarisable_of_isSqIntCoeff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)), IsSqIntCoeff x.rep → IsUnitarisable x.rep := by
  intro k _ _ _ _ x h
  exact GlobalTheory.SqIntUnit.main k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr h

end GlobalTheory.CompanionTheory.SqIntUnit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittChartDescendLevelStatement
section
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution CrystallineSemistableComparison.Pb.LsQ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_chart_descend_level : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) {n : ℕ} (hn : n ≠ 0) {W : X.Opens} {d : ℕ} (c' : Chart (Wc.pd l k (n + 1)) l q ((Wc.res l k (n + 1)).comp ρ) W d), ∃ (c : Chart (Wc.pd l k n) l q ((Wc.res l k n).comp ρ) W d) (e : c.D ≅ (qF (F := B.schFn q) (ρ := ρ) hn).obj c'.D), (∀ i, e.hom.φ (c.t i) = Ideal.Quotient.mk _ (c'.t i)) ∧ (FlatT ((qF (F := B.schFn q) (ρ := ρ) hn).obj c'.D) → FlatT c.D) := by
  first | exact @GlobalTheory.CompanionTheory.ChartRed.chart_q | exact GlobalTheory.CompanionTheory.ChartRed.chart_q | (intros; apply GlobalTheory.CompanionTheory.ChartRed.chart_q <;> assumption)
end

