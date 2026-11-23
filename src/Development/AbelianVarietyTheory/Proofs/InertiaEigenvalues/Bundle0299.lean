module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0265
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0286
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalMapSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLimitCocycleOfCompatibleModPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Filter Topology Pointwise

namespace GlobalTheory.LimCocycle

theorem eventually_smul_mem {LL W : Type} [Field LL] [TopologicalSpace LL] [AddCommGroup W] [Module LL W]
    [TopologicalSpace W] [ContinuousSMul LL W] (c : ℕ → LL) (hc : Tendsto c atTop (𝓝 0))
    {K : Set W} (hK : IsCompact K) {U : Set W} (hU : U ∈ 𝓝 (0 : W)) :
    ∀ᶠ m in atTop, ∀ y ∈ K, c m • y ∈ U := by
  have h : ∀ᶠ a in 𝓝 (0 : LL), ∀ y ∈ K, a • y ∈ U := by
    refine hK.eventually_forall_of_forall_eventually (fun y _ => ?_)
    have := (continuous_fst.smul continuous_snd : Continuous fun p : LL × W => p.1 • p.2).tendsto ((0 : LL), y)
    exact this.eventually_mem (by simpa using hU)
  exact hc.eventually h

theorem isCompact_of_fg {O LL V : Type} [CommRing O] [Field LL] [Algebra O LL] [TopologicalSpace LL]
    [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [TopologicalSpace V]
    [ContinuousAdd V] [ContinuousSMul LL V]
    (hc : IsCompact (Set.range (algebraMap O LL))) (T : Submodule O V) (hT : T.FG) :
    IsCompact (T : Set V) := by
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hT
  have heq : (T : Set V) = (fun c : Fin n → LL => ∑ i, c i • s i) ''
      (Set.univ.pi fun _ => Set.range (algebraMap O LL)) := by
    ext x
    constructor
    · intro hx
      rw [SetLike.mem_coe, ← hs] at hx
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hx
      refine ⟨fun i => algebraMap O LL (a i), fun i _ => ⟨a i, rfl⟩, ?_⟩
      simp only [algebraMap_smul]
      exact ha
    · rintro ⟨c, hc', rfl⟩
      have : ∀ i, ∃ a : O, algebraMap O LL a = c i := fun i => hc' i (Set.mem_univ i)
      choose a ha using this
      rw [SetLike.mem_coe, ← hs]
      have : (∑ i, c i • s i) = ∑ i, a i • s i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← ha i, algebraMap_smul]
      show ∑ i, c i • s i ∈ _
      rw [this]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  rw [heq]
  exact (isCompact_univ_pi fun _ => hc).image
    (continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const)

end GlobalTheory.LimCocycle

namespace GlobalTheory.LimCocycle

theorem limit_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (hI : ∀ n : ℕ, StableSub LA (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)) (w : ℕ → ↥(GK K) → ↥LA.T), (∀ n, (fun g => (Submodule.Quotient.mk (w n g) : ↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T))) ∈ quotientCocycles LA _ (hI n)) → (∀ n g, w (n + 1) g - w n g ∈ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)) → ∃ d ∈ latticeCocycles LA, ∀ n g, ∃ t ∈ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T), d g = (w n g : A.V) + (t : A.V) := by
  intro l _ K LL _ _ _ O _ _ hG A LA ϖ hϖ hI w hw hstep
  have hcO : IsCompact (Set.range (algebraMap O LL)) := (GlobalTheory.T.coefficient_ring_integers_compact_adic_properties l LL O hG).2.1
  obtain ⟨⟨hD, hDVR, hFr⟩, hfin, hmod, htop, hopen⟩ := hG
  haveI := hD
  haveI := hDVR
  haveI := hFr
  haveI : FiniteDimensional ℚ_[l] LL := hfin
  haveI := hmod
  haveI := htop
  haveI : ContinuousSMul ℚ_[l] LL := IsModuleTopology.toContinuousSMul ℚ_[l] LL
  haveI : ContinuousSMul LL A.V := IsModuleTopology.toContinuousSMul LL A.V
  haveI : IsTopologicalAddGroup A.V := IsModuleTopology.topologicalAddGroup LL A.V
  haveI : T2Space LL := by
    let e := (Module.finBasis ℚ_[l] LL).equivFun
    exact T2Space.of_injective_continuous e.injective (IsModuleTopology.continuous_of_linearMap e.toLinearMap)
  haveI : T2Space A.V := by
    let e := (Module.finBasis LL A.V).equivFun
    exact T2Space.of_injective_continuous e.injective (IsModuleTopology.continuous_of_linearMap e.toLinearMap)

  have hlpr : l.Prime := Fact.out
  let c : ℕ → LL := fun m => algebraMap O LL (((l : ℕ) : O) ^ m)
  have hc : Tendsto c atTop (𝓝 0) := by
    have hcont : Continuous (algebraMap ℚ_[l] LL) := by
      have h : (algebraMap ℚ_[l] LL : ℚ_[l] → LL) = fun a => a • (1 : LL) :=
        funext Algebra.algebraMap_eq_smul_one
      rw [h]
      exact continuous_id.smul continuous_const
    have h1 := (hcont.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (Padic.norm_p_lt_one (p := l)))
    rw [map_zero] at h1
    refine h1.congr (fun m => ?_)
    simp [c, Function.comp, map_pow, map_natCast]

  have hl0 : ((l : ℕ) : O) ≠ 0 := by
    intro h
    have h2 := congrArg (algebraMap O LL) h
    rw [map_natCast, map_zero, ← map_natCast (algebraMap ℚ_[l] LL),
      map_eq_zero_iff _ (algebraMap ℚ_[l] LL).injective, Nat.cast_eq_zero] at h2
    exact hlpr.ne_zero h2
  have hlnu : ¬ IsUnit ((l : ℕ) : O) := by
    intro hu
    obtain ⟨a, ha⟩ := hu.exists_right_inv
    have hU : ({1}ᶜ : Set LL) ∈ 𝓝 (0 : LL) := isOpen_compl_singleton.mem_nhds (by simp)
    obtain ⟨m, hm⟩ := (eventually_smul_mem c hc hcO hU).exists
    apply hm (algebraMap O LL (a ^ m)) ⟨_, rfl⟩
    simp only [c, smul_eq_mul, ← map_mul, ← mul_pow, ha, one_pow, map_one, Set.mem_singleton_iff]
  obtain ⟨v, u, hlu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ

  let Q : ℕ → Submodule O A.V := fun n => ϖ ^ n • LA.T
  have hQT : ∀ n, Q n ≤ LA.T := by
    intro n x hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    exact LA.T.smul_mem _ hy
  have hQmono : ∀ m n, m ≤ n → Q n ≤ Q m := by
    intro m n hmn x hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨ϖ ^ (n - m) • y, LA.T.smul_mem _ hy, ?_⟩
    rw [smul_smul, ← pow_add, Nat.add_sub_cancel' hmn]
  have hmem : ∀ n (t : ↥LA.T), t ∈ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T) ↔ (t : A.V) ∈ Q n := by
    intro n t
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists,
      Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨b, -, hb⟩
      exact ⟨b, b.2, by rw [← hb]; rfl⟩
    · rintro ⟨b, hbT, hb⟩
      exact ⟨⟨b, hbT⟩, trivial, Subtype.ext hb⟩
  have hTc : IsCompact (LA.T : Set A.V) := isCompact_of_fg hcO LA.T LA.fg
  have hQc : ∀ n, IsCompact (Q n : Set A.V) := by
    intro n
    have h : (Q n : Set A.V) = (fun x => algebraMap O LL (ϖ ^ n) • x) '' (LA.T : Set A.V) := by
      simp only [Q, Submodule.coe_pointwise_smul, algebraMap_smul]
      rfl
    rw [h]
    exact hTc.image (continuous_const_smul _)
  have hQρ : ∀ n g, ∀ x ∈ Q n, A.ρ g x ∈ Q n := by
    intro n g x hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨A.ρ g y, LA.stable g y hy, ?_⟩
    rw [LinearMap.map_smul_of_tower]

  have hshrink : ∀ U ∈ 𝓝 (0 : A.V), ∃ N, ∀ x ∈ Q N, x ∈ U := by
    intro U hU
    obtain ⟨M, hM⟩ := (eventually_smul_mem c hc hTc hU).exists
    refine ⟨v * M, fun x hx => ?_⟩
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    have hpow : ϖ ^ (v * M) = ((l : ℕ) : O) ^ M * (↑u⁻¹ : O) ^ M := by
      rw [← mul_pow, hlu, pow_mul, mul_comm (↑u : O), mul_assoc, Units.mul_inv, mul_one]
    have h := hM (((↑u⁻¹ : O) ^ M) • y) (LA.T.smul_mem _ hy)
    rw [hpow, mul_smul]
    simpa only [c, algebraMap_smul] using h
  have hsep : ∀ x : A.V, (∀ n, x ∈ Q n) → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨N, hN⟩ := hshrink {x}ᶜ (isOpen_compl_singleton.mem_nhds (Ne.symm hne))
    exact hN x (hx N) rfl

  have hlim : ∀ g, ∃ x : A.V, ∀ n, x - (w n g : A.V) ∈ Q n := by
    intro g
    let C : ℕ → Set A.V := fun n => (fun x => x - (w n g : A.V)) ⁻¹' (Q n : Set A.V)
    have hne := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
      (fun n x hx => by
        have h1 : x - (w (n + 1) g : A.V) ∈ Q n := hQmono n (n + 1) (Nat.le_succ n) hx
        have h2 : ((w (n + 1) g : A.V) - (w n g : A.V)) ∈ Q n := by
          have := (hmem n _).1 (hstep n g)
          simpa using this
        show x - (w n g : A.V) ∈ Q n
        have := (Q n).add_mem h1 h2
        simpa using this)
      (fun n => ⟨w n g, by simp [C]⟩)
      (by
        have : C 0 = (Homeomorph.subRight (w 0 g : A.V)) ⁻¹' (Q 0 : Set A.V) := rfl
        rw [this]
        exact (Homeomorph.subRight (w 0 g : A.V)).isCompact_preimage.2 (hQc 0))
      (fun n => (hQc n).isClosed.preimage (continuous_sub_right _))
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, fun n => Set.mem_iInter.1 hx n⟩
  choose d hd using hlim
  have hdT : ∀ g, d g ∈ LA.T := by
    intro g
    have := LA.T.add_mem (hQT 0 (hd g 0)) (w 0 g).2
    simpa using this

  have hcocn : ∀ n g h, (w n (g * h) : A.V) - w n g - A.ρ g (w n h) ∈ Q n := by
    intro n g h
    have h1 := (hw n).2 g h
    simp only [actQ, Submodule.mapQ_apply] at h1
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq] at h1
    have := (hmem n _).1 h1
    simp only [Submodule.coe_sub, Submodule.coe_add] at this
    rw [sub_sub]
    exact this
  have hcoc : ∀ g h, d (g * h) = d g + A.ρ g (d h) := by
    intro g h
    have : d (g * h) - d g - A.ρ g (d h) = 0 := by
      refine hsep _ (fun n => ?_)
      have e : d (g * h) - d g - A.ρ g (d h) = (d (g * h) - w n (g * h)) - (d g - w n g)
          - A.ρ g (d h - w n h) + ((w n (g * h) : A.V) - w n g - A.ρ g (w n h)) := by
        rw [map_sub]; abel
      rw [e]
      exact (Q n).add_mem ((Q n).sub_mem ((Q n).sub_mem (hd _ n) (hd g n)) (hQρ n g _ (hd h n)))
        (hcocn n g h)
    exact sub_eq_zero.1 (by rw [← sub_sub]; exact this)

  have hcont : Continuous d := by
    rw [continuous_iff_continuousAt]
    intro g₀
    rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff]
    intro U hU
    obtain ⟨N, hN⟩ := hshrink U hU
    have hlc := (IsLocallyConstant.iff_eventually_eq _).1 (hw N).1 g₀
    refine Filter.mem_map.2 ?_
    filter_upwards [hlc] with g hg
    show d g - d g₀ ∈ U
    apply hN
    rw [Submodule.Quotient.eq] at hg
    have h3 := (hmem N _).1 hg
    simp only [Submodule.coe_sub] at h3
    have e : d g - d g₀ = (d g - w N g) - (d g₀ - w N g₀) + ((w N g : A.V) - w N g₀) := by abel
    rw [e]
    exact (Q N).add_mem ((Q N).sub_mem (hd g N) (hd g₀ N)) h3
  refine ⟨d, ⟨⟨hcont, hcoc⟩, fun g _ => hdT g⟩, fun n g => ?_⟩
  refine ⟨⟨d g - w n g, hQT n (hd g n)⟩, (hmem n _).2 (hd g n), ?_⟩
  simp

end GlobalTheory.LimCocycle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalFormUnramifiedRestrictionScalars
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon

theorem intertwine_mul {G ι R S : Type} [Monoid G] [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (B : G → Matrix ι ι S) (hB1 : B 1 = 1)
    (hBm : ∀ g h, B (g * h) = B g * B h) (p : GL ι S) (T : G → Matrix ι ι R)
    (hT : ∀ g, (p : Matrix ι ι S) * (T g).map f = B g * p) :
    T 1 = 1 ∧ ∀ g h, T (g * h) = T g * T h := by
  have hinj : Function.Injective (fun M : Matrix ι ι R => M.map f) := Matrix.map_injective hf
  refine ⟨?_, fun g h => ?_⟩
  · apply hinj
    apply (Units.mul_right_inj p).1
    show (p : Matrix ι ι S) * (T 1).map f = (p : Matrix ι ι S) * (1 : Matrix ι ι R).map f
    rw [hT, hB1, one_mul, Matrix.map_one f (map_zero f) (map_one f), mul_one]
  · apply hinj
    apply (Units.mul_right_inj p).1
    show (p : Matrix ι ι S) * (T (g * h)).map f = (p : Matrix ι ι S) * (T g * T h).map f
    calc (p : Matrix ι ι S) * (T (g * h)).map f = B g * B h * p := by rw [hT, hBm]
      _ = B g * ((p : Matrix ι ι S) * (T h).map f) := by rw [mul_assoc, hT]
      _ = ((p : Matrix ι ι S) * (T g).map f) * (T h).map f := by rw [← mul_assoc, hT]
      _ = (p : Matrix ι ι S) * (T g * T h).map f := by rw [Matrix.map_mul, mul_assoc]

theorem exists_ratForm : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (W : GL (Fin r) ↥(MaximalUnramifiedExtension l)), IsRat r σ →
    (∀ m k : Fin r, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k = fr l m (ω k)) → (∀ k, fr l r (ω k) = ω k) →
    (∀ (X : Type) [TopologicalSpace X] (x : X → ↥(MaximalUnramifiedExtension l)), (∀ t, fr l r (x t) = x t) →
      Continuous (fun t => ((x t : ↥(MaximalUnramifiedExtension l)) : Om l)) →
      ∃ a : X → Fin r → ℚ_[l], Continuous a ∧ ∀ t (m : Fin r),
        fr l m (x t) = ∑ k, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (a t k)) →
    ∃ (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)),
      (∀ i j, Continuous fun g => (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]) i j) ∧
      (∀ i j, (((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) ∧
      (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) ∧
      ∀ c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l), (∀ g i, fr l r (c g i) = c g i) →
        (∀ i, Continuous fun g => ((c g i : ↥(MaximalUnramifiedExtension l)) : Om l)) →
        ∃ c₀ : ↥(GK K) → n × Fin r → ℚ_[l], Continuous c₀ ∧ ∀ g,
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec (fun x => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c₀ g x)) =
            fun x => fr l x.2 (c g x.1) := by
  intro l _ n _ _ K r σ ω W hσ hW hω hcoef
  classical

  let P0 : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) :=
    Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (1 : Matrix n n ↥(MaximalUnramifiedExtension l)) (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l))
  let Q0 : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) :=
    Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (1 : Matrix n n ↥(MaximalUnramifiedExtension l)) ((W⁻¹ : GL (Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l))
  have hPQ : P0 * Q0 = 1 := by
    simp only [P0, Q0]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_kronecker_one]
  have hQP : Q0 * P0 = 1 := by
    simp only [P0, Q0]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_kronecker_one]
  let p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l) := ⟨P0, Q0, hPQ, hQP⟩
  have hp : ∀ i m j k, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) (i, m) (j, k) =
      if i = j then (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k else 0 := by
    intro i m j k
    show P0 (i, m) (j, k) = _
    simp only [P0, Matrix.kronecker_apply, Matrix.one_apply]
    split_ifs <;> simp

  have hA : ∀ (i j : n) (k : Fin r), ∃ a : ↥(GK K) → Fin r → ℚ_[l], Continuous a ∧ ∀ g (m : Fin r),
      fr l m ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j * ω k) =
        ∑ k', (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k' * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (a g k') := by
    intro i j k
    refine hcoef ↥(GK K) (fun g => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j * ω k) (fun g => ?_) ?_
    · rw [map_mul, hσ.rat, hω]
    · show Continuous fun g => (((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) * ((ω k : ↥(MaximalUnramifiedExtension l)) : Om l)
      exact (hσ.cont i j).mul continuous_const
  choose A hAc hA using hA
  let T : ↥(GK K) → Matrix (n × Fin r) (n × Fin r) ℚ_[l] := fun g x y => A x.1 y.1 y.2 g x.2
  let B : ↥(GK K) → Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) := fun g =>
    Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m))
  have hB1 : B 1 = 1 := by
    simp only [B, map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.blockDiagonal_one
  have hBm : ∀ g h, B (g * h) = B g * B h := by
    intro g h
    simp only [B, map_mul, Units.val_mul, Matrix.map_mul]
    rw [Matrix.blockDiagonal_mul]
  have hT : ∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * (T g).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
      B g * p := by
    intro g
    refine Matrix.ext ?_
    rintro ⟨i, m⟩ ⟨j, k⟩
    rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [hp, B, T, Matrix.map_apply, Matrix.blockDiagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Fintype.sum_eq_single i (fun x hx => by simp [Ne.symm hx])]
    simp only [if_true]
    refine (show _ = ∑ x, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m x * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (A i j k g x)
      from rfl).trans ?_
    rw [← hA i j k g m, map_mul]
    symm
    simp [hW]
  obtain ⟨hT1, hTm⟩ := intertwine_mul (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)).injective
    B hB1 hBm p T hT
  let T' : ↥(GK K) →* Matrix (n × Fin r) (n × Fin r) ℚ_[l] :=
    { toFun := T, map_one' := hT1, map_mul' := hTm }
  refine ⟨T'.toHomUnits, p, ?_, ?_, ?_, ?_⟩
  · rintro ⟨i, k'⟩ ⟨j, k⟩
    exact (continuous_apply k').comp (hAc i j k)
  · rintro ⟨i, m⟩ ⟨j, k⟩
    apply hσ.le
    rw [hp]
    split_ifs
    · rw [hW]; exact fr_comm (hω k) m
    · exact map_zero _
  · intro g
    exact hT g
  · intro c hc hcc
    have hC : ∀ i : n, ∃ a : ↥(GK K) → Fin r → ℚ_[l], Continuous a ∧ ∀ g (m : Fin r),
        fr l m (c g i) = ∑ k, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (a g k) :=
      fun i => hcoef ↥(GK K) (fun g => c g i) (fun g => hc g i) (hcc i)
    choose a hac ha using hC
    refine ⟨fun g x => a x.1 g x.2, continuous_pi fun x => (continuous_apply x.2).comp (hac x.1), fun g => ?_⟩
    funext ⟨i, m⟩
    rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
    simp only [hp, ite_mul, zero_mul]
    rw [Fintype.sum_eq_single i (fun x hx => by simp [Ne.symm hx])]
    simp only [if_true]
    rw [ha i g m]

end GlobalTheory.PMon

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThetaDeRhamFiltrationAcris
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PSer TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PSer

open GlobalTheory.MemLoc GlobalTheory.MemLoc.TiedTheta

theorem theta_fil_acris : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    ∃ (S : Subring P.R.BdR) (θ : ↥S →+* ℂ_[l]) (Θ : Formalism.Per.Acris l →+* ℂ_[l]),
      (∀ x, x ∈ S ↔ x ∈ Fil P 0) ∧ (∀ x : ↥S, θ x = 0 ↔ (x : P.R.BdR) ∈ Fil P 1) ∧
      (∀ c : ℚ_[l], ∃ hm, θ ⟨algebraMap ℚ_[l] P.R.BdR c, hm⟩ = algebraMap ℚ_[l] ℂ_[l] c) ∧
      (∀ a, ‖Θ a‖ ≤ 1) ∧
      (∀ z : Formalism.Per.Fl l, Θ (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (Formalism.Per.tm z)) = sh z) ∧
      ∀ a : Formalism.Per.Acris l, ∃ hm, θ ⟨P.ιB (T.eB.symm (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) a)), hm⟩ = Θ a := by
  intro l _ P AI T
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  let S : Subring P.R.BdR := (algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l)).range.comap T.eD.toRingHom
  have hS : ∀ x, x ∈ S ↔ ∃ y : Formalism.Per.BdRp l, T.eD x = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) y := by
    intro x
    change (∃ y, _ = T.eD x) ↔ _
    exact exists_congr fun y => eq_comm
  have hF0 : ∀ x, x ∈ S ↔ x ∈ Fil P 0 := by
    intro x
    rw [hS]
    change _ ↔ x ∈ (P.PD (botExt l)).Fil 0
    rw [T.fil]
    constructor
    · rintro ⟨y, hy⟩
      rw [hy]
      exact TiedUnif.alg_mem_FilD_zero y
    · intro hx
      obtain ⟨y, hy⟩ := exists_of_mem_FilD_zero hx
      exact ⟨y, hy⟩
  let θ : ↥S →+* ℂ_[l] :=
    { toFun := fun x => thetaExt (T.eD x)
      map_one' := by
        change thetaExt (T.eD 1) = 1
        rw [map_one, ← map_one (algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l)), thetaExt_alg, map_one]
      map_mul' := fun x y => by
        obtain ⟨u, hu⟩ := (hS x).1 x.2
        obtain ⟨v, hv⟩ := (hS y).1 y.2
        change thetaExt (T.eD ((x : P.R.BdR) * y)) = thetaExt (T.eD x) * thetaExt (T.eD y)
        rw [map_mul, hu, hv, ← map_mul, thetaExt_alg, thetaExt_alg, thetaExt_alg, map_mul]
      map_zero' := by
        change thetaExt (T.eD 0) = 0
        rw [map_zero, ← map_zero (algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l)), thetaExt_alg, map_zero]
      map_add' := fun x y => by
        obtain ⟨u, hu⟩ := (hS x).1 x.2
        obtain ⟨v, hv⟩ := (hS y).1 y.2
        change thetaExt (T.eD ((x : P.R.BdR) + y)) = thetaExt (T.eD x) + thetaExt (T.eD y)
        rw [map_add (f := _), hu, hv, ← map_add (f := _), thetaExt_alg, thetaExt_alg, thetaExt_alg, map_add (f := _)] }
  have hθ : ∀ (x : ↥S) (y : Formalism.Per.BdRp l), T.eD x = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) y →
      θ x = Formalism.Per.θD l y := by
    intro x y h
    change thetaExt (T.eD x) = _
    rw [h, thetaExt_alg]
  let Θ : Formalism.Per.Acris l →+* ℂ_[l] := (Formalism.Per.θD l).comp C.j
  refine ⟨S, θ, Θ, hF0, fun x => ?_, fun c => ?_, fun a => FundOnto.norm_theta_j_le C a, fun z => ?_,
    fun a => ?_⟩
  · obtain ⟨u, hu⟩ := (hS x).1 x.2
    change θ x = 0 ↔ (x : P.R.BdR) ∈ (P.PD (botExt l)).Fil 1
    rw [T.fil, hu, hθ x u hu, (thetaD_props l).2.1]
    exact ((filD_laws l).2.2.2.2.2.2 1 u).symm
  · have e : algebraMap ℚ_[l] P.R.BdR c = algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l) c) :=
      IsScalarTower.algebraMap_apply _ _ _ _
    obtain ⟨y, hy, hy'⟩ := T.om (algebraMap ℚ_[l] (Om l) c)
    have hm : algebraMap ℚ_[l] P.R.BdR c ∈ S := by
      rw [hS, e]
      exact ⟨y, hy⟩
    refine ⟨hm, ?_⟩
    rw [hθ ⟨_, hm⟩ y (by rw [← hy]; exact congrArg T.eD e), hy']
    rfl
  · change Formalism.Per.θD l (C.j _) = _
    rw [FundOnto.theta_j_alg, FundOnto.theta_tm]
    rfl
  · have hm : P.ιB (T.eB.symm (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) a)) ∈ S := by
      rw [hS, hC.ι, RingEquiv.apply_symm_apply, C.ι_j]
      exact ⟨_, rfl⟩
    refine ⟨hm, hθ ⟨_, hm⟩ (C.j a) ?_⟩
    change T.eD (P.ιB _) = _
    rw [hC.ι, RingEquiv.apply_symm_apply, C.ι_j]

end GlobalTheory.PSer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteImageOfTrivialOnOpen
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

namespace GlobalTheory

theorem GK.finite_image_of_trivial_on_open :
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (Q : Type) [Group Q] (ρ : ↥(GK K) →* Q)
      (J H : Subgroup ↥(GK K)), IsOpen (H : Set ↥(GK K)) → (∀ g ∈ J, g ∈ H → ρ g = 1) →
      (ρ '' (J : Set ↥(GK K))).Finite := by
  intro l _ K Q _ ρ J H hH hρ
  haveI := _root_.GlobalTheory.OpenFiniteIndex.finiteIndex_of_isOpen l K H hH
  exact _root_.GlobalTheory.image_finite_of_trivial_on_inf_finiteIndex _ Q ρ J H inferInstance hρ

end GlobalTheory
end

