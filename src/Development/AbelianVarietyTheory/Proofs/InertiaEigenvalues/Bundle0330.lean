module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeSandwichAinf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0314
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnitOfUniUp
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0131

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeAinfSandwichInvertPi
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL Module

noncomputable section

namespace GlobalTheory.HWL.SandProof

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : WGam PD LL O v n s} {R : WSer Γ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {I : WIo R RA RW inclR φR gR πA} {Zl : Type} [CommRing Zl] {zl : PowerSeries Zl →+* LetA O n}

theorem jD_smulA (E : WEt I) (T : LocLat G Qp LL O) (a : LetA O n) (y : E.DD T) :
    E.jD T (a • y) = inclR (I.io a) • E.jD T y := by
  rw [← algebraMap_smul R.EE a y, E.jD_smul, I.ioE_ext]

theorem φD_smulA (E : WEt I) (T : LocLat G Qp LL O) (a : LetA O n) (y : E.DD T) :
    E.φD T (a • y) = letφ R.φ₀ a • E.φD T y := by
  rw [← algebraMap_smul R.EE a y, E.φD_smul, R.φE_ext, algebraMap_smul]

theorem φA_π (R : WSer Γ) : letφ (n := n) R.φ₀ letπ = letπ * (fun _ => R.q₀) := by
  funext i
  exact R.φ₀_X

theorem φA_one_add_π (R : WSer Γ) : letφ (n := n) R.φ₀ (1 + letπ) = (1 + letπ) ^ PD.p := by
  rw [map_add (f := _), map_one, φA_π]
  funext i
  have := R.q₀_def
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.one_apply, letπ]
  rw [this]; ring

theorem φA_pow_one_add_π (R : WSer Γ) (k : ℕ) :
    (letφ (n := n) R.φ₀ ^ k) (1 + letπ) = (1 + letπ) ^ (PD.p ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', AlgHom.mul_apply, ih, map_pow, φA_one_add_π, ← pow_mul, pow_succ']

theorem frobenius_inclusion_X_eq_mul_Q (I : WIo R RA RW inclR φR gR πA)
    (hu : φR (inclR (1 + πA)) = inclR (1 + πA) ^ PD.p) :
    φR (inclR ((1 + πA) ^ (PD.p ^ (s - 1)) - 1)) =
      inclR ((1 + πA) ^ (PD.p ^ (s - 1)) - 1) * inclR (I.io R.Q) := by
  have hX : (letφ (n := n) R.φ₀ ^ (s - 1)) letπ = (1 + letπ) ^ (PD.p ^ (s - 1)) - 1 := by
    rw [← φA_pow_one_add_π R, map_add (f := _), map_one]; ring
  have hXQ : (letφ (n := n) R.φ₀ ^ (s - 1)) letπ * R.Q =
      ((1 + letπ) ^ PD.p) ^ (PD.p ^ (s - 1)) - 1 := by
    rw [WSer.Q, ← map_mul, ← φA_π, ← pow_mul, mul_comm PD.p, pow_mul,
      ← φA_pow_one_add_π R, ← map_pow, ← φA_one_add_π R, map_add, map_one, map_add, map_one]
    ring
  have hπ : I.io (1 + letπ) = 1 + πA := by rw [map_add (f := _), map_one, I.io_π]
  have h1 : (1 + πA) ^ (PD.p ^ (s - 1)) - 1 = I.io ((letφ (n := n) R.φ₀ ^ (s - 1)) letπ) := by
    rw [hX, map_sub, map_pow, map_one, hπ]
  conv_rhs => rw [h1, ← map_mul, ← map_mul, hXQ]
  simp only [map_sub, map_pow, map_one, hπ, hu]

theorem uniform {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι] (q : A)
    (S : Submodule A M) (w : ι → M) (h : ∀ i, ∃ k : ℕ, q ^ k • w i ∈ S) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ i, q ^ k • w i ∈ S := by
  choose k hk using h
  refine ⟨Finset.univ.sup k, fun m hm i => ?_⟩
  have : k i ≤ m := (Finset.le_sup (Finset.mem_univ i)).trans hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le this
  rw [add_comm, pow_add, mul_smul]
  exact S.smul_mem _ (hk i)

theorem sand_of {E : WEt I} (Mo : WN E zl)
    (hA : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q RW) (P : Matrix p p RA)
      (P' : Matrix q q RA) (Y : Matrix p q RA),
      Z.map φR = P.map inclR * Z * P'.map inclR + Y.map inclR → ∀ a b, Z a b ∈ Set.range inclR)
    (x : RA) (hx : φR (inclR x) = inclR x * inclR (I.io R.Q)) [Nontrivial O]
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    (b : Basis (Fin (Module.finrank O ↥T.L.T)) (LetA O n) ↥(Mo.N T)) :
    ∃ m : ℕ, Sand Mo T (x ^ m) := by
  classical
  have : Module.Free O ↥T.L.T := T.L.free
  have : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  let tb := Module.finBasis O ↥T.L.T
  have hexp : ∀ y ∈ Mo.N T, ∃ c : Fin (Module.finrank O ↥T.L.T) → LetA O n,
      y = ∑ j, c j • (b j : E.DD T) := by
    intro y hy
    refine ⟨fun j => b.repr ⟨y, hy⟩ j, ?_⟩
    have := congrArg (Mo.N T).subtype (b.sum_repr ⟨y, hy⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    exact this.symm
  have hj : ∀ (c : Fin (Module.finrank O ↥T.L.T) → LetA O n)
      (w : Fin (Module.finrank O ↥T.L.T) → E.DD T),
      E.jD T (∑ j, c j • w j) = ∑ j, inclR (I.io (c j)) • E.jD T (w j) := by
    intro c w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => jD_smulA E T _ _
  have hsp : ⊤ ≤ Submodule.span RW (Set.range fun i => E.jD T (b i : E.DD T)) := by
    rw [← E.jD_span T, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    refine (Mo.N_base T hT).inductionOn y ?_ ?_ ?_
    · intro z
      obtain ⟨c, hc⟩ := hexp z.1 z.2
      change E.jD T z.1 ∈ _
      rw [hc, hj]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · intro e z hz
      rw [E.jD_smul]
      exact Submodule.smul_mem _ _ hz
    · intro z z' hz hz'
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hz hz'
  have hli : LinearIndependent RW fun i => E.jD T (b i : E.DD T) := by
    have hs := hsp
    rw [← Finsupp.range_linearCombination, top_le_iff, LinearMap.range_eq_top] at hs
    exact OrzechProperty.injective_of_surjective_of_injective _ _
      (Algebra.TensorProduct.basis RW tb).linearIndependent hs
  obtain ⟨k₁, h1⟩ := uniform R.Q (Mo.N T) (fun i => E.φD T (b i : E.DD T))
    (fun i => Mo.N_φ T _ (b i).2)
  obtain ⟨k₂, h2⟩ := uniform R.Q (Submodule.span (LetA O n) (E.φD T '' (Mo.N T : Set (E.DD T))))
    (fun i => (b i : E.DD T)) (fun i => Mo.N_φinv T _ (b i).2)
  replace h1 := h1 (max k₁ k₂) (le_max_left _ _)
  replace h2 := h2 (max k₁ k₂) (le_max_right _ _)
  refine ⟨max k₁ k₂, ?_⟩
  generalize max k₁ k₂ = m at h1 h2
  unfold Sand
  rw [map_pow]
  constructor
  · choose P hP using fun i => hexp _ (h1 i)
    have hup := GlobalTheory.Sandwich.upper tb inclR φR hA _ _ hx m (fun i => E.jD T (b i : E.DD T))
      (Matrix.of fun i j => I.io (P i j)) (by
        intro i
        have := congrArg (E.jD T) (hP i)
        rw [hj, jD_smulA, E.jD_φ, map_pow, map_pow] at this
        exact this)
    intro y hy
    obtain ⟨c, rfl⟩ := hexp y hy
    change _ ∈ LinearMap.range (TWincl inclR T)
    rw [hj, Finset.smul_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [smul_comm]
    exact GlobalTheory.Sandwich.incl_smul_mem inclR _ _ (hup j)
  · have hexp2 : ∀ y ∈ Submodule.span (LetA O n) (E.φD T '' (Mo.N T : Set (E.DD T))),
        ∃ c : Fin (Module.finrank O ↥T.L.T) → LetA O n,
        y = ∑ j, c j • E.φD T (b j : E.DD T) := by
      intro y hy
      have : Submodule.span (LetA O n) (E.φD T '' (Mo.N T : Set (E.DD T))) ≤ Submodule.span (LetA O n)
          (Set.range fun j => E.φD T (b j : E.DD T)) := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨c, rfl⟩ := hexp z hz
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Submodule.sum_mem _ fun j _ => ?_
        rw [φD_smulA]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp (this hy)
      exact ⟨c, hc.symm⟩
    choose U hU using fun i => hexp2 _ (h2 i)
    let nb : Basis (Fin (Module.finrank O ↥T.L.T)) RW (TW RW T) := Basis.mk hli hsp
    have hnb : ∀ i, nb i = E.jD T (b i : E.DD T) := fun i => Basis.mk_apply _ _ i
    have hlow := GlobalTheory.Sandwich.lower tb inclR φR hA _ _ hx m nb
      (Matrix.of fun i j => I.io (U i j)) (by
        intro i
        have := congrArg (E.jD T) (hU i)
        rw [hj, jD_smulA, map_pow, map_pow] at this
        simp only [E.jD_φ] at this
        simp only [hnb]
        exact this)
    intro t
    rw [← tb.sum_repr t, TensorProduct.tmul_sum, Finset.smul_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [TensorProduct.tmul_smul, smul_comm]
    refine Submodule.smul_mem _ _ ?_
    obtain ⟨c, hc⟩ := hlow k
    rw [hc]
    refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨c j, b j, (b j).2, ?_⟩
    rw [hnb]

end Generic

theorem εroot_pow_pred {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (k : ℕ) :
    AI.εroot (k + 1) ^ l ^ k = AI.ε1 := by
  induction k with
  | zero => simp [LocAinf.εroot, LocAinf.ε1]
  | succ k ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    exact ih

theorem x_eq {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (s : ℕ)
    (hs : 1 ≤ s) :
    ((1 : RA LL) + (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1)) ^ (l ^ (s - 1)) - 1 =
      (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] AI.π₁ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hs
  have h : (1 : RA LL) + (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot (k + 1)) - 1) =
      (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot (k + 1)) : Ainf l) := by
    rw [TensorProduct.tmul_sub, Algebra.TensorProduct.one_def]; abel
  rw [h, Algebra.TensorProduct.tmul_pow, one_pow, ← map_pow, Nat.add_sub_cancel, εroot_pow_pred,
    LocAinf.π₁, TensorProduct.tmul_sub, Algebra.TensorProduct.one_def]


set_option maxHeartbeats 1600000 in
theorem sandwich : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (E : WEt I) (Mo : NS E) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ → ∃ m : ℕ, Sand Mo T ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (AI.π₁ ^ m) : RA LL) := by
  intro l _ P AI K s LL hg Γ R I hI E Mo T hT
  obtain ⟨b⟩ := _root_.GlobalTheory.HWL.lattice_free l P AI K s LL hg Γ R I hI E Mo T hT
  have hp : (P.PD K).p = l := P.PD_p K
  have hx := frobenius_inclusion_X_eq_mul_Q I (by rw [hp]; exact GlobalTheory.Sandwich.φRW_teichmuller LL _)
  rw [hp, x_eq AI LL s Γ.s_pos] at hx
  obtain ⟨m, hm⟩ := sand_of Mo (GlobalTheory.FrobIntegralCoeff.frobenius_integrality_coeff l LL) _ hx T hT b
  refine ⟨m, ?_⟩
  have e : ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (AI.π₁ ^ m) : RA LL) = ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] AI.π₁ : RA LL) ^ m := by
    rw [Algebra.TensorProduct.tmul_pow, one_pow]
  rw [e]
  exact hm

end GlobalTheory.HWL.SandProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionHarishChandraInductionMul
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLq.WhMul

variable {g : ℕ} [Fact g.Prime]

theorem entN_mul_succ {n : ℕ} (M N : Mt g n) (hM : IsUniUp M) (hN : IsUniUp N) (k : ℕ) :
    entN (M * N) k (k + 1) = entN M k (k + 1) + entN N k (k + 1) := by
  unfold entN
  split_ifs with h
  · set i : Fin n := ⟨k, h.1⟩
    set j : Fin n := ⟨k + 1, h.2⟩
    have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
    rw [Matrix.mul_apply, Fintype.sum_eq_add i j hij]
    · rw [(hM i i).2 rfl, (hN j j).2 rfl, one_mul, mul_one, add_comm]
    · rintro c ⟨hci, hcj⟩
      by_cases hc : c < i
      · rw [(hM i c).1 hc, zero_mul]
      · have : j < c := by
          rw [Fin.lt_def] at hc ⊢
          have h1 : (c : ℕ) ≠ k := fun e => hci (Fin.ext e)
          have h2 : (c : ℕ) ≠ k + 1 := fun e => hcj (Fin.ext e)
          simp only [i, j] at hc ⊢
          omega
        rw [(hN c j).1 this, mul_zero]
  · simp only [add_zero]

theorem supFrom_mul {n : ℕ} (M N : Mt g n) (hM : IsUniUp M) (hN : IsUniUp N) :
    supFrom 0 (M * N) = supFrom 0 M + supFrom 0 N := by
  unfold supFrom
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => entN_mul_succ M N hM hN k

theorem supFrom_one (n : ℕ) : supFrom 0 (1 : Mt g n) = 0 := by
  unfold supFrom
  refine Finset.sum_eq_zero fun k _ => ?_
  unfold entN
  split_ifs with h
  · rw [Matrix.one_apply_ne]
    simp [Fin.ext_iff]
  · rfl

theorem tl_one (a b : ℕ) : tl a (1 : Mt g (a + b)) = 1 := by
  ext i j
  rw [ParBasic.tl_apply, Matrix.one_apply, Matrix.one_apply]
  simp [Fin.ext_iff]

theorem br_one (a b : ℕ) : br a b (1 : Mt g (a + b)) = 1 := by
  ext i j
  rw [ParBasic.br_apply, Matrix.one_apply, Matrix.one_apply]
  simp [Fin.ext_iff]

theorem wh_hcT : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (a b n : ℕ), n = a + b →
    ∀ Φ : Gn g a → Gn g b → ℂ, (∀ y, IsClass fun x => Φ x y) → (∀ x, IsClass (Φ x)) →
      wh ψ (hcT a b Φ n) = wh ψ (fun x => wh ψ (Φ x)) := by
  intro g _ ψ hψ a b n hn Φ hΦ1 hΦ2
  obtain ⟨⟨P, hP⟩, ⟨U, hU⟩, -, -, -, -⟩ := ParBasic.par_basic g a b n hn
  subst hn

  have hl : ∀ h ∈ U, ∀ x ∈ U, (fun x : Gn g (a + b) => (ψ (supFrom 0 (x : Mt g (a + b))))⁻¹) (h * x * h⁻¹) =
      (fun x : Gn g (a + b) => (ψ (supFrom 0 (x : Mt g (a + b))))⁻¹) x := by
    intro h hh x hx
    have hh' := (hU h).1 hh
    have hx' := (hU x).1 hx
    have hi' := (hU h⁻¹).1 (U.inv_mem hh)
    have e1 : supFrom 0 ((h : Mt g (a + b)) * ((h⁻¹ : Gn g (a + b)) : Mt g (a + b))) = 0 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, supFrom_one]
    rw [supFrom_mul _ _ hh' hi'] at e1
    have hxh := ParBasic.isUniUp_mul _ _ hh' hx'
    simp only [Units.val_mul]
    rw [supFrom_mul _ _ hxh hi', supFrom_mul _ _ hh' hx']
    congr 2
    linear_combination e1

  have hφ : ∀ k ∈ P, ∀ x ∈ P,
      (fun z : Gn g (a + b) => Φ (toG (tl a (z : Mt g (a + b)))) (toG (br a b (z : Mt g (a + b))))) (k * x * k⁻¹) =
      (fun z : Gn g (a + b) => Φ (toG (tl a (z : Mt g (a + b)))) (toG (br a b (z : Mt g (a + b))))) x := by
    intro k hk x hx
    have hk' := (hP k).1 hk
    have hx' := (hP x).1 hx
    have hi' := (hP k⁻¹).1 (P.inv_mem hk)
    have hkx := (hP (k * x)).1 (P.mul_mem hk hx)
    obtain ⟨uk, vk⟩ := ParBasic.isUnit_blocks k hk'
    obtain ⟨ux, vx⟩ := ParBasic.isUnit_blocks x hx'
    have m1 := ParBasic.blocks_mul _ _ hk' hi'
    have m2 := ParBasic.blocks_mul _ _ hk' hx'
    have m3 := ParBasic.blocks_mul _ _ hkx hi'
    have hkxk := (hP (k * x * k⁻¹)).1 (P.mul_mem (P.mul_mem hk hx) (P.inv_mem hk))
    obtain ⟨uc, vc⟩ := ParBasic.isUnit_blocks _ hkxk
    have e1 : ((k * x * k⁻¹ : Gn g (a + b)) : Mt g (a + b)) = (k : Mt g (a + b)) * (x : Mt g (a + b)) * ((k⁻¹ : Gn g (a + b)) : Mt g (a + b)) := by
      simp only [Units.val_mul]
    have e0 : (k : Mt g (a + b)) * ((k⁻¹ : Gn g (a + b)) : Mt g (a + b)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have iA : (((toG (tl a (k : Mt g (a + b))))⁻¹ : Gn g a) : Mt g a) = tl a ((k⁻¹ : Gn g (a + b)) : Mt g (a + b)) := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [OpenCell.coe_toG uk, ← m1.2.1, e0, tl_one]
    have iB : (((toG (br a b (k : Mt g (a + b))))⁻¹ : Gn g b) : Mt g b) = br a b ((k⁻¹ : Gn g (a + b)) : Mt g (a + b)) := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [OpenCell.coe_toG vk, ← m1.2.2, e0, br_one]
    have cA : toG (tl a ((k * x * k⁻¹ : Gn g (a + b)) : Mt g (a + b))) =
        toG (tl a (k : Mt g (a + b))) * toG (tl a (x : Mt g (a + b))) * (toG (tl a (k : Mt g (a + b))))⁻¹ := by
      apply Units.ext
      rw [OpenCell.coe_toG uc]
      simp only [Units.val_mul] at m3 ⊢
      rw [iA, OpenCell.coe_toG uk, OpenCell.coe_toG ux, m3.2.1, m2.2.1]
    have cB : toG (br a b ((k * x * k⁻¹ : Gn g (a + b)) : Mt g (a + b))) =
        toG (br a b (k : Mt g (a + b))) * toG (br a b (x : Mt g (a + b))) * (toG (br a b (k : Mt g (a + b))))⁻¹ := by
      apply Units.ext
      rw [OpenCell.coe_toG vc]
      simp only [Units.val_mul] at m3 ⊢
      rw [iB, OpenCell.coe_toG vk, OpenCell.coe_toG vx, m3.2.2, m2.2.2]
    show Φ _ _ = Φ _ _
    rw [cA, cB]
    have h1 := hΦ1 (toG (br a b (k : Mt g (a + b))) * toG (br a b (x : Mt g (a + b))) * (toG (br a b (k : Mt g (a + b))))⁻¹)
      (toG (tl a (x : Mt g (a + b)))) (toG (tl a (k : Mt g (a + b))))
    have h2 := hΦ2 (toG (tl a (x : Mt g (a + b)))) (toG (br a b (x : Mt g (a + b)))) (toG (br a b (k : Mt g (a + b))))
    simp only at h1 h2
    rw [h1, h2]
  set R : Finset (Equiv.Perm (Fin (a + b))) := Finset.univ.filter fun σ =>
    ∀ i j : Fin (a + b), i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j with hR
  have hRu : ∀ x : Gn g (a + b), ∃! σ, σ ∈ R ∧ ∃ h ∈ U, ∃ k ∈ P, x = h * pm g σ * k := by
    intro x
    obtain ⟨σ, ⟨hσ, u, p, hu, hp, hx⟩, huniq⟩ :=
      Shuffle.existsUnique_shuffle g a (a + b) (Nat.le_add_right a b) x
    refine ⟨σ, ⟨by simpa [hR] using hσ, u, (hU u).2 hu, p, (hP p).2 hp, hx⟩, ?_⟩
    rintro τ ⟨hτ, u', hu', p', hp', hx'⟩
    exact huniq τ ⟨by simpa [hR] using hτ, u', p', (hU u').1 hu', (hP p').1 hp', hx'⟩
  have M := mackey_doubleCoset_pairing (Gn g (a + b)) U P _ R (pm g) hRu
    (fun x : Gn g (a + b) => (ψ (supFrom 0 (x : Mt g (a + b))))⁻¹)
    (fun z : Gn g (a + b) => Φ (toG (tl a (z : Mt g (a + b)))) (toG (br a b (z : Mt g (a + b))))) hl hφ
  have cU : (Nat.card U : ℂ) = ((Finset.univ.filter fun u : Gn g (a + b) => IsUniUp (u : Mt g (a + b))).card : ℂ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [hU]
  have cP : (Nat.card P : ℂ) = ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [hP]
  refine Eq.trans ?_ (M.trans ?_)
  · rw [OpenCell.wh_eq, cU, cP, ← Finset.sum_filter]
    simp only [hU, hP]
    rfl
  obtain ⟨σ₀, h0⟩ : ∃ σ₀ : Equiv.Perm (Fin (a + b)),
      ∀ j : Fin (a + b), (σ₀ j : ℕ) = if (j : ℕ) < a then b + j else j - a := by
    let f : Fin (a + b) → Fin (a + b) := fun j =>
      ⟨if (j : ℕ) < a then b + j else j - a, by have := j.2; split_ifs <;> omega⟩
    have hf : Function.Injective f := by
      intro i j h
      have := i.2
      have := j.2
      simp only [f, Fin.mk.injEq] at h
      ext
      split_ifs at h <;> omega
    exact ⟨Equiv.ofBijective f hf.bijective_of_finite, fun j => rfl⟩
  have h0R : σ₀ ∈ R := by
    simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i j hij hb
    rw [Fin.lt_def] at hij ⊢
    rw [h0, h0]
    split_ifs <;> omega
  rw [Finset.sum_eq_single_of_mem σ₀ h0R]
  · simp only [hU, hP]
    exact OpenCell.openCell g ψ a b (a + b) σ₀ Φ rfl h0
  · intro σ hσ hne
    have hσ' : ∀ i j : Fin (a + b), i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j := by
      simpa [hR] using hσ
    have hnd : ¬ ∀ i j : Fin (a + b), (i : ℕ) < a → a ≤ (j : ℕ) → (σ j : ℕ) ≠ σ i + 1 := by
      intro h
      apply hne
      exact Equiv.ext fun j => Fin.ext (by rw [(shuffle_noDescent_iff_open a b (a + b) σ rfl hσ').1 h j, h0 j])
    push Not at hnd
    obtain ⟨i, j, hi, hj, hij⟩ := hnd
    simp only [hU, hP]
    rw [NonOpenCell.whittaker_term_eq_zero g ψ hψ a b (a + b) σ Φ i j rfl hi hj hij, mul_zero]

end GlobalTheory.GLq.WhMul
end

