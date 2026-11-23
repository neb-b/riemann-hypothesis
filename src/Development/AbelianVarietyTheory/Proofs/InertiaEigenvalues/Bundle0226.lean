module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionCocycleUniformizerPowSmulMem
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.TorsCoc

theorem exists_pow_smul_mem {LL : Type} [Field LL] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra O LL] [IsFractionRing O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    (T : Submodule O V) (hT : Submodule.span LL (T : Set V) = ⊤) (ϖ : O) (hϖ : Irreducible ϖ)
    (v : V) : ∃ k : ℕ, ∀ j, k ≤ j → (algebraMap O LL ϖ) ^ j • v ∈ T := by
  have hv : v ∈ Submodule.span LL (T : Set V) := hT ▸ Submodule.mem_top

  have up : ∀ (x : V) (k j : ℕ), k ≤ j → (algebraMap O LL ϖ) ^ k • x ∈ T →
      (algebraMap O LL ϖ) ^ j • x ∈ T := by
    intro x k j hkj hx
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hkj
    rw [pow_add, mul_comm, mul_smul, ← map_pow, algebraMap_smul]
    exact T.smul_mem _ hx
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, fun j _ => by rw [← map_pow, algebraMap_smul]; exact T.smul_mem _ hx⟩
  | zero => exact ⟨0, fun j _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨max a b, fun j hj => by
      rw [smul_add]
      exact T.add_mem (ha j (le_trans (le_max_left _ _) hj)) (hb j (le_trans (le_max_right _ _) hj))⟩
  | smul a x _ hx =>
    obtain ⟨k, hk⟩ := hx
    obtain ⟨b, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := O) a
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖ
    refine ⟨n + k, fun j hj => up _ (n + k) j hj ?_⟩
    have key : (algebraMap O LL ϖ) ^ n * (algebraMap O LL b / algebraMap O LL s) =
        algebraMap O LL (b * ((u⁻¹ : Oˣ) : O)) := by
      have hsne : algebraMap O LL s ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
      rw [mul_div_assoc', div_eq_iff hsne, hu]
      simp only [map_mul, map_pow]
      have hu1 : algebraMap O LL ((u⁻¹ : Oˣ) : O) * algebraMap O LL (u : O) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      linear_combination (-(algebraMap O LL b * algebraMap O LL ϖ ^ n)) * hu1
    have e : (algebraMap O LL ϖ) ^ (n + k) • ((algebraMap O LL b / algebraMap O LL s) • x) =
        ((algebraMap O LL ϖ) ^ n * (algebraMap O LL b / algebraMap O LL s)) •
          ((algebraMap O LL ϖ) ^ k • x) := by
      rw [pow_add, mul_smul, mul_smul, smul_comm (algebraMap O LL b / algebraMap O LL s)]
    rw [e, key, algebraMap_smul]
    exact T.smul_mem _ (hk k le_rfl)

theorem cocycle_pow_smul_mem : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL]
    [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL],
    GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ)
    (ϖ : O), Irreducible ϖ → ∀ c ∈ divisibleCocycles LA', ∃ r : ℕ, ∀ g,
    (algebraMap O LL ϖ) ^ r • liftD LA' (c g) ∈ LA'.T := by
  intro l _ K LL _ _ _ O _ _ hO A' LA' ϖ hϖ c hc
  obtain ⟨⟨hD, hDVR, hFR⟩, -⟩ := hO
  haveI : CompactSpace ↥(GK K) := by
    haveI := K.2
    exact isCompact_iff_compactSpace.1 (InfiniteGalois.fixingSubgroup_isClosed K.1).isCompact
  have hfin : (Set.range c).Finite := hc.1.range_finite
  choose f hf using fun y : A'.V ⧸ LA'.T =>
    exists_pow_smul_mem LA'.T LA'.span ϖ hϖ (liftD LA' y)
  refine ⟨hfin.toFinset.sup f, fun g => hf (c g) _ ?_⟩
  exact Finset.le_sup (f := f) (hfin.mem_toFinset.2 ⟨g, rfl⟩)

end GlobalTheory.TorsCoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentDevissageCommRing
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open Filter Topology

namespace GlobalTheory

theorem continuous_adicModule_span_iff {R M G : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace G] (a : R) (f : G → M) :
    @Continuous G M _ ((Ideal.span {a}).adicModuleTopology M) f ↔
      ∀ (g₀ : G) (n : ℕ), ∀ᶠ g in 𝓝 g₀, ∃ y : M, f g = f g₀ + a ^ n • y := by
  letI : TopologicalSpace M := (Ideal.span {a}).adicModuleTopology M
  have hmem : ∀ (n : ℕ) (x : M), x ∈ ((Ideal.span {a}) ^ n • (⊤ : Submodule R M)) ↔
      ∃ y : M, a ^ n • y = x := by
    intro n x
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    simp
  have hb := fun x₀ : M => (@ModuleFilterBasis.toAddGroupFilterBasis R M _
    (Ideal.span {a}).adic_basis.topology _ _
    ((Ideal.span {a}).ringFilterBasis.moduleFilterBasis
      ((Ideal.span {a}).adic_module_basis M))).nhds_hasBasis x₀
  rw [continuous_iff_continuousAt]
  refine forall_congr' fun g₀ => ?_
  refine ((hb (f g₀)).tendsto_right_iff).trans ?_
  constructor
  · intro h n
    filter_upwards [h _ ⟨n, rfl⟩] with g hg
    obtain ⟨y, hy, hy'⟩ := hg
    obtain ⟨z, rfl⟩ := (hmem n y).1 hy
    exact ⟨z, hy'.symm⟩
  · rintro h _ ⟨n, rfl⟩
    filter_upwards [h n] with g hg
    obtain ⟨z, hz⟩ := hg
    exact ⟨a ^ n • z, (hmem n _).2 ⟨z, rfl⟩, hz.symm⟩

theorem torsionExponent_devissage_commRing {R G X X' X'' : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup X] [Module R X] [AddCommGroup X'] [Module R X'] [AddCommGroup X''] [Module R X'']
    (a : R) (htf : ∀ (n : ℕ) (z : X''), a ^ n • z = 0 → z = 0)
    (ρ : Representation R G X) (ρ' : Representation R G X') (ρ'' : Representation R G X'')
    (i : X' →ₗ[R] X) (p : X →ₗ[R] X'') (r' r'' : R)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p)
    (hiρ : ∀ g x, i (ρ' g x) = ρ g (i x)) (hpρ : ∀ g x, p (ρ g x) = ρ'' g (p x))
    (hc : ∀ x, @Continuous G X _ ((Ideal.span {a}).adicModuleTopology X) fun g => ρ g x)
    (h0 : ∀ z, (∀ g, ρ'' g z = z) → ∃ (k : ℕ) (x : X), (∀ g, ρ g x = x) ∧ p x = a ^ k • z)
    (h' : @TorsKilledBy R G X' _ _ _ _ _ ((Ideal.span {a}).adicModuleTopology X') ρ' a r')
    (h'' : @TorsKilledBy R G X'' _ _ _ _ _ ((Ideal.span {a}).adicModuleTopology X'') ρ'' a r'') :
    @TorsKilledBy R G X _ _ _ _ _ ((Ideal.span {a}).adicModuleTopology X) ρ a (r' * r'') := by
  rintro f ⟨hfc, hf⟩ ⟨k, x, hx⟩
  rw [continuous_adicModule_span_iff] at hfc
  simp only [Pi.smul_apply] at hx

  obtain ⟨z'', hz''⟩ := h'' (fun g => p (f g)) ⟨by
      rw [continuous_adicModule_span_iff]
      intro g₀ n
      filter_upwards [hfc g₀ n] with g hg
      obtain ⟨y, hy⟩ := hg
      exact ⟨p y, by rw [hy, map_add (f := _), map_smul]⟩,
    fun g h => by simp only [hf, map_add (f := _), hpρ]⟩
    ⟨k, p x, fun g => by rw [Pi.smul_apply, ← map_smul, hx, map_sub, hpρ]⟩
  obtain ⟨z, rfl⟩ := hp z''
  simp only [Pi.smul_apply] at hz''
  have hex' : ∀ g, ∃ y, i y = r'' • f g - (ρ g z - z) := fun g =>
    (hex _).1 (by rw [map_sub, map_smul, hz'', map_sub, hpρ, sub_self])
  choose f' hf' using hex'
  have hcoc : @IsCoc R G X' _ _ _ _ _ ((Ideal.span {a}).adicModuleTopology X') ρ' f' := by
    refine ⟨?_, fun g h => hi ?_⟩
    · rw [continuous_adicModule_span_iff]
      intro g₀ n
      filter_upwards [hfc g₀ n, (continuous_adicModule_span_iff a _).1 (hc z) g₀ n] with g hg hg'
      obtain ⟨y, hy⟩ := hg
      obtain ⟨w, hw⟩ := hg'
      have h1 : i (f' g) = i (f' g₀) + a ^ n • (r'' • y - w) := by
        rw [hf', hf', hy, hw]; module
      have h2 : p (r'' • y - w) = 0 := by
        apply htf n
        have := congrArg p h1
        rwa [map_add, hex.apply_apply_eq_zero, hex.apply_apply_eq_zero, zero_add, map_smul,
          eq_comm] at this
      obtain ⟨u, hu⟩ := (hex _).1 h2
      exact ⟨u, hi (by rw [h1, map_add (f := _), map_smul, hu])⟩
    · rw [map_add (f := _), hiρ, hf', hf', hf', hf, map_mul]
      simp only [Module.End.mul_apply, map_sub, map_smul]
      module

  have hw : ∀ g, i (a ^ k • f' g) = ρ g (r'' • x - a ^ k • z) - (r'' • x - a ^ k • z) := by
    intro g
    rw [map_smul, hf', smul_sub, smul_comm, hx]
    simp only [map_sub, map_smul]
    module
  obtain ⟨k', x₀, hx₀, hpx₀⟩ := h0 (p (r'' • x - a ^ k • z)) (fun g => by
    rw [← hpρ, ← sub_eq_zero, ← map_sub, ← hw, hex.apply_apply_eq_zero])
  obtain ⟨w', hw'⟩ := (hex (a ^ k' • (r'' • x - a ^ k • z) - x₀)).1
    (by rw [map_sub, map_smul, hpx₀, sub_self])
  obtain ⟨u, hu⟩ := h' f' hcoc ⟨k' + k, w', fun g => hi (by
    rw [Pi.smul_apply, pow_add, mul_smul, map_smul, hw, map_sub i, hiρ, hw', map_sub (ρ g) _ x₀,
      hx₀, map_smul (ρ g) (a ^ k')]
    module)⟩
  refine ⟨i u + r' • z, fun g => ?_⟩
  have := congrArg i (hu g)
  rw [Pi.smul_apply, map_smul, hf', map_sub, hiρ] at this
  rw [Pi.smul_apply, map_add (f := _), map_smul]
  linear_combination (norm := module) this

theorem torsKilledBy_devissage : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] [NoZeroSMulDivisors ℤ_[l] X] [IsAdicComplete (Ideal.span {(l : ℤ_[l])}) X] (X' : Type) [AddCommGroup X'] [Module ℤ_[l] X'] [NoZeroSMulDivisors ℤ_[l] X'] [IsAdicComplete (Ideal.span {(l : ℤ_[l])}) X'] (X'' : Type) [AddCommGroup X''] [Module ℤ_[l] X''] [NoZeroSMulDivisors ℤ_[l] X''] [IsAdicComplete (Ideal.span {(l : ℤ_[l])}) X''] (ρ : Representation ℤ_[l] G X) (ρ' : Representation ℤ_[l] G X') (ρ'' : Representation ℤ_[l] G X'') (i : X' →ₗ[ℤ_[l]] X) (p : X →ₗ[ℤ_[l]] X'') (c' c'' : ℕ), letI : TopologicalSpace X := (Ideal.span {(l : ℤ_[l])}).adicModuleTopology X; letI : TopologicalSpace X' := (Ideal.span {(l : ℤ_[l])}).adicModuleTopology X'; letI : TopologicalSpace X'' := (Ideal.span {(l : ℤ_[l])}).adicModuleTopology X''; Function.Injective i → Function.Surjective p → Function.Exact i p → (∀ g x, i (ρ' g x) = ρ g (i x)) → (∀ g x, p (ρ g x) = ρ'' g (p x)) → (∀ x, Continuous fun g => ρ g x) → (∀ z, (∀ g, ρ'' g z = z) → ∃ (k : ℕ) (x : X), (∀ g, ρ g x = x) ∧ p x = (l : ℤ_[l]) ^ k • z) → TorsKilledBy ρ' (l : ℤ_[l]) ((l : ℤ_[l]) ^ c') → TorsKilledBy ρ'' (l : ℤ_[l]) ((l : ℤ_[l]) ^ c'') → TorsKilledBy ρ (l : ℤ_[l]) ((l : ℤ_[l]) ^ (c' + c'')) := by
  intro l _ G _ _ _ _ _ X _ _ _ _ X' _ _ _ _ X'' _ _ _ _ ρ ρ' ρ'' i p c' c''
  intro hi hp hex hiρ hpρ hc h0 h' h''
  rw [pow_add]
  refine torsionExponent_devissage_commRing (l : ℤ_[l]) ?_ ρ ρ' ρ'' i p _ _ hi hp hex hiρ hpρ hc h0 h' h''
  intro n z hz
  have hl : ((l : ℤ_[l]) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  exact (NoZeroSMulDivisors.eq_zero_or_eq_zero_of_smul_eq_zero hz).resolve_left hl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivCrysJumpZero
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.TrivCrys

section Coord

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
  {ι : Type} [Fintype ι] (b : Basis ι F V)

def crd (i : ι) (N : Type) [AddCommGroup N] [Module F N] : V ⊗[F] N →ₗ[F] N :=
  (TensorProduct.lid F N).toLinearMap ∘ₗ (b.coord i).rTensor N

variable {N N' : Type} [AddCommGroup N] [Module F N] [AddCommGroup N'] [Module F N']

theorem crd_tmul (i : ι) (v : V) (n : N) : crd b i N (v ⊗ₜ n) = b.coord i v • n := by
  simp [crd]

theorem sum_crd (x : V ⊗[F] N) : ∑ i, b i ⊗ₜ[F] crd b i N x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v n =>
    simp only [crd_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, Basis.coord_apply,
      b.sum_repr]
  | add x y hx hy =>
    simp only [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]

theorem eq_zero_of_crd (x : V ⊗[F] N) (h : ∀ i, crd b i N x = 0) : x = 0 := by
  rw [← sum_crd b x]; simp [h]

variable {LL : Type} [Field LL] [Algebra F LL] [Module LL V] [IsScalarTower F LL V]

theorem crd_map (h : V →ₗ[LL] V) (hh : ∀ v, h v = v) (f : N →ₗ[F] N') (i : ι) (x : V ⊗[F] N) :
    crd b i N' (AlgebraTensorModule.map h f x) = f (crd b i N x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v n => simp [crd_tmul, hh]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end Coord

section Period

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem fil_mono {a c : ℤ} (h : a ≤ c) : PD.Fil c ≤ PD.Fil a := by
  exact antitone_int_of_succ_le PD.Fil_anti h

theorem nontrivial_B (PD : PeriodData G Qp K₀ K B BdR) : Nontrivial B := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact PD.not_mem_filtration_two (by rw [Subsingleton.elim PD.t 0, map_zero]; exact zero_mem _)

theorem const_not_fil (a : ℤ) (ha : 1 ≤ a) (c : K) (hc : algebraMap K BdR c ∈ PD.Fil a) : c = 0 := by
  by_contra h0
  have h1 : (1 : BdR) ∈ PD.Fil 1 := by
    have := (PD.Fil a).smul_mem c⁻¹ hc
    rw [Algebra.smul_def, ← map_mul, inv_mul_cancel₀ h0, map_one] at this
    exact fil_mono PD ha this
  have := PD.Fil_mul 1 1 _ _ PD.mem_filtration_one h1
  rw [mul_one] at this
  exact PD.not_mem_filtration_two this

variable {ρ}

theorem actVB_triv (hρ : ∀ g x, ρ g x = x) (g : G) (x : V ⊗[Qp] B) {ι : Type} [Fintype ι] (b : Basis ι Qp V) (i : ι) :
    crd b i B (actVB PD ρ g x) = PD.actB g (crd b i B x) := by
  unfold actVB
  rw [crd_map b (ρ g) (hρ g)]
  rfl

theorem actVdR_triv (hρ : ∀ g x, ρ g x = x) (g : G) (x : V ⊗[Qp] BdR) {ι : Type} [Fintype ι] (b : Basis ι Qp V) (i : ι) :
    crd b i BdR (actVdR PD ρ g x) = PD.actdR g (crd b i BdR x) := by
  unfold actVdR
  rw [crd_map b (ρ g) (hρ g)]
  rfl

theorem crd_Dcris (hρ : ∀ g x, ρ g x = x) {ι : Type} [Fintype ι] (b : Basis ι Qp V) {x : V ⊗[Qp] B}
    (hx : x ∈ Dcris PD ρ) (i : ι) : ∃ c : K₀, algebraMap K₀ B c = crd b i B x := by
  apply PD.invB
  intro g
  have hg : actVB PD ρ g x = x := by
    have := (Submodule.mem_iInf _).1 hx g
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    exact this
  rw [← actVB_triv PD hρ g x b i, hg]

theorem crd_DdR (hρ : ∀ g x, ρ g x = x) {ι : Type} [Fintype ι] (b : Basis ι Qp V) {x : V ⊗[Qp] BdR}
    (hx : x ∈ DdR PD ρ) (i : ι) : ∃ c : K, algebraMap K BdR c = crd b i BdR x := by
  apply PD.invdR
  intro g
  have hg : actVdR PD ρ g x = x := by
    have := (Submodule.mem_iInf _).1 hx g
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    exact this
  rw [← actVdR_triv PD hρ g x b i, hg]

end Period

section Period2

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {ρ : Representation LL G V}

def jK₀ (PD : PeriodData G Qp K₀ K B BdR) : V ⊗[Qp] K₀ →ₗ[LL] V ⊗[Qp] B :=
  AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((Algebra.linearMap K₀ B).restrictScalars Qp)

theorem jK₀_injective [Module.Finite Qp V] : Function.Injective (jK₀ PD (LL := LL) (V := V)) := by
  haveI := nontrivial_B PD
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  let b := Module.finBasis Qp V
  apply eq_zero_of_crd b y
  intro i
  have h := congrArg (crd b i B) hy
  rw [jK₀, crd_map b _ (fun _ => rfl), map_zero] at h
  exact (algebraMap K₀ B).injective (by simpa using h)

theorem Dcris_eq_range [Module.Finite Qp V] (hρ : ∀ g x, ρ g x = x) :
    Dcris PD ρ = LinearMap.range (jK₀ PD (LL := LL) (V := V)) := by
  apply le_antisymm
  · intro x hx
    let b := Module.finBasis Qp V
    choose c hc using fun i => crd_Dcris PD hρ b hx i
    refine ⟨∑ i, b i ⊗ₜ[Qp] c i, ?_⟩
    conv_rhs => rw [← sum_crd b x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [jK₀, AlgebraTensorModule.map_tmul, ← hc i]
    rfl
  · rintro _ ⟨y, rfl⟩
    refine (Submodule.mem_iInf _).2 fun g => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v c => simp [jK₀, actVB, hρ]
    | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz]

theorem finrank_tensor [FiniteDimensional LL V] [FiniteDimensional Qp K₀] :
    finrank LL (V ⊗[Qp] K₀) = finrank LL V * finrank Qp K₀ := by
  rw [finrank_eq_card_basis ((Module.finBasis LL V).tensorProduct (Module.finBasis Qp K₀)),
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

theorem isCrys_triv [FiniteDimensional LL V] [Module.Finite Qp V] (hρ : ∀ g x, ρ g x = x) :
    IsCrys PD ρ := by
  haveI := PD.finK₀
  unfold IsCrys
  rw [Dcris_eq_range PD hρ, ← (LinearEquiv.ofInjective _ (jK₀_injective PD)).finrank_eq,
    finrank_tensor, mul_comm]

theorem DdR_le_FilV [Module.Finite Qp V] (hρ : ∀ g x, ρ g x = x) {a : ℤ} (ha : a ≤ 0) :
    DdR PD ρ ≤ FilV PD (LL := LL) (V := V) a := by
  intro x hx
  let b := Module.finBasis Qp V
  choose c hc using fun i => crd_DdR PD hρ b hx i
  have hmem : ∀ i, crd b i BdR x ∈ (PD.Fil a).restrictScalars Qp := fun i => by
    rw [← hc i, Submodule.restrictScalars_mem, Algebra.algebraMap_eq_smul_one]
    exact fil_mono PD ha ((PD.Fil 0).smul_mem _ PD.one_mem)
  refine ⟨∑ i, b i ⊗ₜ[Qp] (⟨crd b i BdR x, hmem i⟩ : (PD.Fil a).restrictScalars Qp), ?_⟩
  conv_rhs => rw [← sum_crd b x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  rfl

theorem DdR_inf_FilV [Module.Finite Qp V] (hρ : ∀ g x, ρ g x = x) {a : ℤ} (ha : 1 ≤ a) :
    DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, y, rfl⟩
  rw [Submodule.mem_bot]
  let b := Module.finBasis Qp V
  apply eq_zero_of_crd b
  intro i
  obtain ⟨c, hc⟩ := crd_DdR PD hρ b hx i
  have hy := crd_map b (LinearMap.id : V →ₗ[LL] V) (fun _ => rfl)
    ((PD.Fil a).restrictScalars Qp).subtype i y
  rw [hy] at hc ⊢
  have hcm : algebraMap K BdR c ∈ PD.Fil a := by
    rw [hc]; exact (crd b i _ y).2
  rw [← hc, const_not_fil PD a ha c hcm, map_zero]

theorem jump_triv [Module.Finite Qp V] (hρ : ∀ g x, ρ g x = x) (τ : K →ₐ[Qp] LL) (a : ℤ)
    (h : IsJumpV PD ρ τ a) : a = 0 := by
  by_contra h0
  apply h
  unfold FildR
  rcases lt_or_gt_of_ne h0 with hlt | hgt
  · have hle : DdRE PD ρ τ ≤ DdR PD ρ := inf_le_left
    rw [inf_eq_left.2 (hle.trans (DdR_le_FilV PD hρ (by omega))),
      inf_eq_left.2 (hle.trans (DdR_le_FilV PD hρ (by omega)))]
  · have hle : ∀ c : ℤ, 1 ≤ c → DdRE PD ρ τ ⊓ FilV PD (LL := LL) (V := V) c = ⊥ := fun c hc =>
      eq_bot_iff.2 ((inf_le_inf_right _ inf_le_left).trans (DdR_inf_FilV PD hρ hc).le)
    rw [hle _ (by omega), hle _ (by omega)]

end Period2

end GlobalTheory.TrivCrys

namespace GlobalTheory.TrivCrys

theorem triv_crys_jump_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), (∀ g x, ρ g x = x) → IsCrys (P.PD K) ρ ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV (P.PD K) ρ τ a → a = 0 := by
  intro l _ P AI _ K LL V _ _ _ _ _ ρ hρ
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI : Module.Finite ℚ_[l] V := Module.Finite.trans ↥LL.1 V
  exact ⟨isCrys_triv (P.PD K) hρ, fun τ a h => jump_triv (P.PD K) hρ τ a h⟩

end GlobalTheory.TrivCrys
end
end

