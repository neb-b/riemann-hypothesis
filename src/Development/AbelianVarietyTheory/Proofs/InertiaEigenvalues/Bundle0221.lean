module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionLatticeFullDescends
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTorsionCocycleFiniteLevelLift
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TorsionLevel

theorem exists_cocycle_level : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ) (ϖ : O), Irreducible ϖ → ∀ c ∈ divisibleCocycles LA', c ∉ BD LA' → ∀ r : ℕ, (∀ g, (algebraMap O LL ϖ) ^ r • liftD LA' (c g) ∈ LA'.T) → ∀ n : ℕ, r ≤ n → ∀ hI' : StableSub LA' (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA'.T), ∃ c' ∈ quotientCocycles LA' _ hI', c' ∉ BQ LA' _ hI' ∧ ∀ h, ∃ t ∈ LA'.T, Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' h) = (algebraMap O LL ϖ) ^ n • liftD LA' (c h) + (algebraMap O LL ϖ) ^ n • t := by
  intro l _ K LL _ _ _ O _ _ hgood A' LA' ϖ hϖ c hc hcB r hr n hn hI'
  classical
  obtain ⟨⟨_, _, _⟩, -⟩ := hgood
  set p0 : LL := algebraMap O LL ϖ with hp0
  have hp0ne : p0 ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O LL)).mpr hϖ.ne_zero
  have memI : ∀ x : ↥LA'.T, x ∈ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA'.T) ↔
      ∃ y : ↥LA'.T, ϖ ^ n • y = x := by
    intro x
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    simp
  have smulp : ∀ (j : ℕ) (w : A'.V), p0 ^ j • w = ϖ ^ j • w := by
    intro j w; rw [hp0, ← map_pow, algebraMap_smul]
  have hmem : ∀ g, p0 ^ n • liftD LA' (c g) ∈ LA'.T := by
    intro g
    have : p0 ^ n • liftD LA' (c g) = ϖ ^ (n - r) • (p0 ^ r • liftD LA' (c g)) := by
      rw [← smulp, smul_smul, ← pow_add, Nat.sub_add_cancel hn]
    rw [this]; exact LA'.T.smul_mem _ (hr g)
  have hlift : ∀ v : A'.V ⧸ LA'.T, Submodule.Quotient.mk (p := LA'.T) (liftD LA' v) = v :=
    fun v => (Submodule.Quotient.mk_surjective _ v).choose_spec
  let F : A'.V ⧸ LA'.T → ↥LA'.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA'.T) := fun v =>
    if h : p0 ^ n • liftD LA' v ∈ LA'.T then Submodule.Quotient.mk ⟨_, h⟩ else 0
  have hc' : ∀ g, (F ∘ c) g = Submodule.Quotient.mk ⟨_, hmem g⟩ := by
    intro g; simp only [F, Function.comp_apply, dif_pos (hmem g)]
  refine ⟨fun g => Submodule.Quotient.mk ⟨_, hmem g⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · have : (fun g => (Submodule.Quotient.mk ⟨_, hmem g⟩ :
        ↥LA'.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA'.T))) = F ∘ c :=
      funext fun g => (hc' g).symm
    rw [this]; exact hc.1.comp F
  · intro g h
    simp only
    rw [actQ, Submodule.mapQ_apply, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq, memI]
    have hd : liftD LA' (c (g * h)) - liftD LA' (c g) - A'.ρ g (liftD LA' (c h)) ∈ LA'.T := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub,
        hlift, hlift, hc.2 g h]
      have : Submodule.Quotient.mk (p := LA'.T) (A'.ρ g (liftD LA' (c h))) = actD LA' g (c h) := by
        conv_rhs => rw [← hlift (c h)]
        rfl
      rw [this]; abel
    refine ⟨⟨_, hd⟩, Subtype.ext ?_⟩
    rw [Submodule.coe_smul, ← smulp]
    show p0 ^ n • (liftD LA' (c (g * h)) - liftD LA' (c g) - A'.ρ g (liftD LA' (c h))) =
      p0 ^ n • liftD LA' (c (g * h)) - (p0 ^ n • liftD LA' (c g) + A'.ρ g (p0 ^ n • liftD LA' (c h)))
    rw [map_smul, smul_sub, smul_sub]; abel
  · rintro ⟨x, hx⟩
    apply hcB
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine ⟨Submodule.Quotient.mk ((p0 ^ n)⁻¹ • (t : A'.V)), funext fun g => ?_⟩
    have hxg := congrFun hx g
    simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply] at hxg ⊢
    change Submodule.Quotient.mk (actT LA' g t) - Submodule.Quotient.mk t = _ at hxg
    rw [← Submodule.Quotient.mk_sub, Submodule.Quotient.eq, memI] at hxg
    obtain ⟨s, hs⟩ := hxg
    have key : A'.ρ g (t : A'.V) - t - p0 ^ n • liftD LA' (c g) = p0 ^ n • (s : A'.V) := by
      rw [smulp n (s : A'.V)]
      have := congrArg Subtype.val hs
      rw [Submodule.coe_smul] at this
      rw [this]; rfl
    conv_rhs => rw [← hlift (c g)]
    change Submodule.Quotient.mk (p := LA'.T) (A'.ρ g ((p0 ^ n)⁻¹ • (t : A'.V))) - _ = _
    rw [← Submodule.Quotient.mk_sub, Submodule.Quotient.eq]
    have : (A'.ρ g) ((p0 ^ n)⁻¹ • (t : A'.V)) - (p0 ^ n)⁻¹ • (t : A'.V) - liftD LA' (c g) = s := by
      apply smul_right_injective A'.V (pow_ne_zero n hp0ne)
      simp only [map_smul, ← smul_sub]
      rw [smul_sub, smul_inv_smul₀ (pow_ne_zero n hp0ne), key]
    rw [this]; exact s.2
  · intro h
    have key : ∀ x q : ↥LA'.T,
        Submodule.Quotient.mk (p := (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA'.T)) q =
          Submodule.Quotient.mk x → ∃ t ∈ LA'.T, (q : A'.V) = (x : A'.V) + p0 ^ n • t := by
      intro x q hq
      rw [Submodule.Quotient.eq, memI] at hq
      obtain ⟨y, hy⟩ := hq
      refine ⟨y, y.2, ?_⟩
      rw [smulp n (y : A'.V), ← Submodule.coe_smul, hy, Submodule.coe_sub]; abel
    exact key _ _ (Submodule.Quotient.mk_surjective _ _).choose_spec

end GlobalTheory.TorsionLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittTiltLatticeTensorCancel
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL

theorem exists_cancel_tensor {R O A T : Type} [CommRing R] [CommRing O] [CommRing A] [Algebra R O]
    [Algebra R A] [AddCommGroup T] [Module O T] [Module R T] [IsScalarTower R O T] :
    ∃ κ : (A ⊗[R] T) ≃+ ((O ⊗[R] A) ⊗[O] T), ∀ (w : A) (t : T),
      κ (w ⊗ₜ[R] t) = ((1 : O) ⊗ₜ[R] w) ⊗ₜ[O] t := by
  haveI : SMulCommClass R O T := IsScalarTower.to_smulCommClass
  refine ⟨(TensorProduct.comm R A T).toAddEquiv.trans
    (((TensorProduct.AlgebraTensorModule.cancelBaseChange R O O T A).symm.toAddEquiv).trans
      (TensorProduct.comm O T (O ⊗[R] A)).toAddEquiv), fun w t => ?_⟩
  simp

theorem exists_cancel_tensor_compHom (R O A T : Type) [CommRing R] [CommRing O] [CommRing A] [Algebra R O]
    [Algebra R A] [AddCommGroup T] [Module O T] :
    letI : Module R T := Module.compHom T (algebraMap R O)
    ∃ κ : (A ⊗[R] T) ≃+ ((O ⊗[R] A) ⊗[O] T), ∀ (w : A) (t : T),
      κ (w ⊗ₜ[R] t) = ((1 : O) ⊗ₜ[R] w) ⊗ₜ[O] t := by
  letI : Module R T := Module.compHom T (algebraMap R O)
  haveI : IsScalarTower R O T := IsScalarTower.of_compHom R O T
  exact exists_cancel_tensor

theorem exists_kappa : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), letI := Formalism.MainNotions.LocalSituation.zlMod LL T; ∃ κ : (WCb l ⊗[ℤ_[l]] ↥T.L.T) ≃+ TW (RW LL) T, ∀ (w : WCb l) (t : ↥T.L.T), κ (w ⊗ₜ[ℤ_[l]] t) = TensorProduct.tmul ↥(OL LL) ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w : RW LL) t := by
  intro l _ K LL T
  exact exists_cancel_tensor_compHom ℤ_[l] ↥(OL LL) (WCb l) ↥T.L.T

end GlobalTheory.HWL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankPeriodFunctorCoeffBaseChange
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CoeffBC

section General

variable {L L' : Type} [Field L] [Field L'] [Algebra L L'] {ι : Type} [Fintype ι] [DecidableEq ι]
  {M M' : Type} [AddCommGroup M] [Module L M] [AddCommGroup M'] [Module L' M'] [Module L M']
  {N N' : Type} [AddCommGroup N] [Module L N] [AddCommGroup N'] [Module L' N'] [Module L N']

def IsCoord (u : ι → L') (J : M →ₗ[L] M') (π : ι → M' →ₗ[L] M) : Prop :=
  (∀ x, ∑ k, u k • J (π k x) = x) ∧ ∀ k l m, π k (u l • J m) = if k = l then m else 0

def Rel (π : ι → M' →ₗ[L] M) (S : Submodule L M) (S' : Submodule L' M') : Prop :=
  ∀ x, x ∈ S' ↔ ∀ k, π k x ∈ S

theorem exists_isCoord [IsScalarTower L L' M'] (u : Basis ι L L') (J : M →ₗ[L] M')
    (h : IsBaseChange L' J) : ∃ π : ι → M' →ₗ[L] M, IsCoord u J π := by
  let π : ι → M' →ₗ[L] M := fun k =>
    (TensorProduct.lid L M).toLinearMap ∘ₗ LinearMap.rTensor M (u.coord k) ∘ₗ
      (h.equiv.symm.toLinearMap.restrictScalars L)
  have hπ : ∀ k (s : L') (m : M), π k (s • J m) = u.repr s k • m := by
    intro k s m
    have : h.equiv.symm (s • J m) = s ⊗ₜ[L] m := by
      rw [LinearEquiv.symm_apply_eq, h.equiv_tmul]
    simp only [π, LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, this]
    simp
  refine ⟨π, fun x => ?_, fun k l m => ?_⟩
  · obtain ⟨y, rfl⟩ := h.equiv.surjective x
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
      rw [h.equiv_tmul]
      simp only [hπ, map_smul]
      conv_rhs => rw [← u.sum_repr s, Finset.sum_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_assoc, smul_comm]
    | add a b ha hb =>
      simp only [map_add (f := _), smul_add, Finset.sum_add_distrib, ha, hb]
  · rw [hπ, u.repr_self, Finsupp.single_apply]
    by_cases hk : k = l
    · simp [hk]
    · simp [hk, Ne.symm hk]

variable {u : ι → L'} {J : M →ₗ[L] M'} {π : ι → M' →ₗ[L] M}
  {JN : N →ₗ[L] N'} {πN : ι → N' →ₗ[L] N}

theorem IsCoord.sum (h : IsCoord u J π) (m : ι → M) (k : ι) :
    π k (∑ l, u l • J (m l)) = m k := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, h.2]

theorem IsCoord.comm (h : IsCoord u J π) (hN : IsCoord u JN πN) (f : N →ₗ[L] M)
    (f' : N' →ₗ[L'] M') (hf : ∀ y, f' (JN y) = J (f y)) (k : ι) (x : N') :
    π k (f' x) = f (πN k x) := by
  conv_lhs => rw [← hN.1 x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum f', map_smul, hf]
  exact h.sum _ k

theorem IsCoord.rel_ker (h : IsCoord u J π) (hN : IsCoord u JN πN) (f : N →ₗ[L] M)
    (f' : N' →ₗ[L'] M') (hf : ∀ y, f' (JN y) = J (f y)) :
    Rel πN (LinearMap.ker f) (LinearMap.ker f') := by
  intro x
  simp only [LinearMap.mem_ker, ← h.comm hN f f' hf]
  refine ⟨fun hx k => by simp [hx], fun hx => ?_⟩
  rw [← h.1 (f' x)]
  simp [hx]

theorem IsCoord.rel_range (h : IsCoord u J π) (hN : IsCoord u JN πN) (f : N →ₗ[L] M)
    (f' : N' →ₗ[L'] M') (hf : ∀ y, f' (JN y) = J (f y)) :
    Rel π (LinearMap.range f) (LinearMap.range f') := by
  intro x
  constructor
  · rintro ⟨y, rfl⟩ k
    exact ⟨_, (h.comm hN f f' hf k y).symm⟩
  · intro hx
    choose y hy using hx
    refine ⟨∑ k, u k • JN (y k), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hf, hy]
    exact h.1 x

omit [Algebra L L'] [Fintype ι] [DecidableEq ι] in
theorem Rel.inf {S T : Submodule L M} {S' T' : Submodule L' M'} (h : Rel π S S')
    (h' : Rel π T T') : Rel π (S ⊓ T) (S' ⊓ T') := by
  intro x
  simp only [Submodule.mem_inf, h x, h' x, forall_and]

omit [Algebra L L'] [Fintype ι] [DecidableEq ι] in
theorem Rel.iInf {κ : Type} {S : κ → Submodule L M} {S' : κ → Submodule L' M'}
    (h : ∀ i, Rel π (S i) (S' i)) : Rel π (⨅ i, S i) (⨅ i, S' i) := by
  intro x
  simp only [Submodule.mem_iInf, fun i => h i x]
  exact forall_comm

theorem IsCoord.nonempty_equiv [IsScalarTower L L' M'] (h : IsCoord u J π) {S : Submodule L M}
    {S' : Submodule L' M'} (hS : Rel π S S') : Nonempty (S' ≃ₗ[L] (ι → S)) := by
  let F : S' →ₗ[L] (ι → S) := LinearMap.pi fun k =>
    LinearMap.codRestrict S (π k ∘ₗ (S'.subtype.restrictScalars L))
      (fun x => (hS x.1).1 x.2 k)
  have hF : ∀ x k, (F x k : M) = π k x := fun _ _ => rfl
  refine ⟨LinearEquiv.ofBijective F ⟨?_, ?_⟩⟩
  · intro x y hxy
    apply Subtype.ext
    rw [← h.1 x, ← h.1 y]
    simp only [← hF, hxy]
  · intro m
    refine ⟨⟨∑ l, u l • J (m l), (hS _).2 fun k => ?_⟩, ?_⟩
    · rw [h.sum (fun l => (m l : M))]; exact (m k).2
    · funext k
      apply Subtype.ext
      rw [hF]
      exact h.sum (fun l => (m l : M)) k

theorem IsCoord.finrank_eq [IsScalarTower L L' M'] {u : Basis ι L L'} (h : IsCoord u J π)
    {S : Submodule L M} {S' : Submodule L' M'} (hS : Rel π S S') :
    finrank L' S' = finrank L S := by
  obtain ⟨e⟩ := h.nonempty_equiv hS
  haveI : Module.Finite L L' := Module.Finite.of_basis u
  have h1 : finrank L L' * finrank L' S' = finrank L S' := Module.finrank_mul_finrank L L' S'
  have h2 : finrank L (ι → S) = Fintype.card ι * finrank L S := by
    simp [Module.finrank, rank_fun_eq_lift_mul]
  rw [e.finrank_eq, h2, ← Module.finrank_eq_card_basis u] at h1
  exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h1

theorem IsCoord.finite_iff [IsScalarTower L L' M'] {u : Basis ι L L'} (h : IsCoord u J π)
    {S : Submodule L M} {S' : Submodule L' M'} (hS : Rel π S S') :
    Module.Finite L' S' ↔ Module.Finite L S := by
  obtain ⟨e⟩ := h.nonempty_equiv hS
  haveI : Module.Finite L L' := Module.Finite.of_basis u
  obtain ⟨k⟩ := u.index_nonempty
  constructor
  · intro _
    haveI : Module.Finite L S' := Module.Finite.trans L' S'
    haveI : Module.Finite L (ι → S) := Module.Finite.equiv e
    exact Module.Finite.of_surjective (LinearMap.proj k : (ι → S) →ₗ[L] S)
      (LinearMap.proj_surjective k)
  · intro _
    haveI : Module.Finite L S' := Module.Finite.equiv e.symm
    exact Module.Finite.of_restrictScalars_finite L L' S'

theorem IsCoord.tensor {Q : Type} [Field Q] [Algebra Q L] [Algebra Q L'] [Module Q M] [Module Q M']
    [IsScalarTower Q L M] [IsScalarTower Q L M'] [IsScalarTower Q L' M']
    (h : IsCoord u J π) (C : Type) [AddCommGroup C] [Module Q C] :
    IsCoord u (AlgebraTensorModule.map J (LinearMap.id : C →ₗ[Q] C))
      (fun k => AlgebraTensorModule.map (π k) (LinearMap.id : C →ₗ[Q] C)) := by
  constructor
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m c =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, TensorProduct.smul_tmul']
      rw [← TensorProduct.sum_tmul, h.1]
    | add a b ha hb => simp only [map_add (f := _), smul_add, Finset.sum_add_distrib, ha, hb]
  · intro k l x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m c =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, TensorProduct.smul_tmul', h.2]
      split_ifs <;> simp
    | add a b ha hb =>
      simp only [map_add (f := _), smul_add, ha, hb]
      split_ifs <;> simp

theorem map_comm {Q : Type} [Field Q] [Algebra Q L] [Algebra Q L'] [Module Q M] [Module Q M']
    [IsScalarTower Q L M] [IsScalarTower Q L M'] [IsScalarTower Q L' M']
    {C D : Type} [AddCommGroup C] [Module Q C] [AddCommGroup D] [Module Q D]
    (f : M →ₗ[L] M) (f' : M' →ₗ[L'] M') (hf : ∀ m, f' (J m) = J (f m)) (φ : C →ₗ[Q] D)
    (y : M ⊗[Q] C) :
    AlgebraTensorModule.map f' φ (AlgebraTensorModule.map J (LinearMap.id : C →ₗ[Q] C) y) =
      AlgebraTensorModule.map J (LinearMap.id : D →ₗ[Q] D) (AlgebraTensorModule.map f φ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m c => simp [hf]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

end General

theorem finrank_baseChange : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) (LL LL' : Type) [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL'] [FiniteDimensional LL LL'] (V V' : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [AddCommGroup V'] [Module LL' V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL' V'] [IsScalarTower LL LL' V'] (ρ : Representation LL G V) (ρ' : Representation LL' G V') (j : V →ₗ[LL] V'), IsBaseChange LL' j → (∀ g x, j (ρ g x) = ρ' g (j x)) → finrank LL' V' = finrank LL V ∧ finrank LL' ↥(H0V ρ') = finrank LL ↥(H0V ρ) ∧ (finrank LL' ↥(Dcris PD ρ') = finrank LL ↥(Dcris PD ρ) ∧ (Module.Finite LL' ↥(Dcris PD ρ') ↔ Module.Finite LL ↥(Dcris PD ρ))) ∧ (finrank LL' ↥(DdR PD ρ') = finrank LL ↥(DdR PD ρ) ∧ (Module.Finite LL' ↥(DdR PD ρ') ↔ Module.Finite LL ↥(DdR PD ρ))) ∧ (∀ a : ℤ, finrank LL' ↥(DdR PD ρ' ⊓ FilV PD (LL := LL') (V := V') a) = finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a)) ∧ (∀ τ : K₀ →ₐ[Qp] LL, finrank LL' ↥(DcrisL PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ)) = finrank LL ↥(DcrisL PD ρ τ)) ∧ ∀ τ : K →ₐ[Qp] LL, finrank LL' ↥(DdRE PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ)) = finrank LL ↥(DdRE PD ρ τ) ∧ ∀ a : ℤ, finrank LL' ↥(FildR PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ) a) = finrank LL ↥(FildR PD ρ τ a) := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL LL' _ _ _ _ _ _ _ V V' _ _ _ _ _ _ _ _ _ _ ρ ρ' j hj hρ
  classical
  haveI : IsScalarTower Qp LL V' := IsScalarTower.of_algebraMap_smul fun r x => by
    rw [← algebraMap_smul LL' (algebraMap Qp LL r) x, ← IsScalarTower.algebraMap_apply,
      algebraMap_smul]
  let u := Module.finBasis LL LL'
  obtain ⟨π, h⟩ := exists_isCoord u j hj
  have hB := h.tensor (Q := Qp) B
  have hR := h.tensor (Q := Qp) BdR
  have r0 : Rel π (H0V ρ) (H0V ρ') :=
    Rel.iInf fun g => h.rel_ker h _ _ fun y => by simp [hρ]
  have rc : Rel _ (Dcris PD ρ) (Dcris PD ρ') :=
    Rel.iInf fun g => hB.rel_ker hB _ _ fun y => by
      simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, actVB]
      rw [map_comm (ρ g) (ρ' g) (fun m => (hρ g m).symm)]
  have rd : Rel _ (DdR PD ρ) (DdR PD ρ') :=
    Rel.iInf fun g => hR.rel_ker hR _ _ fun y => by
      simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, actVdR]
      rw [map_comm (ρ g) (ρ' g) (fun m => (hρ g m).symm)]
  have rf : ∀ a : ℤ,
      Rel (fun k => AlgebraTensorModule.map (π k) (LinearMap.id : BdR →ₗ[Qp] BdR))
        (FilV PD (LL := LL) (V := V) a) (FilV PD (LL := LL') (V := V') a) := by
    intro a
    have hF := h.tensor (Q := Qp) ↥((PD.Fil a).restrictScalars Qp)
    refine hR.rel_range hF
      (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil a).restrictScalars Qp).subtype)
      (AlgebraTensorModule.map (LinearMap.id : V' →ₗ[LL'] V')
        ((PD.Fil a).restrictScalars Qp).subtype) fun y => ?_
    exact map_comm (J := j) LinearMap.id LinearMap.id (fun _ => rfl)
      ((PD.Fil a).restrictScalars Qp).subtype y
  have re : ∀ τ : K →ₐ[Qp] LL,
      Rel _ (DdRE PD ρ τ) (DdRE PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ)) :=
    fun τ => rd.inf (Rel.iInf fun c => hR.rel_ker hR _ _ fun y => by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, mulVdR,
        map_smul, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, algebraMap_smul]
      rw [map_comm (L' := LL') (J := j) LinearMap.id LinearMap.id (fun _ => rfl)])
  have rl : ∀ τ : K₀ →ₐ[Qp] LL,
      Rel _ (DcrisL PD ρ τ) (DcrisL PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ)) :=
    fun τ => rc.inf (Rel.iInf fun c => hB.rel_ker hB _ _ fun y => by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, mulVB,
        map_smul, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, algebraMap_smul]
      rw [map_comm (L' := LL') (J := j) LinearMap.id LinearMap.id (fun _ => rfl)])
  refine ⟨?_, h.finrank_eq r0, ⟨hB.finrank_eq rc, hB.finite_iff rc⟩,
    ⟨hR.finrank_eq rd, hR.finite_iff rd⟩, fun a => hR.finrank_eq (rd.inf (rf a)),
    fun τ => hB.finrank_eq (rl τ),
    fun τ => ⟨hR.finrank_eq (re τ), fun a => hR.finrank_eq ((re τ).inf (rf a))⟩⟩
  have := h.finrank_eq (S := ⊤) (S' := ⊤) (fun x => by simp)
  simpa using this

end GlobalTheory.CoeffBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodParIffGoodSig
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

noncomputable section

namespace GlobalTheory.EigenProjector

theorem HG_of_mem_Zgood (D : D7) (i : D.nd.Loc) (π : D.nd.X i) (hπ : π ∈ D.nd.Zgood i) :
    HG D.nd D.naut i := ⟨π, (D.Zgood_tie i π).1 hπ⟩

end GlobalTheory.EigenProjector
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H2QuotientFiniteCard
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.QuotientH2Count

def zmodScalarRep (n : ℕ) {O Γ M : Type} [CommRing O] [Group Γ] [AddCommGroup M] [Module O M]
    [Module (ZMod n) M] (χ : Γ →* Oˣ) : Representation (ZMod n) Γ M where
  toFun g := (DistribSMul.toAddMonoidHom M ((χ g : Oˣ) : O)).toZModLinearMap n
  map_one' := LinearMap.ext fun x => by
    show ((χ 1 : Oˣ) : O) • x = x
    rw [map_one, Units.val_one, one_smul]
  map_mul' g h := LinearMap.ext fun x => by
    show ((χ (g * h) : Oˣ) : O) • x = ((χ g : Oˣ) : O) • (((χ h : Oˣ) : O) • x)
    rw [map_mul, Units.val_mul, mul_smul]

theorem h2_twist_card_of_zmod {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
    (hTD : Formalism.GaloisCohomology.LocalTateDualityK) (hK : FiniteDimensional ℚ_[p] K) (i : G ≃ₜ* GK p K)
    (ε : G →* Oˣ) (M : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M]
    [DiscreteTopology M] [Finite M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M]
    (r : ℕ) [Module (ZMod (p ^ r)) M] (hr : 0 < r)
    (hc : Continuous fun q : G × M => ((ε q.1 : Oˣ) : O) • q.2) :
    Finite (H2 (twist ε M)) ∧ Nat.card (H2 (twist ε M)) ≤ Nat.card M := by
  obtain ⟨rho, hrho⟩ : ∃ rho : Representation (ZMod (p ^ r)) (GK p K) M,
      ∀ (g : GK p K) (x : M), rho g x = ((ε (i.symm g) : Oˣ) : O) • x :=
    ⟨zmodScalarRep (p ^ r) (carry i ε), fun _ _ => rfl⟩
  have hcont : ReciprocityTheory.Gal.ContAction rho := by
    have e : (fun q : GK p K × M => rho q.1 q.2) =
        (fun q : G × M => ((ε q.1 : Oˣ) : O) • q.2) ∘ fun q => (i.symm q.1, q.2) := by
      funext q; exact hrho q.1 q.2
    unfold ReciprocityTheory.Gal.ContAction
    rw [e]
    exact hc.comp ((i.symm.continuous.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨hF, hC⟩ := _root_.GlobalTheory.card_H2_le_of_local_duality hTD p K hK r M rho hr hcont
  have htr := GlobalTheory.T.natCard_H2_comp_equiv i rho
  have hsc := GlobalTheory.T.card_H2_eq_same_action (rho.comp i.toMulEquiv.toMonoidHom) (twist ε M) (fun g x => by
      show rho (i g) x = ((ε g : Oˣ) : O) • x
      rw [hrho, i.symm_apply_apply])
  have hcard : Nat.card (H2 (twist ε M)) = Nat.card (H2 rho) := by
    rw [← hsc, htr]
  refine ⟨?_, hcard ▸ hC⟩
  apply Nat.finite_of_card_ne_zero
  rw [hcard]
  exact Nat.card_pos.ne'

theorem h2_quot_card : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] {G : Type} [Group G] [TopologicalSpace G], Formalism.GaloisCohomology.LocalTateDualityK → FiniteDimensional ℚ_[p] K → PadicCoeff p O → ∀ (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) → ∀ k : ℕ, Finite (H2 (twist ε (O ⧸ IsLocalRing.maximalIdeal O ^ k))) ∧ Nat.card (H2 (twist ε (O ⧸ IsLocalRing.maximalIdeal O ^ k))) ≤ Nat.card (O ⧸ IsLocalRing.maximalIdeal O ^ k) := by
  intro p _ K O _ _ _ _ _ G _ _ hTD hK hO i ε hε k
  obtain ⟨hdisc, hfin⟩ := _root_.GlobalTheory.NatQuot.quot_pow_maximalIdeal_discrete_finite hO k
  haveI := hdisc
  haveI := hfin
  have hkill : ∀ x : O ⧸ IsLocalRing.maximalIdeal O ^ k, (p ^ (k + 1)) • x = 0 := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_nsmul, Ideal.Quotient.eq_zero_iff_mem, nsmul_eq_mul]
    push_cast
    rw [pow_succ, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hO.p_mem k)
  have hce := GlobalTheory.T.continuous_cyclotomic_character_localGalois hO i hε
  have hc : Continuous fun q : G × (O ⧸ IsLocalRing.maximalIdeal O ^ k) =>
      ((ε q.1 : Oˣ) : O) • q.2 := by
    have hq : Continuous (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ k)) := continuous_quot_mk
    have e : (fun q : G × (O ⧸ IsLocalRing.maximalIdeal O ^ k) => ((ε q.1 : Oˣ) : O) • q.2) =
        fun q => Ideal.Quotient.mk _ ((ε q.1 : Oˣ) : O) * q.2 := by
      funext q; exact Algebra.smul_def _ _
    rw [e]
    exact ((hq.comp hce).comp continuous_fst).mul continuous_snd
  letI : Module (ZMod (p ^ (k + 1))) (O ⧸ IsLocalRing.maximalIdeal O ^ k) :=
    AddCommGroup.zmodModule hkill
  exact h2_twist_card_of_zmod hTD hK i ε _ (k + 1) (Nat.succ_pos k) hc

end GlobalTheory.QuotientH2Count
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionLatticeFullDescendsStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachExpansionLattice_full_descends : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → Full (Di (HW l) h T i) (Lat C h T i ζ) → Full (Di (HW l) h T (i - 1)) (Lat C h T (i - 1) (ζ ^ l)) := by
  first | exact @GlobalTheory.NL.FullDown.full_down | exact GlobalTheory.NL.FullDown.full_down | (intros; apply GlobalTheory.NL.FullDown.full_down <;> assumption)
end

