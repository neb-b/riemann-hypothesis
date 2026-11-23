module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0214
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopData
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenNormalSubgroupUnderInertia
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published
  GlobalTheory.ResSel GlobalTheory.TwistDet

namespace GlobalTheory.ResSel.SmallSub

theorem exists_fix_roots {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {n : ℕ}
    (hn : n ≠ 0) : ∃ K : Subgroup (G F Ω), IsOpen (K : Set (G F Ω)) ∧ (∀ a b : G F Ω, a * b * a⁻¹ * b⁻¹ ∈ K) ∧
      ∀ g ∈ K, ∀ ζ : Ω, ζ ^ n = 1 → g ζ = ζ := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : NeZero n := ⟨hn⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
  have hp : ∀ ζ : Ω, ζ ^ n = 1 → ∃ k : ℕ, ξ ^ k = ζ := fun ζ h => by
    obtain ⟨k, -, hk⟩ := hξ.eq_pow_of_pow_eq_one h
    exact ⟨k, hk⟩
  have hc : ∀ a b : G F Ω, a (b ξ) = b (a ξ) := fun a b => by
    obtain ⟨j, hj⟩ := hp (a ξ) (by rw [← map_pow, hξ.pow_eq_one, map_one])
    obtain ⟨k, hk⟩ := hp (b ξ) (by rw [← map_pow, hξ.pow_eq_one, map_one])
    conv_lhs => rw [← hk, map_pow, ← hj]
    conv_rhs => rw [← hj, map_pow, ← hk]
    rw [← pow_mul, ← pow_mul, mul_comm]
  refine ⟨MulAction.stabilizer (G F Ω) ξ, stabilizer_isOpen_of_isIntegral ξ, fun a b => ?_, fun g hg ζ h => ?_⟩
  · show a (b (a⁻¹ (b⁻¹ ξ))) = ξ
    rw [hc a⁻¹ b⁻¹, mul_inv_apply, mul_inv_apply]
  · obtain ⟨k, rfl⟩ := hp ζ h
    have : g ξ = ξ := hg
    rw [map_pow, this]

theorem normal_of_comm {Γ : Type} [Group Γ] {K : Subgroup Γ} (h : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ K) : K.Normal :=
  ⟨fun k hk g => by simpa using K.mul_mem (h g k) hk⟩

theorem comm_mem_ker {Γ A : Type} [Group Γ] [CommGroup A] (φ : Γ →* A) (a b : Γ) : a * b * a⁻¹ * b⁻¹ ∈ φ.ker := by
  simp [MonoidHom.mem_ker]

theorem isOpen_ideal {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (h : IsAdic (IsLocalRing.maximalIdeal O)) {I : Ideal O} (hI : I ≠ ⊥) : IsOpen (I : Set O) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  have := (isAdic_iff.1 h).1 n
  rwa [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, ← hn] at this

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw)

theorem l_ne_zero : ((X.l i : ℕ) : X.O0 i) ≠ 0 := by
  intro h
  have : NeZero (X.l i ^ 1) := ⟨pow_ne_zero _ (X.lPrime i).out.ne_zero⟩
  have h1 := (X.zk_prim i 1).neZero'.out
  apply h1
  have := congrArg (phiK X i 1) h
  simpa using this

theorem l_mem : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := by
  intro h
  have h2 := h.map (algebraMap (X.O0 i) (X.O i))
  rw [map_natCast] at h2
  exact X.O_l i h2

theorem exists_eps : ∃ K : Subgroup (GE N), IsOpen (K : Set (GE N)) ∧ (∀ a b : GE N, a * b * a⁻¹ * b⁻¹ ∈ K) ∧
    ∀ g ∈ K, IsLocalRing.residue (X.O0 i) ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) = 1 := by
  refine ⟨((Units.map (IsLocalRing.residue (X.O0 i)).toMonoidHom).comp (eps0 X i)).ker, ?_, comm_mem_ker _,
    fun g hg => congrArg Units.val hg⟩
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  have hc : Continuous fun g : GE N => ‖((cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ) : ℤ_[X.l i]) - 1‖ :=
    ((Units.continuous_val.comp (continuous_cycZ D.host.E N.Om (X.l i))).sub continuous_const).norm
  refine Filter.mem_of_superset ((isOpen_lt hc (continuous_const (y := (1 : ℝ)))).mem_nhds (by simp)) fun g hg => ?_
  obtain ⟨c, hc⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 hg
  apply Units.ext
  change IsLocalRing.residue (X.O0 i) (algebraMap ℤ_[X.l i] (X.O0 i) (cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ)) = 1
  rw [sub_eq_iff_eq_add.1 hc, map_add (f := _), map_add (f := _), map_one, map_one, map_mul, map_natCast, map_mul,
    (IsLocalRing.residue_eq_zero_iff _).2 (l_mem X i), zero_mul, zero_add]

theorem not_mem_two {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (v : PlE D.host)
    (h1 : v ∈ placesOver D.host.E p) : v ∉ placesOver D.host.E q := fun h2 => by
  have hc : IsCoprime (p : 𝓞 D.host.E) (q : 𝓞 D.host.E) := ((Nat.coprime_primes hp hq).mpr hne).cast
  obtain ⟨a, b, hab⟩ := hc
  refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
  exact hab ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left a h1) (v.asIdeal.mul_mem_left b h2)

theorem pD_not_mem {v : PlE D.host} (hv : v ∈ X.pD i) :
    v ∉ placesOver D.host.E (X.l i) ∧ ∀ k, v ∉ placesOver D.host.E (D.host.g k) := by
  have hv' : v ∈ placesOver D.host.E (if X.l i = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← X.pD_eq i]; exact hv
  have hl : (X.l i).Prime := (X.lPrime i).out
  split_ifs at hv' with h
  · exact ⟨not_mem_two D.host.pde'_prime hl (h ▸ D.host.pde_ne.symm) v hv',
      fun k => not_mem_two D.host.pde'_prime (D.host.g_prime k) (D.host.pde_ne_g k).2 v hv'⟩
  · exact ⟨not_mem_two D.host.pde_prime hl (Ne.symm h) v hv',
      fun k => not_mem_two D.host.pde_prime (D.host.g_prime k) (D.host.pde_ne_g k).1 v hv'⟩

theorem exists_kerT (s : X.Sig i) {I : Ideal (X.O0 i)} (hI : I ≠ ⊥) : ∃ K : Subgroup (GE N), IsOpen (K : Set (GE N)) ∧
    K.Normal ∧ (∀ w, X.rhoS i s w = 1 → ∀ g, g * w * g⁻¹ * w⁻¹ ∈ K) ∧ ∀ g ∈ K, ∀ a b, (Tmat i s g - 1) a b ∈ I := by
  let φ : GE N →* GL (Fin D.R.r) (X.O0 i ⧸ I) := (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).comp (Tgl i s)
  have hφ : ∀ g, g ∈ φ.ker ↔ ∀ a b, (Tmat i s g - 1) a b ∈ I := by
    intro g
    rw [MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff, ← Tgl_coe]
    refine forall₂_congr fun a b => ?_
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
    have : ((1 : GL (Fin D.R.r) (X.O0 i ⧸ I)) : Matrix _ _ (X.O0 i ⧸ I)) a b =
        Ideal.Quotient.mk I ((1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) a b) := by
      rw [Units.val_one, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [this]
    rfl
  refine ⟨φ.ker, ?_, inferInstance, fun w hw g => ?_, fun g hg => (hφ g).1 hg⟩
  · have h1 : Continuous fun g : GE N => (((chiS i s g)⁻¹ : (X.O0 i)ˣ) : X.O0 i) := by
      simp only [← map_inv]
      exact (X.twistCharacterFamily_continuous i _ _).comp continuous_inv
    have hc : Continuous (Tmat i s) := h1.smul (X.rhoS_cont i s)
    have e : (φ.ker : Set (GE N)) = ⋂ a, ⋂ b, (fun g => (Tmat i s g - 1) a b) ⁻¹' (I : Set (X.O0 i)) := by
      ext g
      simp only [SetLike.mem_coe, hφ, Set.mem_iInter, Set.mem_preimage]
    rw [e]
    exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
      (isOpen_ideal (X.twistBaseCoefficientRing_isAdic i) hI).preimage ((hc.sub continuous_const).matrix_elem a b)
  · have h1 : Tgl i s w = scalGL D.R.r (chiS i s w)⁻¹ := by
      change scalGL _ _ * X.rhoS i s w = _
      rw [hw, mul_one]
    have h2 : Tgl i s (g * w * g⁻¹ * w⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1, ← scalGL_comm]
      group
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, h2, map_one]

theorem exists_small : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X)
    (i : X.Tw) (T : Set (X.Sig i)), (∀ s ∈ T, GalHyp bkP i s) → ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ (M : ℕ) (H : Subgroup (GE N)),
    IsOpen (H : Set (GE N)) → H.Normal →
    (∀ v ∈ X.pD i, ∀ A : ValuationSubring N.Om, IsPlaceOver A v → Ine (F := D.host.E) A ≤ H) →
    ∃ L : Subgroup (GE N), IsOpen (L : Set (GE N)) ∧ L.Normal ∧ L ≤ H ∧ (∀ s ∈ T, Small i s L z) ∧
      (∀ g ∈ L, ∀ ζ : N.Om, ζ ^ (2 * X.l i ^ M) = 1 → g ζ = ζ) ∧ ∀ s ∈ T, ∀ g ∈ L, ∀ a b,
        (Tmat i s g - 1) a b ∈ Ideal.span {(X.l i : X.O0 i) ^ nu X i} * IsLocalRing.maximalIdeal (X.O0 i) := by
  intro D N X bkP i T hT z hz M H hH hN hI
  obtain ⟨K₁, o₁, c₁, f₁⟩ := exists_fix_roots (F := D.host.E) (Ω := N.Om) (n := 2 * X.l i ^ M)
    (mul_ne_zero two_ne_zero (pow_ne_zero _ (X.lPrime i).out.ne_zero))
  obtain ⟨K₂, o₂, c₂, f₂⟩ := exists_eps X i
  have hne : Ideal.span {(X.l i : X.O0 i) ^ nu X i} * IsLocalRing.maximalIdeal (X.O0 i) ≠ ⊥ :=
    mul_ne_zero (fun h => pow_ne_zero _ (l_ne_zero X i) (Ideal.span_singleton_eq_bot.1 h)) (IsDiscreteValuationRing.not_a_field _)
  choose K o n c f using fun s => exists_kerT X i s hne
  have := normal_of_comm c₁
  have := normal_of_comm c₂
  let H₀ : Subgroup (GE N) := H ⊓ (K₁ ⊓ (K₂ ⊓ ⨅ s : T, K s))
  have hK : (⨅ s : T, K s).Normal := Subgroup.normal_iInf_normal fun s => n s
  have hn₀ : H₀.Normal := inferInstance
  have ho₀ : IsOpen (H₀ : Set (GE N)) := by
    refine hH.inter (o₁.inter (o₂.inter ?_))
    change IsOpen ((⨅ s : T, K s : Subgroup (GE N)) : Set (GE N))
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun s => o s
  have hw : ∀ v ∈ X.pD i, ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ w ∈ Ine (F := D.host.E) A,
      ∀ g, g * w * g⁻¹ * w⁻¹ ∈ H₀ := fun v hv A hA w hw g =>
    ⟨H.mul_mem (hN.conj_mem _ (hI v hv A hA hw) g) (H.inv_mem (hI v hv A hA hw)), c₁ _ _, c₂ _ _,
      Subgroup.mem_iInf.2 fun s => c s w ((hT s s.2).1.1 v (pD_not_mem X i hv).1 (pD_not_mem X i hv).2 A hA w hw) g⟩
  have hL : IsOpen ((H₀ ⊓ H₀.comap (cConj X) : Subgroup (GE N)) : Set (GE N)) := ho₀.inter (isOpen_comap_cConj X ho₀)
  have hf : ∀ s ∈ T, ∀ g ∈ H₀ ⊓ H₀.comap (cConj X), ∀ a b,
      (Tmat i s g - 1) a b ∈ Ideal.span {(X.l i : X.O0 i) ^ nu X i} * IsLocalRing.maximalIdeal (X.O0 i) :=
    fun s hs g hg => f s g (Subgroup.mem_iInf.1 hg.1.2.2.2 ⟨s, hs⟩)
  refine ⟨H₀ ⊓ H₀.comap (cConj X), hL, inferInstance, fun g hg => hg.1.1,
    fun s hs => ⟨hL, inferInstance, fun g g' hg => ?_, fun g => ?_, fun g hg => ⟨?_, f₂ g hg.1.2.2.1⟩⟩,
    fun g hg => f₁ g hg.1.2.1, hf⟩
  · obtain rfl : g' = cConj X g := AlgEquiv.ext hg
    simp only [Subgroup.mem_inf, Subgroup.mem_comap, cConj_cConj]
    exact and_comm
  · obtain ⟨v, hv, A, hA, hzA, -⟩ := hz
    refine ⟨hw v hv A hA z hzA g, ?_⟩
    obtain ⟨v', hv'⟩ := exists_isConjPl v
    have hv'' : v' ∈ X.pD i := by
      rw [← Finset.mem_coe, X.pD_eq] at hv ⊢
      exact mem_placesOver_conj hv' hv
    have := hw v' hv'' _ (isPlaceOver_moveVal_cc X hv' hA) _ (cConj_mem_ine X hzA) (cConj X g)
    change cConj X _ ∈ H₀
    rwa [map_mul, map_mul, map_mul, map_inv, map_inv]
  · ext a b
    have h0 : (Tmat i s g - 1) a b ∈ IsLocalRing.maximalIdeal (X.O0 i) := Ideal.mul_le_right (hf s hs g hg a b)
    have := (IsLocalRing.residue_eq_zero_iff _).2 h0
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [Matrix.map_apply, this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

end GlobalTheory.ResSel.SmallSub

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulIntegralBis
section
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.Isog

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem latHom_ext {T T' : LocLat G Qp LL O} {u w : LatHom T.L T'.L} (h : u.f = w.f) : u = w := by
  cases u; cases w; cases h; rfl

theorem exists_quasi_inverse (c : O)
    (hc : ∀ a : LL, ∃ (k : ℕ) (b : O), algebraMap O LL b = algebraMap O LL c ^ k * a)
    {T' T : LocLat G Qp LL O} (f : LatHom T'.L T.L) (hf : Function.Bijective f.f) :
    ∃ (m : ℕ) (g : LatHom T.L T'.L), latComp g f = latSmul T' (c ^ m) ∧
      latComp f g = latSmul T (c ^ m) := by
  let e : T'.V ≃ₗ[LL] T.V := LinearEquiv.ofBijective f.f hf
  have he : ∀ g y, e.symm (T.ρ g y) = T'.ρ g (e.symm y) := by
    intro g y
    apply e.injective
    rw [e.apply_symm_apply]
    have := f.equiv g (e.symm y)
    change e _ = T.ρ g (e _) at this
    rw [this, e.apply_symm_apply]
  obtain ⟨m, hm⟩ := GlobalTheory.WachSat.exists_pow_smul_le (LL := LL) c hc T'.L.T
    (T.L.T.map (e.symm.toLinearMap.restrictScalars O)) T'.L.span (T.L.fg.map _)
  haveI : ContinuousSMul LL T'.V := IsModuleTopology.toContinuousSMul LL T'.V
  let g : LatHom T.L T'.L :=
    { f := algebraMap O LL (c ^ m) • e.symm.toLinearMap
      equiv := fun g y => by simp [he]
      cont := IsModuleTopology.continuous_of_linearMap _
      T_le := fun y hy => by
        have := hm _ (Submodule.mem_map_of_mem hy)
        rw [← algebraMap_smul LL] at this
        exact this }
  refine ⟨m, g, latHom_ext ?_, latHom_ext ?_⟩
  · ext y
    change algebraMap O LL (c ^ m) • e.symm (e y) = algebraMap O LL (c ^ m) • y
    rw [e.symm_apply_apply]
  · ext y
    change e (algebraMap O LL (c ^ m) • e.symm y) = algebraMap O LL (c ^ m) • y
    rw [map_smul, e.apply_symm_apply]

variable (W : LocWach PD LL O v n)

theorem dd_torsionFree (hp : ∀ a : O, (PD.p : O) * a = 0 → a = 0) (T : LocLat G Qp LL O) (m : ℕ)
    (x : W.DD T) (hx : ((PD.p : O) ^ m) • x = 0) : x = 0 := by
  have hreg : ∀ (k : ℕ) (y : W.EE), (PD.p : W.EE) ^ k * y = 0 → y = 0 := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      exact ih y (GlobalTheory.WachSat.ee_torsionFree W hp _ (by rw [← hy]; ring))
  haveI := (W.DD_free T).1
  let b := Module.Free.chooseBasis W.EE (W.DD T)
  rw [← algebraMap_smul W.EE, map_pow, map_natCast] at hx
  apply b.repr.injective
  ext j
  have := congrArg (fun z => b.repr z j) hx
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] at this
  simpa using hreg m _ this

theorem globalBasis_of_basis (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    (b : Module.Basis (Fin (Module.finrank O ↥T.L.T)) (LetA O n) ↥(W.N T)) :
    GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.GlobalBasis W T := by
  let b' := (W.N_base T hT).basis b
  have hb : (fun j => (b j : W.DD T)) = b' := by
    funext j
    exact ((W.N_base T hT).basis_apply b j).symm
  refine ⟨b, ?_, ?_⟩
  · rw [hb]; exact b'.linearIndependent
  · rw [hb]; exact b'.span_eq

theorem isog_generic (hp : ∀ a : O, (PD.p : O) * a = 0 → a = 0)
    (hc : ∀ a : LL, ∃ (k : ℕ) (b : O), algebraMap O LL b = algebraMap O LL (PD.p : O) ^ k * a)
    (T' T : LocLat G Qp LL O) (f : LatHom T'.L T.L) (hT' : IsCrys PD T'.ρ) (hT : IsCrys PD T.ρ)
    (hs : ∀ (m : ℕ) (x : W.DD T'), ((PD.p : O) ^ m) • x ∈ W.N T' → x ∈ W.N T')
    (hf : Function.Bijective f.f) :
    Function.Injective (W.map f) ∧
    (∃ c : ℕ, ∀ y : W.DD T, ∃ x : W.DD T', W.map f x = ((PD.p : O) ^ c) • y ∧
      (y ∈ W.N T → x ∈ W.N T')) ∧
    ∀ x : W.DD T', W.map f x ∈ W.N T ↔ x ∈ W.N T' := by
  obtain ⟨m, g, hgf, hfg⟩ := exists_quasi_inverse (PD.p : O) hc f hf
  have h1 : ∀ x, W.map g (W.map f x) = ((PD.p : O) ^ m) • x := fun x => by
    rw [← W.map_comp, hgf, W.map_latSmul]
  have h2 : ∀ x, W.map f (W.map g x) = ((PD.p : O) ^ m) • x := fun x => by
    rw [← W.map_comp, hfg, W.map_latSmul]
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_,
    ⟨m, fun y => ⟨W.map g y, h2 y, W.map_N g hT hT' y⟩⟩,
    fun x => ⟨fun hx => hs m x ?_, W.map_N f hT' hT x⟩⟩
  · refine dd_torsionFree W hp T' m x ?_
    rw [← h1, hx, map_zero]
  · rw [← h1]
    exact W.map_N g hT hT' _ hx

end Generic

section Loc

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l)

theorem p_regular (a : ↥(OL LL)) (ha : (((P.PD K).p : ℕ) : ↥(OL LL)) * a = 0) : a = 0 := by
  have hl0 : (l : ↥LL.1) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  rw [P.PD_p] at ha
  have : (l : ↥LL.1) * (a : ↥LL.1) = 0 := by
    have := congrArg (Subtype.val) ha
    simpa using this
  exact Subtype.ext ((mul_eq_zero.1 this).resolve_left hl0)

theorem exists_pow_mul_integral (a : ↥LL.1) : ∃ (k : ℕ) (b : ↥(OL LL)), algebraMap ↥(OL LL) ↥LL.1 b =
    algebraMap ↥(OL LL) ↥LL.1 (((P.PD K).p : ℕ) : ↥(OL LL)) ^ k * a := by
  rw [P.PD_p]
  have : ∃ k : ℕ, 0 ≤ P.v LL ((l : ↥LL.1) ^ k * a) := by
    cases hq : P.v LL a with
    | top => exact ⟨0, by simp [hq]⟩
    | coe q =>
      obtain ⟨k, hk⟩ := exists_nat_ge (-q)
      refine ⟨k, ?_⟩
      rw [AddValuation.map_mul, AddValuation.map_pow, P.v_l, hq, nsmul_one, ← WithTop.coe_natCast,
        ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe]
      linarith
  obtain ⟨k, hk⟩ := this
  exact ⟨k, ⟨_, (P.v_O LL _).1 hk⟩, by rw [map_natCast]; rfl⟩

end Loc

section Main

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL)

set_option synthInstance.maxHeartbeats 100000 in
theorem sat_loc (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) (m : ℕ) (x : (H.W K s LL h).DD T)
    (hx : ((((P.PD K).p : ℕ) : ↥(OL LL)) ^ m) • x ∈ (H.W K s LL h).N T) : x ∈ (H.W K s LL h).N T := by
  obtain ⟨b⟩ := N_basis_loc H K s LL h T hT
  exact GlobalTheory.WachSat.mem_of_pow_smul_mem _ (p_regular P K LL) T (globalBasis_of_basis _ T hT b) m x hx

theorem isog_loc (T' T : Lt K LL) (f : LatHom T'.L T.L) (hT' : IsCrys (P.PD K) T'.ρ)
    (hT : IsCrys (P.PD K) T.ρ) (hf : Function.Bijective f.f) :
    Function.Injective ((H.W K s LL h).map f) ∧
    (∃ c : ℕ, ∀ y : (H.W K s LL h).DD T, ∃ x : (H.W K s LL h).DD T',
      (H.W K s LL h).map f x = ((((P.PD K).p : ℕ) : ↥(OL LL)) ^ c) • y ∧
      (y ∈ (H.W K s LL h).N T → x ∈ (H.W K s LL h).N T')) ∧
    ∀ x : (H.W K s LL h).DD T', (H.W K s LL h).map f x ∈ (H.W K s LL h).N T ↔
      x ∈ (H.W K s LL h).N T' :=
  isog_generic (H.W K s LL h) (p_regular P K LL) (exists_pow_mul_integral P K LL) T' T f hT' hT
    (sat_loc H K s LL h T' hT') hf

end Main

end GlobalTheory.NL.Isog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopDataOfSlotHyps
section
namespace GlobalTheory.TopWindow

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

theorem sg_cast_eq (l n : ℕ) (h : ZMod n → ℕ) (i : ZMod n) :
    (GlobalTheory.PhiGam.sg l h i : ℤ) = tableLineDegreeTwo.sg n l h i := by
  have h0 : (0 : ℝ) ≤ ∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1) :=
    tsum_nonneg fun j => by positivity
  simp only [GlobalTheory.PhiGam.sg, tableLineDegreeTwo.sg, Formalism.WachCohomologyFacts.V2.sgN]
  exact Int.natCast_floor_eq_floor h0

theorem inWin_iff (typ : Bool) (h η : ℕ) (u : ℤ) (h1 : 1 ≤ u) (h2 : u ≤ (h : ℤ) - 1) :
    InWin typ h η u ↔ Formalism.WachCohomologyFacts.V2.InWinN typ h η u := by
  unfold InWin Formalism.WachCohomologyFacts.V2.InWinN
  cases typ <;> simp [h1, h2]

theorem exists_topData_of_positionHyps : ∀ (l n t r : ℕ) [NeZero n] (h w η : ZMod n → ℕ)
    (typ : ZMod n → Bool) (U : ZMod n → Multiset ℤ), 2 ≤ l → 1 ≤ t →
    (∀ i, Multiset.card (U i) = r) → tableLineDegreeTwo.PositionHyps l n t h w η typ U →
    ∃ Dt : TopData n r, Dt.t = t ∧
      (∀ i, Dt.w i = w i ∧ Dt.U i = U i ∧ ∀ a, ((Dt.Ut i).count a : ℤ) = tableLineDegreeTwo.jTil U w t i a) ∧
      Dt.T1 l ∧ Dt.T2 l ∧ Dt.T3 l := by
  intro l n t r _ h w η typ U _ ht hc hS
  unfold tableLineDegreeTwo.PositionHyps at hS
  have hsg : ∀ i, (GlobalTheory.PhiGam.sg l h i : ℤ) = tableLineDegreeTwo.sg n l h i := fun i => sg_cast_eq l n h i
  obtain ⟨Dt, hDt, hw, h1, h2, h3⟩ := exists_topData l n t r h η typ (fun i => (w i : ℤ)) U
    (fun i => by obtain ⟨-, hw1, hw2, -⟩ := hS i; omega)
    (fun i => by
      obtain ⟨-, hw1, hw2, hG, hB, -⟩ := hS i
      by_cases hc : typ i = true
      · have := hG hc; omega
      · have := hB (by simpa using hc); omega)
    ht hc (fun i => (hS i).1)
    (fun i β hβ1 hβ2 => by
      obtain ⟨-, hw1, hw2, hG, hB, -⟩ := hS i
      refine ⟨by omega, by omega, ?_⟩
      unfold InWin
      split_ifs with hc
      · have := hG hc; omega
      · have := hB (by simpa using hc); omega)
    (fun i => by have := (hS i).2.2.2.2.2.1; have := hsg i; omega)
    (fun i u hu hin β hβ1 hβ2 => by
      have hr := (hS i).1 u hu
      have hlow := (hS i).2.2.2.2.2.2.1 u
        (by
          classical
          unfold tableLineDegreeTwo.lows
          exact Multiset.mem_filter.2 ⟨hu, (inWin_iff _ _ _ _ hr.1 hr.2).1 hin⟩) β
        (by rw [Formalism.WachCohomologyFacts.Top.GlobalTheory, Finset.mem_Icc]; omega)
      rw [hsg i]
      exact hlow)
    (fun i u hu hin y hy1 hy2 => by
      have hr := (hS i).1 u hu
      have hT := (hS i).2.2.2.2.2.2.2 u
        (by
          classical
          unfold Formalism.WachCohomologyFacts.V2.ClN
          exact Multiset.mem_filter.2 ⟨hu, fun h' => hin ((inWin_iff _ _ _ _ hr.1 hr.2).2 h')⟩) y
        (by have := hsg i; omega) (by have := hsg i; omega)
      intro hmod
      exact hT ((ZMod.intCast_eq_intCast_iff _ _ _).2 hmod))
  refine ⟨Dt, hDt, fun i => ⟨(hw i).1, (hw i).2.1, fun a => ?_⟩, h1, h2, h3⟩
  rw [(hw i).2.2 a]
  unfold tableLineDegreeTwo.jTil
  split_ifs <;> omega

end GlobalTheory.TopWindow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBoundsCrystallineDeRhamAll
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.FontaineAll

noncomputable def extRep {G : Type} [Group G] {LL : Type} [Field LL] (LL' : Type) [Field LL']
    [Algebra LL LL'] {V : Type} [AddCommGroup V] [Module LL V] (ρ : Representation LL G V) :
    Representation LL' G (LL' ⊗[LL] V) where
  toFun g := (ρ g).baseChange LL'
  map_one' := by rw [map_one]; exact LinearMap.baseChange_one LL V
  map_mul' g h := by rw [map_mul]; exact LinearMap.baseChange_mul _ _

theorem fontCore_of_tied (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (hT : LocTied l P AI) (K : FinExt l) : Formalism.MainNotions.LocalSituation.fontCore (P.PD K) := by
  intro LL _ _ _ O _ _ hO A
  haveI : FiniteDimensional ℚ_[l] LL := hO.2.1
  obtain ⟨LL', ⟨f⟩, -, -⟩ := _root_.GlobalTheory.exists_finExt_embedding_splitting l K LL
  letI : Algebra LL ↥LL'.1 := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[l] LL ↥LL'.1 :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  haveI : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2
  haveI : FiniteDimensional LL ↥LL'.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] LL ↥LL'.1
  obtain ⟨hV, -, ⟨hc, hcf⟩, ⟨hd, hdf⟩, -⟩ :=
    GlobalTheory.T.finrank_periodFunctor_coeff_baseChange (P.PD K) LL ↥LL'.1 A.V (↥LL'.1 ⊗[LL] A.V) A.ρ (extRep ↥LL'.1 A.ρ)
      (TensorProduct.mk LL ↥LL'.1 A.V 1) (TensorProduct.isBaseChange LL A.V ↥LL'.1)
      (fun g x => by simp [extRep])
  obtain ⟨h1, h2⟩ := GlobalTheory.Per.FontaineBound.fontaineLe_of_tied l P AI hT K LL'
  obtain ⟨h3, h4⟩ := GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI hT K LL' _ (extRep ↥LL'.1 A.ρ)
  refine ⟨⟨hcf.1 (h2 _ _), ?_⟩, ⟨hdf.1 h3, ?_⟩, fun hcr => ?_⟩
  · rw [← hc, ← hV]; exact h1 _ _
  · rw [← hd, ← hV]; exact h4
  · have h5 : IsCrys (P.PD K) (extRep ↥LL'.1 A.ρ) := by
      unfold IsCrys at hcr ⊢
      rw [hc, hV]; exact hcr
    have h6 := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI hT K LL' _ _ h5).1
    unfold IsDR at h6 ⊢
    rw [← hd, ← hV]; exact h6

theorem fontaine_bounds : ∀ D : D7, Formalism.MainNotions.LocalSituation.adm7 D :=
  fun D l _ K => fontCore_of_tied l (D.loc l) (D.locA l) (D.locT l) K

end GlobalTheory.Per.FontaineAll
end

