module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0001
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.QuotRepMk
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcPtTail
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X
open UpperTheory.V.Loc GlobalTheory.Published GlobalTheory.Published.PoitouTate

section Transport

variable {R R' Γ M : Type} [CommRing R] [CommRing R'] [Group Γ] [TopologicalSpace Γ]
  [AddCommGroup M] [Module R M] [Module R' M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation R Γ M) (ρ' : Representation R' Γ M) (h : ∀ g m, ρ' g m = ρ g m)

include h in
private theorem mem_Z2_iff (f : Γ × Γ → M) : f ∈ Z2 ρ ↔ f ∈ Z2 ρ' := by
  simp only [mem_cocycles2, h]

include h in
private theorem mem_B2_iff (f : Γ × Γ → M) : f ∈ B2 ρ ↔ f ∈ B2 ρ' := by
  have : ∀ c, d1 ρ c = d1 ρ' c := fun c => funext fun ⟨g, g'⟩ => by simp only [d1_apply, h]
  simp only [separated_dvr_second_cohomology_mem, this]

private def h2EquivOfRepEq : H2 ρ ≃ H2 ρ' :=
  Quotient.congr (Equiv.subtypeEquivRight (mem_Z2_iff ρ ρ' h)) fun a b => by
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap, Submodule.mem_comap]
    exact mem_B2_iff ρ ρ' h _

include h in
private theorem nonempty_sha2_equiv_sha2 {I : Type} {D : I → Type} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
    (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i)) :
    Nonempty (Sha2 ρ φ hφ ≃ Sha2 ρ' φ hφ) := by
  refine ⟨(h2EquivOfRepEq ρ ρ' h).subtypeEquiv fun x => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    simp only [Sha2, Submodule.mem_iInf, LinearMap.mem_ker]
    refine forall_congr' fun i => ?_
    change Submodule.Quotient.mk (restrictCocycles2 ρ (φ i) (hφ i) z) = 0 ↔
      Submodule.Quotient.mk (restrictCocycles2 ρ' (φ i) (hφ i) ⟨z.1, (mem_Z2_iff ρ ρ' h _).1 z.2⟩) = 0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_comap]
    exact mem_B2_iff (ρ.comp (φ i)) (ρ'.comp (φ i)) (fun g m => h _ m) _

end Transport

private theorem card_ker_range {R A B : Type} [Ring R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) : Nat.card A = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f), Nat.card_congr f.quotKerEquivRange.toEquiv]

private theorem card_exact {R A B C : Type} [Ring R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : Function.Exact f g)
    (hg : Function.Surjective g) :
    Nat.card (LinearMap.ker f) * Nat.card B = Nat.card A * Nat.card C := by
  rw [card_ker_range f, card_ker_range g, LinearMap.exact_iff.1 h, LinearMap.range_eq_top.2 hg, mul_assoc,
    Nat.card_congr (Submodule.topEquiv (R := R) (M := C)).toEquiv]

private theorem card_H0dual {R k Γ Γ' M : Type} [Field R] [Field k] [Finite k] [Algebra R k] [Group Γ] [Group Γ']
    [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower R k M] [Finite M]
    (ρ : Representation k Γ M) (ρ' : Representation R Γ' M) (e : Γ' ≃* Γ) (h : ∀ g m, ρ' g m = ρ (e g) m)
    (χ : Γ →* kˣ) (χ' : Γ' →* Rˣ) (hχ : ∀ g, (χ (e g) : k) = algebraMap R k (χ' g)) :
    Nat.card (H0dual χ ρ) = Nat.card (H0dual χ' ρ') := by
  haveI : Finite R := Finite.of_injective _ (algebraMap R k).injective
  let T : Module.Dual k M →+ Module.Dual R M :=
    { toFun := fun f => (Algebra.trace R k).comp (f.restrictScalars R)
      map_zero' := by ext; simp
      map_add' := fun f f' => by ext; simp }
  have hT : ∀ f m, T f m = Algebra.trace R k (f m) := fun _ _ => rfl
  have hinj : Function.Injective T := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf
    ext m
    refine (traceForm_nondegenerate R k).1 (f m) fun a => ?_
    have := hT f (a • m)
    rw [hf, f.map_smul, smul_eq_mul, mul_comm] at this
    exact this.symm
  haveI : Finite (Module.Dual R M) := DFunLike.finite _
  have hbij : Function.Bijective T := hinj.bijective_of_nat_card_le (by
    rw [Module.natCard_eq_pow_finrank (K := R) (V := Dual R M), Module.natCard_eq_pow_finrank (K := k) (V := Dual k M),
      Subspace.dual_finrank_eq, Subspace.dual_finrank_eq, ← Module.natCard_eq_pow_finrank,
      ← Module.natCard_eq_pow_finrank])
  refine Nat.card_congr ((Equiv.ofBijective _ hbij).subtypeEquiv fun f => ?_)
  rw [Equiv.ofBijective_apply]
  constructor
  · intro hf g x
    rw [hT, hT, h, hf, hχ, ← Algebra.smul_def, map_smul, smul_eq_mul]
  · intro hf g x
    obtain ⟨g, rfl⟩ := e.surjective g
    have : f.comp (ρ (e g)) = (χ (e g) : k) • f := hinj (LinearMap.ext fun y => by
      have := hf g y
      rw [hT, hT, h] at this
      rw [hT, hT, LinearMap.comp_apply, this, LinearMap.smul_apply, smul_eq_mul, hχ, ← Algebra.smul_def,
        map_smul, smul_eq_mul])
    exact LinearMap.congr_fun this x

private theorem card_twDual {R Γ Γ' M : Type} [CommRing R] [Group Γ] [Group Γ'] [AddCommGroup M] [Module R M]
    (χ : Γ →* Rˣ) (ρ : Representation R Γ M) (π : Γ' →* Γ) (hπ : Function.Surjective π) :
    Nat.card (H0 (twDual χ ρ)) = Nat.card (H0dual (χ.comp π) (ρ.comp π)) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight (α := TDual R M) fun y => ?_)
  constructor
  · intro hy g m
    have e := congrArg (fun φ : TDual R M => φ (ρ (π g) m)) (hy (π g))
    simp only [twDual_apply] at e
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at e
    exact e.symm
  · intro hy g
    obtain ⟨g, rfl⟩ := hπ g
    refine LinearMap.ext fun m => ?_
    have := hy g (ρ (π g)⁻¹ m)
    simp only [MonoidHom.comp_apply] at this
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
    exact this.symm

theorem UpperTheory.V.X.ptTail :
    LocalFiniteness → GlobalFiniteness → GlobalTheory.Published.PoitouTateNormalised → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (S : Finset (HeightOneSpectrum (𝓞 ℚ))), (∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → v ∈ S) → ∀ (A : S → ValuationSubring Ω), (∀ v, IsPlaceOver (A v) v.1) → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M), ContAction ρ → finrank k (Sha2 ρ (fun v => locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (A v)) fun v => continuous_locHom _ (A v)) + ∑ v, finrank k (H2 (ρ.comp (locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (A v)))) = finrank k (H2 ρ) + finrank k (Loc.H0dual (cycK Ω l k) (ρ.comp (toGS Ω _))) := by
  intro hL _ hP Ω _ _ _ l _ h2 S hS A hA k _ _ _ M _ _ _ _ _ ρ hρ
  have hl : l.Prime := Fact.out
  let χ := cycK Ω l k
  let c : ZMod (l ^ 1) →+* k := ZMod.castHom (dvd_pow_self l one_ne_zero) k
  haveI : Fact (l ^ 1).Prime := ⟨by rwa [pow_one]⟩
  haveI : CharP k (l ^ 1) := by rwa [pow_one]
  letI : Algebra (ZMod (l ^ 1)) k := ZMod.algebra k (l ^ 1)
  letI : Module (ZMod (l ^ 1)) M := Module.compHom M (algebraMap (ZMod (l ^ 1)) k)
  haveI : IsScalarTower (ZMod (l ^ 1)) k M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Finite M := Module.finite_of_finite k
  let ρ' : Representation (ZMod (l ^ 1)) _ M := resCoef (ZMod (l ^ 1)) ρ
  have h : ∀ g m, ρ' g m = ρ g m := fun _ _ => rfl
  have hρ' : ContAction ρ' := hρ
  have hS' : ContainsAbove S l := hS
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_pow ℚ Ω l 1
  obtain ⟨μ, hμ⟩ := exists_lift_cycMod (Ω := Ω) (r := 1) hS'
  obtain ⟨inv, -, hN⟩ := hP ℚ Ω l 1 (Or.inl h2) one_pos ζ hζ
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, hex, hsurj⟩, ⟨⟨-, hfs, -⟩, -⟩, -⟩ := hN S hS' A hA μ hμ M ρ' hρ'
  have hc := card_exact _ _ hex hsurj
  have hker : LinearMap.ker (loc2 S A ρ') = Sha2 ρ' (locFam S A) (continuous_locFam S A) := LinearMap.ker_pi _
  haveI f2 : ∀ v : S, Finite (H2 (ρ'.comp (locFam S A v))) := fun v => by
    obtain ⟨-, -, f2, -⟩ := hL ℚ Ω l 1 M (A v) (ρ'.comp (locFam S A v)) v.1 one_pos (hA v)
      (hρ'.comp' (continuous_locFam S A v))
    exact f2
  haveI : Finite (H2 ρ') := by
    apply Nat.finite_of_card_ne_zero
    rw [card_ker_range (loc2 S A ρ'), hker]
    exact mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
  obtain ⟨eS⟩ := nonempty_sha2_equiv_sha2 ρ ρ' h (locFam S A) (continuous_locFam S A)
  have e2 := h2EquivOfRepEq ρ ρ' h
  have e3 : ∀ v : S, H2 (ρ.comp (locFam S A v)) ≃ H2 (ρ'.comp (locFam S A v)) := fun v =>
    h2EquivOfRepEq _ _ fun g m => h _ m
  haveI : Finite (H2 ρ) := Finite.of_equiv _ e2.symm
  haveI : Finite (Sha2 ρ (locFam S A) (continuous_locFam S A)) := Subtype.finite
  haveI : Module.Finite k (Sha2 ρ (locFam S A) (continuous_locFam S A)) := .of_finite
  haveI : ∀ v : S, Finite (H2 (ρ.comp (locFam S A v))) := fun v => Finite.of_equiv _ (e3 v).symm
  haveI : Module.Finite k (H2 ρ) := .of_finite
  haveI : ∀ v : S, Module.Finite k (H2 (ρ.comp (locFam S A v))) := fun _ => .of_finite
  haveI : Finite (Module.Dual k M) := DFunLike.finite _
  haveI : Finite (TDual (ZMod (l ^ 1)) M) := (DFunLike.finite _ : Finite (M →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)))
  haveI : Finite (H0 (twDual μ ρ')) := Subtype.finite
  have hk : 1 < Nat.card k := Finite.one_lt_card
  have hd : Nat.card (Module.Dual (ZMod (l ^ 1)) (H0 (twDual μ ρ'))) =
      Nat.card (H0dual χ (ρ.comp (toGS Ω _))) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod (l ^ 1)), Subspace.dual_finrank_eq,
      ← Module.natCard_eq_pow_finrank, card_twDual μ ρ' (toGS Ω _) (QuotientGroup.mk'_surjective _), hμ]
    refine (card_H0dual (ρ.comp (toGS Ω _)) (ρ'.comp (toGS Ω _)) (MulEquiv.refl (G ℚ Ω)) (fun _ _ => rfl) χ
      (cycMod ℚ Ω l 1) fun g => ?_).symm
    exact RingHom.congr_fun (Subsingleton.elim c (algebraMap _ k)) _
  change finrank k (Sha2 ρ (locFam S A) (continuous_locFam S A)) +
    ∑ v, finrank k (H2 (ρ.comp (locFam S A v))) = _
  apply Nat.pow_right_injective hk
  beta_reduce
  rw [pow_add, pow_add, ← Finset.prod_pow_eq_pow_sum]
  simp only [← Module.natCard_eq_pow_finrank]
  rw [Nat.card_congr eS, Nat.card_congr e2, ← hd, ← hc, hker, Nat.card_pi]
  exact congrArg _ (Finset.prod_congr rfl fun v _ => Nat.card_congr (e3 v))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcUrIndex
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

private theorem urIndex_mem {k D M : Type} [Field k] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module k M]
    [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k D M) (J : Subgroup D) (f : Z1 ρ) :
    (Submodule.Quotient.mk f : H1 ρ) ∈ H1ur ρ J ↔ ∃ m, ∀ j ∈ J, f.1 j = ρ j m - m := by
  have hJc : Continuous J.subtype := continuous_subtype_val
  show resH1 ρ J.subtype hJc (Submodule.Quotient.mk f) = 0 ↔ _
  unfold resH1
  rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
  show ((restrictCocycles1 ρ J.subtype hJc f : Z1 (ρ.comp J.subtype)) : J → M) ∈ B1 (ρ.comp J.subtype) ↔ _
  rw [mem_coboundaries1]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, fun j hj => ?_⟩
    have h := hm ⟨j, hj⟩
    rw [restrictCocycles1_apply ρ J.subtype hJc] at h
    simpa using h
  · rintro ⟨m, hm⟩
    refine ⟨m, fun j => ?_⟩
    rw [restrictCocycles1_apply ρ J.subtype hJc]
    simpa using hm j j.2

private theorem urIndex_avg {k Γ M : Type} [Field k] [Group Γ] [AddCommGroup M] [Module k M]
    (ρ : Representation k Γ M) (N : Subgroup Γ) (hN : (N.index : k) ≠ 0) (c : Γ → M)
    (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) (h0 : ∀ n ∈ N, c n = 0) :
    ∃ m, ∀ g, c g = ρ g m - m := by
  classical
  have hNi : N.index ≠ 0 := fun h => hN (by rw [h, Nat.cast_zero])
  haveI : N.FiniteIndex := ⟨hNi⟩
  haveI : Fintype (Γ ⧸ N) := Fintype.ofFinite _
  have hconst : ∀ g n, n ∈ N → c (g * n) = c g := fun g n hn => by
    rw [hc, h0 n hn, map_zero, add_zero]
  let c' : Γ ⧸ N → M := Quotient.lift (s := QuotientGroup.leftRel N) c (fun a b hab => by
    have hab' : a⁻¹ * b ∈ N := QuotientGroup.leftRel_apply.1 hab
    have h := hconst a (a⁻¹ * b) hab'
    rw [mul_inv_cancel_left] at h
    exact h.symm)
  have hc' : ∀ (h : Γ) (x : Γ ⧸ N), c' (h • x) = c h + ρ h (c' x) := by
    intro h x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    show c (h * g) = c h + ρ h (c g)
    exact hc h g
  let S := ∑ x : Γ ⧸ N, c' x
  have hS : ∀ h, S = Fintype.card (Γ ⧸ N) • c h + ρ h S := by
    intro h
    calc S = ∑ x, c' (h • x) := (Equiv.sum_comp (MulAction.toPerm h) c').symm
      _ = ∑ x, (c h + ρ h (c' x)) := Finset.sum_congr rfl fun x _ => hc' h x
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, map_sum]
  have hcard : (Fintype.card (Γ ⧸ N) : k) = N.index := by
    rw [Fintype.card_eq_nat_card]
    rfl
  refine ⟨-((N.index : k)⁻¹ • S), fun g => ?_⟩
  have h1 := hS g
  have h2 : S - ρ g S = (N.index : k) • c g := by
    rw [← hcard, Nat.cast_smul_eq_nsmul]
    nth_rewrite 1 [h1]
    rw [add_sub_cancel_right]
  rw [map_neg, map_smul, neg_sub_neg, ← smul_sub, h2, smul_smul, inv_mul_cancel₀ hN, one_smul]

theorem UpperTheory.V.X.urIndex :
    ∀ (l : ℕ) [Fact l.Prime] {k D M : Type} [Field k] [CharP k l] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k D M), ContAction ρ → ∀ (I N : Subgroup D), N ≤ I → ¬ l ∣ N.relIndex I → H1ur ρ N = H1ur ρ I := by
  intro l _ k D M _ _ _ _ _ _ _ _ ρ hρ I N hNI hl
  ext c
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (Submodule.comap (Z1 ρ).subtype (B1 ρ)) c
  refine (urIndex_mem ρ N f).trans (Iff.trans ?_ (urIndex_mem ρ I f).symm)
  constructor
  · rintro ⟨m, hm⟩
    have hf := ((mem_Z1_iff_cocycle ρ _).1 f.2).2
    let cI : I → M := fun j => f.1 j - (ρ j m - m)
    have hcI : ∀ g h : I, cI (g * h) = cI g + (ρ.comp I.subtype) g (cI h) := by
      intro g h
      simp only [cI, MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.coe_mul, hf, map_mul,
        Module.End.mul_apply, map_sub]
      abel
    have h0 : ∀ n ∈ N.subgroupOf I, cI n = 0 := fun n hn => by
      simp only [cI]
      rw [hm n (Subgroup.mem_subgroupOf.1 hn), sub_self]
    have hidx : ((N.subgroupOf I).index : k) ≠ 0 := by
      have e : (N.subgroupOf I).index = N.relIndex I := rfl
      rw [e]
      intro h
      exact hl ((CharP.cast_eq_zero_iff k l _).1 h)
    obtain ⟨m', hm'⟩ := urIndex_avg (ρ.comp I.subtype) (N.subgroupOf I) hidx cI hcI h0
    refine ⟨m + m', fun j hj => ?_⟩
    have h := hm' ⟨j, hj⟩
    simp only [cI, MonoidHom.comp_apply, Subgroup.coe_subtype] at h
    rw [sub_eq_iff_eq_add] at h
    rw [h, map_add (f := _)]
    abel
  · rintro ⟨m, hm⟩
    exact ⟨m, fun j hj => hm j (hNI hj)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcXiSq
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

private theorem UpperTheory.V.X.xiSq_ft {R : Type} [CommRing R] {n d : ℕ} [NeZero n] (χ : DirichletCharacter R n)
    (hd : d ∣ n) : χ.FactorsThrough d ↔ ∀ a : ℤ, IsCoprime a n → (d : ℤ) ∣ a - 1 → χ a = 1 := by
  constructor
  · rintro ⟨hd', χ₀, rfl⟩ a ha hda
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₀ hd' ha]
    have : ((a : ℤ) : ZMod d) = 1 := by
      have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (a - 1) d).mpr hda
      push_cast at h0
      exact sub_eq_zero.mp h0
    rw [this, map_one]
  · intro h
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    set a : ℤ := ((x : ZMod n).val : ℤ) with ha_def
    have hax : ((a : ℤ) : ZMod n) = (x : ZMod n) := by
      simp [ha_def, ZMod.natCast_zmod_val]
    have hcop : IsCoprime a n := by
      have hu : IsUnit ((a : ℤ) : ZMod n) := by rw [hax]; exact x.isUnit
      rw [ZMod.coe_int_isUnit_iff_isCoprime] at hu
      exact hu.symm
    have hd1 : (d : ℤ) ∣ a - 1 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd (a - 1) d).mp
      have h1 := congrArg (fun u : (ZMod d)ˣ => (u : ZMod d)) hx
      simp only [ZMod.unitsMap_val, Units.val_one] at h1
      rw [ZMod.cast_eq_val] at h1
      push_cast
      rw [ha_def]
      push_cast
      rw [h1, sub_self]
    have := h a hcop hd1
    rw [hax] at this
    ext
    simpa using this

private theorem UpperTheory.V.X.xiSq_cong {R : Type} [CommRing R] {n : ℕ} (χ : DirichletCharacter R n)
    {a b : ℤ} (h : (n : ℤ) ∣ a - b) : χ a = χ b := by
  congr 1
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (dvd_sub_comm.mp h)

private theorem UpperTheory.V.X.xiSq_cop (t : ℤ) (m : ℕ) : IsCoprime (1 + 2 * t) ((2 ^ m : ℕ) : ℤ) := by
  push_cast
  exact IsCoprime.pow_right ⟨1, -t, by ring⟩

private theorem UpperTheory.V.X.exists_primitive_square_twist {O : Type} [CommRing O] (k : ℕ) (ψ : DirichletCharacter O (2 ^ (k + 4)))
    (hψ : ψ.IsPrimitive) : ∃ ξ : DirichletCharacter O (2 ^ (k + 3)), ξ.IsPrimitive ∧
      ∀ a : ℤ, IsCoprime a ((2 ^ (k + 4) : ℕ) : ℤ) → ξ a = ψ a ^ 2 * ((ZMod.χ₄ a : ℤ) : O) := by
  have h4 : 4 ∣ 2 ^ (k + 4) := Dvd.intro (2 ^ k * 4) (by ring)
  let χ4O : DirichletCharacter O 4 := ZMod.χ₄.ringHomComp (Int.castRingHom O)
  let φ : DirichletCharacter O (2 ^ (k + 4)) := ψ ^ 2 * DirichletCharacter.changeLevel h4 χ4O
  have hsq : ∀ a : ℤ, ψ a ^ 2 = ψ ((a ^ 2 : ℤ) : ZMod (2 ^ (k + 4))) := by
    intro a
    rw [Int.cast_pow, map_pow]
  have h1 : ψ ((1 : ℤ) : ZMod (2 ^ (k + 4))) = 1 := by rw [Int.cast_one, map_one]
  have hc4 : ∀ a : ℤ, (4 : ℤ) ∣ a - 1 → ((ZMod.χ₄ a : ℤ) : O) = 1 := by
    intro a ha
    have := UpperTheory.V.X.xiSq_cong ZMod.χ₄ (n := 4) (a := a) (b := 1) (by exact_mod_cast ha)
    rw [this]
    simp
  have hval : ∀ a : ℤ, IsCoprime a ((2 ^ (k + 4) : ℕ) : ℤ) →
      φ a = ψ a ^ 2 * ((ZMod.χ₄ a : ℤ) : O) := by
    intro a ha
    simp only [φ, MulChar.coeToFun_mul, Pi.mul_apply, MulChar.pow_apply' _ two_ne_zero]
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd' _ h4 ha]
    simp [χ4O, MulChar.ringHomComp_apply]
  have hd : 2 ^ (k + 3) ∣ 2 ^ (k + 4) := pow_dvd_pow 2 (by omega)
  have hft : φ.FactorsThrough (2 ^ (k + 3)) := by
    rw [UpperTheory.V.X.xiSq_ft φ hd]
    intro a ha hda
    rw [hval a ha]
    obtain ⟨t, ht⟩ := hda
    push_cast at ht
    have ha' : a = 1 + 2 ^ (k + 3) * t := by linarith
    rw [hc4 a ⟨2 ^ (k + 1) * t, by rw [ha']; ring⟩, mul_one, hsq]
    rw [UpperTheory.V.X.xiSq_cong ψ (a := a ^ 2) (b := 1) ⟨t + 2 ^ (k + 2) * t ^ 2, by push_cast; rw [ha']; ring⟩]
    exact h1
  obtain ⟨hd', ξ, hξ⟩ := hft
  have hξv : ∀ a : ℤ, IsCoprime a ((2 ^ (k + 4) : ℕ) : ℤ) → ξ a = ψ a ^ 2 * ((ZMod.χ₄ a : ℤ) : O) := by
    intro a ha
    rw [← DirichletCharacter.changeLevel_eq_cast_of_dvd' ξ hd' ha, ← hξ, hval a ha]
  refine ⟨ξ, ?_, hξv⟩
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ξ.conductor_dvd_level
  show ξ.conductor = 2 ^ (k + 3)
  rw [hj']
  rcases Nat.lt_or_ge j (k + 3) with hlt | hge
  · exfalso
    have hf : ξ.FactorsThrough (2 ^ (k + 2)) :=
      DirichletCharacter.FactorsThrough.mono ξ ξ.factorsThrough_conductor
        (by rw [hj']; exact pow_dvd_pow 2 (by omega)) (pow_dvd_pow 2 (by omega))
    rw [UpperTheory.V.X.xiSq_ft ξ (pow_dvd_pow 2 (by omega))] at hf
    set b : ℤ := 1 + 2 * 2 ^ (k + 1) with hb
    have hb3 := hf b (by simpa [hb] using UpperTheory.V.X.xiSq_cop (2 ^ (k + 1)) (k + 3))
      ⟨1, by push_cast; rw [hb]; ring⟩
    rw [hξv b (by simpa [hb] using UpperTheory.V.X.xiSq_cop (2 ^ (k + 1)) (k + 4)),
      hc4 b ⟨2 ^ k, by rw [hb]; ring⟩, mul_one, hsq,
      UpperTheory.V.X.xiSq_cong ψ (a := b ^ 2) (b := 1 + 2 ^ (k + 3)) ⟨2 ^ k, by push_cast; rw [hb]; ring⟩] at hb3
    have hψf : ψ.FactorsThrough (2 ^ (k + 3)) := by
      rw [UpperTheory.V.X.xiSq_ft ψ hd]
      intro a ha hda
      obtain ⟨t, ht⟩ := hda
      push_cast at ht
      obtain ⟨s, hs | hs⟩ := Int.even_or_odd' t
      · rw [UpperTheory.V.X.xiSq_cong ψ (a := a) (b := 1) ⟨s, by push_cast; rw [hs] at ht; linear_combination ht⟩]
        exact h1
      · rw [UpperTheory.V.X.xiSq_cong ψ (a := a) (b := 1 + 2 ^ (k + 3)) ⟨s, by push_cast; rw [hs] at ht; linear_combination ht⟩]
        exact hb3
    have hle : ψ.conductor ≤ 2 ^ (k + 3) := Nat.sInf_le hψf
    have hpr : ψ.conductor = 2 ^ (k + 4) := hψ
    rw [hpr] at hle
    have := Nat.pow_lt_pow_right (a := 2) (by norm_num) (show k + 3 < k + 4 by omega)
    omega
  · congr 1
    omega

theorem UpperTheory.V.X.xiSq :
    ∀ (O : Type) [CommRing O] [IsDomain O], (2 : O) ≠ 0 → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter O N) (c : ℕ), 4 ≤ c → χ.conductor = 2 ^ c → ∃ ξ : DirichletCharacter O (2 ^ (c - 1)), ξ.IsPrimitive ∧ ∀ a : ℤ, IsCoprime a N → ξ a = χ a ^ 2 * ((ZMod.χ₄ a : ℤ) : O) := by
  intro O _ _ _ N _ χ c hc hcond
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 4 := ⟨c - 4, by omega⟩
  have hf : χ.FactorsThrough (2 ^ (k + 4)) := hcond ▸ χ.factorsThrough_conductor
  obtain ⟨hdv, ψ, hψχ⟩ := hf
  have hψp : ψ.IsPrimitive := by
    show ψ.conductor = 2 ^ (k + 4)
    have h := DirichletCharacter.conductor_changeLevel ψ hdv
    rw [← hψχ, hcond] at h
    exact h.symm
  obtain ⟨ξ, hp, hv⟩ := UpperTheory.V.X.exists_primitive_square_twist k ψ hψp
  refine ⟨ξ, hp, fun a ha => ?_⟩
  have ha' : IsCoprime a ((2 ^ (k + 4) : ℕ) : ℤ) :=
    ha.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr hdv)
  rw [hv a ha', hψχ, DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ hdv ha]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoFinExt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

private theorem fd_adjoin_range (l : ℕ) [Fact l.Prime] {ι : Type} [Finite ι] (f : ι → PadicAlgCl l) :
    FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range f)) := by
  haveI : Finite (Set.range f) := (Set.finite_range _).to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral

private theorem coc_finext (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] (K₀ : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K₀] (n : ℕ)
    (θ : Γ → (Fin n → PadicAlgCl l) → (Fin n → PadicAlgCl l)) (c : Γ → Fin n → PadicAlgCl l)
    (hθ : ∀ (L : IntermediateField ℚ_[l] (PadicAlgCl l)), K₀ ≤ L → ∀ g v, (∀ j, v j ∈ L) → ∀ j, θ g v j ∈ L)
    (hc1 : c 1 = 0) (hc : Continuous c)
    (hcoc : ∀ g h, c (g * h) = c g + θ g (c h)) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ K₀ ≤ E ∧ ∀ g j, c g j ∈ E := by
  obtain ⟨ι, _, K, hK, hcov⟩ := GlobalTheory.CompactRepField.exists_countable_family l
  let H : ι → Subgroup Γ := fun i =>
    { carrier := {g | ∀ j, c g j ∈ K₀ ⊔ K i}
      one_mem' := by
        intro j
        rw [hc1]; exact zero_mem _
      mul_mem' := fun {g h} hg hh j => by
        rw [hcoc]
        exact add_mem (hg j) (hθ _ le_sup_left g _ hh j)
      inv_mem' := fun {g} hg j => by
        have h1 := hcoc g⁻¹ g
        rw [inv_mul_cancel, hc1] at h1
        rw [eq_neg_of_add_eq_zero_left h1.symm]
        exact neg_mem (hθ _ le_sup_left _ _ hg j) }
  have hcl : ∀ i, IsClosed (H i : Set Γ) := fun i => by
    haveI := hK i
    haveI : FiniteDimensional ℚ_[l] (K₀ ⊔ K i).toSubalgebra.toSubmodule :=
      (inferInstance : FiniteDimensional ℚ_[l] (K₀ ⊔ K i : IntermediateField ℚ_[l] (PadicAlgCl l)))
    have : (H i : Set Γ) = ⋂ j, (fun g => c g j) ⁻¹' ((K₀ ⊔ K i).toSubalgebra.toSubmodule : Set (PadicAlgCl l)) := by
      ext g
      rw [Set.mem_iInter]
      exact Iff.rfl
    rw [this]
    exact isClosed_iInter fun j =>
      (Submodule.closed_of_finiteDimensional (K₀ ⊔ K i).toSubalgebra.toSubmodule).preimage
        ((continuous_apply j).comp hc)
  have hun : ⋃ i, (H i : Set Γ) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨i, hi⟩ := hcov (Set.range (c g)) (Set.finite_range _)
    exact Set.mem_iUnion.2 ⟨i, fun j => (le_sup_right : K i ≤ K₀ ⊔ K i) (hi ⟨j, rfl⟩)⟩
  obtain ⟨i, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hcl hun
  have hop : IsOpen (H i : Set Γ) := Subgroup.isOpen_of_mem_nhds _ (mem_interior_iff_mem_nhds.1 hx)
  haveI : Finite (Γ ⧸ H i) := Subgroup.quotient_finite_of_isOpen _ hop
  haveI := fd_adjoin_range l (fun q : (Γ ⧸ H i) × Fin n => c q.1.out q.2)
  haveI := hK i
  refine ⟨IntermediateField.adjoin ℚ_[l] (Set.range fun q : (Γ ⧸ H i) × Fin n => c q.1.out q.2) ⊔ (K₀ ⊔ K i),
    inferInstance, le_sup_left.trans le_sup_right, fun g j => ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (H i) g
  have hg : g = (g : Γ ⧸ H i).out * (h : Γ)⁻¹ := by
    rw [hh, mul_inv_cancel_right]
  rw [hg, hcoc]
  refine add_mem ?_ (hθ _ (le_sup_left.trans le_sup_right) _ _ (fun k => ?_) j)
  · exact (le_sup_left :
        IntermediateField.adjoin ℚ_[l] (Set.range fun q : (Γ ⧸ H i) × Fin n => c q.1.out q.2) ≤ _)
      (IntermediateField.subset_adjoin _ _ ⟨((g : Γ ⧸ H i), j), rfl⟩)
  · exact (le_sup_right : K₀ ⊔ K i ≤ _) ((H i).inv_mem h.2 k)
end

