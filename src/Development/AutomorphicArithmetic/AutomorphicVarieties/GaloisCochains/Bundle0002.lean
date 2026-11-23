module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.InflKer
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

namespace UpperTheory.V.GC

private theorem inflKer_lin {k W P H : Type} [Field k] [AddCommGroup W] [Module k W] [AddCommGroup P] [Module k P]
    [AddCommGroup H] [Module k H] [Module.Finite k P] (r : W →ₗ[k] P) (τ : W →ₗ[k] H)
    (h : LinearMap.ker r ≤ LinearMap.ker τ) (U : Submodule k P) (hU : U ≤ (LinearMap.ker τ).map r) :
    Module.Finite k (LinearMap.range τ) ∧ finrank k (LinearMap.range τ) + finrank k U ≤ finrank k P := by
  let K := (LinearMap.ker τ).map r
  let s : W →ₗ[k] P ⧸ K := K.mkQ.comp r
  have hs : LinearMap.ker s = LinearMap.ker τ := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.comap_map_eq, sup_eq_left.2 h]
  have e : LinearMap.range s ≃ₗ[k] LinearMap.range τ :=
    s.quotKerEquivRange.symm.trans ((Submodule.quotEquivOfEq _ _ hs).trans τ.quotKerEquivRange)
  refine ⟨Module.Finite.equiv e, ?_⟩
  rw [← e.finrank_eq, ← K.finrank_quotient_add_finrank]
  exact add_le_add (Submodule.finrank_le _) (Submodule.finrank_mono hU)

section

variable {Γ' Γ k M : Type} [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ'] [Group Γ] [TopologicalSpace Γ]
  [Field k] [AddCommGroup M] [Module k M] [TopologicalSpace M] [DiscreteTopology M]
  (p : Γ' →* Γ) (hp : Continuous p) (ρ : Representation k Γ M)

private def inflW : Submodule k (Z2 ρ × (Γ' → M)) where
  carrier := {x | Continuous x.2 ∧ x.2 1 = 0 ∧ ∀ g h, ρ (p g) (x.2 h) - x.2 (g * h) + x.2 g = x.1.1 (p g, p h)}
  zero_mem' := ⟨continuous_const, rfl, by simp⟩
  add_mem' := by
    rintro x y ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    refine ⟨a1.add b1, by simp [a2, b2], fun g h => ?_⟩
    simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, map_add (f := _), Submodule.coe_add, ← a3, ← b3]
    abel
  smul_mem' := by
    rintro c x ⟨a1, a2, a3⟩
    refine ⟨a1.const_smul c, by simp [a2], fun g h => ?_⟩
    simp only [Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, map_smul, Submodule.coe_smul, ← a3, smul_add, smul_sub]

omit [IsTopologicalGroup Γ'] in
private theorem inflW_mul (x : inflW p ρ) (n : Γ') (hn : p n = 1) (g : Γ') :
    x.1.2 (n * g) = x.1.2 n + x.1.2 g ∧ x.1.2 (g * n) = x.1.2 g + ρ (p g) (x.1.2 n) := by
  obtain ⟨⟨z, β⟩, -, h1, h⟩ := x
  dsimp only at h1 h ⊢
  have a := h 1 g
  have b := h g 1
  have c := h n g
  have d := h g n
  simp only [h1, hn, map_one, one_mul, mul_one, map_zero, Module.End.one_apply] at a b c d
  rw [← a] at c
  rw [← b] at d
  constructor
  · linear_combination (norm := abel1) -c
  · linear_combination (norm := abel1) -d

omit [IsTopologicalGroup Γ'] in
private theorem inflW_conj (x : inflW p ρ) (n : Γ') (hn : p n = 1) (g : Γ') :
    x.1.2 (g * n * g⁻¹) = ρ (p g) (x.1.2 n) := by
  have a := (inflW_mul p ρ x (g * n * g⁻¹) (by simp [hn]) g).1
  have b := (inflW_mul p ρ x n hn g).2
  rw [inv_mul_cancel_right, b, add_comm] at a
  exact (add_right_cancel a).symm

private theorem inflW_desc [CompactSpace Γ'] [T2Space Γ] (hp : Continuous p) (hs : Function.Surjective p)
    (S : Set Γ') (hS : p.ker = (Subgroup.normalClosure S).topologicalClosure) (x : inflW p ρ)
    (hx : ∀ s ∈ S, x.1.2 s = 0) : ∃ b : Γ → M, Continuous b ∧ ∀ g, b (p g) = x.1.2 g := by
  let N : Subgroup Γ' :=
    { carrier := {n | p n = 1 ∧ x.1.2 n = 0}
      one_mem' := ⟨map_one _, x.2.2.1⟩
      mul_mem' := by
        rintro a b ⟨a1, a2⟩ ⟨b1, b2⟩
        exact ⟨by simp [a1, b1], by rw [(inflW_mul p ρ x a a1 b).1, a2, b2, add_zero]⟩
      inv_mem' := by
        rintro a ⟨a1, a2⟩
        refine ⟨by simp [a1], ?_⟩
        have := (inflW_mul p ρ x a a1 a⁻¹).1
        rw [mul_inv_cancel, x.2.2.1, a2, zero_add] at this
        exact this.symm }
  haveI : N.Normal := ⟨fun n hn g => ⟨by simp [hn.1], by rw [inflW_conj p ρ x n hn.1, hn.2, map_zero]⟩⟩
  have hc : IsClosed (N : Set Γ') :=
    (isClosed_eq hp continuous_const).inter (isClosed_eq x.2.1 continuous_const)
  have hN : p.ker ≤ N := by
    rw [hS]
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun s h => ⟨?_, hx s h⟩) hc
    have : s ∈ p.ker := hS ▸ Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure h)
    exact this
  have hb : ∀ g, x.1.2 (Function.surjInv hs (p g)) = x.1.2 g := fun g => by
    have h1 : p (g⁻¹ * Function.surjInv hs (p g)) = 1 := by simp [Function.surjInv_eq hs]
    have := (inflW_mul p ρ x _ h1 g).2
    rw [mul_inv_cancel_left, (hN h1).2, map_zero, add_zero] at this
    exact this
  refine ⟨fun γ => x.1.2 (Function.surjInv hs γ), ?_, hb⟩
  rw [(hp.isClosedMap.isQuotientMap hp hs).continuous_iff]
  exact x.2.1.congr fun g => (hb g).symm

private def inflR {T : Type} (Dq Jq : T → Subgroup Γ') (hJ : ∀ q, Jq q ≤ p.ker) :
    inflW p ρ →ₗ[k] ∀ q, eqHom (ρ.comp p) (Dq q) (Jq q) where
  toFun x q := ⟨fun j => x.1.2 j, (IsLocallyConstant.iff_continuous _).2 (x.2.1.comp continuous_subtype_val),
    fun a b => (inflW_mul p ρ x a (hJ q a.2) b).1, fun d _ j j' h => by
      dsimp only
      rw [h]
      exact inflW_conj p ρ x j (hJ q j.2) d⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def inflJ : Z1 (ρ.comp p) →ₗ[k] inflW p ρ where
  toFun f := ⟨(0, f.1), f.2.1, by simpa using f.2.2 1 1, fun g h => by
    dsimp only
    rw [f.2.2]
    simp⟩
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

omit [IsTopologicalGroup Γ'] in
private theorem inflW_range :
    LinearMap.range ((Submodule.mkQ _ : Z2 ρ →ₗ[k] H2 ρ) ∘ₗ LinearMap.fst _ _ _ ∘ₗ (inflW p ρ).subtype) =
      LinearMap.ker (resH2 ρ p hp) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    refine (Submodule.Quotient.mk_eq_zero _).2 ((separated_dvr_second_cohomology_mem _ _).2 ⟨x.1.2, x.2.1, ?_⟩)
    funext q
    exact x.2.2.2 q.1 q.2
  · intro y hy
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨β, hβ, he⟩ := (separated_dvr_second_cohomology_mem _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hy)
    have he' : ∀ g h, ρ (p g) (β h) - β (g * h) + β g = z.1 (p g, p h) := fun g h => congrFun he (g, h)
    let c : Z2 ρ := ⟨fun q => ρ q.1 (β 1), ?_, fun g h k => by simp⟩
    · refine ⟨⟨(z - c, fun g => β g - β 1), hβ.sub continuous_const, sub_self _, fun g h => ?_⟩, ?_⟩
      · simp only [c, Submodule.coe_sub, Pi.sub_apply, ← he', map_sub]
        abel
      · refine (Submodule.Quotient.eq _).2 ((separated_dvr_second_cohomology_mem _ _).2 ⟨fun _ => -β 1, continuous_const, ?_⟩)
        funext q
        simp [c, d1]
    · have h1 : β 1 = z.1 (1, 1) := by simpa using he' 1 1
      have h2 : ∀ g, ρ g (z.1 (1, 1)) = z.1 (g, 1) := fun g => by
        have := z.2.2 g 1 1
        simp only [mul_one, sub_add_cancel] at this
        exact sub_eq_zero.1 this
      simp only [h1, h2]
      exact z.2.1.comp (continuous_fst.prodMk continuous_const)

end

end UpperTheory.V.GC

theorem UpperTheory.V.GC.inflKer :
    ∀ (l : ℕ) [Fact l.Prime] (Γ' : Type) [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ'] [CompactSpace Γ'] [T2Space Γ'] [TotallyDisconnectedSpace Γ'] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (p : Γ' →* Γ) (hp : Continuous p), Function.Surjective p →
    ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k Γ M), ContAction ρ → ∀ (T : Type) [Fintype T] (Dq Jq : T → Subgroup Γ'), p.ker = (Subgroup.normalClosure (⋃ q, (Jq q : Set Γ'))).topologicalClosure →
    (∀ q, Module.Finite k (eqHom (ρ.comp p) (Dq q) (Jq q))) → Module.Finite k (H1 (ρ.comp p)) →
    Module.Finite k (H1 ρ) ∧ Module.Finite k (LinearMap.ker (resH2 ρ p hp)) ∧
    finrank k (LinearMap.ker (resH2 ρ p hp)) + finrank k (H1 (ρ.comp p)) ≤ finrank k (H1 ρ) + ∑ q, finrank k (eqHom (ρ.comp p) (Dq q) (Jq q)) := by
  intro l _ Γ' _ _ _ _ _ _ Γ _ _ _ _ _ _ p hp hs k _ _ _ M _ _ _ _ _ ρ _ T _ Dq Jq hker hfin hH
  have hJ : ∀ q, Jq q ≤ p.ker := fun q s h =>
    hker ▸ Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure (Set.mem_iUnion.2 ⟨q, h⟩))
  let r := inflR p ρ Dq Jq hJ
  have hd : ∀ x, r x = 0 → ∃ b : Γ → M, Continuous b ∧ ∀ g, b (p g) = x.1.2 g := fun x hx =>
    inflW_desc p ρ hp hs _ hker x fun s h => by
      obtain ⟨q, hq⟩ := Set.mem_iUnion.1 h
      exact congrFun (congrArg Subtype.val (congrFun hx q)) ⟨s, hq⟩
  have hinj : Function.Injective (resH1 ρ p hp) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hy)
    refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩)
    obtain ⟨g, rfl⟩ := hs g
    exact hm g
  haveI hF : Module.Finite k (H1 ρ) := Module.Finite.of_injective _ hinj
  let r1 : H1 (ρ.comp p) →ₗ[k] ∀ q, eqHom (ρ.comp p) (Dq q) (Jq q) :=
    Submodule.liftQ _ (r.comp (inflJ p ρ)) fun f hf => by
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hf
      funext q
      refine Subtype.ext (funext fun j => (hm j).trans ?_)
      have : p j = 1 := hJ q j.2
      simp [this]
  have hk1 : LinearMap.ker r1 ≤ LinearMap.range (resH1 ρ p hp) := by
    intro y hy
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨b, hb, he⟩ := hd (inflJ p ρ z) hy
    refine ⟨Submodule.Quotient.mk ⟨b, hb, fun g h => ?_⟩, congrArg _ (Subtype.ext (funext he))⟩
    obtain ⟨g, rfl⟩ := hs g
    obtain ⟨h, rfl⟩ := hs h
    rw [← map_mul, he, he, he]
    exact z.2.2 g h
  obtain ⟨h1, h2⟩ := inflKer_lin r
    ((Submodule.mkQ _ : Z2 ρ →ₗ[k] H2 ρ) ∘ₗ LinearMap.fst _ _ _ ∘ₗ (inflW p ρ).subtype) (fun x hx => by
      obtain ⟨b, hb, he⟩ := hd x hx
      refine (Submodule.Quotient.mk_eq_zero _).2 ((separated_dvr_second_cohomology_mem _ _).2 ⟨b, hb, ?_⟩)
      funext ⟨g, h⟩
      obtain ⟨g, rfl⟩ := hs g
      obtain ⟨h, rfl⟩ := hs h
      rw [d1_apply, ← map_mul, he, he, he]
      exact x.2.2.2 g h) (LinearMap.range r1) (by
      rintro _ ⟨y, rfl⟩
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨inflJ p ρ z, (Submodule.mkQ _).map_zero, rfl⟩)
  rw [inflW_range p hp ρ] at h1 h2
  refine ⟨hF, h1, ?_⟩
  rw [Module.finrank_pi_fintype] at h2
  have h3 := r1.finrank_range_add_finrank_ker
  have h4 := (Submodule.finrank_mono hk1).trans (LinearMap.finrank_range_le _)
  have h5 : finrank k (H1 (ρ.comp p)) ≤ finrank k (LinearMap.range r1) + finrank k (H1 ρ) :=
    h3.symm.le.trans (Nat.add_le_add_left h4 _)
  refine (Nat.add_le_add_left h5 _).trans ?_
  rw [← add_assoc, add_comm]
  exact Nat.add_le_add_left h2 _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.LocEuler
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

private noncomputable def subquotEquiv {R R' X : Type*} [CommRing R] [CommRing R'] [AddCommGroup X]
    [Module R X] [Module R' X] (Z B : Submodule R X) (Z' B' : Submodule R' X)
    (hZ : ∀ x, x ∈ Z ↔ x ∈ Z') (hB : ∀ x, x ∈ B ↔ x ∈ B') :
    (Z ⧸ B.comap Z.subtype) ≃ (Z' ⧸ B'.comap Z'.subtype) :=
  Quotient.congr (Equiv.subtypeEquivRight hZ) fun a b => by
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def]
    exact hB _

private theorem card_H0dual {R k Γ Γ' M : Type} [Field R] [Field k] [Finite k] [Algebra R k] [Group Γ] [Group Γ']
    [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower R k M] [Finite M]
    (ρ : Representation k Γ M) (ρ' : Representation R Γ' M) (e : Γ' ≃* Γ) (h : ∀ g m, ρ' g m = ρ (e g) m)
    (χ : Γ →* kˣ) (χ' : Γ' →* Rˣ) (hχ : ∀ g, (χ (e g) : k) = algebraMap R k (χ' g)) :
    Nat.card (Loc.H0dual χ ρ) = Nat.card (Loc.H0dual χ' ρ') := by
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

private theorem card_twDual {R Γ M : Type} [CommRing R] [Group Γ] [AddCommGroup M] [Module R M]
    (χ : Γ →* Rˣ) (ρ : Representation R Γ M) :
    Nat.card (H0 ((twDual χ ρ).comp (MonoidHom.id Γ))) = Nat.card (Loc.H0dual χ ρ) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight (α := TDual R M) fun y => ?_)
  constructor
  · intro hy g m
    have e := congrArg (fun φ : TDual R M => φ (ρ g m)) (hy g)
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, twDual_apply] at e
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at e
    exact e.symm
  · intro hy g
    refine LinearMap.ext fun m => ?_
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, twDual_apply]
    have := hy g (ρ g⁻¹ m)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
    exact this.symm

theorem UpperTheory.V.GC.locEuler :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k (Dec (F := F) A) M), ContAction ρ →
    Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧ (((l : ℕ) : 𝓞 F) ∈ v.asIdeal → finrank k (H1 ρ) = finrank k (H0 ρ) + finrank k (H2 ρ) + locDeg v * finrank k M) ∧
    (((l : ℕ) : 𝓞 F) ∉ v.asIdeal → finrank k (H1 ρ) = finrank k (H0 ρ) + finrank k (H2 ρ)) ∧ finrank k (H2 ρ) = finrank k (Loc.H0dual ((cycF F Ω l k).comp (Dec (F := F) A).subtype) ρ) := by
  intro hF hT hE0 F Ω _ _ _ _ _ l _ w A hAw k _ _ hc M _ _ _ _ _ ρ hρ
  have hl : l.Prime := Fact.out
  haveI : Fact (l ^ 1).Prime := ⟨by rwa [pow_one]⟩
  haveI : CharP k (l ^ 1) := by rwa [pow_one]
  letI : Algebra (ZMod (l ^ 1)) k := ZMod.algebra k (l ^ 1)
  letI : Module (ZMod (l ^ 1)) M := Module.compHom M (algebraMap (ZMod (l ^ 1)) k)
  haveI : IsScalarTower (ZMod (l ^ 1)) k M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Finite M := Module.finite_of_finite k
  let ρ' : Representation (ZMod (l ^ 1)) ↥(Dec (F := F) A) M := Loc.resCoef (ZMod (l ^ 1)) ρ
  have h : ∀ g m, ρ' g m = ρ (MulEquiv.refl _ g) m := fun _ _ => rfl
  have hρ' : ContAction ρ' := hρ
  have e0 : H0 ρ ≃ H0 ρ' := Equiv.subtypeEquivRight fun _ => Iff.rfl
  have e1 : H1 ρ ≃ H1 ρ' := subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have e2 : H2 ρ ≃ H2 ρ' := subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  obtain ⟨-, f1, f2, -⟩ := hF F Ω l 1 M A ρ' w one_pos hAw hρ'
  obtain ⟨⟨inv⟩, -, -, -, hb⟩ := hT F Ω l 1 M A ρ' w one_pos hAw hρ'
  have hE := hE0 F Ω l 1 M A ρ' w one_pos hAw hρ'
  haveI : Finite (H1 ρ) := Finite.of_equiv _ e1.symm
  haveI : Finite (H2 ρ) := Finite.of_equiv _ e2.symm
  have hk : 1 < Nat.card k := Finite.one_lt_card
  refine ⟨Module.Finite.of_finite, Module.Finite.of_finite, fun hw => ?_, fun hw => ?_, ?_⟩
  · apply Nat.pow_right_injective hk
    beta_reduce
    rw [pow_add, pow_add, mul_comm (locDeg w), pow_mul, ← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank,
      ← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank, Nat.card_congr e0, Nat.card_congr e1,
      Nat.card_congr e2]
    exact hE.1 hw
  · apply Nat.pow_right_injective hk
    beta_reduce
    rw [pow_add, ← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank,
      ← Module.natCard_eq_pow_finrank, Nat.card_congr e0, Nat.card_congr e1, Nat.card_congr e2]
    exact hE.2 hw
  · apply Nat.pow_right_injective hk
    beta_reduce
    let χ := (cycMod F Ω l 1).comp (Dec (F := F) A).subtype
    haveI : Finite (Module.Dual k M) := DFunLike.finite _
    haveI : Finite (TDual (ZMod (l ^ 1)) M) := (DFunLike.finite _ : Finite (M →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)))
    let B : Type := H0 ((twDual χ ρ').comp (MonoidHom.id _))
    let E : H2 ρ' ≃ Module.Dual (ZMod (l ^ 1)) B :=
      (Equiv.ofBijective _ hb).trans (LinearEquiv.congrRight inv).toEquiv
    haveI : Finite B := Subtype.finite
    haveI := hc
    have hχ : ∀ g, ((((cycF F Ω l k).comp (Dec (F := F) A).subtype) (MulEquiv.refl _ g) : kˣ) : k) =
        algebraMap (ZMod (l ^ 1)) k (χ g) := fun g =>
      RingHom.congr_fun (Subsingleton.elim (ZMod.castHom (dvd_pow_self l one_ne_zero) k)
        (algebraMap (ZMod (l ^ 1)) k)) _
    rw [← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank, Nat.card_congr e2,
      card_H0dual ρ ρ' (MulEquiv.refl _) h _ χ hχ,
      ← card_twDual, Nat.card_congr E, Module.natCard_eq_pow_finrank (K := ZMod (l ^ 1)),
      Subspace.dual_finrank_eq, ← Module.natCard_eq_pow_finrank]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.PhiGam
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

private theorem pG_nat {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ v ∈ S, ((N : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  refine ⟨∏ v ∈ S, Ideal.absNorm v.asIdeal, Finset.prod_ne_zero_iff.2 fun v _ h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h),
    fun v hv => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 F) => Ideal.absNorm v.asIdeal) hv
  rw [hc, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

private theorem pG_lc {H M : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [Group M]
    (φ : H →* M) (h : IsOpen (φ.ker : Set H)) : IsLocallyConstant φ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have ho : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (φ.ker : Set H)) := h.preimage (by fun_prop)
  filter_upwards [ho.mem_nhds (show x ∈ (fun y => x⁻¹ * y) ⁻¹' (φ.ker : Set H) by simp)] with y hy
  have : φ (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this.symm

theorem UpperTheory.V.GC.phiGam :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (π : G F Ω →* Γ), GLink l S K π → Alg.PhiCond Γ l := by
  intro F Ω _ _ _ _ _ l hl S K Γ _ _ _ _ _ _ π hL H hH
  haveI : IsGalois F Ω := {}
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  obtain ⟨N, hN, hNS⟩ := pG_nat S
  let V : Subgroup (G F Ω) := (H.comap π ⊓ K) ⊓ MulAction.stabilizer (G F Ω) ζ
  have hVo : IsOpen (V : Set (G F Ω)) :=
    ((hH.preimage hL.cont).inter hL.isOpen).inter (stabilizer_isOpen_of_isIntegral ζ)
  let E : IntermediateField F Ω := IntermediateField.fixedField V
  have hE : E.fixingSubgroup = V :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨V, V.isClosed_of_isOpen hVo⟩
  haveI : FiniteDimensional F E := (InfiniteGalois.isOpen_iff_finite E).1 (by rw [← hE] at hVo; exact hVo)
  haveI : NumberField E := NumberField.of_module_finite F E
  have hmem : ∀ σ : G E Ω, Base.galEmb F E Ω σ ∈ V := fun σ => by
    rw [← hE, IntermediateField.mem_fixingSubgroup_iff]
    exact fun x hx => σ.commutes ⟨x, hx⟩
  have hgal : V ≤ Base.galOf F E Ω := fun u hu x => x.2 ⟨u, hu⟩
  have hζE : ζ ∈ E := fun v => v.2.2
  have hζ' : IsPrimitiveRoot (⟨ζ, hζE⟩ : E) l :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap E Ω) hζ (algebraMap E Ω).injective
  haveI := (Kum.finChar E Ω l N _ hl.out.ne_zero hN hζ').to_subtype
  let e : G E Ω →* H := (π.comp (Base.galEmb F E Ω)).codRestrict H fun σ => (hmem σ).1.1
  have he : Continuous e := (hL.cont.comp (Base.galEmbTop F E Ω).1.continuous).subtype_mk _
  have hker : ∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → ∀ g ∈ Ine (F := E) A, e g = 1 := by
    intro A hA g hg
    by_cases hT : A = ⊤
    · subst hT
      rw [(Kum.placeDict E Ω).1, Subgroup.mem_bot] at hg
      rw [hg, map_one]
    · obtain ⟨v, hv⟩ := (Kum.placeDict F Ω).2.1 A hT
      have hvS : v ∉ S := fun h => hA (((Kum.placeDict F Ω).2.2.2 A v N hv).2 (hNS v h))
      have hI : Base.galEmb F E Ω g ∈ Ine (F := F) A := ⟨hg.1, hg.2⟩
      have : Base.galEmb F E Ω g ∈ π.ker := by
        rw [hL.ker]
        refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
        simp only [Set.mem_iUnion]
        exact ⟨v, hvS, A, hv, hI, (hmem g).1.2⟩
      exact Subtype.ext this
  haveI : Finite (G F Ω ⧸ V) := V.quotient_finite_of_isOpen hVo
  have hfin : Finite (H ⧸ e.range) := by
    haveI : V.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    have h1 : (V.map π).FiniteIndex :=
      ⟨fun h => Subgroup.FiniteIndex.index_ne_zero (H := V)
        (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_map_dvd V hL.onto))⟩
    have h2 : (V.map π).subgroupOf H ≤ e.range := by
      rintro x ⟨u, hu, hx⟩
      exact ⟨Kum.toGal E hgal ⟨u, hu⟩, Subtype.ext hx⟩
    haveI := Subgroup.finiteIndex_of_le h2
    infer_instance
  refine Finite.of_injective (β := {φ : G E Ω → ZMod l | IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧
      ∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → ∀ g ∈ Ine (F := E) A, φ g = 0} ×
      (H ⧸ e.range → Multiplicative (ZMod l)))
    (fun φ => (⟨fun g => Multiplicative.toAdd (φ.1 (e g)), ((pG_lc φ.1 φ.2).comp_continuous he).comp _,
      fun a b => by simp only [map_mul, toAdd_mul], fun A hA g hg => by
        show Multiplicative.toAdd (φ.1 (e g)) = 0
        rw [hker A hA g hg, map_one, toAdd_one]⟩, fun q => φ.1 q.out)) ?_
  intro φ ψ h
  have h1 : ∀ g, φ.1 (e g) = ψ.1 (e g) := fun g =>
    Multiplicative.toAdd.injective (congrFun (congrArg Subtype.val (congrArg Prod.fst h)) g)
  have h2 : ∀ q : H ⧸ e.range, φ.1 q.out = ψ.1 q.out := congrFun (congrArg Prod.snd h)
  refine Subtype.ext (MonoidHom.ext fun x => ?_)
  obtain ⟨⟨_, g, rfl⟩, hg⟩ := QuotientGroup.mk_out_eq_mul e.range x
  have h3 := h2 (QuotientGroup.mk x)
  rw [hg, map_mul, map_mul, h1] at h3
  exact mul_right_cancel h3
end

