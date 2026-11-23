module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0029

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSqz
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.co_sqz :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (M : Type) [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [Module O M] [IsScalarTower O R M] [Module.Finite R M] [Algebra O (TrivSqZeroExt R M)],
      (∀ c : O, algebraMap O (TrivSqZeroExt R M) c = TrivSqZeroExt.inl (algebraMap O R c)) → IsCO O (TrivSqZeroExt R M) := by
  intro O _ _ R _ _ _ M _ _ _ _ _ _ _ _ hO
  haveI : IsLocalRing (TrivSqZeroExt R M) :=
    IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
      simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
      exact IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst
  haveI hST := IsScalarTower.of_algebraMap_eq (R := O) (S := R) (A := TrivSqZeroExt R M) fun c => by
    rw [hO, TrivSqZeroExt.algebraMap_eq_inl]
  haveI : Module.Finite R (TrivSqZeroExt R M) := inferInstanceAs (Module.Finite R (R × M))
  refine co_finite O R (TrivSqZeroExt R M) ?_
  intro x
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x.fst
  refine ⟨a, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, hO,
    TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl]
  rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CocycleNormalForm
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.cocycle_normal_form :
    ∀ (k Γ M : Type) [CommRing k] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module k M] (F : Frame Γ) (ρ : Representation k Γ M), (∀ m : M, IsLocallyConstant fun s => ρ s m) → (∀ q, ∀ n ∈ F.N q, ∀ m, ρ (F.ψ q n) m = m) →
          ∀ x ∈ F.framedTwoCoboundaries ρ, ∃ (h : Γ → M) (y : F.T → M), IsLocallyConstant h ∧ y F.v0 = 0 ∧ x.1 = dOne ρ h ∧ (∀ v s, x.2.1 v s = h (F.φ v s) - (ρ (F.φ v s) (y v) - y v)) ∧ ∀ q, ∀ n ∈ F.N q, x.2.2 q n = h (F.ψ q n) := by
  intro k Γ M _ _ _ _ _ F ρ hρ hN x hx
  unfold Frame.framedTwoCoboundaries at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, y, e, h1, h2, h3, h4, h5⟩ := hx
    refine ⟨fun s => h s - (ρ s (y F.v0) - y F.v0), fun v => y v - y F.v0,
      h1.sub ((hρ _).sub (IsLocallyConstant.const _)), sub_self _, ?_, fun v s => ?_, fun q n hn => ?_⟩
    · rw [h3]
      funext p
      simp only [dOne, map_sub, map_mul, Module.End.mul_apply]
      abel
    · rw [h4]
      simp only [map_sub]
      abel
    · rw [h5, (h2 q).2.2 n hn]
      simp only [hN q n hn, sub_self]
  | zero =>
    refine ⟨0, 0, IsLocallyConstant.const 0, rfl, ?_, by simp, by simp⟩
    funext p
    simp [dOne]
  | add x x' _ _ ih ih' =>
    obtain ⟨h, y, a1, a2, a3, a4, a5⟩ := ih
    obtain ⟨h', y', b1, b2, b3, b4, b5⟩ := ih'
    refine ⟨h + h', y + y', a1.add b1, by simp [a2, b2], ?_, fun v s => ?_, fun q n hn => ?_⟩
    · funext p
      simp only [Prod.fst_add, Pi.add_apply, a3, b3, dOne, map_add (f := _)]
      abel
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, a4, b4, map_add (f := _)]
      abel
    · simp only [Prod.snd_add, Pi.add_apply, a5 q n hn, b5 q n hn]
  | smul c x _ ih =>
    obtain ⟨h, y, a1, a2, a3, a4, a5⟩ := ih
    refine ⟨c • h, c • y, a1.comp (c • ·), by simp [a2], ?_, fun v s => ?_, fun q n hn => ?_⟩
    · funext p
      simp [a3, dOne, smul_sub]
    · simp [a4, smul_sub]
    · simp [a5 q n hn]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ContSection
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem chain_stab {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (K : Ideal R)
    (hK : maximalIdeal R * K = ⊥) (F : ℕ → Ideal R) (hF : Antitone F) (hle : ∀ n, F n ≤ K) :
    ∃ N, ∀ n, F N ≤ F n := by
  classical
  have hT : Module.IsTorsionBySet R K (maximalIdeal R : Set R) := by
    intro x a
    apply Subtype.ext
    have h1 : (a : R) * (x : R) ∈ maximalIdeal R * K := Ideal.mul_mem_mul a.2 x.2
    rw [hK] at h1
    simpa using h1
  letI : Module (R ⧸ maximalIdeal R) K := hT.module
  haveI : IsScalarTower R (R ⧸ maximalIdeal R) K := hT.isScalarTower
  haveI : Module.Finite R K := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian K)
  haveI : Module.Finite (R ⧸ maximalIdeal R) K :=
    Module.Finite.of_restrictScalars_finite R _ _
  letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  haveI : IsArtinianRing (R ⧸ maximalIdeal R) := inferInstance
  haveI : IsArtinian (R ⧸ maximalIdeal R) K := isArtinian_of_fg_of_artinian'
  haveI : IsArtinian R K := isArtinian_of_surjective_algebraMap (R := R ⧸ maximalIdeal R)
    (Ideal.Quotient.mk_surjective (I := maximalIdeal R))
  let G : ℕ → Submodule R K := fun n => Submodule.comap (Submodule.subtype K) (F n)
  have hG : Antitone G := fun a b h => Submodule.comap_mono (hF h)
  obtain ⟨_, ⟨N, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule R K)).has_min (Set.range G) ⟨_, 0, rfl⟩
  refine ⟨N, fun n => ?_⟩
  have hle2 : G (max N n) ≤ G N := hG (le_max_left _ _)
  have heq : G (max N n) = G N := by
    by_contra hne
    exact hmin _ ⟨_, rfl⟩ (lt_of_le_of_ne hle2 hne)
  intro x hx
  have hxK : x ∈ K := hle N hx
  have h2 : (⟨x, hxK⟩ : K) ∈ G N := hx
  rw [← heq] at h2
  exact hF (le_max_right N n) h2

private theorem mul_mem_of_mem_ideal_killed_by_maximalIdeal {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R]
    [IsCO O R] (J : Ideal R) (hJ : maximalIdeal R * J = ⊥) (S : Submodule O R) (r k : R)
    (hk : k ∈ J) (hS : k ∈ S) : r * k ∈ S := by
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) r
  have h0 : (r - algebraMap O R a) * k = 0 := by
    have h1 := Ideal.mul_mem_mul ha hk
    rw [hJ] at h1
    exact (Ideal.mem_bot).1 h1
  have h2 : r * k = a • k := by
    rw [Algebra.smul_def]
    linear_combination h0
  rw [h2]
  exact S.smul_mem a hS

theorem UpperTheory.V.Alg.cont_section :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (p : R →ₐ[O] R'), Function.Surjective p → maximalIdeal R * RingHom.ker p = ⊥ → ∀ (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) →
      ∀ (Γ : Type) [TopologicalSpace Γ] (j : X) (x : Γ → R'), AdicCont (maximalIdeal R') x → (∀ g, x g ∈ (W.part j).map p.toLinearMap) →
      ∃ y : Γ → R, AdicCont (maximalIdeal R) y ∧ (∀ g, y g ∈ W.part j) ∧ ∀ g, p (y g) = x g := by
  intro O _ _ _ _ X _ _ _ R _ _ _ R' _ _ _ p hp hker W hz Γ _ j x hxc hxp
  classical
  have hmem : ∀ r : R, p r ∈ maximalIdeal R' ↔ r ∈ maximalIdeal R := by
    intro r
    rw [← res_eq_zero_iff O R', ← res_eq_zero_iff O R, res_map]
  have hmapm : Ideal.map p (maximalIdeal R) = maximalIdeal R' := by
    ext a
    rw [Ideal.mem_map_iff_of_surjective p hp]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact (hmem r).2 hr
    · intro ha
      obtain ⟨r, rfl⟩ := hp a
      exact ⟨r, (hmem r).1 ha, rfl⟩
  have hlift : ∀ n (a : R'), a ∈ maximalIdeal R' ^ n → ∃ w, w ∈ maximalIdeal R ^ n ∧ p w = a := by
    intro n a ha
    rw [← hmapm, ← Ideal.map_pow] at ha
    exact (Ideal.mem_map_iff_of_surjective p hp).1 ha
  obtain ⟨N0, hN0⟩ := chain_stab (RingHom.ker p) hker (fun n => maximalIdeal R ^ n ⊓ RingHom.ker p)
    (fun a b h => inf_le_inf_right _ (Ideal.pow_le_pow_right h)) (fun n => inf_le_right)
  have hinj : ∀ u v : R, u ∈ maximalIdeal R ^ N0 → v ∈ maximalIdeal R ^ N0 → p u = p v → u = v := by
    intro u v hu hv huv
    have hk : u - v ∈ maximalIdeal R ^ N0 ⊓ RingHom.ker p :=
      ⟨Ideal.sub_mem _ hu hv, (RingHom.mem_ker).2 (by rw [map_sub, huv, sub_self])⟩
    have hall : u - v ∈ ⨅ n, maximalIdeal R ^ n := Ideal.mem_iInf.2 fun n => (hN0 n hk).1
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing (I := maximalIdeal R)
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top] at hall
    exact sub_eq_zero.1 ((Ideal.mem_bot).1 hall)
  let F : ℕ → Ideal R := fun n =>
    { carrier := {k | k ∈ RingHom.ker p ∧ k ∈ W.part j ⊔ (maximalIdeal R ^ n).restrictScalars O}
      add_mem' := fun ha hb => ⟨Ideal.add_mem _ ha.1 hb.1, Submodule.add_mem _ ha.2 hb.2⟩
      zero_mem' := ⟨Ideal.zero_mem _, Submodule.zero_mem _⟩
      smul_mem' := fun r k hk =>
        ⟨Ideal.mul_mem_left _ r hk.1, mul_mem_of_mem_ideal_killed_by_maximalIdeal (O := O) _ hker _ r k hk.1 hk.2⟩ }
  have hFanti : Antitone F := by
    intro a b h k hk
    have H : (maximalIdeal R ^ b).restrictScalars O ≤ (maximalIdeal R ^ a).restrictScalars O :=
      fun z hz => Ideal.pow_le_pow_right h hz
    exact ⟨hk.1, SetLike.le_def.1 (sup_le_sup_left H (W.part j)) hk.2⟩
  obtain ⟨N1, hN1⟩ := chain_stab (RingHom.ker p) hker F hFanti (fun n k hk => hk.1)
  have hclosed : ∀ k, k ∈ RingHom.ker p →
      k ∈ W.part j ⊔ (maximalIdeal R ^ N1).restrictScalars O → k ∈ W.part j := by
    intro k hk1 hk2
    have hkF : k ∈ F N1 := ⟨hk1, hk2⟩
    apply part_closed O X R W hz j k
    intro N
    obtain ⟨y, hy, z, hz2, hyz⟩ := Submodule.mem_sup.1 (hN1 N hkF).2
    refine ⟨y, hy, ?_⟩
    rw [← hyz, add_sub_cancel_left]
    exact hz2
  have hL : ∀ a, a ∈ (W.part j).map p.toLinearMap → a ∈ maximalIdeal R' ^ (max N0 N1) →
      ∃ w, w ∈ W.part j ∧ w ∈ maximalIdeal R ^ (max N0 N1) ∧ p w = a := by
    intro a ha haM
    obtain ⟨e, he, rfl⟩ := Submodule.mem_map.1 ha
    obtain ⟨w, hw, hpw⟩ := hlift _ _ haM
    have hk1 : e - w ∈ RingHom.ker p := by
      rw [RingHom.mem_ker, map_sub, hpw, AlgHom.toLinearMap_apply, sub_self]
    have hk2 : e - w ∈ W.part j ⊔ (maximalIdeal R ^ N1).restrictScalars O := by
      rw [sub_eq_add_neg]
      exact Submodule.add_mem_sup he
        (Submodule.neg_mem _ (Ideal.pow_le_pow_right (le_max_right _ _) hw))
    have hk := hclosed _ hk1 hk2
    refine ⟨w, ?_, hw, hpw⟩
    have h3 := Submodule.sub_mem _ he hk
    rwa [sub_sub_cancel] at h3
  let base : (R' ⧸ maximalIdeal R' ^ (max N0 N1)) → R := fun c =>
    if h : ∃ e, e ∈ W.part j ∧ Ideal.Quotient.mk (maximalIdeal R' ^ (max N0 N1)) (p e) = c
    then h.choose else 0
  have hbase : ∀ g, base (Ideal.Quotient.mk _ (x g)) ∈ W.part j ∧
      x g - p (base (Ideal.Quotient.mk _ (x g))) ∈ maximalIdeal R' ^ (max N0 N1) := by
    intro g
    obtain ⟨e, he, hpe⟩ := Submodule.mem_map.1 (hxp g)
    have h : ∃ e, e ∈ W.part j ∧ Ideal.Quotient.mk (maximalIdeal R' ^ (max N0 N1)) (p e) =
        Ideal.Quotient.mk _ (x g) := ⟨e, he, by rw [← hpe]; rfl⟩
    simp only [base]
    rw [dite_eq_left h]
    refine ⟨h.choose_spec.1, ?_⟩
    rw [← Ideal.Quotient.eq]
    exact h.choose_spec.2.symm
  have hw : ∀ g, ∃ w, w ∈ W.part j ∧ w ∈ maximalIdeal R ^ (max N0 N1) ∧
      p w = x g - p (base (Ideal.Quotient.mk _ (x g))) := by
    intro g
    apply hL
    · exact Submodule.sub_mem _ (hxp g) (Submodule.mem_map_of_mem (hbase g).1)
    · exact (hbase g).2
  choose w hwP hwM hwp using hw
  refine ⟨fun g => base (Ideal.Quotient.mk _ (x g)) + w g, ?_,
    fun g => Submodule.add_mem _ (hbase g).1 (hwP g), fun g => ?_⟩
  · unfold AdicCont at hxc ⊢
    intro N
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g0
    have hx0 := (IsLocallyConstant.iff_eventually_eq _).1 (hxc (max N (max N0 N1))) g0
    filter_upwards [hx0] with g hg
    have hd : x g - x g0 ∈ maximalIdeal R' ^ max N (max N0 N1) := Ideal.Quotient.eq.1 hg
    have hcls : Ideal.Quotient.mk (maximalIdeal R' ^ (max N0 N1)) (x g) =
        Ideal.Quotient.mk _ (x g0) :=
      Ideal.Quotient.eq.2 (Ideal.pow_le_pow_right (le_max_right _ _) hd)
    obtain ⟨v, hv, hpv⟩ := hlift _ _ hd
    have hM0 : maximalIdeal R ^ (max N0 N1) ≤ maximalIdeal R ^ N0 :=
      Ideal.pow_le_pow_right (le_max_left _ _)
    have heq : w g - w g0 = v := by
      apply hinj
      · exact Ideal.sub_mem _ (hM0 (hwM g)) (hM0 (hwM g0))
      · exact Ideal.pow_le_pow_right (le_trans (le_max_left _ _) (le_max_right _ _)) hv
      · rw [map_sub, hwp, hwp, hpv, hcls]
        ring
    apply Ideal.Quotient.eq.2
    show base (Ideal.Quotient.mk _ (x g)) + w g - (base (Ideal.Quotient.mk _ (x g0)) + w g0) ∈ _
    rw [hcls]
    have h4 : base (Ideal.Quotient.mk _ (x g0)) + w g -
        (base (Ideal.Quotient.mk _ (x g0)) + w g0) = v := by
      rw [← heq]
      ring
    rw [h4]
    exact Ideal.pow_le_pow_right (le_max_left _ _) hv
  · show p (base _ + w g) = x g
    rw [map_add (f := _), hwp]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ExistsLiftDominatingPairOfMaximalIdealPowEqBot
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem complete_of_pow {R : Type} [CommRing R] (I : Ideal R) (N : ℕ) (h : I ^ N = ⊥) :
    IsAdicComplete I R := by
  have hb : (I ^ N • ⊤ : Submodule R R) = ⊥ := by rw [h, Submodule.bot_smul]
  have key : ∀ x y : R, x ≡ y [SMOD (I ^ N • ⊤ : Submodule R R)] → x = y := by
    intro x y hxy
    rw [hb, SModEq.sub_mem, Submodule.mem_bot, sub_eq_zero] at hxy
    exact hxy
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    exact key x 0 (hx N)
  · intro f hf
    refine ⟨f N, fun n => ?_⟩
    rcases le_total n N with hn | hn
    · exact hf hn
    · have e := key _ _ (hf hn)
      rw [SModEq.sub_mem, e, sub_self]
      exact Submodule.zero_mem _

private theorem mk_inj {R : Type} [CommRing R] (I : Ideal R) (h : I = ⊥) :
    Function.Injective (Ideal.Quotient.mk I) := by
  subst h
  intro x y hxy
  rw [Ideal.Quotient.eq, Ideal.mem_bot, sub_eq_zero] at hxy
  exact hxy

private theorem finite_of_pow (O : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)]
    (A : Type) [CommRing A] [Algebra O A] [IsCO O A] (N : ℕ) (h : maximalIdeal A ^ N = ⊥) : Finite A := by
  haveI : Finite (ResidueField A) := Finite.of_surjective _ (resMap_bijective O A).2
  haveI : Finite (A ⧸ maximalIdeal A) := this
  haveI := Ideal.finite_quotient_pow (IsNoetherian.noetherian (maximalIdeal A)) N
  exact Finite.of_injective _ (mk_inj _ h)

private theorem sub_co (O : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] (N : ℕ)
    (A₁ : Type) [CommRing A₁] [Algebra O A₁] [IsCO O A₁] (A₂ : Type) [CommRing A₂] [Algebra O A₂] [IsCO O A₂]
    (h₁ : maximalIdeal A₁ ^ N = ⊥) (h₂ : maximalIdeal A₂ ^ N = ⊥) (B : Type) [CommRing B] [Algebra O B]
    (p₁ : B →ₐ[O] A₁) (p₂ : B →ₐ[O] A₂) (hinj : ∀ x y, p₁ x = p₁ y → p₂ x = p₂ y → x = y)
    (hres : ∀ x, res O A₁ (p₁ x) = res O A₂ (p₂ x)) :
    ∃ _ : IsCO O B, maximalIdeal B ^ N = ⊥ := by
  classical
  haveI : Finite A₁ := finite_of_pow O A₁ N h₁
  haveI : Finite A₂ := finite_of_pow O A₂ N h₂
  have hinj' : Function.Injective (fun x : B => (p₁ x, p₂ x)) := fun x y hxy =>
    hinj x y (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)
  haveI : Finite B := Finite.of_injective _ hinj'
  let φ : B →ₐ[O] ResidueField O := (res O A₁).comp p₁
  have hφ1 : ∀ x, φ x = res O A₁ (p₁ x) := fun x => rfl
  have hφ2 : ∀ x, φ x = res O A₂ (p₂ x) := fun x => hres x
  have hunit : ∀ x : B, φ x ≠ 0 → IsUnit x := by
    intro x hx
    have u1 : IsUnit (p₁ x) := by
      by_contra hn
      apply hx
      rw [hφ1, res_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hn
    have u2 : IsUnit (p₂ x) := by
      by_contra hn
      apply hx
      rw [hφ2, res_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hn
    have hmul : Function.Injective (fun y : B => x * y) := by
      intro y z hyz
      have e1 := congrArg p₁ hyz
      have e2 := congrArg p₂ hyz
      simp only [map_mul] at e1 e2
      exact hinj y z (u1.mul_left_cancel e1) (u2.mul_left_cancel e2)
    obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hmul) 1
    have hy' : x * y = 1 := hy
    exact ⟨⟨x, y, hy', by rw [mul_comm]; exact hy'⟩, rfl⟩
  have hnon : ∀ x : B, IsUnit x → φ x ≠ 0 := fun x hx => (hx.map φ).ne_zero
  haveI : Nontrivial B := ⟨⟨0, 1, fun h01 => by
    have e := congrArg φ h01
    rw [map_zero, map_one] at e
    exact zero_ne_one e⟩⟩
  haveI : IsLocalRing B := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    by_cases ha : φ a = 0
    · right
      apply hunit
      rw [map_sub, map_one, ha, sub_zero]
      exact one_ne_zero
    · left
      exact hunit a ha
  have hmax : ∀ x : B, x ∈ maximalIdeal B ↔ φ x = 0 := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro hx
      by_contra hne
      exact hx (hunit x hne)
    · intro hx hu
      exact hnon x hu hx
  haveI : IsNoetherian B B := inferInstance
  have hpow : maximalIdeal B ^ N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Ideal.mem_bot]
    have m1 : Ideal.map p₁ (maximalIdeal B) ≤ maximalIdeal A₁ := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      rw [Ideal.mem_comap, ← res_eq_zero_iff O, ← hφ1]
      exact (hmax y).mp hy
    have m2 : Ideal.map p₂ (maximalIdeal B) ≤ maximalIdeal A₂ := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      rw [Ideal.mem_comap, ← res_eq_zero_iff O, ← hφ2]
      exact (hmax y).mp hy
    have x1 : p₁ x ∈ maximalIdeal A₁ ^ N := by
      apply pow_le_pow_left' m1 N
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem p₁ hx
    have x2 : p₂ x ∈ maximalIdeal A₂ ^ N := by
      apply pow_le_pow_left' m2 N
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem p₂ hx
    rw [h₁, Ideal.mem_bot] at x1
    rw [h₂, Ideal.mem_bot] at x2
    exact hinj x 0 (by rw [x1, map_zero]) (by rw [x2, map_zero])
  refine ⟨{ complete := complete_of_pow _ N hpow, isLocalHom := ⟨fun a ha => ?_⟩, res_surj := fun x => ?_ }, hpow⟩
  · rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← ResidueField.algebraMap_eq, ← AlgHom.commutes φ]
    exact hnon _ ha
  · obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (φ x)
    refine ⟨a, (hmax _).mpr ?_⟩
    rw [map_sub, AlgHom.commutes, ResidueField.algebraMap_eq, ha, sub_self]

theorem UpperTheory.exists_lift_dominating_pair_of_maximalIdeal_pow_eq_bot :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] (Γ ι : Type) [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) (N : ℕ) (A₁ : Type) [CommRing A₁] [Algebra O A₁] [IsCO O A₁] (A₂ : Type) [CommRing A₂] [Algebra O A₂] [IsCO O A₂] (r₁ : Lift O rbar A₁) (r₂ : Lift O rbar A₂), maximalIdeal A₁ ^ N = ⊥ → maximalIdeal A₂ ^ N = ⊥ →
          ∃ (B : Type) (_ : CommRing B) (_ : Algebra O B) (_ : IsCO O B) (r : Lift O rbar B) (p₁ : B →ₐ[O] A₁) (p₂ : B →ₐ[O] A₂), maximalIdeal B ^ N = ⊥ ∧ Algebra.adjoin O {x : B | ∃ g a b, x = r.hom g a b} = ⊤ ∧ r.map p₁ = r₁ ∧ r.map p₂ = r₂ := by
  intro O _ _ _ Γ ι _ _ _ _ rbar N A₁ _ _ _ A₂ _ _ _ r₁ r₂ h₁ h₂
  classical
  let gen : Set (A₁ × A₂) := {x | ∃ g a b, x = (r₁.hom g a b, r₂.hom g a b)}
  let S : Subalgebra O (A₁ × A₂) := Algebra.adjoin O gen
  let p₁ : S →ₐ[O] A₁ := (AlgHom.fst O A₁ A₂).comp S.val
  let p₂ : S →ₐ[O] A₂ := (AlgHom.snd O A₁ A₂).comp S.val
  have hinj : ∀ x y : S, p₁ x = p₁ y → p₂ x = p₂ y → x = y := fun x y e1 e2 =>
    Subtype.ext (Prod.ext e1 e2)
  have hle : S ≤ AlgHom.equalizer ((res O A₁).comp (AlgHom.fst O A₁ A₂))
      ((res O A₂).comp (AlgHom.snd O A₁ A₂)) := by
    apply Algebra.adjoin_le
    rintro x ⟨g, a, b, rfl⟩
    rw [SetLike.mem_coe, AlgHom.mem_equalizer]
    show res O A₁ (r₁.hom g a b) = res O A₂ (r₂.hom g a b)
    exact (r₁.red g a b).trans (r₂.red g a b).symm
  have hres : ∀ x : S, res O A₁ (p₁ x) = res O A₂ (p₂ x) := fun x =>
    (AlgHom.mem_equalizer _ _ _).mp (hle x.2)
  obtain ⟨hCO, hpow⟩ := sub_co O N A₁ A₂ h₁ h₂ S p₁ p₂ hinj hres
  haveI := hCO
  let M : Γ → Matrix ι ι S := fun g => Matrix.of fun a b =>
    ⟨(r₁.hom g a b, r₂.hom g a b), Algebra.subset_adjoin ⟨g, a, b, rfl⟩⟩
  have hMv : ∀ g a b, ((M g a b : S) : A₁ × A₂) = (r₁.hom g a b, r₂.hom g a b) := fun _ _ _ => rfl
  let hom : Γ →* Matrix ι ι S :=
    { toFun := M
      map_one' := by
        refine Matrix.ext fun a b => Subtype.ext ?_
        rw [hMv, map_one r₁.hom, map_one r₂.hom]
        by_cases hab : a = b
        · subst hab
          simp
        · simp [Matrix.one_apply_ne hab]
      map_mul' := by
        intro g h
        refine Matrix.ext fun a b => Subtype.ext ?_
        rw [hMv, map_mul r₁.hom, map_mul r₂.hom, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply]
        show _ = S.val (∑ c, M g a c * M h c b)
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp only [map_mul]
        change _ = ∑ c, ((M g a c : A₁ × A₂) * (M h c b : A₁ × A₂))
        simp only [hMv]
        ext <;> simp [Prod.fst_sum, Prod.snd_sum] }
  have hloc : ∀ a b, IsLocallyConstant fun g => M g a b := by
    intro a b
    have l1 : IsLocallyConstant fun g => r₁.hom g a b :=
      IsLocallyConstant.desc _ _ (r₁.cont a b N) (mk_inj _ h₁)
    have l2 : IsLocallyConstant fun g => r₂.hom g a b :=
      IsLocallyConstant.desc _ _ (r₂.cont a b N) (mk_inj _ h₂)
    exact IsLocallyConstant.desc _ (Subtype.val : S → A₁ × A₂) (l1.prodMk l2) Subtype.val_injective
  let r : Lift O rbar S :=
    { hom := hom
      cont := fun a b n => (hloc a b).comp _
      red := fun g a b => by
        rw [← res_map p₁]
        exact r₁.red g a b }
  refine ⟨S, inferInstance, inferInstance, hCO, r, p₁, p₂, hpow, ?_, ?_, ?_⟩
  · apply Subalgebra.map_injective (f := S.val) Subtype.val_injective
    rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨g, a, b, rfl⟩, rfl⟩
      exact ⟨g, a, b, rfl⟩
    · rintro ⟨g, a, b, rfl⟩
      exact ⟨M g a b, ⟨g, a, b, rfl⟩, rfl⟩
  · exact Lift.ext (MonoidHom.ext fun g => Matrix.ext fun a b => rfl)
  · exact Lift.ext (MonoidHom.ext fun g => Matrix.ext fun a b => rfl)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.MapPart
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.map_part :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (W' : WPres O X R'), (∀ s, W'.z s ∈ maximalIdeal R') → ∀ f : R →ₐ[O] R', (∀ s, f (W.z s) ∈ W'.part (W.wt s)) → ∀ j, ∀ x ∈ W.part j, f x ∈ W'.part j := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W hW R' _ _ _ W' hW' f hf j x hx
  classical
  obtain ⟨g, hg, rfl⟩ := hx
  have hm : ∀ s, (f.comp W.π) (MvPowerSeries.X s) ∈ maximalIdeal R' := fun s => by
    show f (W.z s) ∈ maximalIdeal R'
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hW s
  refine part_closed O X R' W' hW' j _ fun N => ⟨_, ?_, GlobalTheory.algHom_sub_aeval_truncTotal_mem (f.comp W.π) hm N g⟩
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hw : Finsupp.weight W.wt d = j := by
    by_contra hne
    apply MvPolynomial.mem_support_iff.1 hd
    rw [coeff_truncTotal_eq_ite, hg d hne, ite_self]
  rw [← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  rw [← hw, Finsupp.weight_apply, Finsupp.sum]
  exact SetLike.prod_pow_mem_graded W'.part W.wt (fun s => f (W.z s)) d (fun s _ => hf s)
end

