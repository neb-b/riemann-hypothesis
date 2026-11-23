module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateDefs
public import ReciprocityTheory.GroupCohomology.ImportsAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0015
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.Bundle0003
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0039
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateFin

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiltByRestrictScalarsOfResidualCharacters
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private def Reach {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    (ρ : Representation A G V) (S : Set (G →* Aˣ)) (U : Submodule A V) : Prop :=
  ∃ (n : ℕ) (F : ℕ → Submodule A V), F 0 = ⊥ ∧ F n = U ∧ ∀ i < n, F i ≤ F (i + 1) ∧
    ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ Submodule.span A {x} ∧ ∀ g, ρ g x - ((κ g : Aˣ) : A) • x ∈ F i

private theorem reach_bot {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    (ρ : Representation A G V) (S : Set (G →* Aˣ)) : Reach ρ S ⊥ :=
  ⟨0, fun _ => ⊥, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩

private theorem reach_step {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    {ρ : Representation A G V} {S : Set (G →* Aˣ)} {U : Submodule A V} (h : Reach ρ S U)
    {κ : G →* Aˣ} (hκ : κ ∈ S) {x : V} (hx : ∀ g, ρ g x - ((κ g : Aˣ) : A) • x ∈ U) :
    Reach ρ S (U ⊔ Submodule.span A {x}) := by
  obtain ⟨n, F, h0, hn, hs⟩ := h
  refine ⟨n + 1, fun i => if i ≤ n then F i else U ⊔ Submodule.span A {x}, by simp [h0], by simp, fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · have h1 : i ≤ n := hi.le
    have h2 : i + 1 ≤ n := hi
    simp only [h1, h2, if_true]
    exact hs i hi
  · have h2 : ¬ (i + 1 ≤ i) := by omega
    simp only [h2, le_refl, if_true, if_false, hn]
    exact ⟨le_sup_left, κ, hκ, x, rfl, hx⟩

private theorem reach_fin {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    {ρ : Representation A G V} {S : Set (G →* Aˣ)} {U : Submodule A V} (h : Reach ρ S U)
    {T : Set V} (hT : T.Finite) :
    (∀ x ∈ T, ∃ κ ∈ S, ∀ g, ρ g x - ((κ g : Aˣ) : A) • x ∈ U) → Reach ρ S (U ⊔ Submodule.span A T) := by
  induction T, hT using Set.Finite.induction_on with
  | empty =>
    intro _
    simpa using h
  | @insert a s ha hs ih =>
    intro hall
    have hr := ih (fun y hy => hall y (Set.mem_insert_of_mem a hy))
    obtain ⟨κ, hκ, hk⟩ := hall a (Set.mem_insert a s)
    have hr2 := reach_step hr hκ (x := a) (fun g => Submodule.mem_sup_left (hk g))
    have e : U ⊔ Submodule.span A (insert a s) = U ⊔ Submodule.span A s ⊔ Submodule.span A {a} := by
      rw [Submodule.span_insert]
      ac_rfl
    rw [e]
    exact hr2

theorem UpperTheory.filtBy_restrictScalars_of_residual_characters :
    ∀ {G E B V : Type} [Group G] [Field E] [CommRing B] [Algebra E B] [Module.Finite E B] [AddCommGroup V] [Module B V] [Module E V] [IsScalarTower E B V] (π : B →ₐ[E] E), (∀ a, π a = 0 → IsNilpotent a) → ∀ (ρ : Representation B G V) (S : Set (G →* Eˣ)) {ι : Type} [Finite ι] (x : ι → V) (κ : ι → G →* Eˣ), Submodule.span B (Set.range x) = ⊤ → (∀ j, κ j ∈ S) → (∀ g j, ρ g (x j) - ((κ j g : Eˣ) : E) • x j ∈ (RingHom.ker (π : B →+* E)) • (⊤ : Submodule B V)) → FiltBy (resCoef E ρ) S := by
  intro G E B V _ _ _ _ _ _ _ _ _ π hπ ρ S ι _ x κ hx hκ hstep
  have hnil : IsNilpotent (RingHom.ker (π : B →+* E)) := by
    haveI : IsNoetherianRing B := isNoetherian_of_tower E inferInstance
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro a ha
    exact mem_nilradical.mpr (hπ a ha)
  obtain ⟨N, hN⟩ := hnil
  obtain ⟨M, hM⟩ : ∃ M : ℕ → Submodule E V, ∀ k,
      M k = ((RingHom.ker (π : B →+* E)) ^ k • (⊤ : Submodule B V)).restrictScalars E :=
    ⟨_, fun _ => rfl⟩
  have hMm : ∀ k v, v ∈ M k ↔ v ∈ (RingHom.ker (π : B →+* E)) ^ k • (⊤ : Submodule B V) := by
    intro k v
    rw [hM, Submodule.restrictScalars_mem]
  have down : ∀ p, Reach (resCoef E ρ) S (M (p + 1)) → Reach (resCoef E ρ) S (M p) := by
    intro p h
    have hfg : (((RingHom.ker (π : B →+* E)) ^ p).restrictScalars E).FG := IsNoetherian.noetherian _
    obtain ⟨s, hsf, hs⟩ := Submodule.fg_def.mp hfg
    have hsub : ∀ a ∈ s, a ∈ (RingHom.ker (π : B →+* E)) ^ p := fun a ha => by
      have : a ∈ ((RingHom.ker (π : B →+* E)) ^ p).restrictScalars E := hs ▸ Submodule.subset_span ha
      exact this
    have hTf : (Set.image2 (fun a j => a • x j) s (Set.univ : Set ι)).Finite :=
      hsf.image2 _ Set.finite_univ
    have hr := reach_fin (ρ := resCoef E ρ) (S := S) h hTf (by
      rintro y ⟨a, ha, j, -, rfl⟩
      refine ⟨κ j, hκ j, fun g => ?_⟩
      rw [hMm]
      show ρ g (a • x j) - ((κ j g : Eˣ) : E) • (a • x j) ∈
        ((RingHom.ker (π : B →+* E)) ^ (p + 1) • (⊤ : Submodule B V))
      rw [map_smul, smul_comm ((κ j g : Eˣ) : E) a, ← smul_sub, pow_succ, Submodule.mul_smul]
      exact Submodule.smul_mem_smul (hsub a ha) (hstep g j))
    have claim : ∀ n ∈ Submodule.span B (Set.range x), ∀ a ∈ (RingHom.ker (π : B →+* E)) ^ p,
        a • n ∈ Submodule.span E (Set.image2 (fun a j => a • x j) s (Set.univ : Set ι)) := by
      intro n hn
      induction hn using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        intro a ha
        have ha' : a ∈ Submodule.span E s := by
          rw [hs]
          exact ha
        clear ha
        induction ha' using Submodule.span_induction with
        | mem b hb => exact Submodule.subset_span ⟨b, hb, j, trivial, rfl⟩
        | zero => simp
        | add b c _ _ hb hc =>
          rw [add_smul]
          exact add_mem hb hc
        | smul c b _ hb =>
          rw [smul_assoc]
          exact Submodule.smul_mem _ c hb
      | zero => intro a _; simp
      | add y z _ _ hy hz =>
        intro a ha
        rw [smul_add]
        exact add_mem (hy a ha) (hz a ha)
      | smul b y _ hy =>
        intro a ha
        rw [smul_smul]
        exact hy (a * b) (Ideal.mul_mem_right b _ ha)
    have e : M p = M (p + 1) ⊔ Submodule.span E (Set.image2 (fun a j => a • x j) s (Set.univ : Set ι)) := by
      apply le_antisymm
      · intro v hv
        apply Submodule.mem_sup_right
        rw [hMm] at hv
        refine Submodule.smul_induction_on hv ?_ ?_
        · intro a ha n _
          exact claim n (by rw [hx]; trivial) a ha
        · intro y z hy hz
          exact add_mem hy hz
      · refine sup_le ?_ ?_
        · intro v hv
          rw [hMm] at hv ⊢
          exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ p)) hv
        · rw [Submodule.span_le]
          rintro y ⟨a, ha, j, -, rfl⟩
          show a • x j ∈ M p
          rw [hMm]
          exact Submodule.smul_mem_smul (hsub a ha) trivial
    rw [e]
    exact hr
  have base : M N = ⊥ := by
    rw [hM, hN, Submodule.zero_eq_bot, Submodule.bot_smul, Submodule.restrictScalars_bot]
  have all : ∀ k, Reach (resCoef E ρ) S (M (N - k)) := by
    intro k
    induction k with
    | zero =>
      rw [Nat.sub_zero, base]
      exact reach_bot _ _
    | succ k ih =>
      rcases Nat.lt_or_ge k N with hk | hk
      · have e : N - k = (N - (k + 1)) + 1 := by omega
        rw [e] at ih
        exact down _ ih
      · have e : N - (k + 1) = N - k := by omega
        rw [e]
        exact ih
  have top : M 0 = ⊤ := by
    rw [hM, pow_zero, Ideal.one_eq_top, Submodule.top_smul, Submodule.restrictScalars_top]
  have fin := all N
  rw [Nat.sub_self, top] at fin
  exact fin
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteLevelOfFiniteLevelMod
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem killed (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] [Finite M] :
    ∃ r : ℕ, 0 < r ∧ ∀ x : M, (l : ℤ_[l]) ^ r • x = 0 :=
  _root_.UpperTheory.Reformulated.B.Qe12.killed l M

private theorem H0dual_eq {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V] (χ : G →* Aˣ)
    (ρ : Representation A G V) : H0dual χ ρ = (coSub χ ρ).dualAnnihilator := by
  ext f
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro hf
    have : coSub χ ρ ≤ LinearMap.ker f := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, x, rfl⟩
      have := hf g x
      simp [this]
    exact fun w hw => this hw
  · intro hf g x
    have := hf _ (Submodule.subset_span ⟨g, x, rfl⟩)
    rw [map_sub, map_smul, sub_eq_zero] at this
    exact this

private theorem card_co {G Q A V : Type} [Group G] [CommRing Q] [CommRing A] [Algebra Q A] [AddCommGroup V]
    [Module A V] [Module Q V] [IsScalarTower Q A V] (hs : Function.Surjective (algebraMap Q A)) (χ : G →* Qˣ)
    (χ' : G →* Aˣ) (h : ∀ g, ((χ' g : Aˣ) : A) = algebraMap Q A (χ g : Qˣ))
    (ρ : Representation A G V) : Nat.card (V ⧸ coSub χ' ρ) = Nat.card (V ⧸ coSub χ (resCoef Q ρ)) := by
  have e : coSub χ (resCoef Q ρ) = (coSub χ' ρ).restrictScalars Q := by
    unfold coSub
    rw [Submodule.restrictScalars_span Q A hs]
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, h, algebraMap_smul]
    rfl
  rw [e]
  exact Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv Q (coSub χ' ρ)).toEquiv.symm

private def modRep (n : ℕ) {G Q V : Type} [Group G] [CommRing Q] [AddCommGroup V] [Module Q V] [Module (ZMod n) V]
    (ρ : Representation Q G V) : Representation (ZMod n) G V where
  toFun g := (ρ g).toAddMonoidHom.toZModLinearMap n
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

theorem UpperTheory.finite_level_of_finite_level_mod :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (χ : G →* ℤ_[l]ˣ) (d : ℕ), FinLevelMod l G χ d → FinLevel l G χ d := by
  intro l _ G _ _ χ d h M _ _ _ _ _ ρ hρ
  obtain ⟨r, hr, hk⟩ := killed l M
  have hk' : ∀ x : M, (l ^ r) • x = 0 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l], Nat.cast_pow]; exact hk x
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ r)) M) := ⟨AddCommGroup.zmodModule hk'⟩
  letI : Algebra ℤ_[l] (ZMod (l ^ r)) := (PadicInt.toZModPow r).toAlgebra
  have hs : Function.Surjective (algebraMap ℤ_[l] (ZMod (l ^ r))) := ZMod.ringHom_surjective _
  haveI : IsScalarTower ℤ_[l] (ZMod (l ^ r)) M := by
    refine IsScalarTower.of_algebraMap_smul fun a x => ?_
    obtain ⟨k, hk2⟩ := ZMod.natCast_zmod_surjective (PadicInt.toZModPow r a)
    have h0 : a - k ∈ RingHom.ker (PadicInt.toZModPow (p := l) r) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, hk2, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at h0
    obtain ⟨b, hb⟩ := h0
    change PadicInt.toZModPow r a • x = a • x
    rw [← hk2, Nat.cast_smul_eq_nsmul, eq_add_of_sub_eq hb.symm, add_smul, mul_smul, hk, smul_zero, zero_add,
      Nat.cast_smul_eq_nsmul]
  let ρ' : Representation (ZMod (l ^ r)) G M := modRep (l ^ r) ρ
  have e : resCoef ℤ_[l] ρ' = ρ := by ext; rfl
  obtain ⟨a1, a2, a3, a4, a5⟩ := h r hr M ρ' hρ
  obtain ⟨⟨e0⟩, ⟨e1⟩, ⟨e2⟩, en⟩ := UpperTheory.nonempty_cohomology_restrictScalars_linearEquiv ℤ_[l] ρ'
  rw [← e]
  refine ⟨Finite.of_equiv _ e1.toEquiv.symm, Finite.of_equiv _ e2.toEquiv.symm, fun n hn => ?_, ?_, ?_⟩
  · obtain ⟨e'⟩ := en n
    have := a3 n hn
    exact e'.toEquiv.subsingleton
  · rw [Nat.card_congr e0.toEquiv, Nat.card_congr e1.toEquiv, Nat.card_congr e2.toEquiv, a4]
  · rw [Nat.card_congr e2.toEquiv, a5, H0dual_eq,
      ← Nat.card_congr (Submodule.dualQuotEquivDualAnnihilator _).toEquiv]
    have : Finite (M ⧸ coSub ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ) ρ') :=
      Finite.of_surjective _ (Submodule.mkQ_surjective _)
    rw [KStar.Selmer.card_dual_of_baer KStar.Selmer.zmod_baer]
    exact card_co hs χ _ (fun g => rfl) ρ'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.HomExt
section
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

private theorem hx_finite {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O]
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
    [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B]
    (x : R →ₐ[O] B) : Module.Finite O x.range := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite ℚ_[l] B
  haveI : IsNoetherianRing x.range := isNoetherianRing_of_surjective R _ x.rangeRestrict.toRingHom
    x.rangeRestrict_surjective
  have hfin : ∀ m : MaximalSpectrum B, Module.Finite ℤ_[l] (integralClosure ℤ_[l] (B ⧸ m.asIdeal)) := fun m => by
    haveI := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    exact IsIntegralClosure.finite ℤ_[l] ℚ_[l] (B ⧸ m.asIdeal) _
  let v : x.range →ₐ[ℤ_[l]] B := x.range.val.restrictScalars ℤ_[l]
  have hint : ∀ (m : MaximalSpectrum B) (z : x.range),
      ((Ideal.Quotient.mkₐ ℤ_[l] m.asIdeal).comp v) z ∈ integralClosure ℤ_[l] (B ⧸ m.asIdeal) := by
    rintro m ⟨_, a, rfl⟩
    haveI := m.isMaximal
    exact ((ptCont (l := l) R (B ⧸ m.asIdeal) ((Ideal.Quotient.mkₐ O m.asIdeal).comp x)).2
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 m.isMaximal)).1 a
  let g : x.range →ₐ[ℤ_[l]] ∀ m : MaximalSpectrum B, integralClosure ℤ_[l] (B ⧸ m.asIdeal) :=
    Pi.algHom _ _ fun m => AlgHom.codRestrict _ _ (hint m)
  haveI : Module.Finite ℤ_[l] g.range :=
    Module.Finite.of_injective g.range.val.toLinearMap Subtype.val_injective
  haveI : Module.Finite ℤ_[l] x.range := by
    refine Module.finite_of_surjective_of_ker_le_nilradical g.rangeRestrict g.rangeRestrict_surjective ?_
      (IsNoetherian.noetherian _)
    intro z hz
    have hz' : g z = 0 := congrArg Subtype.val hz
    have hj : (z : B) ∈ Ideal.jacobson (⊥ : Ideal B) := by
      rw [Ideal.jacobson, Ideal.mem_sInf]
      rintro I ⟨-, hI⟩
      have := congrArg Subtype.val (congrFun hz' ⟨I, hI⟩)
      exact Ideal.Quotient.eq_zero_iff_mem.1 this
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B)
    refine ⟨n, Subtype.ext ?_⟩
    have := Ideal.pow_mem_pow hj n
    rw [hn] at this
    simpa using this
  exact Module.Finite.of_restrictScalars_finite ℤ_[l] O x.range

private theorem hx_pow {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    {A : Type} [CommRing A] [Algebra O A] [Module.Finite O A] (y : R →ₐ[O] A) :
    ∃ N : ℕ, ∀ a ∈ maximalIdeal R ^ N, y a ∈ (maximalIdeal O).map (algebraMap O A) := by
  have h1 : (maximalIdeal R).map y ≤ ((maximalIdeal O).map (algebraMap O A)).radical := by
    rw [Ideal.radical_eq_sInf, le_sInf_iff]
    rintro P ⟨hP, hPp⟩
    have hc : (P.comap (algebraMap O A)).IsMaximal := by
      rw [← (maximalIdeal.isMaximal _).eq_of_le (Ideal.IsPrime.ne_top inferInstance)
        (Ideal.map_le_iff_le_comap.1 hP)]
      infer_instance
    haveI : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under P hc
    have hi : (y : R →+* A).IsIntegral := by
      refine RingHom.IsIntegral.tower_top (algebraMap O R) _ ?_
      rw [AlgHom.comp_algebraMap]
      exact fun a => Algebra.IsIntegral.isIntegral (R := O) a
    have := eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' (y : R →+* A) hi P)
    rw [Ideal.map_le_iff_le_comap, ← this]
    exact le_rfl
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg h1 (Ideal.FG.map (IsNoetherian.noetherian _) _)
  refine ⟨N, fun a ha => hN ?_⟩
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem y ha

theorem UpperTheory.V.Loc.homExt :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : Lift O rbar R), ρ.Generates → ∀ (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (f f' : R →ₐ[O] B), (∀ g a b, f (ρ.hom g a b) = f' (ρ.hom g a b)) → f = f' := by
  intro l _ O _ _ _ _ _ _ _ Γ ι _ _ _ _ rbar R _ _ _ ρ hρ B _ _ _ _ _ _ _ f f' h
  choose c hc using IsCO.res_surj (O := O) (R := R)
  let S : Set R := Set.range fun s : Γ × ι × ι => ρ.hom s.1 s.2.1 s.2.2 - algebraMap O R (c (ρ.hom s.1 s.2.1 s.2.2))
  have hS : S ⊆ maximalIdeal R := by
    rintro _ ⟨s, rfl⟩
    exact hc _
  have hspan := co_span O R O (Algebra.ofId O R) S hS fun u u' _ hu => by
    haveI := (co_res O).2
    refine hρ _ u u' (Lift.ext (MonoidHom.ext fun g => Matrix.ext fun a b => ?_))
    have := hu _ ⟨(g, a, b), rfl⟩
    simp only [map_sub, AlgHom.commutes, sub_left_inj] at this
    exact this
  haveI := hx_finite (l := l) f
  haveI := hx_finite (l := l) f'
  let A : Subalgebra O B := f.range ⊔ f'.range
  haveI : Module.Finite O A := Subalgebra.finite_sup _ _
  let u : R →ₐ[O] A := f.codRestrict A fun a => (le_sup_left : f.range ≤ A) ⟨a, rfl⟩
  let u' : R →ₐ[O] A := f'.codRestrict A fun a => (le_sup_right : f'.range ≤ A) ⟨a, rfl⟩
  haveI : IsHausdorff (maximalIdeal O) A := inferInstance
  haveI : IsHausdorff ((maximalIdeal O).map (algebraMap O A)) A := IsHausdorff.map_algebraMap_iff.2 this
  obtain ⟨N, hN⟩ := hx_pow u
  obtain ⟨N', hN'⟩ := hx_pow u'
  have key : u = u' := by
    refine co_ext O R O A ((maximalIdeal O).map (algebraMap O A)) (Algebra.ofId O R) S hS hspan u u'
      ⟨N + N', fun x hx => ⟨hN x (Ideal.pow_le_pow_right (Nat.le_add_right _ _) hx),
        hN' x (Ideal.pow_le_pow_right (Nat.le_add_left _ _) hx)⟩⟩ (Subsingleton.elim _ _) ?_
    rintro _ ⟨s, rfl⟩
    rw [map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, sub_left_inj]
    exact Subtype.ext (h _ _ _)
  ext a
  exact congrArg Subtype.val (DFunLike.congr_fun key a)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MemFiniteCocyclesIffRestrictSubgroupMem
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

theorem UpperTheory.mem_finiteCocycles_iff_restrict_subgroup_mem :
    ∀ {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {η : GQ l →* ℤˣ} {Ψ : GQ l →* Eˣ} {H : Subgroup (GQ l)} {e : ℕ} (hD : TriDat η Ψ H e) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (T : Tor η B), T.Good π Ψ → ∀ β ∈ Z1 T.M1, (β ∈ UpperTheory.V.Loc.finiteCocycles (MonoidHom.id (GQ l)) T.M1 ↔ (fun g : H => (β g).1) ∈ UpperTheory.V.Loc.finiteCocycles H.subtype (chRep (T.ch H hD.ηH 0 / T.ch H hD.ηH 1)) ∧ (fun g : H => (β g).2) ∈ UpperTheory.V.Loc.finiteCocycles H.subtype (chRep (T.ch H hD.ηH 1 / T.ch H hD.ηH 2))) := by
  intro l _ E _ _ _ _ _ η Ψ H e hD B _ _ _ _ _ _ _ _ _ _ π hπ T hT β hβ
  haveI := hD.normal
  haveI := hD.fin
  have hM : ∀ (g : H) (v : B × B), (T.M1.comp H.subtype : Representation B H (B × B)) g v =
      (chRep (T.ch H hD.ηH 0 / T.ch H hD.ηH 1) g v.1, chRep (T.ch H hD.ηH 1 / T.ch H hD.ηH 2) g v.2) := by
    intro g v
    change T.M1 g v = _
    rw [Tor.adjointSuperdiagRep_apply, if_pos (hD.ηH g g.2)]
    rfl
  rw [z1fDesc (MonoidHom.id (GQ l)) T.M1 H β hβ, MonoidHom.id_comp]
  constructor
  · intro h
    exact ⟨(z1fMap H.subtype _ _).2 (LinearMap.fst ℚ_[l] B B) (fun g x => by rw [hM]; rfl) _ h,
      (z1fMap H.subtype _ _).2 (LinearMap.snd ℚ_[l] B B) (fun g x => by rw [hM]; rfl) _ h⟩
  · rintro ⟨h1, h2⟩
    have k1 := (z1fMap H.subtype _ (T.M1.comp H.subtype : Representation B H (B × B))).2
      (LinearMap.inl ℚ_[l] B B) (fun g x => by rw [hM]; simp) _ h1
    have k2 := (z1fMap H.subtype _ (T.M1.comp H.subtype : Representation B H (B × B))).2
      (LinearMap.inr ℚ_[l] B B) (fun g x => by rw [hM]; simp) _ h2
    have k := add_mem k1 k2
    convert k using 1
    ext g <;> simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PhiCond
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.V.Loc.phiCond :
    LocalPublishedTheorems → ∀ (v l : ℕ) [Fact v.Prime] [Fact l.Prime] (H : Subgroup (GQ v)), IsOpen (H : Set (GQ v)) → Finite {f : H →* Multiplicative (ZMod l) // IsOpen (f.ker : Set H)} := by
  intro hP v l _ _ H hH
  letI : Algebra ℤ_[l] (ZMod l) := (PadicInt.toZMod (p := l)).toAlgebra
  letI : TopologicalSpace (ZMod l) := ⊥
  haveI : DiscreteTopology (ZMod l) := ⟨rfl⟩
  let ρ : Representation (ZMod l) H (ZMod l) := 1
  have hρ : ContAction ρ := continuous_snd
  have hfin := (tateFin hP (v := v) (l := l) H.subtype hH.isOpenEmbedding_subtypeVal (ZMod l) (ZMod l) ρ hρ).1
  haveI : Finite (H1 ρ) := Module.finite_of_finite (ZMod l)
  have hc : ∀ f : {f : H →* Multiplicative (ZMod l) // IsOpen (f.ker : Set H)},
      (fun g => Multiplicative.toAdd (f.1 g)) ∈ Z1 ρ := by
    intro f
    refine ⟨?_, fun g h => ?_⟩
    · refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun g => ?_)
      refine ⟨(fun x => g⁻¹ * x) ⁻¹' (f.1.ker : Set H), f.2.preimage (by fun_prop), by simp, fun x hx => ?_⟩
      have : f.1 (g⁻¹ * x) = 1 := hx
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      rw [this]
    · simp [ρ]
  refine Finite.of_injective (fun f => (Submodule.Quotient.mk ⟨_, hc f⟩ : H1 ρ)) fun f f' hff => ?_
  have h1 := (Submodule.Quotient.eq ((ReciprocityTheory.Gal.B1 ρ).comap (Z1 ρ).subtype)).1 hff
  obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ _).1 (Submodule.mem_comap.1 h1)
  refine Subtype.ext (MonoidHom.ext fun g => Multiplicative.toAdd.injective ?_)
  have := hm g
  simpa [ρ, sub_eq_zero] using this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RankCohomologyRationalEqRankLattice
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.rank_cohomology_rational_eq_rank_lattice :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] G V), ContAction ρ → ∀ {n : ℕ} (ρT : Representation ℤ_[l] G (Fin n → ℤ_[l])) (j : (Fin n → ℤ_[l]) →ₗ[ℤ_[l]] V), ContAction ρT → IsOpenEmbedding j → (∀ g x, j (ρT g x) = ρ g (j x)) → (∀ y : V, ∃ m : ℕ, (l : ℤ_[l]) ^ m • y ∈ LinearMap.range j) → Module.rank ℚ_[l] ↥(H0 ρ) = Module.rank ℤ_[l] ↥(H0 ρT) ∧ Module.rank ℚ_[l] (H1 ρ) = Module.rank ℤ_[l] (H1 ρT) ∧ Module.rank ℚ_[l] (H2 ρ) = Module.rank ℤ_[l] (H2 ρT) := by
  intro l _ G _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ hρ n ρT j hT hj he hm
  haveI : ContinuousConstSMul ℤ_[l] V := ⟨fun c => by
    have h : (fun x : V => c • x) = fun x => (algebraMap ℤ_[l] ℚ_[l] c) • x :=
      funext fun x => (algebraMap_smul ℚ_[l] c x).symm
    rw [h]
    exact continuous_const_smul _⟩
  let L : ReciprocityTheory.Coh.TRep ℤ_[l] G := { V := Fin n → ℤ_[l], rho := ρT, cont := hT }
  let U : ReciprocityTheory.Coh.TRep ℤ_[l] G := { V := V, rho := resCoef ℤ_[l] ρ, cont := hρ }
  let P : ReciprocityTheory.Coh.Pair L U := ⟨MonoidHom.id G, j, continuous_id, hj.continuous, he⟩
  have hl : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl' : (l : ℤ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hloc := ReciprocityTheory.Coh.localise_holds ℤ_[l] G (l : ℤ_[l]) L U P rfl hj
    ⟨Homeomorph.smulOfNeZero (α := V) (l : ℚ_[l]) hl, fun (v : V) => by
      show (l : ℚ_[l]) • v = (l : ℤ_[l]) • v
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]⟩ hm
  have hp : Submonoid.powers (l : ℤ_[l]) ≤ nonZeroDivisors ℤ_[l] :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hl'
  have hr : ∀ k, Module.rank ℤ_[l] (U.H k) = Module.rank ℤ_[l] (L.H k) := fun k =>
    haveI := hloc k
    IsLocalizedModule.rank_eq (Submonoid.powers (l : ℤ_[l])) hp (P.hom.H k)
  obtain ⟨a₀, a₁, a₂, -⟩ := ReciprocityTheory.Coh.exists_isLow L
  obtain ⟨b₀, b₁, b₂, -⟩ := ReciprocityTheory.Coh.exists_isLow U
  obtain ⟨⟨c₀⟩, ⟨c₁⟩, ⟨c₂⟩, -⟩ := UpperTheory.nonempty_cohomology_restrictScalars_linearEquiv ℤ_[l] ρ
  refine ⟨?_, ?_, ?_⟩
  · rw [IsFractionRing.rank_right_eq (R := ℤ_[l]) ℚ_[l]]
    exact (b₀.trans c₀).rank_eq.symm.trans ((hr 0).trans a₀.rank_eq)
  · rw [IsFractionRing.rank_right_eq (R := ℤ_[l]) ℚ_[l]]
    exact (b₁.trans c₁).rank_eq.symm.trans ((hr 1).trans a₁.rank_eq)
  · rw [IsFractionRing.rank_right_eq (R := ℤ_[l]) ℚ_[l]]
    exact (b₂.trans c₂).rank_eq.symm.trans ((hr 2).trans a₂.rank_eq)
end

