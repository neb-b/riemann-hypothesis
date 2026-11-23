module

public import Mathlib
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPres
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0002
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsCocycleTorsionOfHasPres
section
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct UpperTheory.KN

theorem _root_.UpperTheory.KN.exists_cocycle_torsion_of_hasPres :
    ∀ {G O LL : Type} [Group G] [TopologicalSpace G] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field LL]
      [TopologicalSpace LL] [IsTopologicalRing LL] [Algebra O LL] [IsFractionRing O LL] (hinj : Function.Injective (algebraMap O LL))
      (lam : O) {Xs : Type} {n k : ℕ} (N : Xs → (G →* Matrix (Fin n) (Fin n) O)) (M : G →* Matrix (Fin k) (Fin k) O)
      (f : G → (Fin k → LL) ⧸ stdG O LL k), Irreducible lam → IsOpen (Set.range (algebraMap O LL)) →
      (∀ x, Continuous fun g => (N x g).map (algebraMap O LL)) →
      HasPres LL N (Q := (Fin k → LL) ⧸ stdG O LL k) (fun g => actD (stdLatG hinj M) g) f →
      ∃ a : ℕ, f ∈ divisibleCocycles (stdLatG hinj M) ∧ ∀ g, lam ^ a • f g = 0 := by
  intro G O LL _ _ _ _ _ _ _ _ _ _ hinj lam Xs n k N M f hlam hopen hN hP
  obtain ⟨m, x, E, Y, hYfg, hst, hE, φ, hφ, hf⟩ := hP
  haveI : Module.Finite O Y := Module.Finite.iff_fg.mpr hYfg
  obtain ⟨e, he⟩ := exists_pow_uniformizer_smul_eq_zero_quotient_lattice lam hlam φ
  have hmul : ∀ g h (v : Fin m → Fin n → LL), actN LL (fun j => N (x j)) (g * h) v =
      actN LL (fun j => N (x j)) g (actN LL (fun j => N (x j)) h v) := by
    intro g h v
    funext j
    simp only [actN, map_mul, Matrix.map_mul, Matrix.mulVec_mulVec]
  have hsub : ∀ g (v w : Fin m → Fin n → LL), actN LL (fun j => N (x j)) g (v - w) =
      actN LL (fun j => N (x j)) g v - actN LL (fun j => N (x j)) g w := by
    intro g v w
    funext j
    simp only [actN, Pi.sub_apply, Matrix.mulVec_sub]
  have hfun : f = fun g => φ ⟨actN LL (fun j => N (x j)) g E - E, hE g⟩ := funext hf
  refine ⟨e, ⟨?_, fun g h => ?_⟩, fun g => by rw [hf g]; exact he _⟩
  · rw [hfun]
    refine isLocallyConstant_torsion_push_of_continuous Y φ _ hE (lam ^ e) hopen ?_ (pow_ne_zero _ hlam.ne_zero) he
    exact (continuous_pi fun j => (hN (x j)).matrix_mulVec continuous_const).sub continuous_const
  · have hsplit : (⟨actN LL (fun j => N (x j)) (g * h) E - E, hE (g * h)⟩ : Y) =
        ⟨actN LL (fun j => N (x j)) g ↑(⟨actN LL (fun j => N (x j)) h E - E, hE h⟩ : Y),
          hst g _ (hE h)⟩ + ⟨actN LL (fun j => N (x j)) g E - E, hE g⟩ := by
      apply Subtype.ext
      simp only [Submodule.coe_add, hmul, hsub]
      abel
    rw [hf, hf, hf, hsplit, map_add (f := _), hφ]
    exact add_comm _ _
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsGaloisStableLatticeOfPeriodData
section
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct UpperTheory.KN

private theorem admissible_lattice_inclusion {G O LL V : Type} [Group G] [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [Field LL] [Algebra O LL] [IsFractionRing O LL]
    [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] (ρ : Representation LL G V)
    (Λ : Lattice (O := O) ρ)
    {A : Type} [AddCommGroup A] [Module O A] [Module.Finite O A] (j : A →ₗ[O] V) (actA : G → A → A)
    {E : Type} [AddCommGroup E] [Module O E] (act : G → E → E) (S : Submodule O E)
    (q : A →ₗ[O] (E ⧸ S)) (c : O)
    (hj : Function.Injective j) (hact : ∀ g a, j (actA g a) = ρ g (j a)) (hq : Function.Surjective q)
    (hqa : ∀ g a x, q a = Submodule.Quotient.mk x → q (actA g a) = Submodule.Quotient.mk (act g x))
    (hc : c ≠ 0) (hcy : ∀ y : E ⧸ S, c • y = 0) :
    ∃ (L₁ L₂ : Lattice (O := O) ρ),
      L₂.T ≤ L₁.T ∧ ∃ e : (E ⧸ S) ≃ₗ[O] (↥L₁.T ⧸ L₂.T.comap L₁.T.subtype),
        ∀ (g : G) (x : E) (y : ↥L₁.T), e (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
          e (Submodule.Quotient.mk (act g x)) = Submodule.Quotient.mk ⟨ρ g y, L₁.stable g y y.2⟩ := by
  have h0 : ∀ g, actA g 0 = 0 := fun g => hj (by rw [hact, map_zero, map_zero])
  have hker : ∀ g a, q a = 0 → q (actA g a) = 0 := by
    intro g a ha
    have h1 := hqa g a 0 (by rw [ha]; rfl)
    have h2 := hqa g 0 0 (by rw [map_zero]; rfl)
    rw [h1, ← h2, h0, map_zero]
  obtain ⟨μ, hμ, hcom⟩ := UpperTheory.KN.admissible_lattices_commensurable (LL := LL) Λ.T (LinearMap.range j) Λ.fg c hc
  have fg1 : (LinearMap.range j).FG := by
    rw [← Submodule.map_top]
    exact Submodule.FG.map j Module.Finite.fg_top
  have fg2 : ((LinearMap.ker q).map j).FG :=
    Submodule.FG.map j (IsNoetherian.noetherian _)
  obtain ⟨L₁, hL₁⟩ := UpperTheory.KN.exists_lattice_eq_add_smul_of_stable_fg_submodule ρ Λ (LinearMap.range j) fg1
    (by rintro g _ ⟨a, rfl⟩; exact ⟨actA g a, hact g a⟩) μ hμ
  obtain ⟨L₂, hL₂⟩ := UpperTheory.KN.exists_lattice_eq_add_smul_of_stable_fg_submodule ρ Λ ((LinearMap.ker q).map j) fg2
    (by rintro g _ ⟨a, ha, rfl⟩; exact ⟨actA g a, hker g a ha, hact g a⟩) μ hμ
  let B : Submodule O V := Λ.T.map (μ • (LinearMap.id : V →ₗ[O] V))
  have hB : ∀ b, b ∈ B ↔ ∃ u ∈ Λ.T, μ • u = b := fun b => Iff.rfl
  obtain ⟨e, he⟩ := UpperTheory.KN.exists_linearEquiv_quotient_of_lattice_sum j q B L₁.T L₂.T hj hq
    (by
      intro a ha
      obtain ⟨u, hu, hua⟩ := (hB _).1 ha
      obtain ⟨_, ⟨a', rfl⟩, h⟩ := hcom u hu ⟨a, hua.symm⟩
      have : a = c • a' := hj (by rw [map_smul, ← h, hua])
      rw [this, map_smul, hcy])
    (by
      intro v
      rw [hL₁]
      constructor
      · rintro ⟨_, ⟨a, rfl⟩, u, hu, rfl⟩
        exact ⟨a, _, (hB _).2 ⟨u, hu, rfl⟩, rfl⟩
      · rintro ⟨a, b, hb, rfl⟩
        obtain ⟨u, hu, rfl⟩ := (hB _).1 hb
        exact ⟨_, ⟨a, rfl⟩, u, hu, rfl⟩)
    (by
      intro v
      rw [hL₂]
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, u, hu, rfl⟩
        exact ⟨a, ha, _, (hB _).2 ⟨u, hu, rfl⟩, rfl⟩
      · rintro ⟨a, ha, b, hb, rfl⟩
        obtain ⟨u, hu, rfl⟩ := (hB _).1 hb
        exact ⟨_, ⟨a, ha, rfl⟩, u, hu, rfl⟩)
  refine ⟨L₁, L₂, ?_, e, ?_⟩
  · intro v hv
    obtain ⟨_, ⟨a, _, rfl⟩, u, hu, rfl⟩ := (hL₂ v).1 hv
    exact (hL₁ _).2 ⟨_, ⟨a, rfl⟩, u, hu, rfl⟩
  · intro g x y hxy
    obtain ⟨a, ha⟩ := hq (Submodule.Quotient.mk x)
    rw [← ha] at hxy
    obtain ⟨a', ha', b, hb, hy⟩ := (he a y).1 hxy
    obtain ⟨u, hu, rfl⟩ := (hB _).1 hb
    rw [← hqa g a' x (ha'.trans ha)]
    refine (he _ _).2 ⟨actA g a', rfl, μ • ρ g u, (hB _).2 ⟨_, Λ.stable g u hu, rfl⟩, ?_⟩
    show ρ g y = _
    rw [hy, map_add (f := _), hact, LinearMap.map_smul_of_tower]

theorem _root_.UpperTheory.KN.exists_galois_stable_lattice_of_period_data :
    ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
      [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
      {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
      [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
      [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
      {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
      {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [IsFractionRing O LL] {nn : ℕ}
      (emb : ZMod nn → (K₀ →ₐ[Qp] LL)) (lam : O) (jT : ZMod nn → ℤ → ℤ) (cT : G → Polynomial LL)
      {m : ℕ} (F : Fin m → tableLineDegreeTwo.FullRep PD emb lam jT cT) (Λ : Lattice (O := O) (tableLineDegreeTwo.piRep F))
      {A : Type} [AddCommGroup A] [Module O A] [Module.Finite O A] (j : A →ₗ[O] (∀ k, (F k).V)) (actA : G → A → A)
      {E : Type} [AddCommGroup E] [Module O E] (act : G → E → E) (S : Submodule O E) (q : A →ₗ[O] (E ⧸ S)) (c : O),
      Function.Injective j → (∀ g a, j (actA g a) = tableLineDegreeTwo.piRep F g (j a)) → Function.Surjective q →
      (∀ g a x, q a = Submodule.Quotient.mk x → q (actA g a) = Submodule.Quotient.mk (act g x)) →
      c ≠ 0 → (∀ y : E ⧸ S, c • y = 0) → tableLineDegreeTwo.AdmQ PD emb lam jT cT act S := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ _ _ O _ _ _ _ _ nn emb lam jT cT
    m F Λ A _ _ _ j actA E _ _ act S q c hj hact hq hqa hc hcy
  exact ⟨m, F, admissible_lattice_inclusion (tableLineDegreeTwo.piRep F) Λ j actA act S q c hj hact hq hqa hc hcy⟩
end

