module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.EvIff
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem ev_iff {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {n a : ℕ} {Z : Matrix (Fin n) (Fin n) R} :
    Z ∈ Ev A R n a ↔ ∀ i j : Fin n, ¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j = 0 := by
  show (∀ i j : Fin n, ((((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j ∈ (⊤ : Submodule A R)) ∧
      (¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j ∈ (⊥ : Submodule A R))) ↔ _
  simp only [Submodule.mem_top, Submodule.mem_bot, implies_true, true_and]

private theorem od_iff {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {n a : ℕ} {Z : Matrix (Fin n) (Fin n) R} :
    Z ∈ Od A R n a ↔ ∀ i j : Fin n, (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j = 0 := by
  show (∀ i j : Fin n, ((((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j ∈ (⊥ : Submodule A R)) ∧
      (¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j ∈ (⊤ : Submodule A R))) ↔ _
  simp only [Submodule.mem_top, Submodule.mem_bot, implies_true, and_true]

private theorem sandwich {R : Type} [CommRing R] {n a : ℕ} {P Q Z : Matrix (Fin n) (Fin n) R}
    (hP : ∀ i j : Fin n, ¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → P i j = 0)
    (hQ : ∀ i j : Fin n, ¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Q i j = 0) (i j : Fin n)
    (hZ : ∀ i' j' : Fin n, (((i : ℕ) < a) ↔ ((i' : ℕ) < a)) → (((j' : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i' j' = 0) :
    (P * Z * Q) i j = 0 := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun m _ => ?_
  by_cases h1 : (((i : ℕ) < a) ↔ ((m : ℕ) < a))
  · by_cases h2 : (((k : ℕ) < a) ↔ ((j : ℕ) < a))
    · rw [hZ m k h1 h2]
      ring
    · rw [hQ k j h2]
      ring
  · rw [hP i m h1]
    ring

theorem UpperTheory.V.Pa.okX :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] (χ : G.Γ →* x.A), AdOk G.frame (fun g => x.ρX X (h.p₀ g)) (fun g => algebraMap x.A X (χ g)) (Ev x.A X n x.a) ∧ AdOk G.frame (fun g => x.ρX X (h.p₀ g)) (fun g => algebraMap x.A X (χ g)) (Od x.A X n x.a) := by
  intro l _ L G G0 h n x X _ _ χ
  classical
  have hblk : ∀ g : G0.frame.G₀, ∀ i j : Fin n, ¬ (((i : ℕ) < x.a) ↔ ((j : ℕ) < x.a)) →
      x.ρX X g i j = 0 := by
    intro g i j hij
    have hz := ev_iff.mp (x.blk g) i j hij
    simp [NP.ρX, Matrix.map_apply, hz]
  have hconj : ∀ g : G.frame.G₀, h.p₀ (G.frame.conj g) = G0.frame.conj (h.p₀ g) := by
    intro g
    apply Subtype.ext
    simp [GFrame.conj, Glob.Hom.p₀, map_mul, map_inv, h.c]
  have key : ∀ (M : Matrix (Fin n) (Fin n) x.A) (E : (x.A)ˣ),
      M = (E : x.A) • (1 : Matrix (Fin n) (Fin n) x.A) →
        ∃ u : Xˣ, M.map (algebraMap x.A X) = (u : X) • (1 : Matrix (Fin n) (Fin n) X) := by
    rintro M E rfl
    refine ⟨Units.map (algebraMap x.A X).toMonoidHom E, ?_⟩
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hform : ∀ g : G.frame.G₀, ∃ u : Xˣ,
      (x.ρX X (h.p₀ g))ᵀ * x.ρX X (h.p₀ (G.frame.conj g)) =
        (u : X) • (1 : Matrix (Fin n) (Fin n) X) := by
    intro g
    have hf := x.form (h.p₀ g)
    simp only [Units.val_one, Matrix.mul_one] at hf
    obtain ⟨u, hu⟩ := key _ _ hf
    refine ⟨u, ?_⟩
    rw [← hu, hconj]
    simp only [NP.ρX, Matrix.transpose_map, Matrix.map_mul]
  refine ⟨⟨?_, ?_, hform, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, hform, ?_, ?_, ?_, ?_⟩⟩
  all_goals try (simp [NP.ρX, Matrix.map_mul]; done)
  · intro g Z hZ
    rw [ev_iff] at hZ ⊢
    intro i j hij
    rw [Matrix.smul_apply, sandwich (hblk _) (hblk _) i j
      (fun i' j' h1 h2 => hZ i' j' (fun h3 => hij (h1.trans (h3.trans h2)))), smul_zero]
  · intro Z hZ
    rw [ev_iff] at hZ ⊢
    intro i j hij
    rw [Matrix.smul_apply, Matrix.transpose_apply, hZ j i (fun h3 => hij h3.symm), smul_zero]
  · intro g Z hZ
    rw [od_iff] at hZ ⊢
    intro i j hij
    rw [Matrix.smul_apply, sandwich (hblk _) (hblk _) i j
      (fun i' j' h1 h2 => hZ i' j' (h1.symm.trans (hij.trans h2.symm))), smul_zero]
  · intro Z hZ
    rw [od_iff] at hZ ⊢
    intro i j hij
    rw [Matrix.smul_apply, Matrix.transpose_apply, hZ j i hij.symm, smul_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.FiltCount
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.filtCount :
    ∀ (Z Y : Type) [AddCommGroup Z] [AddCommGroup Y] (r : ℕ) (f : Fin r → Z →+ Y) (P : Fin r → Set Y), (∀ z, (∀ i, f i z = 0) → z = 0) → (∀ i, (P i).Finite) → (∀ i z, (∀ j, j < i → f j z = 0) → f i z ∈ P i) → Finite Z ∧ Nat.card Z ≤ ∏ i, (P i).ncard := by
  intro Z Y _ _ r
  induction r generalizing Z with
  | zero =>
    intro f P hinj _ _
    have hsub : Subsingleton Z := ⟨fun a b => by
      rw [hinj a (fun i => i.elim0), hinj b (fun i => i.elim0)]⟩
    refine ⟨inferInstance, ?_⟩
    rw [Finset.univ_eq_empty, Finset.prod_empty]
    exact Finite.card_le_one_iff_subsingleton.2 hsub
  | succ r ih =>
    intro f P hinj hP hfilt
    obtain ⟨hKfin, hKcard⟩ := ih (f 0).ker (fun i => (f i.succ).comp (f 0).ker.subtype)
      (fun i => P i.succ)
      (by
        intro z hz
        have h0 : f 0 z.1 = 0 := AddMonoidHom.mem_ker.1 z.2
        apply Subtype.ext
        apply hinj
        intro i
        cases i using Fin.cases with
        | zero => exact h0
        | succ j => exact hz j)
      (fun i => hP i.succ)
      (by
        intro i z hz
        apply hfilt i.succ z.1
        intro j hj
        cases j using Fin.cases with
        | zero => exact AddMonoidHom.mem_ker.1 z.2
        | succ j' => exact hz j' (Fin.succ_lt_succ_iff.1 hj))
    have hrange : ((f 0).range : Set Y) ⊆ P 0 := by
      rintro _ ⟨z, rfl⟩
      exact hfilt 0 z (fun j hj => absurd hj (Fin.not_lt_zero j))
    haveI : Finite (f 0).range := ((hP 0).subset hrange).to_subtype
    have e := QuotientAddGroup.quotientKerEquivRange (f 0)
    haveI : Finite (Z ⧸ (f 0).ker) := Finite.of_equiv _ e.toEquiv.symm
    haveI : Finite Z := Finite.of_addSubgroup_quotient (f 0).ker
    refine ⟨inferInstance, ?_⟩
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (f 0).ker, Nat.card_congr e.toEquiv,
      Fin.prod_univ_succ]
    refine Nat.mul_le_mul ?_ hKcard
    calc Nat.card (f 0).range = ((f 0).range : Set Y).ncard := Nat.card_coe_set_eq _
      _ ≤ (P 0).ncard := Set.ncard_le_ncard hrange (hP 0)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.FinAm
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.finAm :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (m g : ℕ), Finite (x.Am m) ∧ Nat.card (x.Am m) = Nat.card x.K ^ m ∧ Finite (DD (x.Am m) g) ∧ (∀ y : x.Am m, l • y = 0) ∧ (∀ y : DD (x.Am m) g, l • y = 0) ∧ (algebraMap x.A (x.Am m) x.t) ^ m = 0 ∧ (algebraMap x.A (DD (x.Am m) g) x.t) ^ m = 0 ∧ (l ≠ 2 → IsUnit (2 : x.A)) ∧ CharP x.K l := by
  intro l _ F n x m g
  obtain ⟨h1, h2, -, -, h5, -⟩ := UpperTheory.V.Pa.am_fin l F n x m g
  have hA : (l : x.A) = 0 := h5
  have e : (l : x.K) = 0 := by
    have := congrArg (PowerSeries.constantCoeff (R := x.K)) hA
    rwa [map_natCast, map_zero] at this
  have hc : CharP x.K l := (CharP.charP_iff_prime_eq_zero (Fact.out)).2 e
  have hAm : (l : x.Am m) = 0 := by
    rw [← map_natCast (algebraMap x.A (x.Am m)), hA, map_zero]
  have hDD : (l : DD (x.Am m) g) = 0 := by
    rw [← map_natCast (DD.C (X := x.Am m) (g := g)), hAm, map_zero]
  haveI := h1
  have ht : (algebraMap x.A (x.Am m) x.t) ^ m = 0 := by
    rw [← map_pow, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  refine ⟨h1, h2, Finite.of_equiv _ DD.equiv.symm, fun y => by rw [nsmul_eq_mul, hAm, zero_mul],
    fun y => by rw [nsmul_eq_mul, hDD, zero_mul], ht, ?_, ?_, hc⟩
  · show (DD.C (algebraMap x.A (x.Am m) x.t)) ^ m = 0
    rw [← map_pow, ht, map_zero]
  · intro hl
    show IsUnit (2 : PowerSeries x.K)
    rw [PowerSeries.isUnit_iff_constantCoeff, map_ofNat]
    apply Ne.isUnit
    intro h2
    have h2' : ((2 : ℕ) : x.K) = 0 := by exact_mod_cast h2
    rw [CharP.cast_eq_zero_iff x.K l] at h2'
    exact hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h2')
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.LocCongr
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.locCongr :
    ∀ (l : ℕ) [Fact l.Prime] (D D' : Type) [Group D] [TopologicalSpace D] [Group D'] [TopologicalSpace D'] (α : D ≃ₜ* D') (ε : D →* ℤ_[l]ˣ) (ε' : D' →* ℤ_[l]ˣ) (d : ℕ), (∀ g, ε g = ε' (α g)) → LocCount D' ε' d → LocCount D ε d := by
  intro l _ D D' _ _ _ _ α ε ε' d hε h R M M' _ _ _ _ _ _ _ ρ ρ' b hLC hdual
  let σ : D' →* D := α.symm.toMulEquiv.toMonoidHom
  have hσ : ∀ g, σ g = α.symm g := fun g => rfl
  let ρ2 : Representation R D' M := ρ.comp σ
  let ρ2' : Representation R D' M' := ρ'.comp σ
  have heps : ∀ g : D', epsBar ε (α.symm g) = epsBar ε' g := by
    intro g
    simp only [epsBar, hε, ContinuousMulEquiv.apply_symm_apply]
  have hLC2 : LC ρ2 := fun m => (hLC m).comp_continuous α.symm.continuous
  have hdual2 : IsDualPair ε' ρ2 ρ2' b := by
    refine ⟨hdual.left, hdual.right, fun g x y => ?_⟩
    have := hdual.equiv (α.symm g) x y
    rw [← heps g, ← this]
    rfl
  obtain ⟨hfin, hcard⟩ := h R M M' ρ2 ρ2' b hLC2 hdual2
  let e : Zl ρ ≃ Zl ρ2 :=
    { toFun := fun z => ⟨fun g => z.1 (α.symm g), by
        obtain ⟨hz1, hz2⟩ := z.2
        refine ⟨hz1.comp_continuous α.symm.continuous, fun g k => ?_⟩
        show z.1 (α.symm (g * k)) = z.1 (α.symm g) + ρ (α.symm g) (z.1 (α.symm k))
        rw [map_mul]
        exact hz2 _ _⟩
      invFun := fun z => ⟨fun g => z.1 (α g), by
        obtain ⟨hz1, hz2⟩ := z.2
        refine ⟨hz1.comp_continuous α.continuous, fun g k => ?_⟩
        have := hz2 (α g) (α k)
        rw [← map_mul] at this
        show z.1 (α (g * k)) = z.1 (α g) + ρ g (z.1 (α k))
        rw [this]
        show z.1 (α g) + ρ (α.symm (α g)) (z.1 (α k)) = _
        rw [ContinuousMulEquiv.symm_apply_apply]⟩
      left_inv := fun z => by
        apply Subtype.ext
        funext g
        show z.1 (α.symm (α g)) = z.1 g
        rw [ContinuousMulEquiv.symm_apply_apply]
      right_inv := fun z => by
        apply Subtype.ext
        funext g
        show z.1 (α (α.symm g)) = z.1 g
        rw [ContinuousMulEquiv.apply_symm_apply] }
  have hinv : Nat.card ρ2'.invariants = Nat.card ρ'.invariants := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight (fun v => ?_)
    simp only [Representation.mem_invariants]
    constructor
    · intro hv g
      have := hv (α g)
      simpa [ρ2', hσ] using this
    · intro hv g
      exact hv (α.symm g)
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, hcard, hinv]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.PhiSub
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem phi_sub (l : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (hΦ : PhiCond (Γ := Γ) l) (H : Subgroup Γ) (hH : IsOpen (H : Set Γ)) : PhiCond (Γ := H) l := by
  intro K hK
  have hK' : IsOpen ((K.map H.subtype : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.coe_map]
    exact hH.isOpenMap_subtype_val _ hK
  haveI := hΦ _ hK'
  let e : K ≃* K.map H.subtype := K.equivMapOfInjective H.subtype H.subtype_injective
  have hc : Continuous (e.symm : K.map H.subtype → K) := by
    have hind : Topology.IsInducing (fun k : K => ((k : H) : Γ)) :=
      Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
    rw [hind.continuous_iff]
    have hfun : (fun k : K => ((k : H) : Γ)) ∘ e.symm = fun γ : K.map H.subtype => (γ : Γ) := by
      funext γ
      have h1 := K.coe_equivMapOfInjective_apply H.subtype H.subtype_injective (e.symm γ)
      simp only [Function.comp_apply]
      rw [← H.coe_subtype, ← h1]
      simp [e]
    rw [hfun]
    exact continuous_subtype_val
  refine Finite.of_injective
    (β := {ψ : (K.map H.subtype) →* Multiplicative (ZMod l) // IsOpen (ψ.ker : Set (K.map H.subtype))})
    (fun φ => ⟨φ.1.comp e.symm.toMonoidHom, ?_⟩) ?_
  · have hk : ((φ.1.comp e.symm.toMonoidHom).ker : Set (K.map H.subtype)) = e.symm ⁻¹' (φ.1.ker : Set K) := by
      ext γ
      exact Iff.rfl
    rw [hk]
    exact φ.2.preimage hc
  · intro φ φ' h
    apply Subtype.ext
    ext k
    have h2 := congrArg (fun ψ => ψ.1 (e k)) h
    simpa using h2

private theorem finite_addMonoidHom_zmod_of_finite (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Finite M] :
    Finite (M →+ ZMod l) := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  exact Finite.of_injective (fun f : M →+ ZMod l => (f : M → ZMod l)) DFunLike.coe_injective

private theorem eq_zero_of_forall_hom_zmod_eq_zero_of_l_smul (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] (hl : ∀ m : M, l • m = 0)
    (m : M) (h : ∀ f : M →+ ZMod l, f m = 0) : m = 0 := by
  letI : Module (ZMod l) M := AddCommGroup.zmodModule hl
  let b := Module.Basis.ofVectorSpace (ZMod l) M
  apply b.repr.injective
  ext i
  have := h (b.coord i).toAddMonoidHom
  rw [LinearEquiv.map_zero, Finsupp.coe_zero, Pi.zero_apply]
  simpa using this

theorem UpperTheory.V.Pa.finZ :
    ∀ (l : ℕ) [Fact l.Prime] (R Γ M : Type) [CommRing R] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R Γ M), PhiCond (Γ := Γ) l → LC ρ → (∀ m : M, l • m = 0) → Finite (Zl ρ) ∧ ∀ H : Subgroup Γ, IsOpen (H : Set Γ) → PhiCond (Γ := H) l := by
  intro l _ R Γ M _ _ _ _ _ _ _ _ ρ hΦ hρ hl
  refine ⟨?_, fun H hH => phi_sub l hΦ H hH⟩
  let N : Subgroup Γ :=
    { carrier := {g | ∀ m, ρ g m = m}
      mul_mem' := by
        intro a b ha hb m
        simp only [Set.mem_setOf_eq] at ha hb
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by
        intro m
        simp
      inv_mem' := by
        intro a ha m
        simp only [Set.mem_setOf_eq] at ha
        have h1 := ha (ρ a⁻¹ m)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h1
        exact h1.symm }
  have hN : IsOpen (N : Set Γ) := by
    have hset : (N : Set Γ) = ⋂ m : M, (fun g => ρ g m) ⁻¹' {m} := by
      ext g
      simp [N]
    rw [hset]
    exact isOpen_iInter_of_finite (fun m => (hρ m).isOpen_fiber m)
  haveI : Finite (Γ ⧸ N) := Subgroup.quotient_finite_of_isOpen N hN
  haveI : Finite (M →+ ZMod l) := finite_addMonoidHom_zmod_of_finite l M
  haveI := hΦ N hN
  have z1 : ∀ z ∈ Zl ρ, z 1 = 0 := by
    intro z hz
    have h := ((mem_Zl ρ).1 hz).2 1 1
    simpa using h
  have zN : ∀ z ∈ Zl ρ, ∀ a b : Γ, a ∈ N → z (a * b) = z a + z b := by
    intro z hz a b ha
    rw [((mem_Zl ρ).1 hz).2, ha]
  refine Finite.of_injective
    (β := (Γ ⧸ N → M) × ((M →+ ZMod l) →
      {φ : N →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set N)}))
    (fun z => (fun q => z.1 q.out, fun f =>
      ⟨⟨⟨fun k => Multiplicative.ofAdd (f (z.1 k)), ?_⟩, ?_⟩, ?_⟩)) ?_
  · show Multiplicative.ofAdd (f (z.1 ((1 : N) : Γ))) = 1
    rw [Subgroup.coe_one, z1 _ z.2, map_zero, ofAdd_zero]
  · intro k k'
    show Multiplicative.ofAdd (f (z.1 ((k * k' : N) : Γ))) =
      Multiplicative.ofAdd (f (z.1 k)) * Multiplicative.ofAdd (f (z.1 k'))
    rw [Subgroup.coe_mul, zN _ z.2 _ _ k.2, map_add (f := _), ofAdd_add]
  · have hlc : IsLocallyConstant (fun k : N => Multiplicative.ofAdd (f (z.1 k))) :=
      (((mem_Zl ρ).1 z.2).1.comp_continuous continuous_subtype_val).comp _
    rw [MonoidHom.coe_ker]
    exact hlc.isOpen_fiber 1
  · intro z z' h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    apply Subtype.ext
    funext g
    have key : ∀ k : N, z.1 k = z'.1 k := by
      intro k
      have hf : ∀ f : M →+ ZMod l, f (z.1 k - z'.1 k) = 0 := by
        intro f
        have h3 := congrArg (fun ψ : {φ : N →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set N)} =>
          Multiplicative.toAdd (ψ.1 k)) (congrFun h2 f)
        simp only [MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd] at h3
        rw [map_sub, h3, sub_self]
      exact sub_eq_zero.1 (eq_zero_of_forall_hom_zmod_eq_zero_of_l_smul l M hl _ hf)
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul N g
    have hg : g = (QuotientGroup.mk g : Γ ⧸ N).out * ((k⁻¹ : N) : Γ) := by
      rw [hk]
      simp [mul_assoc]
    have h1' : z.1 (QuotientGroup.mk g : Γ ⧸ N).out = z'.1 (QuotientGroup.mk g : Γ ⧸ N).out :=
      congrFun h1 (QuotientGroup.mk g)
    rw [hg, ((mem_Zl ρ).1 z.2).2, ((mem_Zl ρ).1 z'.2).2, key, h1']
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.PolZCases
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem polZ_mem {l : ℕ} [Fact l.Prime] (F : GFrame l) {γ : F.Γ} (h : γ ∉ F.η.ker) : γ * F.c ∈ F.η.ker := by
  rw [MonoidHom.mem_ker] at h ⊢
  rw [map_mul, F.η_c]
  rcases Int.units_eq_one_or (F.η γ) with h1 | h1
  · exact absurd h1 h
  · rw [h1]
    decide

private theorem polZ_nmem {l : ℕ} [Fact l.Prime] (F : GFrame l) (g : F.G₀) : (g : F.Γ) * F.c ∉ F.η.ker := by
  rw [MonoidHom.mem_ker, map_mul, MonoidHom.mem_ker.mp g.2, F.η_c, one_mul]
  decide

private theorem polZ_proj {l : ℕ} [Fact l.Prime] (F : GFrame l) :
    ∃ p : F.Γ → F.G₀, Continuous p ∧ (∀ g : F.G₀, p g = g) ∧ ∀ g : F.G₀, p (g * F.c) = g := by
  have hK : IsClopen (F.η.ker : Set F.Γ) :=
    ⟨Subgroup.isClosed_of_isOpen _ F.η_open, F.η_open⟩
  have hfr : frontier {a : F.Γ | a ∈ F.η.ker} = ∅ := hK.frontier_eq
  have hf : Continuous fun γ : F.Γ => if γ ∈ F.η.ker then (1 : F.Γ) else F.c := by
    refine continuous_if ?_ continuousOn_const continuousOn_const
    intro a ha
    rw [hfr] at ha
    exact ha.elim
  refine ⟨fun γ => ⟨γ * (if γ ∈ F.η.ker then 1 else F.c), by
    split_ifs with hγ
    · simpa using hγ
    · exact polZ_mem F hγ⟩, ?_, ?_, ?_⟩
  · exact Continuous.subtype_mk (continuous_id.mul hf) _
  · intro g
    apply Subtype.ext
    show (g : F.Γ) * (if (g : F.Γ) ∈ F.η.ker then 1 else F.c) = g
    rw [if_pos g.2, mul_one]
  · intro g
    apply Subtype.ext
    show (g : F.Γ) * F.c * (if (g : F.Γ) * F.c ∈ F.η.ker then 1 else F.c) = g
    rw [if_neg (polZ_nmem F g), mul_assoc, F.c_sq, mul_one]

private theorem polZ_cases {l : ℕ} [Fact l.Prime] (F : GFrame l) (γ : F.Γ) :
    (∃ g : F.G₀, γ = g) ∨ ∃ g : F.G₀, γ = g * F.c := by
  by_cases h : γ ∈ F.η.ker
  · exact Or.inl ⟨⟨γ, h⟩, rfl⟩
  · refine Or.inr ⟨⟨γ * F.c, polZ_mem F h⟩, ?_⟩
    show γ = γ * F.c * F.c
    rw [mul_assoc, F.c_sq, mul_one]

private theorem polZ_conj {l : ℕ} [Fact l.Prime] (F : GFrame l) (g : F.G₀) :
    (F.conj g : F.Γ) = F.c * g * F.c := by
  show F.c * g * F.c⁻¹ = _
  rw [inv_eq_of_mul_eq_one_right F.c_sq]

private theorem polZ_ext {l : ℕ} [Fact l.Prime] (F : GFrame l) {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (rep : Representation A F.Γ M) (Z : F.G₀ → M) (hl : IsLocallyConstant Z)
    (hm : ∀ g h, Z (g * h) = Z g + rep g (Z h)) (hc : ∀ g, Z (F.conj g) = rep F.c (Z g)) :
    ∃ y ∈ Zl rep, y F.c = 0 ∧ ∀ g : F.G₀, y g = Z g := by
  classical
  obtain ⟨p, hp, hp1, hp2⟩ := polZ_proj F
  have hZ1 : Z 1 = 0 := by
    have h1 := hm 1 1
    simpa using h1
  have hpc : p F.c = 1 := by
    have h2 := hp2 1
    simpa using h2
  have hmem : (fun γ => Z (p γ)) ∈ Zl rep := by
    show IsLocallyConstant (fun γ => Z (p γ)) ∧
      ∀ g h : F.Γ, Z (p (g * h)) = Z (p g) + rep g (Z (p h))
    refine ⟨hl.comp_continuous hp, ?_⟩
    intro γ δ
    rcases polZ_cases F γ with ⟨g, rfl⟩ | ⟨g, rfl⟩ <;>
      rcases polZ_cases F δ with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · rw [← Subgroup.coe_mul]
      simp only [hp1]
      exact hm g h
    · rw [show (g : F.Γ) * (h * F.c) = ((g * h : F.G₀) : F.Γ) * F.c by
        simp only [Subgroup.coe_mul, mul_assoc]]
      simp only [hp1, hp2]
      exact hm g h
    · rw [show (g : F.Γ) * F.c * h = ((g * F.conj h : F.G₀) : F.Γ) * F.c by
        simp only [Subgroup.coe_mul, polZ_conj, mul_assoc, F.c_sq, mul_one]]
      simp only [hp1, hp2]
      rw [hm, hc, map_mul, Module.End.mul_apply]
    · rw [show (g : F.Γ) * F.c * (h * F.c) = ((g * F.conj h : F.G₀) : F.Γ) by
        simp only [Subgroup.coe_mul, polZ_conj, mul_assoc]]
      simp only [hp1, hp2]
      rw [hm, hc, map_mul, Module.End.mul_apply]
  refine ⟨fun γ => Z (p γ), hmem, ?_, fun g => ?_⟩
  · show Z (p F.c) = 0
    rw [hpc, hZ1]
  · show Z (p g) = Z g
    rw [hp1]

theorem UpperTheory.V.Pa.polZ :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (n : ℕ) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (χ : F.Γ → R) (V : Submodule A (Matrix (Fin n) (Fin n) R)) (rep : Representation A F.Γ V), IsAd F ρ χ V rep → (∀ z : F.G₀ → Matrix (Fin n) (Fin n) R, (∀ g, z g ∈ V) → IsLocallyConstant z → (∀ g h, z (g * h) = z g + χ g • (ρ g * z h * ρ g⁻¹)) → (∀ g, z (F.conj g) = -(χ F.c • (z g)ᵀ)) → ∃ y ∈ Zl rep, y F.c = 0 ∧ ∀ g : F.G₀, (y g : Matrix (Fin n) (Fin n) R) = z g) ∧ (∀ y ∈ Zl rep, y F.c = 0 → (∀ g : F.G₀, (y (F.conj g) : Matrix (Fin n) (Fin n) R) = -(χ F.c • (y g : Matrix (Fin n) (Fin n) R)ᵀ)) ∧ ((∀ g : F.G₀, y g = 0) → y = 0)) := by
  intro l _ F A R _ _ _ n ρ χ V rep hAd
  obtain ⟨hA1, hA2⟩ := hAd
  refine ⟨fun z hz hzl hzm hzc => ?_, fun y hy hyc => ?_⟩
  · obtain ⟨y, hy, hyc, hyg⟩ := polZ_ext F rep (fun g => (⟨z g, hz g⟩ : V))
      (IsLocallyConstant.desc _ Subtype.val hzl Subtype.val_injective)
      (fun g h => Subtype.ext (by simp only [Submodule.coe_add, hA1]; exact hzm g h))
      (fun g => Subtype.ext (by rw [hA2]; exact hzc g))
    exact ⟨y, hy, hyc, fun g => by rw [hyg g]⟩
  · obtain ⟨-, hyc'⟩ := hy
    refine ⟨fun g => ?_, fun h0 => ?_⟩
    · rw [polZ_conj, hyc', hyc', hyc, map_zero, add_zero, zero_add, hA2]
    · funext γ
      rcases polZ_cases F γ with ⟨g, rfl⟩ | ⟨g, rfl⟩
      · exact h0 g
      · rw [Pi.zero_apply, hyc', h0 g, hyc, map_zero, add_zero]
end

