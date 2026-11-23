module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataArith
public import Formalism.LocalRingCardinality.DataForms
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0017
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0035

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CanonicalTranslateJets
section
theorem UpperTheory.Reformulated.B.CanonicalTranslateJets.K_repr :
    ∀ (D : Formalism.BasicNotions.D7),
    ∀ x ∈ D.host.K,
      ∃ (p : ℚ) (q : ℚ),
        x =
          (↑p : D.host.E) +
            (↑q : D.host.E) *
              D.host.sqd := by
  intro D x hx
  have hs := D.host.sqd_sq
  have hx' : x ∈ Algebra.adjoin ℚ ({D.host.sqd} : Set D.host.E) :=
    (IntermediateField.adjoin_toSubalgebra_of_isAlgebraic fun y _ => Algebra.IsAlgebraic.isAlgebraic y).le hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy => exact ⟨0, 1, by simpa using hy⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy; obtain ⟨c, e, rfl⟩ := hz
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy; obtain ⟨c, e, rfl⟩ := hz
    exact ⟨a * c - b * e * D.host.d, a * e + b * c, by push_cast; linear_combination (b * e : D.host.E) * hs⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EmbeddingTypes
section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem UpperTheory.Reformulated.B.EmbeddingTypes.core {R K V : Type*} [CommRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (L : Submodule R V) (hL : Submodule.span K (L : Set V) = ⊤) (y : V) :
    ∃ s ∈ nonZeroDivisors R, s • y ∈ L := by
  have hy : y ∈ Submodule.span K (L : Set V) := hL ▸ Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K _ y hy
  exact ⟨t, t.2, by simpa [Submonoid.smul_def] using ht⟩

theorem UpperTheory.Reformulated.B.EmbeddingTypes.exists_smul_mem_base_lattice_alt :
    ∀ (D : Formalism.BasicNotions.D7) (j : ℕ) (y : (D.sp.W j).V),
    ∃ s ∈ nonZeroDivisors (NumberField.RingOfIntegers D.host.E),
      s • y ∈
        (D.sp.W
            j).L0 := by
  intro D j y
  classical
  let S := D.sp.W j
  have hspan : Submodule.span D.host.E (S.L0 : Set S.V) = ⊤ := by
    let W := Submodule.span D.host.E (S.L0 : Set S.V)
    change W = ⊤
    by_contra h
    let b := Module.finBasis D.host.E W
    let g : S.V →ₗ[D.host.E] (Fin (Module.finrank D.host.E W) → D.host.E) :=
      LinearMap.pi fun k => S.hT (b k)
    have hdim : Module.finrank D.host.E (Fin (Module.finrank D.host.E W) → D.host.E) < Module.finrank D.host.E S.V := by
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
      exact Submodule.finrank_lt h
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have hzero (y : W) : S.hT y x = 0 := by
      have hb : ∀ k, S.hT (b k) x = 0 := by
        intro k
        exact congrFun (LinearMap.mem_ker.mp hx) k
      have hy : y ∈ Submodule.span D.host.E (Set.range b) := b.span_eq ▸ Submodule.mem_top
      induction hy using Submodule.span_induction with
      | mem z hz => obtain ⟨k, rfl⟩ := hz; exact hb k
      | zero => simp
      | add u v _ _ hu hv => simp [map_add, hu, hv]
      | smul a z _ hz => simp [LinearMap.map_smulₛₗ, hz]
    have hsmul (a : D.host.E) : a • x ∈ S.L0 := by
      rw [← S.baseLattice_isUnimodular]
      change a • x ∈ Formalism.E.hdual S.hT S.L0
      simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
        LinearMap.restrictScalars_apply]
      intro y hy
      have hyzero := hzero ⟨y, Submodule.subset_span hy⟩
      simp [map_smul, hyzero]
    let i : D.host.E →ₗ[NumberField.RingOfIntegers D.host.E] S.L0 :=
      ((LinearMap.toSpanSingleton D.host.E _ x).restrictScalars _).codRestrict S.L0 hsmul
    let : Module.Finite (NumberField.RingOfIntegers D.host.E) S.L0 :=
      Module.Finite.iff_fg.mpr S.standardTuple_isLattice.fg
    let : Module.Finite (NumberField.RingOfIntegers D.host.E) D.host.E :=
      Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E hx₀ (congrArg Subtype.val hab)
    exact NumberField.RingOfIntegers.not_isField D.host.E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (NumberField.RingOfIntegers D.host.E) D.host.E) (Field.toIsField D.host.E))
  exact UpperTheory.Reformulated.B.EmbeddingTypes.core (K := D.host.E) _ hspan y
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsDenominatorThird
section
theorem UpperTheory.Reformulated.B.ExistsDenominatorThird.exists_den :
    ∀ {D : Formalism.BasicNotions.D7} (u : D.what₂.Word) (x : ((D.fm u).lat (0 : ℕ)).V),
    ∃ (d : NumberField.RingOfIntegers D.what₂.LL),
      d ≠ (0 : NumberField.RingOfIntegers D.what₂.LL) ∧
        d • x ∈
          ((D.fm u).lat
              (0 :
                ℕ)).L := by
  intro D u x
  have hx : x ∈ Submodule.span D.what₂.LL
      ((((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V)) := by
    rw [((D.fm u).lat_good 0).2.2]
    exact Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers D.what₂.LL)) D.what₂.LL _ x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t.1, nonZeroDivisors.ne_zero t.2, ht⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsIdealDenominator
section
theorem UpperTheory.Reformulated.B.ExistsIdealDenominator.exists_denI :
    ∀ {D : Formalism.BasicNotions.D7} (u : D.what₂.Word) (i : ℕ) (x : ((D.fm u).lat i).V),
    ∃ (d : NumberField.RingOfIntegers D.what₂.LL),
      d ≠ (0 : NumberField.RingOfIntegers D.what₂.LL) ∧
        d • x ∈
          ((D.fm u).lat
              i).L := by
  intro D u i x
  have hx : x ∈ Submodule.span D.what₂.LL (((D.fm u).lat i).L : Set ((D.fm u).lat i).V) := by
    rw [((D.fm u).lat_good i).2.2]
    exact Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers D.what₂.LL)) D.what₂.LL _ x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t.1, nonZeroDivisors.ne_zero t.2, ht⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSmulMemLattice
section
theorem UpperTheory.Reformulated.B.ExistsIntegerSmulMemOfSpanEqTop.exists_smul_mem :
    ∀ {D : Formalism.BasicNotions.D7} {N : ℕ}
    {L₁ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin N → D.host.E)},
    Submodule.span D.host.E (↑L₁ : Set (Fin N → D.host.E)) = ⊤ →
      ∀ (x : Fin N → D.host.E),
        ∃ (n : NumberField.RingOfIntegers D.host.E),
          n ≠ (0 : NumberField.RingOfIntegers D.host.E) ∧
            (↑n : D.host.E) • x ∈
              L₁ := by
  intro D N L₁ h x
  have hx : x ∈ Submodule.span D.host.E (↑L₁ : Set (Fin N → D.host.E)) := h ▸ Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers D.host.E)) D.host.E _ x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.ne_zero t.2, ht⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherLast
section
theorem UpperTheory.Reformulated.B.Rd4.exists_nat_smul_mem :
    ∀ {D : Formalism.BasicNotions.D7} {n : ℕ}
    {Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin n → D.host.E)},
    Submodule.IsFullLattice D.host.E Λ →
      ∀ (x : Fin n → D.host.E),
        ∃ (N : ℕ),
          (0 : ℕ) < N ∧
            (↑N : D.host.E) • x ∈
              Λ := by
  intro D n Λ h x
  obtain ⟨⟨_, m, hm, rfl⟩, ht⟩ := multiple_mem_span_of_mem_localization_span
    (Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers D.host.E) (nonZeroDivisors ℤ))
    D.host.E (Λ : Set (Fin n → D.host.E)) x (by rw [h.span_eq_top]; trivial)
  change algebraMap ℤ (NumberField.RingOfIntegers D.host.E) m • x ∈ _ at ht
  rw [Submodule.span_eq, algebraMap_smul] at ht
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  refine ⟨m.natAbs * m.natAbs, by positivity, ?_⟩
  rw [Nat.cast_smul_eq_nsmul, ← natCast_zsmul, Int.natAbs_mul_self, mul_smul]
  exact zsmul_mem ht m
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerExtra
section
theorem UpperTheory.Reformulated.B.Gub1.proof.{u_1, u_2} :
    ∀ (E : Type u_1) (W : Type u_2) [inst : Field E] [inst_1 : NumberField E] [inst_2 : AddCommGroup W]
      [inst_3 : _root_.Module E W], GroundTheory.Heights₂.Heights.FiniteCovolume.LineIndexNeZero.Statement E W := by
  intro E W _ _ _ _ La x hL _ _
  have hfg : (La ⊓ (Submodule.span E {x}).toAddSubgroup).FG :=
    (Submodule.fg_iff_addSubgroup_fg (AddSubgroup.toIntSubmodule _)).1
      (((Submodule.fg_iff_addSubgroup_fg (AddSubgroup.toIntSubmodule La)).2 hL.fg).of_le
        (AddSubgroup.toIntSubmodule.monotone inf_le_left))
  have := (AddGroup.fg_iff_addSubgroup_fg _).2 hfg
  refine @AddSubgroup.index_ne_zero_of_finite _ _ _ (AddCommGroup.finite_of_fg_isAddTorsion _ ?_)
  rintro ⟨y, hy', hy⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  obtain ⟨n, hn, hc⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
    (Algebra.IsAlgebraic.isAlgebraic c)).exists_integral_multiple
  refine isOfFinAddOrder_iff_zsmul_eq_zero.2 ⟨n, hn, (QuotientAddGroup.eq_zero_iff (n • _)).2 ?_⟩
  exact ⟨⟨n • c, hc⟩, smul_assoc n c x⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralClosureCriterionSecond
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.be :
    Formalism.BasicNotions.D7 → ℂ :=
    fun (D : Formalism.BasicNotions.D7) ↦ Complex.I * (↑√(↑D.host.d : ℝ) : ℂ)

noncomputable def UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.OKc :
    Formalism.BasicNotions.D7 → ℂ → Prop :=
    fun (D : Formalism.BasicNotions.D7) (z : ℂ) ↦
      ∃ (x : ℤ) (y : ℤ), Even (x - y) ∧ z = ((↑x : ℂ) + (↑y : ℂ) * UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.be D) / (2 : ℂ)

theorem UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.okc_of :
    ∀ (D : Formalism.BasicNotions.D7) (u : NumberField.RingOfIntegers ↥D.host.K),
      UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.OKc D ((D.host.φ₀ : D.host.E → ℂ) (↑(↑u : ↥D.host.K) : D.host.E)) := by
  intro D u
  have hd : Nat.Prime D.host.d := D.host.hyp.2.1
  have hint : IsIntegral ℤ ((u : D.host.K) : D.host.E) :=
    (NumberField.RingOfIntegers.isIntegral_coe u).map (D.host.K.val.toRingHom.toIntAlgHom)
  obtain ⟨x, y, hxy, hz⟩ := UpperTheory.integral_imag_quadratic_half_int D.host.E D.host.d D.host.sqd hd.squarefree
    D.host.sqd_sq _ (u : D.host.K).2 hint
  have hs : D.host.φ₀ D.host.sqd = UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.be D := D.host.φ₀_mem
  refine ⟨x, y, hxy, ?_⟩
  rw [hz, map_div₀, map_add (f := _), map_mul, map_intCast, map_intCast, hs, map_ofNat]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LatticeVariant
section
theorem UpperTheory.Reformulated.B.LatticeVariant.lsd_spanDen :
    ∀ {D : Formalism.BasicNotions.D7} {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers D.host.E) (Fin n → D.host.E)),
    Submodule.span D.host.E (↑L : Set (Fin n → D.host.E)) = ⊤ →
      ∀ (x : Fin n → D.host.E),
        ∃ (d : NumberField.RingOfIntegers D.host.E),
          d ≠ (0 : NumberField.RingOfIntegers D.host.E) ∧
            (↑d : D.host.E) • x ∈
              L := by
  intro D n L hL x
  have hx : x ∈ Submodule.span D.host.E (↑L : Set (Fin n → D.host.E)) := hL ▸ Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers D.host.E)) D.host.E _ x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t.1, nonZeroDivisors.ne_zero t.2, ht⟩
end

