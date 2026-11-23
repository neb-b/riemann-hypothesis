module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartFiniteType
section
noncomputable section

namespace GlobalTheory.ModelPoints

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem existsUnique_extension {W L : Type} [CommRing W] [IsDomain W] [ValuationRing W] [Field L] [Algebra W L]
    [IsFractionRing W L] {X S : Scheme.{0}} (s : X ⟶ S) [IsProper s] (y : Sp L ⟶ X) (r : Sp W ⟶ S)
    (h : y ≫ s = spMap (algebraMap W L) ≫ r) :
    ∃! x : Sp W ⟶ X, x ≫ s = r ∧ spMap (algebraMap W L) ≫ x = y := by
  have hP : (ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType) s := by
    rw [← IsProper.eq_valuativeCriterion]
    exact ‹IsProper s›
  let S : ValuativeCommSq s := { R := W, K := L, i₁ := y, i₂ := r, commSq := ⟨h⟩ }
  obtain ⟨u⟩ := hP.1.1.1 S
  refine ⟨u.default.l, ⟨u.default.fac_right, u.default.fac_left⟩, ?_⟩
  rintro x ⟨hx₁, hx₂⟩
  exact congrArg CommSq.LiftStruct.l (u.uniq ⟨x, hx₂, hx₁⟩)

theorem existsUnique_chartHom {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (W : Type) [CommRing W]
    [IsLocalRing W] (yt : Sp W ⟶ X) (hy : yt (IsLocalRing.closedPoint W) ∈ U) :
    ∃! ψ : Γ(X, U) →+* W, spMap ψ ≫ hU.fromSpec = yt := by
  have hsub : Set.range yt ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint (R := W) p).map yt.continuous).mem_open U.isOpen hy
  let g := IsOpenImmersion.lift hU.fromSpec yt hsub
  have hg : g ≫ hU.fromSpec = yt := IsOpenImmersion.lift_fac _ _ _
  refine ⟨(Spec.preimage g).hom, ?_, ?_⟩
  · show Spec.map (CommRingCat.ofHom (Spec.preimage g).hom) ≫ hU.fromSpec = yt
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, hg]
  · intro ψ hψ
    have h₁ : Spec.map (CommRingCat.ofHom ψ) = g := by
      rw [← cancel_mono hU.fromSpec, hg]
      exact hψ
    have h₂ : CommRingCat.ofHom ψ = Spec.preimage g :=
      Spec.map_injective (h₁.trans (Spec.map_preimage g).symm)
    rw [← h₂]
    rfl

theorem exists_chart_finiteType {O : Type} [CommRing O] {X : Scheme.{0}} (s : X ⟶ Sp O) [LocallyOfFiniteType s]
    {U : X.Opens} (hU : IsAffineOpen U) : ∃ α : O →+* Γ(X, U), hU.fromSpec ≫ s = spMap α ∧ α.FiniteType := by
  refine ⟨(Spec.preimage (hU.fromSpec ≫ s)).hom, ?_, ?_⟩
  · show _ = Spec.map (CommRingCat.ofHom _)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  · have hlf : LocallyOfFiniteType (Spec.map (Spec.preimage (hU.fromSpec ≫ s))) := by
      rw [Spec.map_preimage]
      infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hlf

theorem model_points_charts :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), (∀ (W L : Type) [CommRing W] [IsDomain W] [ValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (oV : O →+* W) (fK : c.F →+* L) (y : Sp L ⟶ Xo.XF c), (algebraMap W L).comp oV = fK.comp β → y ≫ pullback.snd _ _ = spMap fK → ∃! yt : Sp W ⟶ Y.X, yt ≫ Y.s = spMap oV ∧ spMap (algebraMap W L) ≫ yt = y ≫ Y.j) ∧ (∀ (S : Scheme.{0}) (f : S ⟶ Y.X), ∃ G : SAB H S, Nonempty (SABMap G Y.t f)) ∧ ∀ (U : Y.X.Opens) (hU : IsAffineOpen U), ∃ α : O →+* Γ(Y.X, U), hU.fromSpec ≫ Y.s = spMap α ∧ α.FiniteType ∧ ∀ (W : Type) [CommRing W] [IsLocalRing W] (yt : Sp W ⟶ Y.X), yt (IsLocalRing.closedPoint W) ∈ U → ∃! ψ : Γ(Y.X, U) →+* W, spMap ψ ≫ hU.fromSpec = yt := by
  intro E _ _ _ H D l Xo c O _ β Y
  haveI : IsProper Y.s := projProper O Y.X Y.s Y.proj
  refine ⟨?_, ?_, ?_⟩
  · intro W L _ _ _ _ _ _ oV fK y hc hy
    apply existsUnique_extension Y.s (y ≫ Y.j) (spMap oV)
    rw [Category.assoc, Model.j_s, ← Category.assoc, hy, ← spMap_comp, ← spMap_comp, hc]
  · intro S f
    have hp := sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull f Y.t
    exact ⟨_, ⟨hp.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose⟩⟩
  · intro U hU
    obtain ⟨α, hα, hft⟩ := exists_chart_finiteType Y.s hU
    exact ⟨α, hα, hft, fun W _ _ yt hyt => existsUnique_chartHom hU W yt hyt⟩

end GlobalTheory.ModelPoints
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCountableHolomorphicFamiliesSmooth
section
open Topology Filter

namespace GlobalTheory.SmoothPointCover

theorem exists_family_near (K A : Type) [Field K] [NumberField K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.Smooth K A] (σ : K →+* ℂ) (φ₀ : A →+* ℂ) (h₀ : φ₀.comp (algebraMap K A) = σ) :
    ∃ (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →+* ℂ)) (U : Set (A → ℂ)), U ∈ 𝓝 (φ₀ : A → ℂ) ∧
      IsOpen B ∧ (∀ b ∈ B, (φ b).comp (algebraMap K A) = σ) ∧
      (∀ a : A, DifferentiableOn ℂ (fun b => φ b a) B) ∧
      (∀ ψ : A →+* ℂ, ψ.comp (algebraMap K A) = σ → (ψ : A → ℂ) ∈ U → ∃ b ∈ B, φ b = ψ) ∧
      ∀ b ∈ B, ∀ a : A, a ≠ 0 → ∃ᶠ b' in 𝓝 b, φ b' a ≠ 0 := by
  classical
  obtain ⟨m, s, B, φ, S, ε, hB, hε, hφ, hd, hnear⟩ :=
    GlobalTheory.SmoothPointFamily.exists_holomorphic_family K A σ φ₀ h₀
  let U : Set (A → ℂ) := {f | ∀ a ∈ S, ‖f a - φ₀ a‖ < ε}
  have hU : IsOpen U := by
    have : U = ⋂ a ∈ S, {f : A → ℂ | ‖f a - φ₀ a‖ < ε} := by
      ext f; simp [U]
    rw [this]
    exact isOpen_biInter_finset fun a _ => isOpen_lt (by fun_prop) continuous_const
  have hc : ContinuousOn (fun b => (φ b : A → ℂ)) B := continuousOn_pi.2 fun a => (hd a).continuousOn
  refine ⟨m, B ∩ (fun b => (φ b : A → ℂ)) ⁻¹' U, φ, U, hU.mem_nhds (fun a _ => by simpa using hε),
    hc.isOpen_inter_preimage hB hU, fun b hb => (hφ b hb.1).1, fun a => (hd a).mono Set.inter_subset_left,
    fun ψ hψ hψU => ?_, fun b hb a ha => ?_⟩
  · obtain ⟨h1, h2⟩ := hnear ψ hψ hψU
    refine ⟨_, ⟨h1, ?_⟩, h2⟩
    rw [Set.mem_preimage, h2]
    exact hψU
  · rw [Filter.frequently_iff]
    intro V hV
    have hW : U ∩ (fun f : A → ℂ => fun i => f (s i)) ⁻¹' V ∈ 𝓝 (φ b : A → ℂ) := by
      refine Filter.inter_mem (hU.mem_nhds hb.2) ?_
      have hcs : Continuous (fun f : A → ℂ => fun i => f (s i)) := by fun_prop
      refine hcs.continuousAt.preimage_mem_nhds ?_
      have : (fun i => φ b (s i)) = b := funext (hφ b hb.1).2
      simpa only [this] using hV
    obtain ⟨S', δ, hδ, hS'⟩ := GlobalTheory.SmoothPointFamily.exists_finset_of_mem_nhds hW
    obtain ⟨P, hP, hPε⟩ := GlobalTheory.generic_points_dense GlobalTheory.exists_algIndep_tuple_near K A (FractionRing A) σ (φ b)
      (hφ b hb.1).1 S' δ hδ
    let ρ : A →+* ℂ := P.comp (algebraMap A (FractionRing A))
    have hρ : ρ.comp (algebraMap K A) = σ := RingHom.ext fun a => RingHom.congr_fun hP a
    obtain ⟨h3, h4⟩ := hS' ρ hPε
    refine ⟨_, h4, ?_⟩
    have h5 := (hnear ρ hρ h3).2
    change φ (fun i => ρ (s i)) a ≠ 0
    rw [h5]
    exact (map_ne_zero_iff ρ (P.injective.comp (IsFractionRing.injective A (FractionRing A)))).2 ha

theorem exists_countable_families : ∀ (K A : Type) [Field K] [NumberField K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.Smooth K A] (σ : K →+* ℂ), ∃ (ι : Type) (_ : Countable ι) (m : ι → ℕ) (B : ∀ i, Set (Fin (m i) → ℂ)) (φ : ∀ i, (Fin (m i) → ℂ) → (A →+* ℂ)), (∀ i, IsOpen (B i)) ∧ (∀ i, ∀ b ∈ B i, (φ i b).comp (algebraMap K A) = σ) ∧ (∀ i (a : A), DifferentiableOn ℂ (fun b => φ i b a) (B i)) ∧ (∀ ψ : A →+* ℂ, ψ.comp (algebraMap K A) = σ → ∃ i, ∃ b ∈ B i, φ i b = ψ) ∧ ∀ i, ∀ b ∈ B i, ∀ a : A, a ≠ 0 → ∃ᶠ b' in 𝓝 b, φ i b' a ≠ 0 := by
  intro K A _ _ _ _ _ _ σ
  haveI : Countable K := Countable.of_equiv _ (Module.finBasis ℚ K).equivFun.symm.toEquiv
  haveI : Countable A := by
    obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType K A)
    haveI : Countable (MvPolynomial (Fin n) K) := ReciprocityTheory.ChartRestriction.G.T0.NPB.countable_mvPoly
    exact hf.countable
  let X := {ψ : A →+* ℂ // ψ.comp (algebraMap K A) = σ}
  letI : TopologicalSpace X := TopologicalSpace.induced (fun ψ => (ψ.1 : A → ℂ)) inferInstance
  haveI : SecondCountableTopology X := TopologicalSpace.secondCountableTopology_induced X (A → ℂ) _
  choose m B φ U hU hB hσ hd hcov hne using fun x : X => exists_family_near K A σ x.1 x.2
  obtain ⟨t, ht, hcv⟩ := TopologicalSpace.countable_cover_nhds
    (f := fun x : X => (fun ψ : X => (ψ.1 : A → ℂ)) ⁻¹' U x)
    (fun x => continuous_induced_dom.continuousAt.preimage_mem_nhds (hU x))
  refine ⟨t, ht.to_subtype, fun i => m i.1, fun i => B i.1, fun i => φ i.1, fun i => hB i.1, fun i => hσ i.1,
    fun i => hd i.1, fun ψ hψ => ?_, fun i => hne i.1⟩
  have : (⟨ψ, hψ⟩ : X) ∈ ⋃ x ∈ t, (fun ψ : X => (ψ.1 : A → ℂ)) ⁻¹' U x := by rw [hcv]; trivial
  obtain ⟨x, hx, hψx⟩ := Set.mem_iUnion₂.1 this
  exact ⟨⟨x, hx⟩, hcov x ψ hψ hψx⟩

end GlobalTheory.SmoothPointCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FnFGFnTrdeg
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.FlagDim

theorem fnFG_fnTrdeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), ∀ (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FnFG Xo c ∧ FnTrdeg Xo c (Module.finrank ℚ E / 2 * (Dw.p * Dw.q + Dw.p * (Dw.p - 1) / 2 + Dw.q * (Dw.q - 1) / 2)) := by
  intro E _ _ _ H Dw l Xo c
  obtain ⟨h1, h2⟩ := GlobalTheory.Reg.kap_fg_trdeg E H Dw l Xo c
  refine ⟨fnFG_of Xo c h1, ?_⟩
  rw [← dim_add_card_flagVar E H Dw]
  exact fnTrdeg_of Xo c Dw.dim h2

end GlobalTheory.FlagDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.InjectiveAlgebraMapOfDvrOfIsIntegral
section
namespace GlobalTheory

open IsLocalRing


open IsLocalRing in
theorem _root_.GlobalTheory.dvr_finite_over_complete_dvr :
    ∀ (O V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O] [CommRing V] [IsDomain V]
      [IsDiscreteValuationRing V] [Algebra O V] [Module.Finite O V],
      Function.Injective (algebraMap O V) ∧ IsLocalHom (algebraMap O V) ∧
        IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧ CharZero V ∧
          (Finite (IsLocalRing.ResidueField O) → Finite (IsLocalRing.ResidueField V)) := by
  intro O V _ _ _ _ _ _ _ _ _ _
  haveI : Algebra.IsIntegral O V := Algebra.IsIntegral.of_finite O V
  have hinj : Function.Injective (algebraMap O V) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    by_contra h
    push_neg at h
    obtain ⟨a, ha, ha0⟩ := h
    have hker : (RingHom.ker (algebraMap O V)).IsMaximal := by
      refine Ideal.IsPrime.isMaximal (RingHom.ker_isPrime _) ?_
      intro hb
      apply ha0
      have hmem : a ∈ RingHom.ker (algebraMap O V) := ha
      rw [hb] at hmem
      exact (Ideal.mem_bot).1 hmem
    have hbot : (⊥ : Ideal V).IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) ⊥
        (by rwa [Ideal.under_def, ← RingHom.ker_eq_comap_bot])
    exact IsDiscreteValuationRing.not_a_field V (IsLocalRing.eq_maximalIdeal hbot).symm
  have hloc : IsLocalHom (algebraMap O V) :=
    RingHom.IsIntegral.isLocalHom (fun x => Algebra.IsIntegral.isIntegral x) hinj
  haveI := hloc
  refine ⟨hinj, hloc, ?_, charZero_of_injective_algebraMap hinj, fun h => ?_⟩
  swap
  · exact Module.finite_of_finite (ResidueField O)
  haveI : Module.IsTorsionFree O V := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  haveI : Module.Free O V := Module.free_of_finite_type_torsion_free'
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨q, hq⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hπm : π ∈ maximalIdeal O := (mem_maximalIdeal _).2 (mem_nonunits_iff.2 hπ.not_isUnit)
  have hp0 : algebraMap O V π ≠ 0 := (map_ne_zero_iff _ hinj).2 hπ.ne_zero
  have hpm : algebraMap O V π ∈ maximalIdeal V :=
    (mem_maximalIdeal _).2 (mem_nonunits_iff.2 fun hu => hπ.not_isUnit ((isUnit_map_iff _ _).1 hu))
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {algebraMap O V π}) (by simpa using hp0) hq
  have hpow : ∀ k, maximalIdeal V ^ (e * k) = Ideal.span {algebraMap O V π ^ k} := by
    intro k
    rw [hq.maximalIdeal_eq, Ideal.span_singleton_pow, pow_mul, ← Ideal.span_singleton_pow, ← he,
      Ideal.span_singleton_pow]
  refine
    { toIsHausdorff := IsHausdorff.of_isLocalRing _ _ (maximalIdeal.isMaximal V).ne_top
      toIsPrecomplete := ⟨fun f hf => ?_⟩ }
  have hf' : ∀ m n, m ≤ n → f m - f n ∈ maximalIdeal V ^ m := fun m n h => by
    simpa using SModEq.sub_mem.1 (hf h)
  have hg : ∀ m n, m ≤ n →
      ∃ y, f (e * m + m) - f (e * n + n) = algebraMap O V π ^ m * y := by
    intro m n h
    have h1 := hf' _ _ (Nat.add_le_add (Nat.mul_le_mul_left e h) h)
    have h2 : f (e * m + m) - f (e * n + n) ∈ Ideal.span {algebraMap O V π ^ m} := by
      rw [← hpow]
      exact Ideal.pow_le_pow_right (Nat.le_add_right _ _) h1
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h2
    exact ⟨y, by rw [← hy, mul_comm]⟩
  let b := Module.Free.chooseBasis O V
  have hc : ∀ i, ∀ {m n : ℕ}, m ≤ n →
      b.repr (f (e * m + m)) i ≡ b.repr (f (e * n + n)) i
        [SMOD (maximalIdeal O ^ m • ⊤ : Submodule O O)] := by
    intro i m n h
    obtain ⟨y, hy⟩ := hg m n h
    have hdiff : b.repr (f (e * m + m)) i - b.repr (f (e * n + n)) i = π ^ m * b.repr y i := by
      rw [← Finsupp.sub_apply, ← map_sub, hy, ← map_pow, ← Algebra.smul_def, map_smul,
        Finsupp.smul_apply, smul_eq_mul]
    have hmem : π ^ m * b.repr y i ∈ maximalIdeal O ^ m :=
      Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hπm m)
    rw [SModEq.sub_mem, hdiff]
    simpa using hmem
  choose l hl using fun i =>
    (inferInstance : IsPrecomplete (maximalIdeal O) O).prec
      (f := fun k => b.repr (f (e * k + k)) i) (hc i)
  refine ⟨∑ i, l i • b i, fun n => ?_⟩
  have hgn : f (e * n + n) - ∑ i, l i • b i ∈ maximalIdeal V ^ n := by
    have hex : ∀ i, ∃ t, b.repr (f (e * n + n)) i - l i = π ^ n * t := fun i => by
      have hmem := SModEq.sub_mem.1 (hl i n)
      simp only [smul_eq_mul, Ideal.mul_top] at hmem
      rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
      obtain ⟨t, ht⟩ := hmem
      exact ⟨t, by rw [← ht, mul_comm]⟩
    choose t ht using hex
    have hsum : f (e * n + n) - ∑ i, l i • b i =
        algebraMap O V π ^ n * ∑ i, t i • b i := by
      conv_lhs => rw [← b.sum_repr (f (e * n + n))]
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sub_smul, ht, mul_smul, Algebra.smul_def, map_pow]
    rw [hsum]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hpm n)
  have hfg : f n - f (e * n + n) ∈ maximalIdeal V ^ n := hf' n (e * n + n) (Nat.le_add_left _ _)
  have hsum := Ideal.add_mem _ hfg hgn
  rw [sub_add_sub_cancel] at hsum
  rw [SModEq.sub_mem]
  simpa using hsum

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.LieCombBaseChange

variable {R R' : Type} [CommRing R] [CommRing R']

private lemma spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (g : A →+* B) (k : B →+* C) : spMap k ≫ spMap g = spMap (k.comp g) := by
  unfold spMap
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem dualMap_epsScale (f : R →+* R') (c : R) :
    spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ spMap (epsScaleR c) =
      spMap (epsScaleR (f c)) ≫ spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) := by
  rw [spMap_comp_moduli_spaces, spMap_comp_moduli_spaces]
  congr 1
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [epsScaleR, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, mul_comm]

theorem dualMap_over (f : R →+* R') :
    spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ (epsR R).hom = (epsR R').hom ≫ spMap f := by
  simp only [epsR, Over.mk_hom]
  rw [spMap_comp_moduli_spaces, spMap_comp_moduli_spaces]
  congr 1
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem epsScale_over (c : R) : spMap (epsScaleR c) ≫ (epsR R).hom = (epsR R).hom := by
  simp only [epsR, Over.mk_hom]
  rw [spMap_comp_moduli_spaces]
  congr 1
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem prod_left_comp {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S} {T' : Over S'} (d : T'.left ⟶ T.left)
    (hd : d ≫ T.hom = T'.hom ≫ f) {n : ℕ} (u : Fin n → (T ⟶ G)) (u' : Fin n → (T' ⟶ G'))
    (hu : ∀ i, (u' i).left ≫ φ = d ≫ (u i).left) :
    (List.ofFn u').prod.left ≫ φ = d ≫ (List.ofFn u).prod.left := by
  have hd' : d ≫ T.hom = (Over.mk (T'.hom ≫ f)).hom := by simpa using hd
  have hsq : φ ≫ G.hom = G'.hom ≫ f := h.1.w

  have hone : (1 : T' ⟶ G').left ≫ φ = (1 : Over.mk (T'.hom ≫ f) ⟶ G).left := by
    let x₀ : Over.mk (T'.hom ≫ f) ⟶ G := Over.homMk ((1 : T' ⟶ G').left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc, hsq]
      rw [← Category.assoc, Over.w])
    have hx : x₀ * x₀ = x₀ := by
      apply Over.OverMorphism.ext
      rw [h.2 T' 1 1 x₀ x₀ rfl rfl, _root_.mul_one]
      rfl
    have h1 : x₀ = 1 := by simpa using hx
    rw [← h1]
    rfl

  have key : ∀ (m : ℕ) (u : Fin m → (T ⟶ G)) (u' : Fin m → (T' ⟶ G')),
      (∀ i, (u' i).left ≫ φ = d ≫ (u i).left) →
        (List.ofFn u').prod.left ≫ φ = ((Over.homMk d hd' : Over.mk (T'.hom ≫ f) ⟶ T) ≫ (List.ofFn u).prod).left := by
    intro m
    induction m with
    | zero =>
      intro u u' _
      simp only [List.ofFn_zero, List.prod_nil, MonObj.comp_one, hone]
    | succ m ih =>
      intro u u' hu
      rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.comp_mul]
      refine (h.2 T' _ _ _ _ ?_ ?_).symm
      · rw [Over.comp_left]
        exact (hu 0).symm
      · exact (ih _ _ fun i => hu i.succ).symm
  have := key n u u' hu
  rw [Over.comp_left] at this
  exact this

end GlobalTheory.LieCombBaseChange

namespace GlobalTheory

open LieCombBaseChange

theorem lieComb_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (G : Over (Sp R)) [GrpObj G] (G' : Over (Sp R')) [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap f) φ → ∀ (n : ℕ) (v : Fin n → (epsR R ⟶ G)) (w : epsR R ⟶ G) (a : Fin n → R) (v' : Fin n → (epsR R' ⟶ G')) (w' : epsR R' ⟶ G'), (∀ j, (v' j).left ≫ φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ (v j).left) → IsLieComb a v w → (w'.left ≫ φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ w.left ↔ IsLieComb (fun i => f (a i)) v' w') := by
  intro R R' _ _ f G _ G' _ φ h n v w a v' w' hv hc
  obtain ⟨u, hu, rfl⟩ := hc

  have hcomp : ∀ i, (spMap (epsScaleR (f (a i))) ≫ (v' i).left) ≫ φ =
      spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ (u i).left := by
    intro i
    rw [Category.assoc, hv i, hu i, ← Category.assoc, ← Category.assoc,
      LieCombBaseChange.dualMap_epsScale]
  have hprod : ∀ u'' : Fin n → (epsR R' ⟶ G'),
      (∀ i, (u'' i).left = spMap (epsScaleR (f (a i))) ≫ (v' i).left) →
        (List.ofFn u'').prod.left ≫ φ =
          spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ (List.ofFn u).prod.left := fun u'' hu'' =>
    LieCombBaseChange.prod_left_comp h _ (LieCombBaseChange.dualMap_over f) u u''
      (fun i => by rw [hu'' i]; exact hcomp i)
  constructor
  · intro hw
    let u' : Fin n → (epsR R' ⟶ G') := fun i =>
      Over.homMk (spMap (epsScaleR (f (a i))) ≫ (v' i).left) (by
        rw [Category.assoc, Over.w]
        exact LieCombBaseChange.epsScale_over _)
    refine ⟨u', fun i => rfl, ?_⟩

    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · rw [hw, hprod u' fun i => rfl]
    · rw [Over.w w', Over.w]
  · rintro ⟨u'', hu'', rfl⟩
    exact hprod u'' hu''

end GlobalTheory
end
end

