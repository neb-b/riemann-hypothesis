module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.FdomExistsAll
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1093
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantPositivePeterssonForm
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
open MeasureTheory

namespace GlobalTheory.DefU.Petersson

theorem topology_facts (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    T2Space (UA E n) ∧ LocallyCompactSpace (UA E n) ∧ SecondCountableTopology (UA E n) ∧ DiscreteTopology (ratU E n) := by
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.discreteTopology_latticeGL (E := E) (a := n)
  refine ⟨inferInstance, (GlobalTheory.DefU.LocAdm.isClosed_UA (E := E) (n := n)).isClosedEmbedding_subtypeVal.locallyCompactSpace,
    (Topology.IsEmbedding.subtypeVal (p := fun g : GA E n => g ∈ UA E n)).secondCountableTopology, ?_⟩
  have hm : ∀ x : ratU E n, ((x : UA E n) : GA E n) ∈ latticeGL E n := fun x => by
    obtain ⟨δ, hδ⟩ := x.2
    have h := GlobalTheory.CuspRep.CuspidalL2GL.ratGL_mem_latticeGL (E := E) δ
    rw [hδ] at h
    exact h
  let f : ratU E n → latticeGL E n := fun x => ⟨_, hm x⟩
  have hf : Continuous f := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hi : Function.Injective f := fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : latticeGL E n => (z : GA E n)) h))
  exact DiscreteTopology.of_continuous_injective hf hi

theorem exists_isOpen_isCompact_finU (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    ∃ K : Subgroup (finU (E := E) (n := n)), IsOpen (K : Set (finU (E := E) (n := n))) ∧ IsCompact (K : Set (finU (E := E) (n := n))) := by
  haveI := GlobalTheory.DefU.LocAdm.t2Space_adelicGL_cmField (E := E) (n := n)
  obtain ⟨U0, hU0o, hU0c⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E n
  let p : finU (E := E) (n := n) →* GL (Fin n) (Af E) :=
    (GeneralLinearGroup.map (pFin E)).comp ((UA E n).subtype.comp (finU (E := E) (n := n)).subtype)
  have hp : Continuous p := continuous_map_pFin.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hKo : IsOpen (U0.comap p : Set (finU (E := E) (n := n))) := hU0o.preimage hp
  have hfin : ∀ x : UA E n, x ∈ finU (E := E) (n := n) ↔
      finGL E n (GeneralLinearGroup.map (pFin E) (x : GA E n)) = (x : GA E n) := by
    intro x
    constructor
    · intro hx
      have h1 : GeneralLinearGroup.map (pInf E) (x : GA E n) = 1 := hx
      exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL])
    · intro hx
      change GeneralLinearGroup.map (pInf E) (x : GA E n) = 1
      rw [← hx, pInf_finGL]
  have hc : IsClosed ((finU (E := E) (n := n) : Subgroup (UA E n)) : Set (UA E n)) := by
    have e : ((finU (E := E) (n := n) : Subgroup (UA E n)) : Set (UA E n)) =
        {x : UA E n | finGL E n (GeneralLinearGroup.map (pFin E) (x : GA E n)) = (x : GA E n)} :=
      Set.ext hfin
    rw [e]
    exact isClosed_eq (GlobalTheory.DefU.LocAdm.continuous_finGL.comp (continuous_map_pFin.comp continuous_subtype_val))
      continuous_subtype_val
  have hι : Topology.IsClosedEmbedding (fun x : finU (E := E) (n := n) => ((x : UA E n) : GA E n)) :=
    GlobalTheory.DefU.LocAdm.isClosed_UA.isClosedEmbedding_subtypeVal.comp hc.isClosedEmbedding_subtypeVal
  exact ⟨U0.comap p, hKo, IsCompact.of_isClosed_subset
    (hι.isCompact_preimage (hU0c.image GlobalTheory.DefU.LocAdm.continuous_finGL))
    (Subgroup.isClosed_of_isOpen _ hKo) fun x hx => ⟨p x, hx, (hfin x).1 x.2⟩⟩

theorem exists_compact_cover (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    ∃ C : Set (UA E n), IsCompact C ∧ ∀ g, ∃ γ ∈ ratU E n, ∃ c ∈ C, g = γ * c := by
  classical
  obtain ⟨K, hKo, hKc⟩ := exists_isOpen_isCompact_finU E n
  obtain ⟨S, hS⟩ := GlobalTheory.T.definiteUnitary_classSet_finite E n K hKo
  haveI : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) := GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
  haveI : ∀ v : InfinitePlace E, CompactSpace (embU n v.embedding) := fun v => by
    obtain ⟨e, -⟩ := _root_.GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n v.embedding
    exact e.toHomeomorph.symm.compactSpace
  let P : (∀ v : InfinitePlace E, embU n v.embedding) → UA E n :=
    fun y => (Finset.univ.toList.map fun v => (y v : UA E n)).prod
  have hP : Continuous P :=
    continuous_list_prod _ fun v _ => continuous_subtype_val.comp (continuous_apply v)
  have hPc : IsCompact (Set.range P) := isCompact_range hP
  have hKc' : IsCompact (Subtype.val '' (K : Set (finU (E := E) (n := n)))) := hKc.image continuous_subtype_val
  refine ⟨_, (S.finite_toSet.isCompact.mul hPc).mul hKc', fun g => ?_⟩
  obtain ⟨γ, hγ, s, hs, x, hx, k, hk, e⟩ := hS g
  obtain ⟨y, hy, -, hyx⟩ := _root_.GlobalTheory.DefU.infU_eq_list_prod_embU E n x hx
  refine ⟨γ, hγ, s * x * k, Set.mul_mem_mul (Set.mul_mem_mul hs ⟨fun v => ⟨y v, hy v⟩, hyx⟩) ⟨k, hk, rfl⟩, ?_⟩
  rw [e, mul_assoc, mul_assoc, mul_assoc]

end GlobalTheory.DefU.Petersson

namespace GlobalTheory.DefU.Petersson


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in
theorem exists_invariant_pos_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
    ∃ B : GlobalTheory.DefU.autU E n →ₗ⋆[ℂ] GlobalTheory.DefU.autU E n →ₗ[ℂ] ℂ, (∀ u v, star (B u v) = B v u) ∧ (∀ v, 0 ≤ (B v v).re) ∧
      (∀ v, B v v = 0 → v = 0) ∧ ∀ g u v, B (GlobalTheory.DefU.autRep E n g u) (GlobalTheory.DefU.autRep E n g v) = B u v := by
  intro E _ _ _ n
  classical
  obtain ⟨h1, h2, h3, h4⟩ := topology_facts E n
  obtain ⟨C, hC, hcov⟩ := exists_compact_cover E n
  letI : MeasurableSpace (UA E n) := borel _
  haveI : BorelSpace (UA E n) := ⟨rfl⟩
  haveI : SecondCountableTopology (ratU E n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : TopologicalSpace.SeparableSpace (ratU E n) := inferInstance
  haveI : Countable (ratU E n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (UA E n), μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨𝓕, -, h𝓕'⟩ := Formalism.IndefR.Eqv.G5.fdom_exists_all (ratU E n)
  have h𝓕 := h𝓕' μ
  have hfin : μ 𝓕 < ⊤ := by
    refine lt_of_le_of_lt ?_ (hC.measure_lt_top (μ := μ))
    rw [h𝓕.measure_eq_tsum C]
    refine le_trans (measure_mono ?_) (measure_iUnion_le _)
    intro g hg
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov g
    exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨c, hc, rfl⟩, hg⟩
  haveI hR : μ.IsMulRightInvariant :=
    GlobalTheory.unimodular_of_isFundamentalDomain_finite _ (ratU E n) μ 𝓕 hμ h𝓕 hfin.ne
  have hl : ∀ u : autU E n, ∀ γ ∈ ratU E n, ∀ g, u.1 (γ * g) = u.1 g := fun u γ hγ g => u.2.left γ hγ g
  have hI : ∀ u v : autU E n, IntegrableOn (fun g => star (u.1 g) * v.1 g) 𝓕 μ := by
    intro u v
    have hc : Continuous (fun g => star (u.1 g) * v.1 g) := u.2.cont.star.mul v.2.cont
    obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
    refine Measure.integrableOn_of_bounded (M := M) hfin.ne hc.aestronglyMeasurable (ae_of_all _ fun g => ?_)
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov g
    simp only [hl u γ hγ, hl v γ hγ]
    exact hM c hc
  have hright : ∀ (y : UA E n) (f : UA E n → ℂ), (∀ γ ∈ ratU E n, ∀ h, f (γ * h) = f h) →
      ∫ h in 𝓕, f (h * y) ∂μ = ∫ h in 𝓕, f h ∂μ := by
    intro y f hf
    have h' : IsFundamentalDomain (ratU E n) ((fun h => h * y) '' 𝓕) μ := by
      refine h𝓕.image_of_equiv (Equiv.mulRight y) ?_ (Equiv.refl _) ?_
      · exact (measurePreserving_mul_right μ y⁻¹).quasiMeasurePreserving
      · intro γ h
        simp [Subgroup.smul_def, mul_assoc]
    rw [h𝓕.setIntegral_eq h' (f := f) (fun γ h => hf γ γ.2 h)]
    exact ((measurePreserving_mul_right μ y).setIntegral_image_emb
      (measurableEmbedding_mulRight y) f 𝓕).symm
  let F : autU E n → autU E n → ℂ := fun u v => ∫ g in 𝓕, star (u.1 g) * v.1 g ∂μ
  let B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) F
    (fun x x' y => by
      simp only [F]
      rw [← integral_add (hI x y) (hI x' y)]
      congr 1
      funext g
      change star (x.1 g + x'.1 g) * y.1 g = _
      simp only [star_add]
      ring)
    (fun c x y => by
      simp only [F, smul_eq_mul]
      rw [← integral_const_mul]
      congr 1
      funext g
      change star (c * x.1 g) * y.1 g = _
      simp only [star_mul, starRingEnd_apply]
      ring)
    (fun x y y' => by
      simp only [F]
      rw [← integral_add (hI x y) (hI x y')]
      congr 1
      funext g
      change star (x.1 g) * (y.1 g + y'.1 g) = _
      ring)
    (fun c x y => by
      simp only [F, smul_eq_mul, RingHom.id_apply]
      rw [← integral_const_mul]
      congr 1
      funext g
      change star (x.1 g) * (c * y.1 g) = _
      ring)
  have hB : ∀ u v, B u v = ∫ g in 𝓕, star (u.1 g) * v.1 g ∂μ := fun _ _ => rfl
  have hre : ∀ v, B v v = ((∫ g in 𝓕, ‖v.1 g‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    intro v
    rw [hB, ← integral_complex_ofReal]
    congr 1
    funext g
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  refine ⟨B, fun u v => ?_, fun v => ?_, fun v h0 => ?_, fun k u v => ?_⟩
  · rw [hB, hB, Complex.star_def, ← integral_conj]
    congr 1
    funext g
    simp only [map_mul, map_star, starRingEnd_apply, star_star]
    ring
  · rw [hre, Complex.ofReal_re]
    exact integral_nonneg fun g => by positivity
  · rw [hre, Complex.ofReal_eq_zero] at h0
    have hi : IntegrableOn (fun g => ‖v.1 g‖ ^ 2) 𝓕 μ := by
      have := (hI v v).norm
      have e2 : (fun g => ‖star (v.1 g) * v.1 g‖) = fun g => ‖v.1 g‖ ^ 2 := by
        funext g
        rw [norm_mul, norm_star, sq]
      rw [e2] at this
      exact this
    have hae := (integral_eq_zero_iff_of_nonneg (fun g => by positivity) hi).1 h0
    have := GlobalTheory.eq_zero_of_ae_fundamentalDomain_of_leftInvariant (ratU E n) μ 𝓕 h𝓕 v.1 v.2.cont (hl v) (by
      filter_upwards [hae] with g hg
      simpa using hg)
    exact Subtype.ext (funext this)
  · rw [hB, hB]
    exact hright k (fun g => star (u.1 g) * v.1 g) fun γ hγ g => by simp only [hl u γ hγ, hl v γ hγ]

end GlobalTheory.DefU.Petersson
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsOpenSubgroupAdicUnitsNoRootsOfUnity
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RootOpen


open Classical in
theorem finite_roots (E : Type) [Field E] [NumberField E] :
    {t : Eˣ | ∃ n : ℕ, 0 < n ∧ t ^ n = 1}.Finite := by
  have hF : Finite (NumberField.Units.torsion E) := inferInstance
  have hT : ((NumberField.Units.torsion E : Set (𝓞 E)ˣ)).Finite := Set.finite_coe_iff.1 hF
  refine (hT.image (Units.map (algebraMap (𝓞 E) E).toMonoidHom)).subset ?_
  rintro t ⟨n, hn, ht⟩
  have h1 : IsIntegral ℤ (t : E) := IsIntegral.of_pow hn (by rw [← Units.val_pow_eq_pow_val, ht]; exact isIntegral_one)
  have h2 : IsIntegral ℤ ((t⁻¹ : Eˣ) : E) :=
    IsIntegral.of_pow hn (by rw [← Units.val_pow_eq_pow_val, inv_pow, ht, inv_one]; exact isIntegral_one)
  let u : (𝓞 E)ˣ := ⟨⟨t, h1⟩, ⟨(t⁻¹ : Eˣ), h2⟩,
    NumberField.RingOfIntegers.ext (show (t : E) * ((t⁻¹ : Eˣ) : E) = 1 by simp),
    NumberField.RingOfIntegers.ext (show ((t⁻¹ : Eˣ) : E) * (t : E) = 1 by simp)⟩
  refine ⟨u, ?_, ?_⟩
  · show u ∈ CommGroup.torsion (𝓞 E)ˣ
    refine (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, ?_⟩)
    ext
    show ((t ^ n : Eˣ) : E) = 1
    simp [ht]
  · ext; rfl

variable {E : Type} [Field E] [NumberField E]

theorem val_eq_one_of_lt (w : HeightOneSpectrum (𝓞 E)) {z : w.adicCompletion E} (hz : Valued.v (z - 1) < 1) :
    Valued.v z = 1 := by
  have := Valuation.map_add_eq_of_lt_left (Valued.v) (x := (1 : w.adicCompletion E)) (y := z - 1) (by simpa using hz)
  simpa using this

def congOne (w : HeightOneSpectrum (𝓞 E)) (m : ℤ) (hm : m < 0) : Subgroup (w.adicCompletion E)ˣ where
  carrier := {z | Valued.v ((z : w.adicCompletion E) - 1) ≤ WithZero.exp m}
  one_mem' := by simp
  mul_mem' := by
    intro z u hz hu
    have hz' : Valued.v ((z : w.adicCompletion E) - 1) ≤ WithZero.exp m := hz
    have hu' : Valued.v ((u : w.adicCompletion E) - 1) ≤ WithZero.exp m := hu
    have hlt : WithZero.exp m < 1 := by
      rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 hm
    have h1 := val_eq_one_of_lt w (hz'.trans_lt hlt)
    show Valued.v (((z * u : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1) ≤ WithZero.exp m
    have e : ((z * u : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1 =
        (z : w.adicCompletion E) * ((u : w.adicCompletion E) - 1) + ((z : w.adicCompletion E) - 1) := by
      rw [Units.val_mul]; ring
    rw [e]
    refine Valuation.map_add_le _ ?_ hz'
    rw [map_mul, h1, one_mul]; exact hu'
  inv_mem' := by
    intro z hz
    have hz' : Valued.v ((z : w.adicCompletion E) - 1) ≤ WithZero.exp m := hz
    have hlt : WithZero.exp m < 1 := by
      rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 hm
    have h1 := val_eq_one_of_lt w (hz'.trans_lt hlt)
    show Valued.v (((z⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1) ≤ WithZero.exp m
    have e : ((z⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1 =
        ((z⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) * (1 - (z : w.adicCompletion E)) := by
      rw [mul_sub, mul_one, Units.inv_mul]
    rw [e, map_mul, Valuation.map_sub_swap, Units.val_inv_eq_inv_val, map_inv₀, h1, inv_one, one_mul]
    exact hz'

theorem isOpen_congOne (w : HeightOneSpectrum (𝓞 E)) (m : ℤ) (hm : m < 0) :
    IsOpen (congOne w m hm : Set (w.adicCompletion E)ˣ) :=
  (GlobalTheory.Mem.UnitOpen.isOpen_val_le w m).preimage (Units.continuous_val.sub continuous_const)

end GlobalTheory.RootOpen

namespace GlobalTheory.RootOpen

theorem exists_open_subgroup_no_roots : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ V : Subgroup (w.adicCompletion E)ˣ,
    IsOpen (V : Set (w.adicCompletion E)ˣ) ∧ ∀ t : Eˣ, (∃ n : ℕ, 0 < n ∧ t ^ n = 1) →
      Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom t ∈ V → t = 1 := by
  intro E _ _ w
  set S := {t : Eˣ | ∃ n : ℕ, 0 < n ∧ t ^ n = 1}
  have hL : ((fun t : Eˣ => WithZero.log (Valued.v ((algebraMap E (w.adicCompletion E) (t : E)) - 1))) ''
      (S \ {1})).Finite := ((finite_roots E).diff).image _
  obtain ⟨b, hb⟩ := hL.bddBelow
  refine ⟨congOne w (min b 0 - 1) (by omega), isOpen_congOne w _ _, fun t ht hV => ?_⟩
  by_contra h1
  have hmem := hb ⟨t, ⟨ht, h1⟩, rfl⟩
  have hne : Valued.v ((algebraMap E (w.adicCompletion E) (t : E)) - 1) ≠ 0 := by
    rw [Ne, map_eq_zero, sub_eq_zero, ← map_one (algebraMap E (w.adicCompletion E))]
    intro e
    exact h1 (Units.ext ((algebraMap E (w.adicCompletion E)).injective e))
  have hV' : Valued.v ((algebraMap E (w.adicCompletion E) (t : E)) - 1) ≤ WithZero.exp (min b 0 - 1) := hV
  rw [← WithZero.exp_log hne, WithZero.exp_le_exp] at hV'
  simp only at hmem
  omega

end GlobalTheory.RootOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitMulZpowUniformiserTmul
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GraphLocal

theorem exists_isUnit_mul_zpow_tmul :
    ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ'] [Algebra (K ⊗[ℂ] κ') L]
    (E : Place (algebraMap ℂ K)) (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime] (t : E.ring),
  Function.Injective (algebraMap (K ⊗[ℂ] κ') L) → Irreducible t →
  ∀ g : K, g ≠ 0 → ∃ q : locAt (L := L) 𝔭, IsUnit q ∧
    algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1) = q * (algebraMap (K ⊗[ℂ] κ') L ((t : K) ⊗ₜ 1)) ^ E.ord g := by
  intro K κ' L _ _ _ _ _ _ E 𝔭 _ t _ ht g hg
  set n := E.ord g
  have ht0 : (t : K) ≠ 0 := fun h => ht.ne_zero (Subtype.ext h)
  set u : K := g * (t : K) ^ (-n) with hu_def
  have hu0 : u ≠ 0 := mul_ne_zero hg (zpow_ne_zero _ ht0)
  have hord : E.ord u = 0 := by
    rw [hu_def, E.ord_mul hg (zpow_ne_zero _ ht0), E.ord_zpow, E.ord_irreducible ht]
    ring
  have hu : u ∈ E.ring := (E.ord_nonneg_iff hu0).1 hord.ge
  have hui : u⁻¹ ∈ E.ring := (E.ord_nonneg_iff (inv_ne_zero hu0)).1 (by rw [E.ord_inv, hord]; simp)
  let b : tens (κ' := κ') (placeAlg E) := ⟨u ⊗ₜ 1, tmul_mem (mem_placeAlg.2 hu) 1⟩
  let b' : tens (κ' := κ') (placeAlg E) := ⟨u⁻¹ ⊗ₜ 1, tmul_mem (mem_placeAlg.2 hui) 1⟩
  have hbb : b * b' = 1 := by
    apply Subtype.ext
    change (u ⊗ₜ[ℂ] (1 : κ')) * (u⁻¹ ⊗ₜ 1) = 1
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hu0, one_mul]
    rfl
  refine ⟨toQ (L := L) 𝔭 b, (IsUnit.of_mul_eq_one (b := b') hbb).map _, ?_⟩
  let φ : K →+* L := (algebraMap (K ⊗[ℂ] κ') L).comp Algebra.TensorProduct.includeLeftRingHom
  have hφ (x : K) : φ x = algebraMap (K ⊗[ℂ] κ') L (x ⊗ₜ 1) := rfl
  have hg' : g = u * (t : K) ^ n := by
    rw [hu_def, mul_assoc, ← zpow_add₀ ht0, neg_add_cancel, zpow_zero, mul_one]
  rw [coe_toQ, ← hφ, ← hφ, ← hφ, ← map_zpow₀, ← map_mul, ← hg']

end GlobalTheory.GraphLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoAlgebraisation
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AlgUniq

theorem isPullback_square {S S' : Scheme.{0}} {G : Over S} {A : Over S'} {f : S' ⟶ S}
    {a : A.left ⟶ G.left} (hA : IsPullback a A.hom G.hom f)
    {φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left} (h : Geo.Tor.IsSquare a φ₂) :
    IsPullback φ₂ (A ⊗ A).hom (G ⊗ G).hom f := by
  have w₁ : (fst G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have w₂ : (snd G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have v₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₂ : (snd A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have h₁ := h.1
  have h₂ := h.2
  refine ⟨⟨by rw [← w₁, reassoc_of% h₁, hA.w, reassoc_of% v₁]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst G G).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd G G).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply pullback.hom_ext
    · change _ ≫ (fst G G).left = _ ≫ (fst G G).left
      rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ a) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · change _ ≫ (snd G G).left = _ ≫ (snd G G).left
      rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ a) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ A.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₁]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₂]

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Z ⟶ Y)
    (c : Z ⟶ X) (e : b ≫ a = c) : LBIso (L.pull c) ((L.pull a).pull b) := by
  subst e
  exact LBIso.symm (LBIso.chartPull (chartPullLinComb L a (fun _ : PUnit => b)
      (fun _ => b ≫ a) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
      (chartPullId _) (PolBaseChange.lbIso_refl (pull_isLB hL _)))

theorem square_comp {S S' : Scheme.{0}} {G G' : Over S} {A : Over S'} {a : A.left ⟶ G.left}
    {a' : A.left ⟶ G'.left} {g : G ⟶ G'} (hg : a ≫ g.left = a')
    {φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left} {φ₂' : (A ⊗ A).left ⟶ (G' ⊗ G').left}
    (h : Geo.Tor.IsSquare a φ₂) (h' : Geo.Tor.IsSquare a' φ₂') : φ₂ ≫ (g ⊗ₘ g).left = φ₂' := by
  have h₁ := h.1
  have h₂ := h.2
  apply pullback.hom_ext
  · change _ ≫ (fst G' G').left = _ ≫ (fst G' G').left
    rw [Category.assoc, ← Over.comp_left, tensorHom_fst, Over.comp_left, reassoc_of% h₁, hg, h'.1]
  · change _ ≫ (snd G' G').left = _ ≫ (snd G' G').left
    rw [Category.assoc, ← Over.comp_left, tensorHom_snd, Over.comp_left, reassoc_of% h₂, hg, h'.2]

theorem exists_iso_algebraisation : GlobalTheory.Published.FormalAlgebraisation.Morphisms → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (B B' : Over (Spec (CommRingCat.of R))) [GrpObj B] [GrpObj B'], IsAbelianScheme B → IsAbelianScheme B' → IsProjBy B.hom → ∀ (b : ∀ e, (Y e).left ⟶ B.left) (b' : ∀ e, (Y e).left ⟶ B'.left), (∀ e, IsGrpPullback (Y e) B (thick R I e) (b e)) → (∀ e, β e ≫ b (e + 1) = b e) → (∀ e, IsGrpPullback (Y e) B' (thick R I e) (b' e)) → (∀ e, β e ≫ b' (e + 1) = b' e) → ∃ g : B ≅ B', IsMonHom g.hom ∧ (∀ e, b e ≫ g.hom.left = b' e) ∧ (∀ g' : B ⟶ B', (∀ e, b e ≫ g'.left = b' e) → g' = g.hom) ∧ (∀ (M : LB B.left) (M' : LB B'.left), M.IsLB → M'.IsLB → (∀ e, LBIso (M.pull (b e)) (M'.pull (b' e))) → LBIso M (M'.pull g.hom.left)) ∧ ∀ (P : LB (B ⊗ B).left) (P' : LB (B' ⊗ B').left) (b₂ : ∀ e, (Y e ⊗ Y e).left ⟶ (B ⊗ B).left) (b₂' : ∀ e, (Y e ⊗ Y e).left ⟶ (B' ⊗ B').left), P.IsLB → P'.IsLB → (∀ e, Geo.Tor.IsSquare (b e) (b₂ e)) → (∀ e, Geo.Tor.IsSquare (b' e) (b₂' e)) → (∀ e, LBIso (P.pull (b₂ e)) (P'.pull (b₂' e))) → LBIso P (P'.pull (g.hom ⊗ₘ g.hom).left) := by
  intro H R _ _ I hI Y _ β B B' _ _ hB hB' hp b b' hb hβ hb' hβ'
  have := hB.proper
  have := hB'.proper
  obtain ⟨g, hg, hu⟩ := H.exists_iso hI (fun e => (hb e).1) hβ (fun e => (hb' e).1) hβ'
  obtain ⟨k, hk, hk', -⟩ := _root_.GlobalTheory.grpHom_algebraise H R I hI B B' hB.proper hB'.proper Y Y β β b b' hb hβ hb' hβ'
    (fun e => 𝟙 _) (fun e => inferInstance)
    (fun e => by rw [Over.id_left, Over.id_left, Category.comp_id, Category.id_comp])
  have hkg : k = g.hom := hu k fun e => by rw [hk', Over.id_left, Category.id_comp]
  refine ⟨g, hkg ▸ hk, hg, hu, fun M M' hM hM' h => ?_, fun P P' b₂ b₂' hP hP' hs hs' h => ?_⟩
  · exact _root_.GlobalTheory.LBReductions.lbIso_of_reductions R I hI B hB.smooth hp hB.geomConnected Y b (fun e => (hb e).1) M _ hM
      (pull_isLB hM' _) fun e => (h e).trans (pull_isLB hM _) (pull_isLB hM' _)
        (pull_isLB (pull_isLB hM' _) _) (lbIso_pull_comp hM' _ _ _ (hg e))
  · have hBB := AbelianSchemeGerms.isAbelianScheme_tensor B B hB hB
    exact _root_.GlobalTheory.LBReductions.lbIso_of_reductions R I hI (B ⊗ B) hBB.smooth (isProjBy_tensor R B B hp hp) hBB.geomConnected
      (fun e => Y e ⊗ Y e) b₂ (fun e => isPullback_square (hb e).1 (hs e)) P _ hP
      (pull_isLB hP' _) fun e => (h e).trans (pull_isLB hP _) (pull_isLB hP' _)
        (pull_isLB (pull_isLB hP' _) _) (lbIso_pull_comp hP' _ _ _ (square_comp (hg e) (hs e) (hs' e)))

end GlobalTheory.AlgUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenConjStableSubgroupOfSplitLevelStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_conjStable_subgroup_of_splitLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (K' : Subgroup (UL n w)), IsSplitAt w →
    IsLevel (MonoidHom.id _) (KL n w) K' → ∃ N : Subgroup (GLw n w), IsOpen (N : Set (GLw n w)) ∧
      N ≤ K'.map (UL n w).subtype ∧ (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ x ∈ N, k⁻¹ * x * k ∈ N) ∧
      (K' = KL n w → N = GlobalTheory.LFun.KGL w (n := n)) := by
  first | exact @GlobalTheory.BCT.CtLevel.exists_open_conjStable_sub_level | exact GlobalTheory.BCT.CtLevel.exists_open_conjStable_sub_level | (intros; apply GlobalTheory.BCT.CtLevel.exists_open_conjStable_sub_level <;> assumption)
end

