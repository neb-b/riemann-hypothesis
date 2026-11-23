module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini
public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.AbsComm
section
open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

theorem UpperTheory.V.Z.Tf.Orb.absComm :
    UpperTheory.V.Z.Tf.Orb.QuotFubini → UpperTheory.V.Z.Tf.Orb.QuotRight → UpperTheory.V.Z.Tf.Orb.FinPres → UpperTheory.V.Z.Tf.Orb.AbsComm := by
  intro hF hR hP G _ _ _ _ _ _ _ _ μG hμG r1 r2 θ hθ l hl hθl δ hD μ hμ hi a b a1 a2 b1 b2
  have hcl : IsClosed (twCent θ δ : Set G) :=
    isClosed_eq ((continuous_inv.mul continuous_const).mul hθ) continuous_const
  haveI : LocallyCompactSpace (twCent θ δ) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (twCent θ δ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace (twCent θ δ) := inferInstance
  haveI : SigmaFinite μ := inferInstance
  have hmp := hP G μG hμG θ hθ l hl hθl
  have hθθ : ∀ x, (θ ^ (l - 1)) (θ x) = x := fun x => by
    rw [← pow_succ_apply, Nat.sub_add_cancel (Nat.pos_of_ne_zero hl), hθl]; rfl
  have hθθ' : ∀ x, θ ((θ ^ (l - 1)) x) = x := fun x => by
    rw [← pow_succ_apply', Nat.sub_add_cancel (Nat.pos_of_ne_zero hl), hθl]; rfl
  have hpc : ∀ m : ℕ, Continuous (θ ^ m : Monoid.End G) := fun m => by
    induction m with
    | zero => exact continuous_id
    | succ m ih => exact (ih.comp hθ).congr fun x => (pow_succ_apply θ m x).symm
  let e : G ≃ₜ G := ⟨⟨θ, (θ ^ (l - 1) : Monoid.End G), hθθ, hθθ'⟩, hθ, hpc _⟩
  have hinv : ∀ h ∈ twCent θ δ, ∀ g, twConj θ (h * g) δ = twConj θ g δ := fun h hh g => twConj_mul_left θ δ hh g
  have hct : Continuous fun g => twConj θ g δ := (continuous_inv.mul continuous_const).mul hθ
  obtain ⟨D1, d1, e1⟩ := hD _ (a2.isCompact.mul b2.isCompact)
  obtain ⟨D2, d2, e2⟩ := hD _ (b2.isCompact.mul (a2.isCompact.image hθ))
  have k1 := hF G μG hμG _ hcl μ hμ hi (fun y g => a y * b (y⁻¹ * twConj θ g δ))
    ((a1.comp continuous_fst).mul (b1.comp (continuous_fst.inv.mul (hct.comp continuous_snd))))
    (fun y h hh g => by simp only [hinv h hh]) ⟨_, D1, a2.isCompact, d1, fun y g hne =>
      ⟨subset_tsupport _ (left_ne_zero_of_mul hne), e1 g ⟨y, subset_tsupport _ (left_ne_zero_of_mul hne), _,
        subset_tsupport _ (right_ne_zero_of_mul hne), by simp⟩⟩⟩
  have k2 := hF G μG hμG _ hcl μ hμ hi (fun y g => a y * b (twConj θ g δ * (θ y)⁻¹))
    ((a1.comp continuous_fst).mul (b1.comp ((hct.comp continuous_snd).mul (hθ.comp continuous_fst).inv)))
    (fun y h hh g => by simp only [hinv h hh]) ⟨_, D2, a2.isCompact, d2, fun y g hne =>
      ⟨subset_tsupport _ (left_ne_zero_of_mul hne), e2 g ⟨_, subset_tsupport _ (right_ne_zero_of_mul hne), θ y,
        ⟨y, subset_tsupport _ (left_ne_zero_of_mul hne), rfl⟩, by simp⟩⟩⟩
  have k3 : ∀ x, conv μG b (fun x => a ((θ ^ (l - 1)) x)) x = ∫ y, a y * b (x * (θ y)⁻¹) ∂μG := fun x => by
    have s1 := hmp.integral_comp e.measurableEmbedding fun w => a ((θ ^ (l - 1)) w) * b (x * w⁻¹)
    simp only [hθθ] at s1
    rw [s1, ← integral_inv_eq_self, ← integral_mul_left_eq_self _ x⁻¹, conv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp [mul_comm]
  rw [twOrbIntegralC, twOrbIntegralC]
  simp only [k3]
  rw [k2]
  refine k1.trans (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_))
  have k4 := hR G μG hμG r1 _ μ inferInstance hi (fun g => a y * b (y⁻¹ * twConj θ g δ))
    (continuous_const.mul (b1.comp (continuous_const.mul hct))).measurable (fun h hh g => by simp only [hinv h hh]) y⁻¹
  refine k4.symm.trans ?_
  congr 1
  funext g
  simp [twConj, mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.CentComm
section
noncomputable section

open Module

namespace UpperTheory.V.Z.Tf.Orb

private theorem endComm {L V : Type} [Field L] [IsAlgClosed L] [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (f x y : Module.End L V) (hf : f.charpoly.Separable) (hx : Commute x f) (hy : Commute y f) : Commute x y := by
  have key : ∀ μ : L, ∀ v ∈ f.maxGenEigenspace μ, (x * y) v = (y * x) v := by
    intro μ v hv
    have h1 : finrank L (f.maxGenEigenspace μ) ≤ 1 := by
      rw [LinearMap.finrank_maxGenEigenspace_eq]
      exact Polynomial.rootMultiplicity_le_one_of_separable hf μ
    obtain ⟨w, hw⟩ := finrank_le_one_iff.mp h1
    have mx := Module.End.mapsTo_maxGenEigenspace_of_comm hx.symm μ
    have my := Module.End.mapsTo_maxGenEigenspace_of_comm hy.symm μ
    obtain ⟨c, hc⟩ := hw ⟨v, hv⟩
    obtain ⟨a, ha⟩ := hw ⟨x w, mx w.2⟩
    obtain ⟨b, hb⟩ := hw ⟨y w, my w.2⟩
    have hc' : v = c • (w : V) := by simpa using (congrArg Subtype.val hc).symm
    have ha' : x w = a • (w : V) := by simpa using (congrArg Subtype.val ha).symm
    have hb' : y w = b • (w : V) := by simpa using (congrArg Subtype.val hb).symm
    simp only [hc', Module.End.mul_apply, map_smul, ha', hb', smul_smul, mul_comm a b]
  have htop := Module.End.iSup_maxGenEigenspace_eq_top f
  have : (⊤ : Submodule L V) ≤ LinearMap.eqLocus (x * y) (y * x) := by
    rw [← htop]
    exact iSup_le fun μ v hv => key μ v hv
  exact LinearMap.ext fun v => this Submodule.mem_top

theorem centComm : CentComm := by
  intro K _ n A X Y hA hX hY
  let L := AlgebraicClosure K
  let φ : Matrix (Fin n) (Fin n) K →+* Module.End L (Fin n → L) :=
    (Matrix.toLinAlgEquiv' (R := L) (n := Fin n)).toRingEquiv.toRingHom.comp (algebraMap K L).mapMatrix
  have hφ : Function.Injective φ :=
    (Matrix.toLinAlgEquiv' (R := L) (n := Fin n)).injective.comp
      (Matrix.map_injective (algebraMap K L).injective)
  have hch : (φ A).charpoly = A.charpoly.map (algebraMap K L) := by
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_toLin']
    rfl
  have h := endComm (φ A) (φ X) (φ Y) (hch ▸ hA.map) (hX.map φ) (hY.map φ)
  apply hφ
  rw [map_mul, map_mul]
  exact h

end UpperTheory.V.Z.Tf.Orb
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.ConvTest
section
open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

theorem UpperTheory.V.Z.Tf.Orb.convTest :
    UpperTheory.V.Z.Tf.Orb.ConvTest := by
  intro G _ _ _ _ _ _ _ _ μ hμ a b a1 a2 b1 b2
  constructor
  · have h : conv μ a b = fun x => ∫ y in tsupport a, a y * b (y⁻¹ * x) ∂μ := by
      funext x
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
      rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    rw [h]
    haveI : FirstCountableTopology G := inferInstance
    exact continuous_parametric_integral_of_continuous (by fun_prop) a2
  · refine HasCompactSupport.intro (a2.isCompact.mul b2.isCompact) fun x hx => ?_
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
    by_contra hne
    exact hx ⟨y, subset_tsupport _ (left_ne_zero_of_mul hne), y⁻¹ * x, subset_tsupport _ (right_ne_zero_of_mul hne), by simp⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.FinPres
section
noncomputable section

open MeasureTheory Topology

namespace UpperTheory.V.Z.Tf.Orb

theorem finPres : FinPres := by
  intro G _ _ _ _ _ _ _ _ μ hμ θ hθ l hl hθl
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl
  have hpow : ∀ j : ℕ, Continuous (θ ^ j : Monoid.End G) := by
    intro j
    induction j with
    | zero => exact continuous_id
    | succ j ih =>
      rw [pow_succ]
      exact ih.comp hθ
  have h1 : ∀ x, (θ ^ m : Monoid.End G) (θ x) = x := fun x => by
    have : (θ ^ (m + 1) : Monoid.End G) x = x := by rw [hθl]; rfl
    rw [pow_succ] at this
    exact this
  have h2 : ∀ x, θ ((θ ^ m : Monoid.End G) x) = x := fun x => by
    have : (θ ^ (m + 1) : Monoid.End G) x = x := by rw [hθl]; rfl
    rw [pow_succ'] at this
    exact this
  let e : G ≃* G :=
    { toFun := θ, invFun := (θ ^ m : Monoid.End G), left_inv := h1, right_inv := h2,
      map_mul' := map_mul θ }
  have hν : (Measure.map θ μ).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ e hθ (hpow m)
  obtain ⟨c, hc⟩ : ∃ c : NNReal, Measure.map θ μ = c • μ :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul (Measure.map θ μ) μ⟩
  have hj : ∀ j : ℕ, Measure.map (θ ^ j : Monoid.End G) μ = c ^ j • μ := by
    intro j
    induction j with
    | zero =>
      rw [pow_zero, pow_zero, one_smul]
      exact Measure.map_id
    | succ j ih =>
      have hcomp : ((θ ^ (j + 1) : Monoid.End G) : G → G) = (θ ^ j : Monoid.End G) ∘ θ := by
        rw [pow_succ]; rfl
      rw [hcomp, ← Measure.map_map (hpow j).measurable hθ.measurable, hc, Measure.map_smul c (hpow j).aemeasurable, ih,
        smul_smul, pow_succ']
  have hfin : c ^ (m + 1) • μ = μ := by
    rw [← hj, hθl]
    exact Measure.map_id
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
  have hK0 : μ K ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have hKt : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hc1 : c ^ (m + 1) = 1 := by
    have h := congrArg (fun ν : Measure G => ν K) hfin
    simp only [Measure.coe_nnreal_smul_apply] at h
    have h' : ((c ^ (m + 1) : NNReal) : ENNReal) * μ K = 1 * μ K := by rw [one_mul]; exact h
    exact_mod_cast (ENNReal.mul_left_inj hK0 hKt).mp h'
  have hc2 : c = 1 := (pow_eq_one_iff_of_nonneg (by positivity) (Nat.succ_ne_zero m)).mp hc1
  refine ⟨hθ.measurable, ?_⟩
  rw [hc, hc2, one_smul]

end UpperTheory.V.Z.Tf.Orb
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HaarComm
section
open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.haarComm :
    UpperTheory.V.Z.Tf.Orb.HaarComm := by
  intro G _ _ _ _ _ _ _ _ H hH hc μ hμ
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology _
  letI : CommGroup H := { (inferInstance : Group H) with mul_comm := fun a b => Subtype.ext (hc a a.2 b b.2) }
  refine ⟨inferInstance, Measure.IsHaarMeasure.isInvInvariant_of_regular μ, ⟨fun g => ?_⟩⟩
  have : (fun h : H => h * g) = fun h => g * h := funext fun h => mul_comm h g
  rw [this]
  exact map_mul_left_eq_self μ g
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HaarConj
section
open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.haarConj :
    UpperTheory.V.Z.Tf.Orb.HaarConj := by
  intro G _ _ _ _ _ _ _ _ H H' y hy μ hμ
  let e : H ≃ₜ* H' :=
    { toFun := fun x => ⟨y⁻¹ * x * y, (hy x).1 x.2⟩
      invFun := fun z => ⟨y * z * y⁻¹, (hy _).2 (by simp [mul_assoc])⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine ⟨μ.map e, e.isHaarMeasure_map μ, ?_⟩
  have he : Measurable (e : H → H') := (map_continuous e).measurable
  exact (Measure.map_map (g := fun x : H' => (x : G)) measurable_subtype_coe he).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HeckeRepresentationSatake
section
open ValuativeRel Topology

private theorem UpperTheory.V.Z.Tf.Orb.local_field_topology_facts (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] :
    T2Space E ∧ SecondCountableTopology E ∧ IsOpen {x : E | valuation E x ≤ 1} := by
  letI := IsTopologicalAddGroup.rightUniformSpace E
  haveI := isUniformAddGroup_of_addCommGroup (G := E)
  letI : (Valued.v (R := E)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := E).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  refine ⟨inferInstance, ?_, Valued.isOpen_integer E⟩
  open scoped Valued in
  have : ProperSpace E := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace E
  infer_instance

theorem UpperTheory.V.Z.Tf.Orb.gLTop :
    UpperTheory.V.Z.Tf.Orb.GLTop := by
  intro E _ _ _ _ n
  obtain ⟨h2, hsc, hO⟩ := UpperTheory.V.Z.Tf.Orb.local_field_topology_facts E
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) E) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → E))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) E) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → E))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) E)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) E)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  have hlast : ∀ Ω Ω' : Set (Matrix (Fin n) (Fin n) E), IsCompact Ω → IsCompact Ω' →
      IsCompact {g : GL (Fin n) E | (g : Matrix (Fin n) (Fin n) E) ∈ Ω ∧
        ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) ∈ Ω'} := by
    intro Ω Ω' hΩ hΩ'
    have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) E)).isCompact_preimage
      (hΩ.prod (hΩ'.image MulOpposite.continuous_op))
    have e : {g : GL (Fin n) E | (g : Matrix (Fin n) (Fin n) E) ∈ Ω ∧
        ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) ∈ Ω'} =
        Units.embedProduct (Matrix (Fin n) (Fin n) E) ⁻¹' (Ω ×ˢ (MulOpposite.op '' Ω')) := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod,
        MulOpposite.op_injective.mem_set_image]
    rw [e]
    exact h
  refine ⟨Units.isClosedEmbedding_embedProduct.locallyCompactSpace,
    Units.isEmbedding_embedProduct.secondCountableTopology, inferInstance, ?_, hlast⟩
  let O : Subring E := (valuation E).integer
  let M : Set (Matrix (Fin n) (Fin n) E) := {A | ∀ i j, A i j ∈ O}
  have hMmul : ∀ A ∈ M, ∀ B ∈ M, A * B ∈ M := by
    intro A hA B hB i j
    rw [Matrix.mul_apply]
    exact O.sum_mem fun l _ => O.mul_mem (hA i l) (hB l j)
  have hMone : (1 : Matrix (Fin n) (Fin n) E) ∈ M := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  have hMo : IsOpen M := by
    have e : M = ⋂ i, ⋂ j, (fun A : Matrix (Fin n) (Fin n) E => A i j) ⁻¹' {x : E | valuation E x ≤ 1} := by
      ext A
      simp only [M, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
      rfl
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hO.preimage (continuous_apply_apply i j)
  have hMc : IsCompact M := by
    have hc := IsNonarchimedeanLocalField.isCompact_closedBall E 1
    have h : IsCompact (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n =>
        {x : E | valuation E x ≤ 1}) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hc
    have e : M = (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n =>
        {x : E | valuation E x ≤ 1}) := by
      ext A
      exact ⟨fun hA i _ j _ => hA i j, fun hA i j => hA i trivial j trivial⟩
    rw [e]
    exact h
  let K : Subgroup (GL (Fin n) E) :=
    { carrier := {g : GL (Fin n) E | (g : Matrix (Fin n) (Fin n) E) ∈ M ∧
        ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) ∈ M}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨?_, ?_⟩
        · rw [Units.val_mul]
          exact hMmul _ ha _ hb
        · rw [mul_inv_rev, Units.val_mul]
          exact hMmul _ hb' _ ha'
      one_mem' := ⟨hMone, by rw [inv_one]; exact hMone⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨ha', by rw [inv_inv]; exact ha⟩ }
  refine ⟨K, ?_, hlast M M hMc hMc⟩
  exact (hMo.preimage Units.continuous_val).inter (hMo.preimage Units.continuous_coe_inv)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.NormEx
section
open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.normEx :
    UpperTheory.V.Z.Tf.Orb.NormEx := by
  classical
  intro G _ _ _ _ _ _ _ _ ⟨K, hKo, hKc⟩ H hH μ hμ hr
  let r : G → G := fun g => (DoubleCoset.mk H K g).out
  have hr1 : ∀ g, ∃ h ∈ H, ∃ k ∈ K, r g = h * g * k := fun g => by
    obtain ⟨h, hh, k, hk, e⟩ := DoubleCoset.mk_out_eq_mul H K g
    exact ⟨h, hh, k, hk, e⟩
  have hr2 : ∀ h ∈ H, ∀ g, ∀ k ∈ K, r (h * g * k) = r g := fun h hh g k hk =>
    congrArg Quotient.out ((@DoubleCoset.eq _ _ H K _ _).2 ⟨h, hh, k, hk, rfl⟩).symm
  let A : G → Set H := fun x => {h | x⁻¹ * h * x ∈ K}
  have hAo : ∀ x, IsOpen (A x) := fun x => hKo.preimage (by fun_prop)
  have hAc : ∀ x, IsCompact (A x) := fun x => by
    have h1 : IsCompact ((fun z => x⁻¹ * z * x) ⁻¹' (K : Set G)) :=
      ((Homeomorph.mulLeft x⁻¹).trans (Homeomorph.mulRight x)).isCompact_preimage.2 hKc
    exact hH.isClosedEmbedding_subtypeVal.isCompact_preimage h1
  have h0 : ∀ x, μ (A x) ≠ 0 := fun x => ((hAo x).measure_pos μ ⟨1, by simp [A, K.one_mem]⟩).ne'
  have ht : ∀ x, μ (A x) ≠ ∞ := fun x => (hAc x).measure_lt_top.ne
  let ρ : G → ℝ≥0∞ := fun g => if (r g)⁻¹ * g ∈ K then (μ (A (r g)))⁻¹ else 0
  have hk : ∀ g, ∀ k ∈ K, ρ (g * k) = ρ g := fun g k hk => by
    have : r (g * k) = r g := by simpa using hr2 1 H.one_mem g k hk
    simp only [ρ, this, ← mul_assoc, K.mul_mem_cancel_right hk]
  have hlc : IsLocallyConstant ρ := (IsLocallyConstant.iff_exists_open ρ).2 fun g =>
    ⟨(fun z => g⁻¹ * z) ⁻¹' K, hKo.preimage (by fun_prop), by simp [K.one_mem], fun z hz => by
      rw [← hk g _ hz, mul_inv_cancel_left]⟩
  refine ⟨ρ, ⟨hlc.continuous.measurable, fun g => ?_⟩, fun g => ?_⟩
  · obtain ⟨h₀, hh, k, hk', e⟩ := hr1 g
    have e1 : ∀ h : H, ρ (h * g) = (A (r g)).indicator (fun _ => (μ (A (r g)))⁻¹) (h * (⟨h₀, hh⟩ : H)⁻¹) := fun h => by
      have h1 : r (h * g) = r g := by simpa using hr2 h h.2 g 1 K.one_mem
      have h2 : (r g)⁻¹ * (h * g) ∈ K ↔ h * (⟨h₀, hh⟩ : H)⁻¹ ∈ A (r g) := by
        rw [← K.mul_mem_cancel_right hk']
        change _ ↔ (r g)⁻¹ * ((h : G) * h₀⁻¹) * r g ∈ K
        have : (r g)⁻¹ * ((h : G) * h₀⁻¹) * r g = (r g)⁻¹ * (h * g) * k := by
          nth_rewrite 2 [e]
          group
        rw [this]
      simp only [ρ, h1, Set.indicator, h2]
    rw [lintegral_congr e1, lintegral_mul_right_eq_self, lintegral_indicator_const (hAo _).measurableSet,
      ENNReal.inv_mul_cancel (h0 _) (ht _)]
  · simp only [ρ]
    split_ifs
    · exact ENNReal.inv_ne_top.2 (h0 _)
    · exact ENNReal.zero_ne_top
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.OrbComm
section
open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

theorem UpperTheory.V.Z.Tf.Orb.orbComm :
    UpperTheory.V.Z.Tf.Orb.TwOrbComm → UpperTheory.V.Z.Tf.Orb.Untwist → UpperTheory.V.Z.Tf.Orb.OrbComm := by
  intro hT hU k _ _ _ _ _ n _ _ μk hμk γ hγ μ hμ f f' p1 p2 p3 p4
  haveI : ValuativeExtension k k := ⟨fun {_ _} => Iff.rfl⟩
  obtain ⟨h0, h1, h2, h3⟩ := hU k n μk γ
  obtain ⟨μ', a, b, c⟩ := h3 μ hμ
  have t := hT k k 1 h0 n μk hμk γ (h2 hγ) μ' a f f' p1 p2 p3 p4 fun x => by rw [h1]
  simpa only [c] using t
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.OrbLin
section
open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

theorem UpperTheory.V.Z.Tf.Orb.orbLin :
    UpperTheory.V.Z.Tf.Orb.TwOrbLin → UpperTheory.V.Z.Tf.Orb.Untwist → UpperTheory.V.Z.Tf.Orb.OrbLin := by
  intro hT hU k _ _ _ _ _ n _ _ μk hμk γ hγ μ hμ
  haveI : ValuativeExtension k k := ⟨fun {_ _} => Iff.rfl⟩
  obtain ⟨h0, h1, h2, h3⟩ := hU k n μk γ
  obtain ⟨μ', a, b, c⟩ := h3 μ hμ
  have t := hT k k 1 h0 n μk hμk γ (h2 hγ) μ' a
  simpa only [c] using t
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotConj
section
open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.quotConj :
    UpperTheory.V.Z.Tf.Orb.HaarComm → UpperTheory.V.Z.Tf.Orb.QuotIndep → UpperTheory.V.Z.Tf.Orb.QuotConj := by
  intro hC hI G _ _ _ _ _ _ _ _ μG hμ H H' y hH hc hy μ μ' h1 h2 hm F hF hFH
  have hy' : ∀ z, z ∈ H' ↔ y * z * y⁻¹ ∈ H := fun z => by rw [hy]; simp [mul_assoc]
  have hH' : IsClosed (H' : Set G) := by
    have : (H' : Set G) = (fun z => y * z * y⁻¹) ⁻¹' H := Set.ext hy'
    rw [this]
    exact hH.preimage (by fun_prop)
  have hc' : ∀ a ∈ H', ∀ b ∈ H', Commute a b := fun a ha b hb => by
    have := (hc _ ((hy' a).1 ha) _ ((hy' b).1 hb)).eq
    have h : y * a * b = y * b * a := by simpa [← mul_assoc] using this
    rw [mul_assoc, mul_assoc] at h
    exact mul_left_cancel h
  obtain ⟨s1, i1, -⟩ := hC G H hH hc μ h1
  obtain ⟨s2, i2, -⟩ := hC G H' hH' hc' μ' h2
  have key : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ h : H, f (y⁻¹ * h * y) ∂μ = ∫⁻ h : H', f h ∂μ' := fun f hf => by
    rw [← lintegral_map hf (g := fun x : H => y⁻¹ * (x : G) * y) (by fun_prop), hm,
      lintegral_map hf (g := fun x : H' => (x : G)) measurable_subtype_coe]
  by_cases hex : ∃ ρ, IsQuotNormaliser H μ ρ
  · obtain ⟨ρ, hρ⟩ := hex
    have hρ' : IsQuotNormaliser H' μ' fun g => ρ (y * g) := ⟨hρ.1.comp (measurable_const_mul y), fun g => by
      rw [← key (fun z => ρ (y * (z * g))) (hρ.1.comp (by fun_prop)), ← hρ.2 (y * g)]
      exact lintegral_congr fun h => by simp [mul_assoc]⟩
    rw [hI G μG hμ H μ s1 i1 F hF hFH ρ hρ, hI G μG hμ H' μ' s2 i2 (fun g => F (y * g)) (hF.comp (measurable_const_mul y)) (fun h hh g => by
      rw [← hFH _ ((hy' h).1 hh) (y * g)]; simp [mul_assoc]) _ hρ']
    exact integral_mul_left_eq_self (fun g => F g * ((ρ g).toReal : ℂ)) y
  · have hex' : ¬ ∃ ρ, IsQuotNormaliser H' μ' ρ := fun ⟨ρ, hρ⟩ => hex ⟨fun g => ρ (y⁻¹ * g), hρ.1.comp (measurable_const_mul _), fun g => by
      rw [← hρ.2 (y⁻¹ * g), ← key (fun z => ρ (z * (y⁻¹ * g))) (hρ.1.comp (by fun_prop))]
      exact lintegral_congr fun h => by simp [mul_assoc]⟩
    rw [quotIntegral, quotIntegral, dite_eq_right hex, dite_eq_right hex']
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotInt
section
open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.quotInt :
    UpperTheory.V.Z.Tf.Orb.QuotMass → UpperTheory.V.Z.Tf.Orb.QuotInt := by
  intro hM G _ _ _ _ _ _ _ _ μG hμ H hH μ hh hi F hF hFH ⟨C, hC, hs⟩ ρ hρ
  obtain ⟨hf, hm⟩ := hM G μG hμ H hH μ hh hi ρ hρ
  obtain ⟨hcl, hfin⟩ := hm C hC
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hF.continuousOn
  have h1 : IntegrableOn (fun g => (ρ g).toReal) {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c} μG :=
    integrable_toReal_of_lintegral_ne_top hρ.1.aemeasurable hfin
  have h2 := ((integrable_indicator_iff hcl.measurableSet).2 h1).const_mul M
  refine h2.mono' (hF.measurable.mul (Complex.measurable_ofReal.comp hρ.1.ennreal_toReal)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => ?_)
  by_cases hg : g ∈ {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c}
  · rw [Set.indicator_of_mem hg, norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    obtain ⟨h, hh, c, hc, rfl⟩ := hg
    rw [hFH h hh]
    exact mul_le_mul_of_nonneg_right (hM c hc) ENNReal.toReal_nonneg
  · have : F g = 0 := by
      by_contra h0
      exact hg (hs g h0)
    simp [this, Set.indicator_of_notMem hg]
end

