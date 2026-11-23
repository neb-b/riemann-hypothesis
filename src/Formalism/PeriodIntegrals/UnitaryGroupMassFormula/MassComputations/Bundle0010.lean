module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0004
public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ContinuousCrdAllSymm
section
noncomputable section

namespace MassDataMassesW.KCptW

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures MeasureTheory NumberField IsDedekindDomain
  Topology PI.AdicCompletionValuation MassDataLevelSSteps.LatTop MassDataLevelSSteps Matrix

section Hat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [FiniteDimensional F E] {n : ℕ}

def crdAll : (Fin n → Af F ⊗[F] E) ≃ₗ[Af F] (Fin n → Fin (Module.finrank F E) → Af F) :=
  LinearEquiv.piCongrRight fun _ => (Algebra.TensorProduct.basis (Af F) (Module.finBasis F E)).equivFun

theorem continuous_crdAll : Continuous (crdAll (F := F) (E := E) (n := n)) := by
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  have h := IsModuleTopology.continuous_of_linearMap (R := Af F)
    (crdAll (F := F) (E := E) (n := n)).toLinearMap
  exact h

theorem continuous_crdAll_symm : Continuous (crdAll (F := F) (E := E) (n := n)).symm := by
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  have h := IsModuleTopology.continuous_of_linearMap (R := Af F)
    (crdAll (F := F) (E := E) (n := n)).symm.toLinearMap
  exact h

theorem ratV_single (v : HeightOneSpectrum (𝓞 F)) (i : Fin n) (e : E) :
    ratV (F := F) (Fv F v) (Pi.single i e) = Pi.single i ((1 : Fv F v) ⊗ₜ[F] e) := by
  funext j
  unfold ratV
  rcases eq_or_ne j i with rfl | h
  · simp [inclR]
  · simp [h, inclR]

theorem single_mem_Bint (i : Fin n) (k : Fin (Module.finrank F E)) :
    (Pi.single i (Module.finBasis F E k) : Fin n → E) ∈ Bint (F := F) n := by
  unfold Bint
  rw [Set.mem_setOf_eq]
  intro i' k'
  rcases eq_or_ne i' i with rfl | h
  · rw [Pi.single_eq_same, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  · rw [Pi.single_eq_of_ne h, map_zero, Finsupp.zero_apply]
    exact isIntegral_zero

theorem mem_latHat_Bint_iff (x : Fin n → Af F ⊗[F] E) :
    x ∈ latHat (F := F) (Bint (F := F) (E := E) n) ↔ ∀ i k, crd (Af F) (x i) k ∈ Ohat F := by
  constructor
  · intro hx i k v
    have h := crd_mem_of_latLoc v (hx v) i k
    simp only [pv, crd_tens] at h
    exact h
  · intro hx v
    set Btv := Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)
    have hc : ∀ i k, crd (Fv F v) (pv v x i) k ∈ v.adicCompletionIntegers F := by
      intro i k
      simp only [pv, crd_tens]
      exact hx i k v
    rw [← Finset.univ_sum_single (pv v x)]
    refine Submodule.sum_mem _ fun i _ => ?_
    have e1 : pv v x i = ∑ k, crd (Fv F v) (pv v x i) k • Btv k := (Btv.sum_equivFun (pv v x i)).symm
    have e2 : (Pi.single i (pv v x i) : Fin n → Fv F v ⊗[F] E) =
        ∑ k, crd (Fv F v) (pv v x i) k • (Pi.single i (Btv k) : Fin n → Fv F v ⊗[F] E) := by
      conv_lhs => rw [e1]
      funext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [e2]
    refine Submodule.sum_mem _ fun k _ => ?_
    have hm : (Pi.single i (Btv k) : Fin n → Fv F v ⊗[F] E) ∈ latLoc (E := E) v (Bint (F := F) n) := by
      refine Submodule.subset_span ⟨Pi.single i (Module.finBasis F E k), single_mem_Bint i k, ?_⟩
      rw [ratV_single, Algebra.TensorProduct.basis_apply]
    have e3 : crd (Fv F v) (pv v x i) k • (Pi.single i (Btv k) : Fin n → Fv F v ⊗[F] E) =
        (⟨_, hc i k⟩ : v.adicCompletionIntegers F) • (Pi.single i (Btv k) : Fin n → Fv F v ⊗[F] E) := rfl
    rw [e3]
    exact Submodule.smul_mem _ _ hm

theorem latHat_Bint_eq : latHat (F := F) (Bint (F := F) (E := E) n) =
    (crdAll (F := F) (E := E) (n := n)) ⁻¹' (Set.univ.pi fun _ => Set.univ.pi fun _ => Ohat F) := by
  ext x
  rw [mem_latHat_Bint_iff]
  simp only [Set.mem_preimage, Set.mem_univ_pi]
  rfl

theorem isOpen_latHat_Bint : IsOpen (latHat (F := F) (Bint (F := F) (E := E) n)) := by
  rw [latHat_Bint_eq]
  exact (isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ohat F).preimage continuous_crdAll

theorem isCompact_latHat_Bint : IsCompact (latHat (F := F) (Bint (F := F) (E := E) n)) := by
  rw [latHat_Bint_eq, ← LinearEquiv.image_symm_eq_preimage]
  exact (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Ohat F).image continuous_crdAll_symm

theorem mem_std_iff (μ : Fin n → E) :
    μ ∈ (stdSub : Submodule (𝓞 E) (Fin n → E)) ↔ ∀ i, IsIntegral ℤ (μ i) := by
  unfold stdSub
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range, Algebra.linearMap_apply]
  refine forall_congr' fun i => ⟨?_, fun h => ⟨⟨μ i, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]
  exact NumberField.RingOfIntegers.isIntegral_coe y

theorem exists_bint_to_std : ∃ N : ℤ, N ≠ 0 ∧ ∀ μ ∈ Bint (F := F) (E := E) n,
    N • μ ∈ ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  classical
  set b := Module.finBasis F E
  obtain ⟨N, hN0, hN⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image b)
  refine ⟨N, hN0, fun μ hμ => (mem_std_iff _).2 fun i => ?_⟩
  have hb : ∀ k, IsIntegral ℤ (N • b k) := fun k => hN _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  have e : (N • μ) i = ∑ k, algebraMap F E (b.repr (μ i) k) * (N • b k) := by
    rw [Pi.smul_apply]
    conv_lhs => rw [← b.sum_repr (μ i)]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_comm, Algebra.smul_def]
  rw [e]
  exact IsIntegral.sum _ fun k _ => ((hμ i k).algebraMap).mul (hb k)

theorem exists_std_to_bint : ∃ M : ℤ, M ≠ 0 ∧ ∀ μ ∈ ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)),
    M • μ ∈ Bint (F := F) (E := E) n := by
  classical
  set b := Module.finBasis F E
  set β := RingOfIntegers.basis E
  obtain ⟨M, hM0, hM⟩ := exists_integral_multiples ℤ ℚ (L := F)
    (Finset.univ.image fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin (Module.finrank F E) =>
      b.repr (algebraMap (𝓞 E) E (β p.1)) p.2)
  refine ⟨M, hM0, fun μ hμ i k => ?_⟩
  obtain ⟨a, ha⟩ := LinearMap.mem_range.1 ((Submodule.mem_pi.1 hμ) i (Set.mem_univ _))
  rw [Algebra.linearMap_apply] at ha
  have e : b.repr ((M • μ) i) k =
      ∑ j, (β.repr a j) • (M • b.repr (algebraMap (𝓞 E) E (β j)) k) := by
    rw [Pi.smul_apply, ← ha]
    conv_lhs => rw [← β.sum_repr a]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm]
  rw [e]
  refine IsIntegral.sum _ fun j _ => ?_
  have h := hM _ (Finset.mem_image_of_mem _ (Finset.mem_univ (j, k)))
  have h2 : (β.repr a j) • (M • b.repr (algebraMap (𝓞 E) E (β j)) k) =
      ((β.repr a j : ℤ) : F) * (M • b.repr (algebraMap (𝓞 E) E (β j)) k) := by
    rw [zsmul_eq_mul]
  rw [h2]
  have hc : IsIntegral ℤ ((β.repr a j : ℤ) : F) := by
    rw [← eq_intCast (algebraMap ℤ F)]; exact isIntegral_algebraMap
  exact hc.mul h

end Hat

theorem stdHatOpen_holds : StdHatOpen := by
  intro F E _ _ _ _ _ n
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨N, hN0, hN⟩ := exists_bint_to_std (F := F) (E := E) (n := n)
  have hNF : (N : F) ≠ 0 := Int.cast_ne_zero.mpr hN0
  let G : AddSubgroup (Fin n → Af F ⊗[F] E) :=
    { carrier := latHat (F := F) ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E))
      add_mem' := fun {x y} hx hy v => by rw [pv_add]; exact add_mem (hx v) (hy v)
      zero_mem' := fun v => by rw [pv_zero]; exact zero_mem _
      neg_mem' := fun {x} hx v => by rw [pv_neg]; exact neg_mem (hx v) }
  let W : Set (Fin n → Af F ⊗[F] E) := {x | (N : F)⁻¹ • x ∈ latHat (F := F) (Bint (F := F) (E := E) n)}
  have hWo : IsOpen W := (isOpen_latHat_Bint (F := F) (E := E) (n := n)).preimage (continuous_const_smul _)
  have hW0 : (0 : Fin n → Af F ⊗[F] E) ∈ W := by
    show (N : F)⁻¹ • (0 : Fin n → Af F ⊗[F] E) ∈ latHat (F := F) _
    rw [smul_zero]
    intro v
    rw [pv_zero]
    exact zero_mem _
  have hWG : W ⊆ (G : Set (Fin n → Af F ⊗[F] E)) := by
    intro x hx
    have h := zsmul_mem_latHat _ _ N hN hx
    rwa [zsmul_eq_cast_smul, smul_smul, mul_inv_cancel₀ hNF, one_smul] at h
  exact G.isOpen_of_mem_nhds (Filter.mem_of_superset (hWo.mem_nhds hW0) hWG)

theorem stdHatCompact_holds : StdHatCompact := by
  intro F E _ _ _ _ _ n
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨N, hN0, hN⟩ := exists_std_to_bint (F := F) (E := E) (n := n)
  have hNF : (N : F) ≠ 0 := Int.cast_ne_zero.mpr hN0
  set L : Submodule (𝓞 E) (Fin n → E) := stdSub
  have hcl : IsClosed (latHat (F := F) (L : Set (Fin n → E))) := by
    have e : latHat (F := F) (L : Set (Fin n → E)) =
        ⋂ v, pv v ⁻¹' (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) := by
      ext x
      simp [latHat]
    rw [e]
    exact isClosed_iInter fun v => (((latLoc (E := E) v (L : Set (Fin n → E))).toAddSubgroup.isClosed_of_isOpen
      (isOpen_latLoc v L span_std))).preimage (continuous_pv v)
  refine ((isCompact_latHat_Bint (F := F) (E := E) (n := n)).image
    (continuous_const_smul ((N : F)⁻¹))).of_isClosed_subset hcl ?_
  intro x hx
  refine ⟨N • x, zsmul_mem_latHat _ _ N hN hx, ?_⟩
  show (N : F)⁻¹ • (N • x) = x
  rw [zsmul_eq_cast_smul, smul_smul, inv_mul_cancel₀ hNF, one_smul]

end MassDataMassesW.KCptW

namespace MassDataMassesW

end MassDataMassesW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.MassHNonneg
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets
open scoped TensorProduct

namespace MassDataMassesW

theorem massH_nonneg {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    0 ≤ massH X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (frameOf X u) :=
  finsum_nonneg fun _ => inv_nonneg.2 (Nat.cast_nonneg _)

theorem massAll_of (hH : HinfCompact) (hK : KCompactOpen) (hC : ClassFinite) : MassAll := by
  intro D X hb u hT
  have : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  have hN := X.measW_norm u
  have hcs := hH X u
  have hfin : MassFinite (G := ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) (GamH X u) (KH X u) :=
    ⟨hC X u, stabFinite_of hH hK X u⟩
  obtain ⟨𝓕, h𝓕⟩ := fdExistsH_holds X u
  have hKU : MeasurableSet ((KH X u : Subgroup ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) :
      Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) :=
    ((hK X).2.preimage continuous_subtype_val).measurableSet
  have hU := massUnfold_gen X.B.I.cm.sig X.B.I.J (frameOf X u) (isCMExt_of_cmData X.B.I.cm)
    (isHermND_of_setting X) (X.measW u) hN (KH X u) hKU hfin 𝓕 h𝓕
  have hcov : covol (X.measW u).μH = ((X.measW u).μH 𝓕).toReal :=
    covol_eq_of_fd X.B.I.cm.sig X.B.I.J _ (X.measW u).μH hN.1.toIsMulLeftInvariant 𝓕 h𝓕
  have hV : X.muH u Set.univ = (X.measW u).μHinf Set.univ := by
    have h := (hT.2.2.2 u).2
    have h1 := congrArg (fun m => m Set.univ) h
    have hm : Measurable (X.toInf hb) := by
      haveI : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
      unfold Formalism.L2.SG.HidaSetting.HidaSetting.toInf
      exact (continuous_fst.comp ((continuous_splitA _ _).comp
        ((Formalism.L2.SG.AdBridge.toHA X.B.I hb).continuous.comp (continuous_id.prodMk continuous_const)))).measurable
    rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ] at h1
    rw [← h1]
    unfold Formalism.L2.SG.Measures.amb
    rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Set.preimage_univ]

  have h1 := hN.2.1
  have h2 := hN.2.2.1
  have ha0 : (X.measW u).μHinf Set.univ ≠ 0 :=
    (isOpen_univ.measure_pos _ Set.univ_nonempty).ne'
  have haT : (X.measW u).μHinf Set.univ ≠ ⊤ :=
    (h1.toIsFiniteMeasureOnCompacts.lt_top_of_isCompact (@isCompact_univ _ _ (hH X u))).ne
  have hKo : IsOpen (Subtype.val ⁻¹' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) :
      Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) :=
    (hK X).2.preimage continuous_subtype_val
  have hb0 : (X.measW u).μHf (Subtype.val ⁻¹' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))) ≠ 0 :=
    h2.toIsOpenPosMeasure.open_pos _ hKo ⟨1, (KX X).one_mem⟩
  have hcl : IsClosed ((Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) :
      Subgroup (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) :=
    isClosed_stabT' X.B.I.cm.sig X.B.I.J (Af X.B.I.F) (tupH (frameOf X u))
  have hbT : (X.measW u).μHf (Subtype.val ⁻¹' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))) ≠ ⊤ :=
    (h2.toIsFiniteMeasureOnCompacts.lt_top_of_isCompact
      (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage (hK X).1)).ne
  have ha : 0 < ((X.measW u).μHinf Set.univ).toReal := ENNReal.toReal_pos ha0 haT
  have hb' : 0 < ((X.measW u).μHf (Subtype.val ⁻¹' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal :=
    ENNReal.toReal_pos hb0 hbT
  unfold MassAt
  rw [hcov]
  unfold frameOf at hU ⊢
  rw [hU, hV, ENNReal.toReal_mul, ENNReal.toReal_mul]
  change massH _ _ _ (frameOf X u) =
    ((X.measW u).μHinf Set.univ).toReal *
      ((X.measW u).μHf (Subtype.val ⁻¹' (KX X : Set _))).toReal *
      (ENNReal.ofReal (massH _ _ _ (frameOf X u))).toReal / _
  rw [ENNReal.toReal_ofReal (massH_nonneg X u)]
  field_simp

end MassDataMassesW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.UnipotentFundamentalDomain
section
noncomputable section

open MeasureTheory NumberField Set
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets
open scoped TensorProduct

namespace MassDataMassesW

section Bridge

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

def evInf (v : InfinitePlace X.B.I.F) : Ainf X.B.I.F →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding v).comp
    (Pi.evalRingHom (fun w : InfinitePlace X.B.I.F => w.Completion) v)

def thetaInf (v : InfinitePlace X.B.I.F) : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E →+* ℂ :=
  letI : Algebra X.B.I.F ℂ := v.embedding.toAlgebra
  (Algebra.TensorProduct.lift
    ({ evInf X v with commutes' := fun a => evV_algebraMap X.B.I v a } : Ainf X.B.I.F →ₐ[X.B.I.F] ℂ)
    ({ X.B.I.φ v with commutes' := X.B.I.φ_over v } : X.B.I.E →ₐ[X.B.I.F] ℂ)
    (fun _ _ => Commute.all _ _)).toRingHom

theorem thetaV_eq (v : InfinitePlace X.B.I.F) (y : AF X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    thetaV X.B.I v y = thetaInf X v (tensMap (E := X.B.I.E) (fstA X.B.I.F) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [thetaV_tmul]
    simp only [thetaInf, tensMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.lift_tmul, AlgHom.id_apply]
    rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem ofHAInf_congr (a b : HAd X.B.I)
    (h : (splitA X.B.I.cm.sig X.B.I.J a).1 = (splitA X.B.I.cm.sig X.B.I.J b).1) :
    ofHAInf X.B.I a = ofHAInf X.B.I b := by
  funext v
  unfold ofHAInf
  congr 2
  ext i j
  simp only [Matrix.map_apply, thetaV_eq]
  have := congrArg (fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J =>
    (HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g).val i j) h
  exact congrArg (thetaInf X v) this

theorem ofHAFin_congr (a b : HAd X.B.I)
    (h : (splitA X.B.I.cm.sig X.B.I.J a).2 = (splitA X.B.I.cm.sig X.B.I.J b).2) :
    ofHAFin X.B.I a = ofHAFin X.B.I b := by
  unfold ofHAFin
  ext i j
  simp only [Matrix.map_apply, tauF_eq_comm]
  have := congrArg (fun g : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J =>
    (HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J g).val i j) h
  exact congrArg (Algebra.TensorProduct.comm X.B.I.F (Af X.B.I.F) X.B.I.E) this

theorem eq_of_ofHA (p q : X.B.I.GA) (h1 : ofHAInf X.B.I (toHA X.B.I hb p) = ofHAInf X.B.I (toHA X.B.I hb q))
    (h2 : ofHAFin X.B.I (toHA X.B.I hb p) = ofHAFin X.B.I (toHA X.B.I hb q)) : p = q := by
  obtain ⟨a₁, b₁⟩ := (toHA_isBridge X.B.I hb) p
  obtain ⟨a₂, b₂⟩ := (toHA_isBridge X.B.I hb) q
  refine Prod.ext (funext fun v => ?_) ?_
  · exact Subtype.ext (Units.ext ((a₁ v).trans ((congrFun h1 v).trans (a₂ v).symm)))
  · exact Subtype.ext (Units.ext (b₁.trans (h2.trans b₂.symm)))

theorem toInf_mul (s t : X.B.I.Ginf) : X.toInf hb (s * t) = X.toInf hb s * X.toInf hb t := by
  unfold HidaSetting.toInf
  rw [show ((s * t, 1) : X.B.I.GA) = (s, 1) * (t, 1) by simp, map_mul, map_mul]
  rfl

theorem toHA_inf_one (hS : SplitIso) (x : X.B.I.Gf) :
    (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (1, x))).1 = 1 := by
  obtain ⟨e, he⟩ := hS X.B.I.cm.sig X.B.I.J
  set h := toHA X.B.I hb (1, x) with hh
  set h' := e.symm (1, (splitA X.B.I.cm.sig X.B.I.J h).2) with hh'
  have hs' : splitA X.B.I.cm.sig X.B.I.J h' = (1, (splitA X.B.I.cm.sig X.B.I.J h).2) := by
    have h0 := e.apply_symm_apply (1, (splitA X.B.I.cm.sig X.B.I.J h).2)
    rw [he] at h0
    exact h0
  set q := (toHA X.B.I hb).symm h' with hq
  have hqh : toHA X.B.I hb q = h' := (toHA X.B.I hb).apply_symm_apply h'
  have h1 : ofHAInf X.B.I (toHA X.B.I hb q) = ofHAInf X.B.I (toHA X.B.I hb (1, 1)) := by
    rw [hqh]
    apply ofHAInf_congr
    rw [hs', show ((1, 1) : X.B.I.GA) = 1 from rfl, map_one, map_one]
    rfl
  have h1' : ofHAInf X.B.I (toHA X.B.I hb (1, 1)) = ofHAInf X.B.I (toHA X.B.I hb (1, x)) := by
    obtain ⟨a₁, -⟩ := (toHA_isBridge X.B.I hb) (1, 1)
    obtain ⟨a₂, -⟩ := (toHA_isBridge X.B.I hb) (1, x)
    funext v
    exact (a₁ v).symm.trans (a₂ v)
  have h2 : ofHAFin X.B.I (toHA X.B.I hb q) = ofHAFin X.B.I (toHA X.B.I hb (1, x)) := by
    rw [hqh]
    apply ofHAFin_congr
    rw [hs']
  have hq1 : q = (1, x) := eq_of_ofHA X hb q (1, x) (h1.trans h1') h2
  have : h' = h := by rw [← hqh, hq1]
  rw [← this, hs']

theorem split_toHA (hS : SplitIso) (p : X.B.I.GA) :
    splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb p) = (X.toInf hb p.1, finHA X hb p.2) := by
  have e : p = (p.1, 1) * (1, p.2) := by simp
  conv_lhs => rw [e, map_mul, map_mul]
  refine Prod.ext ?_ ?_
  · show X.toInf hb p.1 * (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (1, p.2))).1 = _
    rw [toHA_inf_one X hb hS, mul_one]
  · show (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (p.1, 1))).2 * finHA X hb p.2 = _
    rw [toHA_fin_one X hb, one_mul]

theorem toInf_surjective (hS : SplitIso) : Function.Surjective (X.toInf hb) := by
  intro y
  obtain ⟨e, he⟩ := hS X.B.I.cm.sig X.B.I.J
  set p := (toHA X.B.I hb).symm (e.symm (y, 1))
  have hp : splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb p) = (y, 1) := by
    rw [← he]
    simp [p]
  have h2 : p.2 = 1 := eq_one_of_toHA_fin X hb p (by rw [hp])
  refine ⟨p.1, ?_⟩
  have := congrArg Prod.fst hp
  rw [split_toHA X hb hS] at this
  exact this

end Bridge

end MassDataMassesW
end
end

