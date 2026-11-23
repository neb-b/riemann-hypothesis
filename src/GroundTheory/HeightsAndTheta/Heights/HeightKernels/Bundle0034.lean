module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.Intersections.NotLtLtOfMemMinimalPrimes
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergySymm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace ChartEnergySymmetry

theorem cxHessian_sub {D : ℕ} {f g : (Fin D → ℂ) → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (y : Fin D → ℂ) : cxHessian (fun y' => f y' - g y') y = cxHessian f y - cxHessian g y := by
  have h1 : fderiv ℝ (fun y' => f y' - g y') = fun z => fderiv ℝ f z - fderiv ℝ g z := by
    funext z
    exact fderiv_sub (hf.differentiable (by norm_num) z) (hg.differentiable (by norm_num) z)
  have hf' : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hg' : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ (fun y' => f y' - g y')) y =
      fderiv ℝ (fderiv ℝ f) y - fderiv ℝ (fderiv ℝ g) y := by
    rw [h1]
    exact fderiv_sub (hf' y) (hg' y)
  ext i j
  simp only [cxHessian, h2, _root_.sub_apply, Matrix.sub_apply]
  push_cast
  ring

theorem mixedDisc_update_sub {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (k : Fin D)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (Function.update A k (X - Y)) =
      mixedDisc (Function.update A k X) - mixedDisc (Function.update A k Y) := by
  obtain ⟨M, hM⟩ := (by
    show ∃ F : MultilinearMap (RingHom.id ℂ)
        (fun _ : Fin D => Matrix (Fin D) (Fin D) ℂ) ℂ,
        ⇑F = _root_.ReciprocityTheory.AnForm.mdisc
    refine ⟨MultilinearMap.mk' _root_.ReciprocityTheory.AnForm.mdisc
      _root_.ReciprocityTheory.AnForm.A.mdisc_update_add ?_, rfl⟩
    intro A k c B
    simpa only [RingHom.id_apply, smul_eq_mul] using
      (_root_.ReciprocityTheory.AnForm.A.mdisc_update_smul A k c B))
  have e : ∀ C, mixedDisc (Function.update A k C) = M.toLinearMap A k C := fun C => by
    rw [MultilinearMap.toLinearMap_apply, hM]
    rfl
  simp only [e, map_sub]

theorem maDensity_update_sub {D : ℕ} (Φ : Fin D → (Fin D → ℂ) → ℝ) (p : Fin D) {f g : (Fin D → ℂ) → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (y : Fin D → ℂ) :
    maDensity (Function.update Φ p f) y - maDensity (Function.update Φ p g) y =
      maDensity (Function.update Φ p fun y' => f y' - g y') y := by
  have key : ∀ h : (Fin D → ℂ) → ℝ, (fun k => cxHessian (Function.update Φ p h k) y) =
      Function.update (fun k => cxHessian (Φ k) y) p (cxHessian h y) := fun h => by
    funext k
    exact Function.apply_update (fun _ h' => cxHessian h' y) Φ p h k
  simp only [maDensity, key, cxHessian_sub hf hg y, mixedDisc_update_sub, Complex.sub_re]
  ring

theorem update_comp_swap {α : Type*} {n : ℕ} (Φ : Fin (n + 1) → α) (p : Fin (n + 1)) (f : α) :
    Function.update Φ p f ∘ Equiv.swap 0 p = Fin.cons f (fun i => Φ (Equiv.swap 0 p i.succ)) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · simp only [Function.comp_apply, Fin.cons_succ]
    rw [Function.update_of_ne]
    intro h
    have h' := congrArg (Equiv.swap 0 p) h
    rw [Equiv.swap_apply_self, Equiv.swap_apply_right] at h'
    exact Fin.succ_ne_zero i h'

end ChartEnergySymmetry


open ChartEnergySymmetry in
theorem ChartEnergySymm.proof (hI : ChartIbpSymm.Statement) : ChartEnergySymm.Statement := by
  intro e A B C D T p hA hB hC hD hT
  obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by have := p.pos; omega⟩
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 p with hσ
  set T' : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ := fun i => T (σ i.succ) with hT'def
  have hT' : ∀ i, (T' i).PosDef := fun i => hT _
  have hpot : ∀ X, (fun j => hermChartPot (Function.update T p X j)) =
      Function.update (fun j => hermChartPot (T j)) p (hermChartPot X) := fun X => by
    funext j
    exact Function.apply_update (fun _ M => hermChartPot M) T p X j
  have hdiff : ∀ X Y : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ, X.PosDef → Y.PosDef → ∀ y,
      maDensity (fun j => hermChartPot (Function.update T p X j)) y -
          maDensity (fun j => hermChartPot (Function.update T p Y j)) y =
        maDensity (Fin.cons (fun y' => hermChartPot X y' - hermChartPot Y y')
          fun i => hermChartPot (T' i)) y := by
    intro X Y hX hY y
    rw [hpot, hpot, maDensity_update_sub _ _ (ChartEnergySwapHessian.contDiff_hermChartPot X hX)
      (ChartEnergySwapHessian.contDiff_hermChartPot Y hY), ← Inter.maDensity_comp_perm _ σ, update_comp_swap]
  simp_rw [hdiff C D hC hD, hdiff A B hA hB]
  exact hI n A B C D T' hA hB hC hD hT'

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassLinesProj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace GrassmannianLinesProjective

def single (m : ℕ) (c : Fin (m + 1)) : PlIdx 1 m :=
  ⟨{Fin.cast (Nat.add_comm m 1) c}, Finset.card_singleton _⟩

theorem single_injective (m : ℕ) : Function.Injective (single m) := by
  intro c c' h
  have := congrArg Subtype.val h
  simpa [single] using this

theorem single_surjective (m : ℕ) : Function.Surjective (single m) := by
  rintro ⟨I, hI⟩
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hI
  exact ⟨Fin.cast (Nat.add_comm 1 m) a, Subtype.ext (by simp [single])⟩

def blk : Unit → Fin 1 := fun _ => 0

def coordMap (m : ℕ) : (Σ _ : Unit, Fin (m + 1)) → (Σ _ : Fin 1, PlIdx 1 m) :=
  fun p => ⟨0, single m p.2⟩

theorem coordMap_surjective (m : ℕ) : Function.Surjective (coordMap m) := by
  rintro ⟨k, I⟩
  obtain ⟨c, rfl⟩ := single_surjective m I
  refine ⟨⟨(), c⟩, ?_⟩
  rw [Subsingleton.elim k 0]
  rfl

theorem isBlockMap (m : ℕ) : IsBlockMap blk (coordMap m) := by
  refine ⟨fun _ _ _ => Subsingleton.elim _ _, ?_, fun _ => rfl, fun q _ => coordMap_surjective m q⟩
  rintro ⟨⟨⟩, c⟩ ⟨⟨⟩, c'⟩ h
  simp only [coordMap, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
  rw [single_injective m h]

theorem card_plIdx (m : ℕ) : Fintype.card (PlIdx 1 m) = m + 1 := by
  rw [Fintype.card_subtype, ← Finset.powerset_univ, ← Finset.powersetCard_eq_filter, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, Nat.choose_one_right, add_comm]

theorem ringKrullDim_mring {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] :
    ringKrullDim (MRing ι) = ((1 + Fintype.card (Σ k, ι k) : ℕ) : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField,
    Nat.card_eq_fintype_card]
  push_cast
  rfl

theorem grassIdeal_eq_bot (m : ℕ) : grassIdeal 1 1 m = ⊥ := by
  have hA := GrassArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) 1 1 m le_rfl
  by_contra hne
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hle := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk (grassIdeal 1 1 m))
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_of_ne_zero hx0) (Ideal.Quotient.eq_zero_iff_mem.mpr hx)
  rw [hA.2.2.2, ringKrullDim_mring, Fintype.card_sigma] at hle
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, card_plIdx, smul_eq_mul] at hle
  have h' : ((1 * 1 * m + 1 + 1 + 1 : ℕ) : WithBot ℕ∞) ≤ ((1 + 1 * (m + 1) : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast hle
  have h'' : 1 * 1 * m + 1 + 1 + 1 ≤ 1 + 1 * (m + 1) := by exact_mod_cast h'
  omega

theorem isArithVar_bot (m : ℕ) : IsArithVar (⊥ : Ideal (MRing (PBlk (m + 1)))) (m + 1) := by
  refine ⟨⟨()⟩, ⟨Ideal.isPrime_bot, ⟨∅, by simp, by simp⟩, fun _ => ⟨0, ?_⟩⟩, ?_, ?_⟩
  · rw [Ideal.mem_bot]
    exact X_ne_zero _
  · exact Ideal.comap_bot_of_injective _ (C_injective _ _)
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _), ringKrullDim_mring]
    congr 1
    simp
    omega

theorem isPullHerm (m : ℕ) :
    IsPullHerm blk (coordMap m) (fsMulti (PBlk (m + 1))) (fsMulti (plBlocks 1 1 m)) := by
  refine ⟨?_, fun z => ?_⟩
  · funext k
    rw [Subsingleton.elim k (blk ())]
    show (1 : ℤ) = Function.extend blk (fun _ => (1 : ℤ)) 0 (blk ())
    exact (Function.Injective.extend_apply (f := blk) (fun _ _ _ => Subsingleton.elim _ _)
      (fun _ => (1 : ℤ)) (0 : Fin 1 → ℤ) ()).symm
  · simp only [fsMulti, HermLine.ofMetrics, fsMetric, Fintype.prod_unique, zpow_one, coordMap]
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    exact ((Equiv.ofBijective _ ⟨single_injective m, single_surjective m⟩).sum_comp
      (fun i => ‖z ⟨0, i⟩‖ ^ 2)).symm

theorem blockFnField_le (m : ℕ) :
    blockFnField (grassCoord 1 1 m) ≤ blockFnField (grassCoord 1 1 m ∘ coordMap m) := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro t ⟨p, q, -, rfl⟩
  obtain ⟨p', rfl⟩ := coordMap_surjective m p
  obtain ⟨q', rfl⟩ := coordMap_surjective m q
  exact IntermediateField.subset_adjoin _ _ ⟨p', q', Subsingleton.elim _ _, rfl⟩

end GrassmannianLinesProjective


open GrassmannianLinesProjective in
theorem GrassLinesProj.proof (hPF : PFCoordStatement) : GrassLinesProj.Statement := by
  intro m II hII
  have hd : 1 * 1 * m + 1 = m + 1 := by ring
  have hA : IsArithVar (grassIdeal 1 1 m) (m + 1) := by
    rw [← hd]
    exact GrassArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) 1 1 m le_rfl
  have himg : imageZ (coordMap m) (grassIdeal 1 1 m) = ⊥ := by
    rw [grassIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective _ (rename_injective _ (isBlockMap m).2.1)
  have hB : IsArithVar (imageZ (coordMap m) (grassIdeal 1 1 m)) (m + 1) := by
    rw [himg]
    exact isArithVar_bot m
  have h := hPF II hII Unit (PBlk (m + 1)) (Fin 1) (plBlocks 1 1 m) blk (coordMap m) (GrassField 1 1 m)
    (grassCoord 1 1 m) (m + 1) (fun _ => fsMulti (PBlk (m + 1))) (fun _ => fsMulti (plBlocks 1 1 m))
    (isBlockMap m) hA hB (fun _ => FsLineSmooth.proof _ _) (fun _ => isPullHerm m)
  rw [IntermediateField.relfinrank_eq_one_iff.mpr (blockFnField_le m),
    show mCoordIdeal (grassCoord 1 1 m) = grassIdeal 1 1 m from rfl, himg, Nat.cast_one, one_mul] at h
  rw [hd]
  exact h

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSectionIndexNorm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace SectionIndexNormAlt

variable {T : Type} {K' : Type} [Field K'] {y : (Σ _ : Unit, T) → K'}

theorem ratio_mem (p : Σ _ : Unit, T) (t : T) :
    y p / y ⟨(), t⟩ ∈ chartRingZ y (fun _ => t) :=
  Algebra.subset_adjoin ⟨p, rfl⟩

theorem mem_curveRing_iff {b : K'} :
    b ∈ curveRing y ↔ ∀ t : T, y ⟨(), t⟩ ≠ 0 → b ∈ chartRingZ y (fun _ => t) := by
  rw [mem_curveRing]
  refine ⟨fun h t ht => h (fun _ => t) (fun _ => ht), fun h c hc => ?_⟩
  have hc' : c = fun _ => c () := funext fun u => by cases u; rfl
  rw [hc']
  exact h (c ()) (hc ())

theorem mem_chartLat_iff [Fintype T] {z : K'} :
    z ∈ chartLat y (fun _ => 1) 1 ↔ ∀ t : T, y ⟨(), t⟩ ≠ 0 → z / y ⟨(), t⟩ ∈ chartRingZ y (fun _ => t) := by
  change (∀ c : Unit → T, _ → _) ↔ _
  refine ⟨fun h t ht => ?_, fun h c hc => ?_⟩
  · have := h (fun _ => t) (fun _ => ht)
    simpa [div_eq_mul_inv] using this
  · have hc' : c = fun _ => c () := funext fun u => by cases u; rfl
    rw [hc']
    simpa [div_eq_mul_inv] using h (c ()) (hc ())

theorem aeval_div_mem [Fintype T] {s : MRing (fun _ : Unit => T)} (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s (fun _ => 1))
    (t : T) : aeval y s / y ⟨(), t⟩ ∈ chartRingZ y (fun _ => t) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [s.as_sum, map_sum, Finset.sum_div]
  refine Subalgebra.sum_mem _ fun m hm => ?_
  rw [aeval_monomial, mul_div_assoc]
  refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) ?_
  have hsum : ∑ p, m p = 1 := by
    rw [Fintype.sum_sigma, Fintype.sum_unique]
    exact hs m hm ()
  have key : m.prod (fun p e => y p ^ e) / y ⟨(), t⟩ = ∏ p, (y p / y ⟨(), t⟩) ^ m p := by
    rw [Finsupp.prod_fintype _ _ (by simp)]
    simp only [div_pow]
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hsum, pow_one]
  rw [key]
  exact Subalgebra.prod_mem _ fun p _ => Subalgebra.pow_mem _ (ratio_mem p t) _

theorem exists_mul_mem {m : Ideal (curveRing y)} (hm : m.IsPrime) {t : T}
    (ht : ∀ u, ∃ a b : curveRing y, b ∉ m ∧ (b : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a) {z : K'}
    (hz : z ∈ chartRingZ y (fun _ => t)) : ∃ b : curveRing y, b ∉ m ∧ (b : K') * z ∈ curveRing y := by
  have h1 : (1 : curveRing y) ∉ m := fun h => hm.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨⟨⟩, u⟩, rfl⟩ := hx
    obtain ⟨a, b, hb, hab⟩ := ht u
    exact ⟨b, hb, by convert a.2 using 1⟩
  | algebraMap r =>
    exact ⟨1, h1, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨b1, hb1, h1'⟩ := hx
    obtain ⟨b2, hb2, h2'⟩ := hz
    refine ⟨b1 * b2, fun h => (hm.mem_or_mem h).elim hb1 hb2, ?_⟩
    have e : ((b1 * b2 : curveRing y) : K') * (x + z) = b2 * (b1 * x) + b1 * (b2 * z) := by
      push_cast; ring
    rw [e]
    exact add_mem (mul_mem b2.2 h1') (mul_mem b1.2 h2')
  | mul x z _ _ hx hz =>
    obtain ⟨b1, hb1, h1'⟩ := hx
    obtain ⟨b2, hb2, h2'⟩ := hz
    refine ⟨b1 * b2, fun h => (hm.mem_or_mem h).elim hb1 hb2, ?_⟩
    have e : ((b1 * b2 : curveRing y) : K') * (x * z) = (b1 * x) * (b2 * z) := by
      push_cast; ring
    rw [e]
    exact mul_mem h1' h2'

theorem coe_ne_zero_of_notMem {m : Ideal (curveRing y)} {b : curveRing y} (hb : b ∉ m) : (b : K') ≠ 0 :=
  fun h => hb (by rw [show b = 0 from Subtype.ext h]; exact m.zero_mem)

theorem genIndex_span_div [NumberField K'] [Fintype T] (hy : y ≠ 0) {x : K'} (hx : x ≠ 0) :
    genIndex (Submodule.span (𝓞 K') (Set.range fun p => y p / x)).toAddSubgroup
        (1 : Submodule (𝓞 K') K').toAddSubgroup =
      genIndex (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup (1 : Submodule (𝓞 K') K').toAddSubgroup *
        |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  have hy' : (fun p => y p / x) ≠ 0 := by
    obtain ⟨p, hp⟩ := Function.ne_iff.mp hy
    exact Function.ne_iff.mpr ⟨p, div_ne_zero hp hx⟩
  rw [DualLineIndexAlt.genIndex_span_eq_finprod hy', DualLineIndexAlt.genIndex_span_eq_finprod hy]
  have e : ∀ w : FinitePlace K', ⨆ p, w (y p / x) = (⨆ p, w (y p)) * w x⁻¹ := by
    intro w
    simp only [div_eq_mul_inv, map_mul]
    exact (Real.iSup_mul_of_nonneg (apply_nonneg w _) _).symm
  simp_rw [e]
  rw [finprod_mul_distrib (hasFiniteMulSupport_iSup_place hy)
    (FinitePlace.hasFiniteMulSupport (inv_ne_zero hx)), FinitePlace.prod_eq_inv_abs_norm (inv_ne_zero hx)]
  have hN : Algebra.norm ℚ x⁻¹ = (Algebra.norm ℚ x)⁻¹ :=
    eq_inv_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel₀ hx, map_one])
  rw [hN]
  push_cast
  rw [abs_inv, inv_inv]

theorem genIndex_span_pos [NumberField K'] [Fintype T] {p0 : Σ _ : Unit, T} (hp0 : y p0 ≠ 0) :
    0 < genIndex (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup
      (1 : Submodule (𝓞 K') K').toAddSubgroup := by
  have hy : y ≠ 0 := fun h => hp0 (by rw [h, Pi.zero_apply])
  rw [DualLineIndexAlt.genIndex_span_eq_finprod hy,
    finprod_eq_prod _ (hasFiniteMulSupport_iSup_place hy)]
  refine Finset.prod_pos fun w _ => ?_
  exact lt_of_lt_of_le (FinitePlace.pos_iff.mpr hp0) (le_ciSup (f := fun p => w (y p)) (Finite.bddAbove_range _) p0)

end SectionIndexNormAlt


open SectionIndexNormAlt in
theorem SectionIndexNorm.proof (hC : CurveCharts.Statement) (hI : InvertibleIdealIndex.Statement) :
    SectionIndexNorm.Statement := by
  intro T _ K' _ _ y s hP hs hsP
  obtain ⟨hfin, hrank, hloc⟩ := hC T K' y hP
  set x := aeval y s with hxdef
  have hx0 : x ≠ 0 := by
    intro h0
    apply hsP
    change s ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker]
    erw [HilbertSamuel.SectionBounded.mConeMap_homog y hs]
    rw [← hxdef, h0, map_zero, zero_mul]
  obtain ⟨m0, hm0⟩ := Ideal.exists_maximal (curveRing y)
  obtain ⟨t1, ht1, hl1⟩ := hloc m0 hm0
  let f : K' →+ K' := AddMonoidHom.mulLeft x⁻¹
  have hf : ∀ z, f z = x⁻¹ * z := fun _ => rfl
  let a : (Σ _ : Unit, T) → K' := fun p => y p / x
  have key := hI K' (curveRing y) ((chartLat y (fun _ => 1) 1).map f) (Σ _ : Unit, T) a hfin ?_ ?_ ?_ ?_
  ·
    have hB : (curveRing y).toAddSubgroup = (curveMul y x).map f := by
      rw [curveMul, AddSubgroup.map_map]
      ext z
      simp [hf, hx0]
    have hinj : Function.Injective f := fun u v h => mul_left_cancel₀ (inv_ne_zero hx0) h
    rw [hB, KLinesLineDegree.genIndex_map_of_injective f hinj, genIndex_span_div ?_ hx0,
      Real.log_mul (genIndex_span_pos (p0 := ⟨(), t1⟩) ht1).ne'
        (abs_pos.mpr (by exact_mod_cast Algebra.norm_ne_zero_iff.mpr hx0)).ne',
      hrank, ← (letI : Module.Free (blockFnField y) K' := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (blockFnField y) K')] at key
    · have hF : (0 : ℝ) < Module.finrank ℚ (blockFnField y) := Nat.cast_pos.mpr Module.finrank_pos
      apply mul_left_cancel₀ hF.ne'
      push_cast at key
      linear_combination key
    · exact fun h => ht1 (by rw [h, Pi.zero_apply])
  ·
    intro b hb z hz
    obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.mp hz
    refine AddSubgroup.mem_map.mpr ⟨b * w, ?_, by rw [hf, hf]; ring⟩
    rw [mem_chartLat_iff] at hw ⊢
    intro t ht
    rw [mul_div_assoc]
    exact mul_mem (mem_curveRing_iff.mp hb t ht) (hw t ht)
  ·
    intro p
    refine AddSubgroup.mem_map.mpr ⟨y p, ?_, by rw [hf]; simp [a, div_eq_inv_mul]⟩
    exact mem_chartLat_iff.mpr fun t _ => ratio_mem p t
  ·
    rintro ⟨⟨⟩, u⟩
    obtain ⟨β, hβ, hβx⟩ := exists_mul_mem hm0.isPrime hl1 (aeval_div_mem hs t1)
    obtain ⟨c, b, hb, hbc⟩ := hl1 u
    refine ⟨(β : K') * (x / y ⟨(), t1⟩) * b, mul_mem hβx b.2, ?_, ?_⟩
    · exact mul_ne_zero (mul_ne_zero (coe_ne_zero_of_notMem hβ) (div_ne_zero hx0 ht1))
        (coe_ne_zero_of_notMem hb)
    · have e : (β : K') * (x / y ⟨(), t1⟩) * b * a ⟨(), u⟩ = β * c := by
        rw [← hbc]
        simp only [a]
        field_simp
      rw [e]
      exact mul_mem β.2 c.2
  ·
    intro m hm
    obtain ⟨t, ht, hl⟩ := hloc m hm
    refine ⟨⟨(), t⟩, fun z hz => ?_⟩
    obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.mp hz
    obtain ⟨b, hb, hbw⟩ := exists_mul_mem hm.isPrime hl (mem_chartLat_iff.mp hw t ht)
    refine ⟨b, ⟨_, hbw⟩, hb, ?_⟩
    simp only [hf, a]
    field_simp

end

end GroundTheory.Heights₂.Heights
end

