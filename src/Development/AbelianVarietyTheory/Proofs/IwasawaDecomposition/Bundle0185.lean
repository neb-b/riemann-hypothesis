module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductMeasureBasicProperties
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.ProdBasic

theorem repr_map {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') {d : ℕ} (b : Module.Basis (Fin d) F E)
    (z : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) z) k =
      f ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul]
  | add x y hx hy => simp [hx, hy]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {n M : ℕ}

def box (S : Finset (HeightOneSpectrum (𝓞 F))) : Set (Fin n → Fin M → AF F ⊗[F] E) :=
  {X | ∀ v ∉ S, projV v (projFin X) ∈ latV b v}

theorem isOpen_box (S : Finset (HeightOneSpectrum (𝓞 F))) : IsOpen (box (n := n) (M := M) b S) := by
  have h : box (n := n) (M := M) b S = ⋂ a, ⋂ i, ⋂ k,
      (fun X : Fin n → Fin M → AF F ⊗[F] E =>
        ((Algebra.TensorProduct.basis (AF F) b).coord k (X a i)).2) ⁻¹'
        {x : Af F | ∀ v, v ∉ S → x.1 v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))} := by
    ext X
    simp only [box, latV, projV, projFin, repr_map, Set.mem_setOf_eq, Set.mem_iInter,
      Set.mem_preimage]
    exact ⟨fun h a i k v hv => h v hv a i k, fun h v hv a i k => h a i k v hv⟩
  rw [h]
  refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i =>
    isOpen_iInter_of_finite fun k => IsOpen.preimage ?_ ?_
  · have h1 : Continuous ((Algebra.TensorProduct.basis (AF F) b).coord k) :=
      IsModuleTopology.continuous_of_linearMap _
    exact continuous_snd.comp (h1.comp ((continuous_apply i).comp (continuous_apply a)))
  · exact RestrictedProduct.isOpen_forall_imp_mem
      (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun _ => Valued.isOpen_valuationSubring _)

theorem box_mono {S T : Finset (HeightOneSpectrum (𝓞 F))} (h : S ⊆ T) :
    box (n := n) (M := M) b S ⊆ box b T := fun _ hX v hv => hX v fun hs => hv (h hs)

theorem exists_mem_box (X : Fin n → Fin M → AF F ⊗[F] E) : ∃ S, X ∈ box b S := by
  have h := (GlobalTheory.GaugeGlue.adelicTuple_measurableEmbedding F E d b n M).2.1
  have hX : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, projV v (projFin X) ∈ latV b v := by
    have h1 := Set.mem_range_self (f := fun X : Fin n → Fin M → AF F ⊗[F] E =>
      (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) X
    rw [h, Set.mem_setOf_eq] at h1
    exact h1
  have hf := Filter.eventually_cofinite.1 hX
  refine ⟨hf.toFinset, fun v hv => ?_⟩
  by_contra h'
  exact hv (by simpa using h')

variable {b} {ν : Measure (Fin n → Fin M → AF F ⊗[F] E)}
  {mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)}
  {mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)}

theorem measure_rect (h : IsProd b ν mi mv) (S : Finset (HeightOneSpectrum (𝓞 F)))
    {Ai : Set (Fin n → Fin M → Ainf F ⊗[F] E)}
    {Av : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)}
    (hi : MeasurableSet Ai) (hv : ∀ v, MeasurableSet (Av v)) :
    ν ({X | projInf X ∈ Ai ∧ ∀ v ∈ S, projV v (projFin X) ∈ Av v} ∩ box b S) =
      mi Ai * (∏ v ∈ S, mv v (Av v)) * tailProd b mv S := by
  have hm := (GlobalTheory.GaugeGlue.adelicTuple_measurableEmbedding F E d b n M).1.measurable
  have hmi : Measurable (projInf (F := F) (E := E) (M := M) (n := n)) := measurable_fst.comp hm
  have hmv : ∀ v : HeightOneSpectrum (𝓞 F),
      Measurable fun X : Fin n → Fin M → AF F ⊗[F] E => projV v (projFin X) := fun v =>
    (measurable_pi_apply v).comp (measurable_snd.comp hm)
  have hR : MeasurableSet {X : Fin n → Fin M → AF F ⊗[F] E |
      projInf X ∈ Ai ∧ ∀ v ∈ S, projV v (projFin X) ∈ Av v} := by
    have : {X : Fin n → Fin M → AF F ⊗[F] E |
      projInf X ∈ Ai ∧ ∀ v ∈ S, projV v (projFin X) ∈ Av v} =
        projInf ⁻¹' Ai ∩ ⋂ v ∈ S, (fun X => projV v (projFin X)) ⁻¹' Av v := by
      ext X; simp
    rw [this]
    exact (hmi hi).inter (S.measurableSet_biInter fun v _ => hmv v (hv v))
  have key := h.2 S (Ai.indicator 1) (fun v => (Av v).indicator 1)
    (measurable_const.indicator hi) (fun v => measurable_const.indicator (hv v))
  simp only [lintegral_indicator_one hi, lintegral_indicator_one (hv _)] at key
  rw [← key, ← Measure.restrict_apply hR, ← lintegral_indicator_one hR]
  refine lintegral_congr fun X => ?_
  by_cases hX : projInf X ∈ Ai ∧ ∀ v ∈ S, projV v (projFin X) ∈ Av v
  · rw [Set.indicator_of_mem (by exact hX), Set.indicator_of_mem hX.1,
      Finset.prod_eq_one fun v hv => Set.indicator_of_mem (hX.2 v hv) _]
    simp
  · rw [Set.indicator_of_notMem (by exact hX)]
    rcases not_and_or.1 hX with h1 | h1
    · rw [Set.indicator_of_notMem h1, zero_mul]
    · push Not at h1
      obtain ⟨v, hv, h1⟩ := h1
      rw [Finset.prod_eq_zero hv (Set.indicator_of_notMem h1 _), mul_zero]

theorem exists_tailProd_ne_zero (h : Conv b mi mv) : ∃ S, tailProd b mv S ≠ 0 := by
  have hs := h.2.2
  have ht := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (show (0 : ℝ) < 1 from one_pos))
  have hf := Filter.eventually_cofinite.1 ht
  refine ⟨hf.toFinset, ?_⟩
  have hpos : ∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ hf.toFinset},
      0 < (mv v.1 (latV b v.1)).toReal := fun v => by
    have h1 : |(mv v.1 (latV b v.1)).toReal - 1| < 1 := by
      by_contra h'
      exact v.2 (by simpa using h')
    linarith [(abs_lt.1 h1).1]
  have hs' : Summable fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ hf.toFinset} =>
      (mv v.1 (latV b v.1)).toReal - 1 := (hs.of_abs).subtype _
  have hl := Real.summable_log_one_add_of_summable hs'
  simp only [add_sub_cancel] at hl
  rw [tailProd, ← Real.rexp_tsum_eq_tprod hpos hl]
  exact (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'

theorem finiteOnCompacts (h : IsProd b ν mi mv) : IsFiniteMeasureOnCompacts ν := by
  classical
  refine ⟨fun K hK => ?_⟩
  obtain ⟨S, hS⟩ := hK.elim_directed_cover (box b) (isOpen_box b)
    (fun X _ => Set.mem_iUnion.2 (exists_mem_box b X))
    (fun S T => ⟨S ∪ T, box_mono b Finset.subset_union_left, box_mono b Finset.subset_union_right⟩)
  have hc := (GlobalTheory.GaugeGlue.adelicTuple_measurableEmbedding F E d b n M).2.2
  have hi := hK.image hc.1
  have hv := fun v => hK.image (hc.2 v)
  have key := measure_rect h S hi.measurableSet (fun v => (hv v).measurableSet)
  haveI := h.1.1
  haveI := h.1.2.1
  refine lt_of_le_of_lt (measure_mono fun X hX => ?_) (key.trans_lt ?_)
  · exact ⟨⟨⟨X, hX, rfl⟩, fun v _ => ⟨X, hX, rfl⟩⟩, hS hX⟩
  · exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hi.measure_lt_top
      (ENNReal.prod_lt_top fun v _ => (hv v).measure_lt_top)) ENNReal.ofReal_lt_top

theorem ne_zero (h : IsProd b ν mi mv) (hi : mi ≠ 0) (hv : ∀ v, mv v ≠ 0) : ν ≠ 0 := by
  obtain ⟨S, hS⟩ := exists_tailProd_ne_zero h.1
  have := measure_rect h S (Av := fun _ => Set.univ) MeasurableSet.univ fun _ => MeasurableSet.univ
  rintro rfl
  exact mul_ne_zero (mul_ne_zero (Measure.measure_univ_ne_zero.2 hi)
    (Finset.prod_ne_zero_iff.2 fun v _ => Measure.measure_univ_ne_zero.2 (hv v))) hS this.symm

theorem null (h : IsProd b ν mi mv) (Ai : Set (Fin n → Fin M → Ainf F ⊗[F] E))
    (Av : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hi : MeasurableSet Ai) (hv : ∀ v, MeasurableSet (Av v)) (zi : mi Aiᶜ = 0)
    (zv : ∀ v, mv v (Av v)ᶜ = 0) :
    ν {X | ¬ (projInf X ∈ Ai ∧ ∀ v, projV v (projFin X) ∈ Av v)} = 0 := by
  classical
  haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  have h1 : ∀ S, ν ({X | projInf X ∈ Aiᶜ ∧ ∀ v ∈ S, projV v (projFin X) ∈ Set.univ} ∩ box b S) = 0 :=
    fun S => by
      rw [measure_rect h S (Av := fun _ => Set.univ) hi.compl fun _ => MeasurableSet.univ, zi,
        zero_mul, zero_mul]
  have h2 : ∀ (w : HeightOneSpectrum (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))),
      ν ({X | projInf X ∈ Set.univ ∧ ∀ v ∈ insert w S,
        projV v (projFin X) ∈ (if v = w then (Av v)ᶜ else Set.univ)} ∩ box b (insert w S)) = 0 :=
    fun w S => by
      rw [measure_rect h (insert w S) (Av := fun v => if v = w then (Av v)ᶜ else Set.univ)
        MeasurableSet.univ fun v => by
          split_ifs
          exacts [(hv v).compl, MeasurableSet.univ],
        Finset.prod_eq_zero (Finset.mem_insert_self w S) (by simpa using zv w), mul_zero, zero_mul]
  refine measure_mono_null (fun X hX => ?_) (measure_union_null (measure_iUnion_null h1)
    (measure_iUnion_null fun w => measure_iUnion_null (h2 w)))
  obtain ⟨S, hS⟩ := exists_mem_box b X
  rcases not_and_or.1 hX with h3 | h3
  · exact Or.inl (Set.mem_iUnion.2 ⟨S, ⟨h3, fun _ _ => trivial⟩, hS⟩)
  · obtain ⟨w, hw⟩ := not_forall.1 h3
    refine Or.inr (Set.mem_iUnion₂.2 ⟨w, S, ⟨trivial, fun v _ => ?_⟩,
      box_mono b (Finset.subset_insert w S) hS⟩)
    split_ifs with h4
    · subst h4; exact hw
    · trivial

end GlobalTheory.GaugeEx.ProdBasic

theorem GlobalTheory.GaugeEx.isProd_basic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsProd b ν mi mv → IsFiniteMeasureOnCompacts ν ∧ (mi ≠ 0 → (∀ v, mv v ≠ 0) → ν ≠ 0) ∧ (∀ ν', IsProd b ν' mi mv → ν' = ν) ∧ ∀ (Ai : Set (Fin n → Fin M → Ainf F ⊗[F] E)) (Av : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), MeasurableSet Ai → (∀ v, MeasurableSet (Av v)) → mi Aiᶜ = 0 → (∀ v, mv v (Av v)ᶜ = 0) → ν {X | ¬ (projInf X ∈ Ai ∧ ∀ v, projV v (projFin X) ∈ Av v)} = 0 := by
  intro F E _ _ _ _ _ d b n M ν mi mv h
  refine ⟨ProdBasic.finiteOnCompacts h, ProdBasic.ne_zero h, fun ν' h' => ?_, ProdBasic.null h⟩
  refine GlobalTheory.T.adelicTupleMeasure_ext_of_pureTensor_integrals F E d b n M ν' ν fun Φ Φi Φf Φv h1 h2 h3 h4 => ?_
  have k := _root_.GlobalTheory.GaugeEx.ProdInt.integral_pure F E d b n M ν mi mv h d b Φ Φi Φf Φv h1 h2 h3 h4
  have k' := _root_.GlobalTheory.GaugeEx.ProdInt.integral_pure F E d b n M ν' mi mv h' d b Φ Φi Φf Φv h1 h2 h3 h4
  exact ⟨k'.1, k.1, k'.2.2.trans k.2.2.symm⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaWeightArithmeticAtPlaceProof
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.DivisionValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes Formalism.L2.NTheta

namespace GlobalTheory.PairWeightArith

lemma toNat_floor_cast {x : ℚ} (hz : ∃ z : ℤ, x = z) (h0 : 0 ≤ x) : ((⌊x⌋.toNat : ℕ) : ℚ) = x := by
  obtain ⟨z, rfl⟩ := hz
  have hz : 0 ≤ z := by exact_mod_cast h0
  rw [Int.floor_intCast]
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
  simp

lemma lamAt_tail {R : Ranks} (h : HCParam R) (n : ℕ) (c : Fin R.m) (hn : n + 1 = R.k + c) :
    lamAt h n = -h.b c := by
  have hk := R.m_add_three_le_k
  have hc := c.2
  unfold lamAt
  rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  congr 2
  exact Fin.ext (by simp only; omega)

lemma lamAt_anti {R : Ranks} (h : HCParam R) {a b : ℕ} (hab : a ≤ b) (hb : b < R.r) :
    lamAt h b + b ≤ lamAt h a + a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  have := lamAt_add_add_le h d a hb
  push_cast
  linarith

variable (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau)

lemma sig_eq : pS D i τ = D.R.k + i ∧ qS D i τ = D.R.m - ((i : ℕ) + 1) := by
  have h := D.sp.W_sigval ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2 (tauE D τ)
  refine ⟨?_, ?_⟩
  · show ((D.sp.W ((i : ℕ) + 1)).sig (tauE D τ)).1 = _
    rw [h]; simp [Ranks.sigW]
  · show ((D.sp.W ((i : ℕ) + 1)).sig (tauE D τ)).2 = _
    rw [h]; rfl

lemma pq_eq : pS D i τ + qS D i τ = D.R.r := by
  obtain ⟨h1, h2⟩ := sig_eq D i τ
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  rw [h1, h2]; unfold Ranks.r; omega

lemma t_half : ∃ s : ℕ, (D.R.t : ℚ) = 2 * s + 1 := by
  obtain ⟨s, hs⟩ := D.R.t_odd
  exact ⟨s, by exact_mod_cast hs⟩

lemma aPlusQ_int (a : ℕ) : ∃ z : ℤ, aPlusQ D i τ a = z := by
  obtain ⟨s, hs⟩ := t_half D
  obtain ⟨z, hz⟩ := lamAt_int (D.hc τ) a
  obtain ⟨e, he⟩ := (D.hc τ).e_int i
  refine ⟨z + e - (pS D i τ : ℕ) + a - s, ?_⟩
  simp only [aPlusQ, centred, eS, hs, hz, he]
  push_cast; ring

lemma neg_dRowQ_int (c : ℕ) : ∃ z : ℤ, -dRowQ D i τ c = z := by
  obtain ⟨s, hs⟩ := t_half D
  obtain ⟨z, hz⟩ := lamAt_int (D.hc τ) (pS D i τ + c)
  obtain ⟨e, he⟩ := (D.hc τ).e_int i
  refine ⟨-(z + e + c + 1 + s), ?_⟩
  simp only [dRowQ, centred, eS, hs, hz, he]
  push_cast; ring

lemma aPlusQ_anti {a b : ℕ} (hab : a ≤ b) (hb : b < pS D i τ) : aPlusQ D i τ b ≤ aPlusQ D i τ a := by
  have h := pq_eq D i τ
  have := lamAt_anti (D.hc τ) hab (by omega)
  simp only [aPlusQ, centred]
  linarith

lemma dRowQ_anti {a b : ℕ} (hab : a ≤ b) (hb : b < qS D i τ) : dRowQ D i τ b ≤ dRowQ D i τ a := by
  have h := pq_eq D i τ
  have := lamAt_anti (D.hc τ) (Nat.add_le_add_left hab (pS D i τ)) (by omega)
  simp only [dRowQ, centred]
  push_cast at this
  linarith

lemma one_le_aPlusQ {a : ℕ} (ha : a < pS D i τ) : 1 ≤ aPlusQ D i τ a := by
  obtain ⟨n, hn⟩ : ∃ n, pS D i τ = n + 1 := ⟨pS D i τ - 1, by omega⟩
  refine le_trans ?_ (aPlusQ_anti D i τ (show a ≤ n by omega) (by omega))
  have h1 := lamAt_tail (D.hc τ) n i (by rw [← hn]; exact (sig_eq D i τ).1)
  have g := (D.hc τ).gap_be i
  have hn' : (pS D i τ : ℚ) = n + 1 := by exact_mod_cast hn
  simp only [aPlusQ, centred, eS, h1, hn']
  linarith

lemma one_le_neg_dRowQ {c : ℕ} (hc : c < qS D i τ) : 1 ≤ -dRowQ D i τ c := by
  obtain ⟨hp, hq⟩ := sig_eq D i τ
  have h0 := dRowQ_anti D i τ (Nat.zero_le c) hc
  have hi : (i : ℕ) + 1 < D.R.m := by omega
  have h1 := lamAt_tail (D.hc τ) (pS D i τ + 0) ⟨i + 1, hi⟩ (by simp only; omega)
  have g := (D.hc τ).gap_eb i hi
  have : dRowQ D i τ 0 ≤ -1 := by
    simp only [dRowQ, centred, eS, h1]
    push_cast
    linarith
  linarith

lemma cast_aPlus {a : ℕ} (ha : a < pS D i τ) : (aP D i τ a : ℚ) = aPlusQ D i τ a := by
  unfold aP aPl
  rw [if_pos ha]
  exact toNat_floor_cast (aPlusQ_int D i τ a) (le_trans zero_le_one (one_le_aPlusQ D i τ ha))

lemma aM_cast {c : ℕ} (hc : c < qS D i τ) : (aM D i τ (qS D i τ - 1 - c) : ℚ) = -dRowQ D i τ c := by
  unfold aM aMi
  have e1 : qS D i τ - (qS D i τ - 1 - c) = c + 1 := by omega
  rw [if_pos (by omega), e1, show pS D i τ + (c + 1) - 1 = pS D i τ + c by omega]
  have e2 : -((D.hc τ).e i + lamAt (D.hc τ) (pS D i τ + c) + ((c + 1 : ℕ) : ℚ) + ((D.R.t : ℚ) - 1) / 2)
      = -dRowQ D i τ c := by
    simp only [dRowQ, centred, eS]; push_cast; ring
  rw [e2]
  exact toNat_floor_cast (neg_dRowQ_int D i τ c) (le_trans zero_le_one (one_le_neg_dRowQ D i τ hc))

lemma aM_cast' {a : ℕ} (ha : a < qS D i τ) : (aM D i τ a : ℚ) = -dRowQ D i τ (qS D i τ - 1 - a) := by
  rw [← aM_cast D i τ (by omega)]
  congr 2
  omega

lemma lam_eq {w : IndefiniteWeightData.WeightData} (hw : IsDataOf D i τ w) {a : ℕ} (ha : a < D.R.r) :
    (w.lam (a + 1) : ℚ) = lamAt (D.hc τ) a := by
  obtain ⟨hk, -, -, -, -, hv, hb⟩ := hw
  have hk3 := D.R.m_add_three_le_k
  unfold Ranks.r at ha
  unfold IndefiniteWeightData.WeightData.lam
  rw [hk]
  by_cases h : a < D.R.k - 1
  · rw [if_pos (by omega)]
    unfold lamAt
    rw [dite_eq_left h]
    exact hv ⟨a, h⟩
  · rw [if_neg (by omega), lamAt_tail (D.hc τ) a ⟨a + 1 - D.R.k, by omega⟩ (by simp only; omega),
      ← hb, Int.cast_neg]
    congr 3
    simp only; omega

lemma lamPrime_eq (w : IndefiniteWeightData.WeightData) (hw : IsDataOf D i τ w) (a : ℕ) (ha : a < D.R.r + D.R.t) :
    w.lamPrime (a + 1) = (thetaWt D i τ a : ℚ) + dShift D i τ := by
  obtain ⟨hp, hq⟩ := sig_eq D i τ
  have hr := pq_eq D i τ
  have hl := fun a ha => lam_eq D i τ (a := a) hw ha
  obtain ⟨hk, hm, ht, hj, he, hv, hb⟩ := hw
  have hk3 := D.R.m_add_three_le_k
  have wp : w.p = pS D i τ := by unfold IndefiniteWeightData.WeightData.p; omega
  have wq : w.q = qS D i τ := by unfold IndefiniteWeightData.WeightData.q; omega
  have wn : w.nV = pS D i τ + qS D i τ + D.R.t := by
    unfold IndefiniteWeightData.WeightData.nV IndefiniteWeightData.WeightData.r; unfold Ranks.r at hr; omega
  unfold IndefiniteWeightData.WeightData.lamPrime
  congr 1
  · unfold IndefiniteWeightData.WeightData.thetaWt thetaWt
    rw [wp, wq, ht]
    by_cases h1 : a < pS D i τ
    · rw [if_pos (by omega), if_pos h1, Int.cast_natCast, cast_aPlus D i τ h1]
      unfold IndefiniteWeightData.WeightData.aPlus
      rw [hl a (by omega), wn, wp, wq, he]
      simp only [aPlusQ, centred]
      push_cast; ring
    · rw [if_neg (by omega), if_neg h1]
      by_cases h2 : a < pS D i τ + D.R.t
      · rw [if_pos (by omega), if_pos h2]; simp
      · rw [if_neg (by omega), if_neg h2]
        obtain ⟨c, rfl⟩ : ∃ c, a = pS D i τ + D.R.t + c := ⟨a - (pS D i τ + D.R.t), by omega⟩
        have hc : c < qS D i τ := by omega
        rw [Nat.add_sub_cancel_left, Int.cast_neg, Int.cast_natCast, aM_cast D i τ hc]
        unfold IndefiniteWeightData.WeightData.aMinus
        have e1 : w.q + 1 - (qS D i τ + 1 - (pS D i τ + D.R.t + c + 1 - pS D i τ - D.R.t)) = c + 1 := by
          omega
        have hi : (i : ℕ) + c + 1 < D.R.m := by omega
        have e2 : (w.b (w.j + (c + 1)) : ℚ) = (D.hc τ).b ⟨i + c + 1, hi⟩ := by
          rw [← hb]; congr 2; simp only; omega
        rw [e1, e2, he, ht]
        simp only [dRowQ, centred]
        rw [lamAt_tail (D.hc τ) (pS D i τ + c) ⟨i + c + 1, hi⟩ (by simp only; omega)]
        push_cast; ring
  · unfold IndefiniteWeightData.WeightData.dTau dShift
    rw [wp, wq, he]

theorem arithAt : ∀ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau), ArithAt D i τ := by
  intro D i τ
  have hr := pq_eq D i τ
  have hV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hr' : (D.R.r : ℚ) = (pS D i τ : ℚ) + (qS D i τ : ℚ) := by exact_mod_cast hr.symm
  have ho : Odd (pS D i τ + qS D i τ) := hr ▸ odd_r D.R
  have hL := GlobalTheory.ForcedWeights.lamLForced D ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2 τ
  refine ⟨sig_eq D i τ, ⟨hr, hV⟩, fun a ha => cast_aPlus D i τ ha, fun c hc => aM_cast D i τ hc,
    fun a b hab hb => ?_, fun a b hab hb => ?_, fun a ha => ?_, fun a ha => ?_, fun a => ?_, fun c => ?_, ?_,
    lamPrime_eq D i τ, hL, fun a => ?_⟩
  · rw [← Nat.cast_le (α := ℚ), cast_aPlus D i τ hb, cast_aPlus D i τ (by omega)]
    exact aPlusQ_anti D i τ hab hb
  · rw [← Nat.cast_le (α := ℚ), aM_cast' D i τ hb, aM_cast' D i τ (by omega), neg_le_neg_iff]
    exact dRowQ_anti D i τ (by omega) (by omega)
  · rw [← Nat.cast_le (α := ℚ), cast_aPlus D i τ ha, Nat.cast_one]
    exact one_le_aPlusQ D i τ ha
  · rw [← Nat.cast_le (α := ℚ), aM_cast' D i τ ha, Nat.cast_one]
    exact one_le_neg_dRowQ D i τ (by omega)
  · rw [kapW_cast _ _ _ ho, cast_aPlus D i τ a.2]
    simp only [kapQ, Sum.elim_inl, aPlusQ, centred, hr']; ring
  · rw [kapW_cast _ _ _ ho, aM_cast D i τ c.2]
    simp only [kapQ, Sum.elim_inr, dRowQ, centred, hr']; ring
  · obtain ⟨s, hs⟩ := ho
    have hs' : (qS D i τ : ℚ) = 2 * s + 1 - pS D i τ := by
      have : (pS D i τ : ℚ) + qS D i τ = 2 * s + 1 := by exact_mod_cast hs
      linarith
    obtain ⟨e, he⟩ := (D.hc τ).e_int i
    refine ⟨(pS D i τ : ℕ) - s - 1 - e, ?_⟩
    simp only [dShift, eS, he, hs']
    push_cast; ring
  · obtain ⟨_, w, hk, hm, ht, hj, he, hv, hb, hw⟩ := hL
    rw [hw a]
    exact lamPrime_eq D i τ w ⟨hk, hm, ht, hj, he, hv, hb⟩ a (hV ▸ a.2)

end GlobalTheory.PairWeightArith
end

