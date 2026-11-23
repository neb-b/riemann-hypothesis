module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0072
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0058
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0092
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0084
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0096
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0095
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0079
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0040
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0082
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0094
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegMassNearSmall
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

theorem RegMassNearSmall.proof (hCmp : RegFormCompare.Statement) (hBall : RegBallMass.Statement)
    (hCov : SmallSetBallCover.Statement) : RegMassNearSmall.Statement := by
  classical
  intro n d J I u φ f hJ hdim hu hφ hIdim hf hfc δ hδ
  by_cases h : ∃ A : Matrix (Fin (d + 1)) (Fin n) ℂ, IsFiniteProjection J A
  swap
  · exact ⟨Set.univ, isOpen_univ, Set.subset_univ _, fun χ _ _ _ ε _ => by simp [varInt, h, hδ.le]⟩
  set A := h.choose
  have hA : IsFiniteProjection J A := h.choose_spec
  have hfin : ∀ y, (fibre J A y).Finite := fun y => (FibreBound.proof n (d + 1) J A hJ hdim hA y).2.1
  set K := tsupport f
  obtain ⟨C₁, hC₁, h₁⟩ := hCmp n d J A φ f hJ hdim hA hφ hf hfc
  obtain ⟨C₂, hC₂, h₂⟩ := hBall n d J A u K hJ hdim hA hu hfc
  obtain ⟨C₃, hC₃, h₃⟩ := hCov n d I K hIdim hfc
  have hM : 0 ≤ C₁ * C₂ * C₃ := by positivity
  set r := min 1 (δ / (C₁ * C₂ * C₃ + 1))
  have hr : r ∈ Set.Ioc (0 : ℝ) 1 := ⟨lt_min one_pos (by positivity), min_le_left _ _⟩
  obtain ⟨T, hTK, hcov, hcard⟩ := h₃ r hr
  have hUo : IsOpen ((⋃ c ∈ T, Metric.ball c r) ∪ Kᶜ) :=
    (isOpen_biUnion fun (c : Fin n → ℂ) _ => Metric.isOpen_ball).union hfc.isClosed.isOpen_compl
  refine ⟨(⋃ c ∈ T, Metric.ball c r) ∪ Kᶜ, hUo, fun x hx => ?_, fun χ _ hχ1 hχU ε hε => ?_⟩
  · by_cases hxK : x ∈ K
    · exact Or.inl (hcov ⟨hx, hxK⟩)
    · exact Or.inr hxK
  set ψ : Fin (d + 1) → (Fin n → ℂ) → ℝ := vecCons (logReg u ε) fun _ => euclPot
  set w : (Fin n → ℂ) → ℝ := fun x => ∑ c ∈ T, (Metric.ball c r).indicator (fun _ => (1 : ℝ)) x with hw
  have hi0 : ∀ c x : Fin n → ℂ, 0 ≤ (Metric.ball c r).indicator (fun _ => (1 : ℝ)) x :=
    fun c x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hw0 : ∀ x, 0 ≤ w x := fun x => Finset.sum_nonneg fun c _ => hi0 c x
  have hvw : ∀ x ∈ K, |χ x| ≤ w x := by
    intro x hxK
    by_cases h0 : χ x = 0
    · rw [h0, abs_zero]
      exact hw0 x
    rcases hχU (subset_tsupport χ h0) with hxB | hxK'
    · obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.1 hxB
      calc |χ x| ≤ 1 := hχ1 x
        _ = (Metric.ball c r).indicator (fun _ => (1 : ℝ)) x := (Set.indicator_of_mem hxc (fun _ => (1 : ℝ))).symm
        _ ≤ w x := Finset.single_le_sum (f := fun c => (Metric.ball c r).indicator (fun _ => (1 : ℝ)) x)
            (fun c _ => hi0 c x) hc
    · exact absurd hxK hxK'
  have hsum : chartDens J A w ψ =
      fun y => ∑ c ∈ T, chartDens J A ((Metric.ball c r).indicator fun _ => 1) ψ y := by
    funext y
    simp only [chartDens, sheetSum]
    simp_rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp [hw, Finset.sum_mul]
  have hball := fun c (hc : c ∈ T) => h₂ ε hε c (hTK hc).2 r hr
  have hint : Integrable (chartDens J A w ψ) := by
    rw [hsum]
    exact integrable_finsetSum _ fun c hc => (hball c hc).1
  have hT : ∫ y, chartDens J A w ψ y ≤ T.card * (C₂ * r ^ (2 * d)) := by
    rw [hsum, integral_finsetSum _ fun c hc => (hball c hc).1, ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun c hc => (hball c hc).2
  rw [varInt, dite_eq_left h]
  calc |chartInt J A (fun x => χ x * f x) (vecCons (logReg u ε) φ)|
      ≤ ∫ y, C₁ * chartDens J A w ψ y := by
        refine abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
          (Eventually.of_forall fun y => abs_nonneg _) (hint.const_mul C₁) (Eventually.of_forall fun y => ?_))
        exact (VarIntAdd.abs_chartDens_le hfin _ _ y).trans (h₁ u ε hε.1 χ w hw0 hvw y)
    _ = C₁ * ∫ y, chartDens J A w ψ y := integral_const_mul _ _
    _ ≤ C₁ * (T.card * (C₂ * r ^ (2 * d))) := mul_le_mul_of_nonneg_left hT hC₁
    _ = C₁ * C₂ * (T.card * r ^ (2 * d)) := by ring
    _ ≤ C₁ * C₂ * (C₃ * r ^ 2) := mul_le_mul_of_nonneg_left hcard (by positivity)
    _ ≤ (C₁ * C₂ * C₃ + 1) * r := by
        nlinarith [mul_le_mul_of_nonneg_left hr.2 (mul_nonneg hM hr.1.le), hr.1]
    _ ≤ (C₁ * C₂ * C₃ + 1) * (δ / (C₁ * C₂ * C₃ + 1)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
    _ = δ := mul_div_cancel₀ _ (by positivity)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem SliceDim.homogeneousComponent_zero_linForm_sub_one {n : ℕ} (ℓ : Fin n → ℂ) :
    homogeneousComponent 0 (linForm ℓ - 1 : MvPolynomial (Fin n) ℂ) = -1 := by
  rw [homogeneousComponent_zero]
  simp [linForm, coeff_sum, coeff_C_mul, coeff_X]

theorem SliceDim.linForm_sub_one_not_mem {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (hH : IsHomogIdeal J) (hJ : J ≠ ⊤) (ℓ : Fin n → ℂ) : linForm ℓ - 1 ∉ J := by
  intro h
  have h0 := hH _ h 0
  rw [SliceDim.homogeneousComponent_zero_linForm_sub_one, neg_mem_iff] at h0
  exact hJ ((Ideal.eq_top_iff_one J).mpr h0)

theorem SliceDim.proof : SliceDim.Statement := by
  intro n e J ℓ hJ hdim hℓ
  have hP := hJ.isPrime
  refine le_antisymm ?_ (IndefiniteRowSideFullHecke.ComplexSets.le_ringKrullDim_slice ⟨hP, hdim⟩ hJ.isHomog hℓ)
  set r := Ideal.Quotient.mk J (linForm ℓ - 1) with hr_def
  have hr0 : r ≠ 0 := by
    rw [hr_def, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact SliceDim.linForm_sub_one_not_mem hJ.isHomog hP.ne_top ℓ
  have hr : r ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ J) := mem_nonZeroDivisors_of_ne_zero hr0
  have hle : J ≤ J ⊔ Ideal.span {linForm ℓ - 1} := le_sup_left
  have hkill : Ideal.Quotient.factor hle r = 0 := by
    rw [hr_def, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact le_sup_right (a := J) (Ideal.subset_span rfl)
  have key := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
    (Ideal.Quotient.factor_surjective hle) hr hkill
  rw [hdim] at key
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1})) = D at key ⊢
  induction D using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe b =>
    induction b using ENat.recTopCoe with
    | top =>
      exfalso
      norm_cast at key
    | coe m =>
      have : m + 1 ≤ e + 1 := by exact_mod_cast key
      exact_mod_cast (by omega : m ≤ e)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceLocalDimGeneral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

theorem ringKrullDim_quotient_le_sup_span_add {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R)
    (hI : I ≠ ⊤) {d : ℕ} (t : Fin d → R) (ht : ∀ i, t i ∈ IsLocalRing.maximalIdeal R) :
    ringKrullDim (R ⧸ I) ≤ ringKrullDim (R ⧸ (I ⊔ Ideal.span (Set.range t))) + (d : ℕ) := by
  classical
  let s : Finset (R ⧸ I) := Finset.univ.image fun i => Ideal.Quotient.mk I (t i)
  have hs : Ideal.span (s : Set (R ⧸ I)) = (Ideal.span (Set.range t)).map (Ideal.Quotient.mk I) := by
    rw [Ideal.map_span]
    congr 1
    ext x
    simp [s]
  have hjac : (Ideal.span (Set.range t)).map (Ideal.Quotient.mk I) ≤ Ring.jacobson (R ⧸ I) := by
    rw [← Ideal.jacobson_bot, ← Ideal.map_quotient_self I,
      ← Ideal.map_jacobson_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]),
      IsLocalRing.jacobson_eq_maximalIdeal I hI]
    refine Ideal.map_mono ?_
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact ht i
  have hkey := ringKrullDim_le_ringKrullDim_quotient_add_card s
    fun x hx => hjac (hs ▸ Ideal.subset_span hx)
  rw [hs, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup I _)] at hkey
  refine hkey.trans ?_
  gcongr
  exact_mod_cast Finset.card_image_le.trans (by simp)

theorem one_le_ringKrullDim_localRingAt_sliceIdeal {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (L : Matrix (Fin d) (Fin n) ℂ) (q : Fin n → ℂ)
    (hdim : ringKrullDim (localRingAt J q) = (d + 1 : ℕ)) :
    ((1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (localRingAt (sliceIdeal J L q) q) := by
  let φ := algebraMap (MvPolynomial (Fin n) ℂ)
    (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))
  let t : Fin d → MvPolynomial (Fin n) ℂ := fun i => linPoly L i - C ((L *ᵥ q) i)
  have hI : J.map φ ≠ ⊤ := by
    intro h
    unfold localRingAt at hdim
    have : Subsingleton (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) ⧸
        J.map φ) := Ideal.Quotient.subsingleton_iff.mpr h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact WithBot.bot_ne_coe hdim
  have ht : ∀ i, φ (t i) ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ))) := by
    intro i
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    refine Ideal.mem_map_of_mem _ ?_
    simp [t, RingHom.mem_ker, eval_linPoly]
  have hkey := ringKrullDim_quotient_le_sup_span_add (J.map φ) hI (fun i => φ (t i)) ht
  have hsl : (sliceIdeal J L q).map φ = J.map φ ⊔ Ideal.span (Set.range fun i => φ (t i)) := by
    rw [sliceIdeal, Ideal.map_sup, Ideal.map_span, ← Set.range_comp]
    rfl
  rw [← hsl] at hkey
  change ringKrullDim (localRingAt J q) ≤ ringKrullDim (localRingAt (sliceIdeal J L q) q) + (d : ℕ)
    at hkey
  rw [hdim] at hkey
  generalize ringKrullDim (localRingAt (sliceIdeal J L q) q) = D at hkey ⊢
  induction D using WithBot.recBotCoe with
  | bot => simp at hkey
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact WithBot.coe_le_coe.2 le_top
    | coe k =>
      have h2 : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ ((k + d : ℕ) : WithBot ℕ∞) := by simpa using hkey
      have h3 : d + 1 ≤ k + d := by exact_mod_cast h2
      exact_mod_cast (show 1 ≤ k by omega)

theorem SliceLocalDimGeneral.proof (hL : LocalDimDomain.Statement)
    (hU : SliceLocalDimUpperZariski.Statement) : SliceLocalDimGeneral.Statement := by
  intro n d J q hJ hdim hq
  obtain ⟨F, hF, hgood⟩ := hU n d J q hJ hdim hq
  have hloc := hL n (d + 1) J hJ hdim q hq
  let e : Matrix (Fin d) (Fin n) ℂ → (Fin d × Fin n → ℂ) := fun L ij => L ij.1 ij.2
  let ψ : (Fin d × Fin n → ℂ) → Matrix (Fin d) (Fin n) ℂ := fun y => Matrix.of fun i j => y (i, j)
  have he : Continuous e := continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2
  have hψ : Continuous ψ :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)
  refine ⟨{L | eval (e L) F ≠ 0}, ?_, ?_, fun L hLF => le_antisymm (hgood L hLF)
    (one_le_ringKrullDim_localRingAt_sliceIdeal J L q hloc)⟩
  · exact isOpen_ne_fun ((MvPolynomial.continuous_eval F).comp he) continuous_const
  · rw [dense_iff_inter_open]
    rintro U hU ⟨L₀, hL₀⟩
    obtain ⟨y, hyU, hyF⟩ := exists_eval_ne_zero_of_isOpen_pi hF (hU.preimage hψ) ⟨e L₀, hL₀⟩
    exact ⟨ψ y, hyU, hyF⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceLocalDimUpperZariski
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

theorem SliceLocalDimUpperZariski.ringKrullDim_le_of_finite {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Finite) : ringKrullDim S ≤ ringKrullDim R := by
  let _ := f.toAlgebra
  have : Module.Finite R S := hf
  have : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  refine Order.krullDim_le_of_strictMono
    (fun p : PrimeSpectrum S => PrimeSpectrum.comap (algebraMap R S) p) ?_
  intro p p' h
  have h' : p.asIdeal < p'.asIdeal := h
  exact Ideal.IsIntegral.comap_lt_comap (R := R) h'

theorem SliceLocalDimUpperZariski.localDim_le {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (q : Fin n → ℂ) (hq : q ∈ zeroSet I) :
    ringKrullDim (localRingAt I q) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) := by
  set M : Ideal (MvPolynomial (Fin n) ℂ) := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)
  have hIM : I ≤ M := fun f hf => RingHom.mem_ker.mpr (hq f hf)
  let m : Ideal (MvPolynomial (Fin n) ℂ ⧸ I) := M.map (Ideal.Quotient.mk I)
  have hm : m.IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hIM)
  have hsub : Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ I) M.primeCompl =
      m.primeCompl := by
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · rintro ⟨z, hz, hzy⟩
      change Ideal.Quotient.mk I y ∉ m
      rw [← hzy]
      change Ideal.Quotient.mk I z ∉ M.map (Ideal.Quotient.mk I)
      rw [Ideal.mem_quotient_iff_mem hIM]
      exact hz
    · intro h
      change Ideal.Quotient.mk I y ∉ M.map (Ideal.Quotient.mk I) at h
      rw [Ideal.mem_quotient_iff_mem hIM] at h
      exact ⟨y, h, rfl⟩
  have : m.IsPrime := hm.isPrime
  have : IsLocalization.AtPrime (localRingAt I q) m := by
    unfold IsLocalization.AtPrime
    rw [← hsub]
    unfold localRingAt
    infer_instance
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (localRingAt I q)]
  exact Ideal.height_le_ringKrullDim_of_isPrime

theorem SliceLocalDimUpperZariski.quotient_dim_le_one {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (L : Matrix (Fin d) (Fin n) ℂ) (q : Fin n → ℂ) (M : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (hML : ∀ i j, M (Fin.castSucc i) j = L i j) (hfin : (projHom J M).toRingHom.Finite) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ sliceIdeal J L q) ≤ (1 : ℕ) := by
  set I := sliceIdeal J L q with hI
  have hJI : J ≤ I := le_sup_left
  let g : MvPolynomial (Fin (d + 1)) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ I :=
    (Ideal.Quotient.factor hJI).comp (projHom J M).toRingHom
  have hg : g.Finite :=
    RingHom.Finite.comp (RingHom.Finite.of_surjective _ (Ideal.Quotient.factor_surjective hJI)) hfin
  let π : MvPolynomial (Fin (d + 1)) ℂ →+* Polynomial ℂ :=
    (aeval (Fin.lastCases (motive := fun _ => Polynomial ℂ) Polynomial.X
      (fun k => Polynomial.C ((L *ᵥ q) k)))).toRingHom
  let ψ : Polynomial ℂ →+* MvPolynomial (Fin n) ℂ ⧸ I :=
    Polynomial.eval₂RingHom (algebraMap ℂ _) (Ideal.Quotient.mk I (linPoly M (Fin.last d)))
  have hlin : ∀ k : Fin d, linPoly M k.castSucc = linPoly L k := by
    intro k
    simp only [linPoly, hML]
  have hCI : ∀ c : ℂ, algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ I) c = Ideal.Quotient.mk I (C c) :=
    fun c => rfl
  have hcomp : ψ.comp π = g := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [π, ψ, g, projHom, pullback, hCI]
    · intro i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · simp [π, ψ, g, projHom, pullback]
      · have hmem : linPoly L k - C ((L *ᵥ q) k) ∈ I :=
          Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
        have hq : Ideal.Quotient.mk I (linPoly L k) = Ideal.Quotient.mk I (C ((L *ᵥ q) k)) :=
          Ideal.Quotient.eq.mpr hmem
        simp [π, ψ, g, projHom, pullback, hlin, hq, hCI]
  have hψ : ψ.Finite := RingHom.Finite.of_comp_finite (f := π) (by rw [hcomp]; exact hg)
  calc ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) ≤ ringKrullDim (Polynomial ℂ) :=
        SliceLocalDimUpperZariski.ringKrullDim_le_of_finite ψ hψ
    _ = (1 : ℕ) := by
        rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
        rfl

theorem SliceLocalDimUpperZariski.proof : SliceLocalDimUpperZariski.Statement := by
  intro n d J q hJ hdim hq
  obtain ⟨W, ⟨S, hS⟩, ⟨A₀, hA₀⟩, hWfin⟩ :=
    ComplexSets.FiniteProjectionsContainOpen.proof ComplexSets.ConeAvoidsFinite.proof
      ComplexSets.FiniteProjHomInjective.proof ComplexSets.ConeAvoidsOpen.proof
      (ComplexSets.ConeAvoidsExists.proof ComplexSets.LeadIdealDim.proof
        ComplexSets.LinearFormCut.proof ComplexSets.HomogDimZeroPow.proof) n (d + 1) J hJ hdim
  rw [hS] at hA₀
  obtain ⟨G, hGS, hG⟩ := hA₀
  let ext : Matrix (Fin d) (Fin n) ℂ → Matrix (Fin (d + 1)) (Fin n) ℂ :=
    fun L i j => if h : (i : ℕ) < d then L ⟨i, h⟩ j else A₀ i j
  let F : MvPolynomial (Fin d × Fin n) ℂ :=
    bind₁ (fun ij : Fin (d + 1) × Fin n =>
      if h : (ij.1 : ℕ) < d then X (⟨ij.1, h⟩, ij.2) else C (A₀ ij.1 ij.2)) G
  have hevF : ∀ L : Matrix (Fin d) (Fin n) ℂ,
      eval (fun ij : Fin d × Fin n => L ij.1 ij.2) F =
        eval (fun ij : Fin (d + 1) × Fin n => ext L ij.1 ij.2) G := by
    intro L
    change eval₂Hom (RingHom.id ℂ) _ (bind₁ _ G) = _
    rw [eval₂Hom_bind₁]
    change eval _ G = _
    refine congrArg (fun f => eval f G) (funext fun ij => ?_)
    simp only [ext]
    split_ifs <;> simp
  have hext0 : ext (fun i j => A₀ i.castSucc j) = A₀ := by
    funext i j
    simp only [ext]
    split_ifs with h
    · rfl
    · rfl
  refine ⟨F, fun h0 => hG ?_, fun L hL => ?_⟩
  · have h1 := hevF (fun i j => A₀ i.castSucc j)
    rw [hext0, h0, map_zero] at h1
    exact h1.symm
  · have hmem : ext L ∈ W := by
      rw [hS]
      exact ⟨G, hGS, (hevF L) ▸ hL⟩
    have hfp : IsFiniteProjection J (ext L) := hWfin hmem
    have hq' : q ∈ zeroSet (sliceIdeal J L q) := by
      rw [zeroSet_sliceIdeal]
      exact ⟨hq, rfl⟩
    refine (SliceLocalDimUpperZariski.localDim_le _ q hq').trans
      (SliceLocalDimUpperZariski.quotient_dim_le_one J L q (ext L) (fun i j => ?_) hfp.finite)
    simp [ext, i.isLt]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceMultGeneral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

theorem dim_eq_of_height_add {h : ℕ∞} {x : WithBot ℕ∞} {e : ℕ} (h1 : x + 1 ≤ ((e + 1 : ℕ) : WithBot ℕ∞))
    (hh : h ≤ 1) (hsum : (h : WithBot ℕ∞) + x = ((e + 1 : ℕ) : WithBot ℕ∞)) : x = ((e : ℕ) : WithBot ℕ∞) := by
  cases x using WithBot.recBotCoe with
  | bot => rw [WithBot.add_bot] at hsum; exact absurd hsum (WithBot.bot_ne_natCast _)
  | coe y =>
    cases y using ENat.recTopCoe with
    | top =>
      have h1' : (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((e + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := h1
      rw [WithBot.coe_le_coe, top_add, top_le_iff] at h1'
      exact absurd h1' (ENat.natCast_ne_top _)
    | coe y =>
      cases h using ENat.recTopCoe with
      | top => simp at hh
      | coe h =>
        have a1 : h + y = e + 1 := by exact_mod_cast hsum
        have a2 : h ≤ 1 := by exact_mod_cast hh
        have a3 : y + 1 ≤ e + 1 := by exact_mod_cast h1
        have : y = e := by omega
        subst this; rfl

theorem ringKrullDim_component {n d : ℕ} {J W : Ideal (MvPolynomial (Fin n) ℂ)} [J.IsPrime]
    {s : MvPolynomial (Fin n) ℂ} (hs : s ∉ J) (hW : W ∈ (J ⊔ Ideal.span {s}).minimalPrimes)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((d + 1 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = ((d : ℕ) : WithBot ℕ∞) := by
  have _ : W.IsPrime := hW.1.1
  have hJW : J ≤ W := le_sup_left.trans hW.1.2
  have hsW : s ∈ W := (le_sup_right.trans hW.1.2) (Ideal.mem_span_singleton_self _)
  have _ : Algebra.FiniteType ℂ (MvPolynomial (Fin n) ℂ ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ J) (Ideal.Quotient.mkₐ_surjective ℂ J)
  set W' : Ideal (MvPolynomial (Fin n) ℂ ⧸ J) := W.map (Ideal.Quotient.mk J)
  have _ : W'.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hW'ne : W' ≠ ⊥ := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp (by
    have : Ideal.Quotient.mk J s ∈ W' := Ideal.mem_map_of_mem _ hsW
    rwa [h, Ideal.mem_bot] at this))
  have hquot : ringKrullDim ((MvPolynomial (Fin n) ℂ ⧸ J) ⧸ W') = ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hJW)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient ℂ W'
  have hdrop := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne
  rw [hquot, hdim] at hform hdrop
  exact dim_eq_of_height_add hdrop (Ideal.map_height_le_one_of_mem_minimalPrimes hW) hform

theorem SliceMultGeneral.proof (hC : CMGeneralPoint.Statement) (hT : TransverseSliceGeneral.Statement)
    (hL : LengthTransverseSlice.Statement) : SliceMultGeneral.Statement := by
  intro n d J W u hJ hdim hu hW
  have hWp : W.IsPrime := hW.1.1
  have hdW := ringKrullDim_component hu hW hdim
  obtain ⟨f₁, hf₁W, hf₁⟩ := hC n _ W hW
  obtain ⟨f₂, hf₂W, hf₂⟩ := hT n d W hWp hdW
  refine ⟨f₁ * f₂, fun h => (hWp.mem_or_mem h).elim hf₁W hf₂W, fun q hq hqf => ?_⟩
  rw [map_mul, mul_ne_zero_iff] at hqf
  obtain ⟨hone, hcm⟩ := hf₁ q hq hqf.1
  obtain ⟨hO, hD⟩ := hf₂ q hq hqf.2
  refine ⟨_, hO, hD, fun L hL' => ?_⟩
  have hsl : sliceIdeal J L q ⊔ Ideal.span {linForm u} = sliceIdeal (J ⊔ Ideal.span {linForm u}) L q := by
    simp only [sliceIdeal, sup_right_comm]
  rw [hsl]
  exact hL n d _ W q L hW hdW hq hone hcm hL'

end GroundTheory.Heights₂.Heights
end

