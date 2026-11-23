module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0031
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLatticeChainLatAndComap
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.ChainLattice

theorem exists_smul_mem {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (M : Submodule R V) {v : V} (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ a : R, a ≠ 0 ∧ a • v ∈ M := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11; revert R K V h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 M v hv; exact @_root_.GlobalTheory.SmulMemOfMemSpan.main)
  | exact @_root_.GlobalTheory.SmulMemOfMemSpan.main
  | exact _root_.GlobalTheory.SmulMemOfMemSpan.main
  | (apply _root_.GlobalTheory.SmulMemOfMemSpan.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmulMemOfMemSpan.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmulMemOfMemSpan.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmulMemOfMemSpan.main ..)

theorem span_eq_top_of_smul_mem {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (M : Submodule R V) (h : ∀ v : V, ∃ a : R, a ≠ 0 ∧ a • v ∈ M) :
    Submodule.span K (M : Set V) = ⊤ := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11; revert R K V h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 M h; exact @_root_.GlobalTheory.LemmaTwoFortyThirteen.main)
  | exact @_root_.GlobalTheory.LemmaTwoFortyThirteen.main
  | exact _root_.GlobalTheory.LemmaTwoFortyThirteen.main
  | (apply _root_.GlobalTheory.LemmaTwoFortyThirteen.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LemmaTwoFortyThirteen.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LemmaTwoFortyThirteen.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LemmaTwoFortyThirteen.main ..)

theorem isLattice_chainLat_and_comap :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (n : Type) [Fintype n] [DecidableEq n] (c : ℕ),
      (∀ (ϖ : 𝒪[k]), (ϖ : k) ≠ 0 → ∀ L : Submodule 𝒪[k] (n → k), Submodule.IsLattice k L →
        Submodule.IsLattice k (chainLat ϖ c L)) ∧
      ∀ Λ : Submodule 𝒪[k] (n ⊕ Fin c → k), Submodule.IsLattice k Λ →
        Submodule.IsLattice k (Λ.comap (inX k n c)) := by
  intro k _ _ _ _ n _ _ c
  refine ⟨fun ϖ hϖ L hL => ⟨?_, ?_⟩, fun Λ hΛ => ⟨?_, ?_⟩⟩
  · exact (hL.fg.map _).sup (Submodule.fg_span (Set.finite_range _))
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · refine Submodule.fg_of_fg_map_injective (inX k n c) ?_
      (hΛ.fg.of_le (Submodule.map_comap_le _ _))
    intro x y hxy
    funext r
    have := congrFun hxy (Sum.inl r)
    simpa [inX_apply] using this
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli

end GlobalTheory.RootEx.ChainLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped ENNReal NNReal

namespace GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n]
  (ν : Measure k) [ν.IsAddHaarMeasure]

theorem map_mul_left_volM (h : GL n k) :
    (volM ν n n).map (fun x => h.val * x) =
      ENNReal.ofReal (nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card n : ℝ))) • volM ν n n := by
  haveI := secondCountable k
  haveI := t2Space k
  haveI : BorelSpace (Matrix n n k) := inferInstanceAs (BorelSpace (n → n → k))
  haveI : LocallyCompactSpace (Matrix n n k) := inferInstanceAs (LocallyCompactSpace (n → n → k))
  haveI : SecondCountableTopology (Matrix n n k) := inferInstanceAs (SecondCountableTopology (n → n → k))
  haveI : (volM ν n n).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let e : Matrix n n k ≃+ Matrix n n k :=
    { toFun := fun x => h.val * x
      invFun := fun x => (h⁻¹).val * x
      left_inv := fun x => by simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun x => by simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      map_add' := fun x y => Matrix.mul_add _ _ _ }
  have c1 : Continuous e := continuous_const.matrix_mul continuous_id
  have c2 : Continuous e.symm := continuous_const.matrix_mul continuous_id
  haveI := e.isAddHaarMeasure_map (volM ν n n) c1 c2
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, (volM ν n n).map e = c • volM ν n n :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  change (volM ν n n).map e = _
  set K : Set (Matrix n n k) := {A | ∀ i j, A i j ∈ 𝒪[k]} with hK
  have hKo : IsOpen K := SplitFlip.isOpen_intMatrix
  have hKc : IsCompact K := SplitFlip.isCompact_intMatrix
  have h0 : volM ν n n K ≠ 0 := (hKo.measure_pos _ ⟨0, fun _ _ => zero_mem _⟩).ne'
  have ht : volM ν n n K ≠ ⊤ := hKc.measure_lt_top.ne
  have hr : (volM ν n n).real K ≠ 0 := by simp [Measure.real, ENNReal.toReal_eq_zero_iff, h0, ht]
  have key := integral_comp_mul_mul_volM ν (1 : GL n k) h (K.indicator fun _ => (1 : ℂ))
  have h1 : ∫ x, K.indicator (fun _ => (1 : ℂ)) (h.val * x * (1 : GL n k).val) ∂(volM ν n n) =
      ∫ x, K.indicator (fun _ => (1 : ℂ)) x ∂((volM ν n n).map e) := by
    rw [integral_map c1.measurable.aemeasurable
      (stronglyMeasurable_const.indicator hKo.measurableSet).aestronglyMeasurable]
    simp only [Units.val_one, Matrix.mul_one]
    rfl
  rw [h1, hc, integral_smul_nnreal_measure, integral_indicator_const _ hKo.measurableSet, map_one, nabs_one,
    Real.one_rpow, mul_one] at key
  have h2 : (c : ℝ) = nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card n : ℝ)) := by
    refine mul_right_cancel₀ hr ?_
    simp only [NNReal.smul_def, smul_smul, Complex.real_smul, mul_one] at key
    exact_mod_cast key
  rw [hc, ← h2, ENNReal.ofReal_coe_nnreal]
  rfl

omit [MeasurableSpace k] [BorelSpace k] in
theorem continuous_density_volGL : Continuous fun g : GL n k =>
    ENNReal.ofReal (nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card n : ℝ))) :=
  (((isLocallyConstant_nabs k).comp_continuous Matrix.GeneralLinearGroup.continuous_det).comp
    (fun t : ℝ => ENNReal.ofReal (t ^ (-(Fintype.card n : ℝ))))).continuous

theorem isMulLeftInvariant_volGL : (volGL ν n).IsMulLeftInvariant := by
  haveI := secondCountable k
  haveI : BorelSpace (Matrix n n k) := inferInstanceAs (BorelSpace (n → n → k))
  have hE := Model.measurableEmbedding_val (k := k) n
  have hd := (continuous_density_volGL (k := k) (n := n)).measurable
  set μ := (volM ν n n).comap (fun g : GL n k => g.val) with hμ
  set d := fun g : GL n k =>
    ENNReal.ofReal (nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card n : ℝ))) with hdd
  have dmul : ∀ g h, d (g * h) = d g * d h := fun g h => by
    simp only [hdd, map_mul, nabs_mul]
    rw [Real.mul_rpow (nabs_pos' _).le (nabs_pos' _).le,
      ENNReal.ofReal_mul (Real.rpow_nonneg (nabs_pos' _).le _)]
  have done' : d 1 = 1 := by simp [hdd, nabs_one]
  have hm : ∀ h : GL n k, μ.map (fun x => h * x) = d h • μ := fun h => by
    ext s hs
    have cm : Measurable fun x : Matrix n n k => h.val * x :=
      (continuous_const.matrix_mul continuous_id).measurable
    rw [Measure.map_apply (measurable_const_mul h) hs, Measure.smul_apply, hE.comap_apply, hE.comap_apply,
      ← Measure.smul_apply, ← map_mul_left_volM ν h, Measure.map_apply cm (hE.measurableSet_image.2 hs)]
    congr 1
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨h * g, hg, rfl⟩
    · rintro ⟨g, hg, e⟩
      refine ⟨h⁻¹ * g, by simpa using hg, ?_⟩
      have e' : g.val = h.val * x := e
      simp only [Units.val_mul, e', ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  refine ⟨fun h => ?_⟩
  ext s hs
  have hs' := measurable_const_mul h hs
  change (μ.withDensity d).map _ s = μ.withDensity d s
  rw [Measure.map_apply (measurable_const_mul h) hs, withDensity_apply _ hs', withDensity_apply _ hs,
    ← lintegral_indicator hs', ← lintegral_indicator hs]
  have e1 : ∀ x, ((fun x => h * x) ⁻¹' s).indicator d x = d h⁻¹ * s.indicator d (h * x) := fun x => by
    by_cases hx : h * x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ (fun x => h * x) ⁻¹' s from hx), ← dmul,
        inv_mul_cancel_left]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ (fun x => h * x) ⁻¹' s from hx),
        mul_zero]
  simp_rw [e1]
  rw [lintegral_const_mul _ (f := fun a => s.indicator d (h * a))
      ((hd.indicator hs).comp (measurable_const_mul h)),
    ← lintegral_map (hd.indicator hs) (measurable_const_mul h), hm, lintegral_smul_measure, smul_eq_mul,
    ← mul_assoc, ← dmul, inv_mul_cancel, done', one_mul]

theorem volGL_KO : volGL ν n (KO k n) = volM ν n n ((fun g : GL n k => g.val) '' (KO k n)) := by
  have hE := Model.measurableEmbedding_val (k := k) n
  have hs := (SplitFlip.isOpen_KO (k := k) (n := n)).measurableSet
  unfold volGL
  rw [withDensity_apply _ hs, setLIntegral_congr_fun hs (g := fun _ => 1), setLIntegral_one, hE.comap_apply]
  rintro _ ⟨u, rfl⟩
  have h1 : nabs k (Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u)) = 1 := by
    rw [nabs_eq_one_iff]
    have : ((Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u) : kˣ) : k) = algebraMap 𝒪[k] k u.val.det :=
      ((algebraMap 𝒪[k] k).map_det u.val).symm
    rw [this]
    exact (Valuation.integer.integers (valuation k)).one_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit)
  simp only [h1, Real.one_rpow, ENNReal.ofReal_one]

theorem isHaarMeasure_volGL : (volGL ν n).IsHaarMeasure := by
  haveI := secondCountable k
  haveI := t2Space k
  haveI : (volM ν n n).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI := isMulLeftInvariant_volGL (n := n) ν
  have ho := SplitFlip.isOpen_KO (k := k) (n := n)
  have hc := SplitFlip.isCompact_KO (k := k) (n := n)
  have hoe : Topology.IsOpenEmbedding (fun g : GL n k => g.val) := by
    refine ⟨SplitFlip.isEmbedding_val_GL, ?_⟩
    have : Set.range (fun g : GL n k => g.val) = {x : Matrix n n k | x.det ≠ 0} := by
      ext x
      simp only [Set.mem_range, Set.mem_setOf_eq]
      rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
      rfl
    rw [this]
    exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  refine Measure.isHaarMeasure_of_isCompact_nonempty_interior _ _ hc
    (by rw [ho.interior_eq]; exact ⟨1, one_mem _⟩) ?_ ?_
  · rw [volGL_KO]
    exact ((hoe.isOpenMap _ ho).measure_pos _ ⟨_, 1, one_mem _, rfl⟩).ne'
  · rw [volGL_KO]
    exact (hc.image hoe.continuous).measure_lt_top.ne

theorem volGL_haar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure], BorelSpace (GL n k) ∧ LocallyCompactSpace (GL n k) ∧ SecondCountableTopology (GL n k) ∧ IsCompact (KO k n : Set (GL n k)) ∧ IsOpen (KO k n : Set (GL n k)) ∧ IsOpen (KOne k n : Set (GL n k)) ∧ (volGL ν n).IsHaarMeasure ∧ (volGL ν n).IsMulRightInvariant :=
  fun _ _ _ _ _ _ _ n _ _ ν _ =>
    haveI := isHaarMeasure_volGL (n := n) ν
    ⟨SplitFlip.borel_GL, SplitFlip.locallyCompact_GL, SplitFlip.secondCountable_GL, SplitFlip.isCompact_KO,
      SplitFlip.isOpen_KO, StepData.isOpen_KOne, this, SplitFlip.isMulRightInvariant_of_haar _⟩

end GlobalTheory.SplitWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenSetOfLeRank
section
open Matrix Topology

namespace GlobalTheory

theorem exists_mul_mul_eq_one_of_le_rank {k : Type} [Field k] {m n : Type} [Fintype m] [Fintype n]
    {κ : ℕ} (x : Matrix m n k) (h : κ ≤ x.rank) :
    ∃ (A : Matrix (Fin κ) m k) (B : Matrix n (Fin κ) k), A * x * B = 1 := by
  classical
  obtain ⟨w, hw⟩ := exists_linearIndependent_of_le_finrank
    (R := k) (M := LinearMap.range x.mulVecLin) (n := κ) h
  choose v hv using fun i => (w i).2
  let B : Matrix n (Fin κ) k := Matrix.of fun j i => v i j
  have hw' : LinearIndependent k (fun i => (w i : m → k)) :=
    hw.map' (LinearMap.range x.mulVecLin).subtype (Submodule.ker_subtype _)
  have hcol : (x * B).col = fun i => (w i : m → k) := by
    funext i j
    rw [← hv i]
    simp [B, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.col]
  have hinj : Function.Injective (x * B).mulVec := by
    rw [Matrix.mulVec_injective_iff, hcol]
    exact hw'
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' (x * B))
    (LinearMap.ker_eq_bot.2 (fun a b hab => hinj (by simpa only [Matrix.toLin'_apply] using hab)))
  refine ⟨LinearMap.toMatrix' g, B, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  rw [Matrix.mul_assoc, this]

theorem isOpen_setOf_le_rank (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    [T1Space k] (m n : Type) [Fintype m] [Fintype n] (κ : ℕ) :
    IsOpen {x : Matrix m n k | κ ≤ x.rank} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨A, B, hAB⟩ := exists_mul_mul_eq_one_of_le_rank x hx
  refine ⟨{y | (A * y * B).det ≠ 0}, ?_, ?_, ?_⟩
  · intro y hy
    have hu : IsUnit (A * y * B) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hy)
    have h1 := Matrix.rank_of_isUnit _ hu
    rw [Fintype.card_fin] at h1
    change κ ≤ y.rank
    rw [← h1]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · have hc : Continuous fun y : Matrix m n k => (A * y * B).det :=
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_det
    exact isOpen_ne.preimage hc
  · simp [hAB]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSplitThetaGridPathFlipGridPathAtSquare
section
open GlobalTheory.SplitFlip

namespace GlobalTheory.FlipPathPairwise

def srcDiff (e : Edge) : ℤ := (e.src.1 : ℤ) - e.src.2

theorem srcDiff_of_join {e e' : Edge} (h : e.tgt = e'.src) : srcDiff e' = srcDiff e + 1 := by
  cases e <;> cases e' <;> simp only [Edge.src, Edge.tgt, Prod.mk.injEq] at h <;>
    simp only [srcDiff, Edge.src] <;> omega

theorem pairwise_of_isPath {γ : List Edge} (h : IsPath γ) :
    γ.Pairwise fun a b => srcDiff a < srcDiff b := by
  have h' : γ.IsChain fun a b => srcDiff a < srcDiff b :=
    List.IsChain.imp (fun a b hab => by rw [srcDiff_of_join hab]; omega) h
  haveI : Trans (fun a b : Edge => srcDiff a < srcDiff b) (fun a b => srcDiff a < srcDiff b)
      (fun a b => srcDiff a < srcDiff b) := ⟨fun h1 h2 => lt_trans h1 h2⟩
  exact h'.pairwise

end GlobalTheory.FlipPathPairwise


open GlobalTheory.FlipPathPairwise in
theorem GlobalTheory.SplitFlip.isPath_flipPath : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ →
    IsPath (flipPath i j γ) := by
  intro γ i j hγ hP
  obtain ⟨s, t, rfl⟩ := hP
  have hpw := pairwise_of_isPath hγ
  rw [List.pairwise_append, List.pairwise_append] at hpw
  have hs : ∀ a ∈ s, a ≠ .theta i j ∧ a ≠ .ex i j := fun a ha => by
    have h1 := hpw.1.2.2 a ha (.theta i j) (by simp)
    have h2 := hpw.1.2.2 a ha (.ex i j) (by simp)
    exact ⟨fun h => by subst h; exact lt_irrefl _ h1, fun h => by subst h; exact lt_irrefl _ h2⟩
  have ht : ∀ a ∈ t, a ≠ .theta i j ∧ a ≠ .ex i j := fun a ha => by
    have h1 := hpw.2.2 (.theta i j) (by simp) a ha
    have h2 := hpw.2.2 (.ex i j) (by simp) a ha
    exact ⟨fun h => by subst h; exact lt_irrefl _ h1, fun h => by subst h; exact lt_irrefl _ h2⟩
  have hflip : flipPath i j (s ++ [Edge.theta i j, Edge.ex i j] ++ t) =
      s ++ Edge.ex i (j + 1) :: Edge.theta (i + 1) j :: t := by
    have key : ∀ l : List Edge, (∀ a ∈ l, a ≠ .theta i j ∧ a ≠ .ex i j) →
        l.map (fun e => if e = .theta i j then Edge.ex i (j + 1) else if e = .ex i j then .theta (i + 1) j else e)
          = l := fun l hl =>
      (List.map_congr_left fun a ha => by simp [hl a ha]).trans (List.map_id l)
    unfold flipPath
    rw [List.map_append, List.map_append, key s hs, key t ht]
    simp
  rw [hflip]
  unfold IsPath at hγ ⊢
  rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append, List.isChain_append] at hγ
  obtain ⟨h1, h2, h3⟩ := hγ
  rw [List.isChain_cons_cons] at h2
  obtain ⟨-, h2⟩ := h2
  rw [List.isChain_cons] at h2
  refine List.isChain_append.2 ⟨h1, ?_, ?_⟩
  · rw [List.isChain_cons_cons, List.isChain_cons]
    exact ⟨rfl, h2.1, h2.2⟩
  · intro x hx y hy
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    exact h3 x hx (Edge.theta i j) rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftColumnsMulVecInjectiveOfRankEqCard
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

namespace GlobalTheory


open Matrix Topology Module in
theorem _root_.GlobalTheory.mulVec_firstCols_eq_zero_of_rank_eq_card :
    ∀ (k m a b n : Type) [Field k] [Fintype m] [Fintype a] [Fintype b] [Fintype n] (e : a ⊕ b ≃ n) (x : Matrix m n k), x.rank = Fintype.card a → (∀ i j, x i (e (Sum.inr j)) = 0) → ∀ v : a → k, (x.submatrix id (fun i => e (Sum.inl i))) *ᵥ v = 0 → v = 0 := by
  intro k m a b n _ _ _ _ _ e x hx hz v hv
  classical
  set x' := x.submatrix id (fun i => e (Sum.inl i))
  let Q : Matrix n a k := Matrix.of fun l i => if l = e (Sum.inl i) then 1 else 0
  let P : Matrix a n k := Matrix.of fun i l => if l = e (Sum.inl i) then 1 else 0
  have hQ : x' = x * Q := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [x', Q, Matrix.of_apply, Matrix.submatrix_apply, id, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hP : x = x' * P := by
    ext i l
    obtain ⟨t, rfl⟩ := e.surjective l
    rcases t with t | t
    · rw [Matrix.mul_apply]
      simp only [x', P, Matrix.of_apply, Matrix.submatrix_apply, id, mul_ite, mul_one, mul_zero,
        EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    · rw [Matrix.mul_apply]
      simp [x', P, hz]
  have hr : x'.rank = Fintype.card a := by
    apply le_antisymm
    · rw [← hx, hQ]; exact Matrix.rank_mul_le_left _ _
    · rw [← hx, hP]; exact Matrix.rank_mul_le_left _ _
  have hrn := LinearMap.finrank_range_add_finrank_ker x'.mulVecLin
  have hxr : finrank k (LinearMap.range x'.mulVecLin) = Fintype.card a := hr
  rw [hxr, finrank_fintype_fun_eq_card] at hrn
  have hker : LinearMap.ker x'.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
  have hvk : v ∈ LinearMap.ker x'.mulVecLin := hv
  rw [hker] at hvk
  exact (Submodule.mem_bot k).1 hvk

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviEmbMulSingle
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix MeasureTheory

namespace GlobalTheory.InertSupp

section Blocks

variable {n : Type} [Fintype n] [DecidableEq n]


open ValuativeRel Matrix MeasureTheory in
variable {n : Type} [Fintype n] [DecidableEq n] in
omit [DecidableEq n] in
theorem _root_.GlobalTheory.InertSupp.exists_blocks (c : n → ℤ) :
    ∃ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ n),
    ∀ i j, _root_.GlobalTheory.SmGL.blk e i < _root_.GlobalTheory.SmGL.blk e j ↔ c i < c j := by
  classical
  let S : Finset ℤ := Finset.univ.image c
  let o := S.orderIsoOfFin rfl
  let φ : n → Fin S.card := fun i => o.symm ⟨c i, Finset.mem_image_of_mem c (Finset.mem_univ i)⟩
  refine ⟨S.card, fun a => Fintype.card {i // φ i = a},
    (Equiv.sigmaCongrRight fun a => (Fintype.equivFin {i // φ i = a}).symm).trans
      (Equiv.sigmaFiberEquiv φ), ?_⟩
  intro i j
  have key : ∀ x, (((Equiv.sigmaCongrRight fun a => (Fintype.equivFin {i // φ i = a}).symm).trans
      (Equiv.sigmaFiberEquiv φ)).symm x).1 = φ x := fun x => rfl
  unfold _root_.GlobalTheory.SmGL.blk
  rw [key, key]
  simp only [φ, OrderIso.lt_iff_lt, Subtype.mk_lt_mk]

variable (R : Type) [CommRing R]

def unipOf (c : n → ℤ) : Subgroup (GL n R) :=
  (unipRad R (exists_blocks c).choose_spec.choose_spec.choose).copy
    {g | ∀ i j, ¬ c i < c j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j} (by
      ext g
      simp only [SetLike.mem_coe, CuspMax.mem_unipRad_iff_entries,
        (exists_blocks c).choose_spec.choose_spec.choose_spec, Set.mem_setOf_eq])

variable {R}


open ValuativeRel Matrix MeasureTheory in
variable {n : Type} [Fintype n] [DecidableEq n] in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.InertSupp.mem_unipOf {c : n → ℤ} {g : GL n R} :
    g ∈ _root_.GlobalTheory.InertSupp.unipOf R c ↔
      ∀ i j, ¬ c i < c j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j :=
  Iff.rfl

variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]


open ValuativeRel Matrix MeasureTheory in
variable {n : Type} [Fintype n] [DecidableEq n] in
variable (R : Type) [CommRing R] in
variable {R} in
variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] in
variable (R) in
theorem _root_.GlobalTheory.InertSupp.unipRad_eq_unipOf {e : (Σ a, m a) ≃ n}
    {c : n → ℤ} (h : ∀ i j, _root_.GlobalTheory.SmGL.blk e i < _root_.GlobalTheory.SmGL.blk e j ↔ c i < c j) :
    _root_.GlobalTheory.SmGL.unipRad R e = _root_.GlobalTheory.InertSupp.unipOf R c := by
  ext g
  rw [_root_.GlobalTheory.InertSupp.mem_unipOf, _root_.GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries]
  simp only [h]

end Blocks

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V]

variable [MeasurableSpace k] [BorelSpace k]

def zetaIntegrand (Φ : Matrix n n k → ℂ) (c : GL n k → ℂ) (s : ℂ) (g : GL n k) : ℂ :=
  Φ g.val * c g * (absPow k (s + ((Fintype.card n : ℂ) - 1) / 2) (GeneralLinearGroup.det g) : ℂ)

end Local

end GlobalTheory.InertSupp
end
end

