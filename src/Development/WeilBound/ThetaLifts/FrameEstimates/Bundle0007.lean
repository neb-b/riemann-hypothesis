module

public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0005
public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.LeHeightOfIsTorusElt
section
noncomputable section

namespace PositivityTheory.ThKEst.Sieg

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.SiegelSet GlobalTheory.Orb Matrix
open Formalism.UG (cT)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem realAd_snd (t : ℝ) : (realAd F t).2 = 0 := rfl

theorem realAd_inf [IsTotallyReal F] (w : InfinitePlace F) (t : ℝ) :
    InfinitePlace.Completion.extensionEmbedding w ((realAd F t).1 w) = t := by
  have hw := IsTotallyReal.isReal w
  have e := congrArg (fun z => z.1 ⟨w, hw⟩) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply
    (algebraMap ℝ (mixedEmbedding.mixedSpace F) t))
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
  exact congrArg _ e

theorem rId_snd (t : ℝ) : (rId F t).2 = 1 := add_zero _

theorem rId_inf [IsTotallyReal F] (w : InfinitePlace F) (t : ℝ) :
    InfinitePlace.Completion.extensionEmbedding w ((rId F t).1 w) = Real.exp t := by
  change InfinitePlace.Completion.extensionEmbedding w (1 + (realAd F (Real.exp t - 1)).1 w) = _
  rw [map_add (f := _), map_one, realAd_inf]
  push_cast
  ring

theorem rId_add [IsTotallyReal F] (s t : ℝ) : rId F (s + t) = rId F s * rId F t := by
  refine Prod.ext (funext fun w => (InfinitePlace.Completion.extensionEmbedding w).injective ?_) ?_
  · change _ = InfinitePlace.Completion.extensionEmbedding w ((rId F s).1 w * (rId F t).1 w)
    rw [map_mul, rId_inf, rId_inf, rId_inf, Real.exp_add, Complex.ofReal_mul]
  · change _ = (rId F s).2 * (rId F t).2
    rw [rId_snd, rId_snd, rId_snd, mul_one]

theorem rId_zero' : rId F 0 = 1 := by
  rw [rId, Real.exp_zero, sub_self, realAd, map_zero, map_zero, map_zero]
  exact add_zero (1 : AF F)

theorem continuous_rId [IsTotallyReal F] : Continuous (rId F) := by
  refine Continuous.prodMk (f := fun t => (rId F t).1) (g := fun t => (rId F t).2) (continuous_pi fun w => ?_) ?_
  · refine (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.continuous_iff.2 ?_
    have : (InfinitePlace.Completion.extensionEmbedding w) ∘ (fun t => (rId F t).1 w) = fun t => (Real.exp t : ℂ) :=
      funext fun t => rId_inf w t
    rw [this]
    fun_prop
  · simp only [rId_snd]
    exact continuous_const

variable {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

omit [NumberField F] [NumberField E] in
theorem yx_eq_one (hs : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    cT (σ : E →+* E) Y * J * X = 1 := by
  have cc : cT (σ : E →+* E) (cT (σ : E →+* E) X) = X := Matrix.ext fun i j => hs _
  have cJ : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
  have := congrArg (cT (σ : E →+* E)) hW.xy
  rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, cJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this

omit [NumberField F] [NumberField E] in
theorem two_mul_le_of_wittFrame (hs : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) : 2 * r ≤ n := by
  have e : Matrix.fromRows (cT (σ : E →+* E) Y * J) (cT (σ : E →+* E) X * J) * Matrix.fromCols X Y = 1 := by
    rw [Matrix.fromRows_mul_fromCols, yx_eq_one hs hJ hW, hW.xx, hW.yy, hW.xy, Matrix.fromBlocks_one]
  have e2 := congrArg Matrix.rank e
  rw [Matrix.rank_one, Fintype.card_sum, Fintype.card_fin] at e2
  have := (Matrix.rank_mul_le_right _ _).trans' e2.symm.le |>.trans (Matrix.rank_le_card_height _)
  rw [Fintype.card_fin] at this
  omega


omit [NumberField F] [NumberField E] in
theorem ext_of_frame (hs : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {A : Type} [CommRing A]
    (φ : E →+* A) {m m' : Matrix (Fin n) (Fin n) A} (h1 : m * X.map φ = m' * X.map φ) (h2 : m * Y.map φ = m' * Y.map φ)
    (h3 : ∀ z : Fin n → E, (cT (σ : E →+* E) X * J) *ᵥ z = 0 → (cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
      m *ᵥ (fun i => φ (z i)) = m' *ᵥ fun i => φ (z i)) : m = m' := by
  set P : Matrix (Fin n) (Fin n) E := 1 - X * (cT (σ : E →+* E) Y * J) - Y * (cT (σ : E →+* E) X * J) with hP
  have p1 : cT (σ : E →+* E) X * J * P = 0 := by
    simp only [hP, Matrix.mul_sub, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, hW.xx, hW.xy]
    simp
  have p2 : cT (σ : E →+* E) Y * J * P = 0 := by
    simp only [hP, Matrix.mul_sub, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, hW.yy, yx_eq_one hs hJ hW]
    simp
  have h4 : m * P.map φ = m' * P.map φ := Matrix.ext fun i j =>
    congrFun (h3 (fun k => P k j) (funext fun k => congrFun (congrFun p1 k) j)
      (funext fun k => congrFun (congrFun p2 k) j)) i
  have e : (1 : Matrix (Fin n) (Fin n) A) =
      P.map φ + X.map φ * (cT (σ : E →+* E) Y * J).map φ + Y.map φ * (cT (σ : E →+* E) X * J).map φ := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add φ), ← Matrix.map_add _ (map_add φ), hP,
      ← Matrix.map_one φ (map_zero φ) (map_one φ)]
    congr 1
    abel
  rw [← Matrix.mul_one m, ← Matrix.mul_one m', e]
  simp only [Matrix.mul_add, ← Matrix.mul_assoc, h1, h2, h4]

theorem isTorusElt_unique (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {t : Fin r → ℝ}
    {a a' : GAd σ J} (ha : IsTorusElt σ J X Y t a) (ha' : IsTorusElt σ J X Y t a') : a = a' := by
  refine GAd_ext σ J (fun w => ?_) fun v => by
    rw [mem_infPts_iff_forall.1 ha.1 v, mem_infPts_iff_forall.1 ha'.1 v]
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  apply (archEquiv J h τ).injective
  refine Subtype.ext (Units.ext ?_)
  rw [← archMat_eq_archEquiv J h, ← archMat_eq_archEquiv J h]
  exact ext_of_frame (sigma_sigma h) hJ hW τ.1 ((ha.2 w τ).1.trans (ha'.2 w τ).1.symm)
    ((ha.2 w τ).2.1.trans (ha'.2 w τ).2.1.symm) fun z h1 h2 =>
      ((ha.2 w τ).2.2 z h1 h2).trans ((ha'.2 w τ).2.2 z h1 h2).symm

theorem le_height_of_isTorusElt (hW : IsWittFrame σ J X Y) {t : Fin r → ℝ} {a : GAd σ J}
    (ha : IsTorusElt σ J X Y t a) (i : Fin r) : t i ≤ height σ J a := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  set M := archMat σ J τ (projArch σ J w a) with hM
  have h1 : opNorm M ≤ height σ J a :=
    ((normInf_le_iff F w).1 (le_htOf (normInf F w) (matHom _ σ J (projArch σ J w a))) τ).trans (htInf_le_height σ J w a)
  let v : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 fun k => τ.1 (X k i)
  have hv : v ≠ 0 := fun e => by
    have hx : ∀ k, X k i = 0 := fun k => τ.1.injective ((congrArg (fun z : EuclideanSpace ℂ (Fin n) => z k) e).trans
      (map_zero _).symm)
    have := congrFun (congrFun hW.xy i) i
    simp [Matrix.mul_apply, cT, hx] at this
  have h2 : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) M v = (t i : ℂ) • v := by
    ext k
    have := congrFun (congrFun (ha.2 w τ).1 k) i
    rw [mul_diagonal, mul_comm] at this
    exact this
  have h3 := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) M).le_opNorm v
  rw [h2, norm_smul, Complex.norm_real] at h3
  have h4 := le_of_mul_le_mul_right h3 (norm_pos_iff.2 hv)
  exact (le_abs_self _).trans (h4.trans (show ((opNorm M : ℝ≥0) : ℝ) ≤ _ from h1))

theorem exists_torus (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    ∃ a : (Fin r → ℝ) → GAd σ J, (∀ s t, a (s + t) = a s * a t) ∧ Continuous a ∧
      (∀ t, IsTorusElt σ J X Y (fun i => Real.exp (t i)) (a t)) ∧ ∀ t,
      (matHom _ σ J (a t)).1 * adMat F X = adMat F X * diagonal (fun i => algebraMap (AF F) (AE F E) (rId F (t i))) ∧
      (matHom _ σ J (a t)).1 * adMat F Y = adMat F Y * diagonal (fun i => algebraMap (AF F) (AE F E) (rId F (-t i))) ∧
      ∀ z : Fin n → E, (cT (σ : E →+* E) X * J) *ᵥ z = 0 → (cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
        (matHom _ σ J (a t)).1 *ᵥ incV F z = incV F z := by
  have := h.1
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  let ι := algebraMap (AF F) (AE F E)
  let d : ℝ → (AE F E)ˣ := fun x => ⟨ι (rId F x), ι (rId F (-x)),
    by rw [← map_mul, ← rId_add, add_neg_cancel, rId_zero', map_one],
    by rw [← map_mul, ← rId_add, neg_add_cancel, rId_zero', map_one]⟩
  have c1 : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), cT (sigR (AF F) σ) (adMat F Z) = adMat F (cT (σ : E →+* E) Z) :=
    fun Z => rfl
  have c2 : ∀ Z Z' : Matrix (Fin n) (Fin r) E, (cT (sigR (AF F) σ) (adMat F Z) * JR (F := F) (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F Z' =
      adMat F (cT (σ : E →+* E) Z * J * Z') := fun Z Z' => by
    rw [c1]; simp only [adMat, JR, Matrix.map_mul]
  have key := fun t : Fin r → ℝ => exists_unit_torus (s := sigR (AF F) σ) (J := JR (F := F) (AF F) J) (X := adMat F X)
    (Y := adMat F Y)
    (fun a => by
      induction a using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (sigma_sigma h x))
    ((c1 J).trans (congrArg (adMat F) (Matrix.ext fun i j => hJ.1 i j)))
    ((c2 X X).trans (hW.xx ▸ Matrix.map_zero _ (map_zero _))) ((c2 Y Y).trans (hW.yy ▸ Matrix.map_zero _ (map_zero _)))
    ((c2 X Y).trans (hW.xy ▸ Matrix.map_one _ (map_zero _) (map_one _))) (fun i => d (t i))
    (fun i => congrArg (rId F (t i) ⊗ₜ[F] ·) (map_one σ))
  choose m hm hX hY he using key
  have hZ : ∀ t, ∀ z : Fin n → E, (cT (σ : E →+* E) X * J) *ᵥ z = 0 → (cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
      (m t).1 *ᵥ incV F z = incV F z := fun t z hz hz' => by
    have h4 : ∀ Z : Matrix (Fin n) (Fin r) E, (cT (σ : E →+* E) Z * J) *ᵥ z = 0 →
        (cT (sigR (AF F) σ) (adMat F Z) * JR (F := F) (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) *ᵥ incV F z = 0 :=
      fun Z hZ => funext fun i => by
        have e : (cT (sigR (AF F) σ) (adMat F Z) * JR (F := F) (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) =
          (cT (σ : E →+* E) Z * J).map (inclR (F := F) (AF F)) := by
          rw [c1, Matrix.map_mul]; rfl
        rw [e]
        exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ z i).symm.trans (by rw [hZ]; exact map_zero _)
    rw [he, add_mulVec, add_mulVec, ← mulVec_mulVec, h4 Y hz', mulVec_zero, ← mulVec_mulVec, h4 X hz]
    simp
  have hadd : ∀ s t, m (s + t) = m s * m t := fun s t => by
    refine Units.ext (ext_of_frame (sigma_sigma h) hJ hW (inclR (F := F) (AF F)) ?_ ?_ fun z h1 h2 => ?_)
    · rw [Units.val_mul, Matrix.mul_assoc, hX, hX, ← Matrix.mul_assoc, hX, Matrix.mul_assoc, diagonal_mul_diagonal]
      exact congrArg (_ * diagonal ·) (funext fun i => (congrArg ι (rId_add _ _)).trans (map_mul ι _ _))
    · rw [Units.val_mul, Matrix.mul_assoc, hY, hY, ← Matrix.mul_assoc, hY, Matrix.mul_assoc, diagonal_mul_diagonal]
      exact congrArg (_ * diagonal ·) (funext fun i => (congrArg ι ((congrArg (rId F) (neg_add _ _)).trans
        (rId_add _ _))).trans (map_mul ι _ _))
    · exact (hZ _ z h1 h2).trans (by
        rw [Units.val_mul, ← mulVec_mulVec]
        exact ((congrArg _ (hZ t z h1 h2)).trans (hZ s z h1 h2)).symm)
  have h0 : m 0 = 1 := by simpa using hadd 0 0
  have hinv : ∀ t, (m t)⁻¹ = m (-t) := fun t => inv_eq_of_mul_eq_one_right (by rw [← hadd, add_neg_cancel, h0])
  have hι : Continuous ι := continuous_algebraMap _ _
  have hc : Continuous fun t => (m t).1 := by
    simp only [he]
    refine Continuous.add (Continuous.add continuous_const (Continuous.matrix_mul (Continuous.matrix_mul continuous_const
      (Continuous.matrix_diagonal (continuous_pi fun i => ?_))) continuous_const))
      (Continuous.matrix_mul (Continuous.matrix_mul continuous_const
      (Continuous.matrix_diagonal (continuous_pi fun i => ?_))) continuous_const)
    · exact (hι.comp (continuous_rId.comp (continuous_apply i))).sub continuous_const
    · exact (hι.comp (continuous_rId.comp (continuous_apply i).neg)).sub continuous_const
  have hc' : Continuous m := Units.continuous_iff.2 ⟨hc, by simp only [hinv]; exact hc.comp continuous_neg⟩
  refine ⟨fun t => ⟨m t, hm t⟩, fun s t => Subtype.ext (hadd s t), hc'.subtype_mk _, fun t => ⟨?_, fun w τ => ?_⟩,
    fun t => ⟨hX t, hY t, hZ t⟩⟩
  · refine Units.ext (Matrix.ext fun i j => ?_)
    let ψ := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
    have h1 : ∀ x, ψ (d x).1 = 1 := fun x => congrArg (· ⊗ₜ[F] (1 : E)) (rId_snd (F := F) x)
    have h2 : ∀ x, ψ (d x)⁻¹.1 = 1 := fun x => congrArg (· ⊗ₜ[F] (1 : E)) (rId_snd (F := F) (-x))
    change ψ ((m t).1 i j) = (1 : Matrix (Fin n) (Fin n) _) i j
    rw [he]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.add_apply, Matrix.mul_apply (N := cT _ _ * _), mul_diagonal, map_add (f := _), map_sum, map_mul, map_sub, h1,
      h2, map_one, sub_self, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Matrix.one_apply, apply_ite ψ, map_zero]
  · let φ := (infEmb τ).comp (compInf F E w)
    have h0 : ∀ x : E, φ (inclR (F := F) (AF F) x) = τ.1 x := fun x => by
      change infEmb τ (evInf F w 1 ⊗ₜ[F] x) = _
      simp
    have h1 : ∀ x : ℝ, φ (ι (rId F x)) = Real.exp x := fun x => by
      change infEmb τ ((rId F x).1 w ⊗ₜ[F] 1) = _
      rw [infEmb_tmul, map_one, mul_one, rId_inf]
    have h2 : ∀ Z : Matrix (Fin n) (Fin r) E, (adMat F Z).map φ = Z.map τ.1 := fun Z => Matrix.ext fun i j => h0 _
    have h3 : archMat σ J τ (projArch σ J w ⟨m t, hm t⟩) = (m t).1.map φ := rfl
    rw [h3]
    refine ⟨?_, ?_, fun z hz hz' => ?_⟩
    · rw [← h2, ← Matrix.map_mul, hX, Matrix.map_mul, diagonal_map (map_zero _)]
      exact congrArg (_ * diagonal ·) (funext fun i => h1 _)
    · rw [← h2, ← Matrix.map_mul, hY, Matrix.map_mul, diagonal_map (map_zero _)]
      exact congrArg (_ * diagonal ·) (funext fun i => (h1 (-t i)).trans (by rw [Real.exp_neg, Complex.ofReal_inv]))
    · funext i
      rw [show (fun i => τ.1 (z i)) = φ ∘ incV F z from funext fun i => (h0 _).symm,
        ← RingHom.map_mulVec, hZ t z hz hz']
      exact h0 _

end PositivityTheory.ThKEst.Sieg

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.LevelA
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace levelStructure

open LatticeQuotientMeasure PositivityTheory.ThKF0.Grow PositivityTheory.ThKF0.Grow.Fi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem finiteAdeleIdempotentOfF_mul_self (a : AF F) : e0 F * a = ((0, a.2) : Ainf F × Af F) := Prod.ext (zero_mul a.1) (one_mul a.2)

theorem int_mul {a b : Af F} (ha : Int' a) (hb : Int' b) : Int' (a * b) := fun v => mul_mem (ha v) (hb v)

theorem int_add {a b : Af F} (ha : Int' a) (hb : Int' b) : Int' (a + b) := fun v => add_mem (ha v) (hb v)

theorem int_neg {a : Af F} (ha : Int' a) : Int' (-a) := fun v => neg_mem (ha v)

theorem int_zero : Int' (0 : Af F) := fun _ => zero_mem _

theorem int_sum {ι : Type} (s : Finset ι) {a : ι → Af F} (ha : ∀ i, Int' (a i)) : Int' (∑ i ∈ s, a i) :=
  Finset.sum_induction _ _ (fun _ _ => int_add) int_zero fun i _ => ha i


variable (E) in
theorem exists_lattice (V : Set (AE F E)) (hV : V ∈ 𝓝 (0 : AE F E)) :
    ∃ Λ : AddSubgroup (AE F E), (∀ z ∈ Λ, ∀ z' ∈ Λ, z * z' ∈ Λ) ∧ (Λ : Set (AE F E)) ⊆ V ∧
      ∃ V' ∈ 𝓝 (0 : AE F E), ∀ z ∈ V', e0 F • z = z → z ∈ Λ := by
  classical
  have := ring_AE F E
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hs : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  let b := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)
  let c : AE F E → Fin (Module.finrank F E) → Af F := fun z i => (b.repr z i).2
  have hc : Continuous c := continuous_pi fun i =>
    continuous_snd.comp (IsModuleTopology.continuous_of_linearMap (b.coord i))
  let j : (Fin (Module.finrank F E) → Af F) → AE F E := fun y => ∑ i, (show AF F from ((0, y i) : Ainf F × Af F)) • b i
  have hj : Continuous j := continuous_finsetSum _ fun i _ =>
    (show Continuous fun y : Fin (Module.finrank F E) → Af F => (show AF F from ((0, y i) : Ainf F × Af F)) from
      continuous_const.prodMk (continuous_apply i)).smul continuous_const
  have hj0 : j 0 = 0 := Finset.sum_eq_zero fun i _ => zero_smul (AF F) (b i)
  have hO : {a : Af F | Int' a} ∈ 𝓝 (0 : Af F) := (GlobalTheory.AdLat.OpenLat.isOpen_integral F).mem_nhds int_zero
  have h1 : j ⁻¹' V ∈ 𝓝 0 := hj.continuousAt.preimage_mem_nhds (hj0 ▸ hV)
  obtain ⟨N₁, hN₁, h₁⟩ := exists_pi _ h1
  have h2 : ∀ᶠ a in 𝓝 (0 : Af F), ∀ i j k, Int' (a * c (b i * b j) k) :=
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_all.2 fun k =>
      ((continuous_mul_const (c (b i * b j) k)).tendsto' 0 0 (zero_mul _)).eventually hO
  obtain ⟨N₂, hN₂, h₂⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ h2
  let Λ : AddSubgroup (AE F E) :=
    { carrier := {z | e0 F • z = z ∧ ∃ a : Fin (Module.finrank F E) → Af F, (∀ i, Int' (a i)) ∧ c z = (N₁ * N₂) • a}
      zero_mem' := ⟨smul_zero _, 0, fun _ => int_zero, by funext i; simp [c]⟩
      add_mem' := fun {x y} hx hy => by
        obtain ⟨h, a, ha, e⟩ := hx
        obtain ⟨h', a', ha', e'⟩ := hy
        refine ⟨by rw [smul_add, h, h'], a + a', fun i => int_add (ha i) (ha' i), ?_⟩
        rw [smul_add, ← e, ← e']
        funext i
        simp only [c, map_add (f := _)]
        rfl
      neg_mem' := fun {x} hx => by
        obtain ⟨h, a, ha, e⟩ := hx
        refine ⟨by rw [smul_neg, h], -a, fun i => int_neg (ha i), ?_⟩
        rw [smul_neg, ← e]
        funext i
        simp only [c, map_neg]
        rfl }
  refine ⟨Λ, ?_, ?_, ?_⟩
  · rintro z ⟨h, a, ha, e⟩ z' ⟨h', a', ha', e'⟩
    refine ⟨by rw [← smul_mul_assoc, h], fun k => ∑ i, ∑ j, N₂ • (N₁ • (a i * a' j)) * c (b i * b j) k,
      fun k => int_sum _ fun i => int_sum _ fun j => h₂ _ ((int_mul (ha i) (ha' j)).nsmul N₁) i j k, ?_⟩
    funext k
    have e1 : c (z * z') k = ∑ i, ∑ j, c z i * c z' j * c (b i * b j) k := by
      have e1 : z * z' = ∑ i, ∑ j, (b.repr z i * b.repr z' j) • (b i * b j) := by
        conv_lhs => rw [← b.sum_repr z, ← b.sum_repr z', Finset.sum_mul_sum]
        simp only [smul_mul_smul_comm]
      change (RingHom.snd (Ainf F) (Af F) : AF F →+* Af F) (b.repr (z * z') k) = _
      rw [e1]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
      simp only [map_mul, c]
      rfl
    rw [e1, e, e', Pi.smul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_mul]
    ring
  · rintro z ⟨h, a, ha, e⟩
    have e1 : j (c z) = z := by
      conv_rhs => rw [← h, ← b.sum_repr z, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, finiteAdeleIdempotentOfF_mul_self]
    rw [← e1, e]
    exact h₁ _ (dvd_mul_right _ _) a ha
  · have hN : ((N₁ * N₂ : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 (Nat.mul_pos hN₁ hN₂).ne'
    let t : Af F := algebraMap F (Af F) ((N₁ * N₂ : ℕ) : F)⁻¹
    have h3 : ∀ᶠ z in 𝓝 (0 : AE F E), ∀ i, Int' (t * c z i) := eventually_all.2 fun i =>
      ((show Continuous fun z => t * c z i from continuous_const.mul ((continuous_apply i).comp hc)).tendsto' 0 0 (by
        have : c 0 i = 0 := by simp [c]
        rw [this, mul_zero])).eventually hO
    refine ⟨_, h3, fun z hz h => ⟨h, fun i => t * c z i, hz, funext fun i => ?_⟩⟩
    rw [Pi.smul_apply, nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap F (Af F)), ← map_mul, mul_inv_cancel₀ hN,
      map_one, one_mul]

variable {d : ℕ} {J : Matrix (Fin d) (Fin d) E}

def IsFin (u : UA σ J) : Prop := e0 F • (mat u - 1) = mat u - 1

omit [NumberField E] in
theorem IsFin.inv {u : UA σ J} (h : IsFin u) : IsFin u⁻¹ := by
  have e : mat u⁻¹ - 1 = -(mat u⁻¹ * (mat u - 1)) := by
    rw [mul_sub, show mat u⁻¹ * mat u = 1 from Units.inv_mul u.1, mul_one, neg_sub]
  unfold IsFin at h ⊢
  rw [e, smul_neg, ← Matrix.mul_smul, h]

theorem pow_near (U : Set (UA σ J)) (hU : U ∈ 𝓝 (1 : UA σ J)) :
    ∀ᶠ u in 𝓝 (1 : UA σ J), IsFin u → ∀ p : ℕ, u ^ p ∈ U := by
  classical
  have := ring_AE F E
  let L : Filter (UA σ J) := ⨅ V ∈ 𝓝 (0 : AE F E), 𝓟 {h | (∀ i j, (mat h - 1) i j ∈ V) ∧ ∀ i j, (mat h⁻¹ - 1) i j ∈ V}
  have ent : ∀ f : UA σ J → Matrix (Fin d) (Fin d) (AE F E),
      (∀ V ∈ 𝓝 (0 : AE F E), ∀ᶠ h in L, ∀ i j, (f h - 1) i j ∈ V) → Tendsto f L (𝓝 1) := fun f hf => by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => fun V hV => ?_
    have hc : Continuous fun z : AE F E => z + (1 : Matrix (Fin d) (Fin d) (AE F E)) i j :=
      continuous_id.add continuous_const
    rw [mem_map]
    filter_upwards [hf _ (hc.continuousAt.preimage_mem_nhds (by rwa [zero_add]))] with h hh
    simpa using hh i j
  have hL : L ≤ 𝓝 1 := by
    have : Tendsto (fun h : UA σ J => h) L (𝓝 1) := by
      refine tendsto_subtype_rng.2 (Units.isInducing_embedProduct.tendsto_nhds_iff.2 ?_)
      exact (ent mat fun V hV => mem_iInf_of_mem V (mem_iInf_of_mem hV fun h hh => hh.1)).prodMk_nhds
        ((MulOpposite.continuous_op.tendsto _).comp
          (ent (fun h => mat h⁻¹) fun V hV => mem_iInf_of_mem V (mem_iInf_of_mem hV fun h hh => hh.2)))
    exact this
  obtain ⟨V, hV, hVU⟩ : ∃ V ∈ 𝓝 (0 : AE F E),
      {h | (∀ i j, (mat h - 1) i j ∈ V) ∧ ∀ i j, (mat h⁻¹ - 1) i j ∈ V} ⊆ U := by
    refine (mem_biInf_of_directed ?_ ⟨_, univ_mem⟩).1 (hL hU)
    intro V hV V' hV'
    exact ⟨V ∩ V', inter_mem hV hV', principal_mono.2 fun h hh => ⟨fun i j => (hh.1 i j).1, fun i j => (hh.2 i j).1⟩,
      principal_mono.2 fun h hh => ⟨fun i j => (hh.1 i j).2, fun i j => (hh.2 i j).2⟩⟩
  obtain ⟨Λ, hmul, hΛ, V', hV', hop⟩ := exists_lattice E V hV
  have key : ∀ u : UA σ J, (∀ i j, (mat u - 1) i j ∈ Λ) → ∀ p : ℕ, ∀ i j, (mat (u ^ p) - 1) i j ∈ Λ := by
    intro u hu p
    induction p with
    | zero => intro i j; rw [pow_zero, show mat (1 : UA σ J) = 1 from rfl, sub_self]; exact zero_mem _
    | succ p ih =>
      intro i j
      have e : mat (u ^ (p + 1)) - 1 = (mat (u ^ p) - 1) * (mat u - 1) + (mat (u ^ p) - 1) + (mat u - 1) := by
        rw [pow_succ, show mat (u ^ p * u) = mat (u ^ p) * mat u from rfl]; noncomm_ring
      rw [e, Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply]
      exact add_mem (add_mem (sum_mem fun k _ => hmul _ (ih i k) _ (hu k j)) (ih i j)) (hu i j)
  have ent' : ∀ f : UA σ J → Matrix (Fin d) (Fin d) (AE F E), Continuous f → f 1 = 1 →
      ∀ᶠ h in 𝓝 (1 : UA σ J), ∀ i j, (f h - 1) i j ∈ V' := fun f hf h1 => by
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    have hc : Continuous fun h => (f h - 1) i j := (hf.sub continuous_const).matrix_elem i j
    exact hc.continuousAt.preimage_mem_nhds (by simpa [h1] using hV')
  filter_upwards [ent' mat (Units.continuous_val.comp continuous_subtype_val) rfl,
    ent' (fun h => mat h⁻¹) continuous_mat_inv rfl] with u h1 h2 hu p
  refine hVU ⟨fun i j => hΛ (key u (fun i j => hop _ (h1 i j) (congrFun (congrFun hu i) j)) p i j), fun i j => hΛ ?_⟩
  rw [← inv_pow]
  exact key u⁻¹ (fun i j => hop _ (h2 i j) (congrFun (congrFun hu.inv i) j)) p i j

end levelStructure

end PositivityTheory.ThKEst

end
end

