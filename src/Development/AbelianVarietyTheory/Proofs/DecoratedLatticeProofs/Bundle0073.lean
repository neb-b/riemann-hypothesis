module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0057
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0758

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InfIdeleNegOneNotMemClosurePrincipalIdentityComp
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.RealSignIdele

variable {E : Type} [Field E] [NumberField E]

theorem pos_of_mem_conn {w : InfinitePlace E} (hw : w.IsReal) {u : (InfiniteAdeleRing E)ˣ}
    (hu : u ∈ Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ) :
    0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw ((u : InfiniteAdeleRing E) w) := by
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have he : Continuous (fun y : w.Completion => e y) :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).continuous
  let g : (InfiniteAdeleRing E)ˣ → ℝ := fun u => e ((u : InfiniteAdeleRing E) w)
  have hg : Continuous g := he.comp ((continuous_apply w).comp Units.continuous_val)
  have hg0 : ∀ u, g u ≠ 0 := fun u h => by
    have h1 : (u : InfiniteAdeleRing E) w = 0 := (map_eq_zero e).mp h
    exact left_ne_zero_of_mul_eq_one (congrFun u.mul_inv w) h1
  have hg1 : g 1 = 1 := map_one e
  by_contra hneg
  obtain ⟨v, -, hv⟩ := isPreconnected_connectedComponent.intermediate_value hu mem_connectedComponent
    hg.continuousOn (show (0 : ℝ) ∈ Set.Icc (g u) (g 1) from ⟨not_lt.mp hneg, by rw [hg1]; exact zero_le_one⟩)
  exact hg0 v hv

theorem norm_eq_one_of_sub_one_mem {a : 𝓞 E} (ha : IsUnit a) (h3 : a - 1 ∈ Ideal.span {(3 : 𝓞 E)}) :
    Algebra.norm ℤ a = 1 := by
  classical
  obtain ⟨m, hm⟩ := Ideal.mem_span_singleton'.1 h3
  have ea : a = 1 + (3 : ℤ) • m := by
    rw [zsmul_eq_mul, Int.cast_ofNat, mul_comm, hm]; ring
  let b := RingOfIntegers.basis E
  have hdet : (Int.castRingHom (ZMod 3)) (Algebra.norm ℤ a) = 1 := by
    rw [Algebra.norm_eq_matrix_det b, RingHom.map_det, ea, map_add (f := _), map_one, map_zsmul]
    have : (Int.castRingHom (ZMod 3)).mapMatrix (1 + (3 : ℤ) • Algebra.leftMulMatrix b m) = 1 := by
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        map_add, map_mul, eq_intCast, Int.cast_ofNat]
      have h30 : (3 : ZMod 3) = 0 := rfl
      rw [h30, zero_mul, add_zero, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [this, Matrix.det_one]
  have hu : IsUnit (Algebra.norm ℤ a) := ha.map _
  rcases Int.isUnit_iff.1 hu with h | h
  · exact h
  · rw [h] at hdet
    exact absurd hdet (by decide)

theorem div_norm_of_pos {r : ℝ} (hr : 0 < r) : (r : ℂ) / ((‖(r : ℂ)‖ : ℝ) : ℂ) = 1 := by
  rw [Complex.norm_real, Real.norm_of_nonneg hr.le]
  exact div_self (Complex.ofReal_ne_zero.2 hr.ne')

theorem div_norm_of_neg {r : ℝ} (hr : r < 0) : (r : ℂ) / ((‖(r : ℂ)‖ : ℝ) : ℂ) = -1 := by
  rw [Complex.norm_real, Real.norm_of_nonpos hr.le, Complex.ofReal_neg, div_neg,
    div_self (Complex.ofReal_ne_zero.2 hr.ne)]

theorem norm_ne_one_of_sign {w : InfinitePlace E} (hw : w.IsReal) {k : E} (hk : k ≠ 0)
    (hneg : InfinitePlace.embedding_of_isReal hw k < 0)
    (hpos : ∀ (w' : InfinitePlace E) (hw' : w'.IsReal), w' ≠ w → 0 < InfinitePlace.embedding_of_isReal hw' k) :
    Algebra.norm ℚ k ≠ 1 := by
  classical
  intro hN
  have cc : ∀ ψ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate ψ) = ψ := fun ψ => star_star ψ
  let f : (E →+* ℂ) → ℂ := fun φ => φ k / ((‖φ k‖ : ℝ) : ℂ)
  have hprod : ∏ φ : E →+* ℂ, φ k = 1 := by
    have := Algebra.norm_eq_prod_embeddings ℚ ℂ k
    rw [hN, map_one] at this
    rw [this]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) _ _ fun φ => rfl
  have habs : ∏ φ : E →+* ℂ, ((‖φ k‖ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_prod, ← norm_prod, hprod, norm_one, Complex.ofReal_one]
  have h1 : ∏ φ : E →+* ℂ, f φ = 1 := by
    simp only [f]
    rw [Finset.prod_div_distrib, hprod, habs, div_one]
  have hnz : ∀ φ : E →+* ℂ, φ k ≠ 0 := fun φ => (map_ne_zero φ).2 hk
  have h2 : ∏ φ ∈ Finset.univ.erase w.embedding, f φ = 1 := by
    refine Finset.prod_involution (fun φ _ => ComplexEmbedding.conjugate φ) (fun φ _ => ?_) (fun φ hφ => ?_)
      (fun φ hφ => ?_) (fun φ _ => cc φ)
    · simp only [f]
      rw [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj,
        Complex.normSq_eq_norm_sq]
      have hn : ((‖φ k‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hnz φ))
      push_cast
      field_simp
    · intro hf heq
      apply hf
      have hr : ComplexEmbedding.IsReal φ := ComplexEmbedding.isReal_iff.2 heq
      have hemb := InfinitePlace.embedding_mk_eq_of_isReal hr
      have hw' : (InfinitePlace.mk φ).IsReal := InfinitePlace.isReal_iff.2 (by rw [hemb]; exact hr)
      have hne : InfinitePlace.mk φ ≠ w := by
        rintro h
        apply (Finset.mem_erase.1 hφ).1
        rw [← hemb, h]
      have e1 : φ k = ((InfinitePlace.embedding_of_isReal hw' k : ℝ) : ℂ) := by
        rw [InfinitePlace.embedding_of_isReal_apply, hemb]
      simp only [f]
      rw [e1]
      exact div_norm_of_pos (hpos _ hw' hne)
    · refine Finset.mem_erase.2 ⟨fun h => (Finset.mem_erase.1 hφ).1 ?_, Finset.mem_univ _⟩
      rw [← cc φ, h]
      exact ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 hw)
  have h3 : f w.embedding = -1 := by
    simp only [f]
    rw [← InfinitePlace.embedding_of_isReal_apply hw]
    exact div_norm_of_neg hneg
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w.embedding), h2, h3, mul_one] at h1
  norm_num at h1


open GlobalTheory.RayFromArtin GlobalTheory.Mem.LocTriv in
theorem infIdele_neg_one_not_mem :
    ∀ (E : Type) [Field E] [NumberField E] (w : InfinitePlace E), w.IsReal →
      ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E w (-1) ∉ ((diagUnits E).range ⊔ infConn E).topologicalClosure := by
  intro E _ _ w hw hx
  let 𝔪 : Ideal (𝓞 E) := Ideal.span {(3 : 𝓞 E)}
  have hm : 𝔪 ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    intro h
    have h' := congrArg (algebraMap (𝓞 E) E) h
    rw [map_ofNat, map_zero] at h'
    norm_num at h'
  have hle : ((diagUnits E).range ⊔ infConn E).topologicalClosure ≤ rayGrp 𝔪 :=
    Subgroup.topologicalClosure_minimal _ (sup_le_sup_left (infConn_le_rayIdl 𝔪) _)
      (Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono le_sup_right (isOpen_rayIdl hm)))
  obtain ⟨_, ⟨k, rfl⟩, z, hz, e⟩ := Subgroup.mem_sup.1 (hle hx)
  set x := ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E w (-1) with hxdef
  have hku : diagUnits E k = x * z⁻¹ := eq_mul_inv_of_mul_eq e
  obtain ⟨hunit, hcong, hinf⟩ := inv_mem hz

  have hev : ∀ v, ev v (diagUnits E k : AdeleRing (𝓞 E) E) = ev v ((z⁻¹ : Ideles E) : AdeleRing (𝓞 E) E) := by
    intro v
    rw [hku, Units.val_mul, map_mul]
    show (x : AdeleRing (𝓞 E) E).2 v * _ = _
    rw [hxdef, infIdele_snd, one_mul]
  have hval : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (k : E) = 1 := fun v => by
    rw [← valued_algebraMap, ← ev_diagUnits, hev]
    exact hunit v
  have hcong' : ∀ v : HeightOneSpectrum (𝓞 E), v.asIdeal ∣ 𝔪 → v.valuation E ((k : E) - 1) ≤ rad 𝔪 v :=
    fun v hv => by
      rw [← valued_algebraMap, map_sub, map_one, ← ev_diagUnits, hev]
      exact hcong v hv
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E (k : E) fun v => (hval v).le
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E ((k⁻¹ : Eˣ) : E) fun v => by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hval, inv_one]
  have hab : a * b = 1 := IsFractionRing.injective (𝓞 E) E (by rw [map_mul, ha, hb, map_one, Units.mul_inv])
  have ha1 : a - 1 ∈ 𝔪 := (mem_iff_rad hm _).2 fun v => by
    by_cases hv : v.asIdeal ∣ 𝔪
    · have e1 : ((a - 1 : 𝓞 E) : E) = (k : E) - 1 := by
        rw [RingOfIntegers.coe_eq_algebraMap, map_sub, map_one, ha]
      rw [e1]
      exact hcong' v hv
    · rw [rad_eq_one hm hv]
      exact v.valuation_le_one _
  have hN : Algebra.norm ℚ (k : E) = 1 := by
    rw [← ha, ← RingOfIntegers.coe_eq_algebraMap, ← Algebra.coe_norm_int,
      norm_eq_one_of_sub_one_mem ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, rfl⟩ ha1, Int.cast_one]

  have hcomp : ∀ w' : InfinitePlace E, algebraMap E w'.Completion (k : E) =
      (x : AdeleRing (𝓞 E) E).1 w' * ((z⁻¹ : Ideles E) : AdeleRing (𝓞 E) E).1 w' := fun w' => by
    have := congrArg (fun t : Ideles E => (t : AdeleRing (𝓞 E) E).1 w') hku
    simp only [Units.val_mul, Prod.fst_mul, Pi.mul_apply] at this
    exact this
  have hemb : ∀ (w' : InfinitePlace E) (hw' : w'.IsReal), InfinitePlace.embedding_of_isReal hw' (k : E) =
      InfinitePlace.Completion.ringEquivRealOfIsReal hw' (algebraMap E w'.Completion (k : E)) := fun w' hw' => by
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
      AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
      Algebra.algebraMap_self_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
    simp
  have hpos' : ∀ (w' : InfinitePlace E) (hw' : w'.IsReal),
      0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw' (((z⁻¹ : Ideles E) : AdeleRing (𝓞 E) E).1 w') :=
    fun w' hw' => pos_of_mem_conn hw' hinf
  refine norm_ne_one_of_sign hw (k := (k : E)) k.ne_zero ?_ (fun w' hw' hne => ?_) hN
  · rw [hemb, hcomp, hxdef, infIdele_fst_self, Units.val_neg, Units.val_one, neg_one_mul, map_neg]
    exact neg_neg_of_pos (hpos' w hw)
  · rw [hemb, hcomp, hxdef, infIdele_fst_ne E w w' hne, one_mul]
    exact hpos' w' hw'

end GlobalTheory.RealSignIdele
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixMeasureTopBlockIntegralGLMaxIdeal
section
open MeasureTheory Matrix Formalism.IndefR.Datum
open scoped NNReal ENNReal

noncomputable section

namespace GlobalTheory.RectBlockVolume

section Gen
variable {k : Type} [MeasurableSpace k] (ν : Measure k) [SigmaFinite ν]

def rectEquiv (A D B C : Type) [Fintype A] [Fintype D] [Fintype B] [Fintype C] :
    Matrix (A ⊕ D) (B ⊕ C) k ≃ᵐ ((Matrix A B k × Matrix A C k) × (Matrix D B k × Matrix D C k)) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : A ⊕ D => (B ⊕ C) → k)).trans
    (MeasurableEquiv.prodCongr (GlobalTheory.BlockVolume.colSplit A B C) (GlobalTheory.BlockVolume.colSplit D B C))

theorem rectEquiv_mp (A D B C : Type) [Fintype A] [Fintype D] [Fintype B] [Fintype C] :
    MeasurePreserving (rectEquiv (k := k) A D B C) (GlobalTheory.SplitWeil.volM ν (A ⊕ D) (B ⊕ C))
      (((GlobalTheory.SplitWeil.volM ν A B).prod (GlobalTheory.SplitWeil.volM ν A C)).prod
        ((GlobalTheory.SplitWeil.volM ν D B).prod (GlobalTheory.SplitWeil.volM ν D C))) := by
  have h1 := measurePreserving_sumPiEquivProdPi (fun _ : A ⊕ D => Measure.pi fun _ : B ⊕ C => ν)
  have h2 := (GlobalTheory.BlockVolume.colSplit_mp ν A B C).prod (GlobalTheory.BlockVolume.colSplit_mp ν D B C)
  exact h2.comp h1

theorem volM_rect_blocks (A D B C : Type) [Fintype A] [Fintype D] [Fintype B] [Fintype C]
    (S₁₁ : Set (Matrix A B k)) (S₁₂ : Set (Matrix A C k)) (S₂₁ : Set (Matrix D B k)) (S₂₂ : Set (Matrix D C k)) :
    GlobalTheory.SplitWeil.volM ν (A ⊕ D) (B ⊕ C)
                 {x | x.toBlocks₁₁ ∈ S₁₁ ∧ x.toBlocks₁₂ ∈ S₁₂ ∧ x.toBlocks₂₁ ∈ S₂₁ ∧ x.toBlocks₂₂ ∈ S₂₂} =
      GlobalTheory.SplitWeil.volM ν A B S₁₁ * GlobalTheory.SplitWeil.volM ν A C S₁₂ * GlobalTheory.SplitWeil.volM ν D B S₂₁ *
        GlobalTheory.SplitWeil.volM ν D C S₂₂ := by
  haveI hσ : ∀ (m n : Type) [Fintype m] [Fintype n], SigmaFinite (GlobalTheory.SplitWeil.volM ν m n) := fun m n _ _ => by
    exact (inferInstance : SigmaFinite (Measure.pi fun _ : m => Measure.pi fun _ : n => ν :
      Measure (m → n → k)))
  haveI := hσ A B; haveI := hσ A C; haveI := hσ D B; haveI := hσ D C
  have hset : {x : Matrix (A ⊕ D) (B ⊕ C) k | x.toBlocks₁₁ ∈ S₁₁ ∧ x.toBlocks₁₂ ∈ S₁₂ ∧
      x.toBlocks₂₁ ∈ S₂₁ ∧ x.toBlocks₂₂ ∈ S₂₂} =
      rectEquiv (k := k) A D B C ⁻¹' ((S₁₁ ×ˢ S₁₂) ×ˢ (S₂₁ ×ˢ S₂₂)) := by
    ext x
    exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2⟩, h3, h4⟩, fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩
  rw [hset]
  refine ((rectEquiv_mp ν A D B C).measure_preimage_equiv ((S₁₁ ×ˢ S₁₂) ×ˢ (S₂₁ ×ˢ S₂₂))).trans ?_
  rw [Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  ring

def reidx (r a' b' : ℕ) : Matrix (Fin r ⊕ Fin b') (Fin r ⊕ Fin a') k ≃ᵐ Matrix (Fin (r + b')) (Fin (r + a')) k :=
  (MeasurableEquiv.piCongrRight fun _ => MeasurableEquiv.piCongrLeft (fun _ => k) finSumFinEquiv).trans
    (MeasurableEquiv.piCongrLeft (fun _ => Fin (r + a') → k) finSumFinEquiv)

theorem reidx_apply (r a' b' : ℕ) (y : Matrix (Fin r ⊕ Fin b') (Fin r ⊕ Fin a') k) (i : Fin r ⊕ Fin b')
    (j : Fin r ⊕ Fin a') : reidx r a' b' y (finSumFinEquiv i) (finSumFinEquiv j) = y i j := by
  show Equiv.piCongrLeft (fun _ => Fin (r + a') → k) finSumFinEquiv
    (fun i => Equiv.piCongrLeft (fun _ => k) finSumFinEquiv (y i)) (finSumFinEquiv i) (finSumFinEquiv j) = y i j
  rw [Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply]

theorem reidx_mp (r a' b' : ℕ) :
    MeasurePreserving (reidx (k := k) r a' b') (GlobalTheory.SplitWeil.volM ν (Fin r ⊕ Fin b') (Fin r ⊕ Fin a'))
      (GlobalTheory.SplitWeil.volM ν (Fin (r + b')) (Fin (r + a'))) := by
  have h1 := measurePreserving_pi (fun _ : Fin r ⊕ Fin b' => Measure.pi fun _ : Fin r ⊕ Fin a' => ν)
    (fun _ => Measure.pi fun _ : Fin (r + a') => ν)
    (fun _ => measurePreserving_piCongrLeft (fun _ : Fin (r + a') => ν) finSumFinEquiv)
  have h2 := measurePreserving_piCongrLeft (fun _ : Fin (r + b') => Measure.pi fun _ : Fin (r + a') => ν)
    finSumFinEquiv
  exact h2.comp h1

end Gen

section Loc
open ValuativeRel

theorem pi_smul_const (ι : Type) [Fintype ι] {X : Type} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (c : ℝ≥0) :
    Measure.pi (fun _ : ι => (c : ℝ≥0∞) • μ) = ((c : ℝ≥0∞) ^ Fintype.card ι) • Measure.pi (fun _ : ι => μ) := by
  haveI : SigmaFinite ((c : ℝ≥0∞) • μ) := by
    have e : (c : ℝ≥0∞) • μ = c • μ := by
      ext s _
      simp [Measure.smul_apply]
    rw [e]
    infer_instance
  refine Measure.pi_eq fun s hs => ?_
  simp [Measure.smul_apply, Measure.pi_pi, Finset.prod_mul_distrib, smul_eq_mul]

variable {k : Type} [MeasurableSpace k]

theorem volM_smul (ν : Measure k) [SigmaFinite ν] (c : ℝ≥0) (m n : Type) [Fintype m] [Fintype n] :
    GlobalTheory.SplitWeil.volM ((c : ℝ≥0∞) • ν) m n =
      ((c : ℝ≥0∞) ^ (Fintype.card n * Fintype.card m)) • GlobalTheory.SplitWeil.volM ν m n := by
  unfold GlobalTheory.SplitWeil.volM
  rw [pi_smul_const n ν c]
  have e : ((c : ℝ≥0∞) ^ Fintype.card n) = ((c ^ Fintype.card n : ℝ≥0) : ℝ≥0∞) := by push_cast; rfl
  rw [e, pi_smul_const m _ (c ^ Fintype.card n)]
  push_cast
  rw [← pow_mul]
  rfl

variable [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [BorelSpace k]

theorem volKO_real (ν : Measure k) [ν.IsAddHaarMeasure] (r : ℕ) :
    (GlobalTheory.SplitWeil.volM ν (Fin r) (Fin r) (Units.val '' (GlobalTheory.SplitWeil.KO k (Fin r) : Set (GL (Fin r) k)))).toReal =
      (ν (𝒪[k] : Set k)).toReal ^ (r * r) *
        ∏ n ∈ Finset.Ioc 0 r, (1 - ((GlobalTheory.SplitWeil.resCard k : ℝ) ^ n)⁻¹) := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI : SigmaFinite ν := inferInstance
  have h0 : ν (𝒪[k] : Set k) ≠ 0 := (GlobalTheory.SplitWeil.isOpen_int k).measure_ne_zero ν ⟨0, zero_mem _⟩
  have htop : ν (𝒪[k] : Set k) ≠ ∞ := (GlobalTheory.SplitWeil.isCompact_int k).measure_lt_top.ne
  set c : ℝ≥0 := (ν (𝒪[k] : Set k)).toNNReal with hcdef
  have hcc : (c : ℝ≥0∞) = ν (𝒪[k] : Set k) := ENNReal.coe_toNNReal htop
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by rw [hcc]; exact h0
  set ν₁ : Measure k := (c : ℝ≥0∞)⁻¹ • ν with hν₁def
  haveI hH : ν₁.IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul ν (ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top) (ENNReal.inv_ne_top.2 hc0)
  have hν₁ : GlobalTheory.SplitWeil.IsUnitVol ν₁ := ⟨hH, by
    rw [hν₁def, Measure.smul_apply, smul_eq_mul, ← hcc, ENNReal.inv_mul_cancel hc0 ENNReal.coe_ne_top]⟩
  have hνeq : ν = (c : ℝ≥0∞) • ν₁ := by
    rw [hν₁def, smul_smul, ENNReal.mul_inv_cancel hc0 ENNReal.coe_ne_top, one_smul]
  haveI : SigmaFinite ν₁ := inferInstance
  have hV : GlobalTheory.SplitWeil.volM ν (Fin r) (Fin r) = ((c : ℝ≥0∞) ^ (r * r)) • GlobalTheory.SplitWeil.volM ν₁ (Fin r) (Fin r) := by
    conv_lhs => rw [hνeq]
    rw [volM_smul, Fintype.card_fin]
  have h1 := GlobalTheory.ChainStepIdentities.volAdd_eq k ν₁ hν₁ r
  unfold GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.volAdd at h1
  rw [hV, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ← Measure.real, h1, ENNReal.toReal_pow, ← hcc,
    ENNReal.coe_toReal]
  congr 1
  have hIcc : Finset.Icc 1 r = Finset.Ioc 0 r := by ext; simp; omega
  rw [hIcc]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.zetaAt]

end Loc
end GlobalTheory.RectBlockVolume


open ValuativeRel in
theorem GlobalTheory.RectBlockVolume.vol_topBlock_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (a b r : ℕ), r ≤ a → r ≤ b → (GlobalTheory.SplitWeil.volM ν (Fin b) (Fin a) {x | topL r x ∈ Units.val '' (GlobalTheory.SplitWeil.KO k (Fin r) : Set (GL (Fin r) k)) ∧ (∀ i j, ValuativeRel.valuation k (x i j) ≤ 1) ∧ ∀ i j, r ≤ i.val → j.val < r → ValuativeRel.valuation k (x i j) < 1}).toReal = (GlobalTheory.SplitWeil.volM ν (Fin b) (Fin a) {x | ∀ i j, ValuativeRel.valuation k (x i j) ≤ 1}).toReal * ((∏ n ∈ Finset.Ioc 0 r, (1 - ((GlobalTheory.SplitWeil.resCard k : ℝ) ^ n)⁻¹)) * ((GlobalTheory.SplitWeil.resCard k : ℝ) ^ (r * (b - r)))⁻¹) := by
  intro k _ _ _ _ _ _ ν hν a b r hra hrb
  haveI := hν
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI : SigmaFinite ν := inferInstance
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le hra
  obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hrb
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
    obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
    refine ⟨Units.mk0 x fun h => ?_, hx⟩
    subst h
    rw [map_zero] at hx
    exact (show uniformizer k ≠ 0 by simp) hx.symm
  have hset : GlobalTheory.RectBlockVolume.reidx r a' b' ⁻¹' {x : Matrix (Fin (r + b')) (Fin (r + a')) k | topL r x ∈ Units.val '' (GlobalTheory.SplitWeil.KO k (Fin r) : Set (GL (Fin r) k)) ∧ (∀ i j, valuation k (x i j) ≤ 1) ∧ ∀ i j, r ≤ i.val → j.val < r → valuation k (x i j) < 1} =
      {y | y.toBlocks₁₁ ∈ Units.val '' (GlobalTheory.SplitWeil.KO k (Fin r) : Set (GL (Fin r) k)) ∧
        y.toBlocks₁₂ ∈ {z : Matrix (Fin r) (Fin a') k | ∀ i j, valuation k (z i j) ≤ valuation k ((ϖ : k) ^ ((fun _ _ => (0 : ℤ)) i j))} ∧
        y.toBlocks₂₁ ∈ {z : Matrix (Fin b') (Fin r) k | ∀ i j, valuation k (z i j) ≤ valuation k ((ϖ : k) ^ ((fun _ _ => (1 : ℤ)) i j))} ∧
        y.toBlocks₂₂ ∈ {z : Matrix (Fin b') (Fin a') k | ∀ i j, valuation k (z i j) ≤ valuation k ((ϖ : k) ^ ((fun _ _ => (0 : ℤ)) i j))}} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    have htop : topL r (GlobalTheory.RectBlockVolume.reidx r a' b' y) = y.toBlocks₁₁ := by
      ext i j
      simp only [topL]
      rw [dite_eq_left ⟨by omega, by omega⟩]
      have e1 : (⟨i.val, by omega⟩ : Fin (r + b')) = finSumFinEquiv (Sum.inl i) := Fin.ext (by simp)
      have e2 : (⟨j.val, by omega⟩ : Fin (r + a')) = finSumFinEquiv (Sum.inl j) := Fin.ext (by simp)
      rw [e1, e2, GlobalTheory.RectBlockVolume.reidx_apply]
      rfl
    rw [htop]
    have hall : ∀ P : Fin (r + b') → Fin (r + a') → Prop,
        (∀ i j, P i j) ↔ ∀ i j, P (finSumFinEquiv i) (finSumFinEquiv j) := fun P =>
      ⟨fun h i j => h _ _, fun h i j => by simpa using h (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)⟩
    rw [hall (fun i j => valuation k (GlobalTheory.RectBlockVolume.reidx r a' b' y i j) ≤ 1),
      hall (fun i j => r ≤ i.val → j.val < r → valuation k (GlobalTheory.RectBlockVolume.reidx r a' b' y i j) < 1)]
    have n1 : ∀ i : Fin r, ¬ r ≤ i.val := fun i => not_le.mpr i.2
    have n2 : ∀ j : Fin a', ¬ (r + j.val < r) := fun j => by omega
    simp only [GlobalTheory.RectBlockVolume.reidx_apply, Sum.forall, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      Fin.coe_castAdd, Fin.coe_natAdd, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, of_apply, zpow_zero,
      zpow_one, map_one, n1, n2, false_implies, implies_true, and_true, Nat.le_add_right, Fin.is_lt, true_implies,
      ← GlobalTheory.ParahoricConjBlocks.val_lt_one_iff hϖ]
    constructor
    · rintro ⟨hK, ⟨hI1, hI2⟩, -, hL⟩
      exact ⟨hK, fun i j => (hI1 i).2 j, hL, fun i j => (hI2 i).2 j⟩
    · rintro ⟨hK, h12, hL, h22⟩
      have hK' := (GlobalTheory.ParahoricConjBlocks.mem_KO_val_iff _).1 hK
      exact ⟨hK, ⟨fun i => ⟨fun j => hK'.1 i j, fun j => h12 i j⟩,
        fun i => ⟨fun j => (hL i j).le, fun j => h22 i j⟩⟩, trivial, hL⟩
  have hpre : GlobalTheory.SplitWeil.volM ν (Fin (r + b')) (Fin (r + a')) {x : Matrix (Fin (r + b')) (Fin (r + a')) k | topL r x ∈ Units.val '' (GlobalTheory.SplitWeil.KO k (Fin r) : Set (GL (Fin r) k)) ∧ (∀ i j, valuation k (x i j) ≤ 1) ∧ ∀ i j, r ≤ i.val → j.val < r → valuation k (x i j) < 1} =
      GlobalTheory.SplitWeil.volM ν (Fin r ⊕ Fin b') (Fin r ⊕ Fin a') {y | y.toBlocks₁₁ ∈ Units.val '' (GlobalTheory.SplitWeil.KO k (Fin r) : Set (GL (Fin r) k)) ∧
        y.toBlocks₁₂ ∈ {z : Matrix (Fin r) (Fin a') k | ∀ i j, valuation k (z i j) ≤ valuation k ((ϖ : k) ^ ((fun _ _ => (0 : ℤ)) i j))} ∧
        y.toBlocks₂₁ ∈ {z : Matrix (Fin b') (Fin r) k | ∀ i j, valuation k (z i j) ≤ valuation k ((ϖ : k) ^ ((fun _ _ => (1 : ℤ)) i j))} ∧
        y.toBlocks₂₂ ∈ {z : Matrix (Fin b') (Fin a') k | ∀ i j, valuation k (z i j) ≤ valuation k ((ϖ : k) ^ ((fun _ _ => (0 : ℤ)) i j))}} := by
    rw [← hset]
    exact ((GlobalTheory.RectBlockVolume.reidx_mp ν r a' b').measure_preimage_equiv _).symm
  have htot : GlobalTheory.SplitWeil.volM ν (Fin (r + b')) (Fin (r + a')) {x : Matrix (Fin (r + b')) (Fin (r + a')) k | ∀ i j, valuation k (x i j) ≤ 1} =
      GlobalTheory.SplitWeil.volM ν (Fin (r + b')) (Fin (r + a')) {y | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ ((fun _ _ => (0 : ℤ)) i j))} := by
    simp only [zpow_zero, map_one]
  rw [hpre, htot, GlobalTheory.RectBlockVolume.volM_rect_blocks, GlobalTheory.BoxVolume.volM_box k ν ϖ hϖ, GlobalTheory.BoxVolume.volM_box k ν ϖ hϖ,
    GlobalTheory.BoxVolume.volM_box k ν ϖ hϖ, GlobalTheory.BoxVolume.volM_box k ν ϖ hϖ]
  clear hset hpre htot
  have hq0 : (0 : ℝ) ≤ (GlobalTheory.SplitWeil.resCard k : ℝ) := Nat.cast_nonneg _
  simp only [Fintype.card_fin, Finset.sum_const_zero, neg_zero, zpow_zero, ENNReal.ofReal_one, mul_one,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel_left]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow]
  rw [ENNReal.toReal_ofReal (zpow_nonneg hq0 _), GlobalTheory.RectBlockVolume.volKO_real]
  have hz : ∀ m n : ℕ, (GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-((m : ℤ) * (n : ℤ))) = ((GlobalTheory.SplitWeil.resCard k : ℝ) ^ (n * m))⁻¹ := by
    intro m n
    rw [_root_.zpow_neg, show ((m : ℤ) * (n : ℤ)) = ((n * m : ℕ) : ℤ) by push_cast; ring, _root_.zpow_natCast]
  rw [hz]
  ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SharpUnitAtBadPrimes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.Core.Ht2.AAUnitS

theorem aaUnit_bad_sharp : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ B : Base D D.host.ccK dl, (ambOf s B χ cD).AAUnit (Sall sel mu u) := by
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ h B P hP
  have hcond := h.1.pr_cond
  obtain ⟨⟨-, -, -, hcc, -, -, -, -, -, hPr, -⟩, -, -, -, hmu, -⟩ := h
  subst hmu
  obtain ⟨l, hl, hlP, hd⟩ := GlobalTheory.ColNormsUnit.exists_prime hPr sel u P hP
  rw [hcond] at hd
  refine GlobalTheory.AAUnitAway.locP_AA D X s _ dl B χ cD P l hl ?_ ?_ hlP ?_
  · intro hs
    exact hd (((Nat.dvd_of_mem_primeFactors hs).mul_right _).mul_right _)
  · rintro rfl
    exact hd ((dvd_mul_left _ _).mul_right _)
  · rw [hcc, Ideal.absNorm_top]
    exact Nat.coprime_one_left _

end GlobalTheory.Core.Ht2.AAUnitS
end

