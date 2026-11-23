module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0137
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0062

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UEmbMulPEl
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.Swap

open GlobalTheory.Amp.Rad GlobalTheory.Amp.UEmb

variable {k r : ℕ}

theorem mI_eq (j : Fin (k + 1)) : mI k r j = wI k r j := rfl

def rowAct (u : Matrix (Fin r) (Fin r) ℂ) (B : Fin r → Fin (k + 1) → ℂ) : Fin r → Fin (k + 1) → ℂ :=
  fun a j => ∑ c, star (u a c) * B c j

theorem herm_rowAct (u : Matrix (Fin r) (Fin r) ℂ) (B : Fin r → Fin (k + 1) → ℂ) :
    (Matrix.of fun a b => herm (Hb k) (rowAct u B b) (rowAct u B a)) =
      u * (Matrix.of fun a b => herm (Hb k) (B b) (B a)) * uᴴ := by
  ext a b
  simp only [Matrix.of_apply, Matrix.mul_apply, herm_Hb, rowAct, star_sum, star_mul', star_star,
    Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => by ring

theorem uEmb_mul_pEl (u : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit u.det) (B : Fin r → Fin (k + 1) → ℂ)
    (S : Matrix (Fin r) (Fin r) ℂ) :
    uEmb k r u * pEl k r B S = pEl k r (rowAct u B) (u * S * uᴴ) * uEmb k r u := by
  have h1 : ∀ a b, ∑ c, u⁻¹ a c * u c b = if a = b then 1 else 0 := fun a b => by
    rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul u hu, Matrix.one_apply]
  have h2 : uᴴ * (u⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul u hu, Matrix.conjTranspose_one]
  ext x y
  rw [Matrix.mul_apply, Matrix.mul_apply, sum3, sum3]
  induction x using cases3 <;> induction y using cases3 <;>
    simp only [pEl_ee, pEl_ew, pEl_es, pEl_we, pEl_ww, pEl_ws, pEl_se, pEl_sw, pEl_ss, ← mI_eq,
      u_ee, u_em, u_es, u_me, u_mm, u_ms, u_se, u_sm, u_ss] <;> simp only [mI_eq] <;>
    simp [pEl_ee, pEl_ew, pEl_es, pEl_we, pEl_ww, pEl_ws, pEl_se, pEl_sw, pEl_ss]
  · simp [rowAct, Finset.sum_mul, mul_assoc]
  · rename_i a b
    set G : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => herm (Hb k) (B b) (B a) with hG
    have h3 : ∀ a c, herm (Hb k) (rowAct u B c) (rowAct u B a) = (u * G * uᴴ) a c := fun a c =>
      congrFun (congrFun (herm_rowAct u B) a) c
    have h4 : u * (S - (1 / 2 : ℂ) • G) = (u * S * uᴴ - (1 / 2 : ℂ) • (u * G * uᴴ)) * (u⁻¹)ᴴ := by
      rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc _ uᴴ, Matrix.mul_assoc _ uᴴ, h2, Matrix.mul_one,
        Matrix.mul_one, Matrix.mul_sub, Matrix.mul_smul]
    have h5 := congrFun (congrFun h4 a) b
    rw [Matrix.mul_apply, Matrix.mul_apply] at h5
    simp only [h3]
    convert h5 using 2 with c _ c _
    · simp [hG, div_eq_inv_mul]
    · simp [div_eq_inv_mul]
  · rename_i i b
    simp only [rowAct, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ d, ∑ c, star (u c d) * B d i * (starRingEnd ℂ) (u⁻¹ b c) = star (∑ c, u⁻¹ b c * u c d) * B d i := by
      intro d
      rw [star_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun c _ => by simp; ring
    simp only [this, h1]
    simp [apply_ite (starRingEnd ℂ)]

theorem det_eq_one {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W]
    (ι : V →ₗ[ℝ] W) (hι : Function.Injective ι) (L : Module.End ℝ V) (T : Module.End ℝ W)
    (h : ∀ v, ι (L v) = T (ι v)) (hT : IsNilpotent (T - 1)) : LinearMap.det L = 1 := by
  have hL : IsNilpotent (L - 1) := by
    obtain ⟨n, hn⟩ := hT
    have : ∀ (m : ℕ) (v : V), ι (((L - 1) ^ m) v) = ((T - 1) ^ m) (ι v) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => intro v; simp [pow_succ, ih, h]
    refine ⟨n, LinearMap.ext fun v => hι ?_⟩
    rw [this, hn]; simp
  have hc := hL.neg.charpoly_eq_X_pow_finrank
  have he := LinearMap.eval_charpoly (-(L - 1)) 1
  rw [hc] at he
  simpa using he.symm

theorem nil_mul {R : Type*} [Ring R] {a b : R} (h : Commute a b) (ha : IsNilpotent (a - 1)) (hb : IsNilpotent (b - 1)) :
    IsNilpotent (a * b - 1) := by
  have e : a * b - 1 = (a - 1) * b + (b - 1) := by noncomm_ring
  have c1 : Commute (a - 1) b := h.sub_left (Commute.one_left b)
  rw [e]
  refine Commute.isNilpotent_add ?_ (c1.isNilpotent_mul_right ha) hb
  exact Commute.mul_left (c1.sub_right (Commute.one_right _)) ((Commute.refl b).sub_right (Commute.one_right _))

theorem nil_upper (x : UT r → ℂ) : IsNilpotent (upper x - 1) := by
  have hc : (upper x - 1).charpoly = Polynomial.X ^ r := by
    rw [Matrix.charpoly_of_upperTriangular]
    · simp [upper]
    · intro a b h
      have h : b < a := h
      simp [upper, h.not_gt, h.ne']
  have := Matrix.aeval_self_charpoly (upper x - 1)
  rw [hc] at this
  exact ⟨r, by simpa using this⟩

def rowLin (k : ℕ) (u : Matrix (Fin r) (Fin r) ℂ) : Module.End ℝ (Fin r → Fin (k + 1) → ℂ) where
  toFun := rowAct u
  map_add' B B' := by ext a j; simp [rowAct, mul_add, Finset.sum_add_distrib]
  map_smul' c B := by
    ext a j; simp only [rowAct, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, mul_smul_comm]

def skewLin (r : ℕ) : ((UT r → ℂ) × (Fin r → ℝ)) →ₗ[ℝ] Matrix (Fin r) (Fin r) ℂ where
  toFun p := skewM p.1 p.2
  map_add' p q := by
    ext a b; simp only [skewM, Matrix.add_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    split_ifs <;> simp <;> ring
  map_smul' c p := by
    ext a b; simp only [skewM, Matrix.smul_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp <;> ring

def coordLin (r : ℕ) : Matrix (Fin r) (Fin r) ℂ →ₗ[ℝ] ((UT r → ℂ) × (Fin r → ℝ)) where
  toFun S := (fun q => S q.1.1 q.1.2, fun a => (S a a).im)
  map_add' S T := by ext <;> simp
  map_smul' c S := by ext <;> simp

theorem coord_skew (p : (UT r → ℂ) × (Fin r → ℝ)) : coordLin r (skewLin r p) = p := by
  ext q
  · simp [coordLin, skewLin, skewM, q.2]
  · simp [coordLin, skewLin, skewM]

theorem skew_coord (S : Matrix (Fin r) (Fin r) ℂ) (hS : Sᴴ = -S) : skewLin r (coordLin r S) = S := by
  obtain ⟨p, hp, -⟩ := skewM_unique S hS
  have : S = skewLin r p := hp
  rw [this, coord_skew]

def conjLin (u : Matrix (Fin r) (Fin r) ℂ) : Module.End ℝ (Matrix (Fin r) (Fin r) ℂ) :=
  LinearMap.mulLeft ℝ u * LinearMap.mulRight ℝ uᴴ

def skewAct (u : Matrix (Fin r) (Fin r) ℂ) : Module.End ℝ ((UT r → ℂ) × (Fin r → ℝ)) :=
  coordLin r ∘ₗ conjLin u ∘ₗ skewLin r

theorem skew_skewAct (u : Matrix (Fin r) (Fin r) ℂ) (p : (UT r → ℂ) × (Fin r → ℝ)) :
    skewLin r (skewAct u p) = u * skewLin r p * uᴴ := by
  have h : (skewLin r p)ᴴ = -skewLin r p := skewM_skew p.1 p.2
  have e : skewAct u p = coordLin r (u * skewLin r p * uᴴ) := by
    simp [skewAct, conjLin, Matrix.mul_assoc]
  rw [e, skew_coord]
  simp [Matrix.conjTranspose_mul, h, Matrix.mul_assoc]

theorem mp_of_det {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure] (L : E →ₗ[ℝ] E) (h : LinearMap.det L = 1) :
    MeasurePreserving L μ μ :=
  ⟨L.continuous_of_finiteDimensional.measurable, by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ (by rw [h]; exact one_ne_zero), h]; simp⟩

def parAct (u : Matrix (Fin r) (Fin r) ℂ) (q : PPar k r) : PPar k r := (rowLin k u q.1, skewAct u q.2)

theorem uEmb_mul_pOf (u : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit u.det) (q : PPar k r) :
    uEmb k r u * pOf k r q = pOf k r (parAct u q) * uEmb k r u := by
  have h := skew_skewAct u q.2
  unfold pOf
  rw [uEmb_mul_pEl u hu]
  congr 2
  exact h.symm

theorem cont_upper (r : ℕ) : Continuous (upper : (UT r → ℂ) → Matrix (Fin r) (Fin r) ℂ) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  unfold upper
  split_ifs <;> fun_prop

theorem cont_uEmb (k r : ℕ) : Continuous fun x : UT r → ℂ => uEmb k r (upper x) := by
  have hi : Continuous fun x : UT r → ℂ => (upper x)⁻¹ := by
    have : (fun x : UT r → ℂ => (upper x)⁻¹) = fun x => (upper x).adjugate := by
      funext x; rw [Matrix.inv_def, det_upper]; simp
    rw [this]; exact (cont_upper r).matrix_adjugate
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold uEmb
  split_ifs
  · exact (cont_upper r).matrix_elem _ _
  · exact (hi.matrix_elem _ _).star
  all_goals exact continuous_const

theorem cont_pOf (k r : ℕ) : Continuous (pOf k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold pOf pEl skewM herm Matrix.mulVec dotProduct
  simp only [Pi.star_apply]
  split_ifs <;> fun_prop

theorem cont_parAct (k r : ℕ) : Continuous fun q : (UT r → ℂ) × PPar k r => parAct (upper q.1) q.2 := by
  have hu : Continuous fun q : (UT r → ℂ) × PPar k r => upper q.1 := (cont_upper r).comp continuous_fst
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun a => continuous_pi fun j => ?_
    change Continuous fun q : (UT r → ℂ) × PPar k r => ∑ c, star (upper q.1 a c) * q.2.1 c j
    exact continuous_finsetSum _ fun c _ => (hu.matrix_elem a c).star.mul (by fun_prop)
  · have hs : Continuous fun q : (UT r → ℂ) × PPar k r => skewLin r q.2.2 :=
      (skewLin r).continuous_of_finiteDimensional.comp (by fun_prop)
    exact (coordLin r).continuous_of_finiteDimensional.comp (hu.matrix_mul (hs.matrix_mul hu.matrix_conjTranspose))

end GlobalTheory.Amp.Swap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularOfContracted
section
open MeasureTheory MeasureTheory.Measure Filter Topology
open scoped NNReal ENNReal

namespace GlobalTheory.ModularAutomorphism

section Group

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]

theorem smul_haar_cancel (ρ : Measure H) [ρ.IsHaarMeasure] {c d : ℝ≥0} (h : c • ρ = d • ρ) : c = d := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : H)
  have h0 : ρ K ≠ 0 := (measure_pos_of_mem_nhds ρ hK1).ne'
  have h1 : ρ K ≠ ∞ := hK.measure_lt_top.ne
  have h2 : (c : ℝ≥0∞) * ρ K = (d : ℝ≥0∞) * ρ K := by
    have := congrArg (fun τ : Measure H => τ K) h
    exact this
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj h0 h1).1 h2)

theorem map_right_eq (ρ : Measure H) [ρ.IsHaarMeasure] (g : H) :
    ρ.map (· * g) = modularCharacterFun g • ρ := by
  rw [modularCharacterFun_eq_haarScalarFactor ρ g]
  exact isMulLeftInvariant_eq_smul _ ρ

theorem modular_aut (φ : H ≃ₜ* H) (g : H) : modularCharacterFun (φ g) = modularCharacterFun g := by
  let ρ : Measure H := Measure.haar
  have hφ : Measurable φ := φ.continuous.measurable
  haveI : (ρ.map φ).IsHaarMeasure := φ.toMulEquiv.isHaarMeasure_map ρ φ.continuous φ.symm.continuous
  apply smul_haar_cancel (ρ.map φ)
  rw [← map_right_eq, ← Measure.map_smul, ← map_right_eq, map_map (measurable_mul_const _) hφ,
    map_map hφ (measurable_mul_const _)]
  · congr 1
    funext x
    simp
  · exact hφ.aemeasurable

theorem continuous_modular : Continuous fun g : H => (modularCharacterFun g : ℝ) := by
  let ρ : Measure H := Measure.haar
  obtain ⟨f, hfc, hf0, hf1⟩ := exists_continuous_nonneg_pos (1 : H)
  have hI : ∫ x, f x ∂ρ ≠ 0 :=
    ne_of_gt (f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc hf0 hf1)
  have hc : Continuous fun x : H => ∫ y, f (y⁻¹ * x) ∂ρ.inv :=
    continuous_integral_apply_inv_mul f.continuous hfc
  have he : ∀ g : H, (modularCharacterFun g : ℝ) = (∫ y, f (y⁻¹ * g) ∂ρ.inv) / ∫ x, f x ∂ρ := by
    intro g
    rw [modularCharacterFun_eq_haarScalarFactor ρ g,
      haarScalarFactor_eq_integral_div _ _ f.continuous hfc hI,
      integral_map (measurable_mul_const g).aemeasurable f.continuous.aestronglyMeasurable,
      Measure.inv_def, integral_map measurable_inv.aemeasurable
        (by fun_prop : Continuous fun y : H => f (y⁻¹ * g)).aestronglyMeasurable]
    simp
  simp_rw [he]
  exact hc.div_const _

theorem map_inv_eq (ρ : Measure H) [ρ.IsHaarMeasure] [ρ.IsMulRightInvariant] : ρ.inv = ρ := by
  have h : ρ.inv = haarScalarFactor ρ.inv ρ • ρ := isMulLeftInvariant_eq_smul _ ρ
  set c := haarScalarFactor ρ.inv ρ
  have h2 : (c * c) • ρ = (1 : ℝ≥0) • ρ := by
    have h3 : ρ.inv.inv = c • ρ.inv := by
      conv_lhs => rw [h]
      rw [Measure.inv_def, Measure.map_smul, ← Measure.inv_def]
      exact measurable_inv.aemeasurable
    rw [Measure.inv_inv, h, smul_smul] at h3
    rw [one_smul]
    exact h3.symm
  have h4 : c * c = 1 := smul_haar_cancel ρ h2
  have h5 : c = 1 := by
    have : (c : ℝ) * c = 1 := by exact_mod_cast h4
    have h0 : (0 : ℝ) ≤ c := c.2
    have : (c : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  rw [h, h5, one_smul]

end Group

def conjAut {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (N : Subgroup G) (b : G)
    (h1 : ∀ m ∈ N, b * m * b⁻¹ ∈ N) (h2 : ∀ m ∈ N, b⁻¹ * m * b ∈ N) : N ≃ₜ* N where
  toFun m := ⟨b * m * b⁻¹, h1 m m.2⟩
  invFun m := ⟨b⁻¹ * m * b, h2 m m.2⟩
  left_inv m := Subtype.ext (by simp [mul_assoc])
  right_inv m := Subtype.ext (by simp [mul_assoc])
  map_mul' m n := Subtype.ext (by simp [mul_assoc])
  continuous_toFun := Continuous.subtype_mk (by fun_prop) _
  continuous_invFun := Continuous.subtype_mk (by fun_prop) _

theorem unimodular_of_contracted {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (N : Subgroup G) (hN : IsClosed (N : Set G)) {ν : Measure G} (hν : GlobalTheory.Dec.IsHaarSub (N : Set G) ν)
    (a : ℝ → G) (h1 : ∀ s : ℝ, ∀ m ∈ N, a s * m * (a s)⁻¹ ∈ N)
    (h2 : ∀ s : ℝ, ∀ m ∈ N, (a s)⁻¹ * m * a s ∈ N)
    (h3 : ∀ m ∈ N, Tendsto (fun s : ℝ => a s * m * (a s)⁻¹) atBot (nhds (1 : G))) :
    (∀ m ∈ N, ν.map (fun x : G => x * m) = ν) ∧ ν.map (fun x : G => x⁻¹) = ν := by
  obtain ⟨hne, hfin, hcar, hleft⟩ := hν
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  haveI : SecondCountableTopology N := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have hE : MeasurableEmbedding (Subtype.val : N → G) := MeasurableEmbedding.subtype_coe hN.measurableSet
  have hv : Measurable (Subtype.val : N → G) := hE.measurable
  let μ : Measure N := ν.comap Subtype.val
  have hμ : μ.map Subtype.val = ν := by
    rw [hE.map_comap, Subtype.range_coe_subtype]
    exact Measure.restrict_eq_self_of_ae_mem hcar
  haveI : μ.IsMulLeftInvariant := ⟨fun g => by
    apply hE.map_injective
    change (μ.map (g * ·)).map Subtype.val = μ.map Subtype.val
    have : (Subtype.val : N → G) ∘ (g * ·) = (fun x : G => (g : G) * x) ∘ Subtype.val := rfl
    rw [map_map hv (measurable_const_mul g), this, ← map_map (measurable_const_mul _) hv, hμ, hleft g g.2]⟩
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => by
    rw [hE.comap_apply]
    exact (hK.image continuous_subtype_val).measure_lt_top⟩
  haveI : NeZero μ := ⟨fun h => hne (by rw [← hμ, h, Measure.map_zero])⟩
  haveI : TopologicalSpace.PseudoMetrizableSpace N := inferInstance
  haveI : μ.Regular := inferInstance
  haveI : μ.IsHaarMeasure := {}
  have hmod : ∀ g : N, modularCharacterFun g = 1 := by
    intro g
    have t1 : Tendsto (fun s : ℝ => conjAut N (a s) (h1 s) (h2 s) g) atBot (nhds (1 : N)) :=
      tendsto_subtype_rng.2 (h3 g g.2)
    have t2 := ((continuous_modular (H := N)).tendsto 1).comp t1
    simp only [Function.comp_def, modular_aut, modularCharacterFun_map_one] at t2
    exact_mod_cast tendsto_const_nhds_iff.1 t2
  have hr : ∀ g : N, μ.map (· * g) = μ := fun g => by rw [map_right_eq, hmod, one_smul]
  haveI : μ.IsMulRightInvariant := ⟨hr⟩
  refine ⟨fun m hm => ?_, ?_⟩
  · have : (fun x : G => x * m) ∘ (Subtype.val : N → G) = Subtype.val ∘ (· * (⟨m, hm⟩ : N)) := rfl
    conv_lhs => rw [← hμ]
    rw [map_map (measurable_mul_const m) hv, this, ← map_map hv (measurable_mul_const _), hr, hμ]
  · have : (fun x : G => x⁻¹) ∘ (Subtype.val : N → G) = Subtype.val ∘ (Inv.inv : N → N) := rfl
    conv_lhs => rw [← hμ]
    rw [map_map measurable_inv hv, this, ← map_map hv measurable_inv, ← Measure.inv_def, map_inv_eq, hμ]

end GlobalTheory.ModularAutomorphism
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalBlockUnitriangularFlag
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellDens

private lemma Hpk_apply_of_lt_eq_ite (k r : ℕ) (c s : Fin (2 * r + k + 1)) (hc : c.val < r) :
    Formalism.QuantumDeterminants.Hpk k r c s = if c.val + s.val = 2 * r + k then 1 else 0 := by
  by_cases h : c.val + s.val = 2 * r + k
  · simp [Formalism.QuantumDeterminants.Hpk, hc, h]
  · have h' : ¬ r ≤ c.val := Nat.not_le.mpr hc
    simp [Formalism.QuantumDeterminants.Hpk, h, h']

private lemma Hpk_mul_apply_eq_Hpk_apply_of_lt_val (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hU : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r)
    (hcol : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      g i (Formalism.QuantumDeterminants.eI k r a) = if i = Formalism.QuantumDeterminants.eI k r a then 1 else 0)
    (q : Fin (2 * r + k + 1)) (hq : r + k < q.val) :
    ∀ c : ℕ, ∀ hc : c + q.val ≤ 2 * r + k,
      (Formalism.QuantumDeterminants.Hpk k r * g) ⟨c, by omega⟩ q = Formalism.QuantumDeterminants.Hpk k r ⟨c, by omega⟩ q := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hc
    have hcr : c < r := by omega
    have hE : Formalism.QuantumDeterminants.eI k r ⟨c, hcr⟩ = ⟨c, by omega⟩ := Fin.ext rfl
    have h1 : (gᴴ * (Formalism.QuantumDeterminants.Hpk k r * g)) ⟨c, by omega⟩ q = Formalism.QuantumDeterminants.Hpk k r ⟨c, by omega⟩ q := by
      rw [← Matrix.mul_assoc, hU]
    rw [Matrix.mul_apply, Finset.sum_eq_single (⟨c, by omega⟩ : Fin (2 * r + k + 1))] at h1
    · have hd := hcol ⟨c, hcr⟩ ⟨c, by omega⟩ le_rfl
      rw [hE, if_pos rfl] at hd
      rw [Matrix.conjTranspose_apply, hd, star_one, one_mul] at h1
      exact h1
    · intro t _ htc
      rw [Matrix.conjTranspose_apply]
      have htc' : t.val ≠ c := fun h => htc (Fin.ext h)
      rcases Nat.lt_or_gt_of_ne htc' with hlt | hgt
      · have h2 := ih t.val hlt (by omega)
        simp only [Fin.eta] at h2
        rw [h2, Hpk_apply_of_lt_eq_ite k r t q (by omega), if_neg (by omega), mul_zero]
      · have hz := hcol ⟨c, hcr⟩ t (by simp; omega)
        rw [hE, if_neg htc] at hz
        rw [hz, star_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem nset_block_unitriangular : ∀ (k r : ℕ), ∀ g ∈ Nset k r, ∀ i j : Fin (2 * r + k + 1),
    lev k r j ≤ lev k r i → g i j = (1 : Mat k r) i j := by
  intro k r g hg i j hlev
  obtain ⟨hU, hcol, hmid⟩ := hg
  have hU' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hU
  rw [Matrix.one_apply]
  unfold GlobalTheory.CellDens.lev at hlev
  by_cases hj : j.val < r
  · have hij : j.val ≤ i.val := by split_ifs at hlev <;> omega
    have h := hcol ⟨j.val, hj⟩ i hij
    have he : Formalism.QuantumDeterminants.eI k r ⟨j.val, hj⟩ = j := Fin.ext rfl
    rw [he] at h
    exact h
  · by_cases hj2 : j.val ≤ r + k
    · have hi : r ≤ i.val := by split_ifs at hlev <;> omega
      exact hmid i j (by omega) hj2 hi
    · have hi : r + k < i.val ∧ j.val ≤ i.val := by split_ifs at hlev <;> omega
      have hC : 2 * r + k - i.val < r := by omega
      have h := Hpk_mul_apply_eq_Hpk_apply_of_lt_val k r g hU' hcol j (by omega) (2 * r + k - i.val) (by omega)
      rw [Matrix.mul_apply, Finset.sum_eq_single i] at h
      · rw [Hpk_apply_of_lt_eq_ite k r _ i hC, if_pos (by simp; omega), one_mul] at h
        rw [h, Hpk_apply_of_lt_eq_ite k r _ j hC]
        by_cases hij : i = j
        · subst hij
          rw [if_pos (by simp; omega), if_pos rfl]
        · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
          rw [if_neg (by simp; omega), if_neg hij]
      · intro s _ hs
        have hv : s.val ≠ i.val := fun h => hs (Fin.ext h)
        rw [Hpk_apply_of_lt_eq_ite k r _ s hC, if_neg (by simp; omega), zero_mul]
      · intro h'
        exact absurd (Finset.mem_univ _) h'

end GlobalTheory.CellDens
end

