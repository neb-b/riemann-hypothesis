module

public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0010
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0013
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.Bundle0001
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0012
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0005

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.CommuteTheta
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.Bad

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc (idem)
open PositivityTheory.ThKG.Loc.Cone

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem cartan_pm {M θ : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (hs : HasSig M r s) (h0 : min r s = 0)
    (hM : ∀ i j, star (M j i) = M i j) (h : IsCartan M θ) : θ = 1 ∨ θ = -1 := by
  by_contra hn
  push Not at hn
  have ex : ∀ A : Matrix (Fin n) (Fin n) ℂ, A ≠ 0 → ∃ u, A *ᵥ u ≠ 0 := fun A hA => by
    by_contra c
    push Not at c
    exact hA (Matrix.ext_iff_mulVec.2 fun u => by rw [c, Matrix.zero_mulVec])
  obtain ⟨u, hu⟩ := ex _ (fun e => hn.2 (eq_neg_of_add_eq_zero_left e) : θ + 1 ≠ 0)
  obtain ⟨u', hu'⟩ := ex _ (sub_ne_zero.2 hn.1)
  set x := (θ + 1) *ᵥ u
  set y := (θ - 1) *ᵥ u'
  have hx : θ *ᵥ x = x := by rw [Matrix.mulVec_mulVec, mul_add, h.1, mul_one, add_comm]
  have hy : θ *ᵥ y = -y := by rw [Matrix.mulVec_mulVec, mul_sub, h.1, mul_one, ← Matrix.neg_mulVec, neg_sub]
  have iso : ∀ a b : Fin n → ℂ, (θ *ᵥ a) ⬝ᵥ M *ᵥ star (θ *ᵥ b) = a ⬝ᵥ M *ᵥ star b := fun a b => by
    have : star (θ *ᵥ b) = θ.map star *ᵥ star b := funext fun i => by simp [Matrix.mulVec, dotProduct]
    conv_rhs => rw [← h.2.1, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [this, Matrix.mulVec_mulVec]
  have re : ∀ a : Fin n → ℂ, a ⬝ᵥ M *ᵥ star a = ((a ⬝ᵥ M *ᵥ star a).re : ℂ) := fun a => by
    refine (Complex.conj_eq_iff_re.1 ?_).symm
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, map_sum, map_mul, Pi.star_apply, Complex.star_def, Complex.conj_conj]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [← hM i j, Complex.star_def]; ring
  have p1 := h.2.2 x hu
  have p2 := h.2.2 y hu'
  have c1 := iso x y
  have c2 := iso y x
  rw [hx] at p1
  rw [hy, neg_dotProduct, Complex.neg_re] at p2
  rw [hx, hy] at c1 c2
  rw [star_neg, Matrix.mulVec_neg, dotProduct_neg, neg_eq_self] at c1
  rw [neg_dotProduct, neg_eq_self] at c2
  set a := (x ⬝ᵥ M *ᵥ star x).re
  set b := (y ⬝ᵥ M *ᵥ star y).re
  have z := HasSig.aniso hs h0 (x := (Real.sqrt (-b) : ℂ) • x + (Real.sqrt a : ℂ) • y) (by
    simp only [star_add, star_smul, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, c1, c2, smul_eq_mul, Complex.star_def, Complex.conj_ofReal, mul_zero, add_zero, zero_add]
    rw [re x, re y, ← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, ← Complex.ofReal_mul (Real.sqrt a), Real.mul_self_sqrt p1.le,
      Real.mul_self_sqrt p2.le]
    change ((-b : ℝ) : ℂ) * a + a * b = 0
    push_cast
    ring)
  have z' := congrArg (θ *ᵥ ·) z
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hx, hy, Matrix.mulVec_zero] at z'
  have : (2 * Real.sqrt a : ℂ) • y = 0 := by linear_combination (norm := module) z - z'
  exact hu' ((smul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 p1).ne')))

variable {Y : Spc F E n} {B : Base F E} {v : Pl F} {r s : ℕ}

theorem theta_pm (hB : B.IsGood σ) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) (w) : Y.θ w = 1 ∨ Y.θ w = -1 :=
  cartan_pm (h.sig w) h0 (fun i j => (hB.cm.2.2.2 _ _).symm.trans (congrArg _ (h.herm i j))) (h.cartan w)

theorem commute_theta (hB : B.IsGood σ) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) (w) (A) : Commute A (Y.θ w) := by
  rcases theta_pm hB h h0 w with e | e <;> rw [e]
  exacts [Commute.one_right _, Commute.neg_one_right _]

omit [NumberField E] in
theorem real_latHat {z} (hz : z ∈ latHat Y) : realAd F 1 • z = 0 := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, h0, -, x, -, rfl⟩ := hz
    rw [smul_smul, mul_comm, ← smul_smul, at_real _ b h0]
  | zero => exact smul_zero _
  | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
  | neg x _ hx => rw [smul_neg, hx, neg_zero]

theorem idem_int (v u : Pl F) : evFin F u (idem F v) ∈ u.adicCompletionIntegers F := by
  rcases eq_or_ne u v with rfl | h
  · rw [evFin_idem_self]; exact one_mem _
  · rw [evFin_idem_ne h]; exact zero_mem _

theorem mulVec_mem (hL : Y.L.IsLattice E) {A : Matrix (Fin n) (Fin n) (AE F E)}
    (h : ∀ v, ∀ z ∈ latHat Y, At (evFin F v) z → A *ᵥ z ∈ latHat Y) {z} (hz : z ∈ latHat Y) : A *ᵥ z ∈ latHat Y := by
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  have t := (tendsto_aS (F := F)).smul_const (A *ᵥ z)
  rw [one_smul] at t
  refine (Euler.isClosed_latHat hL).mem_of_tendsto t (.of_forall fun S => ?_)
  rw [aS, add_smul, ← Matrix.mulVec_smul, real_latHat hz, Matrix.mulVec_zero, zero_add, Finset.sum_smul]
  exact sum_mem fun v _ => by
    rw [← Matrix.mulVec_smul]; exact h v _ (latHat_smul (idem_int v) hz) (at_idem v z)

theorem stab_iff (hB : B.IsGood σ) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) {K : Subgroup (UA σ Y.J)} (hK : IsStab B K)
    {g : UA σ Y.J} : g ∈ K ↔ ∀ v, IntAt v g :=
  (hK g).trans ⟨fun a _ z hz _ => a.2 z hz, fun a => ⟨fun w => commute_theta hB h h0 w _, fun _ hz =>
    ⟨mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (a v z h1 h2).1) hz, mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (a v z h1 h2).2) hz⟩⟩⟩

theorem emb_mem (hB : B.IsGood σ) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) {K : Subgroup (G2 σ Y)} (hK : IsStab2 B K)
    {e : UA σ Y.J × UA σ Y.J →* G2 σ Y} (he : ∀ g g', IsEmb g g' (e (g, g'))) {g : UA σ Y.J} (hg : ∀ v, IntAt v g) :
    e (g, 1) ∈ K := by
  refine (hK _).2 ⟨fun w => ?_, fun z z' hz hz' k hk => ?_⟩
  · rw [he g 1, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _)]
    simp only [Commute, SemiconjBy, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      (commute_theta hB h h0 w _).eq, (commute_theta hB h h0 w _).neg_right.eq]
  · obtain ⟨g', e1, hg'⟩ : ∃ g', k = e (g', 1) ∧ mat g' *ᵥ z ∈ latHat Y := by
      rcases hk with rfl | rfl
      · exact ⟨g, rfl, mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (hg v z h1 h2).1) hz⟩
      · exact ⟨g⁻¹, by rw [← map_inv, Prod.inv_mk, inv_one], mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (hg v z h1 h2).2) hz⟩
    rw [e1, he g' 1, Matrix.fromBlocks_mulVec, show mat (1 : UA σ Y.J) = 1 from rfl]
    simpa using ⟨hg', hz'⟩

theorem int_nhds (hL : Y.L.IsFullLattice E) : {g : UA σ Y.J | ∀ v, IntAt v g} ∈ 𝓝 (1 : UA σ Y.J) := by
  classical
  obtain ⟨m, x, hs, hx⟩ := Euler.lat_gen hL.toIsLattice
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  let U : Set (Fin m → AF F) := {a | ∀ i v, evFin F v (a i) ∈ v.adicCompletionIntegers F}
  have hO : IsOpen {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  have hU : IsOpen U := by
    rw [show U = ⋂ i, {a | ∀ v, evFin F v (a i) ∈ v.adicCompletionIntegers F} from Set.ext fun _ => by
      rw [Set.mem_iInter]; rfl]
    exact isOpen_iInter_of_finite fun i => hO.preimage (continuous_snd.comp (continuous_apply i))
  have hV := IsModuleTopology.isOpenMap_of_surjective (Euler.gen_surj hL hs) U hU
  set V := (Fintype.linearCombination (AF F) fun i => incV F (x i).1) '' U with eV
  have key : ∀ A : Matrix (Fin n) (Fin n) (AE F E), (∀ i, A *ᵥ incV F (x i).1 ∈ V) → ∀ v, ∀ z ∈ latHat Y, At (evFin F v) z →
      A *ᵥ z ∈ latHat Y := fun A hA v z hz h => by
    obtain ⟨a, ha, rfl⟩ := (hx z).1 hz
    rw [← Euler.at_iff.1 h, Finset.smul_sum, Matrix.mulVec_sum]
    refine sum_mem fun i _ => ?_
    obtain ⟨b, hb, e⟩ := hA i
    rw [smul_smul, Matrix.mulVec_smul, ← e, Fintype.linearCombination_apply, Finset.smul_sum]
    refine sum_mem fun j _ => ?_
    rw [smul_smul, mul_assoc]
    exact Euler.gen_mem (Euler.idem_mem (by rw [map_mul]; exact mul_mem ((ha i).2 v) (hb j v))) (x j).2
  have o : IsOpen {g : UA σ Y.J | ∀ i, mat g *ᵥ incV F (x i).1 ∈ V} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => hV.preimage (Euler.cont_mat.matrix_mulVec continuous_const)
  have o1 : ∀ i, mat (1 : UA σ Y.J) *ᵥ incV F (x i).1 ∈ V := fun i => by
    rw [show mat (1 : UA σ Y.J) = 1 from rfl, Matrix.one_mulVec]
    refine ⟨Pi.single i 1, fun j v => ?_, by rw [Fintype.linearCombination_apply_single, one_smul]⟩
    rw [Pi.single_apply, apply_ite (evFin F v), map_one, map_zero]
    split_ifs
    exacts [one_mem _, zero_mem _]
  exact mem_of_superset ((o.inter (o.preimage continuous_inv)).mem_nhds ⟨o1, by rw [Set.mem_preimage, inv_one]; exact o1⟩)
    fun g hg v z hz h => ⟨key _ hg.1 v z hz h, key _ hg.2 v z hz h⟩

theorem idem_smul {M : Type} [AddCommGroup M] [Module (AF F) M] {z : M} (h : At (evFin F v) z) : idem F v • z = z :=
  Euler.at_iff.1 h

theorem idem_off {z : AE F E} (h : compFin F E v z = 0) : idem F v • z = 0 := by
  let j : Fv F v ⊗[F] E →ₗ[F] AE F E := TensorProduct.map (LinearMap.inr F (Ainf F) (Af F) ∘ₗ singleFin v) LinearMap.id
  have : ∀ z, idem F v • z = j (compFin F E v z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, map_zero]
    | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy]
    | tmul a x =>
      refine congrArg (· ⊗ₜ[F] x) (af_ext' ((evI_mul _ _).trans (by rw [evI_idem, zero_mul]; exact evI_zero.symm)) fun u => ?_)
      rcases eq_or_ne u v with rfl | h
      · rw [smul_eq_mul, map_mul, evFin_idem_self, one_mul]; exact (evalV_singleFin_self _ _).symm
      · rw [smul_eq_mul, map_mul, evFin_idem_ne h, zero_mul]; exact (evalV_singleFin_ne h _).symm
  rw [this, h, map_zero]

theorem comm_off {e : UA σ Y.J × UA σ Y.J →* G2 σ Y} (he : ∀ g g', IsEmb g g' (e (g, g'))) {g : UA σ Y.J} (hg : OffAt v g)
    {k : G2 σ Y} (hk : At (evFin F v) (mat2 k - 1)) : k * e (g, 1) = e (g, 1) * k := by
  have h1 : idem F v • (mat2 (e (g, 1)) - 1) = 0 := by
    have : idem F v • (mat g - 1) = 0 := Matrix.ext fun i j => idem_off (by
      have := congrFun₂ hg i j
      rw [Matrix.map_apply] at this
      simp [this, Matrix.one_apply, apply_ite (compFin F E v)])
    rw [he g 1, show mat (1 : UA σ Y.J) = 1 from rfl, ← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg,
      Matrix.fromBlocks_add, Matrix.fromBlocks_smul, ← sub_eq_add_neg, this]
    simp
  have a1 : (mat2 k - 1) * (mat2 (e (g, 1)) - 1) = 0 := by rw [← idem_smul hk, smul_mul_assoc, ← mul_smul_comm, h1, mul_zero]
  have a2 : (mat2 (e (g, 1)) - 1) * (mat2 k - 1) = 0 := by rw [← idem_smul hk, mul_smul_comm, ← smul_mul_assoc, h1, zero_mul]
  refine Subtype.ext (Units.ext (show mat2 k * mat2 (e (g, 1)) = mat2 (e (g, 1)) * mat2 k from ?_))
  linear_combination (norm := noncomm_ring) a1 - a2

theorem loc_iwa {K : Subgroup (G2 σ Y)} (hK : IsStab2 B K) {a : G2 σ Y → ℝ} (ha : IsHgt K a) {x : G2 σ Y}
    (hx : At (evFin F v) (mat2 x - 1)) : ∃ p t k, IsPar p t ∧ k ∈ K ∧ At (evFin F v) (mat2 k - 1) ∧ x = p * k := by
  obtain ⟨p, t, hp, k, hk, rfl⟩ := ha.iwa x
  have h1 := idem_mul_self v
  let π : G2 σ Y →* G2 σ Y := MonoidHom.mk' (fun g => ⟨⟨Euler.cut (idem F v) (mat2 g), Euler.cut (idem F v) (mat2 g⁻¹),
    by rw [Euler.cut_mul h1, show mat2 g * mat2 g⁻¹ = 1 from g.1.mul_inv]; exact Euler.cut_one,
    by rw [Euler.cut_mul h1, show mat2 g⁻¹ * mat2 g = 1 from g.1.inv_mul]; exact Euler.cut_one⟩,
    Euler.cut_form h1 _ g.2⟩) fun g h => Subtype.ext (Units.ext (Euler.cut_mul h1 _ _).symm)
  have hπ : ∀ g, mat2 (π g) = (1 - idem F v) • 1 + idem F v • mat2 g := fun _ => rfl
  have h2 : ∀ g, mat2 (π g) - 1 = idem F v • (mat2 g - 1) := fun _ => Euler.cut_sub _
  refine ⟨π p, ⟨Euler.cut (idem F v) t.1, Euler.cut (idem F v) (t⁻¹).1,
    by rw [Euler.cut_mul h1, t.mul_inv]; exact Euler.cut_one, by rw [Euler.cut_mul h1, t.inv_mul]; exact Euler.cut_one⟩, π k, ?_,
    (hK _).2 ⟨fun w => ?_, fun z z' hz hz' k' hk' => ?_⟩, by rw [h2]; exact at_idem v _, ?_⟩
  · rw [isPar_iff] at hp ⊢
    change mat2 (π p) * _ = _ * Euler.cut (idem F v) t.1
    rw [hπ, Euler.cut, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, hp,
      Matrix.one_mul, Matrix.mul_one]
  · have : (mat2 (π k)).map (piInf (B.emb w)) = 1 := by
      rw [eq_add_of_sub_eq (h2 k), Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _)]
      exact add_eq_right.2 (Matrix.ext fun i j => piInf_idem _ v _)
    rw [this]; exact Commute.one_left _
  · obtain ⟨k₁, rfl, h3⟩ : ∃ k₁, k' = π k₁ ∧ k₁ ∈ ({k, k⁻¹} : Set (G2 σ Y)) := by
      rcases hk' with rfl | rfl
      exacts [⟨k, rfl, .inl rfl⟩, ⟨k⁻¹, (map_inv π k).symm, .inr rfl⟩]
    obtain ⟨b1, b2⟩ := ((hK k).1 hk).2 z z' hz hz' k₁ h3
    have i2 : ∀ u, evFin F u (1 - idem F v) ∈ u.adicCompletionIntegers F := fun u => by
      rw [map_sub, map_one]; exact sub_mem (one_mem _) (idem_int v u)
    rw [hπ, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact ⟨add_mem (latHat_smul i2 hz) (latHat_smul (idem_int v) b1), add_mem (latHat_smul i2 hz') (latHat_smul (idem_int v) b2)⟩
  · rw [← map_mul]
    exact Subtype.ext (Units.ext (Euler.cut_eq.2 (idem_smul hx)).symm)

end GlobalTheory.ThK.Dbl.Bad

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.CuspLift
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKEnd (unipU IsCusp)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem IsRapid.bound {φ : UA σ Y.J → ℂ} (hφ : IsRapid φ) (h1 : ∀ h : UA σ Y.J, 1 ≤ ht h) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (T : UA σ Y.J → ℂ) (A : ℝ), 0 ≤ A → (∀ γ ∈ ratU σ Y.J, ∀ h, T (γ * h) = T h) →
      (∀ h, ‖T h‖ ≤ A * (ht h : ℝ) ^ N) → ∀ h, ‖T h‖ * ‖φ h‖ ≤ A * M := by
  obtain ⟨C, hC⟩ := hφ.2.2 N
  refine ⟨2 ^ N * max C 0, by positivity, fun T A hA hi hb h => ?_⟩
  have q1 : 1 ≤ qht h := le_ciInf fun γ => h1 _
  obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt (f := fun γ : ratU σ Y.J => ht (γ.1 * h)) (b := 2 * qht h)
    (lt_two_mul_self (zero_lt_one.trans_le q1))
  calc _ ≤ A * (2 * qht h : ℝ) ^ N * ‖φ h‖ := mul_le_mul_of_nonneg_right (hi γ γ.2 h ▸ (hb _).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) (by exact_mod_cast hγ.le) N) hA)) (norm_nonneg _)
    _ = A * (2 ^ N * (‖φ h‖ * (qht h : ℝ) ^ N)) := by ring
    _ ≤ _ := by gcongr; exact (hC h).trans (le_max_left _ _)

variable {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} {χ : Chr F E} {s₀ : ℂ} {f : G2 σ Y → ℂ} {e : UA σ Y.J × UA σ Y.J →* G2 σ Y}

theorem eis_bound (he : ∀ h h', IsEmb h h' (e (h, h'))) {c : ℝ≥0} (h1 : ∀ h h' x, IsEmb (σ := σ) (Y := Y) h h' x → ht2 x ≤ c * (ht h * ht h'))
    (h2 : ∀ h : UA σ Y.J, 1 ≤ ht h) {φ : UA σ Y.J → ℂ} (hφ : IsRapid φ) (C : ℝ) (N : ℕ) (b : ℝ≥0) :
    ∃ M : ℝ, ∀ Ê : G2 σ Y → ℂ, (∀ c ∈ rat2 σ Y, ∀ x, Ê (c * x) = Ê x) → (∀ x, ‖Ê x‖ ≤ C * (ht2 x : ℝ) ^ N) →
      ∀ h, ht h ≤ b → ∀ h', ‖Ê (e (h, h'))‖ * ‖φ h'‖ ≤ M := by
  obtain ⟨M, -, hM⟩ := hφ.bound h2 N
  refine ⟨max C 0 * (c * b) ^ N * M, fun Ê hi hb h hh => hM (fun x => Ê (e (h, x))) _ (by positivity) (fun γ hγ x => ?_) fun x => ?_⟩
  · rw [← hi _ ((he 1 γ).rat (one_mem _) hγ) (e (h, x)), ← map_mul, Prod.mk_mul_mk, one_mul]
  · refine (hb _).trans ?_
    rw [mul_assoc, ← mul_pow]
    have : ht2 (e (h, x)) ≤ c * b * ht x := (h1 _ _ _ (he h x)).trans (by rw [mul_assoc]; gcongr)
    gcongr
    exacts [le_max_left _ _, by exact_mod_cast this]

theorem sfin {A : Type} [MeasurableSpace A] (μ : Measure A) [IsFiniteMeasure μ] : SFinite μ := inferInstance

theorem sfin' {A : Type} [Group A] [TopologicalSpace A] [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A]
    (μ : Measure A) [μ.IsHaarMeasure] : SFinite μ := inferInstance

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem ct_zero (hO : OffOpen) (hU : PositivityTheory.ThKEnd.Grp.UnipUGood) (hE1 : EisContinues) (hH : HtEmb) {B : Base F E} {r s : ℕ}
    (hB : B.IsGood σ) (hn : 1 ≤ n) (hY : Y.IsSkew σ B r s) (d0 : Y.J.det ≠ 0) [LocallyCompactSpace (UA σ Y.J)]
    [SecondCountableTopology (UA σ Y.J)] [T2Space (UA σ Y.J)] (hb : ∀ Ω : Set (UA σ Y.J), IsCompact Ω → ∃ C : ℝ≥0, ∀ g ∈ Ω, ht g ≤ C)
    (hχ : IsHecke F E χ) (he : ∀ h h', IsEmb h h' (e (h, h'))) (ce : Continuous e) (hS : IsStab2 B K)
    (hK : IsCompact (K : Set (G2 σ Y))) (ha : IsHgt K a) (ca : Continuous a) (a0 : ∀ x, 0 < a x) (cf : Continuous f)
    (hf : Law χ (s₀ + n / 2) f) {U Ê} (hE : IsEisCont (flat a f s₀) U Ê) {μ : Measure (UA σ Y.J)} {D : Set (UA σ Y.J)}
    (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ Y.J) D μ) (fin : μ D < ⊤) {t₀ : ℝ}
    (hi : ∀ t, t₀ ≤ t → Integrable (fun g => a (e (1, g)) ^ t) μ) {φ : UA σ Y.J → ℂ} (hφ : IsRapid φ) (hc : IsCusp Y φ) :
    ∀ s ∈ U, IsCusp Y fun h => ∫ h' in D, Ê s (e (h, h')) * detInv χ h' * φ h' ∂μ := by
  intro s hs V v1 v2 κ 𝓜 k1 k2 h
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨g, -⟩ := hU F E σ hB.cm n Y (.inr hY.skew) d0 V
  haveI := g.sc
  haveI : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 fin.ne
  haveI : IsFiniteMeasure (κ.restrict 𝓜) := isFiniteMeasure_restrict.2 (g.fin κ 𝓜 k1 k2).2.ne
  haveI : SFinite (μ.restrict D) := sfin _
  haveI : SFinite (κ.restrict 𝓜) := sfin _
  haveI : SFinite μ := sfin' μ
  obtain ⟨c, c1, -, c3⟩ := hH F E σ n Y
  obtain ⟨t₁, half⟩ := hE.half
  have cE : ∀ s ∈ U, Continuous (Ê s) := fun s hs =>
    hE.cont.comp_continuous (f := fun x => (s, x)) (by fun_prop) fun _ => ⟨hs, trivial⟩
  have iv : ∀ s ∈ U, ∀ γ ∈ rat2 σ Y, ∀ x, Ê s (γ * x) = Ê s x := fun s hs γ hγ x =>
    An.ident hE.isOpen hE.conn (hE.hol _) (hE.hol _) (fun s hs => ⟨(half s hs).1,
      (hf.flat ha a0 s).eis_rat hχ (half s hs).2 hγ _⟩) hs
  obtain ⟨Ω, hΩ, cov⟩ := g.cov
  obtain ⟨b, hb'⟩ := hb _ ((hΩ.image continuous_subtype_val).image (continuous_mul_const h))
  let k : ℂ → unipU σ Y V × UA σ Y.J → ℂ := fun s y => Ê s (e (y.1.1 * h, y.2)) * detInv χ y.2 * φ y.2
  have ck : ∀ s ∈ U, Continuous (k s) := fun s hs =>
    (((cE s hs).comp (ce.comp (by fun_prop))).mul ((continuous_detInv hχ).comp continuous_snd)).mul (hφ.1.comp continuous_snd)
  have bk : ∀ s ∈ U, ∃ ε > 0, ∃ M, ∀ s' ∈ U ∩ Metric.ball s ε, ∀ y, ‖k s' y‖ ≤ M := fun s hs => by
    obtain ⟨ε, C, N, h0, hg⟩ := hE.grow s hs
    obtain ⟨M, hM⟩ := eis_bound he c1 c3 hφ C N b
    refine ⟨ε, h0, M, fun s' hs' y => ?_⟩
    obtain ⟨γ, hγ, h1⟩ := cov y.1
    have := hM (Ê s') (iv s' hs'.1) (hg s' hs'.2) _ (hb' _ ⟨_, ⟨_, h1, rfl⟩, rfl⟩) y.2
    rw [show e ((γ * y.1).1 * h, y.2) = e (γ.1, 1) * e (y.1.1 * h, y.2) by simp [← map_mul, mul_assoc],
      iv s' hs'.1 _ ((he _ _).rat hγ (one_mem _))] at this
    simpa only [k, norm_mul, norm_detInv, mul_one] using this
  have ik : ∀ s ∈ U, Integrable (k s) ((κ.restrict 𝓜).prod (μ.restrict D)) := fun s hs => by
    obtain ⟨ε, h0, M, hM⟩ := bk s hs
    exact .of_bound (ck s hs).aestronglyMeasurable M (.of_forall (hM s ⟨hs, Metric.mem_ball_self h0⟩))
  have hol : DifferentiableOn ℂ (fun s => ∫ y, k s y ∂(κ.restrict 𝓜).prod (μ.restrict D)) U := fun s hs => by
    obtain ⟨ε, h0, M, hM⟩ := bk s hs
    have o := hE.isOpen.inter (Metric.isOpen_ball (x := s) (ε := ε))
    exact ((An.diffOn_integral o (fun s hs => (ck s hs.1).aestronglyMeasurable)
      (fun y => (((hE.hol _).mul_const _).mul_const _).mono Set.inter_subset_left) fun S hS _ =>
        ⟨M, fun s hs => hM s (hS hs)⟩).differentiableAt (o.mem_nhds ⟨hs, Metric.mem_ball_self h0⟩)).differentiableWithinAt
  have l1 : Law (1 : Chr F E) ((0 : ℂ) + n / 2) fun x => (a x : ℂ) ^ ((0 : ℂ) + n / 2) := fun p t x hp => by
    beta_reduce
    rw [ha.mul hp, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (absE_pos _).le (a0 x).le]; simp
  have h1 : IsHecke F E (1 : Chr F E) := ⟨continuous_const, fun _ => rfl⟩
  obtain ⟨U₁, Ê₁, hE₁, -⟩ := hE1 F E σ B n Y r _ hB hn (.inr hY) 1 h1 0 (fun x => by simp only [pow_zero, ite_self]; rfl) K a hS ha 0 (fun x => (a x : ℂ) ^ ((0 : ℂ) + n / 2))
    ⟨(Complex.continuous_ofReal.comp ca).cpow continuous_const fun x => Complex.ofReal_mem_slitPlane.2 (a0 x), l1, by
      refine FiniteDimensional.span_of_finite ℂ ((Set.finite_singleton fun x => (a x : ℂ) ^ ((0 : ℂ) + n / 2)).subset ?_)
      rintro _ ⟨k, rfl⟩
      refine funext fun x => ?_
      obtain ⟨p, t, hp, k', hk', rfl⟩ := ha.iwa x
      show (a _ : ℂ) ^ _ = (a _ : ℂ) ^ _
      simp only [mul_assoc, ha.val p t hp _ (mul_mem hk' k.2), ha.val p t hp _ hk']⟩
  obtain ⟨t₂, half₁⟩ := hE₁.half
  rw [← integral_prod (k s) (ik s hs)]
  refine An.ident hE.isOpen hE.conn hol (differentiableOn_const 0) (t := max (max t₁ t₂) (t₀ - n / 2)) (fun s hs => ?_) hs
  have s1 := (le_max_left _ _).trans_lt hs
  obtain ⟨u, sm⟩ := half s ((le_max_left _ _).trans_lt s1)
  have cs := continuous_flat (s₀ := s₀) cf ca a0 s
  obtain ⟨C, hC⟩ := (hf.flat (s₀ := s₀) ha a0 s).bound cs ha hK
  have ez : (s - s₀ + (s₀ + n / 2)).re = s.re + n / 2 := by simp; ring
  rw [ez] at hC
  have i1 : Integrable (fun g => flat a f s₀ s (e (1, g))) μ :=
    ((hi (s.re + n / 2) (by have := (le_max_right _ _).trans_lt hs; linarith)).const_mul C).mono'
      (cs.comp (ce.comp (Continuous.prodMk_right 1))).aestronglyMeasurable (.of_forall fun g => hC _)
  have i2 := i1.mul_bdd (continuous_detInv hχ).aestronglyMeasurable (.of_forall fun g => (norm_detInv χ g).le)
  obtain ⟨u₁, sm₁⟩ := half₁ (s.re : ℂ) (by simpa using (le_max_right _ _).trans_lt s1)
  obtain ⟨ε, C₁, N, h0, hg⟩ := hE₁.grow _ u₁
  have hfin : ∀ x, ∑' q : Cos σ Y, ∫⁻ y in D, ‖eisTerm (flat a f s₀ s) (e (x, y)) q * detInv χ y * φ y‖ₑ ∂μ ≠ ⊤ := fun x => by
    obtain ⟨M, hM⟩ := eis_bound he c1 c3 hφ C₁ N (ht x)
    have hM' := hM _ (fun c hc => (l1.flat ha a0 _).eis_rat h1 sm₁ hc) (hg _ (Metric.mem_ball_self h0)) x le_rfl
    haveI : Countable (Cos σ Y) := by
      exact Set.countable_univ_iff.1 ((sm₁ 1).summable.countable_support.mono fun q _ => mul_ne_zero
        (Complex.cpow_ne_zero_iff.2 (.inl (Complex.ofReal_ne_zero.2 (a0 _).ne')))
        (Complex.cpow_ne_zero_iff.2 (.inl (Complex.ofReal_ne_zero.2 (a0 _).ne'))))
    rw [← lintegral_tsum (f := fun q y => ‖eisTerm (flat a f s₀ s) (e (x, y)) q * detInv χ y * φ y‖ₑ) fun q => (((cs.comp (continuous_const.mul (ce.comp (Continuous.prodMk_right x)))).mul
      (continuous_detInv hχ)).mul hφ.1).measurable.enorm.aemeasurable]
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in D, ENNReal.ofReal (max C 0 * M) ∂μ)
      (by rw [setLIntegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top fin.ne) (lintegral_mono fun y => ?_)
    have t1 : ∀ q : Cos σ Y, eisTerm (flat a (fun x => (a x : ℂ) ^ ((0 : ℂ) + n / 2)) 0 (s.re : ℂ)) (e (x, y)) q =
        ((a (q.out.1 * e (x, y)) ^ (s.re + n / 2) : ℝ) : ℂ) := fun q => by
      rw [eisTerm, flat, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 (a0 _).ne'), Complex.ofReal_cpow (a0 _).le]
      congr 1; push_cast; ring
    have t2 : HasSum (fun q : Cos σ Y => a (q.out.1 * e (x, y)) ^ (s.re + n / 2)) (Ê₁ s.re (e (x, y))).re := by
      simpa only [t1, Complex.ofReal_re] using Complex.hasSum_re (sm₁ (e (x, y)))
    have p0 : ∀ q : Cos σ Y, 0 ≤ max C 0 * (a (q.out.1 * e (x, y)) ^ (s.re + n / 2) * ‖φ y‖) := fun q => by
      have := Real.rpow_nonneg (a0 (q.out.1 * e (x, y))).le (s.re + n / 2); positivity
    have t3 := (t2.mul_right ‖φ y‖).mul_left (max C 0)
    refine (ENNReal.tsum_le_tsum fun q => ?_).trans ((ENNReal.ofReal_tsum_of_nonneg p0 t3.summable).symm.le.trans
      (ENNReal.ofReal_le_ofReal ?_))
    · rw [← ofReal_norm_eq_enorm, norm_mul, norm_mul, norm_detInv, mul_one, ← mul_assoc]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ((hC _).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (a0 _).le _))) (norm_nonneg _))
    · rw [t3.tsum_eq]
      exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right (Complex.re_le_norm _) (norm_nonneg _)).trans (hM' y))
        (le_max_right _ _)
  refine ⟨u, ?_⟩
  rw [integral_prod (k s) (ik s u)]
  simp only [k, fun x => unfoldC hO hU hB hY d0 hχ he ce cs (hf.flat ha a0 s) sm hμ hD i1 hφ hc x (hfin x)]
  obtain ⟨b₀, hb₀⟩ := hφ.2.2 0
  rw [integral_integral_swap (f := fun (m : unipU σ Y V) g => flat a f s₀ s (e (1, g)) * detInv χ g * φ (m.1 * h * g))
    ((i2.comp_snd _).mul_bdd (c := b₀) (hφ.1.comp (by fun_prop)).aestronglyMeasurable
      (.of_forall fun y => by simpa using hb₀ (y.1.1 * h * y.2)))]
  simp only [integral_const_mul, mul_assoc _ h, hc V v1 v2 κ 𝓜 k1 k2, mul_zero, integral_zero]

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.NormZeta
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

theorem swFullX_of (h1 : SWAnisoX) (h2 : EisContinues) (h3 : BoxSecX) : SWFullX := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hn hd hX hW h0 hM χ hχ hr dd om S l c1 c2 K a hK ha μ D hμ hD Φ₁ p1 Φ₂ p2
  obtain ⟨U, Ê, hE, hR⟩ := h2 F E σ B n X r s hB hn (.inl hX) χ hχ d hr K a hK ha _ _
    (h3 F E σ B n d X W M r s r' s' hB hn hd hX hW h0 hM χ hχ hr dd om S l c1 c2 K a hK ha Φ₁ p1 Φ₂ p2)
  obtain ⟨k, hk⟩ := hR (((d : ℂ) - n) / 2)
  exact ⟨_, _, hE.update hk (h1 F E σ B n d X W M r s r' s' hB hn hd hX hW h0 hM χ hχ hr dd om S l c1 c2 K a hK ha μ D hμ hD Φ₁ p1 Φ₂ p2),
    Set.mem_insert _ _, fun x => by rw [Function.update_self]⟩

theorem inv_scale {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ f : G → ℂ, (Integrable (fun g => f g⁻¹) μ → Integrable f μ) ∧ ∫ g, f g⁻¹ ∂μ = c * ∫ g, f g ∂μ := by
  have e := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have c0 : μ.inv.haarScalarFactor μ ≠ 0 := fun h => NeZero.ne μ (by rw [← μ.inv_inv, e, h, zero_smul]; exact Measure.map_zero _)
  refine ⟨((μ.inv.haarScalarFactor μ : ℝ) : ℂ), by simpa using c0, fun f => ⟨fun h => ?_, ?_⟩⟩
  · have : Integrable f μ.inv := (integrable_map_equiv (MeasurableEquiv.inv G) f).2 h
    rw [e] at this
    exact (integrable_smul_measure (ENNReal.coe_ne_zero.2 c0) ENNReal.coe_ne_top).1 this
  · have : ∫ g, f g ∂μ.inv = ∫ g, f g⁻¹ ∂μ := integral_map_equiv (MeasurableEquiv.inv G) f
    rw [← this]
    conv_lhs => rw [e]
    rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem normZeta_of (hS : SWFullX) (hX : BoxSecX) (hW : DblX) (hH : HgtEx) (hT : HgtInt) (hK : Stab2Cpt) (hC : CptAll)
    (hB : ThetaBasic) (hP : PolSch) : NormZeta := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' T h0 h0' hn hd K a e k1 k2 he ν hν Φ hΦ
  have cX := hC F E σ B _ X _ _ T.base (.inl T.herm) h0
  have cW := hC F E σ B _ W _ _ T.base (.inr T.skew) h0'
  obtain ⟨μ, D, hμ, hD⟩ := cW.ex
  obtain ⟨⟨K', a', k1', k2', k3, k4⟩, e', ce, he'⟩ := hH F E σ B _ X _ _ T.base (.inl T.herm)
  obtain rfl : K' = K := Subgroup.ext fun k => (k1' k).trans (k1 k).symm
  obtain rfl : a' = a := funext fun x => by
    obtain ⟨p, t, hp, k, hk, rfl⟩ := k2.iwa x
    rw [k2.val p t hp k hk, k2'.val p t hp k hk]
  obtain rfl : e' = e := MonoidHom.ext fun x => Subtype.ext (Units.ext ((he' x.1 x.2).trans (he x.1 x.2).symm))
  have b := (hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ T).1 Φ (hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ T Φ hΦ)
  have s1 := hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ T Φ hΦ
  obtain ⟨dd, om₂, S, l, d1, d2, d3, d4⟩ := hW F E σ B _ _ _ _ _ _ _ _ _ _ _ _ T
  obtain ⟨c', c0, hc⟩ := d4 ν hν
  obtain ⟨t₀, hi⟩ := hT F E σ B _ X _ _ T.base (.inl T.herm) K' a' e' k1 k2 he M.μ T.good.haar
  have sec := hX F E σ B _ _ _ _ M _ _ _ _ T.base hn hd T.herm T.skew h0' T.good χW T.hW T.resW dd om₂ S l d3 d1 K' a' k1 k2 Φ hΦ Φ hΦ
  obtain ⟨U, Ê, hE, u, hv⟩ := hS F E σ B _ _ _ _ M _ _ _ _ T.base hn hd T.herm T.skew h0' T.good χW T.hW T.resW dd om₂ S l d3 d1
    K' a' k1 k2 μ D hμ hD Φ hΦ Φ hΦ
  obtain ⟨hol, t₁, far⟩ := kpair_cont T.base (.inl T.herm) h0 cX T.hW he ce (hK F E σ B _ X _ _ T.base (.inl T.herm) K' k1)
    k2 k3 k4 sec.cont sec.law hE T.good.haar T.good.dom hi
  haveI := cX.sc; haveI := cW.sc; haveI := cX.lc; haveI := cW.lc; haveI := T.good.haar; haveI := cX.right M.μ T.good.haar
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : IsFiniteMeasure (μ.restrict D) := ⟨by rw [Measure.restrict_apply_univ]; exact cW.fin _ _ hμ hD⟩
  haveI : IsFiniteMeasure (M.μ.restrict M.dom) := ⟨by rw [Measure.restrict_apply_univ]; exact cX.fin _ _ T.good.haar T.good.dom⟩
  obtain ⟨c, c1, hc1⟩ := inv_scale M.μ
  have rp : IsRapid (fun _ : UA σ X.J => (1 : ℂ)) := cX.rapid continuous_const fun _ _ _ => rfl
  have v0 := Complex.ofReal_ne_zero.2 (cX.vol_ne T.good.haar T.good.dom)
  have c2 := Complex.ofReal_ne_zero.2 c0.ne'
  have id : ∀ z g, flat a' (fun x => l (om₂ x (boxFun Φ (star Φ)))) (((d : ℂ) - n) / 2) z (e' (1, g)) * detInv χW g =
      c' * zint om ν a' e' Φ z g⁻¹ := fun z g => by
    have := (Law.flat (s₀ := ((d : ℂ) - n) / 2) (f := fun x => l (om₂ x (boxFun Φ (star Φ)))) sec.law k2 k4 z).diag (aniso_of T.base (.inl T.herm) h0) he g (e' (g⁻¹, 1))
    rw [← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one] at this
    have e2 := ((d2 Φ s1 Φ s1).2 1 g⁻¹ 1 _ (he _ _)).2
    rw [detInv_rat T.hW (one_mem _), one_smul, show ((1, 1) : UA σ X.J × UA σ W.J) = 1 from rfl, map_one, Module.End.one_apply] at e2
    rw [this, flat, e2, hc _ (T.weil.isUSplitting.pres _ _ s1) _ s1, zint, coef]
    exact mul_left_comm _ _ _
  refine ⟨U, fun z => (c' * c * M.μ.real M.dom : ℂ)⁻¹ * kpair χW e' M.μ M.dom (Ê z) fun _ => 1, t₁, hE.isOpen, hE.disc, u,
    (hol _ rp).const_mul _, fun z hz => ⟨(far z hz).1, (hc1 _).1 ?_, ?_⟩, fun I0 => mul_eq_zero_of_right _ ?_⟩
  · simpa only [id, integrable_const_mul_iff c2.isUnit] using (far z hz).2.1
  · simp only [(far z hz).2.2 _ rp, id, pet, star_one, mul_one, setIntegral_const, integral_mul_const, integral_const_mul,
      (hc1 _).2, Complex.real_smul]
    field_simp
  · have cT : Continuous fun x : UA σ W.J × UA σ X.J => theta om Φ x.2 x.1 := b.1.comp continuous_swap
    have := An.at_value (φ := fun _ => 1) (M.μ.restrict M.dom) (μ.restrict D)
      ⟨cT, cW.bdd₂ cX cT fun γ hγ δ hδ g g' => b.2.1 δ hδ γ hγ _ _⟩ ⟨continuous_const, 1, by simp⟩
    have z : ∀ h, ∫ g in M.dom, 1 * star (theta om Φ g h) ∂M.μ = 0 := fun h => by
      simp only [one_mul, Complex.star_def, integral_conj]
      exact (map_eq_zero _).2 (congrFun I0 h)
    simp only [z, zero_mul, integral_zero] at this
    refine Eq.trans ?_ ((congrArg ((if n < d then 1 else 2) * (((μ.real D)⁻¹ : ℝ) : ℂ) * ·) this).trans (mul_zero _))
    simp only [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [hv, setAverage_eq, Complex.real_smul, ← fun g => (((d2 Φ s1 Φ s1).2 g y.1 y.2 _ (he _ _)).1), integral_const_mul]
    ring

end GlobalTheory.ThK.Dbl

end
end

