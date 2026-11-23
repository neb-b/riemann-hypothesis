module

public import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle0004
public import Development.WeilBound.ThetaLifts.SmallCones.MatCancel
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle0003
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.IsFrPlane
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0312
public import Development.WeilBound.ThetaLifts.TowerModels.Bundle0004

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.ConeUnf
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Core

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
  {B : Base F E} {M : Model σ X W} {om : Rep σ X W} {M₀ : Model σ X₁ W₁} {om₀ : Rep σ X₁ W₁}
  {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {μ : Measure (AE F E)ˣ} {u : (AE F E)ˣ → Ten F E n d} {ν : Chr F E} {z : ℕ}
  {S : Submodule ℂ (Fn F n d)}

theorem LineOK.fin [SFinite μ] [SFinite M₀.μ] (h : LineOK B M om M₀ om₀ e μ u ν z S) {K : Subgroup (UA σ X.J)} (μK : Measure K)
    {Φ : Fn F n d} {m : ℕ} {Ψ : Fin m → Fn F n d} {c : Fin m → K → ℂ} (hΨ : ∀ i, Ψ i ∈ S) (hc : ∀ i, Integrable (c i) μK)
    (hd : ∀ k : K, om (k.1, 1) Φ = ∑ i, c i k • Ψ i) (h₁ : UA σ W₁.J) :
    ∫⁻ k, ∫⁻ l, ∫⁻ g in M₀.dom, ‖theta om₀ (e (M.co.rho B.ψ (u l) (om (k.1, 1) Φ))) g h₁ *
      ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z)‖ₑ ∂M₀.μ ∂μ ∂μK < ⊤ := by
  set J : Fin m → (AE F E)ˣ × UA σ X₁.J → ℂ := fun i x =>
    theta om₀ (e (M.co.rho B.ψ (u x.1) (Ψ i))) x.2 h₁ * ((ν x.1 : ℂ) * ((absE F E x.1 : ℝ) : ℂ) ^ z) with hJ
  have hJi : ∀ i, Integrable (J i) (μ.prod (M₀.μ.restrict M₀.dom)) := fun i => h.int _ (hΨ i) h₁
  have key : ∀ k : K, ∫⁻ l, ∫⁻ g in M₀.dom, ‖theta om₀ (e (M.co.rho B.ψ (u l) (om (k.1, 1) Φ))) g h₁ *
      ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z)‖ₑ ∂M₀.μ ∂μ ≤
      ∑ i, ‖c i k‖ₑ * ∫⁻ x, ‖J i x‖ₑ ∂(μ.prod (M₀.μ.restrict M₀.dom)) := fun k => by
    have e1 : ∀ l g, theta om₀ (e (M.co.rho B.ψ (u l) (om (k.1, 1) Φ))) g h₁ * ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) =
        ∑ i, c i k * J i (l, g) := fun l g => by
      simp only [hd, h.val_sum _ hΨ, hJ, Finset.sum_mul, mul_assoc]
    simp only [e1]
    have hi : Integrable (fun x => ∑ i, c i k * J i x) (μ.prod (M₀.μ.restrict M₀.dom)) :=
      integrable_finsetSum _ fun i _ => (hJi i).const_mul _
    rw [← lintegral_prod (fun x => ‖∑ i, c i k * J i x‖ₑ) hi.1.enorm]
    calc _ ≤ ∫⁻ x, ∑ i, ‖c i k‖ₑ * ‖J i x‖ₑ ∂(μ.prod (M₀.μ.restrict M₀.dom)) :=
          lintegral_mono fun x => (enorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (enorm_mul _ _).le)
      _ = _ := by
          rw [lintegral_finsetSum' _ fun i _ => (hJi i).1.enorm.const_mul _]
          exact Finset.sum_congr rfl fun i _ => lintegral_const_mul'' _ (hJi i).1.enorm
  refine (lintegral_mono key).trans_lt ?_
  rw [lintegral_finsetSum' _ fun i _ => (hc i).1.enorm.mul_const _]
  refine ENNReal.sum_lt_top.2 fun i _ => ?_
  rw [lintegral_mul_const'' _ (hc i).1.enorm]
  exact ENNReal.mul_lt_top (hc i).2 (hJi i).2

theorem LineOK.unf [SFinite μ] [SFinite M₀.μ] (h : LineOK B M om M₀ om₀ e μ u ν z S) {K : Subgroup (UA σ X.J)} (μK : Measure K)
    {Φ : Fn F n d} {m : ℕ} {Ψ : Fin m → Fn F n d} {c : Fin m → K → ℂ} (hΨ : ∀ i, Ψ i ∈ S) (hc : ∀ i, Integrable (c i) μK)
    (hd : ∀ k : K, om (k.1, 1) Φ = ∑ i, c i k • Ψ i) (ι : (AE F E)ˣ → (AE F E)ˣ)
    (hι : ∀ G : (AE F E)ˣ → ℝ≥0∞, ∫⁻ l, G (ι l) ∂μ = ∫⁻ l, G l ∂μ) (hι' : ∀ G : (AE F E)ˣ → ℂ, ∫ l, G (ι l) ∂μ = ∫ l, G l ∂μ)
    (lev : (AE F E)ˣ × UA σ X₁.J → UA σ X.J) (f : UA σ X.J → ℂ)
    (hf : ∀ l g (k : K), f (lev (ι l, g) * k.1) * (((absE F E (ι l) : ℝ) ^ (1 - (n : ℝ)) : ℝ) : ℂ) =
      theta om₀ (e (M.co.rho B.ψ (u l) (om (k.1, 1) Φ))) g 1 * ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z)) :
    ∫⁻ k, ∫⁻ l, (∫⁻ g in M₀.dom, ‖f (lev (l, g) * k.1)‖ₑ ∂M₀.μ) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - (n : ℝ))) ∂μ ∂μK < ⊤ ∧
    ∫ k, ∫ l, (∫ g in M₀.dom, f (lev (l, g) * k.1) ∂M₀.μ) * (((absE F E l : ℝ) ^ (1 - (n : ℝ)) : ℝ) : ℂ) ∂μ ∂μK =
      coneI B M om M₀ om₀ e K μK μ u ν z Φ 1 := by
  constructor
  · convert h.fin μK hΨ hc hd 1 using 3 with k
    rw [← hι]
    congr 1
    funext l
    rw [← lintegral_mul_const' _ _ (by simp)]
    congr 1
    funext g
    have he : ENNReal.ofReal ((absE F E (ι l) : ℝ) ^ (1 - (n : ℝ))) =
        ‖(((absE F E (ι l) : ℝ) ^ (1 - (n : ℝ)) : ℝ) : ℂ)‖ₑ := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
    rw [he, ← eNorm_mul, hf]
  · unfold coneI
    congr 1
    funext k
    rw [← hι']
    congr 1
    funext l
    rw [← integral_mul_const]
    simp only [hf, Model.I, integral_mul_const, mul_assoc]

end Core

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.FcCols
section
noncomputable section

namespace PositivityTheory.ThKCT.Unf

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKCT.Fr PositivityTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.SW (hypJ)

section Ring

variable {K : Type} [CommRing K]

theorem conj_iff {n : Type} [Fintype n] [DecidableEq n] (s : K →+* K) {ξ : K} (hξ : IsUnit ξ) {J J' : Matrix n n K} (a : GL n K)
    (ha : ξ • (a.1ᵀ * J * a.1.map s)ᵀ = J') {g h : Matrix n n K} (e : g * a.1 = a.1 * h) :
    (h.map s)ᵀ * J' * h = J' ↔ gᵀ * J * g.map s = J := by
  have e1 : (h.map s)ᵀ * J' * h = ξ • (a.1ᵀ * (gᵀ * J * g.map s) * a.1.map s)ᵀ := by
    have : a.1ᵀ * (gᵀ * J * g.map s) * a.1.map s = (g * a.1)ᵀ * J * (g * a.1).map s := by
      simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
    rw [this, e, ← ha]
    simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc, Matrix.transpose_transpose, Matrix.mul_smul,
      Matrix.smul_mul]
  have u1 : IsUnit a.1ᵀ := (Matrix.isUnit_transpose _).2 a.isUnit
  have u2 : IsUnit (a.1.map s) := a.isUnit.map s.mapMatrix
  rw [e1, ← ha, hξ.smul_left_cancel, Matrix.transpose_inj, u2.mul_left_inj, u1.mul_right_inj]

def fc {n m : ℕ} (x y : Fin n → K) (ι : Matrix (Fin n) (Fin m) K) : Matrix (Fin n) (Fin (m + 2)) K :=
  Matrix.of fun i => Fin.cons (x i) (Fin.cons (y i) (ι i))

theorem fc_cols {n m : ℕ} {x y : Fin n → K} {ι : Matrix (Fin n) (Fin m) K} {g : Matrix (Fin n) (Fin n) K} {a b d : K}
    {r w : Fin m → K} {U : Matrix (Fin m) (Fin m) K} (e : g * fc x y ι = fc x y ι * pm a b r d w U) :
    g *ᵥ x = a • x ∧ g *ᵥ y = b • x + d • y + ι *ᵥ w ∧ g * ι = Matrix.vecMulVec x r + ι * U := by
  refine ⟨funext fun i => ?_, funext fun i => ?_, Matrix.ext fun i j => ?_⟩
  · have := congrFun (congrFun e i) 0
    simpa [fc, pm, blk, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.mulVec, dotProduct, mul_comm] using this
  · have := congrFun (congrFun e i) 1
    simpa [fc, pm, blk, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.mulVec, dotProduct, mul_comm, add_assoc] using this
  · have := congrFun (congrFun e i) j.succ.succ
    simpa [fc, pm, blk, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMulVec_apply] using this

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem conjEx (h : IsCMExt F E σ) {n : ℕ} {J J' : Matrix (Fin n) (Fin n) E} {ξ : E} (hξ : ξ ≠ 0) (A : GL (Fin n) E)
    (hA : ξ • (A.1ᵀ * J * A.1.map σ)ᵀ = J') : ∃ Φ : HeckeCharacterZeroLocus.SiegelWeilU.HA (AF F) σ J' ≃ₜ* UA σ J,
      (∀ g, mat (Φ g) * incM F A.1 = incM F A.1 * g.1.val) ∧
      ∀ g, HeckeCharacterZeroLocus.SiegelWeilU.HA.mat (AF F) σ J' g ∈ HeckeCharacterZeroLocus.SiegelWeilU.HFin (AF F) σ J' → Φ g ∈ ratU σ J := by
  obtain ⟨⟨_, _, _⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI : IsTopologicalRing (AE F E) := (_root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ h (AF F)).1
  let a : GL (Fin n) (AE F E) := Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) A
  have ha : inclR (F := F) (AF F) ξ • (a.1ᵀ * incM F J * a.1.map (cA σ : AE F E →+* AE F E))ᵀ = incM F J' := by
    rw [← hA]
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.smul_apply, Matrix.transpose_apply, Matrix.mul_apply, incM, Matrix.map_apply, smul_eq_mul, map_mul, map_sum]
    rfl
  have k := fun (g g' : GL (Fin n) (AE F E)) (e : g * a = a * g') =>
    conj_iff (cA σ : AE F E →+* AE F E) ((IsUnit.mk0 ξ hξ).map _) a ha (congrArg Units.val e)
  refine ⟨{ toFun := fun g => ⟨a * g.1 * a⁻¹, (k _ g.1 (inv_mul_cancel_right _ _)).1 g.2⟩
            invFun := fun g => ⟨a⁻¹ * g.1 * a, (k g.1 _ (by group)).2 g.2⟩
            left_inv := fun g => Subtype.ext (show a⁻¹ * (a * g.1 * a⁻¹) * a = g.1 by group)
            right_inv := fun g => Subtype.ext (show a * (a⁻¹ * g.1 * a) * a⁻¹ = g.1 by group)
            map_mul' := fun g g' => Subtype.ext (show a * (g.1 * g'.1) * a⁻¹ = a * g.1 * a⁻¹ * (a * g'.1 * a⁻¹) by group)
            continuous_toFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
            continuous_invFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _ },
    fun g => congrArg Units.val (inv_mul_cancel_right (a * g.1) a), ?_⟩
  rintro g ⟨u, -, hu⟩
  refine Subgroup.mem_subgroupOf.2 ⟨A * u * A⁻¹, ?_⟩
  rw [map_mul, map_mul, map_inv]
  exact congrArg (fun z => a * z * a⁻¹) hu

variable {B : Base F E} {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {i₀ i₁ r s : ℕ}

theorem parEx (hB : B.IsGood σ) (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) :
    ∃ (N : Type) (_ : TopologicalSpace N) (_ : SecondCountableTopology N) (_ : MeasurableSpace N) (_ : BorelSpace N)
      (μN : Measure N) (_ : SigmaFinite μN) (_ : IsFiniteMeasureOnCompacts μN) (nn : N → UA σ Y.J)
      (ι : UA σ Y₁.J →* UA σ Y.J) (mm : (AE F E)ˣ →* UA σ Y.J) (χ : (AE F E)ˣ →* ℝ≥0),
      Par μN nn ι mm χ ∧ (∀ a, χ a * absE F E a ^ (n₁ + 1) = 1) ∧ (∀ u, u ∈ unip σ Y H ↔ ∃ p, u = nn p) ∧
      (∀ t g, IsLevi H t g (ι g * mm t)) ∧ (∀ p, ∃ R : N → N, MeasurePreserving R μN μN ∧ ∀ x, nn x * nn p = nn (R x)) ∧
      ∃ C : Set N, IsCompact C ∧ ∀ p, ∃ q, nn q ∈ ratU σ Y.J ∧ ∃ p' ∈ C, nn q * nn p = nn p' := by
  have hσ := hB.cm
  have hss := PositivityTheory.ThKG.Tow.Levi.sig_sig hσ
  obtain rfl := hH.rank
  obtain ⟨ε, hε, -⟩ := exists_eps hY
  obtain ⟨ε', A', hfr⟩ := isFr hB hY hH
  have hd : IsUnit Y₁.J.det := hfr.isUnit_det (det_ne hY).isUnit
  obtain ⟨ξ, hξ, hξs⟩ := PositivityTheory.ThKF.exists_scale hσ ε
  have hsξ : σ ξ ≠ 0 := (map_ne_zero σ).2 hξ
  have h1 : ∀ i j, σ (Y₁.J j i) = ((ε : ℤ) : E) * Y₁.J i j := fun i j => by
    have e : ∀ i j, Y₁.J i j = form σ Y.J (fun k => H.ι k i) (fun k => H.ι k j) := fun i j => by
      rw [← hH.gram, Matrix.mul_assoc]; rfl
    rw [e, e, form_eps hss hε]
  have hJ : HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ (ξ • Y₁.Jᵀ) := by
    refine ⟨fun i j => ?_, ?_⟩
    · simp only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, map_mul, hξs, h1 j i]
      linear_combination (ξ * Y₁.J j i) * eps_sq (E := E) ε
    · rw [Matrix.det_smul, Matrix.det_transpose]
      exact mul_ne_zero (pow_ne_zero _ hξ) hd.ne_zero
  set y' : Fin (n₁ + 2) → E := (σ ξ)⁻¹ • H.y with hy'
  have hA : ξ • ((fc H.x y' H.ι)ᵀ * Y.J * (fc H.x y' H.ι).map σ)ᵀ = hypJ (ξ • Y₁.Jᵀ) := by
    have col : ∀ j, (fun i => H.ι i j) = H.ι *ᵥ Pi.single j 1 := fun j => by ext i; simp
    have l1 : ∀ (c : E) x y, form σ Y.J (c • x) y = c * form σ Y.J x y := fun c x y => smul_dotProduct _ _ _
    have l2 : ∀ (c : E) x y, form σ Y.J x (c • y) = σ c * form σ Y.J x y := fun c x y => by
      simp only [form, dotProduct, Matrix.mulVec, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have z : ∀ x y, form σ Y.J x y = 0 → form σ Y.J y x = 0 := fun x y h => by
      rw [← hss (form σ Y.J y x), form_eps hss hε, h, mul_zero, map_zero]
    have yx : form σ Y.J H.y H.x = ((ε : ℤ) : E) := by
      rw [← hss (form σ Y.J H.y H.x), form_eps hss hε, hH.xy, mul_one, map_intCast]
    have o1 : ∀ j, form σ Y.J (fun i => H.ι i j) H.x = 0 := fun j => by rw [col]; exact (hH.orth _).1
    have o2 : ∀ j, form σ Y.J (fun i => H.ι i j) y' = 0 := fun j => by rw [col, hy', l2, (hH.orth _).2, mul_zero]
    ext a b
    have ent : (ξ • ((fc H.x y' H.ι)ᵀ * Y.J * (fc H.x y' H.ι).map σ)ᵀ) a b =
        ξ * form σ Y.J (fun i => fc H.x y' H.ι i b) (fun i => fc H.x y' H.ι i a) := by rw [Matrix.mul_assoc]; rfl
    rw [ent]
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun a => ?_) a) a <;>
      refine Fin.cases ?_ (fun b => Fin.cases ?_ (fun b => ?_) b) b
    · exact mul_eq_zero_of_right _ hH.xx
    · show ξ * form σ Y.J y' H.x = 1
      rw [hy', l1, yx, ← mul_assoc, mul_right_comm, mul_comm ξ, ← hξs, mul_inv_cancel₀ hsξ]
    · exact mul_eq_zero_of_right _ (o1 _)
    · show ξ * form σ Y.J H.x y' = 1
      rw [hy', l2, hH.xy, map_inv₀, hss, mul_one, mul_inv_cancel₀ hξ]
    · show ξ * form σ Y.J y' y' = 0
      rw [hy', l1, l2, hH.yy, mul_zero, mul_zero, mul_zero]
    · exact mul_eq_zero_of_right _ (o2 _)
    · exact mul_eq_zero_of_right _ (z _ _ (o1 _))
    · exact mul_eq_zero_of_right _ (z _ _ (o2 _))
    · show _ = ξ * Y₁.J b a
      rw [← hH.gram, Matrix.mul_assoc]; rfl
  have hu : IsUnit (fc H.x y' H.ι) := by
    have e := congrArg Matrix.det hA
    have e2 := Matrix.isUnit_det_of_left_inverse (hyp_inv (Matrix.nonsing_inv_mul _ (Ne.isUnit hJ.2)))
    rw [← e, Matrix.det_smul, Matrix.det_transpose, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at e2
    exact (Matrix.isUnit_iff_isUnit_det _).2
      (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right e2)))
  obtain ⟨Φ, p1, p2⟩ := conjEx hσ hξ hu.unit hA
  obtain ⟨Ψ, q1, -⟩ := conjEx (J := Y₁.J) hσ hξ 1 (J' := ξ • Y₁.Jᵀ) (by simp [Matrix.map_one _ (map_zero σ) (map_one σ)])
  obtain ⟨N, _, _, _, _, μN, _, _, nn, ι, mm, χ, p₀, hP, c1, n0, hval, hdec, hR, C, hC, hcov⟩ := parH hσ hJ
  have one : incM F (1 : Matrix (Fin n₁) (Fin n₁) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have q2 : ∀ g, (Ψ.symm g).1.val = mat g := fun g => by
    have := q1 (Ψ.symm g)
    rw [Units.val_one, one, Matrix.mul_one, Matrix.one_mul, Ψ.apply_symm_apply] at this
    exact this.symm
  have eA : incM F (fc H.x y' H.ι) = fc (incV F H.x) (incV F y') (incM F H.ι) := by
    ext i j
    refine Fin.cases rfl (fun j => Fin.cases rfl (fun j => rfl) j) j
  have ey : incV F H.y = inclR (F := F) (AF F) (σ ξ) • incV F y' := funext fun i => by
    simp only [incV, hy', Pi.smul_apply, smul_eq_mul, ← map_mul, mul_inv_cancel_left₀ hsξ]
  have cols : ∀ p g (t : (AE F E)ˣ), ∃ (b : AE F E) (r w : Fin n₁ → AE F E), (p = p₀ → b = 0 ∧ r = 0 ∧ w = 0) ∧
      mat (Φ (nn p * ι (Ψ.symm g) * mm t)) *ᵥ incV F H.x = t.1 • incV F H.x ∧
      mat (Φ (nn p * ι (Ψ.symm g) * mm t)) *ᵥ incV F y' = b • incV F H.x + cA σ (t⁻¹).1 • incV F y' + incM F H.ι *ᵥ w ∧
      mat (Φ (nn p * ι (Ψ.symm g) * mm t)) * incM F H.ι = Matrix.vecMulVec (incV F H.x) r + incM F H.ι * mat g := fun p g t => by
    obtain ⟨b, r, w, e1, e2⟩ := hval p (Ψ.symm g) t
    have := p1 (nn p * ι (Ψ.symm g) * mm t)
    rw [e1, q2, hu.unit_spec, eA] at this
    exact ⟨b, r, w, e2, fc_cols this⟩
  refine ⟨N, inferInstance, inferInstance, inferInstance, inferInstance, μN, inferInstance, inferInstance, _, _, _, χ,
    hP.transport Φ Ψ, c1, fun u => ⟨fun hu' => ?_, ?_⟩, fun t g => ?_, fun p => ?_, C, hC, fun p => ?_⟩
  · obtain ⟨u1, u2⟩ := mem_unip.1 hu'
    obtain ⟨p, v, e⟩ := hdec (Φ.symm u) 1 (by
      have e1 := congrArg (· *ᵥ Pi.single 0 1) (p1 (Φ.symm u))
      have e2 : incM F hu.unit.1 *ᵥ Pi.single 0 1 = incV F H.x := by
        rw [hu.unit_spec, eA, Matrix.mulVec_single_one]; rfl
      simp only [← Matrix.mulVec_mulVec, Φ.apply_symm_apply] at e1
      rw [e2, u1, ← e2] at e1
      rw [Units.val_one, one_smul]
      exact (Matrix.mulVec_injective_of_isUnit (hu.unit.isUnit.map (inclR (F := F) (AF F)).mapMatrix) e1).symm)
    obtain ⟨b, r, w, -, -, -, e3⟩ := cols p (Ψ v) 1
    rw [Ψ.symm_apply_apply, ← e, Φ.apply_symm_apply] at e3
    have hv : Ψ v = 1 := mat_inj (Matrix.toLin'.injective (LinearMap.ext fun z => by
      obtain ⟨a, ha⟩ := u2 z
      rw [Matrix.mulVec_mulVec, e3, Matrix.add_mulVec, Matrix.vecMulVec_mulVec, ← Matrix.mulVec_mulVec, op_smul_eq_smul] at ha
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, mat_one, Matrix.one_mulVec]
      exact (hfr.ad.indep (t := 0) (t' := 0) (congrArg (· + _) ((add_comm _ _).trans ha))).1))
    refine ⟨p, ?_⟩
    rw [(map_eq_one_iff Ψ Ψ.injective).1 hv, map_one, map_one, mul_one, mul_one] at e
    rw [← e, Φ.apply_symm_apply]
  · rintro ⟨p, rfl⟩
    obtain ⟨b, r, w, -, e1, -, e3⟩ := cols p 1 1
    rw [map_one, map_one, map_one, mul_one, mul_one] at e1 e3
    refine mem_unip.2 ⟨e1.trans (one_smul _ _), fun z => ⟨r ⬝ᵥ z, ?_⟩⟩
    rw [Matrix.mulVec_mulVec, e3, Matrix.add_mulVec, Matrix.vecMulVec_mulVec, mat_one, Matrix.mul_one, op_smul_eq_smul]
    exact add_comm _ _
  · obtain ⟨b, r, w, e0, e1, e2, e3⟩ := cols p₀ g t
    obtain ⟨rfl, rfl, rfl⟩ := e0 rfl
    rw [n0, one_mul, map_mul] at e1 e2 e3
    refine ⟨e1, ?_, e3.trans (add_eq_right.2 (Matrix.ext fun i j => mul_zero (incV F H.x i)))⟩
    rw [ey, Matrix.mulVec_smul, smul_comm]
    exact congrArg _ (e2.trans (by simp))
  · obtain ⟨R, a, b⟩ := hR p
    exact ⟨R, a, fun x => by rw [← map_mul, b]⟩
  · obtain ⟨q, a, p', b, c⟩ := hcov p
    exact ⟨q, p2 _ a, p', b, by rw [← map_mul, c]⟩

end PositivityTheory.ThKCT.Unf

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.UnipEx
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix NNReal
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Fr
open GlobalTheory.Doubling (absE)

theorem unipEx_of : UnipEx := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H i₀ i₁ r s hB hY hH
  obtain ⟨ε, A', h⟩ := isFr hB hY hH
  have G := PositivityTheory.ThKEnd.Grp.unipGood hB.cm (hY.imp (·.herm) (·.skew)) (det_ne hY)
    ⟨hH.rank, hH.xx, hH.yy, hH.xy, hH.orth, hH.gram, (h.isUnit_det (det_ne hY).isUnit).ne_zero⟩
  refine ⟨G.ex, G.cov, G.closed, G.right, ?_, fun u hu => ⟨(mem_unip.1 hu).1, ?_⟩, ?_⟩
  · choose m h1 h2 using exists_levi hB.cm h
    let lev : (AE F E)ˣ × UA σ Y₁.J →* UA σ Y.J := MonoidHom.mk' (fun z => m z.1 z.2)
      fun a b => levi_uniq h (h1 _ _) (levi_mul (h1 _ _) (h1 _ _))
    have hc : Continuous (cA σ : AE F E → AE F E) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
    have c1 : Continuous fun z => mat (lev z) := by
      have e : (fun z => mat (lev z)) = fun z => _ := funext fun z => h2 z.1 z.2
      rw [e]
      refine (continuous_const.matrix_mul (continuous_matrix fun i j => ?_)).matrix_mul continuous_const
      rcases i with i | i <;> rcases j with j | j
      · exact (PositivityTheory.ThKEnd.Grp.continuous_mat.comp continuous_snd).matrix_elem i j
      · exact continuous_const
      · exact continuous_const
      · fin_cases i <;> fin_cases j
        exacts [Units.continuous_val.comp continuous_fst, continuous_const, continuous_const,
          hc.comp (Units.continuous_coe_inv.comp continuous_fst)]
    refine ⟨lev, Continuous.subtype_mk (f := fun z => (lev z).1) (Units.continuous_iff.2 ⟨c1, ?_⟩) _, h1,
      fun t g p hp => levi_uniq h hp (h1 t g)⟩
    have e : (fun z => mat (lev z)⁻¹) = (fun z => mat (lev z)) ∘ fun z => z⁻¹ := funext fun z => by simp
    exact (e ▸ c1.comp continuous_inv : Continuous fun z => mat (lev z)⁻¹)
  · exact h.ad.fix_y (PositivityTheory.ThKG.Tow.Levi.cA_cA hB.cm) u.2 (mem_unip.1 hu).1
  · obtain ⟨t, ht⟩ : ∃ t, absE F E t = ((4 : ℝ≥0) ^ Fintype.card (InfinitePlace F))⁻¹ := ⟨_, GlobalTheory.Eis.Conv.absE_halfE F E σ hB.cm⟩
    refine ⟨t⁻¹, ?_⟩
    rw [map_inv, ht, inv_inv, NNReal.coe_pow]
    exact one_lt_pow₀ (by norm_num) Fintype.card_ne_zero

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.WittOf
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix NNReal
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Fr

theorem sig_val {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {A : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ}
    (hA : Aᵀ * M * A.map star = Matrix.fromBlocks 1 0 0 (-1)) (u : Fin r ⊕ Fin s → ℂ) :
    (A *ᵥ u) ⬝ᵥ M *ᵥ star (A *ᵥ u) =
      ((∑ i, Complex.normSq (u (Sum.inl i)) - ∑ i, Complex.normSq (u (Sum.inr i)) : ℝ) : ℂ) := by
  have e : star (A *ᵥ u) = A.map star *ᵥ star u := funext fun i => RingHom.map_mulVec (starRingEnd ℂ) A u i
  rw [e, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA]
  simp [Matrix.fromBlocks_mulVec, dotProduct, Matrix.neg_mulVec, Complex.mul_conj, sub_eq_add_neg]

theorem aniso {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) (h0 : min r s = 0) {x : Fin n → ℂ}
    (hx : x ⬝ᵥ M *ᵥ star x = 0) : x = 0 := by
  obtain ⟨hn, A, hA⟩ := h
  obtain ⟨A', -, h1⟩ := PositivityTheory.ThKG.Tow.Pln.frame_inv hn hA
  have e : x = A *ᵥ (A' *ᵥ x) := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  generalize A' *ᵥ x = u at e
  rw [e, sig_val hA, Complex.ofReal_eq_zero] at hx
  have : u = 0 := by
    rcases Nat.min_eq_zero_iff.1 h0 with rfl | rfl
    · simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_sub, neg_eq_zero] at hx
      ext (i | i)
      · exact i.elim0
      · exact Complex.normSq_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg _).1 hx i (Finset.mem_univ _))
    · simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero] at hx
      ext (i | i)
      · exact Complex.normSq_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg _).1 hx i (Finset.mem_univ _))
      · exact i.elim0
  rw [e, this, Matrix.mulVec_zero]

theorem witt_of : Witt := by
  intro F E _ _ _ _ _ σ B n X r s hB hX
  refine ⟨fun h0 x hx => ?_, fun n₁ H h1 h2 => ?_⟩
  · obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have e := congrArg (B.emb w).1 hx
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hB.cm.2.2.2, map_zero] at e
    have := aniso (hX.sig w) h0 (x := fun i => (B.emb w).1 (x i)) e
    exact funext fun i => (B.emb w).1.injective ((congrFun this i).trans (map_zero _).symm)
  · obtain ⟨c, hc, hσ⟩ := PositivityTheory.ThKF.exists_scale hB.cm (-1)
    have f : ∀ x, form σ X.J x x = 0 → form σ (c • X.J) x x = 0 := fun x hx => by
      rw [form, Matrix.smul_mulVec, dotProduct_smul]
      exact smul_eq_zero_of_right _ hx
    have key := fun x : IsoV σ X => PositivityTheory.ThKEnd.Grp.wittVec F E σ hB.cm n (c • X.J)
      (fun i j => by simp [hσ, hX.herm])
      (by rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ hc) (det_ne (Or.inl hX))) x.1 H.x x.2.1 h1 (f _ x.2.2) (f _ h2)
    choose g g1 g2 using key
    have g3 : ∀ x, (g x).1ᵀ * X.J * (g x).1.map σ = X.J := fun x => smul_right_injective _ hc (by
      have := g1 x
      rwa [Matrix.mul_smul, Matrix.smul_mul] at this)
    have key : ∀ x, ∃ p : UA σ X.J, mat p = incM F (g x).1 := fun x =>
      PositivityTheory.ThKG.Tow.Levi.exists_UA (g' := incM F (g x)⁻¹.1)
        (by rw [← PositivityTheory.ThKEnd.Grp.incM_mul, Units.mul_inv, PositivityTheory.ThKEnd.Grp.incM_one])
        (by
          conv_rhs => rw [← g3 x]
          rw [PositivityTheory.ThKEnd.Grp.incM_mul, PositivityTheory.ThKEnd.Grp.incM_mul, PositivityTheory.ThKEnd.Grp.incM_conj]
          rfl)
    choose γ hγ using key
    exact ⟨γ, fun x => ⟨mem_ratU.2 ⟨_, hγ x⟩, by rw [hγ, PositivityTheory.ThKEnd.Grp.incM_mulVec, g2]⟩⟩

end PositivityTheory.ThKCT

end
end

