module

public import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle0006
public import Development.WeilBound.ThetaLifts.SmallCones.ExpAlg
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.ConeLawAB
section
set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cA_cA (hσ : IsCMExt F E σ) (x : AE F E) : cA σ (cA σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => simp [cA, cm_conj_conj hσ]
  | add a b ha hb => simp [ha, hb]

theorem chi_conj (hσ : IsCMExt F E σ) {χ : Chr F E} {k : ℕ}
    (h : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ k) (t : (AE F E)ˣ) :
    χ (GlobalTheory.Doubling.conjUnit σ t) = (χ t)⁻¹ := by
  have h1 := h (Units.map (Algebra.norm (AF F) : AE F E →* AF F) t)
  rw [if_pos (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨t, rfl⟩)), Circle.coe_eq_one,
    show Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) (Units.map (Algebra.norm (AF F) : AE F E →* AF F) t) =
      t * GlobalTheory.Doubling.conjUnit σ t from Units.ext (GlobalTheory.Doubling.algebraMap_norm_eq hσ (R := AF F) t.1), map_mul] at h1
  exact eq_inv_of_mul_eq_one_right h1

theorem conjUnit_val (t : (AE F E)ˣ) : (GlobalTheory.Doubling.conjUnit σ t : (AE F E)ˣ).1 = cA σ t.1 := rfl

section

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E} {M : Model σ X W}
  {om : Rep σ X W} {om₀ : Rep σ X₁ W₁} {H : Plane E n n₁} {H' : Plane E d d₁} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {χX χW : Chr F E}
  {r s r' s' : ℕ} {rX rW : ℝ}

theorem isLevi_inv' {t h₁ p} (h : IsLevi (σ := σ) (W := W) (W₁ := W₁) H' t h₁ p) :
    mat p⁻¹ *ᵥ incV F H'.x = (t⁻¹ : (AE F E)ˣ).1 • incV F H'.x :=
  mat_inv_mulVec p (by rw [Matrix.mulVec_smul, h.1, smul_smul, Units.inv_mul, one_smul])

theorem levi_inv_y {t h₁ p} (h : IsLevi (σ := σ) (W := W) (W₁ := W₁) H' t h₁ p) :
    mat p⁻¹ *ᵥ incV F H'.y = cA σ t.1 • incV F H'.y :=
  mat_inv_mulVec p (by rw [Matrix.mulVec_smul, h.2.1, smul_smul, ← map_mul, Units.mul_inv, map_one, one_smul])

theorem Mix2.levi (h : Mix2 H H' χX χW rX rW om om₀ e) {t g₁ p t' h₁ p'} (h1 : IsLevi H t g₁ p) (h2 : IsLevi H' t' h₁ p') {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) : e (om (p, p') Φ) = ((χW t : ℂ) * (((absE F E t : ℝ) ^ rX : ℝ) : ℂ) *
      ((χX t' : ℂ) * (((absE F E t' : ℝ) ^ rW : ℝ) : ℂ))) • om₀ (g₁, h₁) (e Φ) := by
  simpa using h t g₁ p h1 1 (one_mem _) t' h₁ p' h2 1 (one_mem _) Φ hΦ

theorem Mix2.uni (h : Mix2 H H' χX χW rX rW om om₀ e) {m} (hm : m ∈ unip σ X H) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    e (om (m, 1) Φ) = e Φ := by
  simpa [← Prod.one_eq_mk] using h 1 1 1 (levi_one H) m hm 1 1 1 (levi_one H') 1 (one_mem _) Φ hΦ

theorem rpow_c {a : ℝ} (ha : 0 < a) (x y : ℝ) : ((a ^ x : ℝ) : ℂ) * ((a ^ y : ℝ) : ℂ) = ((a ^ (x + y) : ℝ) : ℂ) := by
  rw [Real.rpow_add ha, Complex.ofReal_mul]

theorem lawsTA (hp : IsPair B M χX χW om r s r' s') (hM : Mix2 H H' χX χW ((d₁ : ℝ) / 2) ((n : ℝ) / 2) om om₀ e)
    (hx : ∀ m ∈ unip σ X H, mat m *ᵥ incV F H.x = incV F H.x) :
    LawsT B M om om₀ H H' e (shiftA H H') (fun l => (χW⁻¹ l : ℂ) * (((absE F E l : ℝ) ^ ((n : ℝ) - 1 - d₁ / 2) : ℝ) : ℂ))
      fun l => l⁻¹ := by
  have hs := fun w Ψ h => rho_mem M hp.base.std w (Φ := Ψ) h
  refine ⟨inv_one, by simp, fun m hm Ψ hΨ => ?_, fun l g₁ p h₁ p' h1 h2 Ψ hΨ => ?_⟩
  · unfold shiftA
    rw [rho_om hp _ _ _ _ _ hΨ, hM.uni hm (hs _ _ hΨ), mat_inv_mulVec m (hx m hm), inv_one, mat_one', Matrix.one_mulVec]
  · unfold shiftA
    rw [rho_om hp _ _ _ _ _ hΨ, hM.levi h1 h2 (hs _ _ hΨ), isLevi_inv' h1, levi_inv_y h2, smul_smul]
    simp only [inv_inv, Units.val_one, map_one, one_smul, Matrix.smul_vecMulVec, NNReal.coe_one, Real.one_rpow, Circle.coe_one,
      Complex.ofReal_one, mul_one, map_inv, MonoidHom.inv_apply]
    congr 1
    have ha := absE_pos (F := F) l
    rw [mul_left_comm, NNReal.coe_inv, rpow_c (inv_pos.2 ha), Real.inv_rpow ha.le, ← Real.rpow_neg ha.le]
    congr 3
    ring

theorem lawsA (hp : IsPair B M χX χW om r s r' s') (hM : Mix2 H H' χX χW ((d₁ : ℝ) / 2) ((n : ℝ) / 2) om om₀ e) {z : ℕ}
    (hz : 2 * n = d + 2 * z) (hd : d = d₁ + 2) (hx : ∀ m ∈ unip σ X H, mat m *ᵥ incV F H.x = incV F H.x) :
    Laws B M om om₀ H H' e (shiftA H H') χW⁻¹ (χX / χW) z fun l => l⁻¹ := by
  have hs := fun w Ψ h => rho_mem M hp.base.std w (Φ := Ψ) h
  have hd' : (d : ℝ) = d₁ + 2 := by exact_mod_cast hd
  have hz' : (2 * n : ℝ) = d + 2 * z := by exact_mod_cast hz
  refine ⟨?_, fun t h₁ p' h2 => ⟨GlobalTheory.Doubling.conjUnit σ t, fun l Ψ hΨ => ?_⟩⟩
  · convert lawsTA hp hM hx using 3 with l
    rw [← Complex.ofReal_pow, ← Real.rpow_natCast]
    congr 2
    linarith
  · unfold shiftA
    rw [rho_om hp _ _ _ _ _ hΨ, hM.levi (levi_one H) h2 (hs _ _ hΨ), levi_inv_y h2, inv_one, mat_one', Matrix.one_mulVec,
      Matrix.vecMulVec_smul, smul_smul, Units.val_mul, conjUnit_val]
    congr 1
    have ha := absE_pos (F := F) t
    simp only [map_one, NNReal.coe_one, Real.one_rpow, Circle.coe_one, Complex.ofReal_one, mul_one, one_mul, MonoidHom.inv_apply,
      chi_conj hp.base.cm hp.resW, inv_inv, GlobalTheory.Doubling.absE_conjUnit, MonoidHom.div_apply, Circle.coe_div]
    rw [← Complex.ofReal_pow, ← Real.rpow_natCast, show (n : ℝ) / 2 = (d - n) / 2 + z by linarith, ← rpow_c ha]
    field_simp

theorem sy_iso (hx : form σ W.J H'.x H'.x = 0) (a b : Fin n → AE F E) :
    sy σ X W (Matrix.vecMulVec a (incV F H'.x)) (Matrix.vecMulVec b (incV F H'.x)) = 0 := by
  have h0 : ∑ j, ∑ l, incV F H'.x j * incM F W.J j l * cA σ (incV F H'.x l) = 0 := by
    have := congrArg (inclR (F := F) (AF F)) hx
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, map_zero] at this
    simpa [incV, incM, cA, inclR, mul_assoc] using this
  have : hTens (cA σ) (incM F X.J) (incM F W.J) (Matrix.vecMulVec a (incV F H'.x)) (Matrix.vecMulVec b (incV F H'.x)) = 0 := by
    calc _ = ∑ i, ∑ k, a i * incM F X.J i k * cA σ (b k) * ∑ j, ∑ l, incV F H'.x j * incM F W.J j l * cA σ (incV F H'.x l) := by
          simp only [hTens, Matrix.vecMulVec_apply, map_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
      _ = 0 := by simp [h0]
  simp only [sy, symp, this, mul_zero, map_zero]

theorem lawsB {M₀ : Model σ X₁ W₁} (hp : IsPair B M χX χW om r s r' s') (he : IsEv B M M₀ H.ι H'.ι (isoB H H') e)
    (hM : Mix2 H H' χX χW ((d : ℝ) / 2) ((n₁ : ℝ) / 2) om om₀ e) {z : ℕ}
    (hz : d + 2 = 2 * n + 2 * z) (hn : n = n₁ + 2) (hxx : form σ W.J H'.x H'.x = 0)
    (hy : ∀ m ∈ unip σ X H, ∃ (y : Fin n₁ → AE F E) (c : AE F E),
      mat m *ᵥ incV F H.y = incV F H.y + incM F H.ι *ᵥ y + c • incV F H.x) :
    Laws B M om om₀ H H' e (shiftB σ H H') χW (χX / χW) z id := by
  have hs := fun w Ψ h => rho_mem M hp.base.std w (Φ := Ψ) h
  have hz' : (d : ℝ) + 2 = 2 * n + 2 * z := by exact_mod_cast hz
  have hn' : (n : ℝ) = n₁ + 2 := by exact_mod_cast hn
  refine ⟨⟨rfl, by simp, fun m hm Ψ hΨ => ?_, fun l g₁ p h₁ p' h1 h2 Ψ hΨ => ?_⟩,
    fun t h₁ p' h2 => ⟨(GlobalTheory.Doubling.conjUnit σ t)⁻¹, fun l Ψ hΨ => ?_⟩⟩
  · unfold shiftB
    obtain ⟨y, c, hy'⟩ := hy m⁻¹ (inv_mem hm)
    rw [rho_om hp _ _ _ _ _ hΨ, hM.uni hm (hs _ _ hΨ), hy', inv_one, mat_one', Matrix.one_mulVec, Units.val_one, map_one, one_smul,
      one_smul, Matrix.add_vecMulVec, Matrix.add_vecMulVec, add_comm, ← rho_rho_of M.co B.ψ _ _ (by
        rw [← Matrix.add_vecMulVec]; exact sy_iso hxx _ _), he.inv _ (Or.inl ⟨c • incV F H'.x, by
        rw [Matrix.smul_vecMulVec, Matrix.vecMulVec_smul]⟩) _ (hs _ _ hΨ), add_comm, ← rho_rho_of M.co B.ψ _ _ (sy_iso hxx _ _),
      he.inv _ (Or.inr ⟨y, rfl⟩) _ (hs _ _ hΨ)]
  · unfold shiftB
    rw [rho_om hp _ _ _ _ _ hΨ, hM.levi h1 h2 (hs _ _ hΨ), levi_inv_y h1, isLevi_inv' h2, smul_smul]
    simp only [id, inv_one, Units.val_one, map_one, one_smul, Matrix.smul_vecMulVec, NNReal.coe_one, Real.one_rpow, Circle.coe_one,
      Complex.ofReal_one, mul_one]
    congr 1
    have ha := absE_pos (F := F) l
    rw [mul_left_comm, rpow_c ha, ← Complex.ofReal_pow, ← Real.rpow_natCast]
    congr 3
    linarith
  · unfold shiftB
    have hc : cA σ (l * (GlobalTheory.Doubling.conjUnit σ t)⁻¹ : (AE F E)ˣ).1 = cA σ l.1 * (t⁻¹ : (AE F E)ˣ).1 := by
      rw [Units.val_mul, map_mul, ← map_inv, conjUnit_val, cA_cA hp.base.cm]
    rw [rho_om hp _ _ _ _ _ hΨ, hM.levi (levi_one H) h2 (hs _ _ hΨ), isLevi_inv' h2, inv_one, mat_one', Matrix.one_mulVec,
      Matrix.vecMulVec_smul, smul_smul, hc]
    congr 1
    have ha := absE_pos (F := F) t
    simp only [map_one, NNReal.coe_one, Real.one_rpow, Circle.coe_one, Complex.ofReal_one, mul_one, one_mul, map_inv,
      chi_conj hp.base.cm hp.resW, inv_inv, GlobalTheory.Doubling.absE_conjUnit, MonoidHom.div_apply, Circle.coe_div, NNReal.coe_inv]
    rw [← Complex.ofReal_pow, ← Real.rpow_natCast, Real.inv_rpow ha.le, ← Real.rpow_neg ha.le,
      show (n₁ : ℝ) / 2 = (d - n) / 2 + -z by linarith, ← rpow_c ha]
    field_simp

end

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.SliceSummable
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d n₁ d₁ m : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
  {M : Model σ X W} {M₁ : Model σ X₁ W₁} {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E}
  {I : Set (Ten F E n d)} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {u z : Fin m → Matrix (Fin n) (Fin d) E}

def rhoL (B : Base F E) (M : Model σ X W) (w : Ten F E n d) : Fn F n d →ₗ[ℂ] Fn F n d where
  toFun := M.co.rho B.ψ w
  map_add' := rho_add _ _ _
  map_smul' := rho_smul _ _ _

theorem slice_summable (hS : Slice) (hB : B.IsGood σ) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) (he : IsEv B M M₁ ι ι' I e)
    (hD : Dual σ X W I u z) {l} (hl : l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁)) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    Summable fun y : Fin m → F => l (e (rhoL B M (lin u fun j => algebraMap F (AF F) (y j)) Φ)) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨wt, P, h1, -, -, h2⟩ := slice_bound hS hB hM hM₁ he hD hl hg
    exact Summable.of_norm_bounded (h1.mul_left (P f)) fun y => h2 y f
  | zero => simpa using summable_zero
  | add Φ Ψ _ _ h1 h2 => simpa only [map_add (f := _)] using h1.add h2
  | smul c Φ _ h => simpa only [map_smul, smul_eq_mul] using h.mul_left c

theorem slice_adm (hS : Slice) (hB : B.IsGood σ) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) (he : IsEv B M M₁ ι ι' I e)
    (hD : Dual σ X W I u z) {l} (hl : l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁)) :
    ∃ L ∈ (adeleClass F).adm (Fin n × Fin d), ∀ Φ ∈ schA F (Fin n × Fin d),
      HasSum (fun y : Fin m → F => l (e (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (y j)) Φ))) (L Φ) := by
  let L₀ : schA F (Fin n × Fin d) →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => ∑' y : Fin m → F, l (e (rhoL B M (lin u fun j => algebraMap F (AF F) (y j)) Φ.1))
      map_add' := fun Φ Ψ => by
        simp only [Submodule.coe_add, map_add (f := _)]
        exact (slice_summable hS hB hM hM₁ he hD hl Φ.2).tsum_add (slice_summable hS hB hM hM₁ he hD hl Ψ.2)
      map_smul' := fun c Φ => by
        simp only [Submodule.coe_smul, map_smul, smul_eq_mul, RingHom.id_apply]
        exact tsum_mul_left }
  obtain ⟨L, hL⟩ := LinearMap.exists_extend L₀
  have hL' : ∀ Φ ∈ schA F (Fin n × Fin d),
      HasSum (fun y : Fin m → F => l (e (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (y j)) Φ))) (L Φ) := fun Φ hΦ => by
    rw [show L Φ = L₀ ⟨Φ, hΦ⟩ from LinearMap.congr_fun hL ⟨Φ, hΦ⟩]
    exact (slice_summable hS hB hM hM₁ he hD hl hΦ).hasSum
  refine ⟨L, fun g hg => ?_, hL'⟩
  obtain ⟨wt, P, h1, h2, h3, h4⟩ := slice_bound hS hB hM hM₁ he hD hl hg
  let T : SInf F (Fin n × Fin d) →ₗ[ℂ] ℂ :=
    { toFun := fun f => L (pureA F f g)
      map_add' := fun f₁ f₂ => by
        rw [← map_add (f := _)]; congr 1; funext x; simp [pureA, add_mul]
      map_smul' := fun c f => by
        rw [RingHom.id_apply, ← map_smul]; congr 1; funext x; simp [pureA, mul_assoc] }
  refine ⟨⟨T, continuous_of_continuousAt_zero T ?_⟩, fun f => rfl⟩
  rw [ContinuousAt, map_zero]
  refine squeeze_zero_norm (a := fun f => P f * ∑' y, wt y) (fun f => ?_) ?_
  · exact (hL' _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)).norm_le_of_bounded (h1.hasSum.mul_left (P f)) fun y => h4 y f
  · simpa [h3] using (h2.tendsto 0).mul_const (∑' y, wt y)

theorem term_zero (h : IsStd B.ψ) (a : (Fin m → F) → Fn F n d → ℂ)
    (ha : ∀ y t, ∀ Φ ∈ schA F (Fin n × Fin d), a y (M.co.rho B.ψ (lin z t) Φ) =
      B.ψ (-((fun j => algebraMap F (AF F) (y j)) ⬝ᵥ t)) * a y Φ)
    (h0 : ∀ Φ ∈ schA F (Fin n × Fin d), HasSum (fun y => a y Φ) 0) (y) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) : a y Φ = 0 := by
  refine fourier_uniq h (fun y => a y Φ) (h0 Φ hΦ).summable (fun t => ?_) y
  rw [← (h0 _ (rho_mem M h (lin z (-t)) hΦ)).tsum_eq]
  exact tsum_congr fun y => by rw [ha y _ Φ hΦ, dotProduct_neg, neg_neg, mul_comm]

theorem thetaExp_of (hS : Slice) : ThetaExp := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e he m u z hP
  have h := hB.std
  obtain ⟨l, hl, hθ⟩ := (GlobalTheory.CompanionTheory.ThetaAdm.theta_adm F (Fin n₁ × Fin d₁)).2.1
  obtain ⟨L, hL, hs⟩ := slice_adm hS hB hM hM₁ he hP.toDual hl
  have hs' : ∀ Φ ∈ schA F (Fin n × Fin d), HasSum (fun y : Fin m → F =>
      thetaSum F (e (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (y j)) Φ))) (L Φ) := fun Φ hΦ => by
    simpa only [hθ _ (he.maps _ (rho_mem M h _ hΦ))] using hs Φ hΦ
  have hu : ∀ a : Fin m → F, ∀ Φ ∈ schA F (Fin n × Fin d),
      L (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (a j)) Φ) = L Φ := fun a Φ hΦ => by
    refine (hs' _ (rho_mem M h _ hΦ)).unique ?_
    have := (Equiv.addRight a).hasSum_iff.2 (hs' Φ hΦ)
    convert this using 2 with y
    rw [rho_rho_of _ _ _ _ (sy_lin_uu M hP _ _), ← lin_add]
    simp only [Function.comp_apply, Equiv.coe_addRight, Pi.add_apply, map_add (f := _)]
    rfl
  have hz : ∀ b : Fin m → F, ∀ Φ ∈ schA F (Fin n × Fin d),
      L (M.co.rho B.ψ (lin z fun j => algebraMap F (AF F) (b j)) Φ) = L Φ := fun b Φ hΦ => by
    refine (hs' _ (rho_mem M h _ hΦ)).unique ?_
    convert hs' Φ hΦ using 2 with y
    rw [ev_rho_uz h he hP _ _ hΦ,
      show -((fun j => algebraMap F (AF F) (y j)) ⬝ᵥ fun j => algebraMap F (AF F) (b j)) = algebraMap F (AF F) (-(y ⬝ᵥ b)) by
        simp [dotProduct], h.2.1, one_smul]
  have hm : ∀ x₁ : Matrix (Fin n₁) (Fin d₁) E, ∀ Φ ∈ schA F (Fin n × Fin d),
      L (M.co.rho B.ψ (incM F ι * incM F x₁ * (incM F ι')ᵀ) Φ) = L Φ := fun x₁ Φ hΦ => by
    refine (hs' _ (rho_mem M h _ hΦ)).unique ?_
    convert hs' Φ hΦ using 2 with y
    obtain ⟨a, b, hab⟩ := hM₁.rat x₁
    rw [ev_rho_um h he hP _ _ hΦ, Darboux.rho, hab, theta_schr_rat h]
  obtain ⟨c, hc⟩ := thetaUniq_of F (Fin n × Fin d) B.ψ h L hL fun ξ η Φ hΦ => by
    obtain ⟨x, hx⟩ := rat_surj hB.cm.2.2.1 M.co.e hM.rat ξ η
    obtain ⟨a, b, x₁, hr⟩ := rho_rat (M := M) h hP x
    rw [← hx, ← Darboux.rho, hr, hu _ _ (rho_mem M h _ (rho_mem M h _ hΦ)), hz _ _ (rho_mem M h _ hΦ), hm _ _ hΦ]
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨Φ, hΦ, hne⟩ := ev_ne_zero hM hM₁ he
    refine hne (thetaInj_of F _ B.ψ h _ (he.maps Φ hΦ) fun w => ?_)
    obtain ⟨w, rfl⟩ := M₁.co.e.surjective w
    have := term_zero (M := M) (z := z) h
      (fun y Φ => thetaSum F (e (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (y j)) Φ)))
      (fun y t Φ hΦ => by rw [ev_rho_uz h he hP _ _ hΦ, thetaSum_smul])
      (fun Φ hΦ => by simpa only [hc Φ hΦ, zero_mul] using hs' Φ hΦ) 0 (rho_mem M h (incM F ι * w * (incM F ι')ᵀ) hΦ)
    rwa [show (fun j => algebraMap F (AF F) ((0 : Fin m → F) j)) = 0 from funext fun j => map_zero _, lin_zero, rho_zero,
      he.Heisenberg₂ _ _ hΦ] at this
  refine ⟨c⁻¹, inv_ne_zero hc0, fun Φ hΦ => ?_⟩
  simpa only [hc Φ hΦ, inv_mul_cancel_left₀ hc0] using (hs' Φ hΦ).mul_left c⁻¹

theorem evUniq_of (hE : ThetaExp) : EvUniq := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e e' he he' m u z hP
  have h := hB.std
  obtain ⟨C, hC, hs⟩ := hE F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e he m u z hP
  obtain ⟨C', hC', hs'⟩ := hE F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e' he' m u z hP
  refine ⟨C'⁻¹ * C, mul_ne_zero (inv_ne_zero hC') hC, fun Φ hΦ => ?_⟩
  have key : C • e Φ + (-C') • e' Φ = 0 := by
    refine thetaInj_of F _ B.ψ h _ (add_mem (Submodule.smul_mem _ _ (he.maps Φ hΦ)) (Submodule.smul_mem _ _ (he'.maps Φ hΦ)))
      fun w => ?_
    obtain ⟨w, rfl⟩ := M₁.co.e.surjective w
    have := term_zero (M := M) (z := z) h
      (fun y Φ => C * thetaSum F (e (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (y j)) Φ)) -
        C' * thetaSum F (e' (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (y j)) Φ)))
      (fun y t Φ hΦ => by rw [ev_rho_uz h he hP _ _ hΦ, ev_rho_uz h he' hP _ _ hΦ, thetaSum_smul, thetaSum_smul]; ring)
      (fun Φ hΦ => by simpa only [sub_self] using (hs Φ hΦ).sub (hs' Φ hΦ)) 0 (rho_mem M h (incM F ι * w * (incM F ι')ᵀ) hΦ)
    rw [show (fun j => algebraMap F (AF F) ((0 : Fin m → F) j)) = 0 from funext fun j => map_zero _, lin_zero, rho_zero,
      he.Heisenberg₂ _ _ hΦ, he'.Heisenberg₂ _ _ hΦ] at this
    rw [← Darboux.rho, rho_add, rho_smul, rho_smul,
      thetaSum_add F (Submodule.smul_mem _ _ (rho_mem M₁ h _ (he.maps Φ hΦ))) (Submodule.smul_mem _ _ (rho_mem M₁ h _ (he'.maps Φ hΦ))),
      thetaSum_smul, thetaSum_smul, ← this]
    ring
  rw [mul_smul, eq_neg_of_add_eq_zero_left key, neg_smul, neg_neg, smul_smul, inv_mul_cancel₀ hC', one_smul]

end PositivityTheory.ThKCT
end
end

