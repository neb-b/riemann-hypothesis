module

public import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
public import Development.WeilBound.ThetaLifts.SmallCones.ConeCore
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Mathlib
public import Development.WeilBound.ThetaLifts.SchwartzMoments.PolynomialFunctionalEvalContinuous

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.ConeAB
section
set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem domSo (hS : SoSemi) (hV : FinVolU) (hE : EpsOf) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W}
    {χX χW om r s r' s'} (hp : IsPair B M χX χW om r s r' s') : Dom M om (soFin B M) := by
  intro φ hφ
  obtain ⟨p, k, hc, h⟩ := hS F E σ B n d X W M χX χW om r s r' s' hp φ hφ 0
  refine ⟨p, k, fun _ => 1, hc, measurable_const, ?_, fun f g y => ?_⟩
  · rw [setLIntegral_one]
    exact hV F E σ hp.base.cm n X.J (hE F E σ B hp.base n X r s (Or.inl hp.herm)).1 M.μ M.dom hp.good.haar hp.good.dom
  · rw [mul_one, ← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (by simpa using h f g y)

theorem incM_vecMulVec {n d : ℕ} (x : Fin n → E) (y : Fin d → E) :
    incM F (Matrix.vecMulVec x y) = Matrix.vecMulVec (incV F x) (incV F y) := by
  ext i j
  simp [incM, incV, Matrix.vecMulVec_apply]

theorem hTens_vec {n d : ℕ} (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E) (x x' : Fin n → E) (y y' : Fin d → E) :
    hTens (cA σ) (incM F J) (incM F J') (incM F (Matrix.vecMulVec x y)) (incM F (Matrix.vecMulVec x' y')) =
      inclR (F := F) (AF F) (form σ J x x' * form σ J' y y') := by
  have hc : ∀ a : E, cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := fun a => by simp [cA, inclR]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hTens, incM, Matrix.map_apply, Matrix.vecMulVec_apply, hc, ← map_mul, ← map_sum, form, dotProduct, Matrix.mulVec]
  congr 1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum _ _ (x i), Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [map_mul]; ring

theorem form_swap (hσ : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {ε : E} (h : ∀ i j, σ (J j i) = ε * J i j)
    (x y : Fin n → E) : σ (form σ J x y) = ε * form σ J y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, cm_conj_conj hσ, Finset.mul_sum, h]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem coneA_of (hUn : Unfold) (hU : UnipEx) (hD : StabDec) (hTB : ThetaBasic) (hG : GrpTop) (hE : EpsOf) (hA : EvAdm)
    (hM : MixAB) (hL : LineInt) (hW : DomWeil) : ConeA := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' e he z hz K μK μ hI hμK hμ
  obtain ⟨κ, hκ, h⟩ := cone_core hUn hU hD hTB hG hE hA (r := r + 1) (s := s + 1) (r' := r' + 1) (s' := s' + 1) (r₀ := r) (s₀ := s)
    (r₀' := r') (s₀' := s') hH hH' he hI hμK hμ (shiftA H H') z _ (Or.inr rfl)
  refine ⟨κ, hκ, fun χX χW om om₀ hp hp₀ Φ hΦ hK => ?_⟩
  have hν : Continuous (χW⁻¹ : Chr F E) := hp.hW.1.inv
  have hyx : form σ X.J H.y H.x = 1 := by
    have := form_swap hp.base.cm (J := X.J) (ε := 1) (fun i j => by rw [one_mul, hp.herm.herm]) H.x H.y
    rw [hH.xy, map_one, one_mul] at this
    exact this.symm
  have key := fun Ψ hΨ => hL F E σ B n d n₁ d₁ X W X₁ W₁ M M₀ hp.base hp.good hp₀.good _ _ _ e he
    (Matrix.vecMulVec H.x H'.y) (Matrix.vecMulVec H.y H'.x)
    (fun a => Or.inl ⟨a • incV F H.y, by rw [incM_vecMulVec, Matrix.smul_vecMulVec]⟩)
    (by rw [hTens_vec, hyx, hH'.xy, mul_one, map_one]; exact isUnit_one) (AlgHom.id _ _) (Or.inl rfl) μ hμ z χW⁻¹ (by omega) hν Ψ hΨ
  simp only [incM_vecMulVec, AlgHom.id_apply] at key
  have h1 := hH.rank
  have h2 := hH'.rank
  exact h χX χW om om₀ hp hp₀ χW⁻¹ (χX / χW) (schA F _) hν
    (lawsA hp ((hM F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' χX χW om om₀ hp hp₀).1 e he) hz.1 h2
      fun m hm => ((hU F E σ B n n₁ X X₁ H j₀ j₁ _ _ hp.base (Or.inl hp.herm) hH).2.2.2.2.2.1 m hm).1)
    (fun _ h => h) (fun x Ψ h => pair_pres hp x h)
    (fun Ψ hΨ h₁ => (key Ψ hΨ).1 om₀ (fun x Φ h => pair_pres hp₀ x h)
      (Or.inl (hW F E σ B _ _ X₁ W₁ M₀ χX χW om₀ r s r' s' hp₀ (Or.inl (by omega)))) h₁)
    (fun Ψ hΨ => (key Ψ hΨ).2) Φ hΦ hK

theorem coneB_of (hUn : Unfold) (hU : UnipEx) (hD : StabDec) (hTB : ThetaBasic) (hG : GrpTop) (hE : EpsOf) (hA : EvAdm)
    (hM : MixAB) (hL : LineInt) (hS : SoSemi) (hV : FinVolU) (hSF : SoFin) (hSt : SoStab) (hSe : SoEv) : ConeB := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' e he z hz K μK μ hI hμK hμ
  obtain ⟨κ, hκ, h⟩ := cone_core hUn hU hD hTB hG hE hA (r := r + 1) (s := s + 1) (r' := r' + 1) (s' := s' + 1) (r₀ := r) (s₀ := s)
    (r₀' := r') (s₀' := s') hH hH' he hI hμK hμ (shiftB σ H H') z _ (Or.inl rfl)
  refine ⟨κ, hκ, fun χX χW om om₀ hp hp₀ Φ hΦ hK => ?_⟩
  have hyx : form σ W.J H'.y H'.x = -1 := by
    have := form_swap hp.base.cm (J := W.J) (ε := -1) (fun i j => by rw [neg_one_mul, hp.skew.skew]) H'.x H'.y
    rw [hH'.xy, map_one, neg_one_mul] at this
    rw [this, neg_neg]
  have key := fun Ψ hΨ => hL F E σ B n d n₁ d₁ X W X₁ W₁ M M₀ hp.base hp.good hp₀.good _ _ _ e he
    (Matrix.vecMulVec H.y H'.x) (Matrix.vecMulVec H.x H'.y)
    (fun a => Or.inl ⟨a • incV F H'.y, by rw [incM_vecMulVec, Matrix.vecMulVec_smul]⟩)
    (by rw [hTens_vec, hyx, hH.xy, one_mul, map_neg, map_one]; exact isUnit_one.neg) (cA σ) (Or.inr rfl) μ hμ z χW hz.2 hp.hW.1 Ψ hΨ
  have hle := (hSF F E σ B n d X W M χX χW om _ _ _ _ hp).2.2.1
  have hso := fun Ψ hΨ => (hSe F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ _ _ _ _ M M₀ hH hH' hp.base hp.herm hp.skew hp.good
    hp₀.good e he Ψ hΨ).2
  simp only [incM_vecMulVec] at key hso
  exact h χX χW om om₀ hp hp₀ χW (χX / χW) (M.So B.ψ B.τ₁) hp.hW.1
    (lawsB hp he ((hM F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' χX χW om om₀ hp hp₀).2 e he) hz.1 hH.rank
      hH'.xx fun m hm => ((hU F E σ B n n₁ X X₁ H j₀ j₁ _ _ hp.base (Or.inl hp.herm) hH).2.2.2.2.2.1 m hm).2)
    hle (hSt F E σ B n d X W M χX χW om _ _ _ _ hp)
    (fun Ψ hΨ h₁ => (key Ψ (hle Ψ hΨ)).1 om₀ (fun x Φ h => pair_pres hp₀ x h) (Or.inr ⟨domSo hS hV hE hp₀, hso Ψ hΨ⟩) h₁)
    (fun Ψ hΨ => (key Ψ hΨ).2) Φ hΦ hK

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.ContinuousEvI
section
set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT.Ker

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)
open Matrix (vecMulVec)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem continuous_evI : Continuous (evI F) := by
  have : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    change Continuous fun x : InfiniteAdeleRing F =>
      ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
       (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
    refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
    · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)
  exact this.comp continuous_fst

theorem sz_le {κ : Type} [Fintype κ] (y : κ → AF F) :
    PositivityTheory.ThKCT.sz y ≤ (1 + Fintype.card κ * Fintype.card (InfinitePlace F)) * (1 + ‖fun j => evI F (y j)‖) := by
  have h : ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (y j)) ≤
      ∑ _j : κ, ∑ _w : InfinitePlace F, ‖fun j => evI F (y j)‖ :=
    Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun w _ => by
      refine le_trans ?_ (norm_le_pi_norm (fun j => evI F (y j)) j)
      rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
      exact Finset.le_sup' (fun w => mixedEmbedding.normAtPlace w (evI F (y j))) (Finset.mem_univ w)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  have h0 := norm_nonneg fun j => evI F (y j)
  have h1 : (0 : ℝ) ≤ Fintype.card κ * Fintype.card (InfinitePlace F) := by positivity
  unfold PositivityTheory.ThKCT.sz
  nlinarith

theorem theta_unif {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    ∃ p : Seminorm ℂ (SInf F κ), Continuous p ∧ ∀ (f : SInf F κ) w, ‖thetaSum F (schr ψ w (pureA F f g))‖ ≤ p f := by
  obtain ⟨K, hK, hc⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  obtain ⟨G, hG⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  have hKp : IsCompact (Set.univ.pi fun _ : κ => K) := isCompact_univ_pi fun _ => hK
  obtain ⟨A, hA⟩ := hKp.exists_bound_of_continuousOn
    (f := fun k : κ → AF F => fun j => evI F (k j)) (continuous_pi fun j => continuous_evI.comp (continuous_apply j)).continuousOn
  have hC : IsCompact ((fun x : (κ → Af F) × (κ → AF F) => x.1 - fun j => (x.2 j).2) '' (tsupport g ×ˢ Set.univ.pi fun _ : κ => K)) :=
    (hg.2.isCompact.prod hKp).image (continuous_fst.sub (continuous_pi fun j => ((continuous_apply j).comp continuous_snd).snd))
  obtain ⟨N, hN⟩ := summable_wt hC
  set C := (fun x : (κ → Af F) × (κ → AF F) => x.1 - fun j => (x.2 j).2) '' (tsupport g ×ˢ Set.univ.pi fun _ : κ => K) with hCd
  set wt : (κ → F) → ℝ := fun ξ => if (fun j => (algebraMap F (AF F) (ξ j)).2) ∈ C then
    (PositivityTheory.ThKCT.sz (fun j => algebraMap F (AF F) (ξ j)) ^ N)⁻¹ else 0 with hwt
  have hw0 : ∀ ξ, 0 ≤ wt ξ := fun ξ => by
    rw [hwt]; dsimp only; split_ifs
    · exact inv_nonneg.2 (pow_pos (sz_pos _) _).le
    · exact le_rfl
  set c : ℝ := (1 + Fintype.card κ * Fintype.card (InfinitePlace F)) * (1 + |A|) with hcdef
  have hc0 : 0 < c := by positivity
  let q : Seminorm ℂ (SInf F κ) := (Finset.Iic (N, 0)).sup (schwartzSeminormFamily ℂ _ ℂ)
  have hq : Continuous q := Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm i
  let D : ℝ≥0 := ⟨2 ^ N * G * c ^ N * ∑' ξ, wt ξ, mul_nonneg (by positivity) (tsum_nonneg hw0)⟩
  refine ⟨D • q, hq.const_smul D, fun f w => ?_⟩
  choose a ha using fun j => hc (w.1 j)
  set k : κ → AF F := fun j => w.1 j - algebraMap F (AF F) (a j) with hk
  have hkK : k ∈ Set.univ.pi fun _ : κ => K := fun j _ => ha j
  have key : ∀ ξ : κ → F, ‖schr ψ w (pureA F f g) fun i => algebraMap F (AF F) (ξ i)‖ ≤ (2 ^ N * G * c ^ N * q f) * wt (ξ + a) := by
    intro ξ
    have e : (fun i => algebraMap F (AF F) (ξ i)) + w.1 = (fun i => algebraMap F (AF F) ((ξ + a) i)) + k := by
      funext i; simp [hk]
    rw [schr, norm_mul, std_norm hψ, one_mul, e]
    set η := ξ + a
    set y : κ → AF F := fun i => algebraMap F (AF F) (η i)
    change ‖f (fun i => evI F ((y + k) i)) * g (fun i => ((y + k) i).2)‖ ≤ _
    by_cases h0 : g (fun i => ((y + k) i).2) = 0
    · rw [h0, mul_zero, norm_zero]
      exact mul_nonneg (by positivity) (hw0 _)
    have hm : wt η = (PositivityTheory.ThKCT.sz y ^ N)⁻¹ := if_pos ⟨(_, k), ⟨subset_tsupport g h0, hkK⟩, by
      funext i
      change (y i).2 + (k i).2 - (k i).2 = _
      rw [add_sub_cancel_right]⟩
    set v : κ → mixedEmbedding.mixedSpace F := fun i => evI F ((y + k) i)
    have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N, 0)) (k := N) (n := 0) le_rfl le_rfl f v
    rw [norm_iteratedFDeriv_zero] at h1
    have h2 : PositivityTheory.ThKCT.sz y ≤ c * (1 + ‖v‖) := by
      refine (sz_le y).trans ?_
      rw [hcdef, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have e2 : (fun j => evI F (y j)) = v - fun j => evI F (k j) := funext fun j =>
        eq_sub_of_add_eq (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (y j).1 (k j).1).symm
      have := norm_sub_le v fun j => evI F (k j)
      have h3 := (hA k hkK).trans (le_abs_self A)
      rw [e2]
      nlinarith [norm_nonneg v, abs_nonneg A]
    rw [hm, ← div_eq_mul_inv, le_div_iff₀ (pow_pos (sz_pos _) _), norm_mul]
    calc _ ≤ ‖f v‖ * G * (c * (1 + ‖v‖)) ^ N :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hG _) (norm_nonneg _)) (pow_le_pow_left₀ (sz_pos _).le h2 N) (pow_pos (sz_pos _) _).le
            (by positivity)
      _ = G * c ^ N * ((1 + ‖v‖) ^ N * ‖f v‖) := by rw [mul_pow]; ring
      _ ≤ G * c ^ N * (2 ^ N * q f) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  have hs : HasSum (fun ξ => wt (ξ + a)) (∑' ξ, wt ξ) := (Equiv.addRight a).hasSum_iff.2 hN.hasSum
  refine (tsum_of_norm_bounded (hs.mul_left _) key).trans_eq ?_
  change _ = (2 ^ N * G * c ^ N * ∑' ξ, wt ξ) * q f
  ring

variable {n d n₁ d₁ m : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
  {M : Model σ X W} {M₁ : Model σ X₁ W₁} {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E}
  {I : Set (Ten F E n d)} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {u z : Fin m → Matrix (Fin n) (Fin d) E}

theorem slice_unif (hS : Slice) (hB : B.IsGood σ) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) (he : IsEv B M M₁ ι ι' I e)
    (hD : Dual σ X W I u z) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) : ∃ b : (Fin m → F) → ℝ, Summable b ∧ ∀ y w,
      ‖thetaSum F (M₁.co.rho B.ψ w (e (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (y j)) Φ)))‖ ≤ b y := by
  obtain ⟨l, -, hl⟩ := (GlobalTheory.CompanionTheory.ThetaAdm.theta_adm F (Fin n₁ × Fin d₁)).2.1
  have h := hB.std
  suffices ∃ b : (Fin m → F) → ℝ, Summable b ∧ ∀ y w,
      ‖l (rhoL B M₁ w (e (rhoL B M (lin u fun j => algebraMap F (AF F) (y j)) Φ)))‖ ≤ b y by
    obtain ⟨b, h1, h2⟩ := this
    exact ⟨b, h1, fun y w => by rw [← hl _ (rho_mem M₁ h _ (he.maps _ (rho_mem M h _ hΦ)))]; exact h2 y w⟩
  induction hΦ using Submodule.span_induction with
  | mem Φ h0 =>
    obtain ⟨f, φ, hφ, rfl⟩ := h0
    obtain ⟨r, φ₁, C, A, h1, hC, -, h2, h3, h4⟩ := hS F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e he m u z hD φ hφ
    obtain ⟨N, hN⟩ := summable_wt hC
    choose q hq hb using fun i => theta_unif h (h1 i)
    choose p hp hpq using fun i => h4 (q i) N (hq i)
    refine ⟨_, hN.mul_left (∑ i, p i f), fun y w => ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show e (rhoL B M _ _) = _ from h2 _ f, map_sum, map_sum]
    have hb' : ∀ i (f' : SInf F (Fin n₁ × Fin d₁)), ‖l (rhoL B M₁ w (pureA F f' (φ₁ i)))‖ ≤ q i f' := fun i f' =>
      (congrArg norm (hl _ (rho_mem M₁ h w (Submodule.subset_span ⟨f', _, h1 i, rfl⟩)))).trans_le (hb i f' _)
    split_ifs with hy
    · rw [Finset.sum_mul]
      refine norm_sum_le_of_le _ fun i _ => (hb' i _).trans ?_
      rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos (sz_pos _) _)]
      exact hpq i i _ f
    · refine (norm_sum_le_of_le _ fun i _ => hb' i _).trans ?_
      simp [h3 _ _ hy]
  | zero => exact ⟨0, summable_zero, fun y w => by simp⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨a, a1, a2⟩ := h1
    obtain ⟨b, b1, b2⟩ := h2
    exact ⟨a + b, a1.add b1, fun y w => by
      simp only [map_add (f := _)]; exact (norm_add_le _ _).trans (add_le_add (a2 y w) (b2 y w))⟩
  | smul c Φ _ h1 =>
    obtain ⟨a, a1, a2⟩ := h1
    exact ⟨fun y => ‖c‖ * a y, a1.mul_left _, fun y w => by
      simp only [map_smul, norm_smul]; exact mul_le_mul_of_nonneg_left (a2 y w) (norm_nonneg c)⟩

end PositivityTheory.ThKCT.Ker

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.KFinAn
section
noncomputable section

namespace PositivityTheory.ThKCT.So

open PositivityTheory.ThKOwn.KPol
open scoped SchwartzMap LineDeriv

section Fil

variable {S ι : Type} [AddCommGroup S] [Module ℂ S]

def fil (P : Submodule ℂ S) (D : ι → S →ₗ[ℂ] S) : ℕ → Submodule ℂ S
  | 0 => P
  | m + 1 => fil P D m ⊔ ⨆ i, (fil P D m).map (D i)

theorem fil_fin [Finite ι] (P : Submodule ℂ S) [FiniteDimensional ℂ P] (D : ι → S →ₗ[ℂ] S) (m : ℕ) :
    FiniteDimensional ℂ (fil P D m) := by
  induction m with
  | zero => exact (inferInstance : FiniteDimensional ℂ P)
  | succ m ih => exact (inferInstance : FiniteDimensional ℂ ↥(fil P D m ⊔ ⨆ i, (fil P D m).map (D i)))

theorem fil_mono (P : Submodule ℂ S) (D : ι → S →ₗ[ℂ] S) : Monotone (fil P D) := monotone_nat_of_le_succ fun _ => le_sup_left

theorem fil_step (P : Submodule ℂ S) (D : ι → S →ₗ[ℂ] S) {m : ℕ} {f g : S} (hf : f ∈ fil P D m)
    (hg : g ∈ Submodule.span ℂ (Set.range fun i => D i f)) : g ∈ fil P D (m + 1) := by
  refine (Submodule.span_le.2 ?_ : _ ≤ fil P D (m + 1)) hg
  rintro _ ⟨i, rfl⟩
  exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem i ⟨f, hf, rfl⟩)

theorem fil_stab (P : Submodule ℂ S) (D : ι → S →ₗ[ℂ] S) (A : S →ₗ[ℂ] S) (h0 : ∀ f ∈ P, A f ∈ P)
    (h : ∀ i f, A (D i f) ∈ Submodule.span ℂ (Set.range fun j => D j (A f))) (m : ℕ) : fil P D m ≤ (fil P D m).comap A := by
  induction m with
  | zero => exact h0
  | succ m ih =>
    refine sup_le (fun f hf => Submodule.mem_sup_left (ih hf)) (iSup_le fun i => ?_)
    rintro _ ⟨f, hf, rfl⟩
    exact fil_step P D (ih hf) (h i f)

end Fil

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (lam : V →ₗ[ℝ] V →L[ℝ] ℝ)

def dopL (w : V × V) : 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ) where
  toFun := dop w.1 (lam w.2)
  map_add' f g := by
    ext x
    have : fderiv ℝ (f + g : 𝓢(V, ℂ)) x = fderiv ℝ f x + fderiv ℝ g x := ((f.hasFDerivAt x).add (g.hasFDerivAt x)).fderiv
    simp only [SchwartzMap.add_apply, dop_apply, this, ContinuousLinearMap.add_apply]
    ring
  map_smul' c f := by
    ext x
    have : fderiv ℝ (c • f : 𝓢(V, ℂ)) x = c • fderiv ℝ f x := ((f.hasFDerivAt x).const_smul c).fderiv
    simp only [SchwartzMap.smul_apply, dop_apply, this, ContinuousLinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem dopL_apply (w : V × V) (f : 𝓢(V, ℂ)) : dopL lam w f = dop w.1 (lam w.2) f := rfl

def evD (f : 𝓢(V, ℂ)) (x : V) : V × V →ₗ[ℝ] ℂ where
  toFun w := dopL lam w f x
  map_add' a b := by
    simp only [dopL_apply, Prod.fst_add, Prod.snd_add, map_add (f := _), dop_add, SchwartzMap.add_apply]
  map_smul' c a := by
    simp only [dopL_apply, dop_apply, Prod.smul_fst, Prod.smul_snd, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply, Complex.real_smul]
    push_cast
    ring

theorem dopL_mem {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ (V × V)) (w : V × V) (f : 𝓢(V, ℂ)) :
    dopL lam w f ∈ Submodule.span ℂ (Set.range fun i => dopL lam (b i) f) := by
  have : dopL lam w f = ∑ i, (b.repr w i : ℂ) • dopL lam (b i) f := by
    ext x
    have h := congrArg (evD lam f x) (b.sum_repr w).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h
    rw [SchwartzMap.sum_apply]
    refine h.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_smul]
    rfl
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def vacs (S : Set ((V × V) × V × V)) : Submodule ℂ 𝓢(V, ℂ) :=
  ⨅ γ ∈ S, LinearMap.ker (dopL lam γ.2 - Complex.I • dopL lam γ.1)

theorem mem_vacs {S : Set ((V × V) × V × V)} {f : 𝓢(V, ℂ)} :
    f ∈ vacs lam S ↔ ∀ γ ∈ S, dopL lam γ.2 f = Complex.I • dopL lam γ.1 f := by
  simp only [vacs, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero]

theorem ray_zero (f : 𝓢(V, ℂ)) (x : V) (c : ℂ) (h : ∀ t : ℝ, fderiv ℝ f (t • x) x = t * c * f (t • x)) (h0 : f 0 = 0) : f x = 0 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (t • x) * Complex.exp (-((t : ℂ) ^ 2 * c / 2))) 0 t := fun t => by
    have h1 : HasDerivAt (fun t : ℝ => f (t • x)) (fderiv ℝ f (t • x) x) t :=
      (f.hasFDerivAt (t • x)).comp_hasDerivAt t (by simpa using (hasDerivAt_id t).smul_const x)
    have h2 : HasDerivAt (fun t : ℝ => -((t : ℂ) ^ 2 * c / 2)) (-(t * c)) t := by
      have := ((((hasDerivAt_id t).ofReal_comp).fun_pow 2).mul_const c).div_const 2 |>.fun_neg
      refine this.congr_deriv ?_
      simp
      ring
    refine (h1.fun_mul h2.cexp).congr_deriv ?_
    rw [h]
    ring
  have := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) 1 0
  simpa [h0] using this

theorem vacs_fin [FiniteDimensional ℝ V] (hl : Function.Injective lam) (S : Set ((V × V) × V × V)) (hS : ∀ p, ∃ γ ∈ S, γ.1 = p) :
    FiniteDimensional ℂ (vacs lam S) := by
  let Γ := Submodule.span ℝ S
  have hΓ : ∀ f ∈ vacs lam S, ∀ x, ∀ γ ∈ Γ, evD lam f x γ.2 = Complex.I * evD lam f x γ.1 := fun f hf x γ hγ => by
    induction hγ using Submodule.span_induction with
    | mem γ h => exact DFunLike.congr_fun ((mem_vacs lam).1 hf γ h) x
    | zero => simp
    | add a b _ _ ha hb => rw [Prod.fst_add, Prod.snd_add, map_add (f := _), map_add (f := _), ha, hb, mul_add]
    | smul c a _ ha => rw [Prod.smul_fst, Prod.smul_snd, map_smul, map_smul, ha, mul_smul_comm]
  have key : ∀ f ∈ vacs lam S, f 0 = 0 → f = 0 := fun f hf h0 => by
    let π : Γ →ₗ[ℝ] V × V := ((LinearMap.fst ℝ V V).prodMap (LinearMap.fst ℝ V V)) ∘ₗ Γ.subtype
    by_cases hπ : Function.Injective π
    · have h1 := LinearMap.finrank_le_finrank_of_injective hπ
      have h2 := LinearMap.finrank_le_finrank_of_surjective (f := LinearMap.fst ℝ (V × V) (V × V) ∘ₗ Γ.subtype) fun p => by
        obtain ⟨γ, h, e⟩ := hS p
        exact ⟨⟨γ, Submodule.subset_span h⟩, e⟩
      have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (le_antisymm h1 h2)).1 hπ
      ext x
      obtain ⟨⟨⟨⟨a, b⟩, a', b'⟩, hγ⟩, e⟩ := hs (0, x)
      obtain ⟨rfl, rfl⟩ : a = 0 ∧ a' = x := Prod.ext_iff.1 e
      refine ray_zero f a' (2 * Real.pi * Complex.I * (lam b' a' - Complex.I * lam b a')) (fun t => ?_) h0
      have := hΓ f hf (t • a') _ hγ
      simp only [evD, LinearMap.coe_mk, AddHom.coe_mk, dopL_apply, dop_apply, map_zero, map_smul, smul_eq_mul] at this
      push_cast at this
      linear_combination this
    · obtain ⟨⟨⟨⟨a, b⟩, a', b'⟩, hγ⟩, e, hne⟩ := (Submodule.ne_bot_iff _).1 fun h => hπ (LinearMap.ker_eq_bot.1 h)
      obtain ⟨rfl, rfl⟩ : a = 0 ∧ a' = 0 := Prod.ext_iff.1 e
      have hz : ∀ x, f x ≠ 0 → lam b x = 0 ∧ lam b' x = 0 := fun x hx => by
        have := hΓ f hf x _ hγ
        simp only [evD, LinearMap.coe_mk, AddHom.coe_mk, dopL_apply, dop_apply, map_zero] at this
        have h3 : (2 * Real.pi * Complex.I) * f x * (lam b' x - Complex.I * lam b x) = 0 := by linear_combination -this
        have h4 := (mul_eq_zero.1 h3).resolve_left (mul_ne_zero (by simp [Real.pi_ne_zero]) hx)
        have h5 := congrArg Complex.re h4
        have h6 := congrArg Complex.im h4
        simp at h5 h6
        exact ⟨h6, h5⟩
      by_contra hf0
      obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hf0 (SchwartzMap.ext hc)
      have hk : ∀ c, (∀ x, f x ≠ 0 → lam c x = 0) → c = 0 := fun c hc => by
        have ht : LinearMap.ker (lam c).toLinearMap = ⊤ := Submodule.eq_top_of_nonempty_interior' _
          ⟨x, mem_interior.2 ⟨{y | f y ≠ 0}, hc, isOpen_ne_fun f.continuous continuous_const, hx⟩⟩
        refine hl ?_
        rw [map_zero]
        ext y
        exact (ht ▸ Submodule.mem_top : y ∈ LinearMap.ker (lam c).toLinearMap)
      obtain rfl := hk b fun x hx => (hz x hx).1
      obtain rfl := hk b' fun x hx => (hz x hx).2
      exact hne rfl
  let ev : vacs lam S →ₗ[ℂ] ℂ := { toFun := fun f => f.1 0, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact FiniteDimensional.of_injective ev ((injective_iff_map_eq_zero ev).2 fun f h => Subtype.ext (key f.1 f.2 h))

theorem level_fin {X Y Z S : Type} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [AddCommGroup S] [Module ℂ S]
    (pt : X → Y → Z) (hpt : ∀ z, ∃ x y, z = pt x y) (c : S →ₗ[ℂ] (X → ℂ)) (P : Submodule ℂ S) [FiniteDimensional ℂ P] {C U : Set Y}
    (hC : IsCompact C) (hU : U ∈ nhds 0) (N : Submodule ℂ (Z → ℂ)) (h1 : ∀ Ψ ∈ N, ∀ y, ∃ f ∈ P, ∀ x, Ψ (pt x y) = c f x)
    (h2 : ∀ Ψ ∈ N, ∀ x, ∀ y ∉ C, Ψ (pt x y) = 0) (h3 : ∀ Ψ ∈ N, ∀ x y, ∀ u ∈ U, Ψ (pt x (y + u)) = Ψ (pt x y)) :
    FiniteDimensional ℂ N := by
  obtain ⟨s, -, hs⟩ := hC.elim_nhds_subcover (fun y => {y' | y' - y ∈ U}) fun y _ =>
    (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds (by simpa using hU)
  let ev : N →ₗ[ℂ] (s → P.map c) :=
    { toFun := fun Ψ y => ⟨fun x => Ψ.1 (pt x y), by
        obtain ⟨f, hf, e⟩ := h1 _ Ψ.2 y
        exact ⟨f, hf, funext fun x => (e x).symm⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective ev ((injective_iff_map_eq_zero ev).2 fun Ψ h => Subtype.ext (funext fun z => ?_))
  obtain ⟨x, y, rfl⟩ := hpt z
  by_cases hy : y ∈ C
  · obtain ⟨y₀, h₀, hy₀⟩ := Set.mem_iUnion₂.1 (hs hy)
    have := h3 _ Ψ.2 x y₀ _ hy₀
    rw [add_sub_cancel] at this
    rw [this]
    exact congrFun (congrArg Subtype.val (congrFun h ⟨y₀, h₀⟩)) x
  · exact h2 _ Ψ.2 x y hy

end PositivityTheory.ThKCT.So

end
end

