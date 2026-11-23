module

public import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle0005
public import Development.WeilBound.ThetaLifts.TowerModels.Bundle0006
public import Development.WeilBound.ThetaLifts.SmallCones.UnfMain
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle0003
public import Development.WeilBound.ThetaLifts.SmallCones.IdeleTop

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.ConeLaw
section
set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Core

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

theorem levi_one (H : Plane E d d₁) : IsLevi (σ := σ) (W := W) (W₁ := W₁) H 1 1 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mat_one']

theorem absE_ne (l : (AE F E)ˣ) : (absE F E l : ℝ) ≠ 0 := by
  have : absE F E l * absE F E l⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact_mod_cast left_ne_zero_of_mul_eq_one this

theorem absE_pos (l : (AE F E)ˣ) : 0 < (absE F E l : ℝ) := lt_of_le_of_ne (NNReal.coe_nonneg _) (absE_ne l).symm

structure LawsT (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (om₀ : Rep σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁)
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (u : (AE F E)ˣ → Ten F E n d) (w : (AE F E)ˣ → ℂ) (ι : (AE F E)ˣ → (AE F E)ˣ) : Prop where
  one : ι 1 = 1
  w1 : w 1 = 1
  uni : ∀ m ∈ unip σ X H, ∀ Ψ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ (u 1) (om (m, 1) Ψ)) = e (M.co.rho B.ψ (u 1) Ψ)
  tor : ∀ l g₁ p h₁ p', IsLevi H (ι l) g₁ p → IsLevi H' 1 h₁ p' → ∀ Ψ ∈ schA F (Fin n × Fin d),
    (((absE F E (ι l) : ℝ) ^ (1 - (n : ℝ)) : ℝ) : ℂ) • e (M.co.rho B.ψ (u 1) (om (p, p') Ψ)) =
      w l • om₀ (g₁, h₁) (e (M.co.rho B.ψ (u l) Ψ))

structure Laws (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (om₀ : Rep σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁)
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (u : (AE F E)ˣ → Ten F E n d) (ν χ : Chr F E) (z : ℕ) (ι : (AE F E)ˣ → (AE F E)ˣ) : Prop
    extends LawsT B M om om₀ H H' e u (fun l => (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) ι where
  torW : ∀ t h₁ p', IsLevi H' t h₁ p' → ∃ s : (AE F E)ˣ, ∀ l, ∀ Ψ ∈ schA F (Fin n × Fin d),
    e (M.co.rho B.ψ (u l) (om (1, p') Ψ)) = ((χ t : ℂ) * (((absE F E t : ℝ) ^ (((d : ℝ) - n) / 2) : ℝ) : ℂ) *
      ((ν s : ℂ) * ((absE F E s : ℝ) : ℂ) ^ z)) • om₀ (1, h₁) (e (M.co.rho B.ψ (u (l * s)) Ψ))

variable {B : Base F E} {M : Model σ X W} {om : Rep σ X W} {M₀ : Model σ X₁ W₁} {om₀ : Rep σ X₁ W₁} {H : Plane E n n₁}
  {H' : Plane E d d₁} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {μ : Measure (AE F E)ˣ} {u : (AE F E)ˣ → Ten F E n d} {ν χ : Chr F E} {z : ℕ}
  {ι : (AE F E)ˣ → (AE F E)ˣ} {w : (AE F E)ˣ → ℂ} {χX χW : Chr F E} {r s r' s' r₀ s₀ r₀' s₀' : ℕ}

theorem LawsT.theta (h : LawsT B M om om₀ H H' e u w ι) {l g₁ p h₁ p'} (h1 : IsLevi H (ι l) g₁ p) (h2 : IsLevi H' 1 h₁ p') {Ψ}
    (hΨ : Ψ ∈ schA F (Fin n × Fin d)) :
    thetaSum F (e (M.co.rho B.ψ (u 1) (om (p, p') Ψ))) * (((absE F E (ι l) : ℝ) ^ (1 - (n : ℝ)) : ℝ) : ℂ) =
      theta om₀ (e (M.co.rho B.ψ (u l) Ψ)) g₁ h₁ * w l := by
  have := congrArg (thetaSum F) (h.tor l g₁ p h₁ p' h1 h2 Ψ hΨ)
  rw [thetaSum_smul', thetaSum_smul'] at this
  rw [mul_comm, this, mul_comm]
  rfl

theorem LawsT.rat (h : LawsT B M om om₀ H H' e u w ι) (hD : StabDec) (hTB : ThetaBasic) (hp : IsPair B M χX χW om r s r' s')
    (hp₀ : IsPair B M₀ χX χW om₀ r₀ s₀ r₀' s₀') {j₀ j₁} (hH : H.IsAdapted σ B X X₁ j₀ j₁)
    (hs : ∀ Ψ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ (u 1) Ψ) ∈ schA F (Fin n₁ × Fin d₁)) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d))
    (y) {δ} (hδ : δ ∈ ratU σ X.J) (hx : mat δ *ᵥ incV F H.x = incV F H.x) (g) :
    thv B M om e (u 1) Φ y (δ * g) = thv B M om e (u 1) Φ y g := by
  obtain ⟨m, hm, g₁, p, hp1, rfl, hr⟩ := (hD F E σ B n n₁ X X₁ H j₀ j₁ r s hp.base (Or.inl hp.herm) hH).1 δ 1 (by simpa using hx)
  have hΨ := pair_pres hp (g, y) hΦ
  have e1 : om (m * p * g, y) Φ = om (m, 1) (om (p, 1) (om (g, y) Φ)) := by simp [om_mul, mul_assoc]
  have e2 := h.theta (l := 1) (by rwa [h.one]) (levi_one (W₁ := W₁) H') hΨ
  have e3 := ((hTB F E σ B _ _ X₁ W₁ M₀ χX χW om₀ _ _ _ _ hp₀).1 _ (hs _ hΨ)).2.1 g₁ (hr hδ) 1 (one_mem _) 1 1
  simp only [h.one, h.w1, map_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, mul_one, Circle.coe_one, one_pow] at e2 e3
  unfold thv
  rw [e1, h.uni m hm _ (pair_pres hp _ hΨ), e2, e3]
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta, ← Prod.one_eq_mk]

theorem Laws.coneI_law [μ.IsMulRightInvariant] [MeasurableMul (AE F E)ˣ] (h : Laws B M om om₀ H H' e u ν χ z ι)
    (hp : IsPair B M χX χW om r s r' s') {K : Subgroup (UA σ X.J)} (μK : Measure K) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d))
    {t h₁ p} (hl : IsLevi H' t h₁ p) (y) :
    coneI B M om M₀ om₀ e K μK μ u ν z (om (1, p * y) Φ) 1 =
      (χ t : ℂ) * (((absE F E t : ℝ) ^ (((d : ℝ) - n) / 2) : ℝ) : ℂ) * coneI B M om M₀ om₀ e K μK μ u ν z (om (1, y) Φ) h₁ := by
  obtain ⟨s, hs⟩ := h.torW t h₁ p hl
  unfold coneI
  rw [← integral_const_mul]
  congr 1
  funext k
  rw [← integral_mul_right_eq_self (fun l => M₀.I om₀ (e (M.co.rho B.ψ (u l) (om (k.1, 1) (om (1, y) Φ)))) h₁ * (ν l : ℂ) *
    ((absE F E l : ℝ) : ℂ) ^ z) s, ← integral_const_mul]
  congr 1
  funext l
  have e1 : om (k.1, 1) (om (1, p * y) Φ) = om (1, p) (om (k.1, 1) (om (1, y) Φ)) := by simp [om_mul]
  rw [e1, hs l _ (pair_pres hp _ (pair_pres hp _ hΦ))]
  simp only [Model.I, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta, map_smul, thetaSum_smul', om_mul, Prod.mk_mul_mk, mul_one, one_mul, integral_const_mul,
    map_mul, Circle.coe_mul, NNReal.coe_mul, Complex.ofReal_mul, mul_pow]
  ring

end Core

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.SplitLatMap
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Fr PositivityTheory.ThKG.Tow.Pln

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cartan_low {n n₁ : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} {θ₁ : Matrix (Fin n₁) (Fin n₁) ℂ}
    {ι : Matrix (Fin n) (Fin n₁) ℂ} {P : Matrix (Fin n₁) (Fin n) ℂ} (hP : P * ι = 1) (h : IsCartan M θ) (e : θ * ι = ι * θ₁) :
    IsCartan (ιᵀ * M * ι.map star) θ₁ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · rw [← Matrix.one_mul (θ₁ * θ₁), ← hP, Matrix.mul_assoc, ← Matrix.mul_assoc ι, ← e, Matrix.mul_assoc θ, ← e,
      ← Matrix.mul_assoc θ, h1, Matrix.one_mul]
  · have m : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) (C : Matrix (Fin b) (Fin c) ℂ),
        (A * C).map star = A.map star * C.map star := fun A C => Matrix.map_mul (f := starRingEnd ℂ)
    calc _ = (ι * θ₁)ᵀ * M * (ι * θ₁).map star := by simp only [Matrix.transpose_mul, m, Matrix.mul_assoc]
      _ = ιᵀ * (θᵀ * M * θ.map star) * ι.map star := by rw [← e]; simp only [Matrix.transpose_mul, m, Matrix.mul_assoc]
      _ = _ := by rw [h2]
  · rw [← gram_vec, Matrix.mulVec_mulVec, ← e, ← Matrix.mulVec_mulVec]
    refine h3 _ fun h0 => hx ?_
    rw [← Matrix.one_mulVec x, ← hP, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]

theorem splitLat_map {v : Pl F} (τ : E →ₐ[F] Fv F v) {n m : ℕ} {L : Submodule (𝓞 E) (Fin n → E)}
    {L' : Submodule (𝓞 E) (Fin m → E)} (A : Matrix (Fin m) (Fin n) E) (h : ∀ z ∈ L, A *ᵥ z ∈ L') {w : Fin n → Fv F v}
    (hw : w ∈ splitLat τ L) : A.map τ *ᵥ w ∈ splitLat τ L' :=
  splitLat_le τ ((splitLat τ L').comap ((A.map τ).mulVecLin.restrictScalars _)) (fun z hz => by
    have e : A.map τ *ᵥ (fun i => τ (z i)) = fun i => τ ((A *ᵥ z) i) :=
      funext fun i => (RingHom.map_mulVec (τ : E →+* Fv F v) A z i).symm
    show A.map τ *ᵥ (fun i => τ (z i)) ∈ splitLat τ L'
    rw [e]
    exact map_mem_splitLat τ (h z hz)) hw

theorem low_eps {B : Base F E} (hB : B.IsGood σ) {ε : E} {κ : ℂ} (hκ1 : κ * star κ = 1)
    (hκ : ∀ e : E →+* ℂ, star κ * e ε = κ) {D : Submodule (𝓞 E) E} {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    {H : Plane E n n₁} {i₀ i₁ r s : ℕ} (hY : IsEps σ B ε κ D Y r s) (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) {ε' : E}
    {A' : Matrix (Fin n₁ ⊕ Fin 2) (Fin n) E} (h : IsFr (σ : E →+* E) ε' Y.J Y₁.J H.ι H.x H.y A') :
    1 ≤ r ∧ 1 ≤ s ∧ IsEps σ B ε κ D Y₁ (r - 1) (s - 1) := by
  have hcm := hB.cm
  set P : Matrix (Fin n₁) (Fin n) E := A'.submatrix Sum.inl id with hPd
  have hP : ∀ (u : Fin n₁ → E) (a b : E), P *ᵥ (H.ι *ᵥ u + a • H.x + b • H.y) = u := fun u a b => funext fun j => by
    have : A' *ᵥ (H.ι *ᵥ u + a • H.x + b • H.y) = Sum.elim u ![a, b] := by
      rw [← fr_mulVec, Matrix.mulVec_mulVec, h.inv2, Matrix.one_mulVec]
    exact congrFun this (Sum.inl j)
  have hPι : P * H.ι = 1 := Matrix.ext fun i j => by
    exact (congrFun (congrFun h.inv2 (Sum.inl i)) (Sum.inl j)).trans (by simp [Matrix.one_apply])
  have hform : ∀ u u', form σ Y₁.J u u' = form σ Y.J (H.ι *ᵥ u) (H.ι *ᵥ u') := hH.gram ▸ form_gram Y.J H.ι
  have hL : Y₁.L = Y.L.comap ((Matrix.mulVecLin H.ι).restrictScalars (𝓞 E)) := Submodule.ext hH.low
  have cg : ∀ e : E →+* ℂ, (H.ι.map e)ᵀ * (κ • Y.J.map e) * (H.ι.map e).map star = κ • Y₁.J.map e := fun e => by
    rw [Matrix.mul_smul, Matrix.smul_mul, map_gram hcm, hH.gram]
  have hPe : ∀ {S : Type} [CommRing S] (e : E →+* S), P.map e * H.ι.map e = 1 := fun e => by
    rw [← Matrix.map_mul, hPι, Matrix.map_one _ (map_zero _) (map_one _)]
  have hXX : ∀ e : E →+* ℂ, (fun i => e (H.x i)) ⬝ᵥ (κ • Y.J.map e) *ᵥ star (fun i => e (H.x i)) = 0 := fun e => by
    rw [Matrix.smul_mulVec, dotProduct_smul, ← map_form hcm, hH.xx, map_zero, smul_zero]
  have hmin : min r s ≠ 0 := fun h0 => by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have h1 := aniso (hY.sig w) h0 (hXX _)
    have h2 : H.x = 0 := funext fun i => (B.emb w).1.injective ((congrFun h1 i).trans (map_zero _).symm)
    have e := hH.xy
    rw [h2, form, zero_dotProduct] at e
    exact zero_ne_one e
  have hlat : (Y.L.comap ((Matrix.mulVecLin H.ι).restrictScalars (𝓞 E))).IsLattice E :=
    Submodule.IsLattice.of_fg E (fg_comap _ (fun u u' e => by
      have := congrArg (P *ᵥ ·) (show H.ι *ᵥ u = H.ι *ᵥ u' from e)
      simpa [Matrix.mulVec_mulVec, hPι] using this) Y.L hY.lat.fg)
  have hfull : (Y.L.comap ((Matrix.mulVecLin H.ι).restrictScalars (𝓞 E))).IsFullLattice E := by
    let := hlat
    refine { span_eq_top := ?_ }
    apply top_unique
    intro u _
    have hz : H.ι *ᵥ u ∈ Submodule.span E (Y.L : Set (Fin n → E)) := by
      rw [Submodule.IsFullLattice.span_eq_top (self := hY.lat)]
      trivial
    have hmap : ∀ z ∈ Y.L, P *ᵥ z ∈
        Submodule.span E (Y.L.comap ((Matrix.mulVecLin H.ι).restrictScalars (𝓞 E)) : Set (Fin n₁ → E)) := by
      intro z hz
      obtain ⟨a, b, u', -, -, hu', rfl⟩ := hH.split z hz
      apply Submodule.subset_span
      change H.ι *ᵥ (P *ᵥ (a • H.x + H.ι *ᵥ u' + b • H.y)) ∈ Y.L
      rw [add_comm (a • H.x), hP]
      exact (hH.low u').1 hu'
    have hspan := (Submodule.span_le.mpr (show (Y.L : Set (Fin n → E)) ⊆
        (Submodule.span E (Y.L.comap ((Matrix.mulVecLin H.ι).restrictScalars (𝓞 E)) : Set (Fin n₁ → E))).comap (Matrix.mulVecLin P) from hmap)) hz
    simpa only [Submodule.mem_comap, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      hPι, Matrix.one_mulVec] using hspan
  refine ⟨by omega, by omega, fun i j => ?_, fun w => ?_, hL ▸ hfull, fun u => ?_,
    fun w => ?_, fun v u => ?_⟩
  · rw [← form_single (σ := σ) Y₁.J j i, ← form_single (σ := σ) Y₁.J i j, hform, hform, form_swap hcm hY.herm]
  · rw [← cg]
    refine (real_plane _ (fun i => (B.emb w).1 (H.x i)) (κ • fun i => (B.emb w).1 (H.y i)) _ (P.map (B.emb w).1) hH.rank
      (map_herm hcm _ (hκ _) hY.herm) (hXX _) ?_ ?_ ?_ ?_ (hPe _) (hY.sig w)).1
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, smul_dotProduct, dotProduct_smul, dotProduct_smul,
        ← map_form hcm, hH.yy, map_zero, smul_zero, smul_zero, smul_zero]
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, dotProduct_smul, dotProduct_smul,
        ← map_form hcm, hH.xy, map_one, smul_eq_mul, smul_eq_mul, mul_one, mul_comm, hκ1]
    · rw [Matrix.smul_mulVec, Matrix.mulVec_smul, map_orth hcm _ Y.J H.ι H.x (fun u => (hH.orth u).1), smul_zero]
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul,
        map_orth hcm _ Y.J H.ι H.y (fun u => (hH.orth u).2), smul_zero, smul_zero]
  · refine ⟨fun hu u' hu' => ?_, fun G => (hH.low u).2 ((hY.dual _).2 fun z hz => ?_)⟩
    · rw [hform]; exact (hY.dual _).1 ((hH.low u).1 hu) _ ((hH.low u').1 hu')
    · obtain ⟨_, _, u', -, -, hu', hz'⟩ := hH.split z hz
      rw [hz', form_add_right, form_add_right, form_smul_right, form_smul_right, (hH.orth u).1,
        (hH.orth u).2, mul_zero, mul_zero, zero_add, add_zero, ← hform]
      exact G u' hu'
  · rw [← cg]
    exact cartan_low (hPe _) (hY.cartan w) (hH.cartan w).1
  · have hn := hH.rank
    let f : Fin n₁ → Fin n := fun j => ⟨skip i₀ i₁ j, by have := j.2; unfold skip; split_ifs <;> omega⟩
    have hf : Function.Injective f := fun a b e => Fin.ext (by
      have := congrArg Fin.val e
      simp only [f, skip] at this
      split_ifs at this <;> omega)
    let T : Matrix (Fin n) (Fin n₁) (Fv F v.1) := (1 : Matrix (Fin n) (Fin n) _).submatrix id f
    have e1 : (Y.bas v).1 * T = H.ι.map (B.τ v) * (Y₁.bas v).1 := Matrix.ext fun a j => by
      rw [← (hH.bas v (f j)).2.2 j rfl a]
      simp [T, Matrix.mul_apply, Matrix.one_apply]
    have e2 : (∀ i, u i ∈ v.1.adicCompletionIntegers F) ↔ ∀ i, (T *ᵥ u) i ∈ v.1.adicCompletionIntegers F := by
      refine ⟨fun G i => sum_mem fun j _ => mul_mem ?_ (G j), fun G j => ?_⟩
      · simp only [T, Matrix.submatrix_apply, Matrix.one_apply]
        split_ifs
        exacts [one_mem _, zero_mem _]
      · simpa [T, Matrix.mulVec, dotProduct, Matrix.one_apply, hf.eq_iff] using G (f j)
    rw [e2, hY.bas v, Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec]
    refine ⟨fun G => ?_, splitLat_map _ _ fun z hz => (hH.low z).1 hz⟩
    have := splitLat_map (L' := Y₁.L) _ P (fun z hz => by
      obtain ⟨a, b, u', -, -, hu', rfl⟩ := hH.split z hz
      rwa [add_comm (a • H.x), hP]) G
    rwa [Matrix.mulVec_mulVec, show P.map (B.τ v) * H.ι.map (B.τ v) = 1 from hPe (B.τ v : E →+* Fv F v.1),
      Matrix.one_mulVec] at this

theorem low_of : Low := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H i₀ i₁ r s hB hH
  refine ⟨fun hY => ?_, fun hY => ?_⟩
  · obtain ⟨ε, A', h⟩ := isFr hB (Or.inl hY) hH
    simp only [isHerm_iff] at hY ⊢
    exact low_eps hB (by simp) (fun e => by simp) hY hH h
  · obtain ⟨ε, A', h⟩ := isFr hB (Or.inr hY) hH
    simp only [isSkew_iff] at hY ⊢
    exact low_eps hB (by simp) (fun e => by simp) hY hH h

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.Unfold
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Fr Unf
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def fixQ {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) : Subgroup (UA σ J) where
  carrier := {δ | δ ∈ ratU σ J ∧ mat δ *ᵥ incV F x = incV F x}
  one_mem' := ⟨Subgroup.one_mem _, Matrix.one_mulVec _⟩
  mul_mem' := fun ha hb => ⟨Subgroup.mul_mem _ ha.1 hb.1, by rw [mat_mul, ← Matrix.mulVec_mulVec, hb.2, ha.2]⟩
  inv_mem' := fun {a} ha => ⟨Subgroup.inv_mem _ ha.1, by conv_lhs => rw [← ha.2, mat_cancel]⟩

theorem exists_iso {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : UA σ J} (hg : g ∈ ratU σ J) {x : Fin n → E} (h0 : x ≠ 0)
    (hx : form σ J x x = 0) : ∃ z : Fin n → E, z ≠ 0 ∧ form σ J z z = 0 ∧ incV F z = mat g *ᵥ incV F x := by
  obtain ⟨M, hM⟩ := mem_ratU.1 hg
  have e : incV F (M *ᵥ x) = mat g *ᵥ incV F x := by
    rw [hM]
    exact funext fun i => RingHom.map_mulVec (inclR (F := F) (AF F)) M x i
  have hU : Mᵀ * J * M.map σ = J := by
    apply Matrix.map_injective (inclR_inj (F := F))
    have := g.2
    change (mat g)ᵀ * _ * (mat g).map _ = _ at this
    rw [hM] at this
    simp only [Matrix.map_mul]
    exact this
  refine ⟨M *ᵥ x, fun h => h0 (funext fun i => inclR_inj (F := F) ?_), ?_, e⟩
  · have := mat_cancel g (incV F x)
    rw [← e, h, show incV F (0 : Fin n → E) = 0 from funext fun _ => map_zero _, Matrix.mulVec_zero] at this
    exact (congrFun this i).symm.trans (map_zero _).symm
  · have e2 : (fun i => σ ((M *ᵥ x) i)) = M.map σ *ᵥ fun i => σ (x i) := funext fun i => RingHom.map_mulVec (σ : E →+* E) M x i
    rw [← hx, form, form, e2]
    conv_rhs => rw [← hU, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose]

theorem unfold_of : Unfold := by
  intro F E _ _ _ _ _ σ B n n₁ X X₁ H j₀ j₁ r s hB hX hH K μK μ ν D ν₁ D₁ lev hK _ _ _ hD _ hD₁ hlev
  have hY : X.IsHerm σ B r s ∨ X.IsSkew σ B r s := Or.inl hX
  obtain ⟨ε, A', hfr⟩ := isFr hB hY hH
  have hd : IsUnit X₁.J.det := hfr.isUnit_det (det_ne hY).isUnit
  have hJ : ∀ i j, σ (X.J j i) = (((1 : ℤˣ) : ℤ) : E) * X.J i j := fun i j => by simp [hX.herm]
  have hJ₁ : ∀ i j, σ (X₁.J j i) = (((1 : ℤˣ) : ℤ) : E) * X₁.J i j := fun i j => by
    have e : ∀ i j, X₁.J i j = form σ X.J (fun k => H.ι k i) (fun k => H.ι k j) := fun i j => by
      rw [← hH.gram, Matrix.mul_assoc]; rfl
    rw [e, e, form_eps (PositivityTheory.ThKG.Tow.Levi.sig_sig hB.cm) hJ]
  obtain ⟨_, _, _, _, _, -⟩ := PositivityTheory.ThKF.unimodLC hB.cm hJ (det_ne hY)
  obtain ⟨_, _, _, _, _, -⟩ := PositivityTheory.ThKF.unimodLC hB.cm hJ₁ hd.ne_zero
  obtain ⟨-, _, _, _, _, _, -⟩ := ideleTop F E
  haveI := PositivityTheory.ThKF.countable_ratU σ X.J
  haveI := PositivityTheory.ThKF.countable_ratU σ X₁.J
  haveI := PositivityTheory.ThKF.discrete_ratU hB.cm hJ (det_ne hY)
  obtain ⟨s1, s2, s3⟩ := stabDec_of F E σ B n n₁ X X₁ H j₀ j₁ r s hB hY hH
  obtain ⟨N, _, _, _, _, μN, _, _, nn, ι, mm, χ, hP, c1, c2, c3, -, C, hC, hcov⟩ := parEx hB hY hH
  have l1 : ∀ g, IsLevi H 1 g (ι g) := fun g => by simpa using c3 1 g
  have l2 : ∀ g ∈ ratU σ X₁.J, ι g ∈ ratU σ X.J := fun g hg => s2 1 g hg _ (by rw [map_one]; exact l1 g)
  have el : ∀ t g, lev (t, g) = ι g * mm t := fun t g => levi_uniq hfr (hlev t g) (c3 t g)
  have eχ : ∀ t, (absE F E t : ℝ) ^ (1 - (n : ℝ)) = χ t := fun t => by
    have h1 : (χ t : ℝ) * (absE F E t : ℝ) ^ (n₁ + 1) = 1 := by exact_mod_cast c1 t
    rw [eq_inv_of_mul_eq_one_left h1, ← Real.rpow_natCast, ← Real.rpow_neg (NNReal.coe_nonneg _), hH.rank]
    congr 1
    push_cast
    ring
  obtain ⟨κ, hκ, hmain⟩ := unfold_abs ν ν₁ μ hP hK.1 μK (Γ := ratU σ X.J) (Q := fixQ X.J H.x)
    (ΓN := ratU σ X.J ⊓ unip σ X H) (Γ₁ := ratU σ X₁.J) (fun g => by
      obtain ⟨p, k, l, hk, hp, rfl⟩ := hK.2 g
      obtain ⟨u, hu, g₁, m, hm, rfl, -⟩ := s1 p l hp
      obtain ⟨q, rfl⟩ := (c2 u).1 hu
      exact ⟨q, g₁, l, k, hk, by rw [levi_uniq hfr hm (c3 l g₁), ← mul_assoc (nn q)]⟩)
    (fun _ h => h.1) (fun δ h => ⟨h.1, (mem_unip.1 h.2).1⟩) (fun δ h => (c2 δ).1 h.2)
    (fun γ h => ⟨l2 γ h, (l1 γ).1.trans (one_smul _ _)⟩) (fun q hq => by
      obtain ⟨u, hu, g₁, m, hm, rfl, hr⟩ := s1 q 1 (hq.2.trans (one_smul _ _).symm)
      obtain rfl := levi_uniq hfr hm (l1 g₁)
      have key : ∀ z z' : ratU σ X₁.J × (ratU σ X.J ⊓ unip σ X H : Subgroup _), ι z.1 * z.2 = ι z'.1 * z'.2 → z = z' :=
        fun z z' e => by
          obtain ⟨p, hp⟩ := (c2 _).1 z.2.2.2
          obtain ⟨p', hp'⟩ := (c2 _).1 z'.2.2.2
          obtain ⟨L, -, hL⟩ := hP.h2 z.1
          obtain ⟨L', -, hL'⟩ := hP.h2 z'.1
          have e1 : z.1 = z'.1 := Subtype.ext (congrArg (fun w => w.2.1)
            (hP.emb.injective (a₁ := (L p, z.1.1, 1)) (a₂ := (L' p', z'.1.1, 1)) (by
              simp only [map_one, mul_one, ← hL, ← hL', ← hp, ← hp', e])))
          rw [e1] at e
          exact Prod.ext e1 (Subtype.ext (mul_left_cancel e))
      refine ⟨(⟨g₁, hr hq.1⟩, ⟨(ι g₁)⁻¹ * u * ι g₁, ?_, levi_conj hm hu⟩), by simp only; group, fun z hz => key _ _ ?_⟩
      · rw [mul_assoc]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (l2 _ (hr hq.1))) hq.1
      · rw [← hz]; simp only; group)
    hC (fun p => by
      obtain ⟨q, h1, h2⟩ := hcov p
      exact ⟨nn q, ⟨h1, (c2 _).2 ⟨q, rfl⟩⟩, h2⟩) hD₁ hD
  refine ⟨κ, hκ, fun γ hγ f hf i1 i2 hfin => ?_⟩
  simp only [el, eχ, ENNReal.ofReal_coe_nnreal] at hfin ⊢
  refine hmain _ γ (fun x => (hγ x).1) (fun g hg => ?_) f hf (fun p => i1 _ ((c2 _).2 ⟨p, rfl⟩)) (fun q hq => i2 q hq.1 hq.2) hfin
  have hx0 : H.x ≠ 0 := fun h => by
    have := hH.xy
    rw [h, form, zero_dotProduct] at this
    exact zero_ne_one this
  have k : ∀ x : IsoV σ X, g * (γ x)⁻¹ ∈ fixQ X.J H.x ↔ incV F x.1 = mat g⁻¹ *ᵥ incV F H.x := fun x => by
    have e : mat (g * (γ x)⁻¹) *ᵥ incV F H.x = mat g *ᵥ incV F x.1 := by
      rw [mat_mul, ← Matrix.mulVec_mulVec, ← (hγ x).2, mat_cancel]
    refine ⟨fun h => by rw [← h.2, e, mat_cancel], fun h => ⟨Subgroup.mul_mem _ hg (Subgroup.inv_mem _ (hγ x).1), ?_⟩⟩
    rw [e, h, mat_cancel']
  obtain ⟨z, z0, z1, z2⟩ := exists_iso (Subgroup.inv_mem _ hg) hx0 hH.xx
  exact ⟨⟨z, z0, z1⟩, (k _).2 z2, fun x hx => Subtype.ext (funext fun i => inclR_inj (F := F)
    (congrFun (((k x).1 hx).trans z2.symm) i))⟩

end PositivityTheory.ThKCT

end
end

