module

public import Development.WeilBound.ThetaLifts.TowerModels.Bundle0002
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.PlaneRemovalConfiguration
public import Development.WeilBound.ThetaLifts.ConeHypotheses.PolDense
public import Development.WeilBound.ThetaLifts.TowerModels.LeviAd
public import Development.WeilBound.ThetaLifts.TowerModels.Bundle0001
public import Development.WeilBound.ThetaLifts.TowerModels.Bundle0003
public import Development.WeilBound.ThetaLifts.TowerModels.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0054

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.LeviEx
section
noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace Levi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H : Plane E d d₁} {i₀ i₁ r s : ℕ}

theorem exists_loc (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) (hH : H.IsAdapted σ B W W₁ i₀ i₁) (w : InfinitePlace F)
    {g g' : Matrix (Fin d) (Fin d) ℂ} (h1 : g * g' = 1)
    (h2 : gᵀ * W.J.map (B.emb w).1 * g.map star = W.J.map (B.emb w).1) :
    ∃ (p p' : Matrix (Fin d) (Fin d) ℂ) (t : ℂ), t ≠ 0 ∧ p * p' = 1 ∧
      pᵀ * W.J.map (B.emb w).1 * p.map star = W.J.map (B.emb w).1 ∧
      (p *ᵥ fun i => (B.emb w).1 (H.x i)) = t • (fun i => (B.emb w).1 (H.x i)) ∧ Commute (p' * g) (W.θ w) := by
  set τ := (B.emb w).1 with hτ
  set M := Complex.I • W.J.map τ with hM
  have hiso : ∀ k : Matrix (Fin d) (Fin d) ℂ, kᵀ * M * k.map star = M ↔ kᵀ * W.J.map τ * k.map star = W.J.map τ := fun k => by
    rw [hM, Matrix.mul_smul, Matrix.smul_mul]
    exact (smul_right_injective _ Complex.I_ne_zero).eq_iff
  have hherm : ∀ i j, star (M j i) = M i j := fun i j => by
    have := hB.cm.2.2.2 τ (W.J j i)
    rw [hW.skew, map_neg] at this
    simp only [hM, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul', ← this]
    simp
  obtain ⟨c1, c2, c3⟩ := hW.cartan w
  set v : Fin d → ℂ := fun i => τ (H.x i) with hv
  have hv0 : v ≠ 0 := fun h => by
    have : H.x = 0 := funext fun i => τ.injective ((congrFun h i).trans (map_zero τ).symm)
    have e := hH.xy
    rw [this, form, zero_dotProduct] at e
    exact zero_ne_one e
  have hvv : hf M v v = 0 := by
    have e := congrArg τ hH.xx
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hB.cm.2.2.2, map_zero] at e
    rw [hf_apply, hM, Matrix.smul_mulVec, dotProduct_smul]
    exact smul_eq_zero_of_right _ e
  have hgv : g *ᵥ (g' *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  obtain ⟨κ, t, ht, k1, k2, k3⟩ := exists_move hherm c1 c2 c3 hv0 (v' := g' *ᵥ v)
    (fun h => hv0 (by rw [← hgv, h, Matrix.mulVec_zero]))
    hvv (by rw [← (hiso g).2 h2, ← hf_mulVec, hgv, hvv])
  have hκ : IsUnit κ.det := by
    have e := congrArg Matrix.det ((hiso κ).1 k1)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at e
    refine IsUnit.mk0 _ fun h => det_ne_zero hW (τ.injective ?_)
    rw [h, zero_mul, zero_mul] at e
    rw [RingHom.map_det, map_zero]
    exact e.symm
  have h1' := mul_eq_one_comm.1 h1
  refine ⟨g * κ, κ⁻¹ * g', t, ht, ?_, (hiso _).1 (iso_of_hf fun x y => ?_), ?_, ?_⟩
  · rw [mul_assoc, ← mul_assoc κ, Matrix.mul_nonsing_inv _ hκ, one_mul, h1]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hf_mulVec, (hiso g).2 h2, hf_mulVec, k1]
  · rw [← Matrix.mulVec_mulVec, k3, Matrix.mulVec_smul, hgv]
  · rw [mul_assoc, h1', mul_one]
    obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det κ).2 hκ
    rw [← Matrix.coe_units_inv]
    exact k2.units_inv_left

theorem exists_stab (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) (hH : H.IsAdapted σ B W W₁ i₀ i₁) (x : UA σ W.J) :
    ∃ (p : UA σ W.J) (t : (AE F E)ˣ), mat p *ᵥ incV F H.x = t.1 • incV F H.x ∧ p⁻¹ * x ∈ PositivityTheory.ThKEnd.FinK σ B W := by
  have hσ := hB.cm
  have one : ∀ {S : Type} [CommRing S] (f : AE F E →+* S), (1 : Matrix (Fin d) (Fin d) (AE F E)).map f = 1 := fun f =>
    Matrix.map_one _ (map_zero _) (map_one _)
  choose p p' t ht h1 h2 h3 h4 using fun w => exists_loc hB hW hH w (g := (mat x).map (piInf (B.emb w)))
    (g' := (mat x⁻¹).map (piInf (B.emb w)))
    (by rw [← Matrix.map_mul, show mat x * mat x⁻¹ = 1 from x.1.mul_inv, one])
    (by
      rw [← iso_map_piInf (fun τ z => piInf_cA hσ τ z), show (mat x)ᵀ * incM F W.J * (mat x).map (cA σ) = incM F W.J from x.2]
      exact Matrix.ext fun i j => piInf_incl _ _)
  obtain ⟨q, q1, q2⟩ := exists_lift hσ B.emb W.J p p' h1 h2
  obtain ⟨a, a1, a2⟩ := exists_inf hσ B.emb t
  obtain ⟨b, b1, b2⟩ := exists_inf hσ B.emb fun w => (t w)⁻¹
  have hab : a * b = 1 := ad_ext hσ B.emb (fun w => by rw [map_mul, a1, b1, mul_inv_cancel₀ (ht w), map_one])
    fun v => by rw [map_mul, a2, b2, mul_one, map_one]
  refine ⟨q, ⟨a, b, hab, (mul_comm _ _).trans hab⟩, funext fun i => ad_ext hσ B.emb (fun w => ?_) fun v => ?_, fun w => ?_⟩
  · have e : piInf (B.emb w) ∘ incV F H.x = fun i => (B.emb w).1 (H.x i) := funext fun i => piInf_incl _ _
    rw [RingHom.map_mulVec, q1, e, h3, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, a1]
    exact congrArg _ (congrFun e i).symm
  · rw [RingHom.map_mulVec, q2, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, a2, one_mul]
    rfl
  · have e : (mat q⁻¹).map (piInf (B.emb w)) = p' w := by
      have e1 : (mat q⁻¹).map (piInf (B.emb w)) * p w = 1 := by
        rw [← q1, ← Matrix.map_mul, show mat q⁻¹ * mat q = 1 from q.1.inv_mul, one]
      exact left_inv_eq_right_inv e1 (h1 w)
    rw [show mat (q⁻¹ * x) = mat q⁻¹ * mat x from rfl, Matrix.map_mul, e]
    exact h4 w

end Levi

open Levi

theorem leviEx : PositivityTheory.ThKG.LeviEx := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB hW hH h₁ => exists_levi hB hW hH 1 h₁

theorem iwa : PositivityTheory.ThKEnd.Iwa := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H i₀ i₁ r s hB hW hH
  have hd : IsUnit W₁.J.det := (isFr hB hW hH).isUnit_det (det_ne_zero hW).isUnit
  refine ⟨⟨hH.rank, hH.xx, hH.yy, hH.xy, hH.orth, hH.gram, hd.ne_zero⟩, fun x => ?_⟩
  obtain ⟨p, t, hp, hk⟩ := exists_stab hB hW hH x
  obtain ⟨g, α, hg, hα⟩ := (isFrA hB hW hH).stab t.mul_inv p.2 hp
  have hgu : IsUnit g.det := by
    have e := congrArg Matrix.det hg
    have hd' : IsUnit (incM F W₁.J).det := by
      have := hd.map (inclR (F := F) (AF F))
      rwa [RingHom.map_det] at this
    rw [← e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd'
    exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hd')
  obtain ⟨h₁, rfl⟩ := exists_UA (σ := σ) (Matrix.mul_nonsing_inv _ hgu) hg
  obtain ⟨m, hm⟩ := exists_levi hB hW hH t 1
  obtain ⟨l, hl⟩ := exists_levi hB hW hH 1 h₁
  refine ⟨p * (m * l)⁻¹, Subgroup.subset_closure ?_, t, m, h₁, l, _, hk, hm, hl, by group⟩
  obtain ⟨u, hu⟩ : ∃ u, u = p * (m * l)⁻¹ := ⟨_, rfl⟩
  have e : mat u * (mat m * mat l) = mat p := by
    rw [hu]; exact congrArg mat (inv_mul_cancel_right p (m * l))
  rw [← hu]
  constructor
  · have e1 : t.1 • (mat u *ᵥ incV F H.x) = t.1 • incV F H.x := by
      rw [← hp, ← e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hl.1, Units.val_one, one_smul, hm.1, Matrix.mulVec_smul]
    exact (t.isUnit.smul_left_cancel).1 e1
  · intro z
    obtain ⟨y, rfl⟩ : ∃ y, z = mat h₁ *ᵥ y :=
      ⟨mat h₁⁻¹ *ᵥ z, by rw [Matrix.mulVec_mulVec, show mat h₁ * mat h₁⁻¹ = 1 from h₁.1.mul_inv, Matrix.one_mulVec]⟩
    refine ⟨α ⬝ᵥ y, ?_⟩
    have e2 : mat u * (incM F H.ι * mat h₁) = mat p * incM F H.ι := by
      rw [← e, Matrix.mul_assoc, Matrix.mul_assoc, hl.2.2, ← Matrix.mul_assoc (mat m), hm.2.2,
        show mat (1 : UA σ W₁.J) = 1 from rfl, Matrix.mul_one]
    rw [← hα, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, e2]
    rfl

end PositivityTheory.ThKG.Tow

end
end

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.PlaneIso
section
noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_skew (h : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  let τ : E →ₐ[F] AlgebraicClosure E := IsScalarTower.toAlgHom F E _
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra H
    push Not at H
    exact comp_conj_ne h τ (AlgHom.ext fun a => congrArg τ (H a))
  exact ⟨a - σ a, sub_ne_zero.2 ha.symm, by rw [map_sub, sigma_sigma h, neg_sub]⟩

theorem denseRange_emb (h : IsCMExt F E σ) (e : E →+* ℂ) : DenseRange e := by
  obtain ⟨δ, hδ0, hδ⟩ := exists_skew h
  have h1 : star (e δ) = -e δ := by rw [← h.2.2.2 e, hδ, map_neg]
  have hre : (e δ).re = 0 := by
    have := congrArg Complex.re h1
    simp at this
    linarith
  have him : (e δ).im ≠ 0 := fun h0 => (map_ne_zero e).2 hδ0 (Complex.ext hre h0)
  let f : ℝ × ℝ → ℂ := fun p => p.1 + p.2 * e δ
  have hf : Function.Surjective f := fun z => ⟨(z.re, z.im / (e δ).im), Complex.ext (by simp [f, hre]) (by
    simp only [f, Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul]
    field_simp
    simp)⟩
  have hd : DenseRange (f ∘ Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)) :=
    hf.denseRange.comp (Rat.denseRange_cast.prodMap Rat.denseRange_cast) (by fun_prop)
  refine hd.mono ?_
  rintro _ ⟨⟨a, b⟩, rfl⟩
  exact ⟨a + b * δ, by simp [f]⟩

theorem exists_pos_neg (h : IsCMExt F E σ) (e : E →+* ℂ) {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : HasSig M r s)
    (hr : 1 ≤ r) (hs : 1 ≤ s) :
    (∃ x : Fin n → E, 0 < ((fun i => e (x i)) ⬝ᵥ M *ᵥ star fun i => e (x i)).re) ∧
      ∃ x : Fin n → E, ((fun i => e (x i)) ⬝ᵥ M *ᵥ star fun i => e (x i)).re < 0 := by
  obtain ⟨-, A, hA⟩ := hM
  have hd : DenseRange fun (x : Fin n → E) i => e (x i) := DenseRange.piMap fun _ => denseRange_emb h e
  have hc : Continuous fun Z : Fin n → ℂ => (Z ⬝ᵥ M *ᵥ star Z).re := by fun_prop
  have ent : ∀ a, (A *ᵥ Pi.single a 1) ⬝ᵥ M *ᵥ star (A *ᵥ Pi.single a 1) =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) a a := fun a => by
    rw [gram_vec, hA, ← Pi.single_star]; simp
  constructor
  · exact hd.exists_mem_open (isOpen_lt continuous_const hc)
      ⟨A *ᵥ Pi.single (Sum.inl ⟨0, hr⟩) 1, by simp only [Set.mem_setOf_eq, ent]; simp⟩
  · exact hd.exists_mem_open (isOpen_lt hc continuous_const)
      ⟨A *ᵥ Pi.single (Sum.inr ⟨0, hs⟩) 1, by simp only [Set.mem_setOf_eq, ent]; simp⟩

theorem exists_isotropic (h : IsCMExt F E σ) (emb : ∀ w : InfinitePlace F, EmbOver E w) {n r s : ℕ} (hn : 3 ≤ n)
    (hr : 1 ≤ r) (hs : 1 ≤ s) {J : Matrix (Fin n) (Fin n) E} (hdet : J.det ≠ 0) {ε : E} (hε : ε = 1 ∨ ε = -1)
    (hJ : ∀ i j, σ (J j i) = ε * J i j) {κ : ℂ} (hκ0 : κ ≠ 0) (hκ : ∀ e : E →+* ℂ, star κ * e ε = κ)
    (hsig : ∀ w, HasSig (κ • J.map (emb w).1) r s) : ∃ x : Fin n → E, x ≠ 0 ∧ form σ J x x = 0 := by
  haveI := h.1
  haveI := h.2.1
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  haveI : IsCMField E := IsCMField.ofCMExtension F E
  obtain ⟨δ₀, hδ₀0, hδ₀⟩ := exists_skew h
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : E, δ ≠ 0 ∧ σ δ * ε = δ := by
    rcases hε with rfl | rfl
    · exact ⟨1, one_ne_zero, by simp⟩
    · exact ⟨δ₀, hδ₀0, by simp [hδ₀]⟩
  have hf : ∀ x y, GlobalTheory.UTrans.hf (σ : E →+* E) (δ • J) x y = δ * form σ J x y := fun x y => by
    simp only [GlobalTheory.UTrans.hf, form, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul,
      RingHom.coe_coe]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  obtain ⟨z, hz0, hz⟩ := GlobalTheory.UTrans.exists_isotropic_of_indefinite E n (σ : E →+* E) (δ • J) (fun a => by
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      apply τ.injective
      rw [IsCMField.complexEmbedding_complexConj]
      exact h.2.2.2 τ a)
    { invol := sigma_sigma h
      ne_id := ⟨δ₀, fun e => hδ₀0 (by
        have : σ δ₀ = δ₀ := e
        linear_combination (hδ₀ - this) / 2)⟩
      herm := fun a b => by
        change σ (δ * J a b) = δ * J b a
        rw [map_mul, hJ, ← mul_assoc, hδ]
      det_ne := by rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ hδ0) hdet } hn (fun τ => by
      let w : InfinitePlace F := InfinitePlace.mk (τ.comp (algebraMap F E))
      have hw : w.embedding = τ.comp (algebraMap F E) :=
        InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal _)
      set e := (emb w).1 with he
      have k1 : ∀ a : E, σ a = a → τ a = e a := fun a ha => by
        have : a = algebraMap F E (Algebra.trace F E a / 2) := by
          rw [map_div₀, trace_cm h, ha, map_ofNat]; ring
        rw [this]
        exact (RingHom.congr_fun hw _).symm.trans (RingHom.congr_fun (emb w).2 _).symm
      have hε0 : e ε ≠ 0 := by rcases hε with rfl | rfl <;> simp
      have hsκ : star κ ≠ 0 := star_ne_zero.2 hκ0
      have ht : star (e δ / κ) = e δ / κ := by
        rw [star_div₀, ← h.2.2.2 e, div_eq_div_iff hsκ hκ0]
        have a1 := congrArg e hδ
        rw [map_mul] at a1
        linear_combination star κ * a1 - e (σ δ) * hκ e
      obtain ⟨t, ht'⟩ : ∃ t : ℝ, (t : ℂ) = e δ / κ := ⟨_, Complex.conj_eq_iff_re.1 ht⟩
      have ht0 : t ≠ 0 := by
        rintro rfl
        exact div_ne_zero ((map_ne_zero e).2 hδ0) hκ0 (by simpa using ht'.symm)
      have k2 : ∀ x, (τ (GlobalTheory.UTrans.hf (σ : E →+* E) (δ • J) x x)).re =
          t * ((fun i => e (x i)) ⬝ᵥ (κ • J.map e) *ᵥ star fun i => e (x i)).re := fun x => by
        rw [hf, k1 _ (by rw [map_mul, form_swap h hJ, ← mul_assoc, hδ]), map_mul, map_form h, Matrix.smul_mulVec,
          dotProduct_smul, smul_eq_mul, ← Complex.re_ofReal_mul, ht', ← mul_assoc, div_mul_cancel₀ _ hκ0]
      simp only [k2]
      obtain ⟨⟨x, hx⟩, y, hy⟩ := exists_pos_neg h e (hsig w) hr hs
      rcases lt_or_gt_of_ne ht0 with ht | ht
      · exact ⟨⟨y, mul_pos_of_neg_of_neg ht hy⟩, x, mul_neg_of_neg_of_pos ht hx⟩
      · exact ⟨⟨x, mul_pos ht hx⟩, y, mul_neg_of_pos_of_neg ht hy⟩)
  rw [hf] at hz
  exact ⟨z, hz0, (mul_eq_zero.1 hz).resolve_left hδ0⟩

end PositivityTheory.ThKG.Tow.Pln

end
end

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.PlanePair
section
noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_adapted_pair (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hdet : J.det ≠ 0) {ε : E}
    (hε : ε = 1 ∨ ε = -1) (hJ : ∀ i j, σ (J j i) = ε * J i j) (D : Submodule (𝓞 E) E) (hD1 : (1 : E) ∈ D)
    (L : Submodule (𝓞 E) (Fin n → E)) (hlat : L.IsFullLattice E) (hd : ∀ y, y ∈ L ↔ ∀ x ∈ L, form σ J y x ∈ D)
    (θ : 𝓞 E) (hθ : (θ : E) + σ θ = 1) (P : Finset (Pl F)) (τ : ∀ v : P, E →ₐ[F] Fv F v)
    (hDτ : ∀ v, ∀ c ∈ D, Valued.v (τ v c) ≤ 1) (x₀ : Fin n → E) (hx₀ : x₀ ≠ 0) (hxx₀ : form σ J x₀ x₀ = 0) :
    ∃ x y : Fin n → E, form σ J x x = 0 ∧ form σ J y y = 0 ∧ form σ J x y = 1 ∧
      (∀ z ∈ L, form σ J z x • y ∈ L ∧ form σ J z y • x ∈ L) ∧
      ∀ v : P, ((∀ c : E, c • x ∈ L → Valued.v (τ v c) ≤ 1) ∧ ∃ c : E, c • x ∈ L ∧ Valued.v (τ v c) = 1) ∧
        ((∀ c : E, c • y ∈ L → Valued.v (τ v c) ≤ 1) ∧ ∃ c : E, c • y ∈ L ∧ Valued.v (τ v c) = 1) := by
  classical
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have hεv : ∀ v, Valued.v (τ v ε) = 1 := fun v => by rcases hε with rfl | rfl <;> simp
  have hεD : ∀ a ∈ D, ε * a ∈ D := fun a ha => by
    rcases hε with rfl | rfl
    · simpa using ha
    · simpa using ha
  have sw : ∀ a b, form σ J b a = ε * σ (form σ J a b) := fun a b => by
    rw [form_swap h hJ, ← mul_assoc, hεε, one_mul]
  have hne : ∃ z ∈ L, formL (σ := σ) J x₀ z ≠ 0 := by
    by_contra H
    push Not at H
    have h0 : formL (σ := σ) J x₀ = 0 := LinearMap.ext_on hlat.span_eq_top fun z hz => H z hz
    have h1 : J *ᵥ (fun i => σ (x₀ i)) = 0 := by
      funext k
      have := LinearMap.congr_fun h0 (Pi.single k 1)
      simpa [formL, form] using this
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hdet h1
    exact hx₀ (funext fun i => by simpa using congrFun h2 i)
  let S : Finset (HeightOneSpectrum (𝓞 E)) :=
    Finset.univ.image (fun v : P => splitPrime (τ v)) ∪ Finset.univ.image (fun v : P => splitPrime ((τ v).comp σ))
  obtain ⟨z₀, hz₀, hc0, hmax⟩ := exists_max_val L hlat.fg (formL (σ := σ) J x₀) hne S
  change form σ J z₀ x₀ ≠ 0 at hc0
  set c₀ := form σ J z₀ x₀ with hc₀
  obtain ⟨x, hxx, hz₀x, hle⟩ : ∃ x, form σ J x x = 0 ∧ form σ J z₀ x = 1 ∧
      ∀ w ∈ S, ∀ z ∈ L, w.valuation E (form σ J z x) ≤ 1 := by
    refine ⟨σ c₀⁻¹ • x₀, by rw [form_smul_left, form_smul_right, hxx₀]; simp,
      by rw [form_smul_right, sigma_sigma h, inv_mul_cancel₀ hc0], fun w hw z hz => ?_⟩
    rw [form_smul_right, sigma_sigma h, map_mul, map_inv₀]
    exact inv_mul_le_one_of_le₀ (hmax w hw z hz) zero_le
  obtain ⟨y, hyy, hxy, hL⟩ := exists_partner h hε hJ D L hlat.fg hd θ hθ x hxx z₀ hz₀ (by rw [hz₀x]; exact one_ne_zero)
  have hyx : form σ J y x = ε := by rw [sw, hxy, map_one, mul_one]
  refine ⟨x, y, hxx, hyy, hxy, hL, fun v => ⟨⟨fun c hc => ?_, ?_⟩, fun c hc => ?_, 1, ?_, by simp⟩⟩
  · have := hεD _ ((hd _).1 hc z₀ hz₀)
    rw [form_smul_left, sw z₀ x, hz₀x, map_one, mul_one, mul_left_comm, hεε, mul_one] at this
    exact hDτ v c this
  · obtain ⟨d, hdw, hdC⟩ := exists_denom (L.map ((formL (σ := σ) J x).restrictScalars (𝓞 E))) (hlat.fg.map _)
      (splitPrime ((τ v).comp σ)) (by
        rintro _ ⟨z, hz, rfl⟩
        exact hle _ (by simp [S]) z hz)
    refine ⟨σ d, (hd _).2 fun z hz => ?_, ?_⟩
    · obtain ⟨o, ho⟩ := hdC _ ⟨z, hz, rfl⟩
      change (d : E) * form σ J z x = o at ho
      rw [form_smul_left, sw z x, mul_left_comm, ← map_mul, ho]
      refine hεD _ ?_
      have := D.smul_mem (conjInt σ o) hD1
      rwa [← algebraMap_smul E, smul_eq_mul, mul_one] at this
    · change Valued.v (((τ v).comp σ) d) = 1
      rw [valued_apply_eq_valuation]
      exact ((splitPrime ((τ v).comp σ)).valuation_eq_one_iff_notMem (K := E)).2 hdw
  · have := hle (splitPrime (τ v)) (by simp [S]) _ hc
    rwa [form_smul_left, hyx, ← valued_apply_eq_valuation, map_mul, map_mul, hεv, mul_one] at this
  · have := (hL z₀ hz₀).1
    rwa [hz₀x] at this

end PositivityTheory.ThKG.Tow.Pln

end
end

