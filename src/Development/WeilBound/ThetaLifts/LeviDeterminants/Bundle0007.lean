module

public import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.AdaptC
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0018
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0002
public import Development.WeilBound.ThetaLifts.LeviDeterminants.NormIteratedFDerivIdLeOneAdd
public import Mathlib
public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle0006

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.ActsEx
section
noncomputable section

namespace PositivityTheory.ThKF0

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK
open PositivityTheory.ThKH.Locrep

theorem actsEx : GlobalTheory.ThK.ActsEx := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v
  obtain ⟨ω, ρ, L⟩ := locRepEx F E σ n d B X W M om ⟨hP.base, ⟨r, s, hP.herm⟩, ⟨r', s', hP.skew⟩, hP.good, χX, χW, hP.weil⟩ v
  refine ⟨fun g hg h hh φ hφ => ⟨ω (g, h) φ, ⟨L.pres g hg h hh φ hφ, (L.acts g hg h hh φ hφ _).2 rfl⟩,
      fun φ₁ h₁ => (L.acts g hg h hh φ hφ _).1 h₁.2⟩,
    fun u hu φ hφ => ⟨ρ u φ, ⟨L.presH u hu φ hφ, (L.actsH u hu φ hφ _).2 rfl⟩,
      fun φ₁ h₁ => (L.actsH u hu φ hφ _).1 h₁.2⟩, fun φ hφ => ?_⟩
  have hs := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
  let loc : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v) := fun p => res v x₀ ∘ₗ om p ∘ₗ tensL v r₀
  have hloc : ∀ p : UA σ X.J × UA σ W.J, p.1 ∈ UAt σ X (evFin F v) → p.2 ∈ UAt σ W (evFin F v) → ∀ φ ∈ SB _,
      loc p φ = ω p φ := fun p h1 h2 φ hφ =>
    (eq_of_acts v h₁ (h₀ φ hφ) ((L.acts p.1 h1 p.2 h2 φ hφ _).2 rfl)).symm
  obtain ⟨K, hK1, hK2, hK3, hK4⟩ := exists_small_subgroups σ X v
  obtain ⟨K', hK1', hK2', hK3', hK4'⟩ := exists_small_subgroups σ W v
  obtain ⟨m, hm⟩ := smooth_of_weak (SB _) (fun k => (K k).prod (K' k))
    (fun a b hab => Subgroup.prod_mono (hK1 hab) (hK1' hab))
    (fun U hU => by
      obtain ⟨U₁, h1, U₂, h2, h⟩ := mem_nhds_prod_iff.1 hU
      obtain ⟨a, ha⟩ := hK2 U₁ h1
      obtain ⟨b, hb⟩ := hK2' U₂ h2
      exact ⟨max a b, fun p hp => h ⟨ha (hK1 (le_max_left a b) hp.1), hb (hK1' (le_max_right a b) hp.2)⟩⟩)
    loc (fun p hp φ hφ => by
      rw [hloc p (hK3 0 hp.1) (hK3' 0 hp.2) φ hφ]
      exact L.pres p.1 (hK3 0 hp.1) p.2 (hK3' 0 hp.2) φ hφ)
    (fun φ hφ => by
      rw [hloc 1 (one_mem_UAt X v) (one_mem_UAt W v) φ hφ]
      exact L.one φ hφ)
    (fun p hp q hq φ hφ => by
      rw [hloc (p * q) (mul_mem_UAt (hK3 0 hp.1) (hK3 0 hq.1)) (mul_mem_UAt (hK3' 0 hp.2) (hK3' 0 hq.2)) φ hφ,
        hloc q (hK3 0 hq.1) (hK3' 0 hq.2) φ hφ,
        hloc p (hK3 0 hp.1) (hK3' 0 hp.2) _ (L.pres q.1 (hK3 0 hq.1) q.2 (hK3' 0 hq.2) φ hφ)]
      exact L.mul p.1 (hK3 0 hp.1) p.2 (hK3' 0 hp.2) q.1 (hK3 0 hq.1) q.2 (hK3' 0 hq.2) φ hφ)
    (fun l φ hφ => hs.cont _ (res_adm v x₀ l) _ (h₀ φ hφ).2) φ hφ
  obtain ⟨U, hU, hUK⟩ := hK4 m
  obtain ⟨U', hU', hUK'⟩ := hK4' m
  refine ⟨U ×ˢ U', prod_mem_nhds hU hU', fun x hx h1 h2 => ?_⟩
  refine (L.acts x.1 h1 x.2 h2 φ hφ φ).2 ?_
  rw [← hloc x h1 h2 φ hφ]
  exact (hm x ⟨hUK _ hx.1 h1, hUK' _ hx.2 h2⟩).symm

end PositivityTheory.ThKF0
end
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.CartanPos
section
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

open PositivityTheory.Mix.Adapt GlobalTheory.CompanionTheory.Ar.RT.Lie

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem tr_evI (h : IsTotallyReal F) (a : AF F) : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F a) =
    ∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (a.1 w)).re := by
  classical
  haveI : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 w.2 (h.isReal w.1)⟩
  rw [evI, Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  refine (congrArg₂ HAdd.hAdd ?_ (Finset.sum_of_isEmpty _)).trans (add_zero _)
  refine Fintype.sum_equiv (Equiv.subtypeUnivEquiv h.isReal) _ _ fun w => ?_
  rw [Equiv.subtypeUnivEquiv_apply, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply w.2, Complex.ofReal_re]
  simp

theorem tr_tr (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (z : AE F E) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (Algebra.trace (AF F) (AE F E) z)) =
      ∑ w, 2 * (piInf (τ w) z).re := by
  rw [tr_evI h.1]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h1 : algebraMap (AF F) (AE F E) (Algebra.trace (AF F) (AE F E) z) = z + cA σ z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]; ring
    | tmul a e =>
      rw [← GlobalTheory.VacIndic.smul_inclR_eq, map_smul (Algebra.trace _ _), map_smul (cA σ), GlobalTheory.VacIndic.trace_inclR, GlobalTheory.VacIndic.cA_inclR, ← smul_add,
        ← map_add, ← GlobalTheory.SelfDualLatticeCompare.trace_field h, smul_eq_mul, map_mul, Algebra.smul_def]
      congr 1
      generalize Algebra.trace F E e = t
      show algebraMap F (AF F) t ⊗ₜ[F] (1 : E) = (1 : AF F) ⊗ₜ[F] algebraMap F E t
      rw [Algebra.algebraMap_eq_smul_one (A := AF F), Algebra.algebraMap_eq_smul_one (A := E), TensorProduct.smul_tmul]
  have hconj (τ : EmbOver E w) (z : AE F E) : piInf τ (cA σ z) = star (piInf τ z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy, star_add]
    | tmul a e =>
      have hz : cA σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := by simp [cA]
      have hr : star (InfinitePlace.Completion.extensionEmbedding w (a.1 w)) =
          InfinitePlace.Completion.extensionEmbedding w (a.1 w) := by
        rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (h.1.isReal w)]
        exact Complex.conj_ofReal _
      rw [hz]
      change InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 (σ e) =
        star (InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 e)
      rw [star_mul', hr, h.2.2.2]
  have h2 := congrArg (piInf (τ w)) h1
  rw [map_add (f := _), hconj] at h2
  have h3 : piInf (τ w) (algebraMap (AF F) (AE F E) (Algebra.trace (AF F) (AE F E) z)) =
      InfinitePlace.Completion.extensionEmbedding w ((Algebra.trace (AF F) (AE F E) z).1 w) * (τ w).1 1 := rfl
  rw [h3, map_one, mul_one] at h2
  rw [h2, Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

abbrev cj : ℂ →ₐ[ℝ] ℂ := Complex.conjAe

variable {n d : ℕ}

def omega (σ : E →ₐ[F] E) (X : Spc F E n) (W : Spc F E d) (u u' : Matrix (Fin n) (Fin d) (AE F E)) : ℝ :=
  Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) u u'))

variable {X : Spc F E n} {W : Spc F E d} {B : Base F E} {r s r' s' : ℕ}

theorem omega_eq (hB : B.IsGood σ) (u u' : Matrix (Fin n) (Fin d) (AE F E)) : omega σ X W u u' =
    ∑ w, 2 * (-hTens cj (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) (u.map (piInf (B.emb w))) (u'.map (piInf (B.emb w)))).re := by
  rw [omega, symp, tr_tr hB.cm B.emb]
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 2
  have hconj (τ : EmbOver E w) (z : AE F E) : piInf τ (cA σ z) = star (piInf τ z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy, star_add]
    | tmul a e =>
      have hz : cA σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := by simp [cA]
      have hr : star (InfinitePlace.Completion.extensionEmbedding w (a.1 w)) =
          InfinitePlace.Completion.extensionEmbedding w (a.1 w) := by
        rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (hB.cm.1.isReal w)]
        exact Complex.conj_ofReal _
      rw [hz]
      change InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 (σ e) =
        star (InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 e)
      rw [star_mul', hr, hB.cm.2.2.2]
  have hincl (x : E) : piInf (B.emb w) (inclR (AF F) x) = (B.emb w).1 x := by
    change piInf (B.emb w) ((1 : AF F) ⊗ₜ[F] x) = _
    change InfinitePlace.Completion.extensionEmbedding w ((1 : AF F).1 w) * (B.emb w).1 x = _
    change InfinitePlace.Completion.extensionEmbedding w 1 * _ = _
    rw [map_one, one_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hTens, neg_one_mul, map_neg, map_sum, map_mul, hconj, incM, Matrix.map_apply, hincl, cj, Complex.star_def]
  rfl

def Rel (B : Base F E) (X : Spc F E n) (W : Spc F E d) (e : InfinitePlace F → ℤˣ) (u u' : Matrix (Fin n) (Fin d) (AE F E)) : Prop :=
  ∀ w, u'.map (piInf (B.emb w)) = (((e w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ)

variable {e : InfinitePlace F → ℤˣ} {u u' u₁ u₁' : Matrix (Fin n) (Fin d) (AE F E)}

theorem sq_sign (x : ℤˣ) : ((x : ℤ) : ℂ) * ((x : ℤ) : ℂ) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp

theorem Rel.add (h : Rel B X W e u u') (h₁ : Rel B X W e u₁ u₁') : Rel B X W e (u + u₁) (u' + u₁') := fun w => by
  rw [Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), h w, h₁ w, Matrix.mul_add, Matrix.add_mul, smul_add]

theorem Rel.symm (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (h : Rel B X W e u u') : Rel B X W e u' (-u) := fun w => by
  have h2 : (W.θ w)ᵀ * (W.θ w)ᵀ = 1 := by rw [← Matrix.transpose_mul, (hW.cartan w).1, Matrix.transpose_one]
  rw [h w, Matrix.map_neg _ (map_neg _), Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    (hX.cartan w).1, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one,
    show ((e w : ℤ) : ℂ) * Complex.I * (((e w : ℤ) : ℂ) * Complex.I) = -1 by
      linear_combination (Complex.I * Complex.I) * sq_sign (e w) + Complex.I_mul_I, neg_one_smul]

theorem at_ext {α β : Type} (hB : B.IsGood σ) {u u' : Matrix α β (AE F E)} (hu : At (evI F) u) (hu' : At (evI F) u')
    (h : ∀ w, u.map (piInf (B.emb w)) = u'.map (piInf (B.emb w))) : u = u' := by
  ext i j
  refine sub_eq_zero.1 (GlobalTheory.CompanionTheory.CMAdele.eq_zero_of_piInf σ hB.cm B.emb _ (fun t ht => ?_) fun w => ?_)
  · rw [smul_sub, show t • u i j = 0 from congrFun (congrFun (hu t ht) i) j,
      show t • u' i j = 0 from congrFun (congrFun (hu' t ht) i) j, sub_zero]
  · rw [map_sub, sub_eq_zero]
    exact congrFun (congrFun (h w) i) j

theorem Rel.unique (hB : B.IsGood σ) (h : Rel B X W e u u') (h₁ : Rel B X W e u u₁') (hu : At (evI F) u') (hu' : At (evI F) u₁') :
    u' = u₁' := at_ext hB hu hu' fun w => (h w).trans (h₁ w).symm

theorem exists_vec {α : Type} (hB : B.IsGood σ) (z : InfinitePlace F → α → ℂ) :
    ∃ a : α → AE F E, At (evI F) a ∧ ∀ w i, piInf (B.emb w) (a i) = z w i := by
  choose a ha using fun i => GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ hB.cm B.emb fun w => z w i
  exact ⟨a, fun t ht => funext fun i => (ha i).1 t ht, fun w i => (ha i).2 w⟩

theorem exists_rel (hB : B.IsGood σ) (X : Spc F E n) (W : Spc F E d) (e) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    ∃ u', At (evI F) u' ∧ Rel B X W e u u' := by
  obtain ⟨a, h1, h2⟩ := exists_vec hB fun w (k : Fin n × Fin d) =>
    ((((e w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ)) k.1 k.2
  exact ⟨Matrix.of fun i j => a (i, j), fun t ht => Matrix.ext fun i j => congrFun (h1 t ht) (i, j),
    fun w => Matrix.ext fun i j => h2 w (i, j)⟩

theorem hTens_smul {α β : Type} [Fintype α] [Fintype β] (J : Matrix α α ℂ) (J' : Matrix β β ℂ) (a b : ℂ) (x y : Matrix α β ℂ) :
    hTens cj J J' (a • x) (b • y) = a * star b * hTens cj J J' x y := by
  simp only [hTens, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  change _ * (star b * _) = _
  ring

theorem omega_rel (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (h : Rel B X W e u u')
    (h₁ : Rel B X W e u₁ u₁') : omega σ X W u' u₁' = omega σ X W u u₁ := by
  rw [omega_eq hB, omega_eq hB]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h2 : (W.θ w)ᵀ * W.J.map (B.emb w).1 * (W.θ w).map cj = W.J.map (B.emb w).1 := by
    have := (hW.cartan w).2.1
    rw [Matrix.mul_smul, Matrix.smul_mul] at this
    exact smul_right_injective _ Complex.I_ne_zero this
  have h3 : (X.θ w)ᵀ * X.J.map (B.emb w).1 * (X.θ w).map cj = X.J.map (B.emb w).1 := (hX.cartan w).2.1
  rw [h w, h₁ w, hTens_smul, hTens_mul, h2, h3,
    show ((e w : ℤ) : ℂ) * Complex.I * star (((e w : ℤ) : ℂ) * Complex.I) = 1 by
      simp only [star_mul, Complex.star_def, Complex.conj_I, map_intCast]
      linear_combination (-Complex.I * Complex.I) * sq_sign (e w) - Complex.I_mul_I, one_mul]

theorem cartan_pos {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) (hM : ∀ i j, star (M j i) = M i j) (a : Fin n → ℂ) :
    ∃ p : ℝ, a ⬝ᵥ M *ᵥ star (θ *ᵥ a) = p ∧ (a = 0 → p = 0) ∧ (a ≠ 0 → 0 < p) := by
  have hs : ∀ x, star (θ *ᵥ x) = θ.map star *ᵥ star x := fun x => funext fun i => by
    simp [Matrix.mulVec, dotProduct, mul_comm]
  have h1 : a ⬝ᵥ M *ᵥ star (θ *ᵥ a) = (θ *ᵥ a) ⬝ᵥ M *ᵥ star a := by
    conv_lhs => rw [← h.2.1, ← Matrix.mulVec_mulVec, ← hs, Matrix.mulVec_mulVec a, h.1, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have h2 : star (a ⬝ᵥ M *ᵥ star (θ *ᵥ a)) = (θ *ᵥ a) ⬝ᵥ M *ᵥ star a := by
    generalize θ *ᵥ a = b
    simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', Pi.star_apply, star_star, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hM]; ring
  refine ⟨(a ⬝ᵥ M *ᵥ star (θ *ᵥ a)).re, (Complex.conj_eq_iff_re.1 (h2.trans h1.symm)).symm, fun h0 => by simp [h0], fun h0 => ?_⟩
  rw [h1]
  exact h.2.2 a h0

theorem omega_pure (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (a : Fin n → AE F E) {b : Fin d → E}
    (hb : b ≠ 0) (h : Rel B X W e (Matrix.vecMulVec a (incV F b)) u') :
    ∃ p : InfinitePlace F → ℝ, omega σ X W (Matrix.vecMulVec a (incV F b)) u' = ∑ w, ((e w : ℤ) : ℝ) * p w ∧
      ∀ w, ((fun i => piInf (B.emb w) (a i)) = 0 → p w = 0) ∧ ((fun i => piInf (B.emb w) (a i)) ≠ 0 → 0 < p w) := by
  choose p hp using fun w => cartan_pos (hX.cartan w) (fun i j => by
    rw [Matrix.map_apply, Matrix.map_apply, ← hB.cm.2.2.2, hX.herm]) fun i => piInf (B.emb w) (a i)
  choose q hq using fun w => cartan_pos (hW.cartan w) (fun i j => by
    rw [Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.map_apply, smul_eq_mul, star_mul', ← hB.cm.2.2.2, hW.skew]
    simp) fun i => (B.emb w).1 (b i)
  have hq' : ∀ w, 0 < q w := fun w => (hq w).2.2 fun h0 => hb (funext fun i => (B.emb w).1.injective
    ((congrFun h0 i).trans (map_zero _).symm))
  refine ⟨fun w => 2 * p w * q w, ?_, fun w => ⟨fun h0 => by simp [(hp w).2.1 h0],
    fun h0 => mul_pos (mul_pos two_pos ((hp w).2.2 h0)) (hq' w)⟩⟩
  rw [omega_eq hB]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e1 : (Matrix.vecMulVec a (incV F b)).map (piInf (B.emb w)) =
      Matrix.vecMulVec (fun i => piInf (B.emb w) (a i)) fun i => (B.emb w).1 (b i) := by
    have hincl (x : E) : piInf (B.emb w) (inclR (AF F) x) = (B.emb w).1 x := by
      change piInf (B.emb w) ((1 : AF F) ⊗ₜ[F] x) = _
      change InfinitePlace.Completion.extensionEmbedding w ((1 : AF F).1 w) * (B.emb w).1 x = _
      change InfinitePlace.Completion.extensionEmbedding w 1 * _ = _
      rw [map_one, one_mul]
    ext i j
    simp only [Matrix.map_apply, Matrix.vecMulVec_apply, map_mul, incV, hincl]
  have e2 : ∀ (J : Matrix (Fin n) (Fin n) ℂ) (J' : Matrix (Fin d) (Fin d) ℂ) x x' y y',
      hTens cj J J' (Matrix.vecMulVec x y) (Matrix.vecMulVec x' y') = (x ⬝ᵥ J *ᵥ star x') * (y ⬝ᵥ J' *ᵥ star y') := by
    intro J J' x x' y y'
    simp only [hTens, dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, map_mul, Pi.star_apply]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    change _ * (star _ * star _) = _
    ring
  have h1 := (hq w).1
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h1
  rw [h w, e1, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, ← one_smul ℂ (Matrix.vecMulVec _ _),
    hTens_smul, e2, (hp w).1]
  generalize (fun i => (B.emb w).1 (b i)) ⬝ᵥ _ = t at h1
  have h4 : -(1 * star (((e w : ℤ) : ℂ) * Complex.I) * (p w * t)) = ((((e w : ℤ) : ℝ) * (p w * q w) : ℝ) : ℂ) := by
    simp only [star_mul, Complex.star_def, Complex.conj_I, map_intCast]
    push_cast
    rw [← h1]
    ring
  rw [h4, Complex.ofReal_re]
  ring

end PositivityTheory.ThKF0
end
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.ExistsGaussBox
section
noncomputable section

open scoped SchwartzMap

namespace PositivityTheory.ThKF0

open PositivityTheory.Mix.Adapt Lib

variable {A κ κ₀ κ₁ : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [Fintype κ] [Fintype κ₀] [Fintype κ₁] (ε : κ ≃ κ₀ ⊕ κ₁)

theorem hcongr {f g : ℝ → ℂ} {a b : ℂ} {x : ℝ} (h : HasDerivAt f a x) (hf : ∀ t, g t = f t) (ha : b = a) : HasDerivAt g b x := by
  rw [ha, funext hf]; exact h

theorem hd {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : 𝓢(V, ℂ)) (x v : V) (s : ℝ) :
    HasDerivAt (fun t : ℝ => f (x + t • v)) (fderiv ℝ f (x + s • v) v) s := by
  have h := (f.hasFDerivAt (x + s • v)).comp_hasDerivAt s (((hasDerivAt_id s).smul_const v).const_add x)
  rw [one_smul] at h
  exact h

theorem hd0 {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : 𝓢(V, ℂ)) (x v : V) :
    HasDerivAt (fun t : ℝ => f (x + t • v)) (fderiv ℝ f x v) 0 := by
  simpa using hd f x v 0

theorem dop_smul {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V) (L : V →L[ℝ] ℝ) (c : ℂ) (f : 𝓢(V, ℂ)) :
    dop a L (c • f) = c • dop a L f := by
  ext x
  have h1 := op_apply a L (c • f) x
  have h2 := op_apply a L f x
  rw [LineDeriv.lineDerivOp_smul] at h1
  change op a L (c • f) x = c * op a L f x
  rw [h1, h2]
  change c * _ + _ * (_ * (c * _)) = _
  ring

theorem dop_add' {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V) (L : V →L[ℝ] ℝ) (f g : 𝓢(V, ℂ)) :
    dop a L (f + g) = dop a L f + dop a L g := by
  simp only [dop, LineDeriv.lineDerivOp_add, map_add (f := _), smul_add]
  abel

theorem dop_neg {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) :
    dop (-a) (-L) f = -dop a L f := by
  ext x
  simp only [SchwartzMap.neg_apply, dop_apply, map_neg, ContinuousLinearMap.neg_apply]
  push_cast
  ring

omit [Fintype κ₀] in
theorem slice_dop (f : 𝓢(κ → A, ℂ)) (g : 𝓢(κ₁ → A, ℂ)) (a : κ₀ → A) (h : ∀ y, g y = f (glue ε a y)) (L : (κ → A) →L[ℝ] ℝ)
    (L₁ : (κ₁ → A) →L[ℝ] ℝ) (hL : ∀ y, L (glue ε a y) = L₁ y) (v y : κ₁ → A) :
    dop (glue ε 0 v) L f (glue ε a y) = dop v L₁ g y := by
  rw [dop_apply, dop_apply, hL, h]
  congr 1
  refine (hd0 f _ _).unique ?_
  refine hcongr (hd0 g y v) (fun t => ?_) rfl
  rw [h, glue_smul, glue_add, smul_zero, add_zero]

omit [Fintype κ₀] [Fintype κ₁] in
theorem slice_normal (f : 𝓢(κ → A, ℂ)) (h : (κ₁ → A) → ℂ) (hf : ∀ a, ∃ c : ℂ, ∀ y, f (glue ε a y) = c * h y) (p a : κ₀ → A) :
    ∃ c : ℂ, ∀ y, fderiv ℝ f (glue ε a y) (glue ε p 0) = c * h y := by
  have e : ∀ y (t : ℝ), glue ε a y + t • glue ε p 0 = glue ε (a + t • p) y := fun y t => by
    rw [glue_smul, glue_add, smul_zero, add_zero]
  by_cases h0 : h = 0
  · refine ⟨0, fun y => (hd0 f _ _).unique ?_⟩
    refine hcongr (hasDerivAt_const (0 : ℝ) (0 : ℂ)) (fun t => ?_) ?_
    · obtain ⟨c, hc⟩ := hf (a + t • p)
      rw [e, hc, h0]; simp
    · simp
  · obtain ⟨y₀, hy⟩ := Function.ne_iff.1 h0
    refine ⟨fderiv ℝ f (glue ε a y₀) (glue ε p 0) / h y₀, fun y => (hd0 f _ _).unique ?_⟩
    refine hcongr (((hd0 f (glue ε a y₀) (glue ε p 0)).div_const (h y₀)).mul_const (h y)) (fun t => ?_) rfl
    obtain ⟨c, hc⟩ := hf (a + t • p)
    rw [e, e, hc, hc, mul_div_cancel_right₀ _ hy]

omit [Fintype κ₀] [Fintype κ₁] in
theorem slice_ode (f : 𝓢(κ → A, ℂ)) (a : κ₀ → A) (l : ℝ)
    (h : ∀ (t : ℝ) y, fderiv ℝ f (glue ε (t • a) y) (glue ε a 0) = -(2 * t * l) * f (glue ε (t • a) y)) (y : κ₁ → A) :
    f (glue ε a y) = Complex.exp (-l) * f (glue ε 0 y) := by
  have e : ∀ t : ℝ, glue ε 0 y + t • glue ε a 0 = glue ε (t • a) y := fun t => by
    rw [glue_smul, glue_add, smul_zero, add_zero, zero_add]
  have h1 : ∀ s : ℝ, HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) ^ 2 * l) * f (glue ε 0 y + t • glue ε a 0)) 0 s := fun s => by
    have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ 2 * l) (2 * s * l) s := by
      simpa using (((hasDerivAt_pow 2 (s : ℂ)).comp_ofReal).mul_const (l : ℂ))
    refine hcongr (h2.cexp.fun_mul (hd f (glue ε 0 y) (glue ε a 0) s)) (fun _ => rfl) ?_
    rw [e, h]
    ring
  have h3 := is_const_of_deriv_eq_zero (fun s => (h1 s).differentiableAt) (fun s => (h1 s).deriv) 1 0
  simp only [e] at h3
  simp only [one_smul, zero_smul, Complex.ofReal_one, one_pow, one_mul, Complex.ofReal_zero] at h3
  rw [Complex.exp_neg, eq_inv_mul_iff_mul_eq₀ (Complex.exp_ne_zero _), h3]
  simp

theorem exists_gauss_box [FiniteDimensional ℝ A] (Q : (κ₀ → A) →ₗ[ℝ] (κ₀ → A) →ₗ[ℝ] ℝ) (hs : ∀ a b, Q a b = Q b a)
    (hp : ∀ a, a ≠ 0 → 0 < Q a a) (g : 𝓢(κ₁ → A, ℂ)) : ∃ f : 𝓢(κ → A, ℂ), (∀ y, f (glue ε 0 y) = g y) ∧
      (∀ a, ∃ c : ℂ, ∀ y, f (glue ε a y) = c * g y) ∧
      ∀ a y p, fderiv ℝ f (glue ε a y) (glue ε p 0) = -(2 * Real.pi * Q a p) * f (glue ε a y) := by
  let Qc : (κ₀ → A) →L[ℝ] (κ₀ → A) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((κ₀ → A) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ ((-Real.pi) • Q))
  have hQ : ∀ a b, Qc a b = -Real.pi * Q a b := fun _ _ => rfl
  obtain ⟨G, hG⟩ := exists_schwartz_exp_diag Qc fun a ha => by
    rw [hQ]; exact mul_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) (hp a ha)
  let f := schwartzBox G g (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (ε.symm (.inl i)))
    (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (ε.symm (.inr i))) fun x : κ → A => by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
      obtain ⟨k, rfl⟩ := ε.symm.surjective k
      rcases k with k | k
      · exact le_max_of_le_left (norm_le_pi_norm (fun i => x (ε.symm (.inl i))) k)
      · exact le_max_of_le_right (norm_le_pi_norm (fun i => x (ε.symm (.inr i))) k)
  have hf : ∀ a y, f (glue ε a y) = Complex.exp (-Real.pi * Q a a) * g y := fun a y => by
    show G (fun i => glue ε a y _) * g (fun i => glue ε a y _) = _
    simp only [glue_inl, glue_inr, hG, hQ]
    push_cast
    rfl
  refine ⟨f, fun y => by simp [hf], fun a => ⟨_, hf a⟩, fun a y p => (hd0 f _ _).unique ?_⟩
  have h2 : HasDerivAt (fun t : ℝ => -(Real.pi : ℂ) * (Q a a + 2 * t * Q a p + (t : ℂ) ^ 2 * Q p p))
      (-(Real.pi : ℂ) * (2 * (Q a p : ℂ))) 0 :=
    hcongr ((((((hasDerivAt_id ((0 : ℝ) : ℂ)).const_mul 2).mul_const (Q a p : ℂ)).const_add (Q a a : ℂ)).fun_add
      ((hasDerivAt_pow 2 ((0 : ℝ) : ℂ)).mul_const (Q p p : ℂ))).const_mul (-(Real.pi : ℂ))).comp_ofReal (fun _ => rfl) (by simp)
  refine hcongr (h2.cexp.mul_const (g y)) (fun t => ?_) ?_
  · skip
    rw [glue_smul, glue_add, smul_zero, add_zero, hf]
    simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hs p a]
    push_cast
    congr 2
    ring
  · rw [hf]
    simp
    ring

end PositivityTheory.ThKF0
end
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.ThetaSumInvariantRationalUnitary
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

noncomputable section
namespace PositivityTheory.ThKF0

theorem rat_det_ne_zero_of_hasSig {n r s : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  have key : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
      Matrix.submatrix_mul Aᵀ M e.symm id id Function.bijective_id]
    simp [Matrix.transpose_submatrix, Matrix.submatrix_map]
  intro h0
  have := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self] at this
  simp [Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg] at this
  exact pow_ne_zero s (by norm_num : (-1 : ℂ) ≠ 0) this.symm

theorem rat_det_ne_zero_of_map {E : Type} [Field E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ)
    (h : (J.map f).det ≠ 0) : J.det ≠ 0 := by
  intro h0
  apply h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem theta_sum_rational_invariance : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP γ hγ γ' hγ' Φ hΦ
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hX : X.J.det ≠ 0 := rat_det_ne_zero_of_map X.J (B.emb w).1 (rat_det_ne_zero_of_hasSig _ (hP.herm.sig w))
  have hW : W.J.det ≠ 0 := by
    refine rat_det_ne_zero_of_map W.J (B.emb w).1 fun h0 => rat_det_ne_zero_of_hasSig _ (hP.skew.sig w) ?_
    rw [Matrix.det_smul, h0, mul_zero]
  exact darboux_coordinates_rational_exist F E σ hP.base.cm B.ψ hP.base.std n d X.J W.J hP.herm.herm hX hP.skew.skew hW M.co
    hP.good.rat χX χW hP.hX hP.hW om hP.weil γ hγ γ' hγ' Φ hΦ

end PositivityTheory.ThKF0
end
end

