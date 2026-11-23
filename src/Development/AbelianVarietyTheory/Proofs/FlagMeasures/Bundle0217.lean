module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0193
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0190
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0213
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Formalism.HermitianLattices.HermitianLatticesProofs.MassTelescope
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DiscriminantKernelAutomorphisms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFiniteAdelicOrthogonalStabilizerEmbedding
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem exists_stab_emb_baseChange {E R : Type} [Field E] [StarRing E] [CommRing R] (φ : E →+* R)
    (σ : R →+* R) (hσ : ∀ a, σ (φ a) = φ (star a)) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (J' : Matrix (Fin m) (Fin m) E) (x : Fin n → E) (A : Matrix (Fin n) (Fin m) E)
    (hn : m + 1 = n) (hJ : Jᴴ = J) (hd : J'.det ≠ 0) (hx : star x ⬝ᵥ (J *ᵥ x) ≠ 0)
    (hxA : star x ᵥ* (J * A) = 0) (hA : Aᴴ * J * A = J') :
    ∃ j : Formalism.UG.UJ σ (J'.map φ) →* Formalism.UG.UJ σ (J.map φ),
      (∀ g, ((j g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ (fun i => φ (x i)) = (fun i => φ (x i)) ∧
        ((j g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * A.map φ =
          A.map φ * ((g : GL (Fin m) R) : Matrix (Fin m) (Fin m) R)) ∧
      ∀ h : Formalism.UG.UJ σ (J.map φ),
        ((h : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ (fun i => φ (x i)) = (fun i => φ (x i)) →
          h ∈ j.range := by
  obtain ⟨u, A', h1, h2, h3, h4, h5, h6⟩ := exists_dual_of_anisotropic_orthogonal E n m J J' x A hn hJ hd hx hxA hA
  have hsx : (fun i => σ (φ (x i))) = φ ∘ star x := by
    funext i; simp [hσ]
  have hcT : Formalism.UG.cT σ (A.map φ) = (Aᴴ).map φ := by
    ext i j; simp [Formalism.UG.cT, hσ]
  have mv : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) E) (v : Fin b → E),
      M.map φ *ᵥ (φ ∘ v) = φ ∘ (M *ᵥ v) := by
    intro a b M v; funext i; exact (RingHom.map_mulVec φ M v i).symm
  have vm : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) E) (v : Fin a → E),
      (φ ∘ v) ᵥ* M.map φ = φ ∘ (v ᵥ* M) := by
    intro a b M v; funext i; exact (RingHom.map_vecMul φ M v i).symm
  have z : ∀ {a : ℕ}, φ ∘ (0 : Fin a → E) = 0 := by
    intro a; funext i; simp
  have k1 : A'.map φ * A.map φ = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one φ (map_zero φ) (map_one φ)]
  have k2 : A'.map φ *ᵥ (φ ∘ x) = 0 := by rw [mv, h2, z]
  have k3 : (φ ∘ u) ᵥ* A.map φ = 0 := by rw [vm, h3, z]
  have k4 : (φ ∘ u) ⬝ᵥ (φ ∘ x) = 1 := by rw [← RingHom.map_dotProduct, h4, map_one]
  have k5 : vecMulVec (φ ∘ x) (φ ∘ u) + A.map φ * A'.map φ = 1 := by
    rw [← Matrix.map_one φ (map_zero φ) (map_one φ), ← h5, ← Matrix.map_mul]
    ext i j; simp [vecMulVec_apply, Matrix.mul_apply]
  obtain ⟨j, hj, hr⟩ := _root_.GlobalTheory.StabRing.exists_emb R σ n m (J.map φ) (J'.map φ) (φ ∘ x) (φ ∘ u) (A.map φ) (A'.map φ)
    (by
      change IsUnit ((fun i => σ (φ (x i))) ⬝ᵥ _)
      rw [hsx, mv, ← RingHom.map_dotProduct]
      exact (IsUnit.mk0 _ hx).map φ)
    (by
      change (fun i => σ (φ (x i))) ᵥ* _ = 0
      rw [hsx, ← Matrix.map_mul, vm, hxA, z])
    (by rw [hcT, mv, mv, h6, z])
    (by rw [hcT, ← Matrix.map_mul, ← Matrix.map_mul, hA])
    k1 k2 k3 k4 k5
  refine ⟨j, fun g => ⟨?_, ?_⟩, hr⟩
  · change _ *ᵥ (φ ∘ x) = φ ∘ x
    rw [hj, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, k2, Matrix.mulVec_zero, add_zero,
      Matrix.vecMulVec_mulVec, k4]
    simp
  · rw [hj, Matrix.add_mul, Matrix.mul_assoc, k1, Matrix.mul_one, Matrix.vecMulVec_mul, k3]
    ext a b; simp [vecMulVec_apply]

theorem exists_finEmb : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∃ jf : D.inst.Gf →* I.Gf, IsFinEmb D x A jf ∧ ∀ h : I.Gf, I.fmat h *ᵥ afVec I x = afVec I x → h ∈ jf.range := by
  intro I D s x A xf h
  obtain ⟨hn, hx, hxA, hA, -, -⟩ := h
  have hσ : ∀ a : I.E, Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) a) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (star a) := by
    intro a
    have : I.cm.sig a = star a := rfl
    simp [Formalism.UG.sigR, Formalism.UG.inclE, this]
  have hx' : star x ⬝ᵥ (I.J *ᵥ x) ≠ 0 := by
    rw [hx]; cases s <;> simp [sgn]
  exact exists_stab_emb_baseChange (Formalism.UG.inclE (F := I.F) (Af I.F)) (Formalism.UG.sigR I.cm.sig (Af I.F)) hσ
    I.J D.J x A hn I.J_herm D.J_det hx' hxA hA

end GlobalTheory.StabUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundSkew
section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical nonZeroDivisors

noncomputable section

namespace GlobalTheory.SkewFund

open GlobalTheory.HomCovolume

theorem one_le_covolume {ι : Type} [Fintype ι] (A : Submodule ℤ (ι → ℝ)) [DiscreteTopology A] [IsZLattice ℝ A]
    (h : ∀ x ∈ A, x ≠ 0 → 1 ≤ ‖x‖) : 1 ≤ ZLattice.covolume A volume := by
  by_contra hlt
  rw [not_le] at hlt
  have : Countable A.toAddSubgroup := inferInstanceAs (Countable A)
  have hF : IsAddFundamentalDomain A.toAddSubgroup (latticeDomain A) volume :=
    isAddFundamentalDomain_latticeDomain A volume
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hF
    (s := Metric.ball 0 1) (fun x hx => by simpa using hx) (convex_ball _ _) (by
      rw [measure_latticeDomain, Real.volume_pi_ball _ one_pos, Module.finrank_fintype_fun_eq_card,
        mul_one, ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
      calc _ < 1 * 2 ^ Fintype.card ι :=
            ENNReal.mul_lt_mul_left (by simp) (by simp) (ENNReal.ofReal_lt_one.2 hlt)
        _ = _ := one_mul _)
  exact absurd (h x x.2 (fun h0 => hx0 (Subtype.ext h0))) (by simpa using hx)

theorem imag_covolume {ι : Type} [Fintype ι] (L : Submodule ℤ (ι → ℂ)) {c : ℝ} (hc : HasCov volume L c)
    (hs : ∀ z ∈ L, (fun v => starRingEnd ℂ (z v)) ∈ L) (hn : ∀ z ∈ L, z ≠ 0 → 1 ≤ ‖z‖) :
    ∃ B : Submodule ℤ (ι → ℝ), (∀ y, y ∈ B ↔ (fun v => (⟨0, y v⟩ : ℂ)) ∈ L) ∧
      ∃ b, HasCov volume B b ∧ 1 ≤ b ∧ b ≤ 2 ^ Fintype.card ι * c := by
  let e : ((ι → ℝ) × (ι → ℝ)) ≃L[ℝ] (ι → ℂ) := LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p v => ⟨p.1 v, p.2 v⟩
      invFun := fun z => (fun v => (z v).re, fun v => (z v).im)
      map_add' := fun p q => by ext v; apply Complex.ext <;> simp
      map_smul' := fun c p => by ext v; apply Complex.ext <;> simp
      left_inv := fun p => rfl
      right_inv := fun z => rfl }
  have he : ∀ p v, e p v = ⟨p.1 v, p.2 v⟩ := fun _ _ => rfl
  have hmp : MeasurePreserving e (Measure.prod volume volume) volume :=
    (volume_preserving_pi (ι := ι) fun _ => Complex.volume_preserving_equiv_real_prod.symm).comp
      (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι).symm
  let M : Submodule ℤ ((ι → ℝ) × (ι → ℝ)) := L.comap (e.toLinearMap.restrictScalars ℤ)
  have hM : ∀ p, p ∈ M ↔ e p ∈ L := fun _ => Iff.rfl
  have : ((volume : Measure (ι → ℝ)).prod (volume : Measure (ι → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  obtain ⟨_, _, hcM⟩ := HasCov.of_measurePreserving e hmp hM hc
  let A : Submodule ℤ (ι → ℝ) := M.comap (LinearMap.inl ℤ _ _)
  let B : Submodule ℤ (ι → ℝ) := M.comap (LinearMap.inr ℤ _ _)
  obtain ⟨⟨_, _⟩, ⟨_, _⟩, h⟩ := GlobalTheory.ReImLattice.reflection_stable volume M (fun p hp => by
    rw [hM] at hp ⊢
    convert hs _ hp using 1
    ext v; apply Complex.ext <;> simp [he]) A B (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have key : ∀ (x : ι → ℝ) (z : ι → ℂ), z ∈ L → (∀ v, ‖z v‖ = ‖x v‖) → x ≠ 0 → 1 ≤ ‖x‖ := by
    intro x z hz hzx hx
    have h1 : ‖z‖ = ‖x‖ := by
      refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun v => ?_)
        ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun v => ?_)
      · rw [hzx]; exact norm_le_pi_norm x v
      · rw [← hzx]; exact norm_le_pi_norm z v
    rw [← h1]
    exact hn z hz (by rw [← norm_ne_zero_iff, h1]; exact norm_ne_zero_iff.2 hx)
  have hA : 1 ≤ ZLattice.covolume A volume := one_le_covolume A fun x hx =>
    key x (e (x, 0)) hx fun v => by
      have : e (x, 0) v = (x v : ℂ) := rfl
      rw [this, Complex.norm_real]
  have hB : 1 ≤ ZLattice.covolume B volume := one_le_covolume B fun x hx =>
    key x (e (0, x)) hx fun v => by
      have : e (0, x) v = (x v : ℂ) * Complex.I := by apply Complex.ext <;> simp [he]
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
  refine ⟨B, fun _ => Iff.rfl, _, ⟨inferInstance, inferInstance, rfl⟩, hB, ?_⟩
  rw [hcM, Module.finrank_fintype_fun_eq_card] at h
  exact (le_mul_of_one_le_left (zero_le_one.trans hB) hA).trans h

theorem prod_norm_sq (K : Type) [Field K] [NumberField K] (hK : IsTotallyComplex K) {ι : Type} [Fintype ι]
    (σ : ι → (K →+* ℂ)) (hσ : ∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (σ v) = w) (t : K) :
    ∏ v, ‖σ v t‖ ^ 2 = ((|Algebra.norm ℚ t| : ℚ) : ℝ) := by
  rw [← InfinitePlace.prod_eq_abs_norm]
  refine Fintype.prod_bijective _ ((Function.bijective_iff_existsUnique _).2 hσ) _ _ fun v => ?_
  rw [InfinitePlace.mult_isComplex ⟨_, hK.isComplex _⟩, InfinitePlace.apply]

theorem exists_fund_skew : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)), IsPlaces σ → ∀ (𝔡 : Ideal (𝓞 K)) (n : ℕ), 𝔡 ≠ ⊥ → (∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) → (Ideal.absNorm 𝔡 : ℝ) = (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * Fintype.card ι) → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → ∃ F : Set (ι → ℝ), MeasurableSet F ∧ (∀ a : ι → ℝ, ∃! t : K, (t ∈ ipow 𝔡 (-(2 * (n : ℤ))) ∧ t + star t = 0) ∧ ((fun v => (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * n) * (σ v t).im) + a) ∈ F) ∧ ENNReal.ofReal ((8 * Formalism.HermitianLatticesTheory.vInv K) ^ (-(Fintype.card ι : ℝ))) ≤ volume F ∧ volume F ≤ ENNReal.ofReal ((8 * Formalism.HermitianLatticesTheory.vInv K) ^ (Fintype.card ι : ℝ)) := by
  intro K _ _ _ hK ι _ σ hσ 𝔡 n h𝔡 hs hN hv
  set v₀ := Formalism.HermitianLatticesTheory.vInv K with hv₀
  set c : ℝ := (2 * v₀) ^ (2 * n) with hc
  have hc0 : 0 < c := by positivity
  have h0 : (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔡
  obtain ⟨L₀, hL₀, hcov⟩ := GlobalTheory.IdealFund.exists_lat K hK.1 ι σ hσ.2 _ (zpow_ne_zero (-(2 * (n : ℤ))) h0)
  have hNa : ((FractionalIdeal.absNorm ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (-(2 * (n : ℤ)))) : ℚ) : ℝ) =
      c⁻¹ ^ (2 * Fintype.card ι) := by
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
    push_cast
    rw [hN, _root_.zpow_neg, inv_pow, hc, show (2 * (n : ℤ)) = ((2 * n : ℕ) : ℤ) by push_cast; rfl, _root_.zpow_natCast,
      ← pow_mul, ← pow_mul, mul_comm (2 * n)]
  let f : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) := c⁻¹ • LinearMap.id
  have hf : ∀ z v, f z v = (c : ℂ)⁻¹ * z v := fun _ _ => by simp [f]
  have hdet : LinearMap.det f = c⁻¹ ^ (2 * Fintype.card ι) := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_pi_fintype]
    simp [mul_comm]
  have hpos : 0 < c⁻¹ ^ (2 * Fintype.card ι) := by positivity
  let L : Submodule ℤ (ι → ℂ) := L₀.comap (f.restrictScalars ℤ)
  have h := HasCov.of_det f (L := L) (by rw [hdet]; exact hpos.ne') (fun _ => Iff.rfl) hcov
  rw [hNa, hdet, abs_of_pos hpos, mul_div_cancel_left₀ _ hpos.ne'] at h
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
  have hL : ∀ z, z ∈ L ↔ ∃ t ∈ ipow 𝔡 (-(2 * (n : ℤ))), z = fun v => c * σ v t := by
    intro z
    change f z ∈ L₀ ↔ _
    rw [hL₀]
    refine exists_congr fun y => and_congr Iff.rfl ⟨fun h => funext fun v => ?_, fun h v => ?_⟩
    · rw [← h, hf, mul_inv_cancel_left₀ hcc]
    · rw [hf, h, inv_mul_cancel_left₀ hcc]
  obtain ⟨B, hB, b, ⟨_, _, hb⟩, hb1, hb2⟩ := imag_covolume L h (fun z hz => by
    obtain ⟨t, ht, rfl⟩ := (hL z).1 hz
    exact (hL _).2 ⟨star t, IdealPow.star_mem h𝔡 hs ht, funext fun v => by simp [hσ.1]⟩) (fun z hz hz0 => by
    obtain ⟨t, ht, rfl⟩ := (hL z).1 hz
    have ht0 : t ≠ 0 := by rintro rfl; exact hz0 (funext fun v => by simp)
    have h1 : c⁻¹ ^ (2 * Fintype.card ι) ≤ ∏ v, ‖σ v t‖ ^ 2 := by
      rw [← hNa, prod_norm_sq K hK.1 σ hσ.2]
      exact_mod_cast GlobalTheory.absNorm_le_abs_norm_of_mem ht ht0
    by_contra hlt
    rw [not_le, pi_norm_lt_iff one_pos] at hlt
    obtain ⟨u, -⟩ := (hσ.2 (Classical.arbitrary _)).exists
    refine absurd h1 (not_le.2 ?_)
    rw [pow_mul, ← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_lt_prod_of_nonempty₀ (fun v _ => pow_pos (norm_pos_iff.2 ((map_ne_zero _).2 ht0)) _)
      (fun v _ => pow_lt_pow_left₀ ?_ (norm_nonneg _) two_ne_zero) ⟨u, Finset.mem_univ _⟩
    have := hlt v
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0.le] at this
    rwa [← one_mul c⁻¹, lt_mul_inv_iff₀ hc0, mul_comm])
  obtain ⟨u, -⟩ := (hσ.2 (Classical.arbitrary _)).exists
  have hre : ∀ t : K, t + star t = 0 → ∀ v, (σ v t).re = 0 := fun t ht v => by
    have := congrArg (fun x => (σ v x).re) ht
    simp only [map_add (f := _), hσ.1, map_zero, Complex.add_re, Complex.conj_re, Complex.zero_re] at this
    linarith
  have hB' : ∀ y, y ∈ B ↔ ∃ t : K, (t ∈ ipow 𝔡 (-(2 * (n : ℤ))) ∧ t + star t = 0) ∧
      y = fun v => c * (σ v t).im := by
    intro y
    rw [hB, hL]
    constructor
    · rintro ⟨t, ht, hy⟩
      refine ⟨t, ⟨ht, (σ u).injective ?_⟩, funext fun v => by simpa using congrArg Complex.im (congrFun hy v)⟩
      have h1 : (σ u t).re = 0 := by simpa [hc0.ne'] using congrArg Complex.re (congrFun hy u)
      rw [map_add (f := _), hσ.1, map_zero]
      apply Complex.ext <;> simp [h1]
    · rintro ⟨t, ⟨ht, ht'⟩, rfl⟩
      exact ⟨t, ht, funext fun v => by apply Complex.ext <;> simp [hre t ht']⟩
  refine ⟨latticeDomain B, measurableSet_latticeDomain B, fun a => ?_, ?_, ?_⟩
  · obtain ⟨z, hz, hu⟩ := existsUnique_add_mem_latticeDomain B a
    obtain ⟨t, ht, hzt⟩ := (hB' z).1 z.2
    refine ⟨t, ⟨ht, by rw [← hzt, add_comm]; exact hz⟩, ?_⟩
    rintro t' ⟨ht', h'⟩
    have h1 := hu ⟨_, (hB' _).2 ⟨t', ht', rfl⟩⟩ (by rw [add_comm] at h'; exact h')
    have h2 := congrFun ((congrArg Subtype.val h1).trans hzt) u
    exact (σ u).injective (Complex.ext (by rw [hre t ht.2, hre t' ht'.2]) (mul_left_cancel₀ hc0.ne' h2))
  · rw [measure_latticeDomain, hb]
    exact ENNReal.ofReal_le_ofReal ((Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by simp)).trans hb1)
  · rw [measure_latticeDomain, hb, Real.rpow_natCast]
    refine ENNReal.ofReal_le_ofReal (hb2.trans ?_)
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) _

end GlobalTheory.SkewFund
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsSatFlag
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.FlagSat

theorem mem_of_isSat (I : AutInst) (x : I.GA) {N : Submodule (𝓞 I.E) (Fin I.n → I.E)}
    (hN : Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) N) {y : Fin I.n → I.E}
    (hy : y ∈ lamX I x) (hy' : y ∈ Submodule.span I.E (N : Set (Fin I.n → I.E))) : y ∈ N := by
  set A : Submodule (𝓞 I.E) (Fin I.n → I.E) :=
    lamX I x ⊓ (Submodule.span I.E (N : Set (Fin I.n → I.E))).restrictScalars (𝓞 I.E) with hA
  have hle : N ≤ A := fun z hz => ⟨hN.1 hz, Submodule.subset_span hz⟩
  have hAL : A ≤ lamX I x := inf_le_left
  have e : N = A := by
    by_contra hne
    have h1 := GlobalTheory.PointFlag.rkK_lt _ _ (GlobalTheory.PointFlag.frm_unit I x) (GlobalTheory.PointFlag.fg_of_le I x hAL)
      (GlobalTheory.PointFlag.isSat_of_le _ _ hN hle hAL) hne
    have h2 : Submodule.span I.E (A : Set (Fin I.n → I.E)) ≤ Submodule.span I.E (N : Set (Fin I.n → I.E)) :=
      Submodule.span_le.2 fun z hz => hz.2
    exact absurd h1 (not_lt.2 (Submodule.finrank_mono h2))
  rw [e]
  exact ⟨hy, hy'⟩

theorem exists_isSatFlag : ∀ (I : AutInst) (a : ℕ) (j : Fin a → ℕ) (B : Set (Fin a → ℝ)) (x : I.GA), x ∈ typeSet I j B → ∃ S, IsSatFlag I (lamX I (1, x.2)) j S ∧ sizesAt I x.2 S x.1 ∈ B := by
  rintro I a j B x ⟨τ, hτ, S, hS, hj⟩
  refine ⟨S, ⟨hS.1, hS.2.1.monotone, hj, fun i y => ?_, ?_⟩, ?_⟩
  · have h := GlobalTheory.PointFlag.flag_sat hS i
    exact ⟨fun hy => ⟨h.1 hy, Submodule.subset_span hy⟩, fun hy => mem_of_isSat I x h hy.1 hy.2⟩
  · rw [hS.2.2.1]
    exact (GlobalTheory.FlagIso.flag_isotropic I x).1
  · have e : sizesAt I x.2 S x.1 = τ := funext fun i => (hS.2.2.2.2.1 i).2.2.2
    rw [e]
    exact hτ

end GlobalTheory.FlagSat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsReductionActionChosenPlaces
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev

theorem IsChoice.eq_of_mem {I : AutInst} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type}
    {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)} (h : IsChoice I g Pl w) {k k' : Fin 2}
    (u : HeightOneSpectrum (𝓞 I.E)) (h1 : ((g k : ℕ) : 𝓞 I.E) ∈ u.asIdeal) (h2 : ((g k' : ℕ) : 𝓞 I.E) ∈ u.asIdeal) :
    k = k' := by
  by_contra hkk
  have hg : g k ≠ g k' := by
    intro e
    apply hkk
    fin_cases k <;> fin_cases k'
    · rfl
    · exact absurd e h.2.1
    · exact absurd e.symm h.2.1
    · rfl
  obtain ⟨a, b, hab⟩ : IsCoprime (g k : ℤ) (g k') :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (h.1 k) (h.1 k')).mpr hg)
  have e : (a : 𝓞 I.E) * ((g k : ℕ) : 𝓞 I.E) + (b : 𝓞 I.E) * ((g k' : ℕ) : 𝓞 I.E) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 I.E) hab
    push_cast at this
    exact this
  apply u.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem IsChoice.ne_of_ne {I : AutInst} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type}
    {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)} (h : IsChoice I g Pl w) {a b : Σ k, Pl k} (hab : b ≠ a) :
    w b.1 b.2 ≠ w a.1 a.2 ∧ ¬ IsConj I (w a.1 a.2) (w b.1 b.2) := by
  obtain ⟨ka, va⟩ := a
  obtain ⟨kb, vb⟩ := b
  dsimp only
  have hmem := h.2.2.2.1
  by_cases hk : kb = ka
  · subst hk
    have hv : vb ≠ va := fun e => hab (by rw [e])
    exact ⟨fun e => hv (h.2.2.2.2.1 kb e), h.2.2.2.2.2.1 kb va vb⟩
  · refine ⟨fun e => hk (h.eq_of_mem (w kb vb) (hmem kb vb).1 (by rw [e]; exact (hmem ka va).1)), fun hcj => hk ?_⟩
    have hx := (hcj ((g ka : ℕ) : 𝓞 I.E) ((g ka : ℕ) : 𝓞 I.E) (by simp)).mp (hmem ka va).1
    exact (h.eq_of_mem (w kb vb) hx (hmem kb vb).1).symm

theorem PlFrame.actsAs_one_of_mem {I : AutInst} {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w)
    {x : I.Gf} (hx : ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ extId I w.asIdeal • I.Lf) : fr.ActsAs x 1 := by
  intro y h
  rw [Matrix.one_mulVec, ← sub_eq_zero, ← map_sub]
  refine (fr.c_ker _).mpr ?_
  have e : ((⟨_, h⟩ - y : I.Lf) : Fin I.n → _) = (I.fmat x - 1) *ᵥ (y : Fin I.n → _) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Submodule.coe_sub]
  rw [e]
  exact hx _ y.2

private theorem val_eq_lemma {I : AutInst} {N : ℕ} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type}
    {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)} {fr : ∀ k v, PlFrame I N (g k) (w k v)}
    {ρ : I.Gf → GProd N g Pl} (hρ : ActsBy fr ρ) {x : I.Gf} (hx : x ∈ I.Kset) (kv : Σ k, Pl k)
    {M : GL (Fin N) (ZMod (g kv.1))} (hM : (fr kv.1 kv.2).ActsAs x (M : Matrix (Fin N) (Fin N) (ZMod (g kv.1)))) :
    ρ x kv = M :=
  Units.ext (PlFrame.ActsAs.unique (fr kv.1 kv.2) hx (hρ x hx kv.1 kv.2) hM)

theorem exists_red_actsBy : ∀ (I : AutInst) (N : ℕ) (g : Fin 2 → ℕ) (Pl : Fin 2 → Type)
    (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)) (fr : ∀ k v, PlFrame I N (g k) (w k v)) [∀ k, Finite (Pl k)],
    I.n = N → IsChoice I g Pl w → ∃ ρ : Red I (g 0 * g 1) (GProd N g Pl), ActsBy fr ρ.toFun := by
  intro I N g Pl w fr _ hn hc
  classical
  obtain ⟨ρ, hρ, hmul⟩ := exists_actsBy fr
  have hK1 : (1 : I.Gf) ∈ I.Kset := (Inhab.mem_Ksub I 1).mp (Inhab.Ksub I).one_mem
  have hKmul : ∀ x ∈ I.Kset, ∀ y ∈ I.Kset, x * y ∈ I.Kset := fun x hx y hy =>
    (Inhab.mem_Ksub I _).mp
      ((Inhab.Ksub I).mul_mem ((Inhab.mem_Ksub I x).mpr hx) ((Inhab.mem_Ksub I y).mpr hy))
  have hone : ∀ x ∈ I.Kset, ∀ kv : (Σ k, Pl k), (fr kv.1 kv.2).ActsAs x 1 → ρ x kv = 1 :=
    fun x hx kv h => val_eq_lemma hρ hx kv (M := 1) (by rw [Units.val_one]; exact h)
  have : Fintype (Σ k, Pl k) := Fintype.ofFinite _
  refine ⟨⟨ρ, hmul, fun x hx => ?_, fun q => ?_⟩, hρ⟩
  · rw [← _root_.GlobalTheory.RowLev.trivial_iff_mem_Kg I N g Pl w fr hn hc x hx]
    constructor
    · intro h1 k v y h
      rw [hρ x hx k v y h, h1]
      simp
    · intro h
      funext kv
      exact hone x hx kv (fun y hy => by rw [h kv.1 kv.2 y hy, Matrix.one_mulVec])
  · have key : ∀ s : Finset (Σ k, Pl k), ∃ x ∈ I.Kset, ρ x = fun kv => if kv ∈ s then q kv else 1 := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · exact ⟨1, hK1, funext fun kv => by simpa using hone 1 hK1 kv (fr kv.1 kv.2).actsAs_one⟩
      · intro a s ha ih
        obtain ⟨xs, hxs, es⟩ := ih
        obtain ⟨xa, hxa, hact, hoth⟩ := _root_.GlobalTheory.RowLev.exists_mem_Kset_actsAs_trivial_away I N (g a.1) (w a.1 a.2) (fr a.1 a.2) hn (hc.1 a.1)
          (hc.2.2.2.1 a.1 a.2).2 (hc.2.2.2.2.2.1 a.1 a.2 a.2) (q a)
        refine ⟨xa * xs, hKmul xa hxa xs hxs, ?_⟩
        rw [hmul xa hxa xs hxs, es]
        funext kv
        by_cases hk : kv = a
        · rw [hk, Pi.mul_apply, val_eq_lemma hρ hxa a hact]
          simp [ha]
        · have hne := IsChoice.ne_of_ne hc hk
          rw [Pi.mul_apply, hone xa hxa kv (PlFrame.actsAs_one_of_mem _ (hoth _ hne.1 hne.2))]
          simp [hk]
    obtain ⟨x, hx, e⟩ := key Finset.univ
    exact ⟨x, hx, by rw [e]; simp⟩

end GlobalTheory.RowLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRepsOfFinite
section
noncomputable section

open scoped Classical

namespace GlobalTheory.RowMassCompare

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.IndefiniteRowSideFullHecke.DiscriminantKernelAutomorphisms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pieces

variable (D : D7) (u : D.what₂.Word)

end Pieces

section Gmap

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem gmap_mul' (a b : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) M = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b M) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [← Submodule.map_comp]
  rfl

theorem gmap_one' (M : Submodule (𝓞 K) V) : Formalism.HermitianLatticesTheory.gmap (1 : V ≃ₗ[K] V) M = M := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

end Gmap

section Stab

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem mul_mem_stabF {a b : (VS D).V ≃ₗ[D.host.E] (VS D).V} (ha : a ∈ stabF D F0) (hb : b ∈ stabF D F0) :
    a * b ∈ stabF D F0 := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ha.1 hb.1, fun j => ?_, ?_⟩
  · have : ((a * b : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) =
        (a : (VS D).V →ₗ[D.host.E] (VS D).V) ∘ₗ (b : (VS D).V →ₗ[D.host.E] (VS D).V) := rfl
    rw [this, Submodule.map_comp, hb.2.1 j, ha.2.1 j]
  · show a (b F0.z) = F0.z
    rw [hb.2.2, ha.2.2]

end Stab

end GlobalTheory.RowMassCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryLeadingTermOfSkewLayerStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_leading_term_of_skew_layer : ∀ (R K : Type) [CommRing R] [Field K] [StarRing K] [Algebra R K] (n m : ℕ) (J : Matrix (Fin n) (Fin n) K) (A : ℕ → Submodule R (Matrix (Fin n) (Fin n) K)) (w : R), Jᴴ = J → J.det ≠ 0 → algebraMap R K w + star (algebraMap R K w) = 1 → (∀ c, A (c + 1) ≤ A c) → A m = ⊥ → (∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1)) → (∀ c, ∀ X ∈ A c, J⁻¹ * Xᴴ * J ∈ A c) → ∀ c, ∀ X ∈ A c, J⁻¹ * Xᴴ * J = -X → ∃ Y ∈ A (c + 1), (1 + X + Y)ᴴ * J * (1 + X + Y) = J := by
  first | exact @GlobalTheory.RadCov.exists_unitary_of_skew_layer | exact GlobalTheory.RadCov.exists_unitary_of_skew_layer | (intros; apply GlobalTheory.RadCov.exists_unitary_of_skew_layer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinrankMatricesLoweringFiltrationByEqSuccAddStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_matricesLoweringFiltrationBy_eq_succ_add : ∀ (n m : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ) (U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ), Biorth r m U (fun b => (U b)ᴴ) → (∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0) → ∀ c, Module.finrank ℂ (lowers W c) = Module.finrank ℂ (lowers W (c + 1)) + ∑ b ∈ Finset.range m, r b * r (b + c + 1) := by
  first | exact @GlobalTheory.RadCov.finrank_lowers_eq_succ_add | exact GlobalTheory.RadCov.finrank_lowers_eq_succ_add | (intros; apply GlobalTheory.RadCov.finrank_lowers_eq_succ_add <;> assumption)
end

