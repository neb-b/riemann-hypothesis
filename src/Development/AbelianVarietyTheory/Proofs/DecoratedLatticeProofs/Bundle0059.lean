module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0048

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AltENsmulLeft
section
open NumberField IsDedekindDomain Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.TwPerSelfDual

open Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.Th1.H

variable {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ}

theorem hv_apply' (sc : ℝ) (z w : VV ι a b) :
    HV sc z w = (sc : ℂ) * ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) := rfl

theorem embH_apply' (emb : ι → E →+* ℂ) (δ : ℂ) (x : HomE E a b) (τ : ι) (i : Fin b) (j : Fin a) :
    embH emb δ x τ i j = δ * emb τ (x (Pi.single j 1) i) := rfl

theorem hv_smul_emb (emb : ι → E →+* ℂ) (δ : ℂ) (sc : ℝ)
    (hst : ∀ (τ : ι) (x : E), emb τ (star x) = starRingEnd ℂ (emb τ x)) (r : E) (x y : HomE E a b) :
    HV sc (embH emb δ (r • x)) (embH emb δ y) = HV sc (embH emb δ x) (embH emb δ (star r • y)) := by
  rw [hv_apply', hv_apply']
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [embH_apply', LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, hst, Complex.conj_conj]
  ring

theorem embH_injective' [Nonempty ι] (emb : ι → E →+* ℂ) {δ : ℂ} (hδ : δ ≠ 0) :
    Function.Injective (embH emb δ : HomE E a b → VV ι a b) := by
  intro x y h
  obtain ⟨τ⟩ := ‹Nonempty ι›
  refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
  funext i
  have := congrFun (congrFun (congrFun h τ) i) j
  rw [embH_apply', embH_apply'] at this
  simpa using (emb τ).injective (mul_left_cancel₀ hδ this)

theorem altE_nsmul_left {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (n : ℕ) (v w : V) :
    altE H (n • v) w = altE H v (n • w) := by
  simp only [altE, map_nsmul, LinearMap.smul_apply]

section Mod

variable {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

theorem npow_smul_mem (L : Submodule (𝓞 E) W) (c n : ℕ) {y : W} (hy : y ∈ L) : ((c : E) ^ n) • y ∈ L := by
  induction n with
  | zero => simpa using hy
  | succ n ih => rw [pow_succ', mul_smul]; exact nat_smul_mem L c ih

theorem zpow_smul_mem (L : Submodule (𝓞 E) W) (c : ℕ) {k : ℤ} (hk : 0 ≤ k) {y : W} (hy : y ∈ L) :
    ((c : E) ^ k) • y ∈ L := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  rw [zpow_natCast]; exact npow_smul_mem L c n hy

end Mod

theorem twO_selfDual : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] [Nonempty ι] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ), δ ≠ 0 → (∀ (τ : ι) (x : E), emb τ (star x) = starRingEnd ℂ (emb τ x)) → 0 < c → (∀ Q, e (Formalism.L2.Col.conjPrime₂ Q) = -e Q) → (∀ Q, e Q = 1 ∨ e Q = 0 ∨ e Q = -1) → Formalism.L2.Th1.H.IsSelfDual (HV sc) (laV emb δ M) → Formalism.L2.Th1.H.IsSemiChar (HV sc) (laV emb δ M) (alV d sc) → Formalism.L2.Th1.H.IsSelfDual (HV sc) (laV emb δ (twist₂ M c e)) := by
  intro E _ _ _ ι _ _ a b emb δ d sc M c e hδ hst hc he her hSD hSC
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  have hstk : ∀ k : ℤ, star ((c : E) ^ k) = (c : E) ^ k := fun k => by rw [star_zpow₀, star_natCast]
  have hSD' : dualLat (HV sc) (laV emb δ M) = laV emb δ M := hSD
  have hdualM : ∀ z : HomE E a b, (∀ y ∈ M, ∃ m : ℤ, altE (HV sc) (embH emb δ z) (embH emb δ y) = m) → z ∈ M := by
    intro z hz
    have h1 : embH emb δ z ∈ dualLat (HV sc) (laV emb δ M) := by
      rintro _ ⟨y, hy, rfl⟩
      exact hz y hy
    rw [hSD'] at h1
    obtain ⟨z', hz', e'⟩ := h1
    rwa [← embH_injective' emb hδ e']
  have hcM : ∀ y ∈ M, (c : E) • y ∈ twist₂ M c e := by
    intro y hy
    rw [mem_twO]
    intro Q
    apply le_locP'
    rw [smul_smul, ← zpow_neg, ← zpow_add_one₀ hcE]
    apply zpow_smul_mem M c _ hy
    rcases her Q with h | h | h <;> rw [h] <;> norm_num
  show dualLat (HV sc) (laV emb δ (twist₂ M c e)) = laV emb δ (twist₂ M c e)
  apply le_antisymm
  · intro v hv
    have hcv : c • v ∈ dualLat (HV sc) (laV emb δ M) := by
      rintro _ ⟨y, hy, rfl⟩
      rw [altE_nsmul_left, ← map_nsmul]
      apply hv
      refine ⟨c • y, ?_, rfl⟩
      show c • y ∈ twist₂ M c e
      rw [← Nat.cast_smul_eq_nsmul E]
      exact hcM y hy
    rw [hSD'] at hcv
    obtain ⟨m, hm, hmv⟩ := hcv
    set x : HomE E a b := ((c : E)⁻¹) • m with hxdef
    have hxm : (c : E) • x = m := by rw [hxdef, smul_smul, mul_inv_cancel₀ hcE, one_smul]
    have hxv : embH emb δ x = v := by
      have h1 : c • embH emb δ x = c • v := by
        rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul E, hxm]; exact hmv
      have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
      rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at h1
      exact smul_right_injective _ hcC h1
    refine ⟨x, ?_, hxv⟩
    show x ∈ twist₂ M c e
    rw [mem_twO]
    intro Q
    have hc2 : ((c : 𝓞 E) ^ 2) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hc.ne')
    obtain ⟨t, ht, hwt⟩ := GlobalTheory.exists_not_mem_dvd_locally_away E (conjPrime₂ Q) _ hc2
    have hT : ∀ y ∈ M, (algebraMap (𝓞 E) E t * ((c : E) ^ e Q)⁻¹) • y ∈ twist₂ M c e := by
      intro y hy
      rw [mem_twO]
      intro Q'
      rw [smul_smul]
      by_cases hQ' : Q' = conjPrime₂ Q
      · subst hQ'
        rw [he Q, zpow_neg, inv_inv]
        have h1 : (c : E) ^ e Q * (algebraMap (𝓞 E) E t * ((c : E) ^ e Q)⁻¹) = algebraMap (𝓞 E) E t := by
          have : (c : E) ^ e Q ≠ 0 := zpow_ne_zero _ hcE
          field_simp
        rw [h1, IsScalarTower.algebraMap_smul]
        exact le_locP' M _ (M.smul_mem t hy)
      · obtain ⟨w, hw, z, hz⟩ := hwt Q' hQ'
        have hz' : algebraMap (𝓞 E) E w * algebraMap (𝓞 E) E t = (c : E) ^ 2 * algebraMap (𝓞 E) E z := by
          have := congrArg (algebraMap (𝓞 E) E) hz
          simpa using this
        have hn : (((2 - e Q' - e Q).toNat : ℕ) : ℤ) = 2 - e Q' - e Q :=
          Int.toNat_of_nonneg (by rcases her Q with h | h | h <;> rcases her Q' with h' | h' | h' <;> omega)
        refine loc_of_scal M Q' hw (ρ := (c : 𝓞 E) ^ (2 - e Q' - e Q).toNat * z) ?_ hy
        rw [map_mul, map_pow, map_natCast, ← zpow_natCast, hn, zpow_sub₀ hcE, zpow_sub₀ hcE, zpow_ofNat]
        linear_combination (((c : E) ^ e Q')⁻¹ * ((c : E) ^ e Q)⁻¹) * hz'
    refine ⟨cO E t, fun h => ht ((mem_conjP Q t).2 h), ?_⟩
    rw [← IsScalarTower.algebraMap_smul E (cO E t), smul_smul]
    apply hdualM
    intro y hy
    unfold altE
    rw [hv_smul_emb emb δ sc hst, star_mul', algebraMap_cO, star_star, star_inv₀, hstk, hxv]
    exact hv _ ⟨_, hT y hy, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    refine (_root_.GlobalTheory.CocIntLoc.integral_of_local E ι a b emb δ d sc M hδ hst hSD hSC x y fun Q =>
      ⟨(c : E) ^ e Q, zpow_ne_zero _ hcE, (mem_twO _ _ _ _).1 hx Q, ?_⟩).1
    rw [hstk]
    have := (mem_twO _ _ _ _).1 hy (conjPrime₂ Q)
    rwa [he Q, zpow_neg, inv_inv] at this

end GlobalTheory.TwPerSelfDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsColSpaceAutToLocalGLMemOpenDense
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

theorem GlobalTheory.denseGL_completion : ∀ {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k), DenseRange ι → ∀ {A : Type} [Fintype A] [DecidableEq A] {M : ℕ} (e : A ≃ Fin M) (y : GL A k) (V : Set (GL A k)), IsOpen V → y ∈ V → ∃ x : Sp E M ≃ₗ[E] Sp E M, locHom ι e x ∈ V := by
  intro E k _ _ _ _ _ ι hι A _ _ M e y V hV hy
  haveI : T2Space k := by
    rw [t2Space_iff_disjoint_nhds]
    intro a b hab
    have hne : valuation k (a - b) ≠ 0 := (Valuation.ne_zero_iff _).2 (sub_ne_zero.2 hab)
    let γ : (ValueGroupWithZero k)ˣ := Units.mk0 _ hne
    rw [Filter.disjoint_iff]
    refine ⟨{z | valuation k (z - a) < γ}, (IsValuativeTopology.mem_nhds_iff').2 ⟨γ, subset_rfl⟩,
      {z | valuation k (z - b) < γ}, (IsValuativeTopology.mem_nhds_iff').2 ⟨γ, subset_rfl⟩, ?_⟩
    rw [Set.disjoint_left]
    intro z hz1 hz2
    have h := Valuation.map_sub_lt _ (show valuation k (z - b) < γ from hz2)
      (show valuation k (z - a) < γ from hz1)
    have e : (z - b) - (z - a) = a - b := by ring
    rw [e, Units.val_mk0] at h
    exact lt_irrefl _ h
  let φ : Matrix A A k → Matrix A A k × (Matrix A A k)ᵐᵒᵖ := fun m => (m, MulOpposite.op m⁻¹)
  have hφ : ∀ g : GL A k, φ g.val = Units.embedProduct _ g := by
    intro g
    refine Prod.ext rfl ?_
    simp [φ, Matrix.coe_units_inv]
  obtain ⟨W, hW, rfl⟩ := (Units.isInducing_embedProduct (M := Matrix A A k)).isOpen_iff.1 hV
  have hdet : y.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero
  have hinv : ContinuousAt (fun m : Matrix A A k => m⁻¹) y.val := by
    have h1 : (fun m : Matrix A A k => m⁻¹) = fun m => (m.det)⁻¹ • m.adjugate := by
      funext m; rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [h1]
    exact ContinuousAt.smul ((continuousAt_inv₀ hdet).comp (continuous_id.matrix_det).continuousAt)
      (continuous_id.matrix_adjugate).continuousAt
  have hφc : ContinuousAt φ y.val :=
    ContinuousAt.prodMk continuousAt_id (MulOpposite.continuous_op.continuousAt.comp hinv)
  have hU : φ ⁻¹' W ∩ {m : Matrix A A k | m.det ≠ 0} ∈ nhds y.val := by
    refine Filter.inter_mem (hφc.preimage_mem_nhds (hW.mem_nhds ?_)) ?_
    · rw [hφ]; exact hy
    · exact (isOpen_compl_singleton.preimage (continuous_id.matrix_det)).mem_nhds hdet
  have hD : DenseRange (fun m : Matrix A A E => m.map ι) :=
    DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => hι))
  obtain ⟨_, ⟨m', rfl⟩, hm'W, hm'd⟩ := Dense.inter_nhds_nonempty hD hU
  have hm'u : IsUnit m'.det := by
    refine isUnit_iff_ne_zero.2 ?_
    intro h0
    apply hm'd
    show (m'.map ι).det = 0
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  let n : Matrix (Fin M) (Fin M) E := m'.submatrix e.symm e.symm
  have hn : IsUnit n.det := by
    simpa [n, Matrix.det_submatrix_equiv_self] using hm'u
  refine ⟨Matrix.toLinearEquiv' n (Matrix.invertibleOfIsUnitDet n hn), ?_⟩
  show Units.embedProduct _ _ ∈ W
  rw [← hφ, locHom_val, GlobalTheory.SymBridge.toLoc_eq_map_toMatrix']
  have h2 : LinearMap.toMatrix' (Matrix.toLinearEquiv' n (Matrix.invertibleOfIsUnitDet n hn)).toLinearMap = n := by
    exact LinearMap.toMatrix'_toLin' n
  rw [h2]
  have h3 : n.submatrix e e = m' := by
    ext i j; simp [n]
  rw [h3]
  exact hm'W
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsN1LocalHomMemOpen
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

noncomputable section
namespace GlobalTheory.VolBridge.NormOneIdeleAutomorphisms

variable {E : Type} [Field E] {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ}

def autOf (e : A ⊕ Fin c ≃ Fin (M + c')) (g : GL (A ⊕ Fin c) E) : (Fin (M + c') → E) ≃ₗ[E] (Fin (M + c') → E) :=
  LinearEquiv.ofLinear (Matrix.toLin' (g.val.submatrix e.symm e.symm)) (Matrix.toLin' ((g⁻¹).val.submatrix e.symm e.symm))
    (by rw [← Matrix.toLin'_mul, Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, Matrix.submatrix_mul_equiv, Units.inv_mul, Matrix.submatrix_one_equiv, Matrix.toLin'_one])

theorem autOf_apply (e : A ⊕ Fin c ≃ Fin (M + c')) (g : GL (A ⊕ Fin c) E) (v : Fin (M + c') → E) :
    autOf e g v = (g.val.submatrix e.symm e.symm).mulVec v := rfl

theorem autOf_inv_apply (e : A ⊕ Fin c ≃ Fin (M + c')) (g : GL (A ⊕ Fin c) E) (v : Fin (M + c') → E) :
    (autOf e g)⁻¹ v = ((g⁻¹).val.submatrix e.symm e.symm).mulVec v := rfl

theorem lev_symm (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val)
    (l : Fin (M + c')) : lev (n := A) (c := c) 1 (e.symm l) = if l.val < M then 1 else l.val - M + 1 := by
  rcases hm : e.symm l with a | i
  · have h1 : l = e (Sum.inl a) := by rw [← hm]; simp
    have := eX_lt e hcc he a
    rw [← h1] at this
    simp [lev, this]
  · have h1 : l = e (Sum.inr i) := by rw [← hm]; simp
    have := he i
    rw [← h1] at this
    simp [lev, this]

theorem mulVec_fix (e : A ⊕ Fin c ≃ Fin (M + c')) (m : Matrix (A ⊕ Fin c) (A ⊕ Fin c) E)
    (hm : ∀ r s, lev 1 s ≤ lev 1 r → m r s = (1 : Matrix (A ⊕ Fin c) (A ⊕ Fin c) E) r s) (v : Fin (M + c') → E)
    (l : Fin (M + c')) (hv : ∀ j, v j ≠ 0 → lev (n := A) (c := c) 1 (e.symm j) ≤ lev 1 (e.symm l)) :
    (m.submatrix e.symm e.symm).mulVec v l = v l := by
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
  rw [Finset.sum_eq_single l]
  · rw [hm _ _ le_rfl, Matrix.one_apply_eq, one_mul]
  · intro j _ hj
    by_cases h0 : v j = 0
    · rw [h0, mul_zero]
    · rw [hm _ _ (hv j h0), Matrix.one_apply_ne (fun h => hj (e.symm.injective h).symm), zero_mul]
  · simp

theorem mem_normOneIdeles (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val)
    (g : GL (A ⊕ Fin c) E) (hg : g ∈ N E A c 1) : autOf e g ∈ Loc.N1 E M c' := by
  have hL := lev_symm e hcc he
  have key : ∀ g : GL (A ⊕ Fin c) E, g ∈ N E A c 1 → ∀ (v : Fin (M + c') → E) (l : Fin (M + c')),
      (∀ j, v j ≠ 0 → lev (n := A) (c := c) 1 (e.symm j) ≤ lev 1 (e.symm l)) →
      (g.val.submatrix e.symm e.symm).mulVec v l = v l := fun g hg v l hv =>
    mulVec_fix e g.val (Model.mem_N_iff.1 hg) v l hv
  have hR : ∀ g : GL (A ⊕ Fin c) E, g ∈ N E A c 1 → ∀ r : (Fin (M + c') → E) ≃ₗ[E] (Fin (M + c') → E),
      (∀ v, r v = (g.val.submatrix e.symm e.symm).mulVec v) → Loc.R1cond E M c' r := by
    intro g hg r hr
    refine ⟨fun i v hv => ?_, ?_, fun i => ?_⟩
    · intro l hl
      simp only [Set.mem_setOf_eq, not_lt] at hl
      rw [hr, key g hg v l ?_]
      · exact hv l (by simpa using hl)
      · intro j hj
        have : j.val < M + i := by
          by_contra h
          exact hj (hv j (by simpa using h))
        rw [hL, hL]; split_ifs <;> omega
    · funext l
      rw [hr, key g hg _ l]
      intro j hj
      have : j.val = M := by
        by_contra h; exact hj (by simp [Loc.eN, h])
      rw [hL, hL]; split_ifs <;> omega
    · intro l hl
      simp only [Set.mem_setOf_eq, not_lt] at hl
      rw [Pi.sub_apply, hr, key g hg _ l, sub_self]
      intro j hj
      have : j.val = M + i := by
        by_contra h; exact hj (by simp [Loc.eN, h])
      rw [hL, hL]; split_ifs <;> omega
  refine ⟨⟨hR g hg _ (autOf_apply e g), hR g⁻¹ (inv_mem hg) _ (autOf_inv_apply e g)⟩, fun x => ?_⟩
  funext l
  rw [autOf_apply, key g hg _ l]
  intro j hj
  have : j.val < M := by
    by_contra h
    exact hj (by simp [Loc.inX, h])
  rw [hL, hL]; split_ifs <;> omega

theorem locHom_autOf {k : Type} [Field k] (ι : E →+* k) (e : A ⊕ Fin c ≃ Fin (M + c')) (g : GL (A ⊕ Fin c) E) :
    (locHom ι e (autOf e g)).val = g.val.map ι := by
  rw [locHom_val]
  ext i j
  simp [GlobalTheory.SymBridge.toLoc, autOf_apply, Matrix.mulVec_single_one]

end GlobalTheory.VolBridge.NormOneIdeleAutomorphisms

namespace GlobalTheory.VolBridge
open NormOneIdeleAutomorphisms

theorem exists_N1_local_hom_mem_open : ∀ {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k), DenseRange ι → ∀ {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ} (e : A ⊕ Fin c ≃ Fin (M + c')), c' = c → (∀ i : Fin c, (e (Sum.inr i)).val = M + i.val) → ∀ u ∈ N k A c 1, ∀ V : Set (GL (A ⊕ Fin c) k), IsOpen V → u ∈ V → ∃ x ∈ Loc.N1 E M c', locHom ι e x ∈ V := by
  intro E k _ _ _ _ _ ι hι A _ _ M c c' e hcc he u hu V hV huV
  let f : (VolN.Ix A c 1 → k) → GL (A ⊕ Fin c) k := fun a => ((Model.mkNel 1 a : N k A c 1) : GL (A ⊕ Fin c) k)
  have hf : Continuous f := continuous_subtype_val.comp (VolN.continuous_mkNel 1)
  have hW : IsOpen (f ⁻¹' V) := hV.preimage hf
  have h0 : VolN.co 1 ⟨u, hu⟩ ∈ f ⁻¹' V := by
    show ((Model.mkNel 1 (VolN.co 1 ⟨u, hu⟩) : N k A c 1) : GL (A ⊕ Fin c) k) ∈ V
    rw [VolN.mkNel_co]; exact huV
  have hD : DenseRange (Pi.map fun (_ : VolN.Ix A c 1) => (ι : E → k)) := DenseRange.piMap fun _ => hι
  obtain ⟨b, hb⟩ := hD.exists_mem_open hW ⟨_, h0⟩
  refine ⟨autOf e ((Model.mkNel 1 b : N E A c 1) : GL (A ⊕ Fin c) E), mem_normOneIdeles e hcc he _ (Model.mkNel 1 b).2, ?_⟩
  have : locHom ι e (autOf e ((Model.mkNel 1 b : N E A c 1) : GL (A ⊕ Fin c) E)) = f (Pi.map (fun _ => (ι : E → k)) b) := by
    apply Units.ext
    rw [locHom_autOf]
    show _ = ((Model.mkNel 1 _ : N k A c 1) : GL (A ⊕ Fin c) k).val
    rw [VolN.val_mkNel, VolN.val_mkNel]
    ext r s
    simp only [Matrix.map_apply, Matrix.add_apply, map_add (f := _), VolN.ext0, Matrix.of_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [this]; exact hb

end GlobalTheory.VolBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPowHeckeCharUnramifiedEverywhere
section
open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.Corev.UnrPow

theorem exists_pow_unrAt : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L),
    ∃ N : ℕ, 0 < N ∧ ∀ v : HeightOneSpectrum (𝓞 L), (χ ^ N).UnrAt v := by
  intro L _ _ χ
  obtain ⟨hfin, hlev⟩ := GlobalTheory.Mem.UnrAe.unr_ae_and_level L χ
  have hm : ∀ v, ∃ m : ℕ, 0 < m ∧ ∀ x, IsUnitAt v x → χ.loc v x ^ m = 1 := by
    intro v
    obtain ⟨n, hn⟩ := hlev v
    obtain ⟨m, hm, hx⟩ := GlobalTheory.Mem.FinOrder.exists_pow_congr v n
    refine ⟨m, hm, fun x hu => ?_⟩
    rw [← map_pow]
    exact hn _ (GlobalTheory.Mem.UnrAe.isUnitAt_pow hu m) (hx x hu)
  choose m hm0 hm using hm
  refine ⟨∏ v ∈ hfin.toFinset, m v, Finset.prod_pos fun v _ => hm0 v, fun v x hx => ?_⟩
  show χ.loc v x ^ (∏ v ∈ hfin.toFinset, m v) = 1
  by_cases hv : χ.UnrAt v
  · rw [hv x hx, one_pow]
  · obtain ⟨d, hd⟩ : m v ∣ ∏ v ∈ hfin.toFinset, m v := Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.2 hv)
    rw [hd, pow_mul, hm v x hx, one_pow]

end GlobalTheory.Corev.UnrPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarOpenSubgroupVolumeInvEqRelIndex
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

namespace GlobalTheory.OpenVolIndex

theorem measure_toReal_inv_eq_relIndex : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] (H L : Subgroup G), H ≤ L → IsOpen (H : Set G) → IsCompact (L : Set G) → μ (L : Set G) = 1 → (μ (H : Set G)).toReal⁻¹ = (H.relIndex L : ℝ) := by
  intro G _ _ _ _ _ μ _ H L hHL hH hL hμL
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hHo : IsOpen ((H.subgroupOf L : Subgroup L) : Set L) :=
    hH.preimage continuous_subtype_val
  haveI : Finite (L ⧸ H.subgroupOf L) := Subgroup.quotient_finite_of_isOpen _ hHo
  haveI : (H.subgroupOf L).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have key := GlobalTheory.BaseModule.relIndex_mul_measure' H L hHL hH.measurableSet μ
  rw [hμL] at key
  have htop : μ (H : Set G) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [hμL]; exact ENNReal.one_ne_top) (measure_mono hHL)
  have hr : (H.relIndex L : ℝ) * (μ (H : Set G)).toReal = 1 := by
    have := congrArg ENNReal.toReal key
    simpa [ENNReal.toReal_mul] using this
  exact (eq_inv_of_mul_eq_one_left hr).symm

end GlobalTheory.OpenVolIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarVolumeRatioCompactEqRelIndexRatio
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge
open scoped Pointwise ENNReal

namespace GlobalTheory.VolRatio

theorem relIndex_mul_measure_sub {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (H L : Subgroup G) (hHL : H ≤ L) [(H.subgroupOf L).FiniteIndex]
    (hH : MeasurableSet (H : Set G)) (μ : Measure G) [μ.IsMulLeftInvariant] :
    (H.relIndex L : ENNReal) * μ H = μ L := by
  obtain ⟨s, hs, -⟩ := (H.subgroupOf L).exists_isComplement_left 1
  have hs' : Finite s := hs.finite_left_iff.mpr inferInstance
  have hU : (⋃ a : s, (a.val : L) • (H : Set G)) = (L : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_smul_set, SetLike.mem_coe]
    constructor
    · rintro ⟨a, h, hh, rfl⟩
      exact L.mul_mem a.val.2 (hHL hh)
    · intro hx
      obtain ⟨⟨b, h⟩, hbh, -⟩ := hs.existsUnique ⟨x, hx⟩
      refine ⟨b, (h.val : G), Subgroup.mem_subgroupOf.mp h.2, ?_⟩
      have := congrArg Subtype.val hbh
      exact this
  have hdisj : Pairwise (Function.onFun Disjoint fun a : s => (a.val : L) • (H : Set G)) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨h1, hh1, rfl⟩ ⟨h2, hh2, he⟩
    apply hab
    have hh1' : (⟨h1, hHL hh1⟩ : L) ∈ H.subgroupOf L := Subgroup.mem_subgroupOf.mpr hh1
    have hh2' : (⟨h2, hHL hh2⟩ : L) ∈ H.subgroupOf L := Subgroup.mem_subgroupOf.mpr hh2
    have e : (a.val : L) * ⟨h1, hHL hh1⟩ = (b.val : L) * ⟨h2, hHL hh2⟩ := Subtype.ext he.symm
    have := (hs.existsUnique ((a.val : L) * ⟨h1, hHL hh1⟩)).unique
      (y₁ := (a, ⟨_, hh1'⟩)) (y₂ := (b, ⟨_, hh2'⟩)) rfl e.symm
    exact congrArg Prod.fst this
  calc (H.relIndex L : ENNReal) * μ H = ∑' a : s, μ ((a.val : L) • (H : Set G)) := by
        simp [measure_smul, hs.encard_left, Subgroup.relIndex]
    _ = μ (⋃ a : s, (a.val : L) • (H : Set G)) :=
        (measure_iUnion hdisj fun a => hH.const_smul _).symm
    _ = μ L := by rw [hU]

theorem vol_ratio : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] (A B : Subgroup G), IsOpen ((A ⊓ B : Subgroup G) : Set G) → IsCompact (A : Set G) → IsCompact (B : Set G) → (μ (A : Set G)).toReal / (μ (B : Set G)).toReal = (B.relIndex A : ℝ) / (A.relIndex B : ℝ) := by
  intro G _ _ _ _ _ μ _ A B hC hA hB
  have hCA : A ⊓ B ≤ A := inf_le_left
  have hCB : A ⊓ B ≤ B := inf_le_right
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  haveI : CompactSpace B := isCompact_iff_compactSpace.mp hB
  haveI : ((A ⊓ B).subgroupOf A).FiniteIndex := by
    haveI := Subgroup.quotient_finite_of_isOpen ((A ⊓ B).subgroupOf A)
      (hC.preimage continuous_subtype_val)
    exact Subgroup.finiteIndex_of_finite_quotient
  haveI : ((A ⊓ B).subgroupOf B).FiniteIndex := by
    haveI := Subgroup.quotient_finite_of_isOpen ((A ⊓ B).subgroupOf B)
      (hC.preimage continuous_subtype_val)
    exact Subgroup.finiteIndex_of_finite_quotient
  have hCm : MeasurableSet ((A ⊓ B : Subgroup G) : Set G) := hC.measurableSet
  have h1 := relIndex_mul_measure_sub (A ⊓ B) A hCA hCm μ
  have h2 := relIndex_mul_measure_sub (A ⊓ B) B hCB hCm μ
  rw [Subgroup.inf_relIndex_left] at h1
  rw [Subgroup.inf_relIndex_right] at h2
  have hpos : 0 < μ ((A ⊓ B : Subgroup G) : Set G) := hC.measure_pos μ ⟨1, (A ⊓ B).one_mem⟩
  have hfin : μ ((A ⊓ B : Subgroup G) : Set G) < ⊤ :=
    lt_of_le_of_lt (measure_mono hCA) hA.measure_lt_top
  have hr : 0 < (μ ((A ⊓ B : Subgroup G) : Set G)).toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  rw [← h1, ← h2, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast, mul_div_mul_right _ _ hr.ne']

end GlobalTheory.VolRatio
end

