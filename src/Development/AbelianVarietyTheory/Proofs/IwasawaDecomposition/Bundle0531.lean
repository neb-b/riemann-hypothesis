module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MajorantHarnackHolomorphicHalfPlane
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PointwiseNormInvarianceHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.BotMulVecExt
public import Formalism.LocalToGlobal.ProjectiveLattices.UnifFrDet
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCastMemNonunitsOfInduces
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad

theorem natCast_mem_nonunits_of_induces (D : D7) (p : ℕ) [hp : Fact p.Prime] (la : PlL D p) (W : ValuationSubring ℂ)
    (h : ∀ x : D.what₂.LL, D.what₂.embLL x ∈ W ↔ la.1.valuation D.what₂.LL x ≤ 1) : (p : ℂ) ∈ W.nonunits := by
  have hlt : la.1.valuation D.what₂.LL (p : D.what₂.LL) < 1 := by
    have := (la.1.valuation_lt_one_iff_mem (K := D.what₂.LL) ((p : ℕ) : 𝓞 D.what₂.LL)).2 la.2
    simpa using this
  have hp0 : (p : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hv0 : 0 < la.1.valuation D.what₂.LL (p : D.what₂.LL) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hp0)
  have hnot : ((p : ℂ))⁻¹ ∉ W := by
    intro hm
    have h1 : D.what₂.embLL ((p : D.what₂.LL)⁻¹) ∈ W := by simpa using hm
    have h2 := (h _).1 h1
    rw [map_inv₀, inv_le_one₀ hv0] at h2
    exact absurd hlt (not_lt.2 h2)
  rw [ValuationSubring.mem_nonunits_iff]
  by_contra hc
  apply hnot
  rw [← ValuationSubring.valuation_le_one_iff, map_inv₀]
  exact inv_le_one_of_one_le₀ (not_lt.1 hc)

theorem placeW_spec (D : D7) (p : ℕ) [Fact p.Prime] (la : PlL D p) (jc : DV.KW p →+* ℂ) (h : JcPin D p la jc) :
    (∀ x : D.what₂.LL, D.what₂.embLL x ∈ placeW D p la jc ↔ la.1.valuation D.what₂.LL x ≤ 1) ∧
    ∀ a : DV.KW p, jc a ∈ placeW D p la jc ↔
      a ∈ (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)).range :=
  Classical.epsilon_spec h

theorem placeW_over : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (la : PlL D p) (jc : DV.KW p →+* ℂ), JcPin D p la jc → (p : ℂ) ∈ (placeW D p la jc).nonunits ∧ ∀ x : D.what₂.LL, D.what₂.embLL x ∈ placeW D p la jc ↔ la.1.valuation D.what₂.LL x ≤ 1 :=
  fun D p _ la jc h =>
    ⟨natCast_mem_nonunits_of_induces D p la _ (placeW_spec D p la jc h).1, (placeW_spec D p la jc h).1⟩

end GlobalTheory.ShFam.Pad
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAdaptedOfIntStep
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag.AdaptedOfStep

theorem eq_zero_of_dense {X : Scheme.{0}} [IsReduced X] {D : Set X} (hD : Dense D) {U : X.Opens} (f : Γ(X, U))
    (h : ∀ (K : Type) [Field K] (w : Sp K ⟶ X) (hw : ⊤ ≤ w ⁻¹ᵁ U), w (IsLocalRing.closedPoint K) ∈ D →
      ev w U hw f = 0) : f = 0 := by
  refine (basicOpen_eq_bot_iff f).1 ?_
  by_contra hne
  obtain ⟨x, hx, hxD⟩ := hD.inter_open_nonempty _ (X.basicOpen f).isOpen
    (((X.basicOpen f).ne_bot_iff_nonempty).1 hne)
  let w : Sp (X.residueField x) ⟶ X := X.fromSpecResidueField x
  have hr : ∀ p, w p = x := fun p => Scheme.fromSpecResidueField_apply x p
  have hb : ⊤ ≤ w ⁻¹ᵁ X.basicOpen f := fun p _ => show w p ∈ X.basicOpen f by rw [hr]; exact hx
  have hw : ⊤ ≤ w ⁻¹ᵁ U := le_preimage_mono (X.basicOpen_le f) hb
  have h0 := h _ w hw ((hr _).symm ▸ hxD)
  have hu : IsUnit (resG X (X.basicOpen_le f) f) := RingedSpace.isUnit_res_basicOpen X.toRingedSpace f
  have := hu.map (ev w _ hb)
  rw [ev_res w _ hb hw, h0] at this
  exact not_isUnit_zero this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F} {M : Model Xo c V.subtype}
  {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ} {A : Atlas M π ty} {σ : E →+* ℂ} {k : ℕ}

variable {U U' : X.Opens} {hU : IsAffineOpen U} {hU' : IsAffineOpen U'} {m m' : ℕ}
  {b : Module.Basis (Fin k ⊕ Fin m) Γ(X, U) (TanM (tau hU ≫ π) M.t.G)}
  {b' : Module.Basis (Fin k ⊕ Fin m') Γ(X, U') (TanM (tau hU' ≫ π) M.t.G)}


end GlobalTheory.DRFlag.AdaptedOfStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFrameLimitsOfOrbit
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt hermC bchar)
open scoped Matrix

namespace GlobalTheory.OrbitNfac

theorem span_bound {α : Type} (l : Filter α) {n m : ℕ} (L : α → Fin n → Fin m → ℂ) (L0 : Fin n → Fin m → ℂ)
    (hL : ∀ j i, Tendsto (fun w => L w j i) l (𝓝 (L0 j i))) (hs : Submodule.span ℂ (Set.range L0) = ⊤) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ w in l, ∀ (ℓ : Fin m → ℂ) (k : Fin m), ‖ℓ k‖ ≤ K * ∑ j, ‖∑ i, ℓ i * L w j i‖ := by
  classical
  have hA : ∀ k : Fin m, ∃ A : Fin n → ℂ, ∑ j, A j • L0 j = Pi.single k 1 := fun k =>
    (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hs ▸ Submodule.mem_top)
  choose A hA using hA
  set K : ℝ := ∑ k, ∑ j, ‖A k j‖ with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hAK : ∀ k j, ‖A k j‖ ≤ K := fun k j =>
    (Finset.single_le_sum (f := fun j => ‖A k j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun k => ∑ j, ‖A k j‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k))
  have ht : Tendsto (fun w => K * ∑ j, ∑ i, ‖L0 j i - L w j i‖) l (𝓝 (K * ∑ j : Fin n, ∑ i : Fin m, (0 : ℝ))) := by
    refine Tendsto.const_mul _ (tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun i _ => ?_)
    have := ((tendsto_const_nhds (x := L0 j i)).sub (hL j i)).norm
    simpa using this
  simp only [Finset.sum_const_zero, mul_zero] at ht
  refine ⟨2 * K, by positivity, ?_⟩
  filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with w hw ℓ k
  set S : ℝ := ∑ j, ‖∑ i, ℓ i * L w j i‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have key : ∀ k, ‖ℓ k‖ ≤ K * S + ‖ℓ‖ / 2 := by
    intro k
    have e1 : ℓ k = ∑ j, A k j * ((∑ i, ℓ i * L w j i) + ∑ i, ℓ i * (L0 j i - L w j i)) := by
      have e2 : ℓ k = ∑ i, ℓ i * (∑ j, A k j • L0 j) i := by
        rw [hA k]; simp [Pi.single_apply]
      rw [e2]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    have e3 : ∀ j, ‖A k j * ((∑ i, ℓ i * L w j i) + ∑ i, ℓ i * (L0 j i - L w j i))‖ ≤
        K * ‖∑ i, ℓ i * L w j i‖ + ‖ℓ‖ * (K * ∑ i, ‖L0 j i - L w j i‖) := by
      intro j
      have h1 : ‖∑ i, ℓ i * (L0 j i - L w j i)‖ ≤ ‖ℓ‖ * ∑ i, ‖L0 j i - L w j i‖ := by
        rw [Finset.mul_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (norm_le_pi_norm ℓ i) (norm_nonneg _)
      rw [norm_mul]
      calc _ ≤ K * (‖∑ i, ℓ i * L w j i‖ + ‖ℓ‖ * ∑ i, ‖L0 j i - L w j i‖) :=
            mul_le_mul (hAK k j) ((norm_add_le _ _).trans (by linarith)) (norm_nonneg _) hK0
        _ = _ := by ring
    calc ‖ℓ k‖ ≤ ∑ j, (K * ‖∑ i, ℓ i * L w j i‖ + ‖ℓ‖ * (K * ∑ i, ‖L0 j i - L w j i‖)) := by
          rw [e1]; exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => e3 j)
      _ = K * S + ‖ℓ‖ * (K * ∑ j, ∑ i, ‖L0 j i - L w j i‖) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ K * S + ‖ℓ‖ / 2 := by nlinarith [norm_nonneg ℓ]
  have h2 : ‖ℓ‖ ≤ K * S + ‖ℓ‖ / 2 := (pi_norm_le_iff_of_nonneg (by positivity)).2 key
  have := norm_le_pi_norm ℓ k
  linarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (X : Data E N)

theorem coord_le {x b : Frame X.Ψ N} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ N) (ho : X.IsOrtho (rmul x b)) (τ : X.Ψ)
    (u : Fin N → ℂ) (i : Fin N) : ‖((mat (rmul x b) τ)⁻¹ *ᵥ u) i‖ ≤ 1 + X.maj x τ u := by
  have hy := ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X hx hb
  have h := UnipMove.GraphH.maj_ortho X ho τ ((mat (rmul x b) τ)⁻¹ *ᵥ u)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit (hy τ).1), Matrix.one_mulVec,
    GlobalTheory.MajInv.maj_rmul X hx hb] at h
  have h2 : ‖((mat (rmul x b) τ)⁻¹ *ᵥ u) i‖ ^ 2 ≤ X.maj x τ u := by
    rw [h]
    exact Finset.single_le_sum (f := fun j => ‖((mat (rmul x b) τ)⁻¹ *ᵥ u) j‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
  nlinarith [sq_nonneg (‖((mat (rmul x b) τ)⁻¹ *ᵥ u) i‖ - 1), sq_nonneg ‖((mat (rmul x b) τ)⁻¹ *ᵥ u) i‖]

theorem inv_diag {b : Frame X.Ψ N} (hb : b ∈ Bor X.Ψ N) (τ : X.Ψ) (i : Fin N) :
    (mat b τ)⁻¹ i i = (b τ i i)⁻¹ := by
  have hi := (ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.invF_mem X hb τ).2
  have h := congrFun (congrFun (Matrix.nonsing_inv_mul (mat b τ) (Ne.isUnit (hb τ).1)) i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single i] at h
  · exact eq_inv_of_mul_eq_one_left h
  · intro a _ ha
    rcases lt_or_gt_of_ne ha with h1 | h1
    · have : (mat b τ)⁻¹ i a = 0 := hi i a h1
      rw [this, zero_mul]
    · have : mat b τ a i = 0 := (hb τ).2 a i h1
      rw [this, mul_zero]
  · simp

theorem quot_bound {x b : Frame X.Ψ N} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ N) (ho : X.IsOrtho (rmul x b)) (τ : X.Ψ)
    {n : ℕ} (v : Fin n → Fin N → E) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ (ℓ : Fin (N - X.p0) → ℂ) (k : Fin (N - X.p0)), ‖ℓ k‖ ≤ K * ∑ j, ‖∑ i, ℓ i * perFr X x (v j) τ.1 i‖)
    (i : Fin N) (hi : X.p0 ≤ i) : ‖b τ i i‖⁻¹ ≤ K * ∑ j, (1 + X.maj x τ (Data.emb τ.1 (v j))) := by
  have hinv := (ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.invF_mem X hb τ).2
  let e : Fin (N - X.p0) → Fin N := fun k => ⟨X.p0 + k, by have := k.2; omega⟩
  have h1 := h (fun k => (mat b τ)⁻¹ i (e k)) ⟨i - X.p0, by have := i.2; omega⟩
  have he : e ⟨i - X.p0, by have := i.2; omega⟩ = i := Fin.ext (by simp only [e]; omega)
  simp only [he] at h1
  rw [inv_diag X hb, norm_inv] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hK)
  have e1 : ∑ k : Fin (N - X.p0), (mat b τ)⁻¹ i (e k) * perFr X x (v j) τ.1 k =
      ((mat (rmul x b) τ)⁻¹ *ᵥ Data.emb τ.1 (v j)) i := by
    have e2 : mat (rmul x b) τ = mat x τ * mat b τ := rfl
    rw [e2, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec]
    show _ = ∑ a, (mat b τ)⁻¹ i a * ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 (v j)) a
    refine Finset.sum_of_injOn e (fun a _ c _ hac => Fin.ext ?_)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) (fun a _ ha => ?_) (fun k _ => ?_)
    · have := congrArg Fin.val hac
      simp only [e] at this
      omega
    · have ha' : (a : ℕ) < X.p0 := by
        by_contra hc
        exact ha ⟨⟨a - X.p0, by have := a.2; omega⟩, by simp, Fin.ext (by simp only [e]; omega)⟩
      have : (mat b τ)⁻¹ i a = 0 := hinv i a (by show (a : ℕ) < i; omega)
      rw [this, zero_mul]
    · rw [perFr_pos X x (v j) τ k (e k).2]
  rw [e1]
  exact coord_le X hx hb ho τ _ i

theorem fil_bound {x b : Frame X.Ψ N} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ N) (ho : X.IsOrtho (rmul x b)) (τ : X.Ψ)
    {n : ℕ} (v : Fin n → Fin N → E) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ (ℓ : Fin X.p0 → ℂ) (k : Fin X.p0), ‖ℓ k‖ ≤ K * ∑ j, ‖∑ i, ℓ i * perFr X x (v j) (conjEmb τ.1) i‖)
    (i : Fin N) (hi : (i : ℕ) < X.p0) : ‖b τ i i‖ ≤ K * ∑ j, (1 + X.maj x τ (Data.emb τ.1 (v j))) := by
  have hp := X.p0_le
  have hy := ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X hx hb
  let e : Fin X.p0 → Fin N := fun k => ⟨X.p0 - 1 - k, by have := k.2; omega⟩
  have h1 := h (fun k => b τ (e k) i) ⟨X.p0 - 1 - i, by omega⟩
  have he : e ⟨X.p0 - 1 - i, by omega⟩ = i := Fin.ext (by simp only [e]; omega)
  simp only [he] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hK)
  have hc : conjEmb τ.1 ∉ X.Ψ := (X.cmType τ.1).1 τ.2
  have e1 : ∑ k : Fin X.p0, b τ (e k) i * perFr X x (v j) (conjEmb τ.1) k =
      hermC τ.1 X.Gm (col (mat (rmul x b) τ) i) (Data.emb τ.1 (v j)) := by
    have e2 : mat (rmul x b) τ = mat x τ * mat b τ := rfl
    rw [e2, UnipMove.GraphH.col_mul, Data.mulVec_eq_sum_col, ReciprocityTheory.ChartRestriction.G.FD.hermC_sum_left]
    refine Finset.sum_of_injOn e (fun a _ c _ hac => Fin.ext ?_)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) (fun a _ ha => ?_) (fun k _ => ?_)
    · have := congrArg Fin.val hac
      simp only [e] at this
      have := a.2
      have := c.2
      omega
    · have ha' : X.p0 ≤ (a : ℕ) := by
        by_contra hc
        exact ha ⟨⟨X.p0 - 1 - a, by omega⟩, by simp, Fin.ext (by simp only [e]; omega)⟩
      have : col (mat b τ) i a = 0 := (hb τ).2 a i (by show (i : ℕ) < a; omega)
      rw [ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_left, this, zero_mul]
    · rw [ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_left,
        perFr_neg X x (v j) (conjEmb τ.1) hc τ (Formalism.L2.Pj.conjEmb_conjEmb τ.1).symm k (e k).2]
      rfl
  rw [e1]
  refine le_trans (le_of_eq ?_) (coord_le X hx hb ho τ (Data.emb τ.1 (v j)) i)
  set c := (mat (rmul x b) τ)⁻¹ *ᵥ Data.emb τ.1 (v j) with hcdef
  have hv : Data.emb τ.1 (v j) = mat (rmul x b) τ *ᵥ c := by
    rw [hcdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit (hy τ).1), Matrix.one_mulVec]
  have hg : ∀ a, hermC τ.1 X.Gm (col (mat (rmul x b) τ) i) (col (mat (rmul x b) τ) a) = if i = a then 1 else 0 := by
    intro a
    have := congrFun (congrFun (ho τ) i) a
    simpa [ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.diagonal_apply, ReciprocityTheory.ChartRestriction.G.FD.sgn, hi] using this
  rw [hv, Data.mulVec_eq_sum_col, ReciprocityTheory.ChartRestriction.G.FD.hermC_sum_right]
  simp_rw [ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_right, hg]
  simp

theorem nfac_ortho {y : Frame X.Ψ N} (ho : X.IsOrtho y) (la : Wt X.Ψ N) : X.nfac la y = 1 := by
  have h : ∀ τ i, ‖dmin X.Gm y τ i‖ = 1 := by
    intro τ i
    unfold dmin
    rw [ho τ, ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.lminor_diagonal, norm_prod]
    refine Finset.prod_eq_one fun j _ => ?_
    rcases ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.sgn_sq X.p0 (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) with h | h <;> rw [h] <;> simp
  unfold Data.nfac
  simp [h]

theorem nfac_shift {T : ℝ} {M : ℕ} {γ : GL (Fin N) E} {x : ℂ → Frame X.Ψ N} (h : IsOrbit X T M γ x) (la : Wt X.Ψ N)
    (k : ℤ) : ∀ w : ℂ, T < w.im → X.nfac la (x (w + k * M)) = X.nfac la (x w) := by
  obtain ⟨-, hγ, -, hd, hs⟩ := h
  have one : ∀ w : ℂ, T < w.im → X.nfac la (x (w + M)) = X.nfac la (x w) := by
    intro w hw
    obtain ⟨b, hb, hb1, e⟩ := hs w hw
    rw [e, ReciprocityTheory.ChartRestriction.G.AR.Inst.normFactor_rightBorel_holds N X la _ (GlobalTheory.MajInv.lact_mem_dom X (X.Γ_stab γ hγ) (hd w hw)) b hb,
      ReciprocityTheory.ChartRestriction.G.AR.Inst.normFactor_leftAction_holds N X la γ hγ _ (hd w hw)]
    simp [bchar, hb1]
  induction k using Int.induction_on with
  | zero => intro w _; simp
  | succ k ih =>
    intro w hw
    rw [← ih w hw, ← one (w + ((k : ℤ) : ℂ) * M) (by simpa using hw)]
    congr 2
    push_cast
    ring
  | pred k ih =>
    intro w hw
    rw [← ih w hw, ← one (w + ((-(k : ℤ) - 1 : ℤ) : ℂ) * M) (by simpa using hw)]
    congr 2
    push_cast
    ring

theorem maj_strip {T : ℝ} {x : ℂ → Frame X.Ψ N} (hx : DifferentiableOn ℂ x {w | T < w.im})
    (hd : ∀ w : ℂ, T < w.im → x w ∈ X.dom) (M : ℝ) (τ : X.Ψ) (u : Fin N → ℂ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ w : ℂ, T + 1 ≤ w.im → 1 ≤ w.im → |w.re| ≤ M → 1 + X.maj (x w) τ u ≤ D * w.im ^ 2 := by
  set w0 : ℂ := ⟨0, T + 1⟩ with hw0
  have h0 : T < w0.im := by simp [hw0]
  have hm : 0 ≤ X.maj (x w0) τ u := ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_nonneg X (hd w0 h0) τ u
  refine ⟨1 + (2 + M ^ 2 + (1 + |T + 1|) ^ 2) * X.maj (x w0) τ u, by positivity, fun w h1 h2 h3 => ?_⟩
  have h := _root_.GlobalTheory.maj_harnack E N X T x hx hd w0 w h0 (by linarith) τ u
  have e0 : w0.im - T = 1 := by simp [hw0]
  rw [e0, one_mul] at h
  have e1 : ‖w0 - w‖ ^ 2 = w.re ^ 2 + (T + 1 - w.im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [hw0]
    ring
  have hs : 1 ≤ w.im ^ 2 := by nlinarith
  have e2 : w.re ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  have e3 : (T + 1 - w.im) ^ 2 ≤ ((1 + |T + 1|) * w.im) ^ 2 := by
    have a1 := le_abs_self (T + 1)
    have a2 := neg_abs_le (T + 1)
    have a3 := abs_nonneg (T + 1)
    exact sq_le_sq' (by nlinarith) (by nlinarith)
  have e4 : ‖w0 - w‖ ^ 2 / (w.im - T) ≤ ‖w0 - w‖ ^ 2 := div_le_self (sq_nonneg _) (by linarith)
  have e5 : 2 + ‖w0 - w‖ ^ 2 / (w.im - T) ≤ (2 + M ^ 2 + (1 + |T + 1|) ^ 2) * w.im ^ 2 := by
    rw [mul_pow] at e3
    nlinarith [sq_nonneg M]
  have e6 := mul_le_mul_of_nonneg_right e5 hm
  nlinarith

end GlobalTheory.OrbitNfac

namespace GlobalTheory


end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodsChangeOfEigenFrame
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor.Chg

open GlobalTheory.ShFam.OpenReg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Letter Dw} {Fu : Fam Xo c σ e} {i : Fin Fu.n}
  {P : (Fu.Di i).La →+ (Fin g → ℂ)} {y : Sp ℂ ⟶ Xo.XF c}


variable (Z P y) in
def Lifts (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ Z.t.G.left) : Prop :=
  ∃ v₀ : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left,
    v₀ ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y ∧ v₀ ≫ Z.m.φ = v ∧
    IsDerivAt0 (fun w => (Fu.ex i P w).left) w (v₀ ≫ Z.m0.toSABMap.φ)

variable (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
  (hy : y ≫ pullback.fst _ _ = Fu.u i P) {x : Sp ℂ ⟶ Z.X} (hx : y ≫ Z.jQ ≫ pullback.fst _ _ = x)

include hP hy hx

theorem exists_dir {v : Sp (DualNumber ℂ) ⟶ Z.t.G.left} (hv : IsTanAtG Z.t x v) : ∃ w, Lifts Z P y w v := by
  obtain ⟨v₀, h1, rfl⟩ := exists_lift Z.m (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
    (by rw [hv.1, ← hx, Category.assoc])
  obtain ⟨w, hw, -⟩ := (isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP).2.2 _
    ((tan_iff Z.m0.toSABMap hy h1).2 ((tan_iff Z.m hx h1).1 hv))
  exact ⟨w, v₀, h1, rfl, hw⟩

theorem eq_sum_of_comb {n : ℕ} {v : Fin n → (Sp (DualNumber ℂ) ⟶ Z.t.G.left)} {W : Fin n → Fin g → ℂ}
    (hW : ∀ k, Lifts Z P y (W k) (v k)) {v' : Sp (DualNumber ℂ) ⟶ Z.t.G.left} {w : Fin g → ℂ} (hw : Lifts Z P y w v')
    {a : Fin n → ℂ} (h : IsCombAtG Z.t x v a v') : w = ∑ k, a k • W k := by
  choose u h1 h2 h3 using hW
  obtain ⟨u', h1', rfl, h3'⟩ := hw
  obtain rfl : v = fun k => u k ≫ Z.m.φ := funext fun k => (h2 k).symm
  have h4 := (comb_iff Z.m0.toSABMap hy h1 a h1').2 ((comb_iff Z.m hx h1 a h1').1 h)
  have h5 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ Fu i P hP n _ W h3 a _).1 h4
  have ht := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP
  exact (ht.2.2 _ (ht.1 _ _ h3')).unique h3' h5

theorem span_eq_top (f : EigFrame Z σ x) {W : Letter Dw → Fin g → ℂ} (hW : ∀ z, Lifts Z P y (W z) (f.v z.1 z.2)) :
    ⊤ ≤ Submodule.span ℂ (Set.range W) := by
  rw [← (Pi.basisFun ℂ (Fin g)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have ht := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP
  obtain ⟨v, hv, -⟩ := ht.2.1 (Pi.basisFun ℂ (Fin g) j)
  have he := (isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e Fu i P hP _ v (e j).1 hv).2 (fun k hk => by
    obtain rfl : k = j := by
      by_contra hne
      exact hk (by simp [hne])
    rfl)
  have htan := ht.1 _ _ hv
  obtain ⟨v₀, h1, rfl⟩ := exists_lift Z.m0.toSABMap (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
    (by rw [htan.1, ← hy, Category.assoc])
  obtain ⟨a, ha, -⟩ := f.basis (e j).1 (v₀ ≫ Z.m.φ) ((tan_iff Z.m hx h1).2 ((tan_iff Z.m0.toSABMap hy h1).1 htan))
    fun a => (eig_iff Z.m h1 a _).2 ((eig_iff Z.m0.toSABMap h1 a _).1 (he a))
  rw [eq_sum_of_comb hP hy hx (W := fun k => W ⟨(e j).1, k⟩) (fun k => hW ⟨_, k⟩) ⟨v₀, h1, rfl, hv⟩ ha]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem linearIndependent (f : EigFrame Z σ x) {W : Letter Dw → Fin g → ℂ}
    (hW : ∀ z, Lifts Z P y (W z) (f.v z.1 z.2)) : LinearIndependent ℂ W :=
  linearIndependent_of_top_le_span_of_card_eq_finrank (span_eq_top hP hy hx f hW)
    (by rw [← Fintype.card_congr e]; simp)

end GlobalTheory.ShFam.Hor.Chg

namespace GlobalTheory.ShFam.Hor

theorem per_chg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (a a' : CxFr Z σ) (i : Fin Fu.n) (Q : (Fu.Di i).La →+ (Letter Dw → ℂ)), Per Fu a i Q → a.1 = a'.1 → ∃ Q', Per Fu a' i Q' ∧ ∀ ρ M, Chg a a' ρ M → ∀ v k, Q v ⟨ρ, k⟩ = ∑ j, Q' v ⟨ρ, j⟩ * M j k := by
  rintro E _ _ _ H Dw l Xo c O _ β Z σ g e Fu ⟨x, f⟩ ⟨x', f'⟩ i Q ⟨P, W, y, hP, hy, hyx, hW, hQ⟩ hxx
  obtain rfl : x = x' := hxx
  have hx : y ≫ Z.jQ ≫ pullback.fst _ _ = x.1 ≫ genι Z := by rw [← Category.assoc, hyx]
  choose W' hW' using fun z : Letter Dw => Chg.exists_dir hP hy hx (f'.tan z.1 z.2)
  let b := Module.Basis.mk (Chg.linearIndependent hP hy hx f' hW') (Chg.span_eq_top hP hy hx f' hW')
  let Q' : (Fu.Di i).La →+ (Letter Dw → ℂ) := b.equivFun.toLinearMap.toAddMonoidHom.comp P
  have hQ' : ∀ v, P v = ∑ z, Q' v z • W' z := fun v => by
    have := b.sum_equivFun (P v)
    simp only [b, Module.Basis.coe_mk] at this
    exact this.symm
  refine ⟨Q', ⟨P, W', y, hP, hy, hyx, hW', hQ'⟩, fun ρ M hM v k => ?_⟩
  choose N hN using fun (τ : E →+* ℂ) j => (f.basis τ _ (f'.tan τ j) (f'.eig τ j)).exists
  have hNM : ∀ j, N ρ j = M j := fun j => (f.basis ρ _ (f'.tan ρ j) (f'.eig ρ j)).unique (hN ρ j) (hM.2 j)
  have hc : ∀ τ j, W' ⟨τ, j⟩ = ∑ k, N τ j k • W ⟨τ, k⟩ := fun τ j =>
    Chg.eq_sum_of_comb hP hy hx (W := fun k => W ⟨τ, k⟩) (fun k => hW ⟨τ, k⟩) (hW' ⟨τ, j⟩) (hN τ j)
  have h1 : ∑ z, Q v z • W z = ∑ z : Letter Dw, (∑ j, Q' v ⟨z.1, j⟩ * N z.1 j z.2) • W z := by
    rw [← hQ, hQ', Fintype.sum_sigma, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [hc, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  have h2 := Fintype.linearIndependent_iffₛ.1 (Chg.linearIndependent hP hy hx f hW) _ _ h1 ⟨ρ, k⟩
  simp only [hNM] at h2
  exact h2

end GlobalTheory.ShFam.Hor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointsOfClosureInProjectiveSpace
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag.LineOfMap

open GlobalTheory.ProjSpace GlobalTheory.FlagMod

variable {Z : Scheme.{0}} {S : Type} [CommRing S]

theorem resG_refl {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)) : resG X h a = a := by
  show (X.presheaf.map (homOfLE h).op).hom a = a
  rw [show (homOfLE h).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  rfl

theorem fnOn_ev (z : Sp S ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) (a : Γ(Z, U)) :
    fnOn ⊤ (ev z U h a) = (z.appLE U ⊤ h).hom a := by
  refine (resG_refl (X := Sp S) le_top _).trans ?_
  exact (Scheme.ΓSpecIso (CommRingCat.of S)).hom_inv_id_apply _

theorem mem_basicOpen_of_isUnit_ev (z : Sp S ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) (a : Γ(Z, U))
    (hu : IsUnit (ev z U h a)) (p : Sp S) : z p ∈ Z.basicOpen a := by
  have h1 := Scheme.basicOpen_of_isUnit _ (hu.map (fnOn ⊤))
  rw [fnOn_ev] at h1
  exact (((Scheme.basicOpen_appLE z ⊤ U h a).symm.trans h1).ge (Set.mem_univ p)).2

variable {O : Type} [CommRing O] {N : ℕ}

end GlobalTheory.DRFlag.LineOfMap
end
end

