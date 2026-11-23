module

public import Development.WeilBound.CoreStatements.FlagImmersions.Transport
public import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifVec
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0168
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0014

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.EqZeroOfTri
section
noncomputable section

namespace RootFieldNumerics

open Filter Topology Matrix

namespace FlImm

variable {N e : ℕ}

def cutRows (A : Matrix (Fin N) (Fin N) ℂ) (b : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun a c => if a ≤ b then A a c else (1 : Matrix (Fin N) (Fin N) ℂ) a c

def upT (A : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun c b => ((cutRows A b)⁻¹ *ᵥ Pi.single b 1) c

theorem cutRows_one (b : Fin N) : cutRows (1 : Matrix (Fin N) (Fin N) ℂ) b = 1 := by
  ext a c
  simp [cutRows]

theorem upT_one : upT (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
  ext c b
  simp [upT, cutRows_one, Matrix.one_apply, Pi.single_apply]

theorem upT_spec {A : Matrix (Fin N) (Fin N) ℂ} (h : ∀ b, (cutRows A b).det ≠ 0) (a b : Fin N) :
    (b < a → upT A a b = 0) ∧ (a ≤ b → (A * upT A) a b = (1 : Matrix (Fin N) (Fin N) ℂ) a b) := by
  have k : cutRows A b *ᵥ ((cutRows A b)⁻¹ *ᵥ Pi.single b 1) = Pi.single b 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ (h b)), Matrix.one_mulVec]
  have k1 := congrFun k a
  constructor
  · intro hba
    have e1 : (cutRows A b *ᵥ ((cutRows A b)⁻¹ *ᵥ Pi.single b 1)) a =
        ((1 : Matrix (Fin N) (Fin N) ℂ) *ᵥ ((cutRows A b)⁻¹ *ᵥ Pi.single b 1)) a := by
      generalize (cutRows A b)⁻¹ *ᵥ Pi.single b 1 = w
      simp only [Matrix.mulVec, dotProduct, cutRows, Matrix.of_apply, if_neg (not_le.2 hba)]
    rw [e1, Matrix.one_mulVec, Pi.single_eq_of_ne hba.ne'] at k1
    exact k1
  · intro hab
    have e1 : (cutRows A b *ᵥ ((cutRows A b)⁻¹ *ᵥ Pi.single b 1)) a = (A * upT A) a b := by
      simp only [Matrix.mul_apply, upT, Matrix.of_apply]
      generalize (cutRows A b)⁻¹ *ᵥ Pi.single b 1 = w
      simp only [Matrix.mulVec, dotProduct, cutRows, Matrix.of_apply, if_pos hab]
    rw [← e1, k1, Matrix.one_apply, Pi.single_apply]

theorem an_mul {f g : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ} {t : Fin e → ℂ}
    (hf : ∀ a b, AnalyticAt ℂ (fun z => f z a b) t) (hg : ∀ a b, AnalyticAt ℂ (fun z => g z a b) t) (a b : Fin N) :
    AnalyticAt ℂ (fun z => (f z * g z) a b) t := by
  simp only [Matrix.mul_apply]
  exact Finset.analyticAt_fun_sum _ fun c _ => (hf a c).mul (hg c b)

theorem an_cut {f : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ} {t : Fin e → ℂ}
    (hf : ∀ a b, AnalyticAt ℂ (fun z => f z a b) t) (b a c : Fin N) : AnalyticAt ℂ (fun z => cutRows (f z) b a c) t := by
  by_cases h : a ≤ b
  · simpa only [cutRows, Matrix.of_apply, if_pos h] using hf a c
  · simpa only [cutRows, Matrix.of_apply, if_neg h] using analyticAt_const

theorem an_upT {f : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ} {t : Fin e → ℂ}
    (hf : ∀ a b, AnalyticAt ℂ (fun z => f z a b) t) (h : ∀ b, (cutRows (f t) b).det ≠ 0) (c b : Fin N) :
    AnalyticAt ℂ (fun z => upT (f z) c b) t :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) c).analyticAt _).comp
    (SheetDecomposition.vecInvAn (h := fun z => cutRows (f z) b) (w := fun _ => Pi.single b 1) (an_cut hf b) (h b) analyticAt_const)

def dM (f : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ) (t v : Fin e → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun a b => fderiv ℂ (fun z => f z a b) t v

theorem dM_mul {f g : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ} {t : Fin e → ℂ}
    (hf : ∀ a b, AnalyticAt ℂ (fun z => f z a b) t) (hg : ∀ a b, AnalyticAt ℂ (fun z => g z a b) t) (v : Fin e → ℂ) :
    dM (fun z => f z * g z) t v = dM f t v * g t + f t * dM g t v := by
  ext a b
  have h : HasFDerivAt (fun z => ∑ c, f z a c * g z c b)
      (∑ c, (f t a c • fderiv ℂ (fun z => g z c b) t + g t c b • fderiv ℂ (fun z => f z a c) t)) t :=
    HasFDerivAt.fun_sum fun c _ =>
      (hf a c).differentiableAt.hasFDerivAt.fun_mul (hg c b).differentiableAt.hasFDerivAt
  simp only [dM, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply]
  rw [h.fderiv, ← Finset.sum_add_distrib]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem dM_const (A : Matrix (Fin N) (Fin N) ℂ) (t v : Fin e → ℂ) : dM (fun _ => A) t v = 0 := by
  ext a b
  simp [dM]

theorem dM_zero {f : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ} {t : Fin e → ℂ} (v : Fin e → ℂ) {a b : Fin N} {c : ℂ}
    (h : ∀ᶠ z in 𝓝 t, f z a b = c) : dM f t v a b = 0 := by
  have k : (fun z => f z a b) =ᶠ[𝓝 t] fun _ => c := h
  simp [dM, k.fderiv_eq]

theorem eq_zero_of_tri {L W : Matrix (Fin N) (Fin N) ℂ} (hd : IsUnit L.det) (hL : ∀ a b, a < b → L a b = 0)
    (hW : W.BlockTriangular id) (h : ∀ a b, a ≤ b → (L * W) a b = 0) : W = 0 := by
  letI := L.invertibleOfIsUnitDet hd
  have hL' : L.BlockTriangular OrderDual.toDual := fun a b hab => hL a b hab
  have hI := Matrix.blockTriangular_inv_of_blockTriangular hL'
  ext a b
  rcases lt_or_ge b a with hab | hab
  · exact hW hab
  · have e1 : W = L⁻¹ * (L * W) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
    rw [e1, Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases le_or_gt c b with hc | hc
    · rw [h c b hc, mul_zero]
    · have hac : a < c := lt_of_le_of_lt hab hc
      rw [hI (OrderDual.toDual_lt_toDual.2 hac), zero_mul]

end FlImm

open FlImm

theorem flagImm_of : RankLem → FlagImm := by
  intro hR Ψ _ N e V gm hV hne han hdet hc
  classical
  obtain ⟨t₀, ht₀⟩ := hne
  let A : Ψ → (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ := fun τ t => (gm τ t₀)⁻¹ * gm τ t
  let T : Ψ → (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ := fun τ t => upT (A τ t)
  let L : Ψ → (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ := fun τ t => A τ t * T τ t
  have hA0 : ∀ τ, A τ t₀ = 1 := fun τ => Matrix.nonsing_inv_mul _ (hdet t₀ ht₀ τ)
  have hA : ∀ t ∈ V, ∀ τ a b, AnalyticAt ℂ (fun z => A τ z a b) t := fun t ht τ =>
    an_mul (f := fun _ => (gm τ t₀)⁻¹) (fun _ _ => analyticAt_const) fun a b => han τ a b t ht
  have hc0 : ∀ τ b, (cutRows (A τ t₀) b).det ≠ 0 := fun τ b => by simp [hA0, cutRows_one]
  have hev : ∀ᶠ t in 𝓝 t₀, t ∈ V ∧ (∀ τ b, (cutRows (A τ t) b).det ≠ 0) ∧ ∀ τ, (T τ t).det ≠ 0 := by
    refine (hV.eventually_mem ht₀).and (Filter.Eventually.and ?_ ?_)
    · exact Filter.eventually_all.2 fun τ => Filter.eventually_all.2 fun b =>
        (SheetDecomposition.vecDetAn (h := fun z => cutRows (A τ z) b) (an_cut (hA t₀ ht₀ τ) b)).continuousAt.eventually_ne (hc0 τ b)
    · refine Filter.eventually_all.2 fun τ => ?_
      refine (SheetDecomposition.vecDetAn (h := T τ) (an_upT (hA t₀ ht₀ τ) (hc0 τ))).continuousAt.eventually_ne ?_
      show (upT (A τ t₀)).det ≠ 0
      simp [hA0, upT_one]
  obtain ⟨W, hW, hWo, hW0⟩ := eventually_nhds_iff.1 hev
  have hT : ∀ t ∈ W, ∀ τ a b, AnalyticAt ℂ (fun z => T τ z a b) t := fun t ht τ =>
    an_upT (hA t (hW t ht).1 τ) ((hW t ht).2.1 τ)
  have hL : ∀ t ∈ W, ∀ τ a b, AnalyticAt ℂ (fun z => L τ z a b) t := fun t ht τ =>
    an_mul (hA t (hW t ht).1 τ) (hT t ht τ)
  have hTt : ∀ t ∈ W, ∀ τ, (T τ t).BlockTriangular id := fun t ht τ a b hab =>
    (upT_spec ((hW t ht).2.1 τ) a b).1 hab
  have hLs : ∀ t ∈ W, ∀ τ a b, a ≤ b → L τ t a b = (1 : Matrix (Fin N) (Fin N) ℂ) a b := fun t ht τ a b hab =>
    (upT_spec ((hW t ht).2.1 τ) a b).2 hab
  have hgL : ∀ τ t, gm τ t₀ * L τ t = gm τ t * T τ t := fun τ t => by
    simp only [L, A, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hdet t₀ ht₀ τ), Matrix.one_mul]
  let q := (Fintype.equivFin (Ψ × Fin N × Fin N)).symm
  let Φ : (Fin e → ℂ) → Fin (Fintype.card (Ψ × Fin N × Fin N)) → ℂ := fun t i => L (q i).1 t (q i).2.1 (q i).2.2
  obtain ⟨t, ht, hinj⟩ := hR e _ W Φ hWo ⟨t₀, hW0⟩ (fun t ht => analyticAt_pi_iff.2 fun i => hL t ht _ _ _) (by
    intro t ht
    refine (hc t (hW t ht).1).mono fun t' ht' => ?_
    refine And.intro (hW t' ht'.1).1 fun τ => ?_
    have e1 : L τ t' = L τ t := by
      ext a b
      simpa [Φ] using congrFun ht'.2 (q.symm (τ, a, b))
    have hu : IsUnit (T τ t').det := IsUnit.mk0 _ ((hW t' ht'.1).2.2 τ)
    letI := (T τ t').invertibleOfIsUnitDet hu
    refine ⟨T τ t * (T τ t')⁻¹, (hTt t ht τ).mul (Matrix.blockTriangular_inv_of_blockTriangular (hTt t' ht'.1 τ)), ?_⟩
    show gm τ t' = gm τ t * (T τ t * (T τ t')⁻¹)
    rw [← Matrix.mul_assoc, ← hgL, ← e1, hgL, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one])
  refine ⟨t, (hW t ht).1, fun v hv => ?_⟩
  have hWn : ∀ᶠ z in 𝓝 t, z ∈ W := hWo.eventually_mem ht
  have hdL : ∀ τ, dM (L τ) t v = 0 := fun τ => by
    have hu : IsUnit (T τ t).det := IsUnit.mk0 _ ((hW t ht).2.2 τ)
    have hg := hdet t (hW t ht).1 τ
    have hg0 := hdet t₀ ht₀ τ
    letI := (T τ t).invertibleOfIsUnitDet hu
    have e1 : dM (fun z => gm τ t₀ * L τ z) t v = dM (fun z => gm τ z * T τ z) t v := by simp only [hgL]
    rw [dM_mul (f := fun _ => gm τ t₀) (fun _ _ => analyticAt_const) (hL t ht τ), dM_const, Matrix.zero_mul, zero_add,
      dM_mul (fun a b => han τ a b t (hW t ht).1) (hT t ht τ)] at e1
    let X := (T τ t)⁻¹ * (((gm τ t)⁻¹ * dM (gm τ) t v) * T τ t + dM (T τ) t v)
    have hX : X.BlockTriangular id := by
      refine (Matrix.blockTriangular_inv_of_blockTriangular (hTt t ht τ)).mul (((hv τ).mul (hTt t ht τ)).add ?_)
      intro a b hab
      exact dM_zero v (hWn.mono fun z hz => hTt z hz τ hab)
    have e2 : L τ t * X = dM (L τ) t v := by
      have e3 : gm τ t₀ * (L τ t * X) = gm τ t₀ * dM (L τ) t v := by
        rw [e1, ← Matrix.mul_assoc, hgL]
        simp only [X, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu, Matrix.mul_add,
          Matrix.mul_nonsing_inv_cancel_left _ _ hg]
      have e4 := congrArg (fun Z => (gm τ t₀)⁻¹ * Z) e3
      simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ hg0] using e4
    have hLu : IsUnit (L τ t).det := by
      have e5 : (gm τ t₀).det * (L τ t).det = (gm τ t).det * (T τ t).det := by
        rw [← Matrix.det_mul (gm τ t₀), hgL, Matrix.det_mul]
      have e6 := hg.mul hu
      rw [← e5] at e6
      exact isUnit_of_mul_isUnit_right e6
    have hX0 : X = 0 := eq_zero_of_tri hLu (fun a b hab => by rw [hLs t ht τ a b hab.le, Matrix.one_apply_ne hab.ne]) hX
      fun a b hab => by
        rw [e2]
        exact dM_zero v (hWn.mono fun z hz => hLs z hz τ a b hab)
    rw [← e2, hX0, Matrix.mul_zero]
  refine hinj (?_ : fderiv ℂ Φ t v = fderiv ℂ Φ t 0)
  rw [map_zero]
  ext i
  have k := fderiv_pi (𝕜 := ℂ) (φ := fun i z => L (q i).1 z (q i).2.1 (q i).2.2) (x := t)
    fun i => (hL t ht _ _ _).differentiableAt
  show fderiv ℂ (fun z i => L (q i).1 z (q i).2.1 (q i).2.2) t v i = 0
  rw [k]
  exact congrFun (congrFun (hdL (q i).1) (q i).2.1) (q i).2.2

end RootFieldNumerics
end
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.TopLeIffCentre
section
noncomputable section

namespace RootFieldNumerics.Un

open AlgebraicGeometry CategoryTheory NumberField Filter Topology Matrix
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

theorem top_le_iff_centre {X : Scheme.{0}} (z : Sp ℂ ⟶ X) (U : X.Opens) : ⊤ ≤ z ⁻¹ᵁ U ↔ centre z ∈ U := by
  constructor
  · exact fun h => h (show IsLocalRing.closedPoint ℂ ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  · intro h q _
    have e : q = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    subst e
    exact h

theorem eventually_centre {X : Scheme.{0}} {n : ℕ} {V : Set (Fin n → ℂ)} {z : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (hz : IsHolTo V z)
    {t₀ : Fin n → ℂ} (ht : t₀ ∈ V) (U : X.Opens) (h : centre (z t₀) ∈ U) : ∀ᶠ t in 𝓝 t₀, centre (z t) ∈ U := by
  filter_upwards [(hz U 0).1.mem_nhds ⟨ht, (top_le_iff_centre _ _).2 h⟩] with t h' using (top_le_iff_centre _ _).1 h'.2

theorem fibreLatVec_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
    {z : Sp ℂ ⟶ X} {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] {R : RiemLat E g Λ} {A₀ A₁ : Type}
    {x : A₀ → Fin g → ℂ} {v : A₀ → (epsAt z ⟶ t.G)} (h : FibreLatVec t z R x v) (f : A₁ → A₀) :
    FibreLatVec t z R (fun a => x (f a)) fun a => v (f a) := by
  obtain ⟨A, i, φ, u, χ, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨A, i, φ, u, χ, h1, h2, h3, h4, h5, fun a => h6 _⟩

theorem exists_tr {Ω Li : Type} [Field Ω] [AddCommGroup Li] [Module Ω Li] {r : ℕ} (b b₀ : Fin r → Li)
    (h : ∀ i, flagStep Ω b i = flagStep Ω b₀ i) (i : Fin r) : ∃ t : Ω, b i - t • b₀ i ∈ flagStep Ω b₀ i := by
  have h1 : b i ∈ flagStep Ω b₀ (i + 1) := by
    rw [← h]
    exact Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩
  have h2 : {k : Fin r | (k : ℕ) < i + 1} = insert i {k : Fin r | (k : ℕ) < i} := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Fin.ext_iff]
    omega
  rw [flagStep, h2, Set.image_insert_eq, Submodule.mem_span_insert] at h1
  obtain ⟨a, w, hw, e⟩ := h1
  exact ⟨a, by rw [e, add_sub_cancel_left]; exact hw⟩

theorem leadMinor_smul {r : ℕ} (c : ℝ) (Γ : Matrix (Fin r) (Fin r) ℂ) (k : ℕ) :
    leadMinor ((c : ℂ) • Γ) k = c ^ k * leadMinor Γ k := by
  unfold leadMinor
  split_ifs with h
  · rw [Matrix.submatrix_smul, Pi.smul_apply, Pi.smul_apply, Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow,
      Complex.re_ofReal_mul]
  · simp

theorem log_nu {r : ℕ} {Γ : Matrix (Fin r) (Fin r) ℂ} (h : Γ.PosDef) (i : Fin r) :
    Real.log (Real.sqrt (leadMinor ((Real.pi : ℂ) • Γ) (i + 1) / leadMinor ((Real.pi : ℂ) • Γ) i)) =
      Real.log (Real.sqrt (leadMinor Γ (i + 1) / leadMinor Γ i)) + Real.log (Real.sqrt Real.pi) := by
  have h1 := leadMinor_pos_of_posDef h (s := i + 1) i.2
  have h2 := leadMinor_pos_of_posDef h (s := i) i.2.le
  have hp := Real.pi_pos
  have e : leadMinor ((Real.pi : ℂ) • Γ) (i + 1) / leadMinor ((Real.pi : ℂ) • Γ) i =
      leadMinor Γ (i + 1) / leadMinor Γ i * Real.pi := by
    rw [leadMinor_smul, leadMinor_smul, pow_succ]
    field_simp
  rw [e, Real.sqrt_mul (div_pos h1 h2).le, Real.log_mul (Real.sqrt_pos.2 (div_pos h1 h2)).ne' (Real.sqrt_pos.2 hp).ne']

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}

def CountAt {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y ∅ y)
    (Fl : 𝔐.Flag) (U : 𝔐.X.Opens) : Prop :=
  ∀ (b : ∀ s, Fin (labelRk D s) → 𝔐.Li) (g : ℕ) (Λ : Type) [AddCommGroup Λ]
      [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (F : CMType H ⊕ CMType H → ℕ → Submodule ℂ (Fin g → ℂ)),
      (∀ s i, flagStep Ω (b s) i = flagStep Ω (Fl.b s) i) →
      {z : Sp ℂ ⟶ 𝔐.X | centre z ∈ U ∧ 𝔐.Interior z ∧ (∀ s, (𝔐.V s).IsFrameAt (b s) ⟨centre z, 𝔐.all _⟩) ∧
        ∃ (x : (Σ s, Fin (labelRk D s)) → Fin g → ℂ) (v : (Σ s, Fin (labelRk D s)) → (epsAt z ⟶ 𝔐.t.G)),
          (∀ a, 𝔐.M.ValAt z (b a.1 a.2) (v a)) ∧ FibreLatVec 𝔐.t z R x v ∧
          ∀ s k, flagStep ℂ (fun i => x ⟨s, i⟩) k = F s k}.Countable

theorem root_log (Γ : ∀ s, Matrix (Fin (labelRk D s)) (Fin (labelRk D s)) ℂ) (hΓ : ∀ s, (Γ s).PosDef) (τ : CMType H)
    (i : Fin (D.p + D.q)) :
    (HodgeCpt.rootSgn D (τ, i) : ℝ) * Real.log (Real.sqrt
      (leadMinor ((Real.pi : ℂ) • Γ (HodgeCpt.rootIdx D (τ, i)).1) ((HodgeCpt.rootIdx D (τ, i)).2 + 1) /
        leadMinor ((Real.pi : ℂ) • Γ (HodgeCpt.rootIdx D (τ, i)).1) (HodgeCpt.rootIdx D (τ, i)).2)) =
      grLog (p := D.p) (q := D.q) (Γ (.inl τ)) (Γ (.inr τ)) i +
        (HodgeCpt.rootSgn D (τ, i) : ℝ) * Real.log (Real.sqrt Real.pi) := by
  rw [log_nu (hΓ _), mul_add]
  congr 1
  let F : (Σ s, Fin (labelRk D s)) → ℝ := fun a => Real.log (Real.sqrt (leadMinor (Γ a.1) (a.2 + 1) / leadMinor (Γ a.1) a.2))
  show _ * F (HodgeCpt.rootIdx D (τ, i)) = _
  by_cases h : (i : ℕ) < D.p
  · have e : HodgeCpt.rootIdx D (τ, i) = ⟨.inl τ, ⟨i, h⟩⟩ := dif_pos h
    rw [e]
    simp only [HodgeCpt.rootSgn, grLog, if_pos h, F, Int.cast_one, one_mul]
    rfl
  · have e : HodgeCpt.rootIdx D (τ, i) = ⟨.inr τ, ⟨D.p + D.q - 1 - i, by have := i.2; show _ < D.q; omega⟩⟩ := dif_neg h
    rw [e]
    simp only [HodgeCpt.rootSgn, grLog, if_neg h, F, Int.cast_neg, Int.cast_one, neg_mul, one_mul]
    rfl

theorem locChart (hLP : LocPer) (hT : Transport) (hFV : FrameVals) (hPM : PerMat) (hPot : PotLoc) (hG : Top.Given)
    (hN : 1 ≤ D.p + D.q) {RM : Top.RootModel (CMType H) (D.p + D.q)}
    {Sys : AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y Sys} (Or : RootOrigin Y ∅ RM Fx)
    (ψ : Sys.X → Or.Re.R.X) (hψ : HoloMap Sys.A Or.Re.R.A ψ) (hπ : ∀ x, Or.Re.π (ψ x) = x) (z : Sys.X → (Sp ℂ ⟶ Or.𝔐.X))
    (hzi : Function.Injective z) (hzc : ∀ x, CoordsAt Or.𝔐.ξ RM.y (z x) (Or.Re.R.lift (ψ x) (ψ x)))
    (k : Fin Sys.A.n) (hzh : IsHolTo (Sys.A.chart k).target fun t => z ((Sys.A.chart k).symm t))
    (U : Or.𝔐.X.Opens) (x₀ : Sys.X) (hx₀ : x₀ ∈ Sys.open') (hk : x₀ ∈ (Sys.A.chart k).source) (hU : centre (z x₀) ∈ U) :
    ∃ (V : Set (Fin (Top.dimFl (CMType H) (D.p + D.q)) → ℂ))
      (gm : CMType H → (Fin (Top.dimFl (CMType H) (D.p + D.q)) → ℂ) → Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ),
      IsOpen V ∧ Sys.A.chart k x₀ ∈ V ∧ V ⊆ (Sys.A.chart k).target ∧ (∀ t ∈ V, (Sys.A.chart k).symm t ∈ Sys.open') ∧
      (∀ τ a b, AnalyticOnNhd ℂ (fun t => gm τ t a b) V) ∧ (∀ t ∈ V, ∀ τ, InFlagDomain (D.p + D.q) D.p (gm τ t)) ∧
      (∀ t₁ ∈ V, ∀ p : RootIx D, ∃ G : (Fin (Top.dimFl (CMType H) (D.p + D.q)) → ℂ) → ℂ, AnalyticAt ℂ G t₁ ∧ ∀ᶠ t in 𝓝 t₁,
        (Sys.potH (some p)).φ ((Sys.A.chart k).symm t₁) ((Sys.A.chart k).symm t) =
          stepPot (D.p + D.q) D.p p.2 (gm p.1 t) + (G t).re) ∧
      (CountAt Or.𝔐 Or.Fl U → ∀ t ∈ V, {t' ∈ V | SameFl (fun τ => gm τ t) fun τ => gm τ t'}.Countable) := by
  classical
  set ch := Sys.A.chart k with hch
  let t₀ := ch x₀
  have hs₀ : ch.symm t₀ = x₀ := ch.left_inv hk
  have hop : IsOpen Sys.open' := (GlobalTheory.T.section_boundary_closed_and_codense _ _ Sys.A Sys.L Sys.s _ Sys.m Sys.W Sys.sec Sys.snc).1.isOpen_compl
  let V₁ := ch.target ∩ ch.symm ⁻¹' Sys.open'
  have hV₁ : IsOpen V₁ := ch.isOpen_inter_preimage_symm hop
  have ht₁ : t₀ ∈ V₁ := ⟨ch.map_source hk, by show ch.symm t₀ ∈ Sys.open'; rwa [hs₀]⟩
  let z' := fun t => z (ch.symm t)
  have hz₁ : IsHolTo V₁ z' := SheetDecomposition.vecMono hzh hV₁ Set.inter_subset_left
  have hint : ∀ t ∈ V₁, Or.𝔐.Interior (z' t) := fun t ht =>
    (Or.interior _ _ (hzc _)).2 (by rw [hπ]; exact ht.2)
  choose Us hUs b hb hfr using fun s => Or.Fl.sub s ⟨centre (z' t₀), Or.𝔐.all _⟩ trivial
  obtain ⟨g, Λ, _, _, R, V₂, σ, hV₂, ht₂, h21, hfam, hlab, hvec⟩ :=
    hLP hG E H D l Xo c Y ∅ RM.Ω RM.K RM.ι RM.y Or.𝔐 _ V₁ z' hN hV₁ hz₁ hint t₀ ht₁
  let I := Σ s : CMType H ⊕ CMType H, Fin (labelRk D s)
  let e := Fintype.equivFin I
  obtain ⟨xF, hxa, hxe⟩ := hvec _ (fun a => b (e.symm a).1 (e.symm a).2) fun a =>
    (hFV hG E H D l Xo c Y RM.Ω RM.K RM.ι RM.y Or.𝔐 (z' t₀) _ (b _) hN (hint _ ht₁) (hfr _ _ trivial (hUs _))).1 _
  let x : I → (Fin (Top.dimFl (CMType H) (D.p + D.q)) → ℂ) → Fin g → ℂ := fun a => xF (e a)
  have hev : ∀ᶠ t in 𝓝 t₀, t ∈ V₂ ∧ (∀ s, centre (z' t) ∈ Us s) ∧ centre (z' t) ∈ U ∧ (∀ a, AnalyticAt ℂ (x a) t) ∧
      ∃ v : I → (epsAt (z' t) ⟶ Or.𝔐.t.G), (∀ a, Or.𝔐.M.ValAt (z' t) (b a.1 a.2) (v a)) ∧
        FibreLatVec Or.𝔐.t (z' t) (R t) (fun a => x a t) v := by
    filter_upwards [hV₂.mem_nhds ht₂, Filter.eventually_all.2 fun s => eventually_centre hz₁ ht₁ (Us s) (hUs s),
      eventually_centre hz₁ ht₁ U (by show centre (z (ch.symm t₀)) ∈ U; rwa [hs₀]),
      Filter.eventually_all.2 fun a : I => (hxa (e a)).eventually_analyticAt, hxe] with t h1 h2 h3 h4 ⟨v, hv, hf⟩
    refine ⟨h1, h2, h3, h4, fun a => v (e a), fun a => ?_, fibreLatVec_comp hf e⟩
    have := hv (e a)
    rwa [e.symm_apply_apply] at this
  obtain ⟨V₃, h3, hV₃, ht₃⟩ := eventually_nhds_iff.1 hev
  have hfr₃ : ∀ t ∈ V₃, ∀ s, (Or.𝔐.V s).IsFrameAt (b s) ⟨centre (z' t), Or.𝔐.all _⟩ := fun t ht s =>
    hfr s _ trivial ((h3 t ht).2.1 s)
  have hval : ∀ t ∈ V₃, ∀ s, LinearIndependent ℂ (fun i => x ⟨s, i⟩ t) ∧
      Submodule.span ℂ (Set.range fun i => x ⟨s, i⟩ t) = eigSp (R t).B (σ s) ∧
      Or.𝔐.M.GramAt Or.𝔐.t.PP.L (z' t) (b s) ((Real.pi : ℂ) • (R t).gram fun i => x ⟨s, i⟩ t) ∧
      ((R t).gram fun i => x ⟨s, i⟩ t).PosDef := fun t ht s => by
    obtain ⟨h1, -, -, -, v, hv, hf⟩ := h3 t ht
    exact (hFV hG E H D l Xo c Y RM.Ω RM.K RM.ι RM.y Or.𝔐 (z' t) s (b s) hN (hint _ (h21 h1)) (hfr₃ t ht s)).2 g Λ (R t) σ
      _ (fun i => v ⟨s, i⟩) (hlab t h1) (fun i => hv ⟨s, i⟩) (fibreLatVec_comp hf fun i => ⟨s, i⟩)
  obtain ⟨σ', -, hσu, -, -, -, hσ⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.LabPt.exists_labVal E H D l Xo c Y ∅ RM.Ω RM.K RM.ι RM.y Or.𝔐 ℂ (z' t₀)
  obtain rfl := hσu σ (hlab _ ht₂)
  obtain ⟨hcm, -, hconj⟩ := hσ (RingHom.id ℂ)
  simp only [RingHom.id_comp] at hcm hconj
  have hfam₃ : IsHolFam V₃ R := ⟨fun t ht t' ht' => hfam.1 t (h3 t ht).1 t' (h3 t' ht').1,
    fun a => (hfam.2 a).mono fun t ht => (h3 t ht).1⟩
  obtain ⟨V, gm, hV, ht, hV3, hga, hgp, hrig⟩ := hPM E (CMType H) g _ D.p D.q Λ V₃ R (fun τ => σ (.inl τ))
    (fun τ i => x ⟨.inl τ, i⟩) (fun τ i => x ⟨.inr τ, i⟩) hV₃ hfam₃ hcm
    ⟨fun τ i t ht => (h3 t ht).2.2.2.1 _, fun τ i t ht => (h3 t ht).2.2.2.1 _, fun t ht τ =>
      ⟨⟨(hval t ht (.inl τ)).1, (hval t ht (.inl τ)).2.1⟩, (hval t ht (.inr τ)).1, by
        rw [← hconj]; exact (hval t ht (.inr τ)).2.1⟩⟩ t₀ ht₃
  have hV1 : V ⊆ V₁ := fun t ht => h21 (h3 t (hV3 ht)).1
  refine ⟨V, gm, hV, ht, fun t ht => (hV1 ht).1, fun t ht => (hV1 ht).2, hga, fun t ht τ => (hgp t ht τ).1,
    fun t₁ ht₁ p => ?_, fun hC t ht => ?_⟩
  · choose tr htr using fun a : I => exists_tr (b a.1) (Or.Fl.b a.1) (hb a.1) a.2
    let Γ := fun t s => (R t).gram fun i => x ⟨s, i⟩ t
    let nu : I → (Fin (Top.dimFl (CMType H) (D.p + D.q)) → ℂ) → ℝ := fun a t =>
      Real.sqrt (leadMinor ((Real.pi : ℂ) • Γ t a.1) (a.2 + 1) / leadMinor ((Real.pi : ℂ) • Γ t a.1) a.2)
    obtain ⟨G, hGa, hGe⟩ := hPot E H D l Xo c Y ∅ RM Sys Fx Or ψ k V z' (fun r => tr (HodgeCpt.rootIdx D r))
      (fun r => nu (HodgeCpt.rootIdx D r)) hψ hπ hV (fun t ht => (hV1 ht).1) (fun t ht => ⟨(hV1 ht).2, hzc _, fun r =>
        ⟨Or.𝔐.all _, b _, _, hb _, hfr₃ t (hV3 ht) _, htr _, (hval t (hV3 ht) _).2.2.1,
          (hval t (hV3 ht) _).2.2.2.smul (by exact_mod_cast Real.pi_pos), rfl⟩⟩) t₁ ht₁ p
    let C : ℝ := ∑ i ∈ Finset.Iic p.2, (HodgeCpt.rootSgn D (p.1, i) : ℝ) * Real.log (Real.sqrt Real.pi)
    refine ⟨fun t => G t + C, hGa.add analyticAt_const, ?_⟩
    filter_upwards [hGe, hV.mem_nhds ht₁] with t h1 h2
    rw [h1, (hgp t h2 p.1).2 p.2, Complex.add_re, Complex.ofReal_re]
    have := fun i => root_log (Γ t) (fun s => (hval t (hV3 h2) s).2.2.2) p.1 i
    rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib]
    exact (add_right_comm _ _ _).trans (add_assoc _ _ _)
  · refine Set.MapsTo.countable_of_injOn (f := z') ?_ ?_ (hC b g Λ (R t) (fun s k => flagStep ℂ (fun i => x ⟨s, i⟩ t) k) hb)
    · rintro t' ⟨ht', hs⟩
      obtain ⟨h, hP, hfl⟩ := hrig t ht t' ht' hs
      obtain ⟨h1, -, hU', -, v, hv, hf⟩ := h3 t' (hV3 ht')
      refine ⟨hU', hint _ (hV1 ht'), hfr₃ t' (hV3 ht'), fun a => h.symm (x a t'), v, hv,
        hT E H _ _ _ g Λ (R t) (R t') h I _ v (hfam₃.1 t (hV3 ht) t' (hV3 ht')) hP hf, ?_⟩
      rintro (τ | τ) k
      · exact (hfl τ k).1
      · exact (hfl τ k).2
    · intro t₁ h₁ t₂ h₂ e
      exact ch.symm.injOn (hV1 h₁.1).1 (hV1 h₂.1).1 (hzi e)

end RootFieldNumerics.Un
end
end

