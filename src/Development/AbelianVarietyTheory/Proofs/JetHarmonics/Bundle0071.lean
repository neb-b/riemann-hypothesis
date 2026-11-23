module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0066

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DualTensorCayleyCompatible
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.RawTens

def lm {k r : ℕ} {R R' : Rep k r} {T : R.H → R'.H} (h : SmMap R R' T) : R.smSub →ₗ[ℂ] R'.smSub where
  toFun v := ⟨T v, h.mem v v.2⟩
  map_add' v w := Subtype.ext (h.add v v.2 w w.2)
  map_smul' a v := Subtype.ext (h.smul a v v.2)

@[simp] theorem lm_coe {k r : ℕ} {R R' : Rep k r} {T : R.H → R'.H} (h : SmMap R R' T) (v : R.smSub) :
    ((lm h v : R'.smSub) : R'.H) = T v := rfl

section alg

variable {n : ℕ} {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem change_inv (A B : Matrix (Fin n) (Fin n) ℂ) (h : A * B = 1) (x : Fin n → M) (c : Fin n) :
    ∑ d, B d c • ∑ e, A e d • x e = x c := by
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have : ∀ e, ∑ d, B d c * A e d = (1 : Matrix (Fin n) (Fin n) ℂ) e c := by
    intro e
    rw [← h, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun d _ => mul_comm _ _
  simp_rw [this]
  simp [Matrix.one_apply]

theorem dualTens_sum {ι : Type} (S : Finset ι) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n)
    (x : ι → Fin n → M) : dualTens E a b (∑ i ∈ S, x i) = ∑ i ∈ S, dualTens E a b (x i) := by
  funext i
  by_cases h : i = b <;> simp [dualTens, Finset.sum_apply, h, map_sum, Finset.sum_sub_distrib]

theorem alg {N : Fin n → Type} [∀ s, AddCommGroup (N s)] [∀ s, Module ℂ (N s)]
    (I : ∀ s, Fin n → N s →ₗ[ℂ] M) (P : ∀ s, Fin n → M →ₗ[ℂ] N s)
    (A B : Matrix (Fin n) (Fin n) ℂ) (hAB : A * B = 1) (hBA : B * A = 1)
    (E : Fin n → Fin n → Module.End ℂ M) (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s))
    (hI : ∀ s a b y c, I s c (F s a b y) =
      E a b (I s c y) - ∑ j, (B * Matrix.single a b (1 : ℂ) * A) j c • I s j y)
    (h1 : ∀ (x : Fin n → M) c, ∑ s, I s c (∑ d, P s d (x d)) = x c)
    (h2 : ∀ s y, ∑ c, P s c (I s c y) = y)
    (h3 : ∀ s t, s ≠ t → ∀ y, ∑ c, P s c (I t c y) = 0) :
    ∃ (io' : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr' : ∀ s, (Fin n → M) →ₗ[ℂ] N s),
      (∀ s a b y, io' s (F s a b y) = dualTens E a b (io' s y)) ∧
      (∀ s a b x, pr' s (dualTens E a b x) = F s a b (pr' s x)) ∧
      (∀ x, ∑ s, io' s (pr' s x) = x) ∧ (∀ s y, pr' s (io' s y) = y) ∧
      (∀ s t, s ≠ t → ∀ y, pr' s (io' t y) = 0) ∧
      (∀ s y d, io' s y d = ∑ c, B c d • I s c y) ∧
      ∀ s x, pr' s x = ∑ c, P s c (∑ d, A d c • x d) := by
  let io' : ∀ s, N s →ₗ[ℂ] (Fin n → M) := fun s => LinearMap.pi fun d => ∑ c, B c d • I s c
  let pr' : ∀ s, (Fin n → M) →ₗ[ℂ] N s := fun s =>
    ∑ c, (P s c).comp (∑ d, A d c • LinearMap.proj d)
  have e1 : ∀ s y d, io' s y d = ∑ c, B c d • I s c y := by
    intro s y d
    simp [io', LinearMap.sum_apply]
  have e2 : ∀ s x, pr' s x = ∑ c, P s c (∑ d, A d c • x d) := by
    intro s x
    simp only [pr', LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.proj_apply]
  have c1 : ∀ s a b y, io' s (F s a b y) = dualTens E a b (io' s y) := by
    intro s a b y
    funext d
    have hY : ∀ j c, (B * Matrix.single a b (1 : ℂ) * A) j c = A b c * B j a := by
      intro j c
      rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single a]
      · simp [mul_comm]
      · intro e _ he
        simp [Matrix.single_mul_apply_of_ne, he]
      · simp
    have hz : ∀ c, ∑ j, (B * Matrix.single a b (1 : ℂ) * A) j c • I s j y = A b c • io' s y a := by
      intro c
      rw [e1, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hY, mul_smul]
    have hd : ∑ c, B c d * A b c = if d = b then 1 else 0 := by
      have : ∑ c, B c d * A b c = (A * B) b d := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun d _ => mul_comm _ _
      rw [this, hAB, Matrix.one_apply]
      simp [eq_comm]
    simp only [dualTens]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, e1 s y d, map_sum]
    simp_rw [hI, hz, smul_sub, Finset.sum_sub_distrib, smul_smul, ← Finset.sum_smul, hd, map_smul]
    by_cases h : d = b <;> simp [h]
  have c3 : ∀ x, ∑ s, io' s (pr' s x) = x := by
    intro x
    funext d
    rw [Finset.sum_apply]
    simp_rw [e1, e2]
    rw [Finset.sum_comm]
    simp_rw [← Finset.smul_sum, h1]
    exact change_inv A B hAB x d
  have c4 : ∀ s y, pr' s (io' s y) = y := by
    intro s y
    rw [e2]
    simp_rw [e1, change_inv B A hBA]
    exact h2 s y
  have c5 : ∀ s t, s ≠ t → ∀ y, pr' s (io' t y) = 0 := by
    intro s t hst y
    rw [e2]
    simp_rw [e1, change_inv B A hBA]
    exact h3 s t hst y
  refine ⟨io', pr', c1, ?_, c3, c4, c5, e1, e2⟩
  intro s a b x
  conv_lhs => rw [← c3 x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [dualTens_sum, map_sum, Finset.sum_eq_single s]
  · rw [← c1, c4]
  · intro t _ ht
    rw [← c1, c5 s t (Ne.symm ht)]
  · simp

end alg

theorem rawTens : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (RI : Fin (2 * r + k + 1) → Rep k r) (muI : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H) (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)) (F : ∀ s, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (RI s).smSub), (∀ s, (RI s).IsDS ε (muI s)) → TensRaw dualM R RI io pr → IsUnit Q → R.IsE Q E → (∀ s, (RI s).IsE Q (F s)) → ∃ (io' : ∀ s, (RI s).smSub →ₗ[ℂ] (Fin (2 * r + k + 1) → R.smSub)) (pr' : ∀ s, (Fin (2 * r + k + 1) → R.smSub) →ₗ[ℂ] (RI s).smSub), (∀ s a b y, io' s (F s a b y) = dualTens E a b (io' s y)) ∧ (∀ s a b x, pr' s (dualTens E a b x) = F s a b (pr' s x)) ∧ (∀ x, ∑ s, io' s (pr' s x) = x) ∧ (∀ s y, pr' s (io' s y) = y) ∧ (∀ s t, s ≠ t → ∀ y, pr' s (io' t y) = 0) ∧ (∀ s y d, ((io' s y d : R.smSub) : R.H) = ∑ c, Q⁻¹ c d • io s c (y : (RI s).H)) ∧ ∀ s x, ((pr' s x : (RI s).smSub) : (RI s).H) = ∑ c, pr s c (∑ d, Q d c • ((x d : R.smSub) : R.H)) := by
  intro hK k r ε mu R hR RI muI io pr Q E F hRI hT hQ hE hF
  have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  obtain ⟨io', pr', c1, c2, c3, c4, c5, e1, e2⟩ :=
    alg (N := fun s => (RI s).smSub) (fun s c => lm (hT.io_sm s c)) (fun s c => lm (hT.pr_sm s c)) Q Q⁻¹
      (Matrix.mul_nonsing_inv Q hdet) (Matrix.nonsing_inv_mul Q hdet) E F
      (by
        intro s a b y c
        apply Subtype.ext
        rw [lm_coe, hF s a b y, GlobalTheory.dualTens_io_dC hK k r ε mu R hR RI muI io pr hRI hT s _ y y.2 c,
          Submodule.coe_sub, hE a b, Submodule.coe_sum]
        rfl)
      (by
        intro x c
        apply Subtype.ext
        have := hT.sum_io_pr (fun d => (x d : R.H)) (fun d => (x d).2) c
        simpa only [Submodule.coe_sum, lm_coe] using this)
      (by
        intro s y
        apply Subtype.ext
        have := hT.pr_io s y y.2
        simpa only [Submodule.coe_sum, lm_coe] using this)
      (by
        intro s t hst y
        apply Subtype.ext
        have := hT.pr_io_ne s t hst y y.2
        simpa only [Submodule.coe_sum, lm_coe, Submodule.coe_zero] using this)
  refine ⟨io', pr', c1, c2, c3, c4, c5, ?_, ?_⟩
  · intro s y d
    rw [e1]
    simp only [Submodule.coe_sum, lm_coe, Submodule.coe_smul]
  · intro s x
    rw [e2]
    simp only [Submodule.coe_sum, lm_coe, Submodule.coe_smul]

end GlobalTheory.RawTens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDualMatrixFrameFvec
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.DualFrame

theorem exists_linearIndependent_extend {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (v : Fin n → V)
    (hv : LinearIndependent ℂ v) (m : ℕ) (hm : n + m ≤ Module.finrank ℂ V) :
    ∃ w : Fin (n + m) → V, LinearIndependent ℂ w ∧ ∀ j, w (Fin.castAdd m j) = v j := by
  induction m with
  | zero => exact ⟨v, hv, fun j => rfl⟩
  | succ m ih =>
    obtain ⟨w, hw, hwv⟩ := ih (by omega)
    have hx : ∃ x, x ∉ Submodule.span ℂ (Set.range w) := by
      by_contra h
      have htop : Submodule.span ℂ (Set.range w) = ⊤ :=
        eq_top_iff.mpr (fun x _ => by_contra (fun hx => h ⟨x, hx⟩))
      have h1 := finrank_range_le_card (R := ℂ) (b := w)
      rw [Set.finrank, htop, finrank_top, Fintype.card_fin] at h1
      omega
    obtain ⟨x, hx⟩ := hx
    refine ⟨Fin.snoc (α := fun _ => V) w x, linearIndependent_finSnoc.mpr ⟨hw, hx⟩, fun j => ?_⟩
    have hj : (Fin.castAdd (m + 1) j : Fin (n + (m + 1))) = Fin.castSucc (Fin.castAdd m j) := Fin.ext rfl
    rw [hj, Fin.snoc_castSucc, hwv]

theorem linearIndependent_fvec (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z') (h0 : z' ≠ 0) :
    LinearIndependent ℂ (fvec k r z') := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hs : ∀ d, ∑ i : Fin r, g (Fin.castSucc i) * bvec (eI k r i) d + g (Fin.last r) * z' d = 0 := by
    intro d
    have := congrFun hg d
    rw [Fin.sum_univ_castSucc] at this
    simpa [fvec] using this
  have hlast : g (Fin.last r) = 0 := by
    obtain ⟨d, hd⟩ := Function.ne_iff.mp h0
    have hd' : r ≤ d.val := by
      by_contra hlt
      exact hd (hz d (Or.inl (by omega)))
    have := hs d
    have hb : ∀ i : Fin r, bvec (eI k r i) d = 0 := by
      intro i
      have hne : d ≠ eI k r i := by
        intro h
        have := congrArg Fin.val h
        simp [eI] at this
        omega
      simp [bvec, hne]
    simp only [hb, mul_zero, Finset.sum_const_zero, zero_add] at this
    exact (mul_eq_zero.mp this).resolve_right hd
  intro i
  refine Fin.lastCases hlast (fun a => ?_) i
  have := hs (eI k r a)
  rw [hlast, zero_mul, add_zero] at this
  rw [Finset.sum_eq_single a] at this
  · simpa [bvec] using this
  · intro b _ hb
    have hne : eI k r a ≠ eI k r b := by
      intro h
      apply hb
      have := congrArg Fin.val h
      simp [eI] at this
      exact Fin.ext this.symm
    simp [bvec, hne]
  · simp

theorem exists_dual_matrix (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (e : Fin (r + 1 + (r + k)) ≃ Fin (2 * r + k + 1)) (hz : inWb k r z') (hT : 0 < Tz k r z') :
    ∃ Q : Matrix (Fin (r + 1 + (r + k))) (Fin (r + 1 + (r + k))) ℂ, Q.det ≠ 0 ∧
      (∀ (i j : Fin (r + 1)), ∑ d, Q (Fin.castAdd (r + k) i) d * fvec k r z' j (e d) = if i = j then 1 else 0) ∧
      ∀ (i : Fin (r + k)) (j : Fin (r + 1)), ∑ d, Q (Fin.natAdd (r + 1) i) d * fvec k r z' j (e d) = 0 := by
  have hz0 : z' ≠ 0 := by
    rintro rfl
    simp [Tz, herm] at hT
  have hli := linearIndependent_fvec k r z' hz hz0
  set u : Fin (r + 1) → Fin (r + 1 + (r + k)) → ℂ := fun j d => fvec k r z' j (e d) with hu
  have hul : LinearIndependent ℂ u :=
    hli.map' (LinearEquiv.funCongrLeft ℂ ℂ e).toLinearMap (LinearEquiv.ker _)
  obtain ⟨w, hw, hwu⟩ := exists_linearIndependent_extend u hul (r + k)
    (by rw [Module.finrank_fin_fun])
  set A : Matrix (Fin (r + 1 + (r + k))) (Fin (r + 1 + (r + k))) ℂ := Matrix.of w with hA
  have hAu : IsUnit A := Matrix.linearIndependent_rows_iff_isUnit.mp hw
  have hdet : IsUnit A.transpose.det := by
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det A).mp hAu
  have hQ : (A.transpose)⁻¹ * A.transpose = 1 := Matrix.nonsing_inv_mul _ hdet
  have hcol : ∀ (i : Fin (r + 1 + (r + k))) (j : Fin (r + 1)),
      ∑ d, (A.transpose)⁻¹ i d * fvec k r z' j (e d) = if i = Fin.castAdd (r + k) j then 1 else 0 := by
    intro i j
    have := congrFun (congrFun hQ i) (Fin.castAdd (r + k) j)
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    simp [hA, hwu, hu]
  refine ⟨(A.transpose)⁻¹, ?_, fun i j => ?_, fun i j => ?_⟩
  · intro h
    have := congrArg Matrix.det hQ
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  · rw [hcol]
    simp [Fin.castAdd_inj]
  · rw [hcol]
    have : Fin.natAdd (r + 1) i ≠ Fin.castAdd (r + k) j := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp [this]

end GlobalTheory.HatNF.DualFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFramesEL
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm

theorem exists_frames_eL {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V]
    (t : SAB H (Sp V)) (L' : LB t.G.left) (h : t.PP.L = L')
    (d : ℕ) (FT : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (ph1 ph2 : PS V 3 d) (sy : PS V 2 d) (ad : 𝓞 E → PS V 2 d)
    (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (uv : Fin d → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G)
    (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (wP : PrimTyG t)
    (hch : IsChartG t (𝟙 (Sp V)) d FT act tg uv x) (hfr : IsFrameG t (𝟙 (Sp V)) d x FT act ph1 ph2 sy ad e)
    (hpr : IsPrimG t wP) :
    ∃ τ : Frames L' (κ := Fin 1 × Fin d) x, τ.Gen ∧
      (∀ (m : ℕ) (y : Sp (Jet V (Fin 1 × Fin d) m)) (J : (Sp (Jet V (Fin 1 × Fin d) m) ⟶ t.G.left) → L'.ι), Good L' y J →
        val (τ m) (𝟙 _) y J = val (genCast h _ _ (eLG t (𝟙 (Sp V)) d x act e wP m)) (𝟙 _) y J) ∧
      (FrTrunc t (𝟙 (Sp V)) d x e → τ.Trunc) := by
  subst h
  have hL := t.PP.isLB
  have heL : ∀ m, (eLG t (𝟙 (Sp V)) d x act e wP m).IsGen := fun m =>
    ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen t.PP.L _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen t.PP.L _ _ _ hpr.1 _)
      (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen t.PP.L _ _ _ (hfr.gen m) _)
  have hτ : ∀ m, ∃ τ : LB.Gen (LB.LinComb t.PP.L (Y := (jOG (𝟙 (Sp V)) d m 1).left) (K := Fin 1) (fun _ => (x m).left)
      fun _ => (1 : ℤ)), τ.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (jOG (𝟙 (Sp V)) d m 1).left) (z : Z)
        (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
          val τ r z J = val (eLG t (𝟙 (Sp V)) d x act e wP m) r z J := by
    intro m
    refine exists_gen hL ?_ _ (heL m)
    intro U _ hU
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id,
      GermD.formEq_eL hch m]
    rw [_root_.mul_assoc, ← Finset.prod_mul_distrib]
    simp only [← zpow_add, neg_add_cancel, zpow_zero, Finset.prod_const_one, _root_.mul_one]
  choose τ hτg hτv using hτ
  refine ⟨τ, hτg, fun m y J hJ => hτv m _ (𝟙 _) y J hJ, fun htr m y J hJ => ?_⟩
  exact (hτv (m + 1) _ (GermD.ρT (𝟙 (Sp V)) d m).left y J hJ).trans
    ((GermD.val_eL_trunc hch e wP htr m y J hJ).trans (hτv m _ (𝟙 _) y J hJ).symm)

theorem frame1St_holds : Frame1St := by
  intro E _ _ _ H V _ _ _ _ t P d FT act ph1 ph2 sy ad tg xT eT wPT hch hfr hpr
  exact exists_frames_eL t P.U.LG.L (congrArg RigLB.L P.bundle).symm d FT act ph1 ph2 sy ad tg _ xT eT wPT hch hfr hpr

end GlobalTheory.PowGerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLettersProdMulMultiplierLeibniz
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF

open MeasureTheory in
private theorem exists_hat_mul_m_eq_double_sum {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}
    (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r) (h : A) (Z : ℂ → A) (Xc : ℕ → A)
    (hZ : ∀ s : ℂ, Z s = ∑ j ∈ Finset.range (r + 2), s ^ j • Xc j)
    (hrule : ∀ m : ℕ → A, _root_.GlobalTheory.HatNF.MulRel L m → ∀ q,
      h * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xc j)
    (hmem : ∀ s, Z s ∈ _root_.GlobalTheory.HatNF.hats L) :
    ∃ (d : Fin (r + 2) → Fin (r + 2) → ℂ) (g : Fin (r + 2) → A),
      (∀ i, g i ∈ _root_.GlobalTheory.HatNF.hats L) ∧ ∀ m : ℕ → A, _root_.GlobalTheory.HatNF.MulRel L m → ∀ q,
        h * m q = ∑ j : Fin (r + 2), ∑ i : Fin (r + 2), d j i • (m (q + j) * g i) := by
  have hν : Function.Injective (fun i : Fin (r + 2) => ((i : ℕ) : ℂ)) :=
    fun i j hij => Fin.ext (by simpa using hij)
  have hspan := (_root_.GlobalTheory.vecPoly_mem_span_values A (r + 2) Z Xc _ hν hZ).1
  have hcoef : ∀ j : Fin (r + 2), ∃ c : Fin (r + 2) → ℂ,
      ∑ i, c i • Z ((i : ℕ) : ℂ) = Xc j :=
    fun j => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hspan j j.2)
  choose d hd using hcoef
  refine ⟨d, fun i => Z ((i : ℕ) : ℂ), fun i => hmem _, fun m hm q => ?_⟩
  rw [hrule m hm q, Finset.sum_range (fun j => m (q + j) * Xc j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hd j, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm]

open MeasureTheory in
private theorem exists_hat_mul_multiplier_expansion {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}
    (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r) {h : A} (hh : h ∈ _root_.GlobalTheory.HatNF.hats L) :
    ∃ (d : Fin (r + 2) → Fin (r + 2) → ℂ) (g : Fin (r + 2) → A),
      (∀ i, g i ∈ _root_.GlobalTheory.HatNF.hats L) ∧ ∀ m : ℕ → A, _root_.GlobalTheory.HatNF.MulRel L m → ∀ q,
        h * m q = ∑ j : Fin (r + 2), ∑ i : Fin (r + 2), d j i • (m (q + j) * g i) := by
  unfold _root_.GlobalTheory.HatNF.hats at hh
  rcases hh with ((⟨Y, rfl⟩ | ⟨Y, rfl⟩) | ⟨Y, rfl⟩) | ⟨Y, rfl⟩
  · obtain ⟨Xa, Xr, hXa, hXr, hrel⟩ := _root_.GlobalTheory.HatTaylorPlus.taylor_plus A r L Y
    exact exists_hat_mul_m_eq_double_sum L _ (fun s => L.Ahat (Y + s)) Xa hXa
      (fun m hm q => (hrel m hm q).1)
      (fun s => by unfold _root_.GlobalTheory.HatNF.hats; exact Or.inl (Or.inl (Or.inl ⟨_, rfl⟩)))
  · obtain ⟨Xa, Xr, hXa, hXr, hrel⟩ := _root_.GlobalTheory.HatTaylorPlus.taylor_plus A r L Y
    exact exists_hat_mul_m_eq_double_sum L _ (fun s => L.R0 (Y + s)) Xr hXr
      (fun m hm q => (hrel m hm q).2)
      (fun s => by unfold _root_.GlobalTheory.HatNF.hats; exact Or.inl (Or.inl (Or.inr ⟨_, rfl⟩)))
  · obtain ⟨Xa, Xr, hXa, hXr, hrel⟩ := _root_.GlobalTheory.HatNF.TaylorMinus.taylor_minus A r L Y
    exact exists_hat_mul_m_eq_double_sum L _ (fun s => L.Ahatv (Y - s)) Xa hXa
      (fun m hm q => (hrel m hm q).1)
      (fun s => by unfold _root_.GlobalTheory.HatNF.hats; exact Or.inl (Or.inr ⟨_, rfl⟩))
  · obtain ⟨Xa, Xr, hXa, hXr, hrel⟩ := _root_.GlobalTheory.HatNF.TaylorMinus.taylor_minus A r L Y
    exact exists_hat_mul_m_eq_double_sum L _ (fun s => L.R0v (Y - s)) Xr hXr
      (fun m hm q => (hrel m hm q).2)
      (fun s => by unfold _root_.GlobalTheory.HatNF.hats; exact Or.inr ⟨_, rfl⟩)

open MeasureTheory in
private theorem exists_hatWord_mul_multiplier_expansion {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}
    (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r) (H : List A) (hH : ∀ h ∈ H, h ∈ _root_.GlobalTheory.HatNF.hats L) :
    ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℕ) (c : ι → ℂ) (P : ι → List A),
      (∀ i, a i ≤ H.length * (r + 1) ∧ (P i).length = H.length ∧
        ∀ h ∈ P i, h ∈ _root_.GlobalTheory.HatNF.hats L) ∧
      ∀ m : ℕ → A, _root_.GlobalTheory.HatNF.MulRel L m → ∀ q,
        H.prod * m q = ∑ i, c i • (m (q + a i) * (P i).prod) := by
  induction H with
  | nil =>
    exact ⟨Unit, inferInstance, fun _ => 0, fun _ => 1, fun _ => [],
      fun _ => ⟨by simp, rfl, by simp⟩, fun m _ q => by simp⟩
  | cons h H ih =>
    obtain ⟨ι, _, a, c, P, hP, hrep⟩ := ih fun x hx => hH x (List.mem_cons_of_mem _ hx)
    obtain ⟨d, g, hg, hrel⟩ := exists_hat_mul_multiplier_expansion L (hH h List.mem_cons_self)
    refine ⟨ι × Fin (r + 2) × Fin (r + 2), inferInstance, fun x => a x.1 + x.2.1,
      fun x => c x.1 * d x.2.1 x.2.2, fun x => g x.2.2 :: P x.1, fun x => ⟨?_, ?_, ?_⟩,
      fun m hm q => ?_⟩
    · have h1 := (hP x.1).1
      have h2 : (x.2.1 : ℕ) ≤ r + 1 := Nat.lt_succ_iff.mp x.2.1.isLt
      rw [List.length_cons, Nat.succ_mul]
      linarith
    · simp [(hP x.1).2.1]
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hg _
      · exact (hP x.1).2.2 y hy
    · rw [List.prod_cons, mul_assoc, hrep m hm q, Finset.mul_sum, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_prod_type, mul_smul_comm, ← mul_assoc, hrel m hm (q + a i), Finset.sum_mul,
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [List.prod_cons, smul_mul_assoc, smul_smul, add_assoc, mul_assoc]


open MeasureTheory in
theorem _root_.GlobalTheory.HatNF.prod_hats_mul_multiplier : ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r), ∀ H : List A, (∀ h ∈ H, h ∈ _root_.GlobalTheory.HatNF.hats L) → ∃ ts : List (ℕ × ℂ × List A), (∀ t ∈ ts, t.1 ≤ H.length * (r + 1) ∧ t.2.2.length = H.length ∧ ∀ h ∈ t.2.2, h ∈ _root_.GlobalTheory.HatNF.hats L) ∧ ∀ m : ℕ → A, _root_.GlobalTheory.HatNF.MulRel L m → ∀ q, H.prod * m q = (ts.map fun t => t.2.1 • (m (q + t.1) * t.2.2.prod)).sum := by
  intro A _ _ r L H hH
  obtain ⟨ι, _, a, c, P, hP, hrep⟩ := exists_hatWord_mul_multiplier_expansion L H hH
  refine ⟨(Finset.univ : Finset ι).toList.map fun i => (a i, c i, P i), ?_, fun m hm q => ?_⟩
  · intro t ht
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ht
    exact hP i
  · rw [hrep m hm q, List.map_map, Finset.sum_map_toList]
    rfl

end GlobalTheory.HatNF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PlusHatsPassGeneratorsStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.Ahat_mul_and_R0_mul_mem_nfSpan_hats : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ b ∈ bset d, ∀ y : ℂ, d.L.Ahat y * b ∈ nfSpan d (hats d.L) 0 0 1 ∧ d.L.R0 y * b ∈ nfSpan d (hats d.L) 0 0 1 := by
  first | exact @GlobalTheory.HatNF.GenPlus.plus_hats_pass_generators | exact GlobalTheory.HatNF.GenPlus.plus_hats_pass_generators | (intros; apply GlobalTheory.HatNF.GenPlus.plus_hats_pass_generators <;> assumption)
end

