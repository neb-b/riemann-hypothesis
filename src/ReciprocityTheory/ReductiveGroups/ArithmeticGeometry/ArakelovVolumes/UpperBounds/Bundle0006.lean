module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0002
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantNormalForms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0017

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bridge
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates

noncomputable section

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
  {E : Type} [Field E] [NumberField E] [IsCMField E]

structure Reading (d : Data K ι Ω WT A) (c : ι) {r : ℕ} (X : FD.Data E r) (sg : K →+* ℂ) where

  Rg : Subring (A c)
  w_mem : ∀ j, d.w j c ∈ Rg
  rd : Rg →+* (Frame X.Ψ r → ℂ)

  WE : AddSubgroup WT
  wL_mem : d.wL ∈ WE
  wt : WE →+ Wt X.Ψ r

  Gen : Set (Frame X.Ψ r)
  Gen_sub : Gen ⊆ X.dom
  Gen_dense : X.dom ⊆ closure Gen
  pt : Frame X.Ψ r → (Ω c →+* ℂ)
  pt_mem : ∀ x ∈ Gen, pt x ∈ PT (Ω := Ω c) sg
  pt_onto : ∀ P ∈ PT (Ω := Ω c) sg, ∃ x ∈ Gen, pt x = P

  w_nz : ∀ x ∈ X.dom, ∃ j, rd ⟨d.w j c, w_mem j⟩ x ≠ 0
  sec : ∀ G (hG : G ∈ WE), ∀ f (hf : f ∈ Rg), f ∈ 𝒜 c G → X.IsSec (wt ⟨G, hG⟩) (rd ⟨f, hf⟩)
  inj : ∀ G, ∀ f (hf : f ∈ Rg), f ∈ 𝒜 c G → (∀ x ∈ X.dom, rd ⟨f, hf⟩ x = 0) → f = 0
  norm : ∀ G (hG : G ∈ WE), ∀ f (hf : f ∈ Rg), f ∈ 𝒜 c G → ∀ x ∈ Gen,
    X.pnorm (wt ⟨G, hG⟩) (rd ⟨f, hf⟩) x = d.nrm c G f (pt x)
  ratio_rd : ∀ G, ∀ f (hf : f ∈ Rg) g (hg : g ∈ Rg), f ∈ 𝒜 c G → g ∈ 𝒜 c G → g ≠ 0 → ∀ x ∈ Gen,
    rd ⟨f, hf⟩ x = pt x (ratio (Ω := Ω c) f g) * rd ⟨g, hg⟩ x

  Gen_inv : ∀ x ∈ Gen, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ Gen ∧ pt (lact γ (rmul x b)) = pt x
  orbit_inj : ∀ x ∈ Gen, ∀ x' ∈ Gen, pt x = pt x' → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x' = lact γ (rmul x b)

  Gen_max : ∀ x ∈ X.dom, ∀ P ∈ PT (Ω := Ω c) sg,
    (∀ G ∈ WE, ∀ f (hf : f ∈ Rg) g (hg : g ∈ Rg), f ∈ 𝒜 c G → g ∈ 𝒜 c G → g ≠ 0 →
      rd ⟨f, hf⟩ x = P (ratio (Ω := Ω c) f g) * rd ⟨g, hg⟩ x) → x ∈ Gen ∧ pt x = P

  bir : ∀ a : Ω c, ∃ (G : WT) (f p : A c), f ∈ Rg ∧ p ∈ Rg ∧ f ∈ 𝒜 c G ∧ p ∈ 𝒜 c G ∧ p ≠ 0 ∧
    p ∈ Algebra.adjoin K (Set.range fun j => d.w j c) ∧ a = ratio (Ω := Ω c) f p

  coordAt : ∀ x ∈ Gen, ∃ (j0 : Fin (d.N + 1)) (jj : Fin (nd X) → Fin (d.N + 1)),
    rd ⟨d.w j0 c, w_mem j0⟩ x ≠ 0 ∧
    (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      rd ⟨d.w (jj k) c, w_mem (jj k)⟩ (cpt X x z) / rd ⟨d.w j0 c, w_mem j0⟩ (cpt X x z) : V (nd X))) 0).det ≠ 0

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStatementPfLA
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Asymptotics

noncomputable section

theorem analyticAt_of_diffOn {n : ℕ} {f : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {z : V n} (hz : z ∈ U) : AnalyticAt ℂ f z := by
  let e : V n ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  have hU' : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
  have hf' : DifferentiableOn ℂ (f ∘ e.symm) (e.symm ⁻¹' U) :=
    hf.comp (e.symm : (Fin n → ℂ) →L[ℂ] V n).differentiableOn (fun y hy => hy)
  have hz' : e z ∈ e.symm ⁻¹' U := by simpa using hz
  have ha := ReciprocityTheory.AnForm.Osgood.osgood n _ _ hU' hf' (e z) hz'
  have hfe : f = (f ∘ e.symm) ∘ e := by
    funext w
    simp
  rw [hfe]
  exact ha.comp ((e : V n →L[ℂ] (Fin n → ℂ)).analyticAt z)

theorem isBigO_norm_pow_of_le {F : Type*} [NormedAddCommGroup F] {k d : ℕ} (h : k ≤ d) :
    (fun y : F => ‖y‖ ^ d) =O[𝓝 0] (fun y => ‖y‖ ^ k) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Metric.ball_mem_nhds (0 : F) one_pos] with y hy
  rw [mem_ball_zero_iff] at hy
  simp only [norm_pow, norm_norm, one_mul]
  exact pow_le_pow_of_le_one (norm_nonneg _) hy.le h

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfD
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.HE

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal

noncomputable section

variable {n : ℕ} {U : Set (V n)}

theorem ext_glue (hU : IsOpen U) (g G : V n → ℂ) (hg : DifferentiableOn ℂ g U)
    (hgn : ∀ W : Set (V n), IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, g y ≠ 0)
    (hG : DifferentiableOn ℂ G {y | y ∈ U ∧ g y ≠ 0})
    (hL : ∀ p ∈ U, ∃ ρ > 0, ball p ρ ⊆ U ∧
      ∫⁻ y in ball p ρ \ {y | g y = 0}, ENNReal.ofReal (‖G y‖ ^ 2) < ⊤) :
    ∃ G' : V n → ℂ, DifferentiableOn ℂ G' U ∧ Set.EqOn G' G {y | y ∈ U ∧ g y ≠ 0} := by
  classical
  have hloc : ∀ p ∈ U, ∃ ρ > 0, ball p ρ ⊆ U ∧ ∃ F : V n → ℂ, DifferentiableOn ℂ F (ball p ρ) ∧
      Set.EqOn F G (ball p ρ \ {y | g y = 0}) := by
    intro p hp
    obtain ⟨ρ, hρ, hsub, hint⟩ := hL p hp
    obtain ⟨F, hF, hFeq⟩ := ReciprocityTheory.L2DbarEstimates.ext n p ρ g G (hg.mono hsub)
      (hG.mono fun y hy => ⟨hsub hy.1, hy.2⟩) hint
    exact ⟨ρ, hρ, hsub, F, hF, hFeq⟩
  choose ρ hρ hsub F hF hFeq using hloc
  have agree : ∀ y (hy : y ∈ U) z (hz : z ∈ U) x, x ∈ ball y (ρ y hy) → x ∈ ball z (ρ z hz) →
      F y hy x = F z hz x := by
    intro y hy z hz x hxy hxz
    by_contra hne
    have hcy : ContinuousAt (F y hy) x :=
      (hF y hy).continuousOn.continuousAt (isOpen_ball.mem_nhds hxy)
    have hcz : ContinuousAt (F z hz) x :=
      (hF z hz).continuousOn.continuousAt (isOpen_ball.mem_nhds hxz)
    have hev : ∀ᶠ t in 𝓝 x, F y hy t ≠ F z hz t := by
      first
        | exact hcy.eventually_ne hcz hne
        | exact ((hcy.sub hcz).eventually_ne (sub_ne_zero.mpr hne)).mono fun t ht h => ht (sub_eq_zero.mpr h)
    have hs : {t | t ∈ ball y (ρ y hy) ∧ t ∈ ball z (ρ z hz) ∧ F y hy t ≠ F z hz t} ∈ 𝓝 x :=
      Filter.inter_mem (isOpen_ball.mem_nhds hxy) (Filter.inter_mem (isOpen_ball.mem_nhds hxz) hev)
    obtain ⟨W, hWs, hWo, hxW⟩ := _root_.mem_nhds_iff.mp hs
    obtain ⟨t, htW, hgt⟩ := hgn W hWo (fun t ht => hsub y hy (hWs ht).1) ⟨x, hxW⟩
    have h1 := hFeq y hy ⟨(hWs htW).1, hgt⟩
    have h2 := hFeq z hz ⟨(hWs htW).2.1, hgt⟩
    exact (hWs htW).2.2 (h1.trans h2.symm)
  refine ⟨fun y => if hy : y ∈ U then F y hy y else 0, ?_, ?_⟩
  · intro y hy
    have hnb : ball y (ρ y hy) ∈ 𝓝 y := isOpen_ball.mem_nhds (mem_ball_self (hρ y hy))
    have heq : (fun y => if hy : y ∈ U then F y hy y else 0) =ᶠ[𝓝 y] F y hy := by
      filter_upwards [hnb] with x hx
      have hxU : x ∈ U := hsub y hy hx
      rw [dite_eq_left hxU]
      exact agree x hxU y hy x (mem_ball_self (hρ x hxU)) hx
    exact (((hF y hy).differentiableAt hnb).congr_of_eventuallyEq heq).differentiableWithinAt
  · intro y hy
    show (if h : y ∈ U then F y h y else 0) = G y
    rw [dite_eq_left hy.1]
    exact hFeq y hy.1 ⟨mem_ball_self (hρ y hy.1), hy.2⟩

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.HE
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfD
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix MeasureTheory

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

abbrev UpI (ι : Type*) (r : ℕ) : Type _ := {i : Ix ι r // ¬ i.2.2 < i.2.1}

abbrev LoI (ι : Type*) (r : ℕ) : Type _ := {i : Ix ι r // i.2.2 < i.2.1}

def Umat (y : UpI ι r → ℂ) (τ : ι) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => if h : ¬ b < a then y ⟨(τ, a, b), h⟩ else 0

lemma Umat_add (y y' : UpI ι r → ℂ) (τ : ι) : Umat (y + y') τ = Umat y τ + Umat y' τ := by
  ext a b
  simp only [Umat, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

lemma Umat_smul (c : ℂ) (y : UpI ι r → ℂ) (τ : ι) : Umat (c • y) τ = c • Umat y τ := by
  ext a b
  simp only [Umat, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

def Lβ (β : ι → Matrix (Fin r) (Fin r) ℂ) : (UpI ι r → ℂ) →ₗ[ℂ] (UpI ι r → ℂ) where
  toFun y i := (β i.1.1 * Umat y i.1.1) i.1.2.1 i.1.2.2
  map_add' y y' := by funext i; simp [Umat_add, Matrix.mul_add]
  map_smul' c y := by funext i; simp [Umat_smul]

def keyU (e : ι ≃ Fin (Fintype.card ι)) (i : UpI ι r) : ℕ ×ₗ (ℕ ×ₗ Fin (Fintype.card ι)) :=
  toLex ((i.1.2.2 : ℕ), toLex (r - (i.1.2.1 : ℕ), e i.1.1))

lemma keyU_injective (e : ι ≃ Fin (Fintype.card ι)) : Function.Injective (keyU (r := r) e) := by
  rintro ⟨⟨τ, a, b⟩, hi⟩ ⟨⟨τ', a', b'⟩, hj⟩ h
  simp only [keyU, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have ha : (a : ℕ) = a' := by have := a.isLt; have := a'.isLt; omega
  apply Subtype.ext
  simp only [Prod.mk.injEq]
  exact ⟨e.injective h3, Fin.ext ha, Fin.ext h1⟩

private lemma toMatrix_entry_lemma (β : ι → Matrix (Fin r) (Fin r) ℂ) (i j : UpI ι r) :
    LinearMap.toMatrix' (Lβ β) i j =
      if j.1.1 = i.1.1 ∧ j.1.2.2 = i.1.2.2 then β i.1.1 i.1.2.1 j.1.2.1 else 0 := by
  obtain ⟨⟨τ, a, b⟩, hi⟩ := i
  obtain ⟨⟨τ', a', b'⟩, hj⟩ := j
  rw [LinearMap.toMatrix'_apply]
  simp only [Lβ, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply, Umat, Matrix.of_apply]
  rw [Finset.sum_eq_single a']
  · by_cases h : τ' = τ ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := h
      simp [hj, Pi.single_apply]
    · rw [if_neg h]
      split_ifs with h'
      · simp
      · rw [Pi.single_apply, if_neg, mul_zero]
        intro heq
        apply h
        simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq
        exact ⟨heq.1.symm, heq.2.2.symm⟩
  · intro c _ hc
    split_ifs with h'
    · simp
    · rw [Pi.single_apply, if_neg, mul_zero]
      intro heq
      simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq
      exact hc heq.2.1
  · simp

lemma toMatrix_Lβ_zero (e : ι ≃ Fin (Fintype.card ι)) (β : ι → Matrix (Fin r) (Fin r) ℂ)
    (hβ : ∀ τ, (β τ).BlockTriangular id) (i j : UpI ι r) (hij : keyU e i < keyU e j) :
    LinearMap.toMatrix' (Lβ β) i j = 0 := by
  rw [toMatrix_entry_lemma]
  split_ifs with h
  · obtain ⟨⟨τ, a, b⟩, hi⟩ := i
    obtain ⟨⟨τ', a', b'⟩, hj⟩ := j
    obtain ⟨rfl, rfl⟩ := h
    simp only [keyU, Prod.Lex.toLex_lt_toLex, lt_irrefl, false_or, and_false, or_false,
      true_and] at hij
    apply hβ _
    have := a.isLt; have := a'.isLt
    show (a' : ℕ) < a
    omega
  · rfl

lemma toMatrix_Lβ_diag (β : ι → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id) (i : UpI ι r) :
    LinearMap.toMatrix' (Lβ β) i i = β i.1.1 i.1.2.1 i.1.2.1 := by
  rw [toMatrix_entry_lemma, if_pos ⟨rfl, rfl⟩]

theorem det_Lβ (β : ι → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id) :
    LinearMap.det (Lβ β) = ∏ i : UpI ι r, β i.1.1 i.1.2.1 i.1.2.1 := by
  rw [← LinearMap.det_toMatrix']
  let e := Fintype.equivFin ι
  letI : LinearOrder (UpI ι r) := LinearOrder.lift' (keyU (r := r) e) (keyU_injective e)
  have h := Matrix.det_of_lowerTriangular (LinearMap.toMatrix' (Lβ β)) (fun i j hij =>
    toMatrix_Lβ_zero e β hβ i j hij)
  convert h using 2 with i
  exact (toMatrix_Lβ_diag β hβ i).symm

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ModeHalfStatementPfA
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace ModeHalfA

open Matrix NumberField Complex ReciprocityTheory.ChartRestriction.G.FD Topology Filter
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

noncomputable def sf (p0 : ℕ) (α β : Fin r → ℂ) : ℂ :=
  ∑ k : Fin r, ((sgn p0 (k : ℕ) : ℝ) : ℂ) * α k * conj (β k)

def cl (N : Fin r → Fin r → ℂ) (a : Fin r) : Fin r → ℂ := fun k => N k a

noncomputable def Ag (p0 : ℕ) (hp : p0 ≤ r) (N : Fin r → Fin r → ℂ) : Matrix (Fin p0) (Fin p0) ℂ :=
  Matrix.of fun a b => sf p0 (cl N (Fin.castLE hp a)) (cl N (Fin.castLE hp b))

noncomputable def Ms (p0 : ℕ) (hp : p0 ≤ r) (N : Fin r → Fin r → ℂ) (v : Fin r → ℂ) : ℝ :=
  2 * (∑ a : Fin p0, ∑ b : Fin p0, sf p0 v (cl N (Fin.castLE hp a)) * (Ag p0 hp N)⁻¹ a b *
    conj (sf p0 v (cl N (Fin.castLE hp b)))).re - (sf p0 v v).re

private lemma hermC_eq_dotProduct_upper_bounds (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) :
    hermC τ G u v = u ⬝ᵥ (G.map τ *ᵥ fun b => conj (v b)) := by
  simp only [ReciprocityTheory.ChartRestriction.G.FD.hermC, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, mul_assoc]

private lemma gram_eq_upper_bounds (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (Y : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G Y = Yᵀ * G.map τ * Y.map conj := by
  ext i j
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col,
    Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

private lemma hermC_mulVec_eq_dotProduct_gram (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (Y : Matrix (Fin r) (Fin r) ℂ) (w n : Fin r → ℂ) :
    hermC τ G (Y *ᵥ w) (Y *ᵥ n) = w ⬝ᵥ (gram τ G Y *ᵥ fun b => conj (n b)) := by
  have hc : (fun b => conj ((Y *ᵥ n) b)) = Y.map conj *ᵥ fun b => conj (n b) := by
    funext b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [hermC_eq_dotProduct_upper_bounds, hc, gram_eq_upper_bounds, dotProduct_comm, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, dotProduct_comm, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

private lemma det_ne_zero_of_gram_eq_diagonal_sgn (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (p0 : ℕ)
    (Y : Matrix (Fin r) (Fin r) ℂ)
    (hY : gram τ G Y = diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) : Y.det ≠ 0 := by
  intro h0
  have h1 := congrArg Matrix.det hY
  rw [gram_eq_upper_bounds, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
    Matrix.det_diagonal] at h1
  exact (Finset.prod_ne_zero_iff.mpr fun a _ => by unfold sgn; split_ifs <;> norm_num) h1.symm

theorem maj_chart (X : Data E r) {w : Frame X.Ψ r} {τ : X.Ψ} {Y : Matrix (Fin r) (Fin r) ℂ}
    (hY : FD.gram τ.1 X.Gm Y = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (N : Fin r → Fin r → ℂ) (hw : mat w τ = Y * Matrix.of N) (v : Fin r → ℂ) :
    X.maj w τ v = Ms X.p0 X.p0_le N (Y⁻¹ *ᵥ v) := by
  have hS : ∀ u' n : Fin r → ℂ, hermC τ.1 X.Gm (Y *ᵥ u') (Y *ᵥ n) = sf X.p0 u' n := by
    intro u' n
    rw [hermC_mulVec_eq_dotProduct_gram, hY]
    simp only [sf, dotProduct, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hdetY := det_ne_zero_of_gram_eq_diagonal_sgn τ.1 X.Gm X.p0 Y hY
  have hv : v = Y *ᵥ (Y⁻¹ *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdetY), Matrix.one_mulVec]
  have hcol : ∀ a, FD.col (mat w τ) a = Y *ᵥ cl N a := by
    intro a
    rw [hw]
    funext k
    simp [ReciprocityTheory.ChartRestriction.G.FD.col, cl, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hgp : X.gramPos w τ = Ag X.p0 X.p0_le N := by
    ext a b
    simp only [Data.gramPos, Matrix.submatrix_apply, ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply, Ag]
    rw [hcol, hcol, hS]
  unfold Data.maj Data.posPart Ms
  rw [hgp]
  conv_lhs => rw [hv]
  simp only [hcol, hS]

theorem dom_of_orth (X : Data E r) {u : Frame X.Ψ r} (hu : IsOrth X u) : u ∈ X.dom := by
  intro τ
  have hY := hu τ
  refine ⟨det_ne_zero_of_gram_eq_diagonal_sgn τ.1 X.Gm X.p0 _ hY, fun i => ?_⟩
  have hd : dmin X.Gm u τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [hY, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    simp only [Function.comp_apply, Fin.coe_castLE, psgn, Complex.ofReal_prod]
    exact Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) i
  rw [hd, Complex.ofReal_re]
  have hne : psgn X.p0 i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ => by unfold sgn; split_ifs <;> norm_num
  exact mul_self_pos.mpr hne

theorem maj_orth (X : Data E r) {u : Frame X.Ψ r} (hu : IsOrth X u) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.maj u τ v = ∑ a, ‖((mat u τ)⁻¹ *ᵥ v) a‖ ^ 2 := by
  have hY := hu τ
  set N : Fin r → Fin r → ℂ := fun i j => (1 : Matrix (Fin r) (Fin r) ℂ) i j with hN
  have hw : mat u τ = mat u τ * Matrix.of N := by
    rw [show Matrix.of N = 1 from rfl, Matrix.mul_one]
  rw [maj_chart X hY N hw v]
  set w := (mat u τ)⁻¹ *ᵥ v
  have hsf : ∀ (α : Fin r → ℂ) (b : Fin r), sf X.p0 α (cl N b) = ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) * α b := by
    intro α b
    unfold sf cl
    rw [Finset.sum_eq_single b]
    · simp [hN]
    · intro k _ hk
      simp [hN, Matrix.one_apply_ne hk]
    · intro h
      exact absurd (Finset.mem_univ b) h
  have hAg : Ag X.p0 X.p0_le N = 1 := by
    ext a b
    simp only [Ag, Matrix.of_apply, hsf]
    by_cases hab : a = b
    · subst hab
      simp [cl, hN, sgn]
    · have hne : (Fin.castLE X.p0_le b : Fin r) ≠ Fin.castLE X.p0_le a :=
        fun h => hab (Fin.castLE_injective _ h).symm
      simp [cl, hN, Matrix.one_apply_ne hne, Matrix.one_apply_ne hab]
  have hcast : ∀ g : Fin r → ℝ, ∑ a : Fin X.p0, g (Fin.castLE X.p0_le a) =
      ∑ k : Fin r, if (k : ℕ) < X.p0 then g k else 0 := by
    intro g
    rw [← Finset.sum_filter]
    have hset : Finset.univ.filter (fun k : Fin r => (k : ℕ) < X.p0) =
        Finset.univ.map (Fin.castLEEmb X.p0_le) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro hk
        exact ⟨⟨k, hk⟩, Fin.ext rfl⟩
      · rintro ⟨a, rfl⟩
        exact a.isLt
    rw [hset, Finset.sum_map]
    rfl
  have hinner : ∀ a : Fin X.p0, ∑ b : Fin X.p0, sf X.p0 w (cl N (Fin.castLE X.p0_le a)) *
      (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) a b * conj (sf X.p0 w (cl N (Fin.castLE X.p0_le b))) =
      ((‖w (Fin.castLE X.p0_le a)‖ ^ 2 : ℝ) : ℂ) := by
    intro a
    rw [Finset.sum_eq_single a (fun b _ hb => by rw [Matrix.one_apply_ne' hb, mul_zero, zero_mul])
      (fun h => absurd (Finset.mem_univ a) h)]
    rw [Matrix.one_apply_eq, mul_one, hsf]
    have ha : ((Fin.castLE X.p0_le a : Fin r) : ℕ) < X.p0 := by simp
    simp only [sgn, ha, if_true, Complex.ofReal_one, one_mul]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hww : (sf X.p0 w w).re = ∑ k : Fin r, sgn X.p0 (k : ℕ) * ‖w k‖ ^ 2 := by
    unfold sf
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, Complex.ofReal_re]
  unfold Ms
  rw [hAg, inv_one]
  simp only [hinner]
  rw [← Complex.ofReal_sum, Complex.ofReal_re, hww]
  have hc := hcast (fun k => ‖w k‖ ^ 2)
  beta_reduce at hc
  rw [hc, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold sgn
  split_ifs <;> ring

end ModeHalfA

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

