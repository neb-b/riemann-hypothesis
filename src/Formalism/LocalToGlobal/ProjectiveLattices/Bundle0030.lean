module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ReadProofs
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def TestRd (σ : c.F →+* ℂ) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (ψ : p.R →ₐ[c.F] CAt σ),
    ∃ (k : (U σ).Comp) (x : ((U σ).X k).dom) (u : ℂ), ∀ f ∈ sec Xo c a n,
      cvalR σ (ψ (f p y)) = u * rdU (U σ) f k x.1

def BCEx (σ : c.F →+* ℂ) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (ψ : p.R →ₐ[c.F] CAt σ), ∃ z : FrPt Xo c (CAt σ), FrMap ψ y z

def WtC (σ : c.F →+* ℂ) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec Xo c a n, ∀ (t : Ix Dw → (CAt σ)ˣ) (y y' : FrPt Xo c (CAt σ)),
    FrBor t y y' → evR Xo c f y' = wchar (ex Dw a n) t * evR Xo c f y

section Adelic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def frInv {Ψ : Finset (E →+* ℂ)} (b : Frame Ψ r) : Frame Ψ r := fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)

theorem mat_frInv {Ψ : Finset (E →+* ℂ)} (b : Frame Ψ r) (τ : Ψ) : mat (frInv b) τ = (mat b τ)⁻¹ := rfl

theorem mat_rmul {Ψ : Finset (E →+* ℂ)} (x b : Frame Ψ r) (τ : Ψ) : mat (rmul x b) τ = mat x τ * mat b τ := rfl

theorem eq_zero_of_orbit (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x)
    (hΓ : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, P (lact γ x) = X.χ la γ * P x)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (hz : rmul (lact γ x) b ∈ X.dom) (h0 : P (rmul (lact γ x) b) = 0) : P x = 0 := by
  have hbinv : frInv b ∈ Bor X.Ψ r := by
    intro τ
    obtain ⟨hdet, htri⟩ := hb τ
    have hu : IsUnit (mat b τ).det := isUnit_iff_ne_zero.2 hdet
    refine ⟨?_, ?_⟩
    · rw [mat_frInv]
      exact (Matrix.isUnit_nonsing_inv_det_iff.2 hu).ne_zero
    · intro i j hij
      haveI : Invertible (mat b τ) := Matrix.invertibleOfIsUnitDet _ hu
      have hBT : (mat b τ).BlockTriangular id := fun i' j' h' => htri i' j' h'
      exact Matrix.blockTriangular_inv_of_blockTriangular hBT hij
  have hrm : rmul (rmul (lact γ x) b) (frInv b) = lact γ x := by
    funext τ
    show mat (rmul (lact γ x) b) τ * mat (frInv b) τ = mat (lact γ x) τ
    rw [mat_rmul, mat_frInv, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hb τ).1), Matrix.mul_one]
  have h1 : P (lact γ x) = 0 := by
    have h2 := hB _ hz (frInv b) hbinv
    rw [hrm, h0, mul_zero] at h2
    exact h2
  rw [hΓ γ hγ x hx] at h1
  obtain ⟨n, hn, hχ⟩ := X.χ_fin la
  have hne : X.χ la γ ≠ 0 := by
    intro h
    have h3 := hχ γ hγ
    rw [h, zero_pow hn.ne'] at h3
    exact zero_ne_one h3
  exact (mul_eq_zero.1 h1).resolve_left hne

theorem eqv_holSub {Comp : Type} (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r) {P : FDSec X}
    (hP : P ∈ holSub X la) :
    (∀ k, ∀ x ∈ (X k).dom, ∀ b ∈ Bor (X k).Ψ r, P k (rmul x b) = bchar (la k) b * P k x) ∧
      (∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, P k (lact γ x) = (X k).χ (la k) γ * P k x) := by
  replace hP : P ∈ Submodule.span ℂ {Q | IsHolCusp X la Q} := hP
  induction hP using Submodule.span_induction with
  | mem Q hQ =>
    have hQ' : IsHolCusp X la Q := hQ
    exact ⟨fun k x hx b hb => (hQ' k).1.1.2.1 x hx b hb, fun k γ hγ x hx => (hQ' k).1.1.2.2 γ hγ x hx⟩
  | zero => exact ⟨fun k x _ b _ => by simp, fun k γ _ x _ => by simp⟩
  | add Q R _ _ hQ hR =>
    refine ⟨fun k x hx b hb => ?_, fun k γ hγ x hx => ?_⟩
    · simp only [Pi.add_apply]
      rw [hQ.1 k x hx b hb, hR.1 k x hx b hb]
      ring
    · simp only [Pi.add_apply]
      rw [hQ.2 k γ hγ x hx, hR.2 k γ hγ x hx]
      ring
  | smul a Q _ hQ =>
    refine ⟨fun k x hx b hb => ?_, fun k γ hγ x hx => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [hQ.1 k x hx b hb]
      ring
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [hQ.2 k γ hγ x hx]
      ring

variable {D : D7} {Comp : Type} {X : Comp → Data E r} (V : HSp D) (dict : GA D V → Σ k, Frame (X k).Ψ r)
  (mu : GA D V → ℂ)

def AdelAut : Prop :=
  ∀ (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X), IsHolCusp X la P →
    (∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g) ∧ Continuous (adel V dict mu P)

def QuotSupp : Prop :=
  ∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) → onQ V φ =ᵐ[muQ1 V] 0 → ∀ g, φ g = 0

variable {V dict mu}

theorem adelAut_holSub (h : AdelAut V dict mu) (la : ∀ k, Wt (X k).Ψ r) {P : FDSec X} (hP : P ∈ holSub X la) :
    (∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g) ∧ Continuous (adel V dict mu P) := by
  replace hP : P ∈ Submodule.span ℂ {Q | IsHolCusp X la Q} := hP
  induction hP using Submodule.span_induction with
  | mem Q hQ => exact h la Q hQ
  | zero =>
    refine ⟨fun γ _ g => ?_, ?_⟩
    · simp only [map_zero, Pi.zero_apply]
    · rw [map_zero]
      exact continuous_const
  | add Q R _ _ hQ hR =>
    refine ⟨fun γ hγ g => ?_, ?_⟩
    · simp only [map_add (f := _), Pi.add_apply, hQ.1 γ hγ g, hR.1 γ hγ g]
    · rw [map_add (f := _)]
      exact hQ.2.add hR.2
  | smul a Q _ hQ =>
    refine ⟨fun γ hγ g => ?_, ?_⟩
    · simp only [map_smul, Pi.smul_apply, hQ.1 γ hγ g]
    · rw [map_smul]
      exact hQ.2.const_smul a

theorem onQ_eq_lift (φ : GA D V → ℂ) (hL : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) :
    onQ V φ = Quotient.lift φ (fun a b hab => by
      have h' : b * a⁻¹ ∈ GQ V := QuotientGroup.rightRel_apply.1 hab
      have := hL _ h' a
      rw [inv_mul_cancel_right] at this
      exact this.symm) := by
  funext q
  exact congrArg (Quotient.lift φ _) (Quotient.out_eq q)

theorem adelMeas_of_aut {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {σ : c.F →+* ℂ} {V : HSp D}
    {dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r} {mu : GA D V → ℂ}
    (h : AdelAut V dict mu) : AdelMeas U σ V dict mu := by
  intro la P hP
  obtain ⟨hL, hc⟩ := h la P hP
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  rw [onQ_eq_lift _ hL]
  refine Measurable.aestronglyMeasurable ?_
  exact measurable_from_quotient.2 hc.measurable

theorem aeDom_of_aut {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {σ : c.F →+* ℂ} {V : HSp D}
    {dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r} {mu : GA D V → ℂ} {Kf : Subgroup (GA D V)}
    {th : ∀ k, ((U σ).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hA : AdelAut V dict mu) (hQ : QuotSupp V) (hmu : MuUnit V dict mu) (hd : DictIsUnif V dict Kf th hr) :
    AeDom U σ V dict mu := by
  intro la P hP h0 k x hx
  have hA' := adelAut_holSub hA la hP
  have hz : ∀ g, adel V dict mu P g = 0 := hQ _ hA'.2 hA'.1 h0
  obtain ⟨-, -, -, hdom, hsurj, -⟩ := hd
  obtain ⟨g, γ, hγ, b, hb, hg⟩ := hsurj k x hx
  have hm : mu g ≠ 0 := by
    intro h
    have h1 := hmu.2.1 g
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have h1 : mu g * P (dict g).1 (dict g).2 = 0 := hz g
  have h2 : P (dict g).1 (dict g).2 = 0 := (mul_eq_zero.1 h1).resolve_left hm
  have h3 := hdom g
  rw [hg] at h2 h3
  have hE := eqv_holSub (U σ).X la hP
  exact eq_zero_of_orbit ((U σ).X k) (la k) (P k) (hE.1 k) (hE.2 k) hx hγ hb h3 h2

end Adelic

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.RegularityR1ValuedPoints
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def IntAlg (f : Rul Xo c) : Prop := ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f

theorem intAlg_zero : IntAlg (0 : Rul Xo c) := by
  intro la v hv
  simp only [valSet, Set.mem_setOf_eq] at hv
  obtain ⟨y, rfl⟩ := hv
  unfold vAtV
  obtain ⟨⟨w, q⟩, T, io, e, ho, z, hz, eta, -, hw⟩ := y
  unfold profI at hw
  obtain ⟨rfl, -⟩ := Prod.mk.inj hw
  simp [evI, evR, evalAt, nval]

theorem intAlg_add {f g : Rul Xo c} (hf : IntAlg f) (hg : IntAlg g) : IntAlg (f + g) := fun la v hv =>
  (le_min (hf la v hv) (hg la v hv)).trans ((isVal_valSet la v hv).add f g)

theorem intAlg_smul (a : 𝓞 c.F) {f : Rul Xo c} (hf : IntAlg f) : IntAlg (a • f) := fun la v hv => by
  have e : (a • f : Rul Xo c) = (a : c.F) • f := rfl
  rw [e]
  by_cases ha : (a : c.F) = 0
  · set_option synthInstance.maxHeartbeats 200000 in
      rw [ha, zero_smul, (isVal_valSet la v hv).zero]
    exact le_top
  · rw [(isVal_valSet la v hv).smul _ _ ha]
    exact add_nonneg (by exact_mod_cast vAdd_int_nonneg la ha) (hf la v hv)

theorem intAlg_span {s : Set (Rul Xo c)} (hs : ∀ f ∈ s, IntAlg f) {f : Rul Xo c}
    (hf : f ∈ Submodule.span (𝓞 c.F) s) : IntAlg f := by
  induction hf using Submodule.span_induction with
  | mem x h => exact hs x h
  | zero => exact intAlg_zero
  | add x y _ _ hx hy => exact intAlg_add hx hy
  | smul a x _ hx => exact intAlg_smul a hx


variable (Xo c) in
def RegularityR1ValuedPoints (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c))
    (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop) (PY : HeightOneSpectrum (𝓞 c.F) → Type)
    (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ C a n, IntAlg f →
    ∀ la (y : PtV Xo c cls (PY la) (lies la) la), 0 ≤ vAtV y f

theorem ramIdx_nonneg {Ω : Type} [Field Ω] [Algebra c.F Ω] {v : AddValuation Ω (WithTop ℤ)}
    {la : HeightOneSpectrum (𝓞 c.F)} (ho : IsOver (K := c.F) v la) : 0 ≤ ramIdx (K := c.F) v la := by
  unfold ramIdx
  have hpos : ∀ n ∈ {n : ℤ | ∃ a ∈ la.asIdeal, a ≠ 0 ∧ v ((algebraMap c.F Ω) ↑a) = ↑n}, 0 ≤ n := by
    rintro n ⟨a, ha, -, hv⟩
    have h := (ho a).mpr ha
    rw [hv] at h
    exact_mod_cast h.le
  rcases Set.eq_empty_or_nonempty
      {n : ℤ | ∃ a ∈ la.asIdeal, a ≠ 0 ∧ v ((algebraMap c.F Ω) ↑a) = ↑n} with he | hne
  · rw [he, Int.csInf_empty]
  · exact hpos _ (Int.csInf_mem hne ⟨0, hpos⟩)

variable (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
  (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c))
  (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop) (PY : HeightOneSpectrum (𝓞 c.F) → Type)
  (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop)

theorem ord_nonneg_of [Nonempty (HeightOneSpectrum (𝓞 c.F))]
    (hT : OrdTie h δ cls PY lies) (hTQ : OrdTieQ h δ) (hR1 : RegularityR1ValuedPoints Xo c C cls PY lies) (hR1Q : RegularityR1Quotient Xo c C)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {F : Rul Xo c} (hFs : F ∈ sec Xo c a n) (hFC : F ∈ C a n) (hF : IntAlg F)
    {Z : Comp Xo c} {v : AddValuation (Om Z) (WithTop ℤ)} (hd : IsNormDiscrete v)
    (hv : (∃ la, IsOver (K := c.F) v la) ∨ IsTrivOn c.F v) (hne : evC h Z F ≠ 0) :
    0 ≤ ordC (δ Z v) v (wtZ a n) (valC h a n F Z) := by
  have key : (0 : EReal) ≤ (((ordC (δ Z v) v (wtZ a n) (valC h a n F Z) : ℤ) : ℝ) : EReal) := by
    rcases hv with ⟨la, ho⟩ | ht
    · obtain ⟨y, hy⟩ := hT Z v la hd ho
      rw [hy a n F hFs hne]
      exact mul_nonneg (by exact_mod_cast ramIdx_nonneg ho) (hR1 a n F hFC hF la y)
    · obtain ⟨q, hq⟩ := hTQ Z v hd ht
      rw [hq a n F hFs hne]
      obtain ⟨la⟩ := ‹Nonempty (HeightOneSpectrum (𝓞 c.F))›
      exact hR1Q a n F hFC ⟨la, hF la⟩ q
  exact_mod_cast key

theorem mem_of_mem_span_int (S : Submodule c.F (Rul Xo c)) {s : Set (Rul Xo c)} (hs : s ⊆ S) {F : Rul Xo c}
    (hF : F ∈ Submodule.span (𝓞 c.F) s) : F ∈ S := by
  induction hF using Submodule.span_induction with
  | mem x h => exact hs h
  | zero => exact S.zero_mem
  | add x y _ _ hx hy => exact S.add_mem hx hy
  | smul a x _ hx => exact S.smul_mem (a : c.F) hx


omit δ C cls PY lies in
theorem exists_of_mem_span_valG {u : WtR E} {ι : Type} {R : ι → Rul Xo c} {x : ∀ Z : Comp Xo c, AC Z}
    (hx : x ∈ (letI : ∀ Z : Comp Xo c, Module (𝓞 c.F) (AC Z) := fun _ => Algebra.toModule
      Submodule.span (𝓞 c.F) (Set.range fun k => valG h u (R k)))) :
    ∃ F ∈ Submodule.span (𝓞 c.F) (Set.range R), x = valG h u F := by
  try dsimp only at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    exact ⟨R k, Submodule.subset_span ⟨k, rfl⟩, rfl⟩
  | zero => exact ⟨0, zero_mem _, funext fun Z => (valC_zero h u.1 u.2 Z).symm⟩
  | add y z _ _ hy hz =>
    obtain ⟨F, hF, rfl⟩ := hy
    obtain ⟨G, hG, rfl⟩ := hz
    exact ⟨F + G, add_mem hF hG, funext fun Z => (valC_add h u.1 u.2 F G Z).symm⟩
  | smul a y _ hy =>
    obtain ⟨F, hF, rfl⟩ := hy
    refine ⟨a • F, Submodule.smul_mem _ a hF, funext fun Z => ?_⟩
    refine (Algebra.smul_def a (valG h u F Z)).trans ?_
    rw [IsScalarTower.algebraMap_apply (𝓞 c.F) c.F (AC Z)]
    exact (valC_smul_ct h u.1 u.2 (a : c.F) F Z).symm

section LawA2Of

variable [Fintype (Comp Xo c)]
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)

end LawA2Of

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.SecPtRed
section
noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

section Ev

variable (Xr : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)
  {K2 : Type} [Field K2] (ev : Rp Xr la N →+* K2) (hu : IsUnit (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec Xr la w 0)))

lemma liftEv_alg (r : Rp Xr la N) :
    IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec Xr la w 0) hu (algebraMap (Rp Xr la N) (Lw Xr la w) r) = ev r :=
  IsLocalization.lift_eq _ r

lemma liftEv_w0inv :
    IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec Xr la w 0) hu (w0inv Xr la w) = (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec Xr la w 0))⁻¹ := by
  have := congrArg (IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec Xr la w 0) hu) (section_mul_inverse_eq_one Xr la w)
  rw [map_mul, liftEv_alg, map_one] at this
  exact eq_inv_of_mul_eq_one_right this

lemma liftEv_frac (k : ℕ) (g : Rp Xr la N) :
    IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec Xr la w 0) hu (frac Xr la w k g) = ev g * (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec Xr la w 0))⁻¹ ^ k := by
  rw [frac_apply, map_mul, map_pow, liftEv_alg, liftEv_w0inv]

end Ev

section Std

variable {Xr : PJ D B P j} {la : HeightOneSpectrum (𝓞 B.KO)} {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData Xr ka wL wF}

theorem isUnif_of_ring (hfd : FiniteDimensional (Kp Xr la G.N) (OsK Xr la G.w)) :
    IsUnif (OsK Xr la G.w) (unifO Xr la G.N) := by
  have : Algebra.IsIntegral (Kp Xr la G.N) (OsK Xr la G.w) := Algebra.IsIntegral.of_finite _ _
  exact isUnif_of_field (Kp Xr la G.N)
    (Op.irreducible_map Xr la G.N (Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (Xr.Ol la))))

theorem kp_charZero' : CharZero (Kp Xr la G.N) := by
  have := Kl_charZero Xr la
  exact charZero_of_injective_algebraMap (algebraMap (Xr.Kl la) (Kp Xr la G.N)).injective

theorem isDVRAt_of_ring (hfd : FiniteDimensional (Kp Xr la G.N) (OsK Xr la G.w)) (hred : IsReduced (OsK Xr la G.w))
    (ζ : PtsG G la) : IsDVRAt ζ := by
  have := kp_charZero' (la := la) (G := G)
  exact (integralClosure_dvr' (Op Xr la G.N) (Kp Xr la G.N) (OsK Xr la G.w)).2 ζ

theorem loc_charZero (h : IsUnif (OsK Xr la G.w) (unifO Xr la G.N)) (ζ : PtsG G la) [IsDVRAt ζ] :
    CharZero (Loc ζ) := by
  have hK := kp_charZero' (la := la) (G := G)
  have hO : CharZero (Op Xr la G.N) :=
    (RingHom.charZero_iff (IsFractionRing.injective (Op Xr la G.N) (Kp Xr la G.N))).2 hK
  refine charZero_of_injective_algebraMap (R := Op Xr la G.N) ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 h.irreducible
  rw [map_mul, map_pow] at ha
  have hb : algebraMap (Op Xr la G.N) (Loc ζ) (unifO Xr la G.N) ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply (Op Xr la G.N) ↥(As (Op Xr la G.N) (OsK Xr la G.w)) (Loc ζ)]
    intro h0
    exact vL_ne_top ζ (unif_mem_nonZeroDivisors h) ((vL_eq_top_iff ζ _).2 h0)
  exact (mul_ne_zero ((u.isUnit.map (algebraMap (Op Xr la G.N) (Loc ζ))).ne_zero) (pow_ne_zero n hb)) ha

end Std

variable {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}

theorem addVal_map_of_unr {W V : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (ι : W →+* V) (hunr : ∃ ϖ : W, Irreducible ϖ ∧ Irreducible (ι ϖ)) (r : W) :
    IsDiscreteValuationRing.addVal V (ι r) = IsDiscreteValuationRing.addVal W r := by
  obtain ⟨ϖ, hϖ, hιϖ⟩ := hunr
  by_cases hr : r = 0
  · subst hr
    rw [map_zero, IsDiscreteValuationRing.addVal_zero, IsDiscreteValuationRing.addVal_zero]
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  rw [IsDiscreteValuationRing.addVal_def' u hϖ n, map_mul, map_pow]
  exact IsDiscreteValuationRing.addVal_def' ((u.isUnit.map ι).unit) hιϖ n

theorem fromW_of {ζ : PtsG G la} [IsDVRAt ζ] {y : E.Pt' la}
    (h : IsUnif (OsK (xplus X E hM) la G.w) (unifO (xplus X E hM) la G.N))
    (T : CDVR) (ι : Loc ζ →+* T.V) (hloc : IsLocalHom ι) (hunr : ∃ ϖ : Loc ζ, Irreducible ϖ ∧ Irreducible (ι ϖ))
    (ev : Rp (xplus X E hM) la G.N →+* T.Fr) (hu : IsUnit (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0)))
    (hv : ∀ (w : WeightFamilies.Wt D j) (F : B.Cusp j w), E.vAt' la y (X.inc w F) =
      nval T.V (ep (unifO (xplus X E hM) la G.N) ζ) (ev (emb (xplus X E hM) la G.N (X.inc w F))))
    (hdeg : ∀ x : ↥(Frac0 (xplus X E hM) la G.w),
      IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0) hu (x : Lw (xplus X E hM) la G.w) =
        phiAt ζ T.Fr ι h (addVal_map_of_unr ι hunr) (toOsK (xplus X E hM) la G.w x)) :
    Nonempty (FromW ζ y) := by
  have hι : AddValPres ζ ι := addVal_map_of_unr ι hunr
  have honS : ∀ i : Fin (WeightFamilies.dimY D j), ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w i.succ) = 0 := by
    intro i
    have h1 := hdeg (sfr (xplus X E hM) la G.w i.succ)
    rw [(toOsK_eq_zero_iff _ _ _ _).2 (sfr_succ_mem_Jid _ _ _ i), map_zero, coe_sfr, liftEv_frac] at h1
    exact (mul_eq_zero.1 h1).resolve_right (pow_ne_zero _ (inv_ne_zero hu.ne_zero))
  have hord : ∀ x : ↥(Frac0 (xplus X E hM) la G.w),
      toE (ord (unifO (xplus X E hM) la G.N) ζ (toOsK (xplus X E hM) la G.w x)) =
        nval T.V 1 (IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0) hu (x : Lw (xplus X E hM) la G.w)) := by
    intro x
    rw [hdeg x]
    exact toE_ord_eq T.Fr h hι _
  let sp : SecPt ζ y :=
    { T := T, ep_pos := ep_pos ζ h, ev := ev, hv := hv, onS := honS, s0 := hu, ord := hord }
  have hevW : ∀ (x : ↥(Frac0 (xplus X E hM) la G.w))
      (a : ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))),
      toOsK (xplus X E hM) la G.w x = (a : OsK (xplus X E hM) la G.w) →
      IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0) hu (x : Lw (xplus X E hM) la G.w) =
        algebraMap T.V T.Fr (ι (algebraMap _ (Loc ζ) a)) := by
    intro x a hxa
    rw [hdeg x, hxa]
    exact phiAt_coe T.Fr h hι a
  exact ⟨{ toSecPt := sp
           ι := ι
           loc := hloc
           unr := hunr
           evW := hevW }⟩

end Formalism.L2.Pj
end
end

