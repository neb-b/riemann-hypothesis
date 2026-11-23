module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0497
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FjCauchyBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bNormHolds
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPerHolOne
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.PeriodSpan

variable {X : Scheme.{0}} (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X)

def torusPts (E : TorusExtension ((Over.pullback y).obj G)) : Set (Over.mk y ⟶ G) :=
  letI := E.addCommGroup
  {x | ∃ t : Over.mk (𝟙 (Sp ℂ)) ⟶ splitTorus (Spec (.of ℂ)) E.X, (t ≫ E.i).left ≫ pullback.fst G.hom y = x.left}

def IsPerHol (ψ : ℂ → (Over.mk y ⟶ G)) : Prop :=
  (∀ s t, ψ (s + t) = ψ s * ψ t) ∧ IsHolTo Set.univ (fun s => (ψ s).left) ∧
    ψ (2 * Real.pi * Complex.I) = 1

def perHolSub : Subgroup (Over.mk y ⟶ G) :=
  Subgroup.closure (⋃ (ψ : ℂ → (Over.mk y ⟶ G)) (_ : IsPerHol G y ψ), Set.range ψ)

end GlobalTheory.PeriodSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicFlowMajorantCauchySchwarz
section
open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom
open scoped ComplexConjugate

namespace GlobalTheory.CuspFrom.FlowMaj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma majForm_conj {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    X.Hf x τ w u = conj (X.Hf x τ u w) := by
  rw [X.Hf_eq_jp, X.Hf_eq_jp, hermC_conj τ.1 X.Gm_herm, X.hermC_jp_left hx]

lemma majForm_sub_smul (x : Frame X.Ψ r) (τ : X.Ψ) (a : ℂ) (v e w : Fin r → ℂ) :
    X.Hf x τ (v - a • e) w = X.Hf x τ v w - a * X.Hf x τ e w := by
  simp only [X.Hf_eq_jp, X.jp_sub, X.jp_smul, hermC_sub_left, hermC_smul_left]

lemma maj_zero {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) : X.maj x τ 0 = 0 := by
  have h := X.Hf_self hx τ 0
  rw [X.Hf_eq_jp, hermC_zero_right] at h
  exact_mod_cast h.symm

lemma maj_nonneg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) : 0 ≤ X.maj x τ v := by
  by_cases hv : v = 0
  · rw [hv, maj_zero X hx]
  · exact (X.maj_pos hx τ hv).le

lemma maj_split {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (a : ℂ) (e u : Fin r → ℂ)
    (h : X.Hf x τ u e = 0) : X.maj x τ (u + a • e) = X.maj x τ u + ‖a‖ ^ 2 * X.maj x τ e := by
  have h' : X.Hf x τ e u = 0 := by rw [majForm_conj X hx, h, map_zero]
  have h1 := X.Hf_self hx τ (u + a • e)
  have h2 := X.Hf_self hx τ u
  have h3 := X.Hf_self hx τ e
  simp only [X.Hf_eq_jp] at h h' h1 h2 h3
  simp only [X.jp_add, X.jp_smul, hermC_add_left, hermC_add_right, hermC_smul_left, hermC_smul_right,
    h, h', h2, h3] at h1
  have h4 : a * conj a = ((‖a‖ : ℝ) : ℂ) ^ 2 := Complex.mul_conj' a
  have h5 : ((X.maj x τ (u + a • e) : ℝ) : ℂ) = ((X.maj x τ u + ‖a‖ ^ 2 * X.maj x τ e : ℝ) : ℂ) := by
    rw [← h1]
    push_cast
    linear_combination (X.maj x τ e : ℂ) * h4
  exact_mod_cast h5

lemma majForm_perp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) {e : Fin r → ℂ} (he : e ≠ 0) :
    X.Hf x τ (v - (X.Hf x τ v e / X.Hf x τ e e) • e) e = 0 := by
  have h0 : X.Hf x τ e e ≠ 0 := by
    rw [X.Hf_self hx]
    exact_mod_cast (X.maj_pos hx τ he).ne'
  rw [majForm_sub_smul, div_mul_cancel₀ _ h0, sub_self]

lemma majForm_cs {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v w : Fin r → ℂ) :
    ‖X.Hf x τ v w‖ ^ 2 ≤ X.maj x τ v * X.maj x τ w := by
  by_cases hw : w = 0
  · rw [hw, maj_zero X hx, X.Hf_eq_jp, hermC_zero_right]
    simp
  have hp := X.maj_pos hx τ hw
  have h1 := maj_split X hx τ (X.Hf x τ v w / X.Hf x τ w w) w _ (majForm_perp X hx τ v hw)
  rw [sub_add_cancel] at h1
  have h2 := maj_nonneg X hx τ (v - (X.Hf x τ v w / X.Hf x τ w w) • w)
  have h3 : ‖X.Hf x τ v w / X.Hf x τ w w‖ ^ 2 * X.maj x τ w * X.maj x τ w = ‖X.Hf x τ v w‖ ^ 2 := by
    rw [norm_div, X.Hf_self hx τ w, Complex.norm_real, Real.norm_of_nonneg hp.le]
    field_simp
  rw [← h3]
  exact mul_le_mul_of_nonneg_right (by linarith) hp.le

lemma maj_jp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.maj x τ (X.jp x τ v) = X.maj x τ v := by
  have h1 := X.Hf_self hx τ (X.jp x τ v)
  have h2 := X.Hf_self hx τ v
  rw [X.Hf_eq_jp, X.hermC_jp_jp hx, ← X.Hf_eq_jp, h2] at h1
  exact_mod_cast h1.symm

lemma herm_cs {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v w : Fin r → ℂ) :
    ‖hermC τ.1 X.Gm v w‖ ^ 2 ≤ X.maj x τ v * X.maj x τ w := by
  have h := majForm_cs X hx τ (X.jp x τ v) w
  rwa [X.Hf_eq_jp, X.jp_jp hx, maj_jp X hx] at h

lemma maj_flow {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ)
    (hxs : X.flow ξ s x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) (hv : hermC τ.1 X.Gm v (Data.emb τ.1 ξ) = 0) :
    X.maj (X.flow ξ s x) τ v = X.maj x τ v +
      ‖X.Hf x τ v (Data.emb τ.1 ξ) / X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ ^ 2 *
        (X.maj (X.flow ξ s x) τ (Data.emb τ.1 ξ) - X.maj x τ (Data.emb τ.1 ξ)) := by
  have hiso : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := by
    rw [← emb_herm, hξ.2.1, map_zero]
  have he : Data.emb τ.1 ξ ≠ 0 := emb_ne_zero τ.1 hξ.2.2
  have hH := majForm_perp X hx τ v he
  set a := X.Hf x τ v (Data.emb τ.1 ξ) / X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) with ha
  set u := v - a • Data.emb τ.1 ξ with hu
  have hu0 : hermC τ.1 X.Gm u (Data.emb τ.1 ξ) = 0 := by
    rw [hu, hermC_sub_left, hermC_smul_left, hv, hiso, mul_zero, sub_zero]
  have hp : hermC τ.1 X.Gm (X.ppos x τ u) (Data.emb τ.1 ξ) = 0 := by
    have h := hH
    rw [X.Hf_eq_two_ppos, hu0, sub_zero] at h
    exact (mul_eq_zero.mp h).resolve_left two_ne_zero
  have hpp := Data.ppos_flow X ξ τ hx s hxs u hu0 hp
  have hHy : ∀ w, X.Hf (X.flow ξ s x) τ u w = X.Hf x τ u w := fun w => by
    rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, hpp]
  have hm : X.maj (X.flow ξ s x) τ u = X.maj x τ u := by
    have h := hHy u
    rw [X.Hf_self hxs, X.Hf_self hx] at h
    exact_mod_cast h
  have h1 := maj_split X hx τ a _ u hH
  have h2 := maj_split X hxs τ a _ u ((hHy _).trans hH)
  rw [hu, sub_add_cancel, ← hu] at h1 h2
  rw [h1, h2, hm]
  ring

end GlobalTheory.CuspFrom.FlowMaj

namespace GlobalTheory.CuspFrom

theorem flowMajSt_holds : FlowMajSt := fun _ _ _ _ _ X =>
  ⟨fun _ hξ _ hx s hxs τ v hv => FlowMaj.maj_flow X hξ hx s hxs τ v hv,
    fun _ hx τ v w => ⟨FlowMaj.herm_cs X hx τ v w, FlowMaj.majForm_cs X hx τ v w⟩⟩

end GlobalTheory.CuspFrom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchEqOneOfWchar
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

theorem kch_eq_one_of_wchar {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {S : Type} [CommRing S] (t : Ix Dw → Sˣ)
    (h : wchar (Formalism.L2.Pj.ex Dw (fun _ => 1) 0) t = wchar (Formalism.L2.Pj.ex Dw (fun _ => 0) 2) t) : kch t = 1 := by
  rw [kch_eq, mul_inv_eq_one]
  apply Units.ext
  simp only [wchar, Fintype.prod_option, Formalism.L2.Pj.ex, pow_zero, pow_one, one_mul, Finset.prod_const_one,
    mul_one] at h
  rw [Units.coe_prod, Units.val_pow_eq_pow_val]
  exact h

theorem rootVal_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)), Formalism.L2.PjFree.GoodEmb c σ → ModelBase M → NegXi M → FramesOK e F M un → ∀ (y : FrPt Xo c (CAt σ)) (v v' : ℂ), RootVal (unfOf e F M un) y v → RootVal (unfOf e F M un) y v' → v = v' := by
  intro E _ _ _ H Dw l Xo c σ g e F r M un hσ hM hN hun y v v' hv hv'
  obtain ⟨k, x, t, ht, rfl⟩ := hv
  obtain ⟨k', x', t', ht', rfl⟩ := hv'
  obtain ⟨-, hmul, hinv, huniq⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)
  have h0 : FrBor (t * t'⁻¹) (un k x) (un k' x') := hmul _ _ _ _ _ ht (hinv _ _ _ ht')
  obtain ⟨γ, hγ, b, hb, heq⟩ := (fibre_unfOf e F M un hun hM
    (GlobalTheory.FibreFlag.fibTri E H Dw l Xo c σ g e F r M hσ hM hN) k k' x x').1 ⟨_, h0⟩
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 heq
  have h3 : x'.1 = rmul (lact γ x.1) b := eq_of_heq h2
  have hxg : lact γ x.1 ∈ (M.X k').dom := (hM.domStab k' x.1 x.2).2 γ hγ
  obtain ⟨t1, ht1, hw1⟩ := hun.2.2.1 k' γ hγ x hxg
  have hxb : rmul (⟨lact γ x.1, hxg⟩ : (M.X k').dom).1 b ∈ (M.X k').dom := by
    have hx2 := x'.2
    rw [h3] at hx2
    exact hx2
  obtain ⟨t2, ht2, hw2⟩ := hun.2.1 k' ⟨lact γ x.1, hxg⟩ b hb hxb
  have hx' : (⟨rmul (lact γ x.1) b, hxb⟩ : (M.X k').dom) = x' := Subtype.ext h3.symm
  rw [hx'] at ht2
  have h12 : t * t'⁻¹ = t1 * t2 := huniq _ _ _ _ h0 (hmul _ _ _ _ _ ht1 ht2)
  have d1 : Formalism.L2.Pj.Dom (fun _ : (E →+* ℂ) × ℕ => 1) 0 := ⟨fun _ => antitone_const, by decide⟩
  have d2 : Formalism.L2.Pj.Dom (fun _ : (E →+* ℂ) × ℕ => 0) 2 := ⟨fun _ => antitone_const, by decide⟩
  have k1 : kch t1 = 1 := kch_eq_one_of_wchar t1 ((hw1 _ _ d1).trans (hw1 _ _ d2).symm)
  have hla : Formalism.L2.PjFree.laU (unfOf e F M un) (fun _ => 1) 0 k' =
      Formalism.L2.PjFree.laU (unfOf e F M un) (fun _ => 0) 2 k' := by
    funext τ j
    simp only [Formalism.L2.PjFree.laU]
    split_ifs <;> simp
  have k2 : kch t2 = 1 :=
    kch_eq_one_of_wchar t2 ((hw2 _ _ d1).trans ((congrArg (fun la => bchar la b) hla).trans (hw2 _ _ d2).symm))
  have hk := congrArg kch h12
  rw [kch_mul, kch_mul, kch_inv, k1, k2, one_mul, mul_inv_eq_one] at hk
  rw [hk]

end GlobalTheory.KeyFourth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KoecherPrincipleFlagDomainFrequenciesNonneg
section
open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom Filter Topology

namespace GlobalTheory.Koecher

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)


open MajorantConjugateTransfer TwoSidedBoostBounds MinimumGrowthBounds FractionalSliceDomains in
theorem fj_le_slice (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) (ξ : Fin r → E) (hξ : X.IsIso ξ)
    (ν : X.Ψ → ℝ) (x : Frame X.Ψ r) (hx : x ∈ X.dom) (y : X.Ψ → ℝ) (M : ℝ)
    (hy : ∀ τ, 0 < X.tt ξ x τ + y τ)
    (hM : ∀ u : X.Ψ → ℝ, ‖P (X.flow ξ (fun τ => (u τ : ℂ) + (y τ : ℂ) * Complex.I) x)‖ ≤ M) :
    ‖X.fj la ξ ν P x‖ * Real.exp (-4 * Real.pi * ∑ τ, ν τ * y τ) ≤ M := by
  classical
  obtain ⟨bs, hω⟩ := FlowMeanContinuity.exists_basis X la
  have hωp : ∀ j, bs j ∈ X.periods la := by
    intro j
    have : bs j ∈ Submodule.span ℤ (Set.range bs) := Submodule.subset_span ⟨j, rfl⟩
    rw [hω] at this
    exact this
  have hrepr : ∀ (v : X.Ψ → ℝ) τ, ∑ j, bs.repr v j * bs j τ = v τ := by
    intro v τ
    conv_rhs => rw [← bs.sum_repr v]
    simp [Finset.sum_apply, mul_comm]
  by_cases hf : ∀ j, ∃ k : ℤ, 2 * ∑ τ, ν τ * bs j τ = k
  swap
  · have h0 : X.fj la ξ ν P x = 0 := by
      unfold Data.fj
      rw [if_neg]
      intro hall
      exact hf fun j => hall _ (hωp j)
    rw [h0, norm_zero, zero_mul]
    exact (norm_nonneg _).trans (hM 0)
  choose k hk using hf
  rw [FlowMeanContinuity.fj_eq_fourCoeff X la P hP hξ hx bs hω ν k hk]
  change ‖ReciprocityTheory.L2DbarEstimates.Y.fourCoeff (hfun X P ξ x bs) 0 k‖ * _ ≤ _
  have hm : ∀ τ, 0 < X.maj x τ (Data.emb τ.1 ξ) :=
    fun τ => X.maj_pos hx τ (emb_ne_zero τ.1 hξ.2.2)
  have hc := c_pos X
  set b' : Fin (Fintype.card X.Ψ) → ℝ := fun j => bs.repr y j with hb'
  have hb'ω : ∀ τ, ∑ j, b' j * bs j τ = y τ := hrepr y
  have hb'Ω : b' ∈ FractionalSliceDomains.Om X ξ x bs := by
    show (fun τ => ∑ j, b' j * bs j τ) ∈ AdmissibleHermitianColumns.admissibleImaginary X ξ x
    rw [mem_admissibleImaginary_iff X hx hξ]
    intro τ
    rw [hb'ω]
    have h1 := mul_pos (hc τ) (hm τ)
    have h2 := mul_pos (hy τ) h1
    have e : (X.tt ξ x τ + y τ) * (X.c τ * X.maj x τ (Data.emb τ.1 ξ)) =
        1 + X.c τ * y τ * X.maj x τ (Data.emb τ.1 ξ) := by
      rw [Data.tt, add_mul, one_div_mul_cancel h1.ne']
      ring
    rwa [e] at h2
  have hind := ReciprocityTheory.L2DbarEstimates.Y.four_indep (Fintype.card X.Ψ) (FractionalSliceDomains.Om X ξ x bs) (hfun X P ξ x bs)
    (Om_open_conn X bs hx).1 (Om_open_conn X bs hx).2 (hfun_diff X bs P la hP hx hξ)
    (hfun_periodic X bs P la hP hx hξ hω) 0 (zero_mem_Om X bs hx hξ) b' hb'Ω k
  rw [hind]
  have hslice : ∀ t : Fin (Fintype.card X.Ψ) → ℝ,
      ‖hfun X P ξ x bs (fun k => (t k : ℂ) + (b' k : ℂ) * Complex.I)‖ ≤ M := by
    intro t
    have h := hM (fun τ => ∑ j, t j * bs j τ)
    unfold hfun
    convert h using 4
    funext τ
    rw [← hb'ω τ]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hbd := ReciprocityTheory.L2DbarEstimates.Y.four_bound (Fintype.card X.Ψ) (hfun X P ξ x bs) b' k _ hslice
  have hsum : ∑ j, (k j : ℝ) * b' j = 2 * ∑ τ, ν τ * ∑ j, b' j * bs j τ := by
    simp only [← hk, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsum] at hbd
  simp only [hb'ω] at hbd
  convert hbd using 3
  ring

theorem exists_ne (h : 1 < Module.finrank ℚ E / 2) (τ₀ : X.Ψ) : ∃ τ₁ : X.Ψ, τ₁ ≠ τ₀ := by
  classical
  by_contra hne
  push Not at hne
  have hsub : (Finset.univ : Finset (E →+* ℂ)) ⊆ {τ₀.1, ComplexEmbedding.conjugate τ₀.1} := by
    intro τ _
    by_cases hτ : τ ∈ X.Ψ
    · have := congrArg Subtype.val (hne ⟨τ, hτ⟩)
      simp only at this
      simp [this]
    · have h2 : ComplexEmbedding.conjugate τ ∈ X.Ψ := by
        by_contra h3
        exact hτ ((X.cmType τ).mpr h3)
      have := congrArg Subtype.val (hne ⟨_, h2⟩)
      simp only at this
      have h4 : τ = ComplexEmbedding.conjugate τ₀.1 := by
        rw [← this]
        exact (star_star τ).symm
      simp [h4]
  have h1 := (Finset.card_le_card hsub).trans Finset.card_le_two
  rw [Finset.card_univ, NumberField.Embeddings.card] at h1
  omega

theorem eq_zero_of_exp_le {a b c K A : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (h : ∀ L : ℝ, 1 ≤ L → a * Real.exp (b * L - c) ≤ K * L ^ A) : a = 0 := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero A b hb).const_mul (K * Real.exp c)
  rw [mul_zero] at ht
  refine le_antisymm (ge_of_tendsto ht ?_) ha
  filter_upwards [eventually_ge_atTop 1] with L hL
  have h1 := mul_le_mul_of_nonneg_right (h L hL) (Real.exp_pos (c - b * L)).le
  rw [mul_assoc, ← Real.exp_add] at h1
  simp only [sub_add_sub_cancel', sub_self, Real.exp_zero, mul_one] at h1
  refine h1.trans (le_of_eq ?_)
  rw [sub_eq_add_neg, Real.exp_add, neg_mul]
  ring

end GlobalTheory.Koecher

namespace GlobalTheory


open Koecher FjCauchy in
theorem freqNonneg_of_thickBdd : OrbitThickSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), 1 < Module.finrank ℚ E / 2 → X.IsSec la P →
    ThickBdd X (X.pnorm la P) → FreqNonneg X la P := by
  intro hO E _ _ _ r X la P hE hP hT ξ hξ ν x hx hne τ₀
  classical
  by_contra hneg
  push Not at hneg
  obtain ⟨τ₁, h10⟩ := exists_ne X hE τ₀
  obtain ⟨ε, hε, hth⟩ := hO E r X ξ hξ x hx
  obtain ⟨S, hS⟩ := hT ε hε
  have ht := tt_pos X hξ hx
  have hn := FlowCoefficientBounds.nfac_pos X hx la
  apply hne
  rw [← norm_eq_zero]
  refine eq_zero_of_exp_le (b := 4 * Real.pi * (-ν τ₀ * X.tt ξ x τ₀))
    (c := 4 * Real.pi * (-ν τ₀ * X.tt ξ x τ₀ + |ν τ₁| * X.tt ξ x τ₁)) (K := |S| / X.nfac la x)
    (A := ∑ τ, |X.spread la τ / 2|) (norm_nonneg _)
    (mul_pos (by positivity) (mul_pos (by linarith) (ht _))) fun L hL => ?_
  have hL0 : 0 < L := by linarith
  have hLi : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL
  let q : X.Ψ → ℝ := fun τ => (if τ = τ₀ then L else 1) * (if τ = τ₁ then L⁻¹ else 1)
  have hq0 : ∀ τ, 0 < q τ := fun τ => by
    simp only [q]
    split_ifs <;> positivity
  have hqm : ∀ τ, max (q τ) (q τ)⁻¹ ≤ L := fun τ => by
    simp only [q]
    split_ifs with h1 h2 h2
    · exact absurd (h2.symm.trans h1) h10
    · simp [hLi.trans hL]
    · simp [hLi.trans hL]
    · simp [hL]
  have hq1 : ∀ τ, 1 ≤ max (q τ) (q τ)⁻¹ := fun τ => by
    rcases le_total 1 (q τ) with h | h
    · exact le_max_of_le_left h
    · exact le_max_of_le_right ((one_le_inv₀ (hq0 τ)).mpr h)
  have hqp : ∏ τ, q τ = 1 := by
    simp only [q, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
    exact mul_inv_cancel₀ hL0.ne'
  let y : X.Ψ → ℝ := fun τ => (q τ - 1) * X.tt ξ x τ
  have hty : ∀ τ, X.tt ξ x τ + y τ = q τ * X.tt ξ x τ := fun τ => by simp only [y]; ring
  have hy : ∀ τ, 0 < X.tt ξ x τ + y τ := fun τ => by rw [hty]; exact mul_pos (hq0 τ) (ht τ)
  refine le_trans ?_ (fj_le_slice X la P hP ξ hξ ν x hx y _ hy fun u => ?_)
  · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have e : ∑ τ, ν τ * y τ = ν τ₀ * ((L - 1) * X.tt ξ x τ₀) + ν τ₁ * ((L⁻¹ - 1) * X.tt ξ x τ₁) := by
      rw [Fintype.sum_eq_add τ₀ τ₁ h10.symm]
      · simp [y, q, h10, h10.symm]
      · rintro τ ⟨h1, h2⟩
        simp [y, q, h1, h2]
    rw [e]
    have h1 : ν τ₁ * ((L⁻¹ - 1) * X.tt ξ x τ₁) ≤ |ν τ₁| * X.tt ξ x τ₁ := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos (ht τ₁)]
      refine mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (ht τ₁).le ?_) (abs_nonneg _)
      have := inv_pos.mpr hL0
      rw [abs_le]
      constructor <;> linarith
    nlinarith [Real.pi_pos]
  · set s : X.Ψ → ℂ := fun τ => (u τ : ℂ) + (y τ : ℂ) * I with hs
    have him : ∀ τ, (s τ).im = y τ := fun τ => by simp [hs]
    have hd : X.flow ξ s x ∈ X.dom := flow_mem_dom X hξ hx s fun τ => by rw [him]; exact hy τ
    have hprod : ∏ τ, X.tt ξ (X.flow ξ s x) τ = ∏ τ, X.tt ξ x τ := by
      simp only [tt_flow X hξ hx s hd, him, hty]
      rw [Finset.prod_mul_distrib, hqp, one_mul]
    have hb : ‖P (X.flow ξ s x)‖ * X.nfac la (X.flow ξ s x) ≤ S := hS _ hd (hth s hd hprod)
    have hn' := FlowCoefficientBounds.nfac_pos X hd la
    have hN : X.nfac la x / X.nfac la (X.flow ξ s x) ≤
        ∏ τ, max (1 + (s τ).im / X.tt ξ x τ) (1 + (s τ).im / X.tt ξ x τ)⁻¹ ^ (X.spread la τ / 2) :=
      (m3bNorm_holds r X _ (isIsoV_embV X hξ) la x hx s hd).2
    have hqe : ∀ τ, 1 + (s τ).im / X.tt ξ x τ = q τ := fun τ => by
      rw [him]
      simp only [y]
      rw [mul_div_cancel_right₀ _ (ht τ).ne']
      ring
    simp only [hqe] at hN
    have hN2 : ∏ τ, max (q τ) (q τ)⁻¹ ^ (X.spread la τ / 2) ≤ L ^ ∑ τ, |X.spread la τ / 2| := by
      rw [Real.rpow_sum_of_pos hL0]
      refine Finset.prod_le_prod₀ (fun τ _ => Real.rpow_nonneg (zero_le_one.trans (hq1 τ)) _) fun τ _ => ?_
      exact (Real.rpow_le_rpow_of_exponent_le (hq1 τ) (le_abs_self _)).trans
        (Real.rpow_le_rpow (zero_le_one.trans (hq1 τ)) (hqm τ) (abs_nonneg _))
    calc ‖P (X.flow ξ s x)‖ ≤ |S| / X.nfac la (X.flow ξ s x) := by
          rw [le_div_iff₀ hn']
          exact hb.trans (le_abs_self S)
      _ = |S| / X.nfac la x * (X.nfac la x / X.nfac la (X.flow ξ s x)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hN.trans hN2) (by positivity)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftFormsReferenceTupleBasisExtendedStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftForms_referenceTuple_basis_extended : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (L : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms →+ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms), (∀ (a : (w.st Z).toD7.what₂.LL) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), L (a • f) = φ a • L f) → (∀ (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (L f) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm f : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1)) → LinearIndependent (w'.st Z').toD7.what₂.LL (fun k => L (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.basis k)) ∧ ⊤ ≤ Submodule.span (w'.st Z').toD7.what₂.LL (Set.range fun k => L (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.basis k))) := by
  first | exact @GlobalTheory.Mem.R3.DefLatBC.lift_basis_ext | exact GlobalTheory.Mem.R3.DefLatBC.lift_basis_ext | (intros; apply GlobalTheory.Mem.R3.DefLatBC.lift_basis_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfInterLwInterPoly
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.Member

theorem selfInter_Lw_interPoly : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}
    (C : FlagCpt Z e) (la : GlobalTheory.AllWt.Weight Dw),
    ((C.Y.inter (fun _ => C.Lw la) : ℤ) : ℝ) =
      C.Y.interPoly (fun x : Root Dw.mult => C.gr x.1 x.2)
        ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ C.Y.dim) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C la
  rw [← Fin.prod_const]
  have h := C.Y.interPoly_prod_sum (fun x : Root Dw.mult => C.gr x.1 x.2)
    (fun _ x => -(GlobalTheory.AllWt.exOf Dw la 0 (some x)))
  push_cast at h
  rw [h]
  congr 2
  funext i
  simp [FlagCpt.Lw, FlagCpt.LEx, Finset.sum_neg_distrib]

end GlobalTheory.Member
end

