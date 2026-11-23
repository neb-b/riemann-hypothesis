module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0933
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyFormGroupToPadicPointsComponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0972
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedConjClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2812
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2816
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomPairBigMemberTwistedTuple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2822
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2821
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2823
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2830
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCosetsAndFixedPoints
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.FinPtsSep

open scoped Pointwise in
open IsDedekindDomain GlobalTheory.OrbFinAf GlobalTheory.OrbFinAf.AwayIrr in
theorem fin_cosets_away_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (y₀ : grp G β), (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable → (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n → ∃ R : Finset G.GAf, ∀ h : G.GAf, f (h⁻¹ * toAfF G β x t hx y₀ * h) ≠ 0 → ∃ c : G.GAf, c * toAfF G β x t hx y₀ = toAfF G β x t hx y₀ * c ∧ ∃ r ∈ R, ∃ k ∈ L.K.toSubgroup, h = c * r * k := by
  intro p _ G L f hf β x t hx y₀ hsep0 hdeg
  set y : G.Cˣ := (y₀ : G.Cˣ × ℚˣ).1 with hy
  have hsep : (minpoly G.F (y : G.C)).Separable := hsep0
  set γ := toAfF G β x t hx y₀ with hγ
  have hg0 : ∀ v, ((piV G v γ : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) =
      xV G x v * yV G y v * (xV G x v)⁻¹ := fun v => piV_toAfF_fst G β x t hx y₀ v
  set T := GlobalTheory.BCT.twCent (MonoidHom.id G.GAf) γ with hT
  set K := L.K.toSubgroup with hK
  obtain ⟨S, hSf⟩ := hf.2.2.2
  let Ω : Set G.GAf := ⋃ s ∈ S, (fun k : G.GAf × G.GAf => k.1 * s * k.2) '' ((K : Set G.GAf) ×ˢ (K : Set G.GAf))
  have hΩ : IsCompact Ω := S.isCompact_biUnion fun s _ =>
    (L.compact.prod L.compact).image ((continuous_fst.mul continuous_const).mul continuous_snd)
  have hsupp : ∀ g : G.GAf, f g ≠ 0 → g ∈ Ω := by
    intro g hg
    obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, e⟩ := hSf g hg
    exact Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, e.symm⟩
  let Good : Set (AwayP p) := {v | piV G v '' Ω ⊆ IntV G v ∧
    (∀ g : Gv G v, g⁻¹ * piV G v γ * g ∈ IntV G v → ∃ c ∈ GlobalTheory.BCT.twCent (MonoidHom.id (Gv G v)) (piV G v γ),
      ∃ d ∈ IntV G v, g = c * d) ∧ ∀ a ∈ IntV G v, ∀ b ∈ IntV G v, a * b ∈ IntV G v}
  have hGood : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), v ∈ Good := by
    filter_upwards [GlobalTheory.T.eventually_compact_unitaryAdelic_image_integral p G Ω hΩ, kottwitz_almost' G y hdeg hsep x (fun v => piV G v γ) hg0, GlobalTheory.T.eventually_integralUnitaryPointsAtPlace_mul_mem p G]
      with v h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hL1 := fun v : AwayP p => local_fin' G v y hdeg hsep (xV G x v) (piV G v γ) (hg0 v) (piV G v '' Ω)
    (hΩ.image (GlobalTheory.T.continuous_unitaryAdelicComponentAtPlace_explicit p G v))
  choose D₁ hD₁ hD₁g using hL1
  let D' : ∀ v : AwayP p, Set (Gv G v) := fun v => if v ∈ Good then IntV G v else D₁ v
  have hD'c : ∀ v, IsCompact (D' v) := by
    intro v; by_cases hv : v ∈ Good
    · simp only [D', if_pos hv]; exact GlobalTheory.T.isCompact_integralUnitaryPointsAtPlace p G v
    · simp only [D', if_neg hv]; exact hD₁ v
  have hD'i : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), D' v ⊆ IntV G v := by
    filter_upwards [hGood] with v hv
    simp only [D', if_pos hv]; exact le_rfl
  have key : ∀ g : G.GAf, g⁻¹ * γ * g ∈ Ω → ∃ c ∈ T, ∃ d ∈ {g : G.GAf | ∀ v, piV G v g ∈ D' v}, g = c * d := by
    intro g hg
    have hloc : ∀ v, ∃ c ∈ GlobalTheory.BCT.twCent (MonoidHom.id (Gv G v)) (piV G v γ), ∃ d ∈ D' v, piV G v g = c * d := by
      intro v
      have hgv : (piV G v g)⁻¹ * piV G v γ * piV G v g ∈ piV G v '' Ω :=
        ⟨_, hg, by simp only [map_mul, map_inv]⟩
      by_cases hv : v ∈ Good
      · obtain ⟨c, hc, d, hd, e⟩ := hv.2.1 _ (hv.1 hgv)
        exact ⟨c, hc, d, by simp only [D', if_pos hv]; exact hd, e⟩
      · obtain ⟨c, hc, d, hd, e⟩ := hD₁g v _ hgv
        exact ⟨c, hc, d, by simp only [D', if_neg hv]; exact hd, e⟩
    choose c hc d hd e using hloc
    have hcint : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), c v ∈ IntV G v := by
      filter_upwards [GlobalTheory.T.eventually_compact_unitaryAdelic_image_integral p G {g} isCompact_singleton, hGood] with v h1 h2
      have hdv : d v ∈ IntV G v := by have := hd v; simp only [D', if_pos h2] at this; exact this
      have ec : c v = piV G v g * (d v)⁻¹ := by rw [e v]; group
      rw [ec]
      exact h2.2.2 _ (h1 ⟨g, rfl, rfl⟩) _ (inv_mem_IntV G v hdv)
    obtain ⟨tt, htt⟩ := GlobalTheory.T.exists_unitaryAdelicPoint_of_eventually_integral_local p G c hcint
    refine ⟨tt, ?_, tt⁻¹ * g, ?_, by group⟩
    · show tt * γ = γ * (MonoidHom.id _) tt
      apply GlobalTheory.T.unitaryAdelicPoint_ext_of_components p G
      intro v
      have h1 : c v * piV G v γ = piV G v γ * (MonoidHom.id _) (c v) := hc v
      simp only [map_mul, htt, MonoidHom.id_apply] at h1 ⊢
      exact h1
    · intro v
      have : piV G v (tt⁻¹ * g) = d v := by rw [map_mul, map_inv, htt, e v]; group
      rw [this]; exact hd v
  set D := {g : G.GAf | ∀ v, piV G v g ∈ D' v}
  have hD : IsCompact D := GlobalTheory.T.isCompact_unitaryAdelic_prod_local_compacts p G D' hD'c hD'i
  obtain ⟨I, hI⟩ := hD.elim_finite_subcover (fun d : G.GAf => d • (K : Set G.GAf))
    (fun d => L.K.isOpen.smul d) (fun d _ => Set.mem_iUnion.2 ⟨d, ⟨1, one_mem _, mul_one d⟩⟩)
  refine ⟨I, fun h hh => ?_⟩
  obtain ⟨c, hc, d, hd, e⟩ := key _ (hsupp _ hh)
  obtain ⟨i, hi, hdi⟩ := Set.mem_iUnion₂.1 (hI hd)
  obtain ⟨k, hk, rfl⟩ := hdi
  refine ⟨c, hc, i, hi, k, hk, ?_⟩
  rw [e]; simp only [smul_eq_mul]; group

end GlobalTheory.FinPtsSep

noncomputable section

namespace GlobalTheory.FinPtsSep

variable {p : ℕ} [Fact p.Prime]

theorem exists_finset_doubleCoset_cover_of_separable : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ),
    IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (y₀ : grp G β),
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable →
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n →
    ∃ R : Finset (Gr G 1), ∀ h : Gr G 1, f' (h⁻¹ * toP1 G β y₀ * h) ≠ 0 →
      ∃ c : Gr G 1, c * toP1 G β y₀ = toP1 G β y₀ * c ∧ ∃ r ∈ R, ∃ k ∈ K', h = c * r * k := by
  intro p _ G K' f' hT β y₀ hsep hdeg
  obtain ⟨hcomm, -, -, S₀, hS₀⟩ := hT
  obtain ⟨S, hS⟩ := GlobalTheory.FinAtP.prod_fin G (toP1 G β y₀)
    (fun w => by rw [GlobalTheory.FinAtP.charpoly_formGroupToPadicPoints_component]; exact (GlobalTheory.FinAtP.rho_charpoly_sep G w _ hdeg hsep).map) S₀
  obtain ⟨T, hT⟩ := GlobalTheory.FinAtP.exists_finset_cosets (KHT p G.m G.n 1 G.Fw) K' hcomm.1.relIndex_ne_zero
  refine ⟨(S ×ˢ T).image fun x => x.1 * x.2, fun h hh => ?_⟩
  obtain ⟨a, ha, s, hs, k, hk, rfl⟩ := hS h (hS₀ _ hh)
  obtain ⟨t, ht, k', hk', rfl⟩ := hT k hk
  exact ⟨a, ha, s * t, Finset.mem_image.2 ⟨(s, t), Finset.mem_product.2 ⟨hs, ht⟩, rfl⟩, k', hk', by group⟩

theorem posV_toV (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (y : grp G β) (z : PosV G v β) :
    0 < (star ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1) ⬝ᵥ
      (herm G v β *ᵥ ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1))).re := by
  have hs := GlobalTheory.LKCx.grp_similitude_herm p G v β y
  have e : star ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1) ⬝ᵥ
      (herm G v β *ᵥ ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1)) =
      (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℂ)) * (star z.1 ⬝ᵥ (herm G v β *ᵥ z.1)) := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hs, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [e]
  have hpos : (0 : ℚ) < (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := y.2.2
  rw [show (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℂ)) = ((((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ)) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul]
  exact mul_pos (by exact_mod_cast hpos) z.2

def mapPosV (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (y : grp G β) (z : PosV G v β) : PosV G v β :=
  ⟨(toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1, posV_toV G v β y z⟩

def conjC (G : HTGroup p) (y : G.Cˣ) : G.C ≃ₐ[G.F] G.C where
  toFun x := y * x * ((y⁻¹ : G.Cˣ) : G.C)
  invFun x := ((y⁻¹ : G.Cˣ) : G.C) * x * y
  left_inv x := by simp [_root_.mul_assoc]
  right_inv x := by simp [_root_.mul_assoc]
  map_mul' a b := by simp [_root_.mul_assoc]
  map_add' a b := by simp [mul_add, add_mul]
  commutes' a := by
    show (y : G.C) * algebraMap G.F G.C a * ((y⁻¹ : G.Cˣ) : G.C) = algebraMap G.F G.C a
    rw [← Algebra.commutes, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]

theorem minpoly_conjC (G : HTGroup p) (y g : G.Cˣ) :
    minpoly G.F ((y * g * y⁻¹ : G.Cˣ) : G.C) = minpoly G.F (g : G.C) := by
  have := minpoly.algEquiv_eq (conjC G y) (g : G.C)
  rw [← this]
  rfl

theorem fixL_conj (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (g y : grp G β) (z : Fin G.n → ℂ)
    (h : FixL G v β (g * y * g⁻¹) z) : FixL G v β y ((toV G v β g⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  have e : y * g⁻¹ = g⁻¹ * (g * y * g⁻¹) := by group
  calc (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ ((toV G v β g⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)
      = (toV G v β g⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ ((toV G v β (g * y * g⁻¹) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, e]
    _ = c • ((toV G v β g⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by rw [hc, Matrix.mulVec_smul]

theorem finite_pts_conj_fixL_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y z) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) → sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ y₀ : grp G β, Set.Finite {q : Pts G v β x t hx L.K.toSubgroup K' | ∃ γ : grp G β, FixL G v β (γ * y₀ * γ⁻¹) (Quot.out q).2.1 ∧ f ((Quot.out q).1.1⁻¹ * toAfF G β x t hx (γ * y₀ * γ⁻¹) * (Quot.out q).1.1) * f' ((Quot.out q).1.2⁻¹ * toP1 G β (γ * y₀ * γ⁻¹) * (Quot.out q).1.2) ≠ 0} := by
  intro p _ G ha v hv L f hf K' f' hf' β x t hx hsees hsym htr y₀
  classical
  by_cases hne : ∃ (b : Dat G v β) (γ : grp G β), FixL G v β (γ * y₀ * γ⁻¹) b.2.1 ∧
      f (b.1.1⁻¹ * toAfF G β x t hx (γ * y₀ * γ⁻¹) * b.1.1) * f' (b.1.2⁻¹ * toP1 G β (γ * y₀ * γ⁻¹) * b.1.2) ≠ 0
  swap
  · apply Set.Finite.subset Set.finite_empty
    rintro q ⟨γ, h1, h2⟩
    exact False.elim (hne ⟨_, γ, h1, h2⟩)
  obtain ⟨b₀, γ₀, hfix₀, hne₀⟩ := hne
  have hsd : (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧
      (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable := by
    have h := hsees (γ₀ * y₀ * γ₀⁻¹) b₀.1.1 (left_ne_zero_of_mul hne₀) ⟨b₀.2.1, b₀.2.2, hfix₀⟩
    have e : (((γ₀ * y₀ * γ₀⁻¹ : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) =
        ((γ₀ : G.Cˣ × ℚˣ).1) * ((y₀ : G.Cˣ × ℚˣ).1) * ((γ₀ : G.Cˣ × ℚˣ).1)⁻¹ := by simp
    rw [e, minpoly_conjC] at h
    exact h
  let z₀ : PosV G v β := mapPosV G v β γ₀⁻¹ b₀.2
  have hz₀ : FixL G v β y₀ z₀.1 := fixL_conj G v β γ₀ y₀ _ hfix₀
  obtain ⟨R1, hR1⟩ := fin_cosets_away_sep p G L f hf β x t hx y₀ hsd.2 hsd.1
  obtain ⟨R2, hR2⟩ := exists_finset_doubleCoset_cover_of_separable p G K' f' hf' β y₀ hsd.2 hsd.1
  have h3 := GlobalTheory.T.finite_classNumber_centraliserTorus_separable p G L K' hf'.1 β x t hx hsym y₀ hsd.2 hsd.1
  choose R3 hR3 using h3
  let Fs : Finset (G.GAf × Gr G 1) := (R1 ×ˢ R2).biUnion R3
  refine (Fs.finite_toSet.image (fun s => (Quot.mk _ (s, z₀) : Pts G v β x t hx L.K.toSubgroup K'))).subset ?_
  rintro q ⟨γ, hfix, hne⟩
  have hq : Quot.mk (Same G v β x t hx L.K.toSubgroup K') (Quot.out q) = q := Quot.out_eq q
  generalize Quot.out q = b at hfix hne hq
  have e1 : (toAfF G β x t hx γ⁻¹ * b.1.1)⁻¹ * toAfF G β x t hx y₀ * (toAfF G β x t hx γ⁻¹ * b.1.1) =
      b.1.1⁻¹ * toAfF G β x t hx (γ * y₀ * γ⁻¹) * b.1.1 := by
    simp only [map_mul, map_inv]; group
  have e2 : (toP1 G β γ⁻¹ * b.1.2)⁻¹ * toP1 G β y₀ * (toP1 G β γ⁻¹ * b.1.2) =
      b.1.2⁻¹ * toP1 G β (γ * y₀ * γ⁻¹) * b.1.2 := by
    simp only [map_mul, map_inv]; group
  obtain ⟨c1, hc1, r1, hr1, k1, hk1, hh1⟩ := hR1 _ (by rw [e1]; exact left_ne_zero_of_mul hne)
  obtain ⟨c2, hc2, r2, hr2, k2, hk2, hh2⟩ := hR2 _ (by rw [e2]; exact right_ne_zero_of_mul hne)
  obtain ⟨y, hy, s, hs, k3, hk31, hk32, hcr⟩ := hR3 (r1, r2) (c1, c2) (Prod.ext hc1 hc2)
  have hfix' : FixL G v β y₀ (mapPosV G v β γ⁻¹ b.2).1 := fixL_conj G v β γ y₀ _ hfix
  let w : PosV G v β := mapPosV G v β y⁻¹ (mapPosV G v β γ⁻¹ b.2)
  have hw : FixL G v β y₀ w.1 := by
    have e : y * y₀ * y⁻¹ = y₀ := by rw [hy]; group
    exact fixL_conj G v β y y₀ _ (by rw [e]; exact hfix')
  obtain ⟨c, hc⟩ := GlobalTheory.LKCx.fixL_pos_unique_of_sep p G v hv β hsym htr y₀ hsd.1 hsd.2 z₀.1 w.1 z₀.2 w.2 hz₀ hw
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h := w.2
    rw [hc, zero_smul] at h
    simp at h
  have hb2 : b.2.1 = c • ((toV G v β (γ * y) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z₀.1) := by
    rw [← Matrix.mulVec_smul, ← hc]
    show b.2.1 = (toV G v β (γ * y) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
      ((toV G v β y⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ ((toV G v β γ⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ b.2.1))
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
    simp
  have hb1 : b.1 = ((toAfF G β x t hx (γ * y), toP1 G β (γ * y)) : G.GAf × Gr G 1) * s * (k3 * (k1, k2)) := by
    have hh : ((toAfF G β x t hx γ⁻¹ * b.1.1, toP1 G β γ⁻¹ * b.1.2) : G.GAf × Gr G 1) =
        (c1, c2) * (r1, r2) * (k1, k2) := Prod.ext hh1 hh2
    rw [hcr] at hh
    have hb : b.1 = ((toAfF G β x t hx γ, toP1 G β γ) : G.GAf × Gr G 1) *
        ((toAfF G β x t hx γ⁻¹ * b.1.1, toP1 G β γ⁻¹ * b.1.2) : G.GAf × Gr G 1) := by
      ext <;> simp [← mul_assoc]
    rw [hb, hh]
    ext <;> simp [mul_assoc]
  have hsF : s ∈ Fs := Finset.mem_biUnion.2 ⟨(r1, r2), Finset.mem_product.2 ⟨hr1, hr2⟩, hs⟩
  refine ⟨s, hsF, ?_⟩
  rw [← hq]
  exact Quot.sound ⟨γ * y, k3 * (k1, k2), c, mul_mem hk31 hk1, mul_mem hk32 hk2, hc0, hb1, hb2⟩

end GlobalTheory.FinPtsSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupCocycleCoboundaryModPrime
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.CobModP

theorem constantCoeff_subst_of_zero' {σ τ R : Type} [CommRing R] [Finite σ]
    {a : σ → MvPowerSeries τ R} (ha0 : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  have h := constantCoeff_subst_eq_zero ha ha0 (f := f - C (constantCoeff f)) (by simp)
  rw [subst_sub ha, subst_C, map_sub, constantCoeff_C, sub_eq_zero] at h
  exact h

theorem constantCoeff_formalGroupLawCoboundaryOne_eq_zero {R : Type} [CommRing R] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (h : ∀ i, constantCoeff (μ i) = 0)
    (f : MvPowerSeries (Fin d) R) : constantCoeff (cob1 μ f) = -constantCoeff f := by
  unfold cob1 inL inR
  rw [map_sub, map_sub, constantCoeff_subst_of_zero' h,
    constantCoeff_subst_of_zero' (fun _ => constantCoeff_X _),
    constantCoeff_subst_of_zero' (fun _ => constantCoeff_X _)]
  ring

theorem coboundary_mod_p : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (κ : MvPowerSeries (Fin d ⊕ Fin d) O) (B : MvPowerSeries (Fin d) O) (y : G.A 1), constantCoeff κ = 0 → IsCoc c.μ κ → (∀ α, (p : O) ∣ coeff α (cob1 c.μ B - pull2 (nmul c.μ p) κ)) → c.ev 1 B = (p : O) • y → ∃ t : MvPowerSeries (Fin d) O, constantCoeff t = 0 ∧ ∀ α, (p : O) ∣ coeff α (κ - cob1 c.μ t) := by
  intro p _ O _ G d c κ B y hκ0 hcoc hdiv hB
  set I : Ideal O := Ideal.span {(p : O)} with hI
  set r : O →+* O ⧸ I := Ideal.Quotient.mk I with hr
  obtain ⟨c', hlaw, hev, -⟩ := _root_.GlobalTheory.QLog.ChartRed.exists_chart p O G d c I 1 (by
    rw [pow_one]; exact Ideal.mem_span_singleton_self _)
  have hconst := c.isLaw.const
  obtain ⟨hm1, hm2, hm3, -, hm5⟩ := _root_.GlobalTheory.Katz.map_cob_swap_pull O d c.μ hconst (O ⧸ I) r
  obtain ⟨-, hn⟩ := _root_.GlobalTheory.isLaw_map_nmul O d c.μ c.isLaw (O ⧸ I) r
  have hnc : ∀ i, constantCoeff (nmul c.μ p i) = 0 := fun i => (hn p i).1
  have hcoc' : IsCoc (fun i => map r (c.μ i)) (map r κ) :=
    ⟨by rw [← hm2, hcoc.1, map_zero], by rw [← hm3, hcoc.2]⟩
  have heq : cob1 (fun i => map r (c.μ i)) (map r B) =
      pull2 (nmul (fun i => map r (c.μ i)) p) (map r κ) := by
    have h0 : map r (cob1 c.μ B - pull2 (nmul c.μ p) κ) = 0 :=
      ((GlobalTheory.mvPowerSeries_lift_quotient O (Fin d ⊕ Fin d) I).2.1 _).2
        (fun α => Ideal.mem_span_singleton.2 (hdiv α))
    rw [map_sub, hm1, (hm5 _ hnc).1, sub_eq_zero] at h0
    rw [h0]
    congr 1
    funext i
    exact (hn p i).2
  have hp1 : (p : O) • (1 : O ⧸ I) = 0 := by
    rw [Algebra.smul_def, mul_one]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hev0 : c'.ev 1 (map r B) = 0 := by
    rw [hev, hB, toBase_app, ← TensorProduct.smul_tmul, hp1, TensorProduct.zero_tmul]
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_coboundary_of_pullback_nmul_coboundary p (O ⧸ I) d (G.baseChange (O ⧸ I)) c' _ hlaw (map r κ) (map r B)
    hcoc' heq hev0
  have hs0 : constantCoeff s = 0 := by
    have h1 : constantCoeff (map r κ) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hκ0,
        map_zero]
    have hc' : ∀ i, constantCoeff (map r (c.μ i)) = 0 := fun i => by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
        hconst i, map_zero]
    rw [hs, constantCoeff_formalGroupLawCoboundaryOne_eq_zero hc'] at h1
    exact neg_eq_zero.1 h1
  obtain ⟨t, ht, ht0⟩ := (GlobalTheory.mvPowerSeries_lift_quotient O (Fin d) I).1 s
  refine ⟨t, ht0 hs0, fun α => ?_⟩
  have h2 : map r (κ - cob1 c.μ t) = 0 := by rw [map_sub, hm1, ht, hs, sub_self]
  exact Ideal.mem_span_singleton.1 (((GlobalTheory.mvPowerSeries_lift_quotient O (Fin d ⊕ Fin d) I).2.1 _).1 h2 α)

end GlobalTheory.CobModP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
section
noncomputable section

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormRatio

variable {D : D7}

def GoodMod (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)) : Prop :=
  𝔪 ≠ ⊥ ∧ 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ ∧ IsCoprime 𝔪 (Ideal.span {((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E)}) ∧
    ∀ v, v ∈ Sf ↔ ∃ w : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ w.asIdeal ∧ w.under (𝓞 D.host.F) = v

abbrev stdLat (V : HSp D) : Lat V := Formalism.MainNotions.StandardLatticesGL3.stdL D V.rank

def locNorm (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a a' : ℕ) : ℝ :=
  ∏ w ∈ (normalizedFactors 𝔪).toFinset,
    (((Ideal.absNorm w : ℝ) ^ ((normalizedFactors 𝔪).count w * a * a'))⁻¹ * glVol (Ideal.absNorm w : ℝ) a)

def locIdx (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a a' : ℕ) : ℝ :=
  ∏ w ∈ (normalizedFactors 𝔪).toFinset, blockIdx (Ideal.absNorm w : ℝ) ((normalizedFactors 𝔪).count w) a a'

def vacNorm (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (a d : ℕ) : ℝ :=
  Formalism.MainNotions.StandardLatticesGL3.nrm1Sq (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) (Formalism.MainNotions.GL3Theta.th0 (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) t0) ^ (Formalism.MainNotions.TaylorLogMetric.fF D * a * d)

def mass (D : D7) (N : ℕ) : ℂ := ∑ᶠ x : Cls D N (intG D N), ((gam D (intG D N) x.out : ℂ))⁻¹

def fockSum (D : D7) (a d : ℕ) (n : D.what₂.Tau → ℕ) : ℂ :=
  ∑ T : Tup D a d n, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp (minorPol D T) (minorPol D T)

theorem goodMod_modT {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} (hL : L.Is μ₀) (hpq : Nat.Coprime D.host.pde (D.host.QS * D.host.q))
    (hpq' : Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) (G : GridData L sc) (t : T) : GoodMod D (modT G t) (sfB G t) := by
  refine ⟨GlobalTheory.FunObj.StdDatum.TwBig.modT_ne_bot G t, GlobalTheory.SqTop.modT_sup_conj hL G t,
    GlobalTheory.BotPairSmallTw.modT_isCoprime_two_q hL hpq hpq' G t, fun v => ?_⟩
  have key : ∀ w : HeightOneSpectrum (𝓞 D.host.E), modT G t ≤ w.asIdeal ↔ w ∈ locPl G t := by
    intro w
    have hp := w.isPrime
    have hc : ∀ v, SqNum.condExp G.pl v ≠ 0 := fun v => by unfold SqNum.condExp; split_ifs <;> omega
    unfold modT condE
    rw [hp.mul_le, hp.prod_le, hp.prod_le]
    constructor
    · rintro (⟨v, hv, h⟩ | ⟨w', hw', h⟩)
      · have h1 : (G.pl.w v).asIdeal ≤ w.asIdeal := (Ideal.IsPrime.pow_le_iff (hc v)).1 h
        have h2 : G.pl.w v = w := HeightOneSpectrum.ext ((G.pl.w v).isMaximal.eq_of_le hp.ne_top h1)
        unfold locPl Places.W0
        exact Finset.mem_union_left _ (h2 ▸ Finset.mem_image_of_mem _ hv)
      · have h2 : w' = w := HeightOneSpectrum.ext (w'.isMaximal.eq_of_le hp.ne_top h)
        subst h2
        exact (Finset.mem_filter.1 hw').1
    · intro hw
      by_cases h0 : w ∈ G.pl.W0
      · unfold Places.W0 at h0
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h0
        exact Or.inl ⟨v, hv, Ideal.pow_le_self (hc v)⟩
      · exact Or.inr ⟨w, Finset.mem_filter.2 ⟨hw, h0⟩, le_rfl⟩
  unfold sfB
  simp only [Finset.mem_image, key]

end GlobalTheory.NormRatio
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceVectorValuedEqFiniteKernelSumStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTrace_vectorValued_eq_finite_kernelSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → trOn (GlobalTheory.BCT.TrKer.vecM S lam K') (GlobalTheory.BCT.TrKer.hopM S lam K' f) = (((globLev S K').relIndex (globLev S (KL n)) : ℕ) : ℂ)⁻¹ * ∑ᶠ q : DoubleCoset.Quotient (ratFinU E n : Set (finU (E := E) (n := n))) (globLev S K' : Set (finU (E := E) (n := n))), ((Nat.card (ratFinU E n ⊓ (globLev S K').map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup (finU (E := E) (n := n))) : ℂ))⁻¹ * ∑ᶠ γ : UE E n, globFn S f ((Quotient.out q)⁻¹ * finPt γ * Quotient.out q) * LinearMap.trace ℂ _ (GlobalTheory.BCT.TrKer.wAt lam γ⁻¹) := by
  first | exact @GlobalTheory.BCT.TrKer.trOn_vecM_hopM | exact GlobalTheory.BCT.TrKer.trOn_vecM_hopM | (intros; apply GlobalTheory.BCT.TrKer.trOn_vecM_hopM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomDegreeIntegerCombinationIsHomogeneousStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homDegree_integerCombination_isHomogeneous : ∀ (K : Type) [Field K] (A B : AbVar K), A.dim = B.dim → ∀ (n : ℕ) (f : Fin n → (A ⟶ B)), ∃ F : MvPolynomial (Fin n) ℚ, F.IsHomogeneous (2 * A.dim) ∧ ∀ m : Fin n → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) F = (deg (∑ i, m i • f i) : ℚ) := by
  first | (exact @GlobalTheory.AV.AbVar.deg_isHomogeneousPoly) | (exact GlobalTheory.AV.AbVar.deg_isHomogeneousPoly) | (intros; apply GlobalTheory.AV.AbVar.deg_isHomogeneousPoly  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFamilyExpansionEqConstMulAlgClosureStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_family_expansion_eq_const_mul_algClosure : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ E₀ (Φ₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → H0 C.A.L (C.n ^ j)), Eqv D.toPre C.A (Kb R) (C.n ^ j) (C.lab j) E₀ → (∀ F₀ s, F₀.Over s → Agree C.A.L (E₀ s) (Φ₀ F₀)) → ∀ (Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j)), (∀ F₀ (Z : Scheme.{0}) (p : Z ⟶ C.A.A.left) (z : Z) J J', Good C.P.L.L z J → Good C.A.L z J' → sval (Φ F₀) p z J = (gw wA p z (J (p ≫ C.α)) (J' p) ^ (C.n ^ j)).val * sval (Φ₀ F₀) p z J') → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ c : F, c ≠ 0 ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval (Φ F₀) (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J := by
  first | exact @GlobalTheory.Mum.fvalue_const | exact GlobalTheory.Mum.fvalue_const | (intros; apply GlobalTheory.Mum.fvalue_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperSmoothConnGroupSchemeDvrOfProperFibres
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GoodRedProper

theorem isProper_of_proper_fibres :
    ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G], GlobalTheory.SS.SmConn G → IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom → IsProper (GlobalTheory.SS.spFibre G).hom → IsProper G.hom := by
  intro W L _ _ _ _ _ _ G _ h _ h2
  obtain ⟨a, b, c, d, e⟩ := h
  have := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ G
  exact _root_.GlobalTheory.FibreProperDvr.isProper_of_specialFibre W G.left G.hom inferInstance inferInstance inferInstance inferInstance inferInstance h2

end GlobalTheory.GoodRedProper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareRatioValuationWithoutNormFormulaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_ratio_valuation_without_norm_formula : (∀ D, GlobalTheory.NormSum.Inp D) → LNe → TorEx → BotSmall → BotExT → NormBig → BotNe → TriEx → Tower → BotConst → Refl → RhoLow → OneSqSt := by
  first | exact @GlobalTheory.SqTop.OneSqNoSmall.oneSqSt_of_claims' | exact GlobalTheory.SqTop.OneSqNoSmall.oneSqSt_of_claims' | (intros; apply GlobalTheory.SqTop.OneSqNoSmall.oneSqSt_of_claims' <;> assumption)
end

