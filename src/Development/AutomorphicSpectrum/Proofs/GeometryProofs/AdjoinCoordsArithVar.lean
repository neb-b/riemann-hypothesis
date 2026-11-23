module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0020
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0120
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0123
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0118
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0119
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0121
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0122
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0074
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0075
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomogeneousFormNonvanishingPoint

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory.CompanionTheory.Ar.SncRes
variable {Ω : Type} [Field Ω] [CharZero Ω]

theorem closure_facts {N : ℕ} (x : Fin (N + 1) → Ω) (hx : x ≠ 0) :
    IsReduced (point ℚ x hx).image ∧ IsDominant (point ℚ x hx).toImage :=
  _root_.GlobalTheory.CompanionTheory.Ar.SncRes.closure_reduced_dominant Ω N x hx

theorem smooth_basicOpen {Z : Scheme.{0}} (ζ : Sp Ω ⟶ Z) [IsDominant ζ] [IsReduced Z] (g : Z ⟶ Sp ℚ)
    (e : ℕ) {W : Z.Opens} (hW : IsAffineOpen W) (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω)
    (hA : Set.range (valMap ζ W h).hom = A) (σ : Γ(Z, W)) (g₀ : A) (hg : (g₀ : Ω) = valR ζ W σ)
    [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away g₀)] :
    SmoothOfRelativeDimension e ((Z.basicOpen σ).ι ≫ g) :=
  _root_.GlobalTheory.CompanionTheory.Ar.SncRes.smoothOfRelativeDimension_basicOpen_of_away Ω Z ζ g e W hW h A hA σ g₀ hg

theorem lift_generic {X X' : Scheme.{0}} (ξ : Sp Ω ⟶ X) [IsDominant ξ] (f : X' ⟶ X) (U : X.Opens)
    [IsIso (f ∣_ U)] (hd : Dense ((f ⁻¹ᵁ U : X'.Opens) : Set X')) (hU : ⊤ ≤ ξ ⁻¹ᵁ U) :
    ∃ ζ : Sp Ω ⟶ X', ζ ≫ f = ξ ∧ IsDominant ζ ∧ ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U) :=
  _root_.GlobalTheory.CompanionTheory.Ar.Coords.dense_point_lift Ω X X' ξ f U hd hU

theorem exists_coords {r : ℕ} (p : Sp Ω ⟶ PSpace ℚ r) : ∃ (x' : Fin (r + 1) → Ω) (hx' : x' ≠ 0), p = point ℚ x' hx' :=
  _root_.GlobalTheory.CompanionTheory.Ar.TupleCoords.exists_tuple_eq_point Ω r p

theorem val_mem_field {X X' : Scheme.{0}} (ξ : Sp Ω ⟶ X) [IsDominant ξ] [IsReduced X] (f : X' ⟶ X) (U : X.Opens)
    [IsIso (f ∣_ U)] (ζ : Sp Ω ⟶ X') (hζ : ζ ≫ f = ξ) (hU : ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U)) {W₀ : X.Opens}
    (hW₀ : IsAffineOpen W₀) (h₀ : ⊤ ≤ ξ ⁻¹ᵁ W₀) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ξ W₀ h₀).hom = A)
    (W' : X'.Opens) (h' : ⊤ ≤ ζ ⁻¹ᵁ W') (s : Γ(X', W')) :
    valR ζ W' s ∈ IntermediateField.adjoin ℚ (A : Set Ω) :=
  _root_.GlobalTheory.CompanionTheory.Ar.SncRes.valR_mem_adjoin_of_modification Ω X X' ξ f U ζ hζ hU W₀ hW₀ h₀ A hA W' h' s

theorem prod_chart {N r : ℕ} {Z : Scheme.{0}} (j : Z ⟶ pullback (PSpace.str ℚ N) (PSpace.str ℚ r))
    [IsClosedImmersion j] (ζ : Sp Ω ⟶ Z) (x : Fin (N + 1) → Ω) (hx : x ≠ 0) (x' : Fin (r + 1) → Ω) (hx' : x' ≠ 0)
    (h₁ : ζ ≫ j ≫ pullback.fst _ _ = point ℚ x hx) (h₂ : ζ ≫ j ≫ pullback.snd _ _ = point ℚ x' hx')
    (a : Fin (N + 1)) (l : Fin (r + 1)) (ha : x a ≠ 0) (hl : x' l ≠ 0) :
    IsAffineOpen ((j ≫ pullback.fst _ _) ⁻¹ᵁ chart ℚ N a ⊓ (j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l) ∧
      ∃ h : ⊤ ≤ ζ ⁻¹ᵁ ((j ≫ pullback.fst _ _) ⁻¹ᵁ chart ℚ N a ⊓ (j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l),
        Set.range (valMap ζ _ h).hom =
          Algebra.adjoin ℚ (Set.range (fun k => x k / x a) ∪ Set.range (fun k => x' k / x' l)) :=
  _root_.GlobalTheory.CompanionTheory.Ar.SncRes.ProdChart.prod_chart Ω N r Z j ζ x hx x' hx' h₁ h₂ a l ha hl

theorem snc_transfer {Z : Scheme.{0}} (ζ : Sp Ω ⟶ Z) [IsDominant ζ] [IsReduced Z] (g : Z ⟶ Sp ℚ) (e : ℕ) (T : Set Z)
    (hsm : SmoothOfRelativeDimension e g) (hc : HasSncCoords g e T) {W : Z.Opens} (hW : IsAffineOpen W)
    (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ζ W h).hom = A) (σ : Γ(Z, W))
    (hσ : ∀ t ∈ W, t ∈ T ↔ t ∉ Z.basicOpen σ) : SncChart A e (valR ζ W σ) :=
  _root_.GlobalTheory.CompanionTheory.Ar.SncRes.sncChart_of_coords Ω Z ζ g e T hsm hc W hW h A hA σ hσ

theorem form_section {N : ℕ} {Z : Scheme.{0}} (u : Z ⟶ PSpace ℚ N) (η : Sp Ω ⟶ Z) (x : Fin (N + 1) → Ω) (hx : x ≠ 0)
    (hu : η ≫ u = point ℚ x hx) {W : Z.Opens} (hW : ⊤ ≤ η ⁻¹ᵁ W) {a : Fin (N + 1)} (hi : W ≤ u ⁻¹ᵁ chart ℚ N a)
    {n : ℕ} {G : MvPolynomial (Fin (N + 1)) ℚ} (hG : G.IsHomogeneous n) :
    ∃ σ : Γ(Z, W), valR η W σ = aeval (fun j => x j / x a) G ∧
      Z.basicOpen σ = W ⊓ u ⁻¹ᵁ Proj.basicOpen (grading ℚ N) G := by
  refine ⟨(u.appLE _ W hi).hom (formOn (chart ℚ N a) a le_rfl n G hG), ?_, ?_⟩
  · have ha : x a ≠ 0 := ne_zero_of_le hu hW hi
    have h : ⊤ ≤ point ℚ x hx ⁻¹ᵁ chart ℚ N a := (le_point_preimage_iff a).2 ha
    rw [valR_appLE η u hi hW, hu, formOn_eq_aeval, valR_eq _ _ h]
    apply (valMap_eval₂Hom point_str h _ G).trans
    have heq : (fun k => valR (point ℚ x hx) (chart ℚ N a)
        (ratioOn (chart ℚ N a) a le_rfl k)) = (fun k => x k / x a) := by
      funext k
      change valR (point ℚ x hx) (chart ℚ N a) (ratio ℚ N a k) = x k / x a
      have hu : IsUnit ((aeval x).toRingHom (X a : MvPolynomial (Fin (N + 1)) ℚ)) := by simpa using ha
      have hpre : ⊤ ≤ Proj.awayι (grading ℚ N) (X a) (X_mem ℚ N a) Nat.one_pos ⁻¹ᵁ chart ℚ N a := by
        have e1 := Scheme.Hom.preimage_opensRange
          (Proj.awayι (grading ℚ N) (X a) (X_mem ℚ N a) Nat.one_pos)
        rw [Proj.opensRange_awayι] at e1
        exact e1.ge
      have hmem : (X k : MvPolynomial (Fin (N + 1)) ℚ) ∈ grading ℚ N (1 • 1) := by
        simpa using X_mem ℚ N k
      have hA : ratio ℚ N a k = (Proj.awayToSection (grading ℚ N) (X a)).hom
          (HomogeneousLocalization.Away.mk (grading ℚ N) (X_mem ℚ N a) 1 (X k) hmem) := by
        rw [ProjFrac.awayToSection_mk]
        exact ProjFrac.frac_eq (by ring)
      have key : Proj.awayToSection (grading ℚ N) (X a) ≫
          (Proj.awayι (grading ℚ N) (X a) (X_mem ℚ N a) Nat.one_pos).appLE (chart ℚ N a) ⊤ hpre =
          (Scheme.ΓSpecIso _).inv := by
        set A := Proj.awayι (grading ℚ N) (X a) (X_mem ℚ N a) Nat.one_pos
        set e := Proj.basicOpenIsoSpec (grading ℚ N) (X a) (X_mem ℚ N a) Nat.one_pos
        have : IsIso (Proj.awayToSection (grading ℚ N) (X a)) :=
          (Proj.basicOpenIsoAway (grading ℚ N) (X a) (X_mem ℚ N a) Nat.one_pos).isIso_hom
        have hι : e.hom ≫ A = (chart ℚ N a).ι := by
          exact Iso.hom_inv_id_assoc e _
        have gen : ∀ (g : (chart ℚ N a).toScheme ⟶ Proj (grading ℚ N)) (_ : e.hom ≫ A = g)
            (hle : ⊤ ≤ g ⁻¹ᵁ chart ℚ N a),
            g.appLE (chart ℚ N a) ⊤ hle = A.appLE (chart ℚ N a) ⊤ hpre ≫ e.hom.appLE ⊤ ⊤ le_rfl := by
          rintro g rfl hle
          exact (Scheme.Hom.appLE_comp_appLE e.hom A (chart ℚ N a) ⊤ ⊤ hpre _).symm
        have h1 := gen _ hι (chart ℚ N a).ι_preimage_self.ge
        have F1 : e.hom.appLE ⊤ ⊤ le_rfl = (Scheme.ΓSpecIso _).hom ≫
            Proj.awayToSection (grading ℚ N) (X a) ≫ (chart ℚ N a).topIso.inv := by
          rw [← Proj.basicOpenToSpec_app_top]
          rfl
        have F2 : (chart ℚ N a).ι.appLE (chart ℚ N a) ⊤ (chart ℚ N a).ι_preimage_self.ge =
            (chart ℚ N a).topIso.inv := by
          rw [Scheme.Opens.ι_appLE]
          rfl
        rw [F2, F1] at h1
        have h3 : A.appLE (chart ℚ N a) ⊤ hpre ≫ (Scheme.ΓSpecIso _).hom ≫
            Proj.awayToSection (grading ℚ N) (X a) = 𝟙 _ := by
          rw [← cancel_mono (chart ℚ N a).topIso.inv, Category.id_comp, Category.assoc, Category.assoc]
          exact h1.symm
        rw [← cancel_mono ((Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection (grading ℚ N) (X a)),
          Category.assoc, h3, Category.comp_id, Iso.inv_hom_id_assoc]
      rw [point, ProjPoint.ofHom_eq_awayι _ _ _ Nat.one_pos (X_mem ℚ N a) hu,
        ← valR_appLE _ _ hpre (le_preimage_top _), hA, ← CommRingCat.comp_apply, key, valR_specMap]
      apply eq_div_of_mul_eq ha
      simpa using ProjPoint.awayLift_mk_mul (grading ℚ N) ((aeval x).toRingHom) hu (X_mem ℚ N a) 1 (X k) hmem
    rw [heq]
  · rw [Scheme.basicOpen_appLE, basicOpen_formOn]
    refine le_antisymm (le_inf inf_le_left (inf_le_right.trans (u.preimage_mono inf_le_right)))
      (le_inf inf_le_left ?_)
    rintro t ⟨h1, h2⟩
    exact ⟨hi h1, h2⟩

theorem chart_single {N : ℕ} {Z : Scheme.{0}} (i : Z ⟶ PSpace ℚ N) [IsClosedImmersion i] (ζ : Sp Ω ⟶ Z)
    (x : Fin (N + 1) → Ω) (hx : x ≠ 0) (hi : ζ ≫ i = point ℚ x hx) (a : Fin (N + 1)) (ha : x a ≠ 0) :
    IsAffineOpen (i ⁻¹ᵁ chart ℚ N a) ∧ ∃ h : ⊤ ≤ ζ ⁻¹ᵁ (i ⁻¹ᵁ chart ℚ N a),
      Set.range (valMap ζ _ h).hom = Algebra.adjoin ℚ (Set.range fun k => x k / x a) := by
  have hc := (isAffineOpen_chart ℚ N a)
  refine ⟨hc.preimage i, le_preimage_chart hi ha, ?_⟩
  have h₁ : ⊤ ≤ point ℚ x hx ⁻¹ᵁ chart ℚ N a := (le_point_preimage_iff a).2 ha
  rw [← range_valMap_point h₁, ← (i.app_surjective _ hc).range_comp]
  congr 1
  funext s
  have := valR_comp ζ i (chart ℚ N a) s
  rw [hi, valR_eq _ _ h₁, valR_eq _ _ (le_preimage_chart hi ha)] at this
  exact this.symm

theorem snc_of_res (hR : ResKStatement) (N e d : ℕ) (x : Fin (N + 1) → Ω) (c₀ : Fin (N + 1)) (hc₀ : x c₀ ≠ 0)
    (G : MvPolynomial (Fin (N + 1)) ℚ) (hG : G.IsHomogeneous (d + 1)) (hdiv : (X c₀ : MvPolynomial _ ℚ) ∣ G)
    (g₀ : Algebra.adjoin ℚ (Set.range fun j => x j / x c₀))
    (hg₀ : (g₀ : Ω) = aeval (fun j => x j / x c₀) G) (h0 : g₀ ≠ 0)
    [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away g₀)] :
    ∃ (r : ℕ) (x' : Fin (r + 1) → Ω), x' ≠ 0 ∧
      (∀ i l, x' l ≠ 0 → x' i / x' l ∈
        IntermediateField.adjoin ℚ ((Algebra.adjoin ℚ (Set.range fun j => x j / x c₀) : Subalgebra ℚ Ω) : Set Ω)) ∧
      ∀ a l, x a ≠ 0 → x' l ≠ 0 →
        SncChart (Algebra.adjoin ℚ (Set.range (fun k => x k / x a) ∪ Set.range (fun k => x' k / x' l))) e
          (aeval (fun j => x j / x a) G) := by
  have hx : x ≠ 0 := fun h => hc₀ (by simp [h])
  obtain ⟨hred, hdom⟩ := closure_facts x hx
  set p := point ℚ x hx with hp
  have hπ : p.toImage ≫ p.imageι = point ℚ x hx := Scheme.Hom.toImage_imageι p
  obtain ⟨hW₀, h₀, hA₀⟩ := chart_single p.imageι p.toImage x hx hπ c₀ hc₀
  obtain ⟨σ₀, hσ₀, hb₀⟩ := form_section p.imageι p.toImage x hx hπ h₀ le_rfl hG
  have hsub : Proj.basicOpen (grading ℚ N) G ≤ chart ℚ N c₀ := by
    obtain ⟨G', rfl⟩ := hdiv
    rw [Proj.basicOpen_mul]
    exact inf_le_left
  set U : (p.image).Opens := p.imageι ⁻¹ᵁ Proj.basicOpen (grading ℚ N) G with hUdef
  have hUb : p.image.basicOpen σ₀ = U := by
    rw [hb₀]
    exact inf_eq_right.2 (p.imageι.preimage_mono hsub)
  have hval : valR p.toImage _ σ₀ = g₀ := by rw [hσ₀, hg₀]
  have hUtop : ⊤ ≤ p.toImage ⁻¹ᵁ U := by
    rw [← hUb, le_preimage_basicOpen_iff _ h₀, hval]
    exact isUnit_iff_ne_zero.2 (by simpa using h0)
  have hsmU : SmoothOfRelativeDimension e (U.ι ≫ p.imageι ≫ PSpace.str ℚ N) := by
    have := smooth_basicOpen p.toImage (p.imageι ≫ PSpace.str ℚ N) e hW₀ h₀ _ hA₀ σ₀ g₀ hval.symm
    rwa [hUb] at this
  have hdense : Dense (U : Set p.image) := by
    refine p.toImage.denseRange.mono ?_
    rintro _ ⟨y, rfl⟩
    exact hUtop (Set.mem_univ y)
  obtain ⟨r, X', j, f, hj, hf, hsm, hiso, hd, hco⟩ := hR ℚ N e p.image p.imageι U ⟨inferInstance, hred, hdense, hsmU⟩
  obtain ⟨ζ, hζ, hdomζ, hζU⟩ := lift_generic p.toImage f U hd hUtop
  obtain ⟨x', hx', hp₂⟩ := exists_coords (ζ ≫ j ≫ pullback.snd _ _)
  have hp₁ : ζ ≫ j ≫ pullback.fst _ _ = point ℚ x hx := by
    rw [← hf, reassoc_of% hζ, hπ]
  have : Smooth (f ≫ p.imageι ≫ PSpace.str ℚ N) := hsm.smooth
  have hredX' : IsReduced X' := GlobalTheory.isReduced_of_smooth_of_isReduced (f ≫ p.imageι ≫ PSpace.str ℚ N)
  refine ⟨r, x', hx', fun i l hl => ?_, fun a l ha hl => ?_⟩
  · have hW : ⊤ ≤ ζ ⁻¹ᵁ ((j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l) := le_preimage_chart (by simpa using hp₂) hl
    have := val_mem_field p.toImage f U ζ hζ hζU hW₀ h₀ _ hA₀ _ hW
      (pullRatio (j ≫ pullback.snd _ _) _ l le_rfl i)
    have hratio : valR (point ℚ x' hx') (chart ℚ r l) (ratio ℚ r l i) = x' i / x' l := by
      have hu : IsUnit ((aeval x').toRingHom (X l : MvPolynomial (Fin (r + 1)) ℚ)) := by simpa using hl
      have hpre : ⊤ ≤ Proj.awayι (grading ℚ r) (X l) (X_mem ℚ r l) Nat.one_pos ⁻¹ᵁ chart ℚ r l := by
        have e1 := Scheme.Hom.preimage_opensRange
          (Proj.awayι (grading ℚ r) (X l) (X_mem ℚ r l) Nat.one_pos)
        rw [Proj.opensRange_awayι] at e1
        exact e1.ge
      have hmem : (X i : MvPolynomial (Fin (r + 1)) ℚ) ∈ grading ℚ r (1 • 1) := by
        simpa using X_mem ℚ r i
      have hA : ratio ℚ r l i = (Proj.awayToSection (grading ℚ r) (X l)).hom
          (HomogeneousLocalization.Away.mk (grading ℚ r) (X_mem ℚ r l) 1 (X i) hmem) := by
        rw [ProjFrac.awayToSection_mk]
        exact ProjFrac.frac_eq (by ring)
      have key : Proj.awayToSection (grading ℚ r) (X l) ≫
          (Proj.awayι (grading ℚ r) (X l) (X_mem ℚ r l) Nat.one_pos).appLE (chart ℚ r l) ⊤ hpre =
          (Scheme.ΓSpecIso _).inv := by
        set A := Proj.awayι (grading ℚ r) (X l) (X_mem ℚ r l) Nat.one_pos
        set e := Proj.basicOpenIsoSpec (grading ℚ r) (X l) (X_mem ℚ r l) Nat.one_pos
        have : IsIso (Proj.awayToSection (grading ℚ r) (X l)) :=
          (Proj.basicOpenIsoAway (grading ℚ r) (X l) (X_mem ℚ r l) Nat.one_pos).isIso_hom
        have hι : e.hom ≫ A = (chart ℚ r l).ι := by
          exact Iso.hom_inv_id_assoc e _
        have gen : ∀ (g : (chart ℚ r l).toScheme ⟶ Proj (grading ℚ r)) (_ : e.hom ≫ A = g)
            (hle : ⊤ ≤ g ⁻¹ᵁ chart ℚ r l),
            g.appLE (chart ℚ r l) ⊤ hle = A.appLE (chart ℚ r l) ⊤ hpre ≫ e.hom.appLE ⊤ ⊤ le_rfl := by
          rintro g rfl hle
          exact (Scheme.Hom.appLE_comp_appLE e.hom A (chart ℚ r l) ⊤ ⊤ hpre _).symm
        have h1 := gen _ hι (chart ℚ r l).ι_preimage_self.ge
        have F1 : e.hom.appLE ⊤ ⊤ le_rfl = (Scheme.ΓSpecIso _).hom ≫
            Proj.awayToSection (grading ℚ r) (X l) ≫ (chart ℚ r l).topIso.inv := by
          rw [← Proj.basicOpenToSpec_app_top]
          rfl
        have F2 : (chart ℚ r l).ι.appLE (chart ℚ r l) ⊤ (chart ℚ r l).ι_preimage_self.ge =
            (chart ℚ r l).topIso.inv := by
          rw [Scheme.Opens.ι_appLE]
          rfl
        rw [F2, F1] at h1
        have h3 : A.appLE (chart ℚ r l) ⊤ hpre ≫ (Scheme.ΓSpecIso _).hom ≫
            Proj.awayToSection (grading ℚ r) (X l) = 𝟙 _ := by
          rw [← cancel_mono (chart ℚ r l).topIso.inv, Category.id_comp, Category.assoc, Category.assoc]
          exact h1.symm
        rw [← cancel_mono ((Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection (grading ℚ r) (X l)),
          Category.assoc, h3, Category.comp_id, Iso.inv_hom_id_assoc]
      rw [point, ProjPoint.ofHom_eq_awayι _ _ _ Nat.one_pos (X_mem ℚ r l) hu,
        ← valR_appLE _ _ hpre (le_preimage_top _), hA, ← CommRingCat.comp_apply, key, valR_specMap]
      apply eq_div_of_mul_eq hl
      simpa using ProjPoint.awayLift_mk_mul (grading ℚ r) ((aeval x').toRingHom) hu (X_mem ℚ r l) 1 (X i) hmem
    rw [pullRatio, valR_appLE ζ (j ≫ pullback.snd _ _) le_rfl hW, hp₂, hratio] at this
    exact this
  · obtain ⟨hWa, hW, hAW⟩ := prod_chart j ζ x hx x' hx' hp₁ hp₂ a l ha hl
    obtain ⟨σ, hσ, hb⟩ := form_section (j ≫ pullback.fst _ _) ζ x hx (by simpa using hp₁) hW inf_le_left hG
    rw [← hσ]
    refine snc_transfer ζ (f ≫ p.imageι ≫ PSpace.str ℚ N) e _ hsm hco hWa hW _ hAW σ fun t ht => ?_
    rw [hb]
    have e₁ : (j ≫ pullback.fst _ _) t = p.imageι (f t) := by
      rw [← hf]
      rfl
    constructor
    · rintro h ⟨-, h2⟩
      exact h (show p.imageι (f t) ∈ Proj.basicOpen (grading ℚ N) G from e₁ ▸ h2)
    · intro h h2
      exact h ⟨ht, show (j ≫ pullback.fst _ _) t ∈ Proj.basicOpen (grading ℚ N) G from e₁ ▸ h2⟩

section Top
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_smooth (y : (Σ k, ι k) → Ω) (e : ℕ) (hA : IsArithVar (mCoordIdeal y) (e + 1)) (N : ℕ)
    (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1)) (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) :
    ∃ s : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩), s ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s) :=
  _root_.GlobalTheory.CompanionTheory.Ar.SegreChart.exists_away_standardSmooth Ω K ι y e hA N E c₀ hc

theorem exists_form (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (b : K → ℕ) (hb : IsMultiHomog β b)
    (hβ : β ∉ mCoordIdeal y) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1))
    (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0)
    (s : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩)) (hs : s ≠ 0)
    [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s)] :
    ∃ (d : ℕ) (Gz : MvPolynomial (Fin (N + 1)) ℤ)
      (g₀ : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩)),
      Gz.IsHomogeneous (d + 1) ∧ (X c₀ : MvPolynomial _ ℤ) ∣ Gz ∧
      (g₀ : Ω) = aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) Gz ∧ g₀ ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away g₀) ∧
      ∀ z ∈ mcPts (mCoordIdeal y), evC z β = 0 →
        eval (fun j => ∏ k, z ⟨k, E j k⟩) (map (Int.castRingHom ℂ) Gz) = 0 :=
  _root_.GlobalTheory.CompanionTheory.Ar.SncRes.exists_segre_form Ω K ι y e β b hb hβ N E c₀ hc s hs

theorem final_data (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k))
    (d : ℕ) (Gz : MvPolynomial (Fin (N + 1)) ℤ) (r : ℕ) (x' : Fin (r + 1) → Ω)
    (hG : Gz.IsHomogeneous (d + 1)) (h0 : aeval (fun j => ∏ k, y ⟨k, E j k⟩) Gz ≠ 0)
    (hβ : ∀ z ∈ mcPts (mCoordIdeal y), evC z β = 0 →
      eval (fun j => ∏ k, z ⟨k, E j k⟩) (map (Int.castRingHom ℂ) Gz) = 0)
    (hx' : x' ≠ 0) (hF : ∀ i l, x' l ≠ 0 → x' i / x' l ∈ blockFnField y)
    (hch : ∀ a l, (∏ k, y ⟨k, E a k⟩) ≠ 0 → x' l ≠ 0 →
      SncChart (Algebra.adjoin ℚ (Set.range (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) ∪
        Set.range (fun k => x' k / x' l))) e
        (aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) (map (algebraMap ℤ ℚ) Gz))) :
    ∃ (y' : (Σ _ : Unit, Fin (r + 1)) → Ω) (J : Ideal (MRing (joinIdx ι fun _ : Unit => Fin (r + 1)))),
      (∃ i, y' ⟨(), i⟩ ≠ 0) ∧ blockFnField (joinVec y y') = blockFnField y ∧ IsMultiHomogIdeal J ∧
      ¬ J ≤ mCoordIdeal (joinVec y y') ∧ IsSncModel (joinVec y y') e J ∧
      ∀ z ∈ mcPts (mCoordIdeal (joinVec y y')),
        evC z (rename (joinInl ι fun _ : Unit => Fin (r + 1)) β) = 0 → z ∈ mcPts J :=
  _root_.GlobalTheory.CompanionTheory.Ar.SegreChart.final_data_main Ω K ι y e β N E d Gz r x' hG h0 hβ hx' hF hch

theorem adjoin_seg_le (y : (Σ k, ι k) → Ω) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1))
    (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) :
    IntermediateField.adjoin ℚ ((Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) :
      Subalgebra ℚ Ω) : Set Ω) ≤ blockFnField y := by
  rw [IntermediateField.adjoin_le_iff]
  have h1 : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) ≤
      (blockFnField y).toSubalgebra := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    change (∏ k, y ⟨k, E j k⟩) / (∏ k, y ⟨k, E c₀ k⟩) ∈ blockFnField y
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => IntermediateField.subset_adjoin _ _ ⟨⟨k, E j k⟩, ⟨k, E c₀ k⟩, rfl, rfl⟩
  exact h1

theorem exists_snc_model : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (b : K → ℕ), IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomog β b → β ∉ mCoordIdeal y → ∃ (M : ℕ) (y' : (Σ _ : Unit, Fin M) → Ω) (J : Ideal (MRing (joinIdx ι fun _ : Unit => Fin M))), (∃ i, y' ⟨(), i⟩ ≠ 0) ∧ blockFnField (joinVec y y') = blockFnField y ∧ IsMultiHomogIdeal J ∧ ¬ J ≤ mCoordIdeal (joinVec y y') ∧ IsSncModel (joinVec y y') e J ∧ ∀ z ∈ mcPts (mCoordIdeal (joinVec y y')), evC z (rename (joinInl ι fun _ : Unit => Fin M) β) = 0 → z ∈ mcPts J := by
  intro hR K _ ι _ Ω _ _ y e β b hA hb hβ
  classical
  obtain ⟨-, ⟨-, -, hrel⟩, -, -⟩ := id hA
  choose c hc using hrel
  have hc' : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hc k (by
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul])
  have : Nonempty ((k : K) → ι k) := ⟨c⟩
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card ((k : K) → ι k) = N + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  let E : Fin (N + 1) ≃ ((k : K) → ι k) := (Fintype.equivFinOfCardEq hN).symm
  let c₀ := E.symm c
  have hE : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0 := fun k => by simpa [c₀] using hc' k
  obtain ⟨s, hs, hsm⟩ := exists_smooth y e hA N E c₀ hE
  obtain ⟨d, Gz, g₀, hG, hdiv, hg₀, hg0, hsm₀, hz⟩ := exists_form y e β b hb hβ N E c₀ hE s hs
  let x : Fin (N + 1) → Ω := fun j => ∏ k, y ⟨k, E j k⟩
  have hx₀ : x c₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hE k
  let G := map (algebraMap ℤ ℚ) Gz
  obtain ⟨r, x', hx', hF, hch⟩ := snc_of_res hR N e d x c₀ hx₀ G (hG.map _)
    (by simpa [G] using map_dvd (MvPolynomial.map (algebraMap ℤ ℚ)) hdiv) g₀
    (by rw [hg₀]; exact (aeval_map_algebraMap ℚ _ _).symm) hg0
  obtain ⟨y', J, h⟩ := final_data y e β N E d Gz r x' hG (by
      intro h
      have h1 : aeval (fun j => x j / x c₀) Gz = 0 := by
        simp only [div_eq_inv_mul]
        rw [GlobalTheory.CompanionTheory.Ar.ProjCoord.aeval_mul_of_isHomogeneous x _ hG]
        exact mul_eq_zero_of_right _ h
      exact hg0 (Subtype.ext (hg₀.trans h1))) hz hx'
    (fun i l hl => adjoin_seg_le y N E c₀ hE (hF i l hl)) (fun a l ha hl => hch a l ha hl)
  exact ⟨r + 1, y', J, h⟩
end Top

end GlobalTheory.CompanionTheory.Ar.SncRes
