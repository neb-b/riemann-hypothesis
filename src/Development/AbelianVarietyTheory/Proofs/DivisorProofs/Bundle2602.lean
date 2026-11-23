module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0228
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2532

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotKerIdealDvd
section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.DeRham (spOver spOver_comp)
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.KerPart

variable {k : Type} [Field k] {A B : AbVar k}

def KerPow (f : A ⟶ B) (c : ℕ) (H : Type) [CommRing H] [Algebra k H] (i : ptOver k H ⟶ A.X) : Prop :=
  (i ≫ f.hom = 1 ∧ i ^ c = 1) ∧
    ∀ (R : Type) [CommRing R] [Algebra k R] (x : ptOver k R ⟶ A.X), x ≫ f.hom = 1 → x ^ c = 1 →
      ∃! φ : H →ₐ[k] R, spMap φ.toRingHom ≫ i.left = x.left

theorem finrank_eq_of_kerPow {f : A ⟶ B} {c c' : ℕ} {H H' : Type} [CommRing H] [Algebra k H] [CommRing H']
    [Algebra k H'] {i : ptOver k H ⟶ A.X} {i' : ptOver k H' ⟶ A.X} (h : KerPow f c H i) (h' : KerPow f c' H' i')
    (e : ∀ (R : Type) [CommRing R] [Algebra k R] (x : ptOver k R ⟶ A.X), x ≫ f.hom = 1 → (x ^ c = 1 ↔ x ^ c' = 1)) :
    Module.finrank k H = Module.finrank k H' := by
  obtain ⟨φ, hφ, -⟩ := h.2 H' i' h'.1.1 ((e H' i' h'.1.1).2 h'.1.2)
  obtain ⟨ψ, hψ, -⟩ := h'.2 H i h.1.1 ((e H i h.1.1).1 h.1.2)
  have h1 : ψ.comp φ = AlgHom.id k H := by
    obtain ⟨χ, -, hχ⟩ := h.2 H i h.1.1 h.1.2
    refine (hχ _ ?_).trans (hχ _ ?_).symm
    · change spMap ((ψ : H' →+* H).comp (φ : H →+* H')) ≫ i.left = i.left
      rw [Cris.spMap_comp, Category.assoc]
      exact (congrArg (spMap (ψ : H' →+* H) ≫ ·) hφ).trans hψ
    · change spMap (RingHom.id H) ≫ i.left = i.left
      rw [Cris.spMap_id, Category.id_comp]
  have h2 : φ.comp ψ = AlgHom.id k H' := by
    obtain ⟨χ, -, hχ⟩ := h'.2 H' i' h'.1.1 h'.1.2
    refine (hχ _ ?_).trans (hχ _ ?_).symm
    · change spMap ((φ : H →+* H').comp (ψ : H' →+* H)) ≫ i'.left = i'.left
      rw [Cris.spMap_comp, Category.assoc]
      exact (congrArg (spMap (φ : H →+* H') ≫ ·) hψ).trans hφ
    · change spMap (RingHom.id H') ≫ i'.left = i'.left
      rw [Cris.spMap_id, Category.id_comp]
  exact (AlgEquiv.ofAlgHom φ ψ h2 h1).toLinearEquiv.finrank_eq

theorem pow_eq_one_of_comp {f : A ⟶ B} {g : B ⟶ A} {N : ℕ} (h : f ≫ g = N • 𝟙 A) {T : Over (Sp k)}
    (x : T ⟶ A.X) (hx : x ≫ f.hom = 1) : x ^ N = 1 := by
  have e := congrArg (fun u : A ⟶ A => x ≫ u.hom) h
  simp only [comp_hom, nsmul_hom, id_hom] at e
  rw [← Category.assoc, hx, MonObj.one_comp, MonObj.comp_pow, Category.comp_id] at e
  exact e.symm

section Tower

variable {p : ℕ} {G H : PDivGroup p k} (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B) (n : ℕ)

def kerPt : ptOver k (G.A n ⧸ kerIdeal ((t.map t' f.hom).app n)) ⟶ A.X :=
  spOver (Ideal.Quotient.mkₐ k (kerIdeal ((t.map t' f.hom).app n))) ≫ t.y n

theorem comp_eq_one_iff {R : Type} [CommRing R] [Algebra k R] (φ : G.A n →ₐ[k] R) :
    (spOver φ ≫ t.y n) ≫ f.hom = 1 ↔ kerIdeal ((t.map t' f.hom).app n) ≤ RingHom.ker φ := by
  let u : H.A n →ₐ[k] G.A n := (t.map t' f.hom).app n
  have hu : spOver u ≫ t'.y n = t.y n ≫ f.hom := t.map_y t' f.hom n
  rw [Category.assoc, ← hu, ← Category.assoc, spOver_comp, t'.eq_one_iff]
  exact (kerIdeal_le_ker_iff ((t.map t' f.hom).app n) φ).symm

theorem kerPow_kerPt : KerPow f (p ^ n) _ (kerPt t t' f n) := by
  let I := kerIdeal ((t.map t' f.hom).app n)
  let q := Ideal.Quotient.mkₐ k I
  refine ⟨⟨(comp_eq_one_iff t t' f n q).2 ?_, (t.exists_iff n _).1 ⟨q, rfl⟩⟩, ?_⟩
  · exact fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  · intro R _ _ x hx hp
    obtain ⟨φ, hφ⟩ := t.surj n R x hp
    have hI : I ≤ RingHom.ker φ := (comp_eq_one_iff t t' f n φ).1 (hφ ▸ hx)
    let ψ : G.A n ⧸ I →ₐ[k] R := Ideal.Quotient.liftₐ I φ (fun _ ha => hI ha)
    have hψ : ψ.comp q = φ := AlgHom.ext fun _ => rfl
    have hψx : spOver ψ ≫ kerPt t t' f n = x := by
      change spOver ψ ≫ (spOver q ≫ t.y n) = x
      rw [← Category.assoc, spOver_comp, hψ]
      exact hφ
    refine ⟨ψ, congrArg Over.Hom.left hψx, fun χ hχ => ?_⟩
    have hχx : spOver (χ.comp q) ≫ t.y n = x := by
      rw [← spOver_comp, Category.assoc]
      exact Over.OverMorphism.ext hχ
    exact Ideal.Quotient.algHom_ext k ((t.inj n R _ _ (hχx.trans hφ.symm)).trans hψ.symm)

end Tower

theorem finrank_quot_kerIdeal_dvd {p : ℕ} {G H : PDivGroup p k} (φ : G ⟶ H) (n : ℕ) :
    Module.finrank k (G.A n ⧸ kerIdeal (φ.app n)) ∣ p ^ (n * G.height) := by
  have h := finrank_eq_ker_mul_range k (G.A n) (H.A n) (φ.app n)
  have h2 : Module.finrank k (G.A n) = p ^ (n * G.height) := by
    have h3 := G.fibreDim_eq n ⟨⊥, Ideal.isPrime_bot⟩
    rw [fibreDim, Module.finrank_baseChange] at h3
    exact h3
  exact ⟨_, h2 ▸ h⟩

end GlobalTheory.AV.KerPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagRefinementBundleDimEqBaseAddCardAboveDiagona
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

noncomputable section

namespace GlobalTheory.FlagCell2.Dim

theorem card_low (s : ℕ) : Fintype.card (Low s) = s.choose 2 := by
  have h₁ : Fintype.card (Low s) = ∑ i : Fin s, (Finset.Ioi i).card := by
    rw [← Finset.card_sigma, ← Finset.card_univ]
    refine Finset.card_bij' (fun s _ => ⟨s.1.2, s.1.1⟩) (fun t ht => ⟨(t.2, t.1), by simpa using ht⟩) ?_ ?_ ?_ ?_ <;>
      simp
  rw [h₁, Nat.choose_two_right]
  simp only [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => s - 1 - i), Finset.sum_range_reflect (fun i => i), Finset.sum_range_id]

theorem dim_eq_of_refines {F : Type} [Field F] [CharZero F] {X Y Y' : Var F} {ι : Type} [Fintype ι] {m : ι → ℕ}
    {E : Fr (ratOf X) m 0} {S : Fr (ratOf Y) m m} {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X}
    {S' : Fr (ratOf Y') m m} {φ' : X.Fn →ₐ[F] Y'.Fn} {f' : Y'.X ⟶ X.X}
    (hR : Refines E S φ f) (hR' : Refines E S' φ' f') : Y.dim = Y'.dim := by
  have R₁ := hR.reps
  have R₂ := hR'.reps
  obtain ⟨ψ, hψ, hG⟩ := exists_fieldMap_coBear_generic F ι m X Y Y' E S φ f S' φ' f' R₁ R₂
  obtain ⟨h, hh⟩ := GlobalTheory.ZH.RatModel.exists_isHom_of_map_O F Y'.Fn (ratOf Y') Y.Fn (ratOf Y) ψ
    (dominates_O F ι m X Y Y' E S φ f S' φ' f' R₁ R₂ ψ hψ hG)
  have hf : h ≫ f' = f := by
    have h1 := R₂.1.comp hh
    rw [hψ] at h1
    exact h1.unique R₁.1
  have hb := CoBear₂ F ι m X Y Y' E S φ f S' φ' f' R₁ R₂ h hf
    (coBear_comp_of_isHom F ι m X Y Y' E S φ f S' φ' f' R₁ R₂ ψ hψ hG h hh)
  change Y.X ⟶ Y'.X at h
  have : IsIso h := GlobalTheory.BijPointsIso.isIso_of_bijective_points F Y Y' h hh.inducedModelMorphism_comp_structureMap fun K _ _ => hb K
  have hd : topologicalKrullDim Y.X = topologicalKrullDim Y'.X :=
    IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso (asIso h)).isHomeomorph
  rw [Y.topologicalKrullDim_eq, Y'.topologicalKrullDim_eq] at hd
  exact_mod_cast hd

theorem main : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → Y.dim = X.dim + Fintype.card (Cell m) := by
  intro F _ σ X Y ι _ m E E' φ f _ hR
  have : CharZero F := σ.charZero
  obtain ⟨Y', φ', f', S', hd, hR'⟩ := tower _ (ratOf X) X.dim E (good_ratOf X) (fun _ => Nat.zero_le _) rfl
  rw [dim_eq_of_refines hR hR', hd, Fintype.card_sigma]
  simp only [card_low, Pi.zero_apply, Nat.sub_zero]

end GlobalTheory.FlagCell2.Dim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlaggedBundleMetricSmoothUnitEtaleChart
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem isMetricFr_smoothUnitAt : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (y : CxPts X.str σ), ∀ A ∈ E.S (under y), ∀ τ, SmoothUnitAt (atlas X σ) (fun z => H A z τ) y ∧ ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∀ᶠ v in 𝓝 (c.e y), MContDiffAt ∞ (fun u => H A (c.e.symm u) τ) v ∧ (H A (c.e.symm v) τ).PosDef := by
  intro F _ σ X ι _ m k E H hH y A hA τ
  set U : Set (CxPts X.str σ) := interior {z : CxPts X.str σ | A ∈ E.S (under z)} with hU
  have hyU : y ∈ U := mem_interior_iff_mem_nhds.2 (_root_.GlobalTheory.ChernCalc.frame_eventually_near F σ X ι m k E y A hA)
  have hUo : IsOpen U := isOpen_interior
  have hUS : ∀ z ∈ U, A ∈ E.S (under z) := fun z hz => interior_subset (s := {z : CxPts X.str σ | A ∈ E.S (under z)}) hz
  have key : ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∀ᶠ v in 𝓝 (c.e y),
      MContDiffAt ∞ (fun u => H A (c.e.symm u) τ) v ∧ (H A (c.e.symm v) τ).PosDef := by
    intro c hc
    have ho : IsOpen (c.e.target ∩ c.e.symm ⁻¹' U) := c.e.isOpen_inter_preimage_symm hUo
    have hm : c.e y ∈ c.e.target ∩ c.e.symm ⁻¹' U :=
      ⟨c.e.map_source hc, by simpa [Set.mem_preimage, c.e.left_inv hc] using hyU⟩
    filter_upwards [ho.mem_nhds hm] with v hv
    refine ⟨fun i j => ?_, hH.posDef _ A (hUS _ hv.2) τ⟩
    have hre := contDiffOn_chart (S := U) (f := fun z => (H A z τ i j).re)
      (fun z hz => (hH.smooth z A (hUS z hz) τ i j).1) c
    have him := contDiffOn_chart (S := U) (f := fun z => (H A z τ i j).im)
      (fun z hz => (hH.smooth z A (hUS z hz) τ i j).2) c
    have h1 := (hre.contDiffAt (ho.mem_nhds hv))
    have h2 := (him.contDiffAt (ho.mem_nhds hv))
    have h3 : ContDiffAt ℝ ∞ (fun u => ((((H A (c.e.symm u) τ i j).re : ℝ) : ℂ) +
        (((H A (c.e.symm u) τ i j).im : ℝ) : ℂ) * Complex.I)) v :=
      (Complex.ofRealCLM.contDiff.contDiffAt.comp v h1).add
        ((Complex.ofRealCLM.contDiff.contDiffAt.comp v h2).mul contDiffAt_const)
    refine h3.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
    simp [Complex.re_add_im]
  refine ⟨⟨?_, fun c hc => (key c hc).mono fun v hv => hv.1⟩, key⟩
  exact (Matrix.isUnit_iff_isUnit_det _).1 (hH.posDef y A hA τ).isUnit

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormPartComplComplexPointsInOpenEqZero
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell2Null

theorem part_compl_ptsIn : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (Y : Var F) (β : (atlas Y σ).Fld) (W : Y.X.Opens), genericPoint Y.X ∈ W → ∀ s : ℤˣ, (atlas Y σ).part β s (ptsIn Y.str σ W)ᶜ = 0 := by
  intro F _ σ Y β W hW s
  exact GlueCoverNull.glueMeas_null _ _ (isOpen_ptsIn _).measurableSet.compl fun c =>
    GlobalTheory.Mean4O.CoverInt.volume_image_compl_ptsIn F Y.X Y.str σ σ.injective
      (fun W hW => (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str W).injective) W hW _ c

end GlobalTheory.FlagCell2Null
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormPartEqLintegralImageInjectiveHolomorphic
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

open Function

namespace GlobalTheory.FlagCell2.ChangeOfVariables

theorem part_eq_lintegral_image : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (β : A.Fld), A.IsForm β → ∀ (Ω : Set M) (Φ : M → V n) (γ : V n → Alt n), IsOpen Ω → Set.InjOn Φ Ω → (∀ x : A.Pt, x.pt ∈ Ω → DifferentiableAt ℂ (Φ ∘ x.ch.symm) x.crd ∧ β x = pull (fderiv ℂ (Φ ∘ x.ch.symm) x.crd) (γ (Φ x.pt))) → ∀ (s : ℤˣ) (T : Set M), MeasurableSet T → T ⊆ Ω → A.part β s T = ∫⁻ v in Φ '' T, ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (γ v)).re) := by
  intro M _ _ _ _ _ n A β hβ Ω Φ γ hΩ hinj hloc s T hT hTΩ
  set ρ : A.ι → M → ℝ≥0∞ := fun k y => ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (A.loc β k (A.e k y))).re) with hρ
  have hp : A.part β s = ChartGlue.glueMeas A.e ρ := rfl
  have hρc : ∀ k l y, y ∈ (A.e k).source → y ∈ (A.e l).source →
      ρ k y = ENNReal.ofReal (‖ChartGlue.transDet (A.e k) (A.e l) y‖ ^ 2) * ρ l y := by
    intro k l y hk hl
    have h1 := A.loc_crd β (⟨(k, y), hk⟩ : A.Pt)
    have h2 := A.loc_crd β (⟨(l, y), hl⟩ : A.Pt)
    have h3 := hβ.compat (⟨(k, y), hk⟩ : A.Pt) ⟨(l, y), hl⟩ rfl
    simp only [hρ]
    erw [h1, h2, h3, dens_pull]
    rw [Complex.re_ofReal_mul, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [ChartGlue.transDet]
    ring

  have chart : ∀ (i : A.ι) (P : Set M), MeasurableSet P → P ⊆ (A.e i).source → P ⊆ Ω →
      MeasurableSet (Φ '' P) ∧ A.part β s P =
        ∫⁻ v in Φ '' P, ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (γ v)).re) := by
    intro i P hP hPs hPΩ
    set g : V n → V n := Φ ∘ (A.e i).symm with hg
    have hQ : MeasurableSet (A.e i '' P) := ChartGlue.measurableSet_image (A.e i) hP hPs
    have hder : ∀ v ∈ A.e i '' P, HasFDerivWithinAt g ((fderiv ℂ g v).restrictScalars ℝ) (A.e i '' P) v := by
      rintro _ ⟨y, hy, rfl⟩
      exact ((hloc ⟨(i, y), hPs hy⟩ (hPΩ hy)).1.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    have hinjg : Set.InjOn g (A.e i '' P) := by
      rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hyz
      simp only [hg, Function.comp_apply, (A.e i).left_inv (hPs hy), (A.e i).left_inv (hPs hz)] at hyz
      rw [hinj (hPΩ hy) (hPΩ hz) hyz]
    have himg : Φ '' P = g '' (A.e i '' P) := by
      rw [Set.image_image]
      exact Set.image_congr fun y hy => by simp only [hg, Function.comp_apply, (A.e i).left_inv (hPs hy)]
    refine ⟨himg ▸ measurable_image_of_fderivWithin hQ hder hinjg, ?_⟩
    rw [hp, ChartGlue.glueMeas_apply A.e ρ A.holo hρc i hP hPs, ChartGlue.chartMeas_apply_of_subset _ _ hP hPs, himg,
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hQ hder hinjg]
    refine setLIntegral_congr_fun hQ ?_
    rintro _ ⟨y, hy, rfl⟩
    have hx := hloc ⟨(i, y), hPs hy⟩ (hPΩ hy)
    have hl := A.loc_crd β (⟨(i, y), hPs hy⟩ : A.Pt)
    have hdet : ((fderiv ℂ g (A.e i y)).restrictScalars ℝ).det = Algebra.norm ℝ (fderiv ℂ g (A.e i y)).det :=
      LinearMap.det_restrictScalars (f := (fderiv ℂ g (A.e i y) : V n →ₗ[ℂ] V n))
    have hx2 : β ⟨(i, y), hPs hy⟩ = pull (fderiv ℂ g (A.e i y)) (γ (Φ y)) := hx.2
    have hgy : g (A.e i y) = Φ y := by simp only [hg, Function.comp_apply, (A.e i).left_inv (hPs hy)]
    beta_reduce
    rw [hdet, hgy]
    simp only [hρ, (A.e i).left_inv (hPs hy)]
    erw [hl, hx2, dens_pull]
    rw [Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, abs_of_nonneg (by positivity),
      Complex.re_ofReal_mul, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring

  rcases Set.eq_empty_or_nonempty T with rfl | ⟨y₀, -⟩
  · simp
  obtain ⟨C, hCc, hCU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun j => (A.e j).source)
    (fun j => (A.e j).open_source)
  obtain ⟨f, hf⟩ := (hCc.insert (A.cover y₀).choose).exists_eq_range (Set.insert_nonempty _ _)
  set U : ℕ → Set M := fun k => (A.e (f k)).source with hU
  have hUo : ∀ k, IsOpen (U k) := fun k => (A.e (f k)).open_source
  set P : ℕ → Set M := fun k => T ∩ disjointed U k with hPdef
  have hPm : ∀ k, MeasurableSet (P k) := fun k =>
    hT.inter (MeasurableSet.disjointed (fun k => (hUo k).measurableSet) k)
  have hPU : ∀ k, P k ⊆ U k := fun k => Set.inter_subset_right.trans (disjointed_subset U k)
  have hPΩ : ∀ k, P k ⊆ Ω := fun k => Set.inter_subset_left.trans hTΩ
  have hPd : Pairwise (Disjoint on P) := (disjoint_disjointed U).mono fun k l h =>
    h.mono Set.inter_subset_right Set.inter_subset_right
  have hTP : T = ⋃ k, P k := by
    rw [← Set.inter_iUnion, iUnion_disjointed, eq_comm, Set.inter_eq_left]
    intro y _
    have hy : y ∈ ⋃ j, (A.e j).source := Set.mem_iUnion.2 (A.cover y)
    rw [← hCU] at hy
    obtain ⟨l, hl, hy⟩ := Set.mem_iUnion₂.1 hy
    obtain ⟨k, rfl⟩ := hf.le (Set.mem_insert_of_mem _ hl)
    exact Set.mem_iUnion.2 ⟨k, hy⟩
  have hIm : ∀ k, MeasurableSet (Φ '' P k) := fun k => (chart (f k) (P k) (hPm k) (hPU k) (hPΩ k)).1
  have hId : Pairwise (Disjoint on fun k => Φ '' P k) := by
    intro k l hkl
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have := hinj (hPΩ l hy) (hPΩ k hx) hxy
    subst this
    exact Set.disjoint_left.1 (hPd hkl) hx hy
  rw [hTP, Set.image_iUnion, measure_iUnion hPd hPm, lintegral_iUnion hIm hId]
  exact tsum_congr fun k => (chart (f k) (P k) (hPm k) (hPU k) (hPΩ k)).2

end GlobalTheory.FlagCell2.ChangeOfVariables
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormPartSubsetChartEqLintegralImage
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FlagCell2

theorem part_subset_chart : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (β : A.Fld), A.IsForm β → ∀ (s : ℤˣ) (i : A.ι) (T : Set M), MeasurableSet T → T ⊆ (A.e i).source → A.part β s T = ∫⁻ v in A.e i '' T, ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (A.loc β i v)).re) := by
  intro M _ _ _ _ _ n A β hβ s i T hT hTi
  set ρ : A.ι → M → ENNReal := fun k y => ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (A.loc β k (A.e k y))).re) with hρ
  have hp : A.part β s = ChartGlue.glueMeas A.e ρ := rfl
  have hρc : ∀ k l y, y ∈ (A.e k).source → y ∈ (A.e l).source →
      ρ k y = ENNReal.ofReal (‖ChartGlue.transDet (A.e k) (A.e l) y‖ ^ 2) * ρ l y := by
    intro k l y hk hl
    have h1 := A.loc_crd β (⟨(k, y), hk⟩ : A.Pt)
    have h2 := A.loc_crd β (⟨(l, y), hl⟩ : A.Pt)
    have h3 := hβ.compat (⟨(k, y), hk⟩ : A.Pt) ⟨(l, y), hl⟩ rfl
    simp only [hρ]
    erw [h1, h2, h3, dens_pull]
    rw [Complex.re_ofReal_mul, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [ChartGlue.transDet]
    ring
  rw [hp, ChartGlue.glueMeas_apply A.e ρ A.holo hρc i hT hTi, ChartGlue.chartMeas_apply_of_subset _ _ hT hTi]
  refine setLIntegral_congr_fun (ChartGlue.measurableSet_image _ hT hTi) ?_
  rintro _ ⟨y, hy, rfl⟩
  simp only [hρ, (A.e i).left_inv (hTi hy)]

end GlobalTheory.FlagCell2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalFibreIsReducedOfField
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem isReduced_of_isRegularRing (R : Type) [CommRing R] [IsRegularRing R] : IsReduced R :=
  isReduced_ofLocalizationMaximal R fun P _ => by
    haveI := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing (R := Localization.AtPrime P)
    infer_instance

theorem tensor_map_injective_of_field (A M K L : Type) [CommRing A] [CommRing M] [Algebra A M]
    [Field K] [Field L] [Algebra A K] [Algebra A L] (ι : K →ₐ[A] L) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id A M) ι) := by
  letI : Algebra K L := ι.toRingHom.toAlgebra
  haveI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun a => (ι.commutes a).symm
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.mpr (algebraMap K L).injective)
  have hcomp : (r.restrictScalars A) ∘ₗ ι.toLinearMap = LinearMap.id := by
    ext k
    exact LinearMap.congr_fun hr k
  intro x y hxy
  have h := congrArg (LinearMap.lTensor M (r.restrictScalars A)) hxy
  have key : ∀ z : M ⊗[A] K,
      LinearMap.lTensor M (r.restrictScalars A) (Algebra.TensorProduct.map (AlgHom.id A M) ι z) = z := by
    intro z
    have : (LinearMap.lTensor M (r.restrictScalars A)) ∘ₗ (LinearMap.lTensor M ι.toLinearMap) =
        LinearMap.id := by
      rw [← LinearMap.lTensor_comp, hcomp, LinearMap.lTensor_id]
    have e : Algebra.TensorProduct.map (AlgHom.id A M) ι z = LinearMap.lTensor M ι.toLinearMap z := by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
    rw [e]
    exact LinearMap.congr_fun this z
  rwa [key, key] at h

end GlobalTheory

namespace GlobalTheory

theorem formalFibre_isReduced_of_field :
    ∀ (A L : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A] [Field L] [Algebra A L],
      IsReduced (AdicCompletion (maximalIdeal A) A ⊗[A] L) := by
  intro A L _ _ _ _ _
  classical
  refine ⟨fun x hx => ?_⟩
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
  set T : Subalgebra A L := Algebra.adjoin A ((S.image Prod.snd : Finset L) : Set L) with hT
  haveI : Algebra.FiniteType A T := (Subalgebra.fg_iff_finiteType T).mp (Subalgebra.fg_adjoin_finset _)
  let K := FractionRing T
  haveI : Algebra.EssFiniteType T K := Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors T)
  haveI : Algebra.EssFiniteType A K := Algebra.EssFiniteType.comp A T K
  have hinj : Function.Injective (IsScalarTower.toAlgHom T T L) := Subtype.val_injective
  let ι : K →ₐ[A] L := (IsFractionRing.liftAlgHom (K := K) hinj).restrictScalars A
  have hι : ∀ t : T, ι (algebraMap T K t) = t := fun t => by
    simp [ι, IsFractionRing.liftAlgHom_apply]
  have hmem : ∀ i ∈ S, i.2 ∈ T := fun i hi =>
    Algebra.subset_adjoin (by simpa using ⟨i.1, hi⟩)
  let y : AdicCompletion (maximalIdeal A) A ⊗[A] K :=
    ∑ i ∈ S.attach, i.1.1 ⊗ₜ[A] algebraMap T K ⟨i.1.2, hmem i.1 i.2⟩
  let Φ := Algebra.TensorProduct.map (AlgHom.id A (AdicCompletion (maximalIdeal A) A)) ι
  have hΦ : Φ y = ∑ i ∈ S, i.1 ⊗ₜ[A] i.2 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [y, map_sum, Φ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hι]
    exact Finset.sum_attach S (fun i => i.1 ⊗ₜ[A] i.2)
  haveI : IsRegularRing (AdicCompletion (maximalIdeal A) A ⊗[A] K) :=
    formalFibre_isRegularRing_of_essFiniteType_int A K
  haveI := isReduced_of_isRegularRing (AdicCompletion (maximalIdeal A) A ⊗[A] K)
  obtain ⟨n, hn⟩ := hx
  have hy : IsNilpotent y := ⟨n, tensor_map_injective_of_field A _ K L ι (by rw [map_pow, map_zero, hΦ, hn])⟩
  rw [← hΦ, IsReduced.eq_zero y hy, map_zero]

end GlobalTheory
end

