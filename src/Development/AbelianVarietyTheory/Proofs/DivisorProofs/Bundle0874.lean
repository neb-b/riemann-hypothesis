module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0847
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0573
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0864
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleEquivalenceSchemeOfStrictlyHenselianStalks
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ColumnDataLaws
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VacuumCharacterDeterminant
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0848

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetVolumeWeightedSumConj
section
open MeasureTheory Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.OrbDesc

variable {H : Type} [Group H]

theorem locPart_conj (T L : Subgroup H) (c x : H) :
    GlobalTheory.LKLoc.locPart (T.map (MulAut.conj c).toMonoidHom) (L.map (MulAut.conj c).toMonoidHom)
      (MulAut.conj c x) = (GlobalTheory.LKLoc.locPart T L x).map (MulAut.conj c).toMonoidHom := by
  unfold GlobalTheory.LKLoc.locPart
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective, Subgroup.map_map, Subgroup.map_map]
  congr 2
  ext k
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply]
  group

theorem volRat_conj (U V : Subgroup H) (c : H) :
    GlobalTheory.LKLoc.volRat (U.map (MulAut.conj c).toMonoidHom) (V.map (MulAut.conj c).toMonoidHom) =
      GlobalTheory.LKLoc.volRat U V := by
  unfold GlobalTheory.LKLoc.volRat
  rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective]

theorem wt_conj (T L U : Subgroup H) (Ψ : H → ℂ) (c x : H) :
    wt (T.map (MulAut.conj c).toMonoidHom) (L.map (MulAut.conj c).toMonoidHom)
      (U.map (MulAut.conj c).toMonoidHom) (fun y => Ψ (c⁻¹ * y * c)) (MulAut.conj c x) = wt T L U Ψ x := by
  unfold wt
  rw [locPart_conj, volRat_conj]
  congr 2
  simp only [MulAut.conj_apply]
  group

theorem dsum_conj : ∀ (H : Type) [Group H] (T L U : Subgroup H) (Ψ : H → ℂ) (c : H),
  (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) → (∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x) → (∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x) →
  GlobalTheory.OrbDesc.dsum T L U Ψ = GlobalTheory.OrbDesc.dsum (T.map (MulAut.conj c).toMonoidHom) (L.map (MulAut.conj c).toMonoidHom)
    (U.map (MulAut.conj c).toMonoidHom) (fun x => Ψ (c⁻¹ * x * c)) := by
  intro H _ T L U Ψ c hT hΨl hΨr
  set φ := MulAut.conj c with hφ
  have hT' : ∀ s ∈ T.map φ.toMonoidHom, ∀ t ∈ T.map φ.toMonoidHom, s * t = t * s := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hT s hs t ht]
  have hΨl' : ∀ t ∈ T.map φ.toMonoidHom, ∀ x, Ψ (c⁻¹ * (t * x) * c) = Ψ (c⁻¹ * x * c) := by
    rintro _ ⟨t, ht, rfl⟩ x
    have : c⁻¹ * (φ.toMonoidHom t * x) * c = t * (c⁻¹ * x * c) := by
      simp only [hφ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
    rw [this, hΨl t ht]
  have hΨr' : ∀ l ∈ L.map φ.toMonoidHom, ∀ x, Ψ (c⁻¹ * (x * l) * c) = Ψ (c⁻¹ * x * c) := by
    rintro _ ⟨l, hl, rfl⟩ x
    have : c⁻¹ * (x * φ.toMonoidHom l) * c = (c⁻¹ * x * c) * l := by
      simp only [hφ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
    rw [this, hΨr l hl]
  let E : DoubleCoset.Quotient (T : Set H) (L : Set H) ≃
      DoubleCoset.Quotient ((T.map φ.toMonoidHom : Subgroup H) : Set H) ((L.map φ.toMonoidHom : Subgroup H) : Set H) :=
    Quotient.congr φ.toEquiv (by
      intro a b
      rw [DoubleCoset.rel_iff, DoubleCoset.rel_iff]
      constructor
      · rintro ⟨t, ht, l, hl, rfl⟩
        exact ⟨φ t, ⟨t, ht, rfl⟩, φ l, ⟨l, hl, rfl⟩, by simp [map_mul]⟩
      · rintro ⟨_, ⟨t, ht, rfl⟩, _, ⟨l, hl, rfl⟩, h⟩
        refine ⟨t, ht, l, hl, φ.injective ?_⟩
        simpa [map_mul] using h)
  unfold dsum
  rw [← finsum_comp_equiv E]
  congr 1
  ext q
  have hE : E q = DoubleCoset.mk _ _ (φ (Quotient.out q)) := by
    conv_lhs => rw [← DoubleCoset.out_eq' q]
    rfl
  rw [hE, wt_out _ hT' hΨl' hΨr', wt_conj]

end GlobalTheory.OrbDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingReducedResidueFieldBijectiveUnramified
section
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PrimePart

open Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg

theorem exists_inv_of_not_dvd_discr (E : Type) [Field E] [NumberField E] {V : Type} [CommRing V] [IsDomain V]
    [IsLocalRing V] {Fr : Type} [Field Fr] [Algebra V Fr]
    [DecidableEq (E →+* ℂ)] (hinj : Function.Injective (algebraMap V Fr)) {F : Type} [Field F] (j : F →+* ℂ)
    (io : F →+* Fr)
    (φ : (E →+* ℂ) → (E →+* F)) (hφ : ∀ σ x, j (φ σ x) = σ x)
    (χ : (E →+* ℂ) → (𝓞 E →+* V)) (hχ : ∀ σ (a : 𝓞 E), algebraMap V Fr (χ σ a) = io (φ σ (a : E)))
    (g : ℕ) (hg : g.Prime) (hgV : ¬ IsUnit (g : V)) (hd : ¬ (g : ℤ) ∣ discr E) :
    ∃ Cm : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → (E →+* ℂ) → V,
      (∀ σ τ, ∑ i, χ σ (RingOfIntegers.basis E i) * Cm i τ = if σ = τ then 1 else 0) ∧
      (∀ i i', ∑ τ, Cm i τ * χ τ (RingOfIntegers.basis E i') = if i = i' then 1 else 0) := by
  classical
  let bs := RingOfIntegers.basis E
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) = Fintype.card (E →ₐ[ℚ] ℂ) := by
    rw [AlgHom.card, ← RingOfIntegers.rank, Module.finrank_eq_card_chooseBasisIndex]
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →ₐ[ℚ] ℂ) := Fintype.equivOfCardEq hcard
  let e' : Module.Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →+* ℂ) := e.trans (RingHom.equivRatAlgHom E ℂ).symm
  let A : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) V :=
    fun i k => χ (e' k) (bs i)
  have hAij : ∀ i k, A i k = χ (e' k) (bs i) := fun _ _ => rfl
  let AF : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) F :=
    fun i k => φ (e' k) (bs i : E)
  have hAF : AF.map j = Algebra.embeddingsMatrixReindex ℚ ℂ (fun i => (bs i : E)) e := by
    ext i k
    simp only [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix,
      Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, Equiv.refl_symm, Equiv.refl_apply,
      Equiv.symm_symm]
    show j (φ (e' k) (bs i : E)) = (e k) (bs i : E)
    rw [hφ]
    rfl
  have hdF : AF.det ^ 2 = ((discr E : ℤ) : F) := by
    apply j.injective
    rw [map_pow, RingHom.map_det, RingHom.mapMatrix_apply, hAF,
      ← Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two, map_intCast]
    have hb : (fun i => (bs i : E)) = ⇑(integralBasis E) := funext fun i => (integralBasis_apply E i).symm
    rw [hb, ← coe_discr, map_intCast]
  have hdV : A.det ^ 2 = ((discr E : ℤ) : V) := by
    apply hinj
    rw [map_pow, RingHom.map_det, map_intCast]
    have hA : (algebraMap V Fr).mapMatrix A = io.mapMatrix AF := by
      ext i k
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hAij, AF, hχ]
      rfl
    rw [hA, ← RingHom.map_det, ← map_pow, hdF, map_intCast]
  have hu : IsUnit A.det := by
    have h := isUnit_of_not_dvd g hg hgV _ hd
    rw [← hdV] at h
    exact (isUnit_pow_iff two_ne_zero).1 h
  refine ⟨fun i τ => A⁻¹ (e'.symm τ) i, ?_, ?_⟩
  · intro σ τ
    have h1 := congrFun (congrFun (Matrix.nonsing_inv_mul A hu) (e'.symm τ)) (e'.symm σ)
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    simp only [hAij, Equiv.apply_symm_apply] at h1
    rw [show (∑ i, χ σ (bs i) * A⁻¹ (e'.symm τ) i) = ∑ i, A⁻¹ (e'.symm τ) i * χ σ (bs i) from
      Finset.sum_congr rfl fun _ _ => mul_comm _ _, h1]
    by_cases h : σ = τ
    · subst h; simp
    · rw [if_neg (fun h' => h (e'.symm.injective h').symm), if_neg h]
  · intro i i'
    have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv A hu) i') i
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    simp only [hAij] at h1
    rw [← Equiv.sum_comp e' (fun τ => A⁻¹ (e'.symm τ) i * χ τ (bs i'))]
    simp only [Equiv.symm_apply_apply]
    rw [show (∑ k, A⁻¹ k i * χ (e' k) (bs i')) = ∑ k, χ (e' k) (bs i') * A⁻¹ k i from
      Finset.sum_congr rfl fun _ _ => mul_comm _ _, h1]
    by_cases h : i = i'
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]

theorem red_bijective (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H)
    (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p)
    (hp : UnramIn E p) : Function.Bijective (red io X) := by
  classical
  haveI : IsDomain X.O := X.ints.hom_inj.isDomain _
  obtain ⟨Cm, hAC, hCA⟩ := exists_inv_of_not_dvd_discr E (V := X.O) (Fr := X.C) X.ints.hom_inj
    (c.F.val : c.F →+* ℂ) (X.ιF.comp io) (embF c) (fun σ x => by simp [embF])
    (embO io X) (fun σ a => algebraMap_embO io X σ a) p Fact.out X.nonunit.out hp
  set b := RingOfIntegers.basis E
  let Cr : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → (E →+* ℂ) → ResidueField X.O := fun i τ => residue X.O (Cm i τ)
  have hAC' : ∀ σ τ, ∑ i, red io X σ (b i) * Cr i τ = if σ = τ then 1 else 0 := by
    intro σ τ
    have := congrArg (residue X.O) (hAC σ τ)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, red, Cr, apply_ite (residue X.O)] using this
  have hCA' : ∀ i i', ∑ τ, Cr i τ * red io X τ (b i') = if i = i' then 1 else 0 := by
    intro i i'
    have := congrArg (residue X.O) (hCA i i')
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, red, Cr, apply_ite (residue X.O)] using this
  refine ⟨fun σ τ hst => ?_, fun χ => ?_⟩
  · by_contra hne
    have h1 := hAC' σ τ
    rw [if_neg hne, hst, hAC' τ τ, if_pos rfl] at h1
    exact one_ne_zero h1
  · let ρ : 𝓞 E →+* Module.End (ResidueField X.O) (ResidueField X.O) :=
      (Algebra.lmul (ResidueField X.O) (ResidueField X.O)).toRingHom.comp χ
    obtain ⟨mσ, hm, hs⟩ := ((decomp_of_inv ρ (red io X) b Cr hAC' hCA').1 1)
    obtain ⟨σ, hσ⟩ : ∃ σ, mσ σ ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      simp [h] at hs
    refine ⟨σ, RingHom.ext fun a => ?_⟩
    have : χ a * mσ σ = red io X σ a * mσ σ := hm σ a
    exact (mul_right_cancel₀ hσ this).symm

end GlobalTheory.PrimePart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsAfterBaseChangeSpecTopOpenOfStableBasisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeds_after_baseChange_specTopOpen_of_stable_basis : ∀ {Rg : Type} [CommRing Rg] (B : Over (Sp Rg)) [GrpObj B] (M : LB B.left) (k : ℕ) {mB : ℕ} (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))), IsAbelianScheme B → M.IsLB → VeryAmpleAt B M k → IsBCBasis B M k bB → ∃ (x : Sp Rg ⟶ (topS Rg).left) (b' : Fin mB → LB.Sec (LPow B M (k : ℤ) (baseAt x))), IsIso x ∧ (∀ i, IsPullSec B M (k : ℤ) (homAt x ▷ B) (whiskerRight_snd (homAt x) B) (bB i) (b' i)) ∧ GlobalTheory.AmpleSpan.EmbedsBy (fst (baseAt x) B).left b' := by
  first | (exact @GlobalTheory.HomFixMat.EmbedsBC.embeds_bc) | (exact GlobalTheory.HomFixMat.EmbedsBC.embeds_bc) | (intros; apply GlobalTheory.HomFixMat.EmbedsBC.embeds_bc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfProportionalGermsSectionsEmbedProjectivelyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_proportional_germs_sectionsEmbedProjectively : ∀ {X Y Z : Scheme.{0}} (π : Y ⟶ Z) {N : LB Y} {κ : Type} (s : κ → LB.Sec N), GlobalTheory.AmpleSpan.EmbedsBy π s → ∀ (f₁ f₂ : X ⟶ Y), f₁ ≫ π = f₂ ≫ π → (∀ x : X, ∃ σ : κ → X.presheaf.stalk x, (∃ p, f₁ x ∈ N.U p ∧ ∃ u : (X.presheaf.stalk x)ˣ, ∀ l, gs f₁ x (N.U p) ((s l).f p) = u * σ l) ∧ (∃ p, f₂ x ∈ N.U p ∧ ∃ u : (X.presheaf.stalk x)ˣ, ∀ l, gs f₂ x (N.U p) ((s l).f p) = u * σ l)) → f₁ = f₂ := by
  first | (exact @GlobalTheory.HomFixGerm.eq_of_germs) | (exact GlobalTheory.HomFixGerm.eq_of_germs) | (intros; apply GlobalTheory.HomFixGerm.eq_of_germs  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOnDoubleCosetOfEqOnArchimedeanSlice
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.MirPatch

theorem eq_on_cell_of_eq_on_slice : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b W : GA E (m + 1) → ℂ) (V : Subgroup (GL (Fin (m + 1)) (Af E))) (q : GA E (m + 1)), q ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) → GeneralLinearGroup.map (pInf E) q = 1 → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ V, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ u ∈ V, ∀ g, W (g * finGL E (m + 1) u) = W g) → (∀ y : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) → W (q * infGL E (m + 1) y) = b (q * infGL E (m + 1) y)) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), p ∈ GlobalTheory.JSW.MirPatch.cell V q → W p = b p := by
  intro E _ _ _ m S b W V q hq hqi hb hW hbV hWV hsl p hp hpc
  obtain ⟨u, hu, k, hk, y, rfl⟩ := hpc
  have key : u * q * finGL E (m + 1) k * infGL E (m + 1) y = u * ((q * infGL E (m + 1) y) * finGL E (m + 1) k) := by
    rw [mul_assoc (q) (infGL E (m + 1) y), infGL_comm, ← mul_assoc, ← mul_assoc]

  have hy : ∀ j, (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j = if j = Fin.last m then 1 else 0 := by
    intro j
    have h1 := congrArg (pInf E) (hp.2 j)
    have hmap : GeneralLinearGroup.map (pInf E) (u * q * finGL E (m + 1) k * infGL E (m + 1) y)
        = GeneralLinearGroup.map (pInf E) u * y := by
      simp [map_mul, hqi]
    have h2 : (GeneralLinearGroup.map (pInf E) (u * q * finGL E (m + 1) k * infGL E (m + 1) y) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j
        = if j = Fin.last m then 1 else 0 := by
      rw [GeneralLinearGroup.map_apply] at *
      simpa [apply_ite (pInf E)] using h1
    rw [hmap] at h2
    rw [← h2]
    simp only [Units.val_mul, Matrix.mul_apply]
    rw [Finset.sum_eq_single (Fin.last m)]
    · have : (u : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) (Fin.last m) = 1 := hu.2 _
      simp [GeneralLinearGroup.map_apply, this]
    · intro l _ hl
      have hlt : l < Fin.last m := lt_of_le_of_ne (Fin.le_last l) hl
      have : (u : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l = 0 := hu.1 _ _ hlt
      simp [GeneralLinearGroup.map_apply, this]
    · simp
  have hslice : q * infGL E (m + 1) y ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) := by
    refine ⟨?_, ?_⟩
    · intro w hw
      rw [map_mul, hq.1 w hw, one_mul]
      exact map_cornerGL_of_zero _ _ (fun _ => map_zero (pLoc E w)) y
    · intro j
      refine ad_ext ?_ ?_
      · have := congrArg (fun g : GL (Fin (m + 1)) (Cinf E) => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j)
          (show GeneralLinearGroup.map (pInf E) (q * infGL E (m + 1) y) = y by simp [hqi])
        simp only [GeneralLinearGroup.map_apply] at this
        rw [this, hy j]; split_ifs <;> simp
      · have := congrArg (fun g : GL (Fin (m + 1)) (Af E) => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E)) (Fin.last m) j)
          (show GeneralLinearGroup.map (pFin E) (q * infGL E (m + 1) y) = GeneralLinearGroup.map (pFin E) q by simp)
        simp only [GeneralLinearGroup.map_apply] at this
        rw [this, hq.2 j]
  rw [key, hW u hu, hb u hu, hWV k hk, hbV k hk, hsl y hslice]

end GlobalTheory.JSW.MirPatch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfOrbit
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmoothCyclic

open GlobalTheory.LowTypeDetermined

theorem eq_zero_of_orbit : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau)
    (ℓ : M.H τ →ₗ[ℂ] ℂ), Sobolev₂ (lieAt V τ) (M.rep τ) ℓ → ∀ v ∈ M.sm τ, v ≠ 0 →
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ℓ (M.rep τ g v) = 0) → ∀ w ∈ M.sm τ, ℓ w = 0 := by
  intro D V S M τ ℓ hℓ v hv hv0 h0 w hw
  obtain ⟨_, -, hσ, hi, -⟩ := M.ds τ
  have hs : M.sm τ = smooth (gramAt D V τ) (M.rep τ) := Submodule.span_eq (smooth (gramAt D V τ) (M.rep τ))
  have hP := M.fr_unit τ
  have h := M.fr_gram τ
  refine eq_zero_of_translates hσ hi hP h hℓ (hs.le hv) hv0 (fun g hg => ?_) (hs.le hw)
  have e : M.rep τ ((M.fr τ)⁻¹ * g * M.fr τ) = M.σ τ g := congrArg (M.σ τ) (conj_conj hP g)
  rw [← e]
  exact h0 _ (conj_inv_mem hP h hg)

end GlobalTheory.SmoothCyclic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleEquivalenceSchemeOfStrictlyHenselianStalksStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleEquivalence_scheme_of_strictlyHenselian_stalks : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (Y X S : Scheme.{0}) (f : Y ⟶ X) (p : X ⟶ S) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f], (∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R (sch.map (pullback.map (f ≫ p) s p s f (𝟙 _) (𝟙 _) (by simp) (by simp))) F) → Eqv R (sch.map f) F := by
  first
  | exact @GlobalTheory.EtC.eqv_sch_of_stalks
  | exact GlobalTheory.EtC.eqv_sch_of_stalks
  | (intros; apply GlobalTheory.EtC.eqv_sch_of_stalks <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicUnitCarryingFormToNormMultiple
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem adelic_norm_move : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.C) (M : Type) [Field M] [NumberField M] (j : M →+* G.C) (σ : M →+* M), (∀ y : M, β * sh G (j y) = j (σ y) * β) → ∀ (a : M) (u : (AfP p ⊗[ℚ] M)ˣ), (u : AfP p ⊗[ℚ] M) * Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom u = 1 ⊗ₜ a → ∃ U : (AfP p ⊗[ℚ] G.C)ˣ, (U : AfP p ⊗[ℚ] G.C) * inC G (AfP p) β * (starT G.star (AfP p) U).unop = inC G (AfP p) (j a * β) ∧ ∀ y : G.C, (∀ m : M, y * j m = j m * y) → inC G (AfP p) y * U = U * inC G (AfP p) y := by
  intro p _ G β M _ _ j σ hβ a u hu
  let J : AfP p ⊗[ℚ] M →ₐ[ℚ] AfP p ⊗[ℚ] G.C := Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) j.toRatAlgHom
  have hJ : ∀ (r : AfP p) (m : M), J (r ⊗ₜ m) = r ⊗ₜ j m := fun r m => rfl
  have key : ∀ w : AfP p ⊗[ℚ] M, inC G (AfP p) β * (starT G.star (AfP p) (J w)).unop =
      J (Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom w) * inC G (AfP p) β := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      have e2 : J (Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom (r ⊗ₜ m)) = r ⊗ₜ j (σ m) := rfl
      rw [hJ, e2, starT_tmul]
      show ((1 : AfP p) ⊗ₜ β) * (r ⊗ₜ (G.star (j m)).unop) = (r ⊗ₜ j (σ m)) * ((1 : AfP p) ⊗ₜ β)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      congr 1
      exact hβ m
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), MulOpposite.unop_add, mul_add, hx, hy, map_add (f := _), add_mul]
  refine ⟨Units.map J.toMonoidHom u, ?_, ?_⟩
  · show J u * inC G (AfP p) β * (starT G.star (AfP p) (J u)).unop = _
    rw [mul_assoc, key, ← mul_assoc, ← map_mul, hu, hJ]
    show ((1 : AfP p) ⊗ₜ j a) * ((1 : AfP p) ⊗ₜ β) = (1 : AfP p) ⊗ₜ (j a * β)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  · intro y hy
    show inC G (AfP p) y * J u = J u * inC G (AfP p) y
    generalize (u : AfP p ⊗[ℚ] M) = w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [hJ]
      show ((1 : AfP p) ⊗ₜ y) * (r ⊗ₜ j m) = (r ⊗ₜ j m) * ((1 : AfP p) ⊗ₜ y)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, hy m]
    | add x z hx hz => rw [map_add (f := _), mul_add, add_mul, hx, hz]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApplyPvNeZero
section
open NumberField
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame)
open GlobalTheory.ThFr (IsSympl per_add)
open GlobalTheory.Dict (pv pv_smul span_range_pv)

namespace GlobalTheory.FrameEquiv

theorem dense_of_rat_of_span {V : Type} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V]
    [ContinuousSMul ℝ V] (S : Set V) (h0 : (0 : V) ∈ S) (ha : ∀ u ∈ S, ∀ v ∈ S, u + v ∈ S)
    (hq : ∀ q : ℚ, ∀ u ∈ S, (q : ℝ) • u ∈ S) (hS : Submodule.span ℝ S = ⊤) : Dense S := by
  let P : Submodule ℝ V :=
    { carrier := closure S
      zero_mem' := subset_closure h0
      add_mem' := fun {a b} h1 h2 => map_mem_closure₂ continuous_add h1 h2 ha
      smul_mem' := fun t a h1 => by
        have ht : t ∈ closure (Set.range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast t
        refine map_mem_closure₂ (f := fun (s : ℝ) (v : V) => s • v) continuous_smul ht h1 ?_
        rintro _ ⟨q, rfl⟩ u hu
        exact hq q u hu }
  have hP : Submodule.span ℝ S ≤ P := Submodule.span_le.2 subset_closure
  intro z
  exact hP (hS ▸ Submodule.mem_top)

theorem denseRange_pv {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {g : ℕ}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) : DenseRange (pv X idx x) := by
  have hq (q : ℚ) (v : Fin r → E) : pv X idx x ((q : E) • v) = (q : ℝ) • pv X idx x v := by
    rw [pv_smul]
    funext j
    simp
  refine dense_of_rat_of_span _ ⟨0, ?_⟩ ?_ ?_ (span_range_pv idx hs hx)
  · simpa using hq 0 0
  · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    refine ⟨u + v, ?_⟩
    rw [pv, pv, pv, per_add]
    rfl
  · rintro q _ ⟨u, rfl⟩
    exact ⟨_, hq q u⟩

theorem exists_apply_pv_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → ∀ x ∈ X.dom, ∀ θ : (Fin g → ℂ) → ℂ, Continuous θ → θ ≠ 0 → ∃ v : Fin r → E, θ (pv X idx x v) ≠ 0 := by
  intro E _ _ _ r X g bas idx hs x hx θ hθ h0
  by_contra h
  push Not at h
  exact h0 ((denseRange_pv idx hs hx).equalizer hθ continuous_const (funext h))

end GlobalTheory.FrameEquiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffPullbackBaseChangeStableSectionBasisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeff_pullback_baseChangeStableSectionBasis : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k : ℕ) (mA : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))), IsBCBasis A L k bA → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' : Over (Sp R)) (φA' : A'.left ⟶ A.left), IsPullback φA' A'.hom A.hom t → ∀ (ψA : A'.left ⟶ (topS Rg ⊗ A).left), ψA ≫ (snd (topS Rg) A).left = φA' → ∀ s : LB.Sec (powPull L (ψA ≫ (snd (topS Rg) A).left) (k : ℤ)), ∃ c : Fin mA → Γ(Sp R, ⊤), ∀ q : Fin 1 → L.ι, s.f q = ∑ i, (A'.hom.appLE ⊤ (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) q) (fun _ _ => trivial)).hom (c i) * (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) q) (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) q) (GlobalTheory.HomFixMat.wchart_comp_le L ψA (snd (topS Rg) A).left q)).hom ((bA i).f q) := by
  first | (exact @GlobalTheory.HomFixMat.exists_coeff_of_isBCBasis) | (exact GlobalTheory.HomFixMat.exists_coeff_of_isBCBasis) | (intros; apply GlobalTheory.HomFixMat.exists_coeff_of_isBCBasis  <;> assumption)
end

