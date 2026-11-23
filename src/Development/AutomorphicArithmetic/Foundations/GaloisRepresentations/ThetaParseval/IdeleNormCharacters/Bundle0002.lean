module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.AbsFactsAlt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ReadLoc
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Neutral.B1 ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr

open scoped TensorProduct

namespace UpperTheory.Gal.TP.Chr

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem fst_extZero (y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) :
    (GlobalTheory.UnitaryHeckeBaseChange.toAdele F E (extZero F E y)).1 = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have h : extZero F E (a ⊗ₜ[F] x) =
        (((0, a) : HeckeCharacterZeroLocus.ThmBIn.AF F) ⊗ₜ[F] x : HeckeCharacterZeroLocus.ThmBIn.AF F ⊗[F] E) :=
      GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul _ _ _ _
    rw [h]
    erw [GlobalTheory.UnitaryHeckeBaseChange.toAdele_tmul]
    show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E 0 * _ = 0
    rw [map_zero, zero_mul]
  | add y z hy hz =>
    simp only [map_add (f := _)]
    erw [Prod.fst_add, hy, hz]
    simp

private theorem snd_extZero (y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) :
    (GlobalTheory.UnitaryHeckeBaseChange.toAdele F E (extZero F E y)).2 = finAdEquiv F E y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have h : extZero F E (a ⊗ₜ[F] x) =
        (((0, a) : HeckeCharacterZeroLocus.ThmBIn.AF F) ⊗ₜ[F] x : HeckeCharacterZeroLocus.ThmBIn.AF F ⊗[F] E) :=
      GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul _ _ _ _
    rw [h]
    refine (congrArg (fun z : AdeleRing (𝓞 E) E => z.2)
      (GlobalTheory.UnitaryHeckeBaseChange.toAdele_tmul (F := F) (E := E) ((0, a) : HeckeCharacterZeroLocus.ThmBIn.AF F) x)).trans ?_
    show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap F E a * algebraMap E (FiniteAdeleRing (𝓞 E) E) x = _
    apply RestrictedProduct.ext
    intro w
    refine Eq.trans ?_ (finAdEquiv_tmul a x w).symm
    simp only [complMap_rfl, GlobalTheory.CharTransport.locMap_eq]
    rfl
  | add y z hy hz =>
    simp only [map_add (f := _)]
    erw [Prod.snd_add, hy, hz]

private theorem toAdele_locIdele (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) :
    GlobalTheory.UnitaryHeckeBaseChange.toAdele F E (locIdele F w x : AF F ⊗[F] E) =
      (GlobalTheory.Mem.Chr.localIdele E w x : AdeleRing (𝓞 E) E) := by
  rw [coe_locIdele]
  simp only [map_add (f := _), map_sub, map_one]
  refine Prod.ext ?_ ?_
  · erw [Prod.fst_add, Prod.fst_sub, fst_extZero, fst_extZero]
    simp
    rfl
  · erw [Prod.snd_add, Prod.snd_sub, snd_extZero, snd_extZero]
    simp
    rfl

end

end UpperTheory.Gal.TP.Chr

theorem UpperTheory.Gal.TP.Chr.readLoc :
    UpperTheory.Gal.TP.Chr.ReadLoc := by
  intro E _ _ _ μ χ hR w
  ext y
  simp only [locChar, Formalism.L2.Host.HChar.loc, MonoidHom.comp_apply]
  show ((χ ((locIdele (↥(maximalRealSubfield E)) w) y) : Circle) : ℂ) = _
  rw [hR]
  congr 2
  exact Units.ext (toAdele_locIdele w y)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ReadRes
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Neutral.B1 ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr
open scoped TensorProduct

theorem UpperTheory.Gal.TP.Chr.readRes :
    UpperTheory.Gal.TP.Chr.ReadRes := by
  intro E _ _ _ μ χ hR hμ a
  rw [hR]
  have h3 : ∀ {σ : E →ₐ[↥(maximalRealSubfield E)] E} (h : HeckeCharacterZeroLocus.ThmBIn.IsCMExt (↥(maximalRealSubfield E)) E σ),
      Units.map ((GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv h).toRingHom
        : AE (↥(maximalRealSubfield E)) E →* AdeleRing (𝓞 E) E)
      (Units.map (algebraMap (AF ↥(maximalRealSubfield E)) (AE (↥(maximalRealSubfield E)) E)
        : AF ↥(maximalRealSubfield E) →* AE (↥(maximalRealSubfield E)) E) a)
      = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap _ E a := fun _ =>
    Units.ext (GlobalTheory.UnitaryHeckeBaseChange.toAdele_algebraMap (a : AF ↥(maximalRealSubfield E)))
  erw [h3 (GlobalTheory.GalOfCusp.isCMExt_real E), hμ a]
  simp only [GlobalTheory.GalOfCusp.quadChar, MonoidHom.comp_apply]
  split_ifs with hm
  · obtain ⟨y, ⟨t, rfl⟩, z, hz, hyz⟩ := Subgroup.mem_sup.1 hm
    have hn : GlobalTheory.IdeleNormChar.normSign E a = 1 := by
      refine (GlobalTheory.IdeleNormChar.normSign_eq_one_iff E a).2 ⟨t, ?_⟩
      rw [← hyz]
      simpa [GlobalTheory.QuadSymbol.toUnits, GlobalTheory.QuadSymbol.normGroup] using hz
    simp [hn]
  · rcases Int.units_eq_one_or (GlobalTheory.IdeleNormChar.normSign E a) with hn | hn
    · exfalso
      obtain ⟨t, ht⟩ := (GlobalTheory.IdeleNormChar.normSign_eq_one_iff E a).1 hn
      exact hm (Subgroup.mem_sup.2 ⟨_, ⟨t, rfl⟩, _, ht, mul_div_cancel _ _⟩)
    · simp [hn]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.TypProd
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Neutral.B1 ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr

private theorem pl_emb {E : Type} [Field E] [NumberField E] [IsCMField E]
    {w : InfinitePlace (maximalRealSubfield E)} (τ : EmbOver E w) : pl τ.1 = w := by
  unfold pl
  rw [InfinitePlace.comap_mk, τ.2, InfinitePlace.mk_embedding]

private theorem pl_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (φ : E →+* ℂ) :
    pl (ComplexEmbedding.conjugate φ) = pl φ := by
  unfold pl
  rw [InfinitePlace.mk_conjugate_eq]

private theorem eq_or_conj_of_pl_eq {E : Type} [Field E] [NumberField E] [IsCMField E]
    {φ ψ : E →+* ℂ} (h : pl φ = pl ψ) : φ = ψ ∨ φ = ComplexEmbedding.conjugate ψ := by
  have hmk : InfinitePlace.mk φ = InfinitePlace.mk ψ :=
    (IsCMField.equivInfinitePlace E).injective (by
      simpa only [IsCMField.equivInfinitePlace_apply, pl] using h)
  rcases InfinitePlace.mk_eq_iff.1 hmk with h' | h'
  · exact Or.inl h'
  · right
    rw [← h']
    exact (star_star φ).symm

theorem UpperTheory.Gal.TP.Chr.typProd :
    UpperTheory.Gal.TP.Chr.TypVal → UpperTheory.Gal.TP.Chr.TypProd := by
  intro hv E _ _ _ emb a b x
  classical
  rw [← Finset.prod_fiberwise Finset.univ (pl (E := E))]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hne : (emb w).1 ≠ ComplexEmbedding.conjugate (emb w).1 := fun h =>
    IsTotallyComplex.complexEmbedding_not_isReal _ (ComplexEmbedding.isReal_iff.2 h.symm)
  have hfib : Finset.univ.filter (fun φ : E →+* ℂ => pl φ = w) =
      {(emb w).1, ComplexEmbedding.conjugate (emb w).1} := by
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      exact eq_or_conj_of_pl_eq (h.trans (pl_emb (emb w)).symm)
    · rintro (rfl | rfl)
      · exact pl_emb _
      · rw [pl_conj, pl_emb]
  rw [hfib, Finset.prod_pair hne, (hv E emb a b w).1, (hv E emb a b w).2,
    ComplexEmbedding.conjugate_coe_eq]
end

