module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0013
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0008
public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.LocalComparison.Bundle0001
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.TiedAInvOfTheta
public import GroundTheory.PAdicHodge.ACrisPhi

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.BcSplits
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV UpperTheory.Gal.G3

private theorem bcSplits : BcSplits :=
  pBcSplits (pSplitsBasic (pSplitsPts pIsoPts) pPtsOfSplits)

theorem UpperTheory.Gal.crystallineComparison.Br.trBc :
    UpperTheory.Gal.crystallineComparison.Br.TrBc := by
  intro B B' R _ T g Z Y p q s _ _ hs tr htr W r c hc J _ σ hσ hsp x
  exact htr _ (pullback.snd r g) (UpperTheory.Gal.G3.bcMap g c hc) (bcMap_snd g c hc) J
    (fun j ↦ UpperTheory.Gal.G3.bcMap g (σ j) ((hσ j).trans rfl)) (fun j ↦ bcMap_snd g (σ j) _)
    ((bcSplits g p q r s hs c hc J σ hσ).2.2 hsp) x
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.GenFEt
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt gen)

namespace UpperTheory.Gal.crystallineComparison.Br

private theorem range_subset_basicOpen (l : ℕ) {k : Type} [Field k] (hl : (l : k) ≠ 0) {Y P : Scheme.{0}} (a : P ⟶ Y)
    (c : P ⟶ sp k) : Set.range a ⊆ (Y.basicOpen (l : Γ(Y, ⊤)) : Set Y) := by
  rintro _ ⟨x, rfl⟩
  have h1 : IsUnit ((l : Γ(sp k, ⊤))) := by
    have := (IsUnit.mk0 _ hl).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    simpa using this
  have h2 : IsUnit ((l : Γ(P, ⊤))) := by
    have := h1.map (c.app ⊤).hom
    rwa [map_natCast] at this
  have hu : IsUnit (a.app ⊤ (l : Γ(Y, ⊤))) := by
    rw [map_natCast]
    exact h2
  have hx : x ∈ a ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤)) := by
    rw [Scheme.preimage_basicOpen, Scheme.basicOpen_of_isUnit _ hu]
    trivial
  exact hx

theorem genFEt : GenFEt := by
  intro l O k _ _ _ hl Y p T
  have sY := (IsPullback.of_hasPullback p (gen O k)).flip
  have sZ := (IsPullback.of_hasPullback (T.p ≫ p) (gen O k)).flip
  have hsq : IsPullback (pullback.fst (T.p ≫ p) (gen O k)) (bcMap (gen O k) (p := p) T.p rfl)
      T.p (pullback.fst p (gen O k)) := by
    have h := IsPullback.of_right (h₁₁ := bcMap (gen O k) (p := p) T.p rfl)
      (h₁₂ := pullback.snd p (gen O k)) (v₁₁ := pullback.fst (T.p ≫ p) (gen O k))
      (v₁₂ := pullback.fst p (gen O k)) (h₂₁ := T.p) (h₂₂ := p)
      (by rw [bcMap_snd]; exact sZ) (bcMap_fst _ _ _) sY
    exact h.flip
  show FEt (bcMap (gen O k) (p := p) T.p rfl) T.d
  refine ⟨?_, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @IsFinite) hsq T.fin
  · have hr : Set.range (pullback.fst p (gen O k)) ⊆ Set.range (Y.basicOpen (l : Γ(Y, ⊤))).ι := by
      rw [Scheme.Opens.range_ι]
      exact range_subset_basicOpen l hl _ (pullback.snd p (gen O k))
    let φ := IsOpenImmersion.lift (Y.basicOpen (l : Γ(Y, ⊤))).ι (pullback.fst p (gen O k)) hr
    have hφ : φ ≫ (Y.basicOpen (l : Γ(Y, ⊤))).ι = pullback.fst p (gen O k) :=
      IsOpenImmersion.lift_fac _ _ _
    have t := (isPullback_morphismRestrict T.p (Y.basicOpen (l : Γ(Y, ⊤)))).flip
    have w : pullback.fst (T.p ≫ p) (gen O k) ≫ T.p =
        (bcMap (gen O k) (p := p) T.p rfl ≫ φ) ≫ (Y.basicOpen (l : Γ(Y, ⊤))).ι := by
      rw [Category.assoc, hφ]
      exact hsq.w
    have sq2 : IsPullback (t.lift _ _ w) (bcMap (gen O k) (p := p) T.p rfl)
        (T.p ∣_ Y.basicOpen (l : Γ(Y, ⊤))) φ := by
      refine IsPullback.of_right (h₁₂ := (T.p ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤))).ι)
        (h₂₂ := (Y.basicOpen (l : Γ(Y, ⊤))).ι) (v₁₃ := T.p) ?_ (t.lift_snd _ _ w) t
      rw [t.lift_fst, hφ]
      exact hsq
    exact MorphismProperty.of_isPullback (P := @Etale) sq2 T.et
  · intro K _ _ x
    have hlK : (l : K) ≠ 0 := by
      intro h
      apply hl
      apply (Spec.preimage (x ≫ pullback.snd p (gen O k))).hom.injective
      rw [map_natCast, map_zero]
      exact h
    rw [← T.deg K hlK (x ≫ pullback.fst p (gen O k))]
    exact Nat.card_congr
      { toFun := fun y => ⟨y.1 ≫ pullback.fst (T.p ≫ p) (gen O k), by
          rw [Category.assoc, hsq.w, ← Category.assoc, y.2]⟩
        invFun := fun z => ⟨hsq.lift z.1 x z.2, hsq.lift_snd _ _ _⟩
        left_inv := fun y => Subtype.ext (hsq.hom_ext (hsq.lift_fst _ _ _)
          (by rw [hsq.lift_snd]; exact y.2.symm))
        right_inv := fun z => Subtype.ext (hsq.lift_fst _ _ _) }

end UpperTheory.Gal.crystallineComparison.Br
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.PBTied
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison GroundTheory.PAdicHodge

namespace UpperTheory.Gal.crystallineComparison.Br

variable {l : ℕ} [Fact l.Prime]

private theorem l_dvd : ∃ r : ℕ, (l : Acris l) ∣ tA l ^ r := by
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1
    (ACris.periodT_pow_mem' (K := ℂ_[l]) (p := l) (untilt_epsilon (p := l)))
  exact ⟨l - 1, u, by rw [tA, ← hu, mul_comm]⟩

private def cT {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) : Acris l →+* P.R.B :=
  T.eB.symm.toRingHom.comp (Formalism.Per6.cB l)

private theorem eB_cT {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (a : Acris l) :
    T.eB (cT T a) = Formalism.Per6.cB l a :=
  T.eB.apply_symm_apply _

private theorem cT_unit {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) : IsUnit (cT T (tA l)) :=
  (Formalism.Per6.Loc2.isUnit_right (l : Acris l) (tA l)).map T.eB.symm

private theorem cT_loc {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (x : P.R.B) :
    ∃ (r : ℕ) (a : Acris l), cT T (tA l) ^ r * x = cT T a := by
  obtain ⟨r, y, h⟩ := (locFacts (Acris l) (l : Acris l) (tA l) l_dvd).1 (T.eB x)
  refine ⟨r, y, T.eB.injective ?_⟩
  rw [map_mul, map_pow, eB_cT, eB_cT]
  exact h

private theorem cT_ker {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (a : Acris l)
    (h : cT T a = 0) : ∃ r : ℕ, tA l ^ r * a = 0 := by
  refine (locFacts (Acris l) (l : Acris l) (tA l) l_dvd).2 a ?_
  have h1 := eB_cT T a
  rw [h, map_zero] at h1
  exact h1.symm

private theorem cT_φ {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (a : Acris l) :
    P.φB (cT T a) = cT T (phiA l a) := by
  refine T.eB.injective ?_
  rw [T.frob, eB_cT, eB_cT]
  exact PositivityTheory.LocInh.φB_cB a

private theorem cT_σ {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI)
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (g : K.fixingSubgroup) (a : Acris l) :
    P.actQ g.1 (cT T a) = cT T (galA g a) := by
  refine T.eB.injective ?_
  rw [T.actB, eB_cT, eB_cT, ((actEq l).1 K g a)]
  exact PositivityTheory.LocInh.σB_cB _ a

private theorem algebraMap_padic_int_eq_period {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (x : ℤ_[l]) :
    algebraMap ℚ_[l] P.R.B (x : ℚ_[l]) = cT T (zA l x) := by
  refine T.eB.injective ?_
  rw [T.zB, eB_cT]
  exact (actEq l).2 x

private def pullbackToFiniteExtension {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (K : FinExt l) : PB l K.1 where
  C := P.R.B
  c := cT T
  φ := P.φB
  σ g := (P.actQ g.1).toAlgHom
  t_unit := cT_unit T
  loc := cT_loc T
  ker := cT_ker T
  φ_c := cT_φ T
  σ_c := cT_σ T K.1
  z_c := algebraMap_padic_int_eq_period T

theorem pBTied : PBTied := by
  intro l _ P AI hT K
  obtain ⟨T⟩ := UpperTheory.Lit.Cmp.locTied6 l P AI hT
  exact ⟨pullbackToFiniteExtension T K, AlgEquiv.refl, fun _ _ => rfl, fun _ => rfl, PositivityTheory.LocInh.tiedA_φ_injective P⟩

end UpperTheory.Gal.crystallineComparison.Br
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.TrPush
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison UpperTheory.Gal.G3

namespace UpperTheory.Gal.crystallineComparison.Br

theorem trPush : TrPush := by
  intro l _ B Z Y p q s hs n tr htr W x m σ hσ hiso z
  exact htr W (x ≫ p) x rfl (Fin m) σ (fun j => by rw [← hs, ← Category.assoc, hσ j]) ⟨hσ, hiso⟩ z

end UpperTheory.Gal.crystallineComparison.Br
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.TrTot
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison UpperTheory.Gal.G3

namespace UpperTheory.Gal.crystallineComparison.Br

theorem trTot : TrTot := by
  intro l _ B Z Y p q s tr htr W r c hc J _ σ hσ hsp x
  change Htot l (sch.obj Y) at x
  change pullTot l (sch.map c) (DirectSum.lmap tr x) = ∑ j, pullTot l (sch.map (σ j)) x
  ext n
  rw [DirectSum.sum_apply]
  simp only [pullTot, DirectSum.lmap_apply]
  exact htr n W r c hc J σ hσ hsp (x n)

end UpperTheory.Gal.crystallineComparison.Br
end
end

