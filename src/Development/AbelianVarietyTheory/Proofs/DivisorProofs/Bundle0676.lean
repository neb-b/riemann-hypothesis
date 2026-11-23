module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0501
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0530
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0642
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0660
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPureBCId
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PureLift

def IsPure {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (W : A ⟶ A) [IsMonHom W] (r s : R) : Prop :=
  (∀ x ∈ Fil A, push (dp0 R) (𝟙 _) W x = r • x) ∧ ∀ y : HdR A, push (dp0 R) (𝟙 _) W y - s • y ∈ Fil A

def IsPureBC {S : Type} [CommRing S] (G : Over (Sp S)) [GrpObj G] (W : G ⟶ G) (r s : S) : Prop :=
  ∀ (R : Type) [CommRing R] (f : S →+* R) (A : Over (Sp R)) [GrpObj A] (φ : A.left ⟶ G.left),
    IsGrpPullback A G (spMap f) φ → ∀ (W' : A ⟶ A) [IsMonHom W'], W'.left ≫ φ = φ ≫ W.left → IsPure A W' (f r) (f s)

theorem IsPure.mem_Fil {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {W : A ⟶ A} [IsMonHom W] {r r' s : R}
    (h : IsPure A W r' s) (hu : IsUnit (r - s)) {y : HdR A} (hy : push (dp0 R) (𝟙 _) W y = r • y) : y ∈ Fil A := by
  have hm := h.2 y
  rw [hy, ← sub_smul] at hm
  obtain ⟨u, hu'⟩ := hu
  have hv := (Fil A).smul_mem (↑u⁻¹ : R) hm
  rwa [smul_smul, ← hu', Units.inv_mul, one_smul] at hv

end GlobalTheory.PureLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRatInPadicIntegersOfTwistedDifference
section
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

namespace GlobalTheory

theorem inZl_of_twisted_difference {G : Type} [CommGroup G] [Finite G] (l : ℕ) [Fact l.Prime]
    (g : G) (q : ℕ) (hq : l ∣ q) (x : G → ℚ)
    (hx : ∀ C, InZl l (x C - (q : ℚ) * x (C * g))) : ∀ C, InZl l (x C) := by
  by_contra h
  push_neg at h
  obtain ⟨C0, hC0⟩ := h
  obtain ⟨C, hC⟩ := Finite.exists_max (fun C => ‖((x C : ℚ) : ℚ_[l])‖)
  have h0 : 1 < ‖((x C0 : ℚ) : ℚ_[l])‖ := by
    unfold InZl at hC0; push_neg at hC0; exact hC0
  have h1 : 1 < ‖((x C : ℚ) : ℚ_[l])‖ := lt_of_lt_of_le h0 (hC C0)
  have hqn : ‖((q : ℚ) : ℚ_[l])‖ < 1 := by
    rw [Rat.cast_natCast]
    exact Padic.norm_natCast_lt_one_iff.2 hq
  have hy : ‖(((x C - (q : ℚ) * x (C * g) : ℚ)) : ℚ_[l])‖ ≤ 1 := hx C
  have hsplit : ((x C : ℚ) : ℚ_[l]) =
      (((x C - (q : ℚ) * x (C * g) : ℚ)) : ℚ_[l]) + ((q : ℚ) : ℚ_[l]) * ((x (C * g) : ℚ) : ℚ_[l]) := by
    push_cast; ring
  have hprod : ‖((q : ℚ) : ℚ_[l]) * ((x (C * g) : ℚ) : ℚ_[l])‖ < ‖((x C : ℚ) : ℚ_[l])‖ := by
    rw [norm_mul]
    have hle : ‖((x (C * g) : ℚ) : ℚ_[l])‖ ≤ ‖((x C : ℚ) : ℚ_[l])‖ := hC (C * g)
    calc ‖((q : ℚ) : ℚ_[l])‖ * ‖((x (C * g) : ℚ) : ℚ_[l])‖
        ≤ ‖((q : ℚ) : ℚ_[l])‖ * ‖((x C : ℚ) : ℚ_[l])‖ :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ < 1 * ‖((x C : ℚ) : ℚ_[l])‖ :=
          mul_lt_mul_of_pos_right hqn (by linarith)
      _ = ‖((x C : ℚ) : ℚ_[l])‖ := one_mul _
  have hna := Padic.nonarchimedean (p := l)
    (((x C - (q : ℚ) * x (C * g) : ℚ)) : ℚ_[l]) (((q : ℚ) : ℚ_[l]) * ((x (C * g) : ℚ) : ℚ_[l]))
  rw [← hsplit] at hna
  rcases le_max_iff.1 hna with h2 | h2
  · linarith
  · linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyGenericOfKeyClosedPts
section
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.LocAcyc

private theorem spread_torsor : ∀ (T O : Type) [CommRing T] [CommRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale φ →
    ∀ (q : ℕ), 0 < q → ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib T O) D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib T O] D)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T O) D q act →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (ψ : E →ₐ[Polynomial T] O) (DE : Type) (_ : CommRing DE)
      (_ : Algebra (GlobalTheory.LocAcyc.GenFib T E) DE)
      (actE : Multiplicative (ZMod q) →* (DE ≃ₐ[GlobalTheory.LocAcyc.GenFib T E] DE)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T E) DE q actE ∧
      ∀ s : DE →+* GlobalTheory.LocAcyc.GenFib T O,
        (∀ e : E, s (algebraMap (GlobalTheory.LocAcyc.GenFib T E) DE (algebraMap E _ e)) =
          algebraMap O (GlobalTheory.LocAcyc.GenFib T O) (ψ e)) →
        Nonempty (D →ₐ[GlobalTheory.LocAcyc.GenFib T O] GlobalTheory.LocAcyc.GenFib T O) := GlobalTheory.T.spread_torsor_to_etale_algebra
private theorem exists_maximal_over_closedPt : ∀ (T E : Type) [CommRing T] [IsLocalRing T] [CommRing E] [Algebra (Polynomial T) E]
    [Algebra.FiniteType (Polynomial T) E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial T) E) =
      (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∃ y : Ideal E, y.IsMaximal ∧ Q ≤ y ∧
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) ∧
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T := GlobalTheory.T.exists_maximal_over_closedPoint_closedFibre
private theorem section_at_closedPt : GlobalTheory.LocAcyc.KeyClosedPts →
    ∀ (T E : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing E]
      [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
      [Algebra.Etale (Polynomial T) E], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (y : Ideal E) [y.IsPrime],
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T →
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (DE : Type) [CommRing DE] [Algebra (GlobalTheory.LocAcyc.GenFib T E) DE]
      (actE : Multiplicative (ZMod q) →* (DE ≃ₐ[GlobalTheory.LocAcyc.GenFib T E] DE)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T E) DE q actE →
    ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra E S) (_ : Algebra T S)
      (_ : IsScalarTower T E S),
      (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y ∧ Module.Flat E S ∧
      GlobalTheory.LocAcyc.LocPiecesEtale E S ∧
      ∃ s : DE →+* GlobalTheory.LocAcyc.GenFib T S,
        ∀ e : E, s (algebraMap (GlobalTheory.LocAcyc.GenFib T E) DE (algebraMap E _ e)) =
          algebraMap S (GlobalTheory.LocAcyc.GenFib T S) (algebraMap E S e) := _root_.GlobalTheory.LocAcyc.exists_section_strictHenselisation_at_closed
private theorem specialisation_map : ∀ (R S O : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing O]
    [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)] [Algebra R S] [Algebra R O]
    (Q y : Ideal R) [Q.IsPrime] [y.IsPrime], Q ≤ y →
    (IsLocalRing.maximalIdeal S).comap (algebraMap R S) = y →
    (IsLocalRing.maximalIdeal O).comap (algebraMap R O) = Q →
    Module.Flat R S → GlobalTheory.LocAcyc.LocPiecesEtale R S → Nonempty (S →ₐ[R] O) := _root_.GlobalTheory.Specialise.specialisation_exists

theorem keyGeneric_of_keyClosedPts : KeyClosedPts → KeyGeneric := by
  intro hC T O _ _ _ _ _ _ _ _ hAIC P _ φ hφ hSH hP hPeq q hq hqu
  rw [torsorsTrivial_iff]
  intro D _ _ act hD
  obtain ⟨E, _, _, _, _, _, ψ, DE, _, _, actE, hDE, hred⟩ := spread_torsor T O P φ hφ hSH.2.2.2 q hq D act hD

  set Q : Ideal E := (maximalIdeal O).comap ψ.toRingHom with hQdef
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  have hloc : (maximalIdeal O).comap φ = maximalIdeal (Localization.AtPrime P) := by
    haveI := hSH.2.2.1
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top inferInstance))
    · intro x hx
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (IsLocalRing.mem_maximalIdeal _).1 hx (isUnit_of_map_unit φ x hu)
  have hQP : Q.comap (algebraMap (Polynomial T) E) = P := by
    rw [hQdef, Ideal.comap_comap]
    have h1 : ψ.toRingHom.comp (algebraMap (Polynomial T) E) = φ.comp (algebraMap (Polynomial T) _) := by
      rw [hφ]; exact ψ.comp_algebraMap
    rw [h1, ← Ideal.comap_comap, hloc]
    exact Localization.AtPrime.under_maximalIdeal (R := Polynomial T) (I := P)
  obtain ⟨y, hymax, hQy, hyne, hyT⟩ := exists_maximal_over_closedPt T E Q (hQP.trans hPeq)
  haveI : y.IsPrime := hymax.isPrime
  obtain ⟨S, _, _, _, _, _, hSy, hSflat, hSpieces, s, hs⟩ :=
    section_at_closedPt hC T E hAIC y hyT hyne q hq hqu DE actE hDE
  letI : Algebra E O := ψ.toRingHom.toAlgebra
  haveI : HenselianLocalRing O := hSH.1
  haveI : IsSepClosed (ResidueField O) := hSH.2.1
  obtain ⟨σ⟩ := specialisation_map E S O Q y hQy hSy rfl hSflat hSpieces
  have hσT : ∀ t : T, σ (algebraMap T S t) = algebraMap T O t := by
    intro t
    rw [IsScalarTower.algebraMap_apply T E S, σ.commutes, IsScalarTower.algebraMap_apply T (Polynomial T) E]
    change ψ (algebraMap (Polynomial T) E _) = _
    rw [ψ.commutes, ← IsScalarTower.algebraMap_apply]
  have hM : Algebra.algebraMapSubmonoid S (nonZeroDivisors T) ≤
      (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)).comap σ.toRingHom := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, ht, (hσT t).symm⟩
  let m : GenFib T S →+* GenFib T O := IsLocalization.map (GenFib T O) σ.toRingHom hM
  refine hred (m.comp s) fun e => ?_
  rw [RingHom.comp_apply, hs e]
  simp only [m, IsLocalization.map_eq]
  change algebraMap O (GenFib T O) (σ (algebraMap E S e)) = _
  rw [σ.commutes]
  rfl

end GlobalTheory.LocAcyc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsCharOne
section
noncomputable section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters

namespace GlobalTheory.ParamLabel

variable {p : ℕ} [Fact p.Prime]

def LabelsChar (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (θ : Tor p d →* ℂˣ) (x : Fbar p) : Prop :=
  x ^ (p ^ d - 1) = 1 ∧ ∀ u : Tor p d, ((θ u : ℂˣ) : ℂ) = GlobalTheory.GLq.thetaOf L d x ((u : (Fbar p)ˣ) : Fbar p)

def LabelsTame (L : GlobalTheory.GLq.LabelDatum p) (χ : (ZMod p)ˣ →* ℂˣ) (a : (ZMod p)ˣ) : Prop :=
  ∀ u : (ZMod p)ˣ, GlobalTheory.GLq.thetaOf L 1 (algebraMap (ZMod p) (Fbar p) (a : ZMod p))
    (algebraMap (ZMod p) (Fbar p) (u : ZMod p)) = ((χ u : ℂˣ) : ℂ)

def rootElt {r : ℕ} {b : Fin r → Fin r} (x : Cyc b → Fbar p) (y : Σ c : Cyc b, Fin (cycLen b c)) : Fbar p :=
  x y.1 ^ p ^ (y.2 : ℕ)

def IsRootPoly {r : ℕ} {b : Fin r → Fin r} (x : Cyc b → Fbar p) (f : (ZMod p)[X]) : Prop :=
  (∀ c, x c ^ (p ^ cycLen b c - 1) = 1) ∧ f.Monic ∧ Formalism.CyclotomicNorms.rootsBar f = Finset.univ.val.map (rootElt x)

def Labels (L : GlobalTheory.GLq.LabelDatum p) {r : ℕ} (s : SSParam p ℂ r) (x : Cyc s.1 → Fbar p) (f : (ZMod p)[X]) : Prop :=
  (∀ c, LabelsChar L (s.2 c) (x c)) ∧ IsRootPoly x f

def cuspOn {ι : Type} [Fintype ι] [DecidableEq ι] (θ : Tor p (Fintype.card ι) →* ℂˣ) :
    GlobalTheory.GLq.Gn p (Fintype.card ι) → ℂ := fun y =>
  cuspChar θ ((y : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) (ZMod p)).submatrix
    (Fintype.equivFin ι) (Fintype.equivFin ι))

end GlobalTheory.ParamLabel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentClassVanishesFinitelyGeneratedSubalgebra
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.GmStep

noncomputable section
namespace GlobalTheory.EtC.GmStep.KillColim

theorem laurentMap_coeff_apply {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (p : LaurentPolynomial A) (m : ℤ) : (laurentMap f p).coeff m = f (p.coeff m) := by
  rw [laurentMap_coeff, Finsupp.mapRange_apply]

theorem laurentMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (laurentMap g).comp (laurentMap f) = laurentMap (g.comp f) := by
  refine RingHom.ext fun p => ?_
  · apply AddMonoidAlgebra.coeff_injective
    ext m
    simp [laurentMap_coeff_apply]

theorem laurentMap_id (A : Type) [CommRing A] : laurentMap (RingHom.id A) = RingHom.id _ := by
  refine RingHom.ext fun p => ?_
  · apply AddMonoidAlgebra.coeff_injective
    ext m
    simp [laurentMap_coeff_apply]

theorem laurentMap_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) : Function.Injective (laurentMap f) := by
  intro p r h
  apply AddMonoidAlgebra.coeff_injective
  ext m
  apply hf
  rw [← laurentMap_coeff_apply, ← laurentMap_coeff_apply, h]

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Functor.map_comp, ← Spec.map_comp]; rfl

variable (A S : Type) [CommRing A] [CommRing S] [Algebra A S]

def diag : Finset S ⥤ CommRingCat.{0} where
  obj t := CommRingCat.of (LaurentPolynomial (Algebra.adjoin A (t : Set S)))
  map {t u} h := CommRingCat.ofHom
    (laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.2 h.le))).toRingHom)
  map_id t := by
    ext1
    refine (Eq.trans ?_ (laurentMap_id _)).trans rfl
    congr 1
  map_comp f g := by
    ext1
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    rw [laurentMap_comp]
    rfl

def cocone : Cocone (diag A S) where
  pt := CommRingCat.of (LaurentPolynomial S)
  ι := { app := fun t => CommRingCat.ofHom (laurentMap (Algebra.adjoin A (t : Set S)).val.toRingHom)
         naturality := fun t u h => by
           ext1
           simp only [diag, Functor.const_obj_map, Category.comp_id, CommRingCat.hom_comp,
             CommRingCat.hom_ofHom]
           rw [laurentMap_comp]
           rfl }

theorem val_CT (t : Finset S) (a : Algebra.adjoin A (t : Set S)) (n : ℤ) :
    laurentMap (Algebra.adjoin A (t : Set S)).val.toRingHom (LaurentPolynomial.C a * LaurentPolynomial.T n) =
      LaurentPolynomial.C (a : S) * LaurentPolynomial.T n := by
  rw [map_mul, laurentMap_C, laurentMap_T]
  rfl

theorem lm_val_incl {t u : Finset S} (h : (t : Set S) ⊆ u) (p : LaurentPolynomial (Algebra.adjoin A (t : Set S))) :
    laurentMap (Algebra.adjoin A (u : Set S)).val.toRingHom
        (laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono h)).toRingHom p) =
      laurentMap (Algebra.adjoin A (t : Set S)).val.toRingHom p := by
  apply AddMonoidAlgebra.coeff_injective
  ext m
  simp only [laurentMap_coeff_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Subalgebra.coe_val,
    Subalgebra.coe_inclusion]

theorem exists_finset_adjoin_laurent_preimage (x : LaurentPolynomial S) : ∃ (t : Finset S) (y : LaurentPolynomial (Algebra.adjoin A (t : Set S))),
    x = laurentMap (Algebra.adjoin A (t : Set S)).val.toRingHom y := by
  classical
  induction x using LaurentPolynomial.induction_on' with
  | add p r hp hr =>
    obtain ⟨t, y, rfl⟩ := hp
    obtain ⟨t', y', rfl⟩ := hr
    have h1 : (t : Set S) ⊆ ((t ⊔ t' : Finset S) : Set S) := Finset.coe_subset.2 le_sup_left
    have h2 : (t' : Set S) ⊆ ((t ⊔ t' : Finset S) : Set S) := Finset.coe_subset.2 le_sup_right
    refine ⟨t ⊔ t', laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono h1)).toRingHom y +
      laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono h2)).toRingHom y', ?_⟩
    rw [map_add (f := _), lm_val_incl A S h1, lm_val_incl A S h2]
  | C_mul_T n a =>
    have hmem : a ∈ Algebra.adjoin A (({a} : Finset S) : Set S) :=
      Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_singleton_self a))
    refine ⟨{a}, LaurentPolynomial.C (⟨a, hmem⟩ : Algebra.adjoin A (({a} : Finset S) : Set S)) *
      LaurentPolynomial.T n, ?_⟩
    rw [val_CT]

theorem laurent_adjoin_eq_of_image_eq [DecidableEq S] {i j : Finset S} (xi : LaurentPolynomial (Algebra.adjoin A (i : Set S)))
    (xj : LaurentPolynomial (Algebra.adjoin A (j : Set S)))
    (h : laurentMap (Algebra.adjoin A (i : Set S)).val.toRingHom xi =
      laurentMap (Algebra.adjoin A (j : Set S)).val.toRingHom xj) :
    laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono
        (Finset.coe_subset.2 (le_sup_left : i ≤ i ⊔ j)))).toRingHom xi =
      laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono
        (Finset.coe_subset.2 (le_sup_right : j ≤ i ⊔ j)))).toRingHom xj := by
  refine laurentMap_injective (Algebra.adjoin A ((i ⊔ j : Finset S) : Set S)).val.toRingHom
    Subtype.val_injective ?_
  exact (lm_val_incl A S (Finset.coe_subset.2 (le_sup_left : i ≤ i ⊔ j)) xi).trans
    (h.trans (lm_val_incl A S (Finset.coe_subset.2 (le_sup_right : j ≤ i ⊔ j)) xj).symm)

def coconeIsColimit : IsColimit (cocone A S) := by
  classical
  haveI : ReflectsColimitsOfShape (Finset S) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget CommRingCat.{0})
    (Types.FilteredColimit.isColimitOf _ ((forget CommRingCat.{0}).mapCocone (cocone A S)) ?_ ?_)
  · intro x
    exact exists_finset_adjoin_laurent_preimage A S x
  · intro i j xi xj h
    exact ⟨i ⊔ j, homOfLE le_sup_left, homOfLE le_sup_right, laurent_adjoin_eq_of_image_eq A S xi xj h⟩

end GlobalTheory.EtC.GmStep.KillColim
end

namespace GlobalTheory.EtC.GmStep.KillColim

theorem val_laurent (A S : Type) [CommRing A] [CommRing S] [Algebra A S] (t : Finset S) :
    (laurentMap (Algebra.adjoin A (t : Set S)).val.toRingHom).comp
        (laurentMap (algebraMap A (Algebra.adjoin A (t : Set S)))) = laurentMap (algebraMap A S) := by
  rw [laurentMap_comp]
  congr 1

theorem incl_laurent (A S : Type) [CommRing A] [CommRing S] [Algebra A S] {t u : Finset S}
    (h : (t : Set S) ⊆ u) :
    (laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono (R := A) h)).toRingHom).comp
        (laurentMap (algebraMap A (Algebra.adjoin A (t : Set S)))) =
      laurentMap (algebraMap A (Algebra.adjoin A (u : Set S))) := by
  rw [laurentMap_comp]
  congr 1

theorem kill_colim : ∀ (q : ℕ) (A S : Type) [CommRing A] [CommRing S] [Algebra A S], IsUnit (q : A) →
    ∀ (n i : ℤ) (x : Ht q (sp (LaurentPolynomial A)) n i),
    pull _ (spMap (laurentMap (algebraMap A S))) _ _ x = 0 →
    ∃ t : Finset S, pull _ (spMap (laurentMap (algebraMap A (Algebra.adjoin A (t : Set S))))) _ _ x = 0 := by
  intro q A S _ _ _ hq n i x hx
  classical
  have hu : IsUnit (q : (diag A S).obj ∅) := by
    have := hq.map ((LaurentPolynomial.C : Algebra.adjoin A ((∅ : Finset S) : Set S) →+* _).comp
      (algebraMap A _))
    rw [map_natCast] at this
    exact this
  have e1 : spMap ((cocone A S).ι.app ∅).hom ≫
      spMap (laurentMap (algebraMap A (Algebra.adjoin A ((∅ : Finset S) : Set S)))) =
      spMap (laurentMap (algebraMap A S)) :=
    (spMap_comp' _ (laurentMap (Algebra.adjoin A ((∅ : Finset S) : Set S)).val.toRingHom)).trans
      (congrArg spMap (val_laurent A S ∅))
  have hy0 : pull _ (spMap ((cocone A S).ι.app ∅).hom) _ _
      (pull _ (spMap (laurentMap (algebraMap A (Algebra.adjoin A ((∅ : Finset S) : Set S))))) _ _ x) = 0 :=
    (pull_comp _ _ _ _ _ x).symm.trans ((congrArg (fun g => pull _ g (tw q i) n x) e1).trans hx)
  obtain ⟨k, f, hk⟩ := (GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q (diag A S) (cocone A S) (coconeIsColimit A S) n i).2 ∅ _ hu hy0
  have e2 : spMap ((diag A S).map f).hom ≫
      spMap (laurentMap (algebraMap A (Algebra.adjoin A ((∅ : Finset S) : Set S)))) =
      spMap (laurentMap (algebraMap A (Algebra.adjoin A (k : Set S)))) :=
    (spMap_comp' _ (laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono (R := A)
      (Finset.coe_subset.2 f.le))).toRingHom)).trans
      (congrArg spMap (incl_laurent A S (Finset.coe_subset.2 f.le)))
  exact ⟨k, (congrArg (fun g => pull _ g (tw q i) n x) e2).symm.trans ((pull_comp _ _ _ _ _ x).trans hk)⟩

end GlobalTheory.EtC.GmStep.KillColim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeISupOfUniformisationParametersCover
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem le_iSup_of_pre_cover : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens) (K : Type) (W : K → A.left.Opens), (∀ z ∈ pre u.ex U, ∃ i, z ∈ pre u.ex (W i)) → U ≤ ⨆ i, W i := by
  intro A _ g L u hA U K W h x hx
  obtain ⟨-, -, -, -, hinf, hmono, hsup, -, -, -, hbasic, -⟩ := _root_.GlobalTheory.CechPer.pre_val_rules A g L u
  obtain ⟨V, hV, hxV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp A.left.isBasis_affineOpens hx
  have hV' : IsAffineOpen V := hV
  let p : Ideal Γ(A.left, V) :=
    (IsLocalRing.maximalIdeal (A.left.presheaf.stalk x)).comap (A.left.presheaf.germ V x hxV).hom
  have hp : p ≠ ⊤ := Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hp
  obtain ⟨z, hzV, hz⟩ := _root_.GlobalTheory.MaxPoints.main A g L u hA V hV' m hm
  obtain ⟨i, hi⟩ := h z (hmono U V hVU hzV)
  have hzi : z ∈ pre u.ex (W i ⊓ V) := by rw [hinf]; exact ⟨hi, hzV⟩
  have hle : W i ⊓ V ≤ ⨆ b : {b : Γ(A.left, V) // A.left.basicOpen b ≤ W i}, A.left.basicOpen b.1 := by
    intro y hy
    obtain ⟨f, hf, hyf⟩ := hV'.exists_basicOpen_le (V := W i) ⟨y, hy.1⟩ hy.2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, hf⟩, hyf⟩
  obtain ⟨⟨b, hb⟩, hzb⟩ := (hsup _ _ z).mp (hmono _ _ hle hzi)
  have hbm : b ∉ m := fun hh ↦ (hbasic V b z).mp hzb ((hz b).mp hh)
  have hxb : x ∈ A.left.basicOpen b := by
    rw [Scheme.mem_basicOpen _ b x hxV]
    by_contra hn
    exact hbm (hpm (Ideal.mem_comap.mpr ((IsLocalRing.mem_maximalIdeal _).mpr hn)))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hb hxb⟩

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiNormIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnifTorsK

def PsiNormAt (p : ℕ) [Fact p.Prime] {V : Type} [CommRing V] [IsDomain V] [Algebra (FractionRing V) (PadicAlgCl p)]
    (D : DegPre V) (χ : D.X) (r : ℝ) : Prop :=
  ∀ j : PUnit → D.P.L.ι, ⊤ ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit) →
    ‖algebraMap (FractionRing V) (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing V))) _ ((D.psi χ).s j).val)‖ = r

theorem psiNorm_iff {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ}
    [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (χ : u.D.toPre.X) (r : ℝ) :
    u.PsiNorm χ r ↔ PsiNormAt p u.D.toPre χ r := Iff.rfl

end GlobalTheory.UnifTorsK
end

