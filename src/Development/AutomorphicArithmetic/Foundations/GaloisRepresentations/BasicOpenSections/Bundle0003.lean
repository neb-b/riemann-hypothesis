module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.Bundle0002
public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PCycAll
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)
open UpperTheory.Gal UpperTheory.Gal.Mod

private lemma natCast_eq_zero_of_pt {p : ℕ} {Y : Scheme.{0}} {Ω : Type} [Field Ω] (x : gp Ω ⟶ Y)
    (h : pt x ∉ Y.basicOpen (p : Γ(Y, ⊤))) : (p : Ω) = 0 := by
  by_contra hne
  apply h
  have hu : IsUnit ((ConcreteCategory.hom (Scheme.Hom.app x ⊤)) (p : Γ(Y, ⊤))) := by
    rw [map_natCast]
    have e : (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (p : Ω) = (p : Γ(gp Ω, ⊤)) := map_natCast _ p
    have hu0 := (IsUnit.mk0 _ hne).map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
    rw [e] at hu0
    exact hu0
  have hpre := Scheme.preimage_basicOpen x (p : Γ(Y, ⊤))
  rw [Scheme.basicOpen_of_isUnit _ hu] at hpre
  have hm : IsLocalRing.closedPoint Ω ∈ x ⁻¹ᵁ Y.basicOpen (p : Γ(Y, ⊤)) := by
    rw [hpre]
    trivial
  exact hm

private lemma sp_closedPoint {K L : Type} [Field K] [Field L] (a : K →+* L) :
    (sp a) (IsLocalRing.closedPoint L) = IsLocalRing.closedPoint K := by
  exact IsLocalRing.comap_closedPoint a

private lemma resPt_closedPoint (V : Type) [CommRing V] [IsLocalRing V] :
    (resPt V) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)) = IsLocalRing.closedPoint V := by
  exact IsLocalRing.comap_closedPoint (IsLocalRing.residue V)

private lemma exists_frob (p f : ℕ) (hp : p.Prime) (F : Type) [Field F] (h : (p : F) = 0) :
    ∃ φ : F →+* F, ∀ a, φ a = a ^ p ^ f := by
  haveI : CharP F p := (CharP.charP_iff_prime_eq_zero hp).2 h
  haveI : ExpChar F p := ExpChar.prime hp
  exact ⟨iterateFrobenius F p f, fun a => iterateFrobenius_def p f a⟩

theorem UpperTheory.Gal.Mod.cycAll :
    ResClosed → ValLift → CycRes → CycExt → CycAll := by
  intro hRC hVL hCR hCE p f n hp Y π T w hOne hPt hdense hbasic Ω _ _ x hgen
  obtain ⟨η, hη, hsp⟩ := hdense (pt x)
  obtain ⟨V, _, _, _, _, y, Ω', _, _, a, b, hpV, hsq⟩ := hVL p Y Ω x η hsp hη
  haveI := hRC V
  have hx0 : pt x ∉ Y.basicOpen (p : Γ(Y, ⊤)) := fun h => hgen.1 (hbasic _ h)
  have hptA : pt (sp a ≫ x) = pt x := by
    change x (sp a (IsLocalRing.closedPoint Ω')) = _
    rw [sp_closedPoint]
    rfl
  have hptB : pt (sp b ≫ resPt V ≫ y) = y (IsLocalRing.closedPoint V) := by
    change y (resPt V (sp b (IsLocalRing.closedPoint Ω'))) = _
    rw [sp_closedPoint, resPt_closedPoint]
  have hyx : y (IsLocalRing.closedPoint V) = pt x := by
    rw [← hptB, ← hsq, hptA]
  have hpΩ := natCast_eq_zero_of_pt x hx0
  have hpΩ' := natCast_eq_zero_of_pt (sp a ≫ x) (by rw [hptA]; exact hx0)
  have hpR := natCast_eq_zero_of_pt (resPt V ≫ y) (by
    change y (resPt V (IsLocalRing.closedPoint _)) ∉ _
    rw [resPt_closedPoint, hyx]
    exact hx0)
  obtain ⟨φ, hφ⟩ := exists_frob p f hp Ω hpΩ
  obtain ⟨φ', hφ'⟩ := exists_frob p f hp Ω' hpΩ'
  obtain ⟨ψ, hψ⟩ := exists_frob p f hp (IsLocalRing.ResidueField V) hpR
  refine ⟨φ, hφ, ?_⟩
  have hW : ∀ j, IsWt (T j).p (w j) := fun j => (hOne j).1
  have h1 := hCR p (p ^ f) n Y π T w hOne hPt V hpV y (by rw [hyx]; exact hgen) ψ hψ
  have h2 := (hCE p (p ^ f) n Y T w hW _ Ω' b ψ φ'
    (RingHom.ext fun z => by simp [hψ, hφ', map_pow]) (resPt V ≫ y)).mp h1
  rw [← hsq] at h2
  exact (hCE p (p ^ f) n Y T w hW Ω Ω' a φ φ'
    (RingHom.ext fun z => by simp [hφ, hφ', map_pow]) x).mpr h2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PResClosed
section
open Polynomial

namespace UpperTheory.Gal.Mod

theorem resClosed : ResClosed := by
  intro V _ _ _ _
  refine IsAlgClosed.of_exists_root _ ?_
  intro P hmon hirr
  have hl : P ∈ Polynomial.lifts (IsLocalRing.residue V) := by
    rw [Polynomial.mem_lifts]
    exact Polynomial.map_surjective _ IsLocalRing.residue_surjective P
  obtain ⟨Q, hQ, hdeg, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hmon
  have hpos : 0 < P.degree := Polynomial.degree_pos_of_irreducible hirr
  have hdeg' : (Q.map (algebraMap V (FractionRing V))).degree ≠ 0 := by
    rw [hQm.degree_map, hdeg]
    exact hpos.ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (Q.map (algebraMap V (FractionRing V))) hdeg'
  have hint : IsIntegral V x := ⟨Q, hQm, by
    rw [Polynomial.IsRoot.def, Polynomial.eval_map] at hx
    exact hx⟩
  obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (K := FractionRing V)).1 hint
  have hy : Q.eval y = 0 := by
    apply IsFractionRing.injective V (FractionRing V)
    rw [map_zero, ← hx.eq_zero, Polynomial.eval_map, Polynomial.eval₂_hom]
  refine ⟨IsLocalRing.residue V y, ?_⟩
  rw [← hQ, Polynomial.eval_map, Polynomial.eval₂_hom, hy, map_zero]

end UpperTheory.Gal.Mod
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PValLiftB
section
open CategoryTheory Limits AlgebraicGeometry
open UpperTheory.Gal.TranscendenceTraces (gp pt)
open UpperTheory.Gal.crystallineComparison (resPt)
open UpperTheory.Gal UpperTheory.Gal.Mod

private theorem exists_common_algClosed_embedding {k A B : Type} [Field k] [Field A] [Field B] [Algebra k A]
    [Algebra k B] :
    ∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (f : A →+* C) (g : B →+* C),
      f.comp (algebraMap k A) = g.comp (algebraMap k B) := by
  haveI : Nontrivial (TensorProduct k A B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left k A B
      (algebraMap k B).injective
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (TensorProduct k A B)
  letI := Ideal.Quotient.field M
  let q : TensorProduct k A B →+* TensorProduct k A B ⧸ M := Ideal.Quotient.mk M
  let iA : A →ₐ[k] TensorProduct k A B := Algebra.TensorProduct.includeLeft
  let iB : B →ₐ[k] TensorProduct k A B := Algebra.TensorProduct.includeRight
  refine ⟨AlgebraicClosure (TensorProduct k A B ⧸ M), inferInstance, inferInstance,
    (algebraMap _ _).comp (q.comp iA.toRingHom), (algebraMap _ _).comp (q.comp iB.toRingHom), ?_⟩
  ext c
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    AlgHom.commutes, iA, iB]

theorem UpperTheory.Gal.Mod.valLiftB :
    ValLift := by
  intro p Y Ω _ x η hsp hp
  let O := Y.presheaf.stalk (pt x)
  let sx : O ⟶ CommRingCat.of Ω := Scheme.stalkClosedPointTo x
  haveI : IsLocalHom sx.hom := Scheme.isLocalHom_stalkClosedPointTo' x
  have hx : Spec.map sx ≫ Y.fromSpecStalk (pt x) = x :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk x
  let K := AlgebraicClosure (Y.residueField η)
  let f : O →+* K := (algebraMap (Y.residueField η) K).comp
    ((Y.residue η).hom.comp (Y.presheaf.stalkSpecializes hsp).hom)
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  let g : O →+* A := f.codRestrict A.toSubring hA
  haveI : IsLocalHom g := hloc
  haveI : IsAlgClosed (FractionRing A) :=
    IsAlgClosed.of_ringEquiv K _ (FractionRing.algEquiv A K).symm.toRingEquiv
  let φ : IsLocalRing.ResidueField O →+* Ω := IsLocalRing.ResidueField.lift sx.hom
  let ψ : IsLocalRing.ResidueField O →+* IsLocalRing.ResidueField A :=
    IsLocalRing.ResidueField.map g
  letI : Algebra (IsLocalRing.ResidueField O) Ω := φ.toAlgebra
  letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField A) := ψ.toAlgebra
  obtain ⟨C, _, _, fa, fb, hab⟩ := exists_common_algClosed_embedding (k := IsLocalRing.ResidueField O) (A := Ω)
    (B := IsLocalRing.ResidueField A)
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom g) ≫ Y.fromSpecStalk (pt x), C, inferInstance, inferInstance,
    fa, fb, ?_, ?_⟩
  · intro h0
    have hu := ((Y.mem_basicOpen (p : Γ(Y, ⊤)) η trivial).mp hp).map (Y.residue η).hom
    simp only [map_natCast] at hu
    have h1 := congrArg A.subtype h0
    simp only [map_natCast, map_zero] at h1
    have h2 : (p : Y.residueField η) = 0 :=
      (algebraMap (Y.residueField η) K).injective (by rw [map_natCast, map_zero]; exact h1)
    exact hu.ne_zero h2
  · conv_lhs => rw [← hx]
    simp only [sp, resPt, ← Spec.map_comp_assoc]
    congr 2
    ext z
    have hz := congrArg (fun h => h (IsLocalRing.residue O z)) hab
    simpa [φ, ψ, RingHom.algebraMap_toAlgebra, IsLocalRing.ResidueField.map_residue] using hz
end

