module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0695
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2604
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2224
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2226
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2608
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearOpenEmbeddingCompOfSumMapComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2374
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExtensionSecPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2443
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2599
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoproductThickeningQuotientFreeThickening
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.CopEx

theorem exists_cop : ∀ (D : Data) (Λ : Lift D) (n : ℕ) (U : AffOp D.X) (T : Thick D.κ D.t), IsLev T.δ (n + 1) →
    ⊤ ≤ (T.x ≫ D.i) ⁻¹ᵁ U.unop.1 → ∃ (F G : Thick D.κ D.t) (u : T ⟶ F) (q : F ⟶ G) (r : Λ.L.obj U ⟶ G),
      (KK D.κ D.t).QAt u ∧ IsLev F.δ (n + 1) ∧ Function.Surjective q.φ ∧ (∀ b, q.φ b ∈ G.J → b ∈ F.J) ∧
        IsCop (n + 1) (u ≫ q) r := by
  intro D Λ n U T hT hU
  obtain ⟨h1, h2, h3, -⟩ := _root_.GlobalTheory.PDForm.Lift.hom_spec D Λ
  haveI : Algebra.Smooth D.R (Sec D.s U.unop.1) := (_root_.GlobalTheory.SmoothLift.Data.smooth_mono_inf D).1 U.unop
  obtain ⟨m, pres, hpres⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    (inferInstance : Algebra.FiniteType D.R (Sec D.s U.unop.1))
  obtain ⟨g, hgx, hgR⟩ := h2 U T hU
  choose bl hbl using fun i : Fin m ↦ T.surj (g (pres (MvPolynomial.X i)))
  obtain ⟨F, u, τ, hfree, hQ⟩ := _root_.GlobalTheory.PDForm.FreeFin.exists_free D.R D.I D.κ D.X₀ D.t n m T hT
  let ψ : MvPolynomial (Fin m) D.R →ₐ[D.R] F.B := MvPolynomial.aeval fun i ↦ u.φ (bl i) + τ i
  have hψX : ∀ i, ψ (MvPolynomial.X i) = u.φ (bl i) + τ i := fun i ↦ MvPolynomial.aeval_X _ _

  have hψπ : ∀ p, F.π (ψ p) = u.φ₀ (g (pres p)) := by
    have e : F.π.comp (ψ : MvPolynomial (Fin m) D.R →+* F.B) =
        u.φ₀.comp (g.comp (pres : MvPolynomial (Fin m) D.R →+* Sec D.s U.unop.1)) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        show F.π (ψ (MvPolynomial.C r)) = u.φ₀ (g (pres (MvPolynomial.C r)))
        have hC : MvPolynomial.C r = algebraMap D.R (MvPolynomial (Fin m) D.R) r := rfl
        rw [hC, AlgHom.commutes, AlgHom.commutes, hgR, u.comm, u.φ.commutes]
      · intro i
        simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, hψX, map_add (f := _)]
        rw [(F.ker _).2 (hfree.2.1 i), add_zero, ← hbl i, u.comm]
    exact fun p ↦ RingHom.congr_fun e p
  have hker : ∀ k ∈ RingHom.ker pres, ψ k ∈ F.J := fun k hk ↦
    (F.ker _).1 (by rw [hψπ, (RingHom.mem_ker).1 hk, map_zero, map_zero])
  set 𝔟 : Ideal F.B := Ideal.span {y | ∃ j : ℕ, j ≠ 0 ∧ ∃ x ∈ ψ '' (RingHom.ker pres : Set _), y = F.δ.dpow j x}
    with h𝔟def
  have h𝔟 : F.δ.IsSubDPIdeal 𝔟 := (GlobalTheory.DPQuot.quotient_subDPIdeal F.B F.J F.δ).2 _ (by
    rintro _ ⟨k, hk, rfl⟩; exact hker k hk)
  obtain ⟨G, q, hqs, hq0, hGJ, hGlev, hquniv⟩ := _root_.GlobalTheory.ThickQuot.exists_quotient D.R D.I D.κ D.X₀ D.t F 𝔟 h𝔟
  have hψ𝔟 : ∀ k ∈ RingHom.ker pres, (q.φ.comp ψ) k = 0 := fun k hk ↦ (hq0 _).2
    (Ideal.subset_span ⟨1, one_ne_zero, ψ k, ⟨k, hk, rfl⟩, (F.δ.dpow_one (hker k hk)).symm⟩)

  let y : Sec D.s U.unop.1 →ₐ[D.R] G.B :=
    (Ideal.Quotient.liftₐ (RingHom.ker pres) (q.φ.comp ψ) hψ𝔟).comp
      (Ideal.quotientKerAlgEquivOfSurjective hpres).symm.toAlgHom
  have hy : ∀ p, y (pres p) = q.φ (ψ p) := by
    intro p
    have : (Ideal.quotientKerAlgEquivOfSurjective hpres).symm (pres p) = Ideal.Quotient.mk _ p :=
      (AlgEquiv.symm_apply_eq _).2 rfl
    change Ideal.Quotient.liftₐ (RingHom.ker pres) (q.φ.comp ψ) hψ𝔟
      ((Ideal.quotientKerAlgEquivOfSurjective hpres).symm (pres p)) = _
    rw [this]
    rfl
  have hyπ : G.π.comp (y : Sec D.s U.unop.1 →+* G.B) = (u ≫ q).φ₀.comp g := by
    ext a
    obtain ⟨p, rfl⟩ := hpres a
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, hy]
    rw [← q.comm, hψπ]
    rfl
  obtain ⟨r, hr⟩ := (h1 U G y).1 (by
    rw [hyπ, Cris.spMap_comp, Category.assoc, hgx, ← Category.assoc, (u ≫ q).pt])
  refine ⟨F, G, u, q, r, hQ, hfree.1, hqs, ?_, hGlev _ hfree.1, ?_⟩
  · intro b hb
    rw [hGJ] at hb
    obtain ⟨j, hj, hjb⟩ := (Ideal.mem_map_iff_of_surjective _ hqs).1 hb
    have : b - j ∈ 𝔟 := (hq0 _).1 (by rw [map_sub]; change q.φ b - q.φ j = 0; rw [← hjb]; exact sub_self _)
    have := F.J.add_mem hj (h𝔟.isSubideal this)
    rwa [add_sub_cancel] at this
  intro S hS a b

  have hsame : ∀ x, S.π (b.φ (Λ.e U x)) = a.φ₀ (g x) := by
    have e := h3 U S.B₀ (b.φ₀.comp ((Λ.L.obj U).π.comp (Λ.e U : Sec D.s U.unop.1 →+* (Λ.L.obj U).B)))
      (a.φ₀.comp g) (by
        rw [Cris.spMap_comp, Category.assoc, Λ.pt U, ← Category.assoc, b.pt, Cris.spMap_comp, Category.assoc, hgx, ← Category.assoc, a.pt])
    intro x
    rw [← b.comm]
    exact RingHom.congr_fun e x
  let c : Fin m → S.B := fun i ↦ b.φ (Λ.e U (pres (MvPolynomial.X i))) - a.φ (bl i)
  have hc : ∀ i, c i ∈ S.J := by
    intro i
    refine (S.ker _).1 ?_
    simp only [c, map_sub, hsame, ← a.comm, hbl i, sub_self]
  obtain ⟨g', ⟨hg'u, hg'τ⟩, hg'uniq⟩ := hfree.2.2 S hS a c hc
  have hg'ψ : ∀ p, g'.φ (ψ p) = b.φ (Λ.e U (pres p)) := by
    have e : g'.φ.comp ψ = b.φ.comp ((Λ.e U).toAlgHom.comp pres) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, hψX, map_add (f := _), AlgEquiv.coe_toAlgHom, AlgHom.coe_coe]
      rw [hg'τ i, ← Thick.comp_φ, hg'u]
      simp only [c]
      abel
    exact fun p ↦ AlgHom.congr_fun e p
  have hkill : ∀ z ∈ 𝔟, g'.φ z = 0 := by
    intro z hz
    refine (Ideal.span_le (I := RingHom.ker (g'.φ : F.B →+* S.B))).2 ?_ hz
    rintro _ ⟨j, hj, _, ⟨k, hk, rfl⟩, rfl⟩
    change g'.φ (F.δ.dpow j (ψ k)) = 0
    have hdp := g'.dp.dpow_comp (n := j) _ (hker k hk)
    change S.δ.dpow j (g'.φ (ψ k)) = g'.φ (F.δ.dpow j (ψ k)) at hdp
    rw [← hdp, hg'ψ, (RingHom.mem_ker).1 hk, map_zero, map_zero, dpow_eval_zero _ hj]
  obtain ⟨c0, hc0, hc0u⟩ := hquniv S g' hkill
  refine ⟨c0, ⟨by rw [Category.assoc, hc0, hg'u], ?_⟩, ?_⟩
  · apply Thick.Hom.ext'
    apply AlgHom.ext
    intro z
    obtain ⟨x, rfl⟩ := (Λ.e U).surjective z
    obtain ⟨p, rfl⟩ := hpres x
    rw [Thick.comp_φ, hr, hy, ← Thick.comp_φ, hc0, hg'ψ]
  · rintro c1 ⟨hc1a, hc1b⟩
    refine hc0u c1 (hg'uniq (q ≫ c1) ⟨by rw [← Category.assoc, hc1a], fun i ↦ ?_⟩)
    have hτ : τ i = ψ (MvPolynomial.X i) - u.φ (bl i) := by rw [hψX]; abel
    rw [hτ, map_sub, Thick.comp_φ, Thick.comp_φ, ← hy, ← hr, ← Thick.comp_φ, hc1b, ← Thick.comp_φ q c1,
      ← Thick.comp_φ u, ← Category.assoc, hc1a]

end GlobalTheory.CopEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCpEvenOn
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.PrimCube

open GlobalTheory.PrimNorm GlobalTheory.MulPull

theorem evenOn_of_prim : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (P : GlobalTheory.UU.CP G) (a : G ⟶ G), IsMonHom a → LBIso P.L.L (cubeLB G ![𝟙 G, a] P.L.L) → EvenOn P := by
  intro R _ _ _ hR D A G _ _ hS U P a ha hw
  have hp : IsProper (pullback.snd G.hom (jK R)) := by
    have := A.isAb.proper
    have e : pullback.snd G.hom (jK R) = U.gen.hom.left ≫ A.A.hom := (Over.w U.gen.hom).symm
    have : IsIso U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.hom))
    exact e ▸ MorphismProperty.comp_mem @IsProper U.gen.hom.left A.A.hom inferInstance A.isAb.proper
  have hB : IsAbelianScheme (thickObj R (maximalIdeal R) 0 D.toPre.P.A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ _ D.toPre.P.isAb
  let Q₀ := GlobalTheory.Mum.tqOfGtCoord (U.gt 0) hB
  obtain ⟨P₀, v, hv⟩ := GlobalTheory.UU.exists_isLevelCP (maximalIdeal R) 0 P
  have hm : (maximalIdeal R ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  letI : Field (R ⧸ maximalIdeal R ^ (0 + 1)) := Ideal.Quotient.field _
  have hS0 := IsSemiAbelian.pullback (thick R (maximalIdeal R) 0) G hS
  have := hS0.smooth
  have := hS0.geomConnected
  have := Q₀.i_hom
  letI := D.toPre.addX
  haveI := D.toPre.freeX
  haveI := D.toPre.finX
  obtain ⟨s⟩ := GlobalTheory.BiextTriv.main (R ⧸ maximalIdeal R ^ (0 + 1)) D.toPre.X (thickObj R (maximalIdeal R) 0 G) P₀.L P₀.c Q₀.i
    Q₀.i_hom
  obtain ⟨σ, hσ⟩ := GlobalTheory.EvenTriv.exists_even_of_surjective (GlobalTheory.EvenTriv.surjective_cube_of_generic G hS hp) P a hw P₀
    (IsPullback.of_hasPullback G.hom (thick R (maximalIdeal R) 0)) hv Q₀.i s
  exact ⟨D.toPre.X, D.toPre.addX, D.toPre.freeX, D.toPre.finX, Q₀, P₀, ⟨v, hv⟩, σ, hσ⟩

theorem exists_cp_evenOn : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, w + star w = 1 → TraceFormTwistIso D.toPre o w → ∃ P : GlobalTheory.UU.CP G, LBIso P.L.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) ∧ EvenOn P := by
  intro R _ _ _ hR D A G _ _ hS U O _ _ _ o oA oG hlin w hw _
  obtain ⟨hno, -, hic, -⟩ := hR.1
  have ha := oG.hom w
  have hb := oG.hom (star w)
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hgh := U.gen_hom
  have hp : IsProper (pullback.snd G.hom (jK R)) := by
    have := A.isAb.proper
    have e : pullback.snd G.hom (jK R) = U.gen.hom.left ≫ A.A.hom := (Over.w U.gen.hom).symm
    have : IsIso U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.hom))
    exact e ▸ MorphismProperty.comp_mem @IsProper U.gen.hom.left A.A.hom inferInstance A.isAb.proper
  have hM := U.LG.isLB
  have hT : ∃ t : LB.Gen (Theta G U.LG.L), t.IsGen := ⟨U.cubG.t, U.cubG.isGen⟩
  have hadd : oG.act w * oG.act (star w) = 𝟙 G := by
    have e := oG.map_add w (star w)
    rw [hw, oG.map_one] at e
    exact (e.trans rfl).symm
  have hadj := _root_.GlobalTheory.Mum.UnifAdjoint.lbIso_cubeLB_star R hR.1 D A G hS U O o oA oG hlin w
  have hc := fun T : Over (Sp R) => diff₃_ptCls (T := T) hM hT
  have hq : ∀ T : Over (Sp R), (fun x : T ⟶ G => normCls U.LG.L (oG.act w) x.left) =
      fun x => diff₂ (ptCls U.LG.L T) x (postHom (oG.act w) T x) := fun T => funext fun x => normCls_left _ x
  have hs : ∀ (T : Over (Sp R)) (y : T ⟶ G), postHom (oG.act w) T y * postHom (oG.act (star w)) T y = y :=
    fun T y => (MonObj.comp_mul y _ _).symm.trans (by rw [hadd, Category.comp_id])
  have hadj' : ∀ (T : Over (Sp R)) (x y : T ⟶ G), diff₂ (ptCls U.LG.L T) (postHom (oG.act w) T x) y =
      diff₂ (ptCls U.LG.L T) x (postHom (oG.act (star w)) T y) := fun T x y => diff₂_ptCls_adj hM hadj x y
  have iso : ∀ (T : Over (Sp R)) (x y : T ⟶ G),
      LBIso (cubeLB G ![x, y] (cubeLB G ![𝟙 G, oG.act w] U.LG.L)) (cubeLB G ![x, y] U.LG.L) := fun T x y => by
    refine lbIso_nested hM _ _ _ _ _ _ ((prod_square_id x y (normCls U.LG.L (oG.act w))).trans
      (Eq.trans ?_ (prod_square_id x y (cls U.LG.L)).symm))
    rw [hq]
    exact diff₂_quadratic (hc T) _ _ (hs _) (hadj' _) x y
  have symN : HasGen (cubeLB G ![𝟙 G, oG.act w] U.LG.L) (K := Fin 2) ![(GrpObj.inv (X := G)).left, 𝟙 _] ![1, -1] := by
    refine hasGen_nested hM _ _ _ _ ?_
    rw [Fin.prod_univ_two]
    show normCls U.LG.L (oG.act w) (GrpObj.inv (X := G)).left ^ (1 : ℤ) *
      normCls U.LG.L (oG.act w) (𝟙 G : G ⟶ G).left ^ (-1 : ℤ) = 1
    have e : GrpObj.inv (X := G) = (𝟙 G)⁻¹ := by simp [Hom.inv_def]
    have e' : (𝟙 G)⁻¹ ≫ oG.act w = (𝟙 G ≫ oG.act w)⁻¹ := map_inv (postHom (oG.act w) G) _
    rw [normCls_left, normCls_left, e, e', diff₂_inv_inv (hc G), zpow_neg, mul_inv_cancel]
  have hN := GlobalTheory.LamCalc.cubeLB_isLB hM ![𝟙 G, oG.act w]
  obtain ⟨L', c', hL'⟩ := GlobalTheory.RigCube.exists_rigLB_cubicalStr R G hS hp _ hN
  have hsym : L'.IsSymmetric := isSymmetric_of_hasGen L' (hL' ▸ symN)
  obtain ⟨P, hP, -⟩ := GlobalTheory.UU.exists_cp_of_isSymmetric hL R A G hS U.gen hgh L' c' hsym
  have hPN : P.L.L = cubeLB G ![𝟙 G, oG.act w] U.LG.L := by rw [hP, hL']
  refine ⟨P, hPN ▸ GlobalTheory.PolBaseChange.lbIso_refl P.L.isLB, evenOn_of_prim R hR D A G hS U P (oG.act w) ha ?_⟩
  rw [hPN]
  exact (iso G (𝟙 G) (oG.act w)).symm

end GlobalTheory.Mum.PrimCube
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumOfDescendedMultiplication
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Desc

theorem pt_of_fix {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G' : Over S}
    (N : Near π G') (φl : pullback G'.hom (pullback.fst π π) ⟶ pullback G'.hom (pullback.snd π π))
    (hfix : Desc.embL N _ (rfl : pullback.fst π π ≫ π = _) ≫ φl = Desc.embL N _ pullback.condition.symm)
    (T' : Scheme.{0}) (a : T' ⟶ N.U.left) (x : T' ⟶ pullback G'.hom (pullback.fst π π))
    (h : N.Pt (x ≫ pullback.snd G'.hom (pullback.fst π π) ≫ pullback.fst π π) a (x ≫ pullback.fst G'.hom (pullback.fst π π))) :
    N.Pt (x ≫ pullback.snd G'.hom (pullback.fst π π) ≫ pullback.snd π π) a (x ≫ φl ≫ pullback.fst G'.hom (pullback.snd π π)) := by
  obtain ⟨x₀, h1, h2, h3⟩ := h
  have hw : a ≫ N.U.hom = (x ≫ pullback.snd G'.hom (pullback.fst π π)) ≫ pullback.fst π π ≫ π := by
    calc a ≫ N.U.hom = x₀ ≫ pullback.snd N.U.hom π ≫ π := by
          rw [← h1, Category.assoc, pullback.condition]
      _ = (x ≫ pullback.snd G'.hom (pullback.fst π π)) ≫ pullback.fst π π ≫ π := by
          rw [reassoc_of% h2, Category.assoc]
  have hx₀ : pullback.lift a (x ≫ pullback.snd G'.hom (pullback.fst π π)) hw ≫
      Desc.toS N (pullback.fst π π) rfl = x₀ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Desc.toS, pullback.lift_fst, pullback.lift_fst, h1]
    · rw [Category.assoc, Desc.toS, pullback.lift_snd, pullback.lift_snd_assoc, h2, Category.assoc]
  have hx : pullback.lift a (x ≫ pullback.snd G'.hom (pullback.fst π π)) hw ≫
      Desc.embL N (pullback.fst π π) rfl = x := by
    apply pullback.hom_ext
    · rw [Category.assoc, Desc.embL, pullback.lift_fst, reassoc_of% hx₀, h3]
    · rw [Category.assoc, Desc.embL, pullback.lift_snd, pullback.lift_snd]
  have hφ : x ≫ φl = pullback.lift a (x ≫ pullback.snd G'.hom (pullback.fst π π)) hw ≫
      Desc.embL N (pullback.snd π π) pullback.condition.symm := by
    rw [← hfix, ← Category.assoc, hx]
  refine ⟨pullback.lift a (x ≫ pullback.snd G'.hom (pullback.fst π π)) hw ≫
      Desc.toS N (pullback.snd π π) pullback.condition.symm, ?_, ?_, ?_⟩
  · rw [Category.assoc, Desc.toS, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, Desc.toS, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc]
  · rw [reassoc_of% hφ, Desc.embL, pullback.lift_fst, Category.assoc]

theorem exists_datum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∃ φ, N.Datum φ := by
  intro R _ _ _ hA S π hP hS hI G' _ _ hG N hL
  have h1 : pullback.fst π π ≫ π = pullback.fst π π ≫ π := rfl
  have h2 : pullback.snd π π ≫ π = pullback.fst π π ≫ π := pullback.condition.symm
  obtain ⟨fl1, su1, qc1⟩ := _root_.GlobalTheory.Mum.Desc.sum_flat_surjective_quasiCompact R hA S π hP hS hI G' hG N _ h1
  obtain ⟨fl2, su2, qc2⟩ := _root_.GlobalTheory.Mum.Desc.sum_flat_surjective_quasiCompact R hA S π hP hS hI G' hG N _ h2
  have e12 := _root_.GlobalTheory.Mum.DescKP.sum_eq_of_sum_eq R hA S π hP hS hI G' hG N hL _ _ h1 h2
  have e21 := _root_.GlobalTheory.Mum.DescKP.sum_eq_of_sum_eq R hA S π hP hS hI G' hG N hL _ _ h2 h1
  let f := EffectiveEpi.desc (Desc.sum N _ h1).left (Desc.sum N _ h2).left (fun g g' h => e12 _ g g' h)
  let g := EffectiveEpi.desc (Desc.sum N _ h2).left (Desc.sum N _ h1).left (fun g g' h => e21 _ g g' h)
  have hf : (Desc.sum N _ h1).left ≫ f = (Desc.sum N _ h2).left := EffectiveEpi.fac _ _ _
  have hg : (Desc.sum N _ h2).left ≫ g = (Desc.sum N _ h1).left := EffectiveEpi.fac _ _ _
  have wf : f ≫ ((Over.pullback (pullback.snd π π)).obj G').hom =
      ((Over.pullback (pullback.fst π π)).obj G').hom := by
    rw [← cancel_epi (Desc.sum N _ h1).left, reassoc_of% hf, Over.w, Over.w]
  have wg : g ≫ ((Over.pullback (pullback.fst π π)).obj G').hom =
      ((Over.pullback (pullback.snd π π)).obj G').hom := by
    rw [← cancel_epi (Desc.sum N _ h2).left, reassoc_of% hg, Over.w, Over.w]
  have hfg : f ≫ g = 𝟙 _ := by
    rw [← cancel_epi (Desc.sum N _ h1).left, reassoc_of% hf, hg, Category.comp_id]
  have hgf : g ≫ f = 𝟙 _ := by
    rw [← cancel_epi (Desc.sum N _ h2).left, reassoc_of% hg, hf, Category.comp_id]
  have hs : Desc.sum N _ h1 ≫ Over.homMk f wf = Desc.sum N _ h2 := by
    apply Over.OverMorphism.ext
    exact hf
  have he := _root_.GlobalTheory.Mum.DescFix.emb_comp_of_sum_comp R hA S π hP hS hI G' hG N hL _ _ h1 h2 (Over.homMk f wf) hs
  have hm := _root_.GlobalTheory.Mum.DescHom.isMonHom_of_sum_of_emb R hA S π hP hS hI G' hG N _ _ h1 h2 (Over.homMk f wf) hs he
  refine ⟨⟨Over.homMk f wf, Over.homMk g wg, ?_, ?_⟩, hm, ?_⟩
  · apply Over.OverMorphism.ext
    exact hfg
  · apply Over.OverMorphism.ext
    exact hgf
  · intro T a x hx
    have hfix : Desc.embL N _ h1 ≫ f = Desc.embL N _ h2 := congrArg (fun k => k.left) he
    exact pt_of_fix N f hfix T a x hx

end GlobalTheory.Mum.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantBijectionLargerClosedField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.UpExt
open GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_eqv_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) E₀ (Φ : IntFam (maximalIdeal R) D.toPre N → H0 A.L N), Eqv D.toPre A (Kb R) N lab E₀ → (∀ F₀ s, F₀.Over s → Agree A.L (E₀ s) (Φ F₀)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) lab', LabExt em lab lab' → ∃ E', Eqv D.toPre A F N lab' E' ∧ ∀ F₀ s, F₀.Over s → Agree A.L (E' s) (Φ F₀) := by
  intro R _ _ _ hR D A N hN lab E₀ Φ hE hΦ F _ _ _ em lab' hlab
  have hN1 : 1 ≤ N := hN.pos
  haveI : CharZero R := hR.2
  letI : Algebra (Kb R) F := em.toAlgebra
  haveI : IsScalarTower (FractionRing R) (Kb R) F := IsScalarTower.of_algebraMap_eq fun x => (em.commutes x).symm
  have hem : IsScalarTower.toAlgHom (FractionRing R) (Kb R) F = em := AlgHom.ext fun _ => rfl
  let e : Fam D.toPre (Kb R) N →ₗ[Kb R] SecF A (Kb R) N :=
    { toFun := E₀
      map_add' := fun s t => SecOver.ext _ _ fun j => hE.add s t (s + t) (fun _ _ => rfl) j
      map_smul' := fun c s => SecOver.ext _ _ fun j => hE.smul c s (c • s) ((isSmul_iff _ _ _).2 rfl) j }
  obtain ⟨e', he', hc⟩ := _root_.GlobalTheory.FieldBaseChange.exists_bijective_extension _ _ _ _ _ _ (famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds N) (secPull A (Kb R) F N)
    (isExtension_famPull _ _ _ GlobalTheory.globalFns_holds hN1) (isExtension_secPull A (Kb R) F N) e hE.bij
  have hq := _root_.GlobalTheory.Mum.qkPt_algClosure_bijective R D.toPre F em N hN1
  have onto : ∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab' p = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := GlobalTheory.T.exists_torsion_point_from_fractionAlgClosure R A F em N hN1 x hx
      obtain ⟨p₀, hp₀⟩ := (hE.onto y).1 hy
      obtain ⟨p', hp', -⟩ := hq.1 p₀
      refine ⟨p', Over.OverMorphism.ext ?_⟩
      rw [hlab p₀ p' hp', hp₀, hxy]
    · rintro ⟨p, rfl⟩
      obtain ⟨p₀, hp₀, -⟩ := hq.2 p
      have hy := (hE.onto (lab p₀)).2 ⟨p₀, rfl⟩
      have e1 : lab' p = baseK (Kb R) F ≫ lab p₀ := Over.OverMorphism.ext (hlab p₀ p hp₀)
      rw [e1, ← MonObj.comp_pow, hy, MonObj.comp_one]
  refine ⟨fun s => e' s, ⟨he', fun s s' s'' h j => ?_, fun c s s' h j => ?_, onto,
    fun p => ((GlobalTheory.UT.SymFrame.main GlobalTheory.firstFiveLaws R (maximalIdeal R) hR.1 D F N hN p).1),
    fun p => GlobalTheory.SymFrameClause.exists_symLift R A F N hN (lab' p) ((onto _).2 ⟨p, rfl⟩),
    fun p w θ s s' hw hθ hs => GlobalTheory.T.equivariant_linearExtension_to_algClosedField R hR D A N hN lab E₀ hE F lab' (hem ▸ hlab) e' hc p w θ s s' hw hθ hs⟩, ?_⟩
  · obtain rfl : s'' = s + s' := fam_ext h
    rw [map_add (f := _)]
    rfl
  · obtain rfl : s' = c • s := (isSmul_iff _ _ _).1 h
    rw [map_smul]
    rfl
  · intro F₀ s hs
    obtain ⟨s₀, hs₀, -⟩ := _root_.GlobalTheory.Mum.IntFam.existsUnique_over R (maximalIdeal R) D.toPre N F₀ (Kb R)
    have h1 := _root_.GlobalTheory.Mum.UpExt.over_famPull R (maximalIdeal R) D.toPre N F₀ (Kb R) F s₀ hs₀
    obtain rfl := (_root_.GlobalTheory.Mum.IntFam.existsUnique_over R (maximalIdeal R) D.toPre N F₀ F).unique hs h1
    intro Z p p' hpp z J hJ
    show sval (e' (famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds N s₀)) p z J = _
    rw [hc]
    refine (sval_pullOver _ _ _ _ hJ).trans (hΦ F₀ s₀ hs₀ Z (p ≫ (secMap A (Kb R) F).left) p' ?_ z J hJ)
    rw [Category.assoc, ← hpp]
    exact congrArg (p ≫ ·) (congrArg (fun q => q.left) (secMap_snd A (Kb R) F))
end GlobalTheory.Mum.UpExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExternalTensorRigidifiedCubicalProduct
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.GrpBox

open GlobalTheory.SumDeg

theorem isBoxGen_extGen {X X₁ X₂ Y Y₁ Y₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : X ⟶ X₁) (f₂ : X ⟶ X₂)
    {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h₁ : Y ⟶ Y₁) (φ₁ : K → (Y₁ ⟶ X₁)) (e₁ : ∀ k, ψ k ≫ f₁ = h₁ ≫ φ₁ k) (t₁ : LB.Gen (LB.LinComb L₁ φ₁ ε))
    (h₂ : Y ⟶ Y₂) (φ₂ : K → (Y₂ ⟶ X₂)) (e₂ : ∀ k, ψ k ≫ f₂ = h₂ ≫ φ₂ k) (t₂ : LB.Gen (LB.LinComb L₂ φ₂ ε))
    (ht₁ : t₁.IsGen) (ht₂ : t₂.IsGen) :
    IsBoxGen (CubePf.idIsoL (extLB L₁ L₂ f₁ f₂)) h₁ h₂ (extGen L₁ L₂ f₁ f₂ ψ ε h₁ φ₁ e₁ t₁ h₂ φ₂ e₂ t₂) t₁ t₂ := by
  intro Z r z J₁ J₂ J hJ₁ hJ₂ hJ
  have hE := good_ext (f₁ := f₁) (f₂ := f₂) hJ₁ hJ₂
  have key := gen_trans (isGen_extGen L₁ L₂ f₁ f₂ ψ ε h₁ φ₁ e₁ t₁ h₂ φ₂ e₂ t₂ ht₁ ht₂) r z (hE.mem ψ r) (hJ.mem ψ r)
  have k2 := gm_extGen L₁ L₂ f₁ f₂ ψ ε h₁ φ₁ e₁ t₁ h₂ φ₂ e₂ t₂ r z _ (hE.mem ψ r)
  rw [val_of t₁ (r ≫ h₁) z J₁ (fun k => J₁ ((r ≫ ψ k) ≫ f₁)) (fun k => by rw [Category.assoc, Category.assoc, e₁]),
    val_of t₂ (r ≫ h₂) z J₂ (fun k => J₂ ((r ≫ ψ k) ≫ f₂)) (fun k => by rw [Category.assoc, Category.assoc, e₂])]
  exact key.symm.trans k2

section Grp

variable {S : Scheme.{0}} {A A₁ A₂ : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A₁] [IsCommMonObj A₁]
  [GrpObj A₂] [IsCommMonObj A₂]

def pullCub (L : RigLB A₁) (c : CubicalStr A₁ L) (a : A ⟶ A₁) [IsMonHom a] :=
  CubePf.cubical (CubeMap.ofHom a) L c (LB.isLB_pull L.isLB _)
    (LBxP.isGen_pullAlong L.L a.left (𝟙 _) (fun _ : PUnit => eSec A₁) (fun _ => 1)
      (fun _ => eSec A) (fun _ => (CubeMap.ofHom a).e_comm) L.rig L.rigGen)

theorem exists_strBox (a₁ : A ⟶ A₁) (a₂ : A ⟶ A₂) [IsMonHom a₁] [IsMonHom a₂]
    (L₁ : RigLB A₁) (L₂ : RigLB A₂) (c₁ : CubicalStr A₁ L₁) (c₂ : CubicalStr A₂ L₂)
    (s₁ : SymGen A₁ L₁.L) (s₂ : SymGen A₂ L₂.L) (hs₁ : s₁.IsGen) (hs₂ : s₂.IsGen)
    (n₁ : LB.Gen.Corr L₁.L _ _ _ _ (LB.pullGen L₁.L _ _ s₁ (eSec A₁)) (LB.oneGen L₁.L))
    (n₂ : LB.Gen.Corr L₂.L _ _ _ _ (LB.pullGen L₂.L _ _ s₂ (eSec A₂)) (LB.oneGen L₂.L)) :
    ∃ (L : RigLB A) (c : CubicalStr A L) (s : SymGen A L.L)
      (w : LB.Iso L.L (extLB L₁.L L₂.L a₁.left a₂.left)), s.IsGen ∧
      LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec A)) (LB.oneGen L.L) ∧
      StrBox a₁ a₂ w L.rig L₁.rig L₂.rig c.t c₁.t c₂.t s s₁ s₂ := by
  have hL := isLB_extLB L₁.isLB L₂.isLB a₁.left a₂.left
  refine ⟨⟨extLB L₁.L L₂.L a₁.left a₂.left,
      extAt L₁.L L₂.L a₁.left a₂.left (eSec A) 1 _ (eSec_comp a₁) L₁.rig _ (eSec_comp a₂) L₂.rig, hL,
      isGen_extAt _ _ _ _ _ _ _ _ _ _ _ _ L₁.rigGen L₂.rigGen⟩,
    tensCub (pullCub L₁ c₁ a₁) (pullCub L₂ c₂ a₂) _ hL _,
    extGen L₁.L L₂.L a₁.left a₂.left _ _ a₁.left _ (inv_comp a₁) s₁ a₂.left _ (inv_comp a₂) s₂,
    CubePf.idIsoL _, isGen_extGen _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs₁ hs₂, ?_, CubePf.idIsoL_isGen hL,
    isBoxGen_extGen _ _ _ _ _ _ _ _ _ _ _ _ _ _ L₁.rigGen L₂.rigGen,
    isBoxGen_extGen L₁.L L₂.L a₁.left a₂.left (thφ A (x3 A)) thε
      (a₁ ⊗ₘ a₁ ⊗ₘ a₁).left (thφ A₁ (x3 A₁)) (fun I => (CubeMap.ofHom a₁).psum_comm I.down) c₁.t
      (a₂ ⊗ₘ a₂ ⊗ₘ a₂).left (thφ A₂ (x3 A₂)) (fun I => (CubeMap.ofHom a₂).psum_comm I.down) c₂.t
      c₁.isGen c₂.isGen,
    isBoxGen_extGen _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs₁ hs₂⟩
  refine corr_of_val hL fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at L₁.isLB y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at L₂.isLB y
  have o : eSec A ≫ (ι[A]).left = eSec A :=
    congrArg (fun m => m.left) (GrpObj.one_inv : η[A] ≫ ι[A] = η[A])
  have v₁ : val s₁ (eSec A₁) y J₁ = 1 := by
    have v := val_corr hJ₁ n₁ (𝟙 _)
    rwa [val_pull hJ₁, Category.id_comp, val_one] at v
  have v₂ : val s₂ (eSec A₂) y J₂ = 1 := by
    have v := val_corr hJ₂ n₂ (𝟙 _)
    rwa [val_pull hJ₂, Category.id_comp, val_one] at v
  have e := (val_extGen L₁.L L₂.L a₁.left a₂.left _ _ a₁.left _ (inv_comp a₁) s₁ a₂.left _ (inv_comp a₂) s₂
    hs₁ hs₂ (eSec A) hJ hJ₁ hJ₂).trans (congrArg₂ (· * ·) (prod_sym (eSec A) _) rfl)
  rw [o, mul_inv_cancel, eSec_comp, eSec_comp, v₁, v₂, _root_.mul_one, _root_.mul_one] at e
  rw [val_pull hJ, Category.id_comp, val_one]
  exact e

end Grp

theorem exists_prod : ∀ (S : Scheme.{0}) (G₁ G₂ : Over S) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (L₁ : RigLB G₁) (L₂ : RigLB G₂) (c₁ : CubicalStr G₁ L₁) (c₂ : CubicalStr G₂ L₂) (s₁ : SymGen G₁ L₁.L) (s₂ : SymGen G₂ L₂.L), s₁.IsGen → s₂.IsGen → LB.Gen.Corr L₁.L _ _ _ _ (LB.pullGen L₁.L _ _ s₁ (eSec G₁)) (LB.oneGen L₁.L) → LB.Gen.Corr L₂.L _ _ _ _ (LB.pullGen L₂.L _ _ s₂ (eSec G₂)) (LB.oneGen L₂.L) → ∃ (L : RigLB (G₁ ⊗ G₂)) (c : CubicalStr (G₁ ⊗ G₂) L) (s : SymGen (G₁ ⊗ G₂) L.L) (w : LB.Iso L.L (extLB L₁.L L₂.L (fst G₁ G₂).left (snd G₁ G₂).left)), s.IsGen ∧ LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec (G₁ ⊗ G₂))) (LB.oneGen L.L) ∧ StrBox (fst G₁ G₂) (snd G₁ G₂) w L.rig L₁.rig L₂.rig c.t c₁.t c₂.t s s₁ s₂ := by
  intro S G₁ G₂ _ _ _ _ L₁ L₂ c₁ c₂ s₁ s₂ hs₁ hs₂ n₁ n₂
  exact exists_strBox (fst G₁ G₂) (snd G₁ G₂) L₁ L₂ c₁ c₂ s₁ s₂ hs₁ hs₂ n₁ n₂

end GlobalTheory.GrpBox
end
end

