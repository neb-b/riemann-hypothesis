module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInvertibleAdaptedBasisLinkMatrix
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsOpensEtaleOfUniqueClassicalPoints
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClassicalPointEqOfReductionCoords
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpecialFibreTorsionEqReductions
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0099

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LinearIndependentThetaBasisGeometricFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight

noncomputable section
namespace GlobalTheory.ZH.FibreIndep

open GlobalTheory.VVRank GlobalTheory.UnivBasisMove

theorem linearIndependent_pullM (hS : SecBaseChangeAnySt) {S : Scheme.{0}} (P : PolAV S) (n : ℕ) (hn : 1 ≤ n)
    {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (p : T'.left) (hp : ∀ q, q = p) (h : T' ⟶ T)
    {J : Type} [Fintype J] (hJ : Fintype.card J = n ^ P.g) (s : J → SecM P.A P.L n T)
    (hs : ∀ x, ∃ c : J → Γ(T.left, ⊤), x = ∑ i, c i • s i) :
    LinearIndependent Γ(T'.left, ⊤) (fun i => pullM P.A P.L n h (s i)) := by
  have hne : Nonempty (⊤ : T'.left.Opens) := ⟨⟨p, trivial⟩⟩
  have hnt : Nontrivial Γ(T'.left, ⊤) := Scheme.component_nontrivial T'.left ⊤
  obtain ⟨V, hV, b, hb⟩ := hS S P n hn (T'.hom p)
  let l : T' ⟶ overRes (T := baseOver S) V := Over.homMk
    (IsOpenImmersion.lift V.ι T'.hom (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      rw [hp y]
      exact hV)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
  obtain ⟨c, -⟩ := exists_basis P n b hb T' l
  have := Module.Free.of_basis c
  have := Module.Finite.of_basis c
  refine linearIndependent_of_top_le_span_of_card_eq_finrank (fun x _ => ?_)
    (by rw [Module.finrank_eq_card_basis c, Fintype.card_fin, hJ])
  refine Submodule.span_le.2 ?_ (LinkMatrix.mem_span_pullM hS P n hn p hp h x)
  rintro _ ⟨u, rfl⟩
  obtain ⟨a, rfl⟩ := hs u
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Submodule.sum_mem _ fun i _ => by
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem linearIndependent_moved : LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)), w.IsGen → ∀ t : S.J → SecA u.A (PadicAlgCl p) S.N, (∀ i, Moved u w (t i) (ρ.s i)) → LinearIndependent Γ((TFK (R := u.V) (PadicAlgCl p)).left, ⊤) (fun i => SecM.ofSec u.A.A (t i)) := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u w hw t ht
  have hN : 1 ≤ S.N := by
    rw [ρ.N_eq]
    exact Nat.one_le_pow _ _ (pow_pos ρ.n_prime.pos _)
  let T := TFK (R := u.V) (PadicAlgCl p)
  let T' : Over (Sp S.R) := Over.mk (T.hom ≫ spMap u.yK)
  have : IsAffine T'.left := inferInstanceAs (IsAffine (Sp (PadicAlgCl p)))
  have : IsAffine (baseOver (Sp S.R)).left := inferInstanceAs (IsAffine (Sp S.R))
  let h₀ : T' ⟶ baseOver (Sp S.R) := Over.homMk (spMap y₀) (base_eq u)
  have li := linearIndependent_pullM hL.2.1.secBaseChangeAny ρ.P S.N hN (T' := T')
    (IsLocalRing.closedPoint (PadicAlgCl p))
    (fun q => Subsingleton.elim (α := PrimeSpectrum (PadicAlgCl p)) _ _) h₀ (J := S.J)
    (by rw [ρ.g_eq]; exact ρ.card) (fun i => SecM.ofSec ρ.P.A (ρ.s i)) (fun x => by
      obtain ⟨c, hc⟩ := (ρ.s_basis (SecM.toSec ρ.P.A x)).exists
      refine ⟨c, Subtype.ext (funext fun j => ?_)⟩
      rw [Submodule.coe_sum, Finset.sum_apply]
      exact hc j)
  obtain ⟨E, hE⟩ := exists_linearEquiv u.cart hw ρ.P.isLB u.A.isLB (S.N : ℤ) T
  have e : ∀ i, E (pullM ρ.P.A ρ.P.L S.N h₀ (SecM.ofSec ρ.P.A (ρ.s i))) = SecM.ofSec u.A.A (t i) := fun i => by
    have r : Rel u.cart (T := T) (T₀ := baseOver (Sp S.R)) (spMap y₀) (base_eq u) w (SecM.ofSec u.A.A (t i))
      (SecM.ofSec ρ.P.A (ρ.s i)) := ht i
    have r' := r.pull (T' := T) (T₀' := T') (𝟙 T.left) (Category.id_comp _) (𝟙 T) h₀ rfl
    rw [pullM_id _ u.A.isLB] at r'
    exact (hE _).unique_down ρ.P.isLB u.A.isLB r'
  have li' := LinearIndependent.map' (R := Γ(T.left, ⊤)) li E.toLinearMap E.ker
  exact (funext e : _ = fun i => SecM.ofSec u.A.A (t i)) ▸ li'

end GlobalTheory.ZH.FibreIndep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmoothOfRelativeDimensionGroupSchemeOfTests
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory

theorem isStandardSmoothOfRelativeDimension_mvPolynomial_fin (R : Type) [CommRing R] (n : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R) := by
  let P₀ : Algebra.Presentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    { __ := Algebra.Generators.mvPolynomial R (Fin n)
      relation := Empty.elim
      span_range_relation_eq_ker := by
        rw [Algebra.Generators.ker_mvPolynomial]
        simp }
  let P₁ : Algebra.PreSubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    { __ := P₀
      map := Empty.elim
      map_inj := fun a => a.elim }
  let P₂ : Algebra.SubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    { __ := P₁
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  exact P₂.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])

theorem smoothOfRelativeDimension_affineSpace_fin (S : Scheme.{0}) (n : ℕ) :
    SmoothOfRelativeDimension n (𝔸(Fin n; S) ↘ S) := by
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} n
  refine MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension n) _ _ ?_
  have := isIso_of_isTerminal specULiftZIsTerminal.{0} terminalIsTerminal (terminal.from _)
  rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom MvPolynomial.C)),
    MorphismProperty.cancel_right_of_respectsIso (P := @SmoothOfRelativeDimension n),
    HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).2
    (isStandardSmoothOfRelativeDimension_mvPolynomial_fin (ULift ℤ) n)

namespace ZJ

theorem Core.exists_opens_smoothOfRelativeDimension (C : Core) (hT : C.HasTests) (hF : C.Fib)
    (w : C.G.toScheme) (hc : IsClosed ({w} : Set C.G.toScheme)) :
    ∃ V : C.G.toScheme.Opens, w ∈ V ∧ SmoothOfRelativeDimension C.g (V.ι ≫ C.GG.hom) := by
  obtain ⟨hsep, hlft, -, hint, -, -, ha, hcart, -, -, -, hdom, -⟩ := _root_.GlobalTheory.ZJ.core_basic C
  obtain ⟨W, hw, u, -, hu⟩ := GlobalTheory.T.exists_coord_reducedFibre_closedPoint C hT hF w hc
  have hqf := _root_.GlobalTheory.quasiFiniteAt_homOfVector_of_coord C w W hw u hc hu
  have huniq := _root_.GlobalTheory.ZJ.classical_eq_of_coord C hT hF w W hw u hu
  have hint' : IsIntegral C.G.toScheme := hint
  have : Nonempty W.toScheme := ⟨⟨w, hw⟩⟩
  have : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  let t : W.toScheme ⟶ C.Z := W.ι ≫ C.GG.hom
  let u' : Fin C.g → Γ(W.toScheme, ⊤) := fun i => W.topIso.inv.hom (u i)
  let v : W.toScheme ⟶ 𝔸(Fin C.g; C.Z) := AffineSpace.homOfVector t u'
  have hv : v ≫ 𝔸(Fin C.g; C.Z) ↘ C.Z = t := AffineSpace.homOfVector_over _ _
  have : LocallyOfFiniteType t := inferInstanceAs (LocallyOfFiniteType (W.ι ≫ C.GG.hom))
  have : IsSeparated t := inferInstanceAs (IsSeparated (W.ι ≫ C.GG.hom))
  have : IsDominant W.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact W.isOpen.dense ⟨w, hw⟩⟩
  have : IsDominant t := inferInstanceAs (IsDominant (W.ι ≫ C.GG.hom))
  have hA := smoothOfRelativeDimension_affineSpace_fin C.Z C.g
  have : Smooth (𝔸(Fin C.g; C.Z) ↘ C.Z) := SmoothOfRelativeDimension.smooth C.g _
  have : LocallyOfFiniteType v := by
    have : LocallyOfFiniteType (v ≫ 𝔸(Fin C.g; C.Z) ↘ C.Z) := by rw [hv]; infer_instance
    exact locallyOfFiniteType_of_comp v (𝔸(Fin C.g; C.Z) ↘ C.Z)
  have : IsSeparated v := by
    have : IsSeparated (v ≫ 𝔸(Fin C.g; C.Z) ↘ C.Z) := by rw [hv]; infer_instance
    exact IsSeparated.of_comp v (𝔸(Fin C.g; C.Z) ↘ C.Z)
  let U' : W.toScheme.Opens := t ⁻¹ᵁ C.U
  have hU' : (U' : Set W.toScheme).Nonempty := by
    obtain ⟨x, hx⟩ := t.denseRange.exists_mem_open C.U.isOpen C.ne
    exact ⟨x, hx⟩
  have hsm : SmoothOfRelativeDimension C.g (U'.ι ≫ t) := by
    let l : U'.toScheme ⟶ C.A.left := hcart.lift (U'.ι ≫ W.ι) (t ∣_ C.U)
      (by rw [morphismRestrict_ι, Category.assoc])
    have h1 : l ≫ C.a = U'.ι ≫ W.ι := hcart.lift_fst _ _ _
    have h2 : l ≫ C.A.hom = t ∣_ C.U := hcart.lift_snd _ _ _
    have : IsOpenImmersion (l ≫ C.a) := by rw [h1]; infer_instance
    have : IsOpenImmersion l := IsOpenImmersion.of_comp l C.a
    have h3 : U'.ι ≫ t = l ≫ C.A.hom ≫ C.U.ι := by
      rw [reassoc_of% h2, morphismRestrict_ι]
    have := C.dim
    have h4 : SmoothOfRelativeDimension (0 + (C.g + 0)) (l ≫ C.A.hom ≫ C.U.ι) := inferInstance
    rw [h3]
    simpa using h4
  have : IsDominant v := _root_.GlobalTheory.isDominant_homOfVector_of_quasiFiniteAt W.toScheme C.Z t C.g U' hU' hsm u' ⟨w, hw⟩ hqf
  have := C.flat
  have := C.lft
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme 𝔸(Fin C.g; C.Z) :=
    forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (𝔸(Fin C.g; C.Z) ↘ C.Z) C.normal
  have hc' : IsClosed ({⟨w, hw⟩} : Set W.toScheme) := by
    have := hc.preimage W.ι.continuous
    convert this using 1
    ext z
    exact Subtype.ext_iff
  have huniq' : ∀ (p : ℕ) [Fact p.Prime] (a a' : Sp (OO p) ⟶ W.toScheme),
      a ≫ v = a' ≫ v → a (cPt p) = ⟨w, hw⟩ → rPt p ≫ a = rPt p ≫ a' →
      Set.range (gPt p ≫ a) ⊆ U' → Set.range (gPt p ≫ a') ⊆ U' → a = a' := by
    intro p _ a a' h hp hr hg _
    refine huniq p a a' ?_ ?_ hp hr fun i => ?_
    · change Set.range (gPt p ≫ a ≫ t) ⊆ C.U
      rintro _ ⟨z, rfl⟩
      rw [← Category.assoc, Scheme.Hom.comp_apply]
      exact hg (Set.mem_range_self z)
    · change a ≫ t = a' ≫ t
      rw [← hv, reassoc_of% h]
    · have e : ∀ b : Sp (OO p) ⟶ W.toScheme,
          b.appTop.hom (u' i) = (b ≫ v).appTop.hom (AffineSpace.coord C.Z i) := fun b => by
        rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
        exact congrArg _ (AffineSpace.homOfVector_appTop_coord t u' i).symm
      exact (e a).trans ((congrArg (fun c : Sp (OO p) ⟶ 𝔸(Fin C.g; C.Z) =>
        c.appTop.hom (AffineSpace.coord C.Z i)) h).trans (e a').symm)
  obtain ⟨V, hV, hE⟩ : ∃ V : W.toScheme.Opens, ⟨w, hw⟩ ∈ V ∧ Etale (V.ι ≫ v) :=
    exists_opens_etale_of_unique_classical_points 𝔸(Fin C.g; C.Z)
      (𝔸(Fin C.g; C.Z) ↘ C.Z ≫ C.π) hN W.toScheme v ⟨w, hw⟩ U' hc' hqf hU' huniq'
  have h5 : SmoothOfRelativeDimension (0 + C.g) ((V.ι ≫ v) ≫ 𝔸(Fin C.g; C.Z) ↘ C.Z) :=
    inferInstance
  rw [Category.assoc, hv, zero_add] at h5
  refine ⟨(V.ι ≫ W.ι).opensRange, ⟨⟨⟨w, hw⟩, hV⟩, rfl⟩, ?_⟩
  have h6 : SmoothOfRelativeDimension (0 + C.g)
      ((V.ι ≫ W.ι).isoOpensRange.inv ≫ V.ι ≫ t) := inferInstance
  rw [zero_add] at h6
  convert h6 using 1
  rw [← (V.ι ≫ W.ι).isoOpensRange_inv_comp]
  simp only [Category.assoc, t]

theorem Core.smoothOfRelativeDimension_of_hasTests :
    ∀ C : Core, C.HasTests → C.Fib → SmoothOfRelativeDimension C.g C.GG.hom := by
  intro C hT hF
  obtain ⟨-, hlft, -⟩ := _root_.GlobalTheory.ZJ.core_basic C
  have := C.lft
  choose V hV hs using C.exists_opens_smoothOfRelativeDimension hT hF
  let V' : {w : C.G.toScheme // IsClosed ({w} : Set C.G.toScheme)} → C.G.toScheme.Opens :=
    fun w => V w.1 w.2
  have htop : iSup V' = ⊤ :=
    (jacobson_closedPoints_tools_int C.G.toScheme (C.GG.hom ≫ C.π)).2.2.1 _ _ fun x hx =>
      ⟨fun _ => trivial, fun _ => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hV x hx⟩⟩
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} C.g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{0} C.g) V' htop
    fun w => hs w.1 w.2

end ZJ
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPointsSpecialFibreSupportCoordinates
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.TorsCrd

theorem exists_unit_smul {O C J : Type} [CommRing O] [Field C] [Fintype J] [DecidableEq J] (φ : O →+* C)
    (hφ : Function.Injective φ) (m : Matrix J J O) (hm : IsUnit m.det) (w u : J → O) (lam : C)
    (h : ∀ i, φ (u i) = lam * φ (m.mulVec w i)) {i k : J} (hi : IsUnit (w i)) (hk : IsUnit (u k)) :
    ∃ mu : Oˣ, m.mulVec (fun j => (mu : O) * w j) = u := by
  have h1 : φ (m⁻¹.mulVec u i) = lam * φ (w i) := by
    have e : m⁻¹.mulVec (m.mulVec w) = w := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hm, Matrix.one_mulVec]
    conv_rhs => rw [← e]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul] at h ⊢
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h j]; ring
  obtain ⟨v, hv⟩ := hi.exists_right_inv
  have h2 : φ (m⁻¹.mulVec u i * v) = lam := by
    rw [map_mul, h1, _root_.mul_assoc, ← map_mul, hv, map_one, _root_.mul_one]
  have h3 : ∀ j, u j = (m⁻¹.mulVec u i * v) * m.mulVec w j := fun j => hφ (by rw [map_mul, h2, h])
  have h4 : IsUnit (m⁻¹.mulVec u i * v) := isUnit_of_mul_isUnit_left (h3 k ▸ hk)
  refine ⟨h4.unit, funext fun j => ?_⟩
  rw [h3 j, IsUnit.unit_spec]
  exact congrFun (Matrix.mulVec_smul m (m⁻¹.mulVec u i * v) w) j

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem sec_mem (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) {l : Q.Λ} {z : M.Z} (hz : z ∈ Q.W l)
    {x₀ h : S.Gam} (hx : x₀ ∈ S.supI M z) (hh : h ∈ S.HH M z) (i : S.J) :
    (Q.B l i ⬝ᵥ S.ev h) / S.th x₀ ∈ M.O z := by
  refine (hB.sec z x₀ hx h hh).1 _ ?_
  rw [Q.basis l z hz]
  exact Submodule.subset_span ⟨i, rfl⟩

theorem sec_unit (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) {l : Q.Λ} {z : M.Z} (hz : z ∈ Q.W l)
    {x₀ h : S.Gam} (hx : x₀ ∈ S.supI M z) (hh : h ∈ S.HH M z) :
    ∃ i, IsUnit (⟨_, sec_mem hB Q hz hx hh i⟩ : M.O z) := by
  obtain ⟨h1, i, h2, h3⟩ := hB.sec z x₀ hx h hh
  set v : S.J → Ω := fun j => algebraMap o Ω (S.proj (S.TT M z) 0 j i) with hv
  have hvE : v ∈ EE.E z := by
    have e : v = ∑ j, (algebraMap o (M.O z) (S.proj (S.TT M z) 0 j i)) • (Pi.single j (1 : Ω) : S.J → Ω) := by
      ext j
      simp [hv, Finset.sum_apply, Pi.single_apply, Subalgebra.smul_def, Algebra.algebraMap_eq_smul_one]
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hB.mem z j)
  have hu : IsUnit (⟨_, h1 v hvE⟩ : M.O z) :=
    (RatModel.isUnit_O_iff _).2 ⟨div_ne_zero h2 hx.1, by simpa using h3⟩
  have hvE' := hvE
  rw [Q.basis l z hz] at hvE'
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (M.O z) (v := fun k j => Q.B l k j)).1 hvE'
  have e : (⟨_, h1 v hvE⟩ : M.O z) = ∑ k, c k * ⟨_, sec_mem hB Q hz hx hh k⟩ := by
    refine Subtype.ext ?_
    show v ⬝ᵥ S.ev h / S.th x₀ = _
    rw [← hc, sum_dotProduct, Finset.sum_div]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_dotProduct, Subalgebra.smul_def, smul_eq_mul, mul_div_assoc]
  rw [e] at hu
  by_contra hn
  push_neg at hn
  refine (IsLocalRing.mem_maximalIdeal _).1 (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ ?_) hu
  exact (IsLocalRing.mem_maximalIdeal _).2 (hn k)

variable {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p}

theorem cen {Q : Clos ρ M U₀ EE} {u : ρ.UTest p y₀} (c : Q.Fac y u) : M.Cen U₀ (y (cPt p)) y := by
  refine ⟨rfl, ?_⟩
  have e : gPt p ≫ spMap u.j = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have e2 : gPt p ≫ y = (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ c.yK) ≫ U₀.ι := by
    rw [Category.assoc, c.yK_fac, ← Category.assoc, ← e, Category.assoc, c.fac]
  rw [e2]
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Hom.comp_apply]
  exact ((spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ c.yK) w).2

theorem val_gen (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) {l : Q.Λ} (hz : y (cPt p) ∈ Q.W l)
    (hc : M.Cen U₀ (y (cPt p)) y) (ha : S.At M y y₀) {x₀ : S.Gam} (hx : S.th x₀ ≠ 0) (h : S.Gam) (i : S.J) :
    M.val (gPt p ≫ y) ((Q.B l i ⬝ᵥ S.ev h) / S.th x₀) = M.val (gPt p ≫ y) (S.th x₀)⁻¹ *
      ((Q.B l).map (M.val (gPt p ≫ y))).mulVec (fun j => y₀ ⟨S.ev h j, S.ev_mem h j⟩) i := by
  let s : Sp (PadicAlgCl p) := IsLocalRing.closedPoint _
  set ξ := (gPt p ≫ y) s with hξ
  have hr : Set.range (gPt p ≫ y) = {ξ} := RatModel.range_eq_singleton _ s
  have hU : ξ ∈ U₀ := hc.2 ⟨s, rfl⟩
  have hW : ξ ∈ Q.W l := (RatModel.gPt_specializes rfl s).mem_open (Q.W l).isOpen hz
  have hBm : ∀ j, Q.B l i j ∈ M.O ξ := by
    have : Q.B l i ∈ EE.E ξ := by
      rw [Q.basis l ξ hW]
      exact Submodule.subset_span ⟨i, rfl⟩
    rw [hB.ee.1 ξ hU] at this
    exact (RatModel.Lat.mem_const_iff M).1 this
  have hev : ∀ j, S.ev h j ∈ M.O ξ := fun j => RatModel.mem_ringOn.1 (hB.ov.le (S.ev_mem h j)) ξ hU
  have hth : (S.th x₀)⁻¹ ∈ M.O ξ := RatModel.mem_ringOn.1 (hB.ov.th_unit x₀ hx) ξ hU
  let e : M.O ξ := ⟨_, hth⟩ * ∑ j, ⟨_, hBm j⟩ * ⟨_, hev j⟩
  have he : (Q.B l i ⬝ᵥ S.ev h) / S.th x₀ = (e : Ω) := by
    simp only [e]
    push_cast
    rw [div_eq_inv_mul]
    rfl
  rw [he, ← RatModel.valHom_apply _ _ hr]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [e, map_mul, map_sum, RatModel.valHom_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  exact congrArg (_ * ·) (ha ⟨_, S.ev_mem h j⟩).symm

theorem ker_eq (t : ρ.GeoTest p y₀) : t.τ.yy.ker = t.l.yy.ker := by
  obtain ⟨e, -, he⟩ := t.mt
  ext a
  have := he a 0
  rw [map_zero] at this
  exact this

theorem big (ρ : S.Real) (h : S.Big) : Big S.g S.N (S.r * S.N) := by
  refine ⟨?_, h.1, h.2.1⟩
  have h1 : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
  rw [ρ.N_eq]
  nlinarith

theorem crd_red (hL : GlobalTheory.UT.LL) [ArithBase o Ω] (hB : BaseFacts S M U₀ EE) {Q : Clos ρ M U₀ EE}
    {t : ρ.GeoTest p y₀} {c : Q.Fac y t.u} (tm : Q.TMap t c) (hS : S.Big) {x₀ a : S.Gam}
    (hx : x₀ ∈ S.supI M (y (cPt p))) (ha : a ∈ S.HH M (y (cPt p))) (cc : Sp (OO p) ⟶ t.u.G.left) (a' : t.u.PtC)
    (x : t.mod.Φ.Pt) (h₁ : cc ≫ t.u.G.hom = spMap t.u.j) (h₂ : gPt p ≫ cc = t.u.toG a')
    (h₃ : t.u.toA a' = spMap y₀ ≫ (ρ.pt a).left) (h₄ : rPt p ≫ cc = x.left ≫ t.mod.r) :
    ∃ w, Crd (t.mod.Φ.H 1) t.mod.F x.left w ∧
      (tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)).mulVec w =
        fun i => M.val (rPt p ≫ y) ((Q.B tm.l i ⬝ᵥ S.ev a) / S.th x₀) := by
  have hv := (_root_.GlobalTheory.ZH.EvCrd.ev_crd_act hL o Ω S ρ).1 _ y₀ a
  rw [← h₃] at hv
  have hb := t.link a' _ hv
  obtain ⟨wc, hwc⟩ := CrdCalc.crd_exists t.mod.isLB t.σ cc
  have hg := CrdCalc.crd_map (OO p).subtype hwc
  rw [← h₂] at hb
  obtain ⟨κ, hκ⟩ := CrdCalc.crd_unique hg hb
  obtain ⟨⟨i, -, hi⟩, -⟩ := _root_.GlobalTheory.ZH.ModPrim.exists_unit_and_residue_point hL.1 hL.2.1 p t.u.V t.u.j t.u.G S.g S.N (S.r * S.N) _ t.l.q _ S.J t.σ t.cls
    t.mod (big ρ hS) cc wc h₁ hwc
  obtain ⟨k, hk⟩ := sec_unit hB Q tm.mem hx ha
  let u : S.J → OO p := fun i => RatModel.valLoc y (y (cPt p)) specializes_rfl ⟨_, sec_mem hB Q tm.mem hx ha i⟩
  have hm : IsUnit (tm.m.map t.u.j).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact tm.unit.map _
  obtain ⟨mu, hmu⟩ := exists_unit_smul (OO p).subtype Subtype.val_injective (tm.m.map t.u.j) hm wc u
    (M.val (gPt p ≫ y) (S.th x₀)⁻¹ * κ) (fun i => by
      refine (RatModel.val_spMap_comp (OO p).subtype y specializes_rfl _).symm.trans ?_
      refine (val_gen hB Q tm.mem (cen c) c.at_ hx.1 a i).trans ?_
      rw [tm.m_eq, ← Matrix.mulVec_mulVec, funext hκ, _root_.mul_assoc]
      congr 1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact mul_left_comm _ _ _) hi (hk.map _)
  have hr := CrdCalc.crd_map (IsLocalRing.residue (OO p)) (CrdCalc.crd_smul mu hwc)
  obtain ⟨w', hw'⟩ := CrdCalc.crd_exists (t.mod.Φ.H_isLB 1) t.mod.F (R := kb p) x.left
  have hw'' := t.mod.red x w' hw'
  rw [← h₄] at hw''
  obtain ⟨ν, hν⟩ := CrdCalc.crd_unique hw'' hr
  refine ⟨fun j => IsLocalRing.residue (OO p) (mu * wc j), ?_, funext fun i => ?_⟩
  · rw [funext hν]
    exact CrdCalc.crd_smul ν hw'
  · refine Eq.trans ?_ (RatModel.val_spMap_comp (IsLocalRing.residue (OO p)) y specializes_rfl
      ⟨_, sec_mem hB Q tm.mem hx ha i⟩).symm
    refine Eq.trans ?_ (congrArg (IsLocalRing.residue (OO p)) (congrFun hmu i))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

theorem tors_crd : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → (∀ x : t.mod.Φ.Pt, x ^ (S.r * S.N) = 1 → ∃ w, Crd (t.mod.Φ.H 1) t.mod.F x.left w ∧ (tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)).mulVec w ∈ Q.Tors (rPt p ≫ y) tm.l) ∧ ∀ v ∈ Q.Tors (rPt p ≫ y) tm.l, ∃ (x : t.mod.Φ.Pt) (w : S.J → kb p), x ^ (S.r * S.N) = 1 ∧ Crd (t.mod.Φ.H 1) t.mod.F x.left w ∧ (tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)).mulVec w = v := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q p _ y y₀ t c tm hS
  have hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := fun a => by
    rw [c.at_]
    exact RatModel.norm_val_le_one rfl ((M.O _).algebraMap_mem a)
  have hH : S.HH M (y (cPt p)) = t.l.yy.ker := (hB.atTest _ p y y₀ t.τ (cen c) c.at_).trans (ker_eq t)
  obtain ⟨-, g₁, g₂⟩ := _root_.GlobalTheory.ZH.special_torsion_eq_reduction hL o Ω S ρ p y₀ t.u t.l t.σ t.cls t.mod hint
  have hr : Set.range (rPt p ≫ y) = {y (cPt p)} := by
    rw [RatModel.range_eq_singleton (K := kb p) _ (IsLocalRing.closedPoint (kb p))]
    exact congrArg (fun s => ({y s} : Set M.Z)) (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))
  constructor
  · intro x hx
    obtain ⟨a, ha, cc, a', h₁, h₂, h₃, h₄⟩ := g₁ x hx
    obtain ⟨x₀, hx₀⟩ := hB.ov.div (y (cPt p))
    rw [← hH] at ha
    obtain ⟨w, hw, e⟩ := crd_red hL hB tm hS hx₀ ha cc a' x h₁ h₂ h₃ h₄
    exact ⟨w, hw, y (cPt p), by rw [hr]; rfl, x₀, hx₀, a, ha, e⟩
  · rintro v ⟨z, hz, x₀, hx₀, a, ha, rfl⟩
    rw [hr] at hz
    obtain rfl : z = y (cPt p) := hz
    obtain ⟨cc, a', x, h₁, h₂, h₃, h₄, h₅⟩ := g₂ a (hH ▸ ha)
    obtain ⟨w, hw, e⟩ := crd_red hL hB tm hS hx₀ ha cc a' x h₁ h₂ h₃ h₄
    exact ⟨x, w, h₅, hw, e⟩

end GlobalTheory.ZH.TorsCrd
end
end

