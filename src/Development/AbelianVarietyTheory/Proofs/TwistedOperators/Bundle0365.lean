module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0344
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotientSummable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.GenInhabited
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0345
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLineGeneratorZariskiLocally
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

namespace GlobalTheory.HeckeEx

theorem exists_secGen_away : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : Type) [CommRing T] [Algebra c.F T] (x : Sp T ⟶ Xo.X), x ≫ Xo.s = sOf c T → ∀ q : PrimeSpectrum T, ∃ g : T, g ∉ q.asIdeal ∧ ∃ s : LB.Sec (PPx (spMap (algebraMap T (Localization.Away g)) ≫ x)), SecGen _ s := by
  intro E _ _ _ H Dw l Xo c T _ _ x hx q
  have hS := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨xF, h1, h2⟩ : ∃ xF : Sp T ⟶ Xo.XF c, xF ≫ pullback.fst _ _ = x ∧
      xF ≫ pullback.snd _ _ = spMap (algebraMap c.F T) := by
    refine ⟨pullback.lift x (spMap (algebraMap c.F T)) ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [hx]
    simp only [sOf, spMap, ← Spec.map_comp]
    rfl
  obtain ⟨p, j, y₀, hj, hp⟩ := GlobalTheory.Frames.exists_openChart_testRing hS E H Dw l Xo c (xF q)
  obtain ⟨g, hg, hT⟩ := openChart_factor_near_prime E H Dw l Xo c p.R j y₀ hj T xF h2 q hp
  refine ⟨g, hg, ?_⟩
  let lam : T →ₐ[c.F] Localization.Away g := IsScalarTower.toAlgHom c.F T (Localization.Away g)
  obtain ⟨ψ, hψ⟩ := hT (Localization.Away g) lam (IsLocalization.Away.algebraMap_isUnit g)
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c p.R _ ψ y₀
  have hzx : z.x = spMap (algebraMap T (Localization.Away g)) ≫ x := by
    rw [hz.1, ← hj.2.1, ← Category.assoc, ← hψ, Category.assoc, h1]
    rfl
  have key : ∀ x' : Sp (Localization.Away g) ⟶ Xo.X, z.x = x' → ∃ s : LB.Sec (PPx x'), SecGen x' s := by
    rintro _ rfl
    exact ⟨z.s, z.gen⟩
  exact key _ hzx

end GlobalTheory.HeckeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTraceEqFinsumGeometricPointsEtale
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

noncomputable section

namespace GlobalTheory.EtaleTraceGeom

open TensorProduct

theorem exists_eq_eval {K : Type} [Field K] {P : Type} [Fintype P] [DecidableEq P]
    (θ : (P → K) →ₐ[K] K) : ∃ p : P, ∀ z : P → K, θ z = z p := by
  first
  | exact @_root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval
  | exact _root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval
  | (apply _root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval <;> assumption)
  | (intros; apply _root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval ..)

theorem trace_pi_self {K : Type} [Field K] {P : Type} [Fintype P] [DecidableEq P] (z : P → K) :
    Algebra.trace K (P → K) z = ∑ p, z p := by
  let b := Pi.basisFun K P
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Algebra.leftMulMatrix_eq_repr_mul, b, Pi.single_apply]

theorem exists_trace_eq_finsum : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B], Module.Finite R B →
    Algebra.Etale R B → ∀ b : B, ∃ v : R, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : R →+* Ω),
      φ v = ∑ᶠ χ : {χ : B →+* Ω // χ.comp (algebraMap R B) = φ}, χ.1 b := by
  intro R B _ _ _ hfin het b
  classical
  have : Module.FinitePresentation R B := .of_finite_of_finitePresentation R B
  have : Module.Flat R B := inferInstance
  have : Module.Projective R B := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R B
  refine ⟨LinearMap.trace R _ (g ∘ₗ Algebra.lmul R B b ∘ₗ f), fun Ω _ _ φ => ?_⟩
  letI := φ.toAlgebra
  have hφ : algebraMap R Ω = φ := rfl

  have step1 : φ (LinearMap.trace R _ (g ∘ₗ Algebra.lmul R B b ∘ₗ f)) =
      Algebra.trace Ω (Ω ⊗[R] B) (1 ⊗ₜ b) := by
    rw [← hφ, ← LinearMap.trace_baseChange, LinearMap.baseChange_comp, LinearMap.baseChange_comp,
      LinearMap.trace_comp_comm', LinearMap.comp_assoc, ← LinearMap.baseChange_comp, hfg,
      LinearMap.baseChange_id, LinearMap.comp_id, Algebra.trace_apply, Algebra.baseChange_lmul]
  rw [step1]
  set e := Algebra.FormallyEtale.equivPiOfIsSepClosed Ω (Ω ⊗[R] B) with he
  haveI : Module.Finite Ω (PrimeSpectrum (Ω ⊗[R] B) → Ω) := Module.Finite.equiv e.toLinearEquiv
  haveI : IsArtinianRing (Ω ⊗[R] B) := isArtinian_of_tower Ω inferInstance
  haveI : Finite (PrimeSpectrum (Ω ⊗[R] B)) := inferInstance
  haveI : Fintype (PrimeSpectrum (Ω ⊗[R] B)) := Fintype.ofFinite _
  rw [← Algebra.trace_eq_of_algEquiv e, trace_pi_self]
  let S := {χ : B →+* Ω // χ.comp (algebraMap R B) = φ}
  let G : PrimeSpectrum (Ω ⊗[R] B) → (B →ₐ[R] Ω) := fun p =>
    (((Pi.evalAlgHom Ω (fun _ => Ω) p).comp (e : Ω ⊗[R] B →ₐ[Ω] _)).restrictScalars R).comp
      Algebra.TensorProduct.includeRight
  let F : PrimeSpectrum (Ω ⊗[R] B) → S := fun p =>
    ⟨(G p).toRingHom, RingHom.ext fun r => (G p).commutes r⟩
  have hF : ∀ p y, (F p).1 y = e (1 ⊗ₜ y) p := fun p y => rfl
  have hinj : Function.Injective F := by
    intro p q h
    have h' : ∀ y : B, e (1 ⊗ₜ y) p = e (1 ⊗ₜ y) q := fun y => by
      rw [← hF, ← hF, h]
    have h'' : ∀ x, e x p = e x q := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a y =>
        rw [show a ⊗ₜ[R] y = a • (1 ⊗ₜ[R] y : Ω ⊗[R] B) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one], map_smul, Pi.smul_apply,
          Pi.smul_apply, h' y]
      | add x y hx hy => rw [map_add (f := _), Pi.add_apply, Pi.add_apply, hx, hy]
    have := h'' (e.symm (Pi.single p 1))
    rw [e.apply_symm_apply, Pi.single_eq_same] at this
    by_contra hne
    rw [Pi.single_eq_of_ne (Ne.symm hne)] at this
    exact one_ne_zero this
  have hsurj : Function.Surjective F := by
    rintro ⟨χ, hχ⟩
    let χ' : B →ₐ[R] Ω := { χ with commutes' := fun r => RingHom.congr_fun hχ r }
    let ψ : Ω ⊗[R] B →ₐ[Ω] Ω := AlgHom.liftEquiv R Ω B Ω χ'
    obtain ⟨p, hp⟩ := exists_eq_eval (ψ.comp e.symm.toAlgHom)
    refine ⟨p, Subtype.ext (RingHom.ext fun y => ?_)⟩
    rw [hF, ← hp (e (1 ⊗ₜ y))]
    simp [ψ, χ']
  rw [← finsum_comp_equiv (Equiv.ofBijective F ⟨hinj, hsurj⟩), finsum_eq_sum_of_fintype]
  rfl

end GlobalTheory.EtaleTraceGeom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FibreIsogenyPairDefinedOverFiniteSubextension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

open GlobalTheory.Spread

theorem fibre_transition {G X : Scheme.{0}} (p : G ⟶ X) {K L : Type} [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L) (x : Sp K ⟶ X)
    (π : pullback p (spMap (algebraMap K L) ≫ x) ⟶ pullback p (spMap (algebraMap K M) ≫ x))
    (h₁ : π ≫ pullback.fst _ _ = pullback.fst _ _)
    (h₂ : π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap M.val.toRingHom) :
    (pullbackLeftPullbackSndIso p x (spMap (algebraMap K L))).hom ≫ π =
      bcMap (pullback.snd p x) M.val ≫ (pullbackLeftPullbackSndIso p x (spMap (algebraMap K M))).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, h₁, Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
      pullbackLeftPullbackSndIso_hom_fst, bcMap_fst_assoc]
  · rw [Category.assoc, h₂, Category.assoc, pullbackLeftPullbackSndIso_hom_snd,
      pullbackLeftPullbackSndIso_hom_snd_assoc, bcMap_snd]

theorem exists_descend_fibre {G X : Scheme.{0}} (p : G ⟶ X) [QuasiCompact p] [QuasiSeparated p]
    [LocallyOfFinitePresentation p] {K L : Type} [Field K] [Field L] [Algebra K L] (x x' : Sp K ⟶ X)
    (g : pullback p (spMap (algebraMap K L) ≫ x) ⟶ pullback p (spMap (algebraMap K L) ≫ x'))
    (hg : g ≫ pullback.snd _ _ = pullback.snd _ _) :
    ∃ s : Finset L, ∀ M : IntermediateField K L, (s : Set L) ⊆ M →
      ∃ f : pullback p (spMap (algebraMap K M) ≫ x) ⟶ pullback p (spMap (algebraMap K M) ≫ x'),
        f ≫ pullback.snd _ _ = pullback.snd _ _ ∧
        ∀ (π : pullback p (spMap (algebraMap K L) ≫ x) ⟶ pullback p (spMap (algebraMap K M) ≫ x))
          (π' : pullback p (spMap (algebraMap K L) ≫ x') ⟶ pullback p (spMap (algebraMap K M) ≫ x')),
          π ≫ pullback.fst _ _ = pullback.fst _ _ →
          π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap M.val.toRingHom →
          π' ≫ pullback.fst _ _ = pullback.fst _ _ →
          π' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap M.val.toRingHom →
          g ≫ π' = π ≫ f := by
  let A : Over (Sp K) := Over.mk (pullback.snd p x)
  let B : Over (Sp K) := Over.mk (pullback.snd p x')
  have : QuasiCompact A.hom := inferInstanceAs (QuasiCompact (pullback.snd p x))
  have : QuasiSeparated A.hom := inferInstanceAs (QuasiSeparated (pullback.snd p x))
  have : LocallyOfFinitePresentation B.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd p x'))
  let g₀ : pullback (pullback.snd p x) (spMap (algebraMap K L)) ⟶
      pullback (pullback.snd p x') (spMap (algebraMap K L)) :=
    (pullbackLeftPullbackSndIso p x (spMap (algebraMap K L))).hom ≫ g ≫
      (pullbackLeftPullbackSndIso p x' (spMap (algebraMap K L))).inv
  have hg₀ : g₀ ≫ pullback.snd _ _ = pullback.snd _ _ := by
    simp only [g₀, Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd, hg, pullbackLeftPullbackSndIso_hom_snd]
  obtain ⟨s, hs⟩ := HomPairDescent.exists_descend (Ω := L) A B (Over.homMk g₀ hg₀)
  refine ⟨s, fun M hM => ?_⟩
  obtain ⟨f, hf⟩ := hs M hM
  let f₀ : pullback (pullback.snd p x) (spMap (algebraMap K M)) ⟶
      pullback (pullback.snd p x') (spMap (algebraMap K M)) := f.left
  have hf₀ : f₀ ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f
  have hf₁ : bcMap (pullback.snd p x) M.val ≫ f₀ = g₀ ≫ bcMap (pullback.snd p x') M.val := hf
  refine ⟨(pullbackLeftPullbackSndIso p x (spMap (algebraMap K M))).inv ≫ f₀ ≫
      (pullbackLeftPullbackSndIso p x' (spMap (algebraMap K M))).hom, ?_, fun π π' h₁ h₂ h₃ h₄ => ?_⟩
  · simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd, hf₀, pullbackLeftPullbackSndIso_hom_snd]
  · have e := fibre_transition p M x π h₁ h₂
    have e' := fibre_transition p M x' π' h₃ h₄
    rw [← cancel_epi (pullbackLeftPullbackSndIso p x (spMap (algebraMap K L))).hom, reassoc_of% e,
      Iso.hom_inv_id_assoc, reassoc_of% hf₁, ← e']
    simp only [g₀, Category.assoc, Iso.inv_hom_id_assoc]

theorem pair_defined_over_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X) (g : Fib Xo w ⟶ Fib Xo w') (g' : Fib Xo w' ⟶ Fib Xo w), φ.IsIntegral → w = spMap φ ≫ x → w' = spMap φ ≫ x' → IsMonHom g → IsMonHom g' → ∃ (M : Type) (_ : Field M) (i : K →+* M) (j : M →+* L), j.comp i = φ ∧ i.Finite ∧ ∀ v v' : Sp M ⟶ Xo.X, v = spMap i ≫ x → v' = spMap i ≫ x' → ∃ (f : Fib Xo v ⟶ Fib Xo v') (f' : Fib Xo v' ⟶ Fib Xo v), IsBC j f g ∧ IsBC j f' g' := by
  classical
  intro E _ _ _ H Dw l Xo K L _ _ φ x x' w w' g g' hφ hw hw' _ _
  let _ : Algebra K L := φ.toAlgebra
  have hint : Algebra.IsIntegral K L := ⟨hφ⟩
  subst hw hw'
  have hA := ObjDim.isAbelianScheme Xo.univ
  have := hA.proper
  have := hA.smooth
  obtain ⟨s, hs⟩ := exists_descend_fibre Xo.univ.t.G.hom (L := L) x x' g.left (Over.w g)
  obtain ⟨t, ht⟩ := exists_descend_fibre Xo.univ.t.G.hom (L := L) x' x g'.left (Over.w g')
  let M : IntermediateField K L := IntermediateField.adjoin K ((s ∪ t : Finset L) : Set L)
  have hM : ((s ∪ t : Finset L) : Set L) ⊆ M := IntermediateField.subset_adjoin _ _
  obtain ⟨f, hf, hf'⟩ := hs M ((Finset.coe_subset.2 Finset.subset_union_left).trans hM)
  obtain ⟨r, hr, hr'⟩ := ht M ((Finset.coe_subset.2 Finset.subset_union_right).trans hM)
  have hfin : FiniteDimensional K M :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨M, inferInstance, algebraMap K M, M.val.toRingHom, RingHom.ext fun _ => rfl,
    RingHom.finite_algebraMap.2 hfin, ?_⟩
  rintro v v' rfl rfl
  have e : ∀ y : Sp K ⟶ Xo.X, spMap φ ≫ y = spMap M.val.toRingHom ≫ spMap (algebraMap K M) ≫ y := fun y => by
    rw [← Category.assoc, spMap_algHom_comp]
  exact ⟨Over.homMk f hf, Over.homMk r hr, ⟨e x, e x', hf'⟩, ⟨e x', e x, hr'⟩⟩

end GlobalTheory.HkIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteClassesRationalIsometriesBoundedDenominato
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx.QFin

section Lemmas

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem mulVec_mul (g h : GL (Fin r) E) (v : Fin r → E) :
    ((g * h : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v =
      (g : Matrix (Fin r) (Fin r) E) *ᵥ ((h : Matrix (Fin r) (Fin r) E) *ᵥ v) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

theorem mulVec_inv_mulVec (g : GL (Fin r) E) (v : Fin r → E) :
    ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((g : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := by
  rw [← mulVec_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem mulVec_mulVec_inv (g : GL (Fin r) E) (v : Fin r → E) :
    (g : Matrix (Fin r) (Fin r) E) *ᵥ (((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := by
  rw [← mulVec_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

variable {X X' : Data E r} {N : ℕ}

theorem qmatch_stab_mul {a g : GL (Fin r) E} (h : QMatch X X' N a) (hg : IsUStab X'.Gm X'.Λ g) :
    QMatch X X' N (g * a) := by
  refine ⟨h.psi, h.p0, h.xi, fun u v => ?_, fun v hv => ?_, fun w hw => ?_⟩
  · rw [mulVec_mul, mulVec_mul, hg.1, h.iso]
  · rw [mulVec_mul, ← Matrix.mulVec_smul]
    exact (hg.2 _).1 (h.lat v hv)
  · rw [mul_inv_rev, mulVec_mul]
    exact h.lat' _ ((hg.2 _).2 (by rw [mulVec_mulVec_inv]; exact hw))

def InL (X' : Data E r) (N : ℕ) (a : GL (Fin r) E) (v : Fin r → E) : Prop :=
  (N : E)⁻¹ • ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) ∈ X'.Λ

theorem inL_transfer (hN : 0 < N) {a a' : GL (Fin r) E} (h' : QMatch X X' N a')
    (hP : ∀ v ∈ X.Λ, InL X' N a' v → InL X' N a v) {w : Fin r → E} (hw : w ∈ X'.Λ) :
    ((a * a'⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w ∈ X'.Λ := by
  have hN' : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have key : ∀ g : GL (Fin r) E, (N : E)⁻¹ • ((g : Matrix (Fin r) (Fin r) E) *ᵥ
      ((N : E) • (((a'⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w))) =
      (g : Matrix (Fin r) (Fin r) E) *ᵥ (((a'⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) := by
    intro g
    rw [Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hN', one_smul]
  have h1 := hP _ (h'.lat' w hw) (by unfold InL; rw [key, mulVec_mulVec_inv]; exact hw)
  unfold InL at h1
  rw [key] at h1
  rw [mulVec_mul]
  exact h1

theorem isUStab_of_inL (hN : 0 < N) {a a' : GL (Fin r) E} (h : QMatch X X' N a) (h' : QMatch X X' N a')
    (hP : ∀ v ∈ X.Λ, InL X' N a v ↔ InL X' N a' v) : IsUStab X'.Gm X'.Λ (a * a'⁻¹) := by
  refine ⟨fun x y => ?_, fun x => ⟨fun hx => inL_transfer hN h' (fun v hv => (hP v hv).2) hx, fun hx => ?_⟩⟩
  · rw [mulVec_mul, mulVec_mul, h.iso, ← h'.iso, mulVec_mulVec_inv, mulVec_mulVec_inv]
  · have := inL_transfer hN h (fun v hv => (hP v hv).1) hx
    rwa [mulVec_mul, mulVec_mul, mulVec_inv_mulVec, mulVec_mulVec_inv] at this

end Lemmas

theorem finite_reps (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (N : ℕ)
    (hN : 0 < N) : ∃ S : Finset (GL (Fin r) E), (∀ s ∈ S, QMatch X X' N s) ∧
      ∀ a, QMatch X X' N a → ∃ s ∈ S, ∃ b ∈ X'.Γ, a = b * s := by
  classical
  have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  set A := X.Λ.toAddSubgroup
  have hfg : A.FG := by
    haveI : Module.Finite (𝓞 E) X.Λ := Module.Finite.iff_fg.2 X.Λ_fg
    haveI : Module.Finite ℤ X.Λ := Module.Finite.trans (𝓞 E) X.Λ
    exact (AddGroup.fg_iff_addSubgroup_fg _).1 (Module.Finite.iff_addGroup_fg.1 this)
  haveI : AddGroup.FG A := (AddGroup.fg_iff_addSubgroup_fg _).2 hfg
  set K := (nsmulAddMonoidHom (α := A) (N * N)).range
  haveI : K.FiniteIndex := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg A (mul_ne_zero hN.ne' hN.ne')
  haveI : Fintype (Set (A ⧸ K)) := Fintype.ofFinite _
  let f : GL (Fin r) E → Set (A ⧸ K) := fun a =>
    (QuotientAddGroup.mk : A → A ⧸ K) '' {v | InL X' N a (v : Fin r → E)}
  have hf : ∀ a, QMatch X X' N a → ∀ v : A,
      (QuotientAddGroup.mk v : A ⧸ K) ∈ f a ↔ InL X' N a (v : Fin r → E) := by
    intro a ha v
    constructor
    · rintro ⟨v', hv', he⟩
      obtain ⟨u, hu⟩ := QuotientAddGroup.eq.1 he
      have hv : (v : Fin r → E) = (v' : Fin r → E) + ((N : E) * N) • (u : Fin r → E) := by
        have := congrArg (fun z : A => (z : Fin r → E)) hu
        simp only [nsmulAddMonoidHom_apply, AddSubgroup.coe_add, AddSubgroup.coe_neg,
          AddSubgroup.coe_nsmul] at this
        rw [← Nat.cast_mul, Nat.cast_smul_eq_nsmul, this]
        abel
      show InL X' N a (v : Fin r → E)
      have hv'' : InL X' N a (v' : Fin r → E) := hv'
      unfold InL at hv'' ⊢
      rw [hv, Matrix.mulVec_add, Matrix.mulVec_smul, smul_add, smul_smul, ← _root_.mul_assoc,
        inv_mul_cancel₀ hN0, _root_.one_mul]
      exact X'.Λ.add_mem hv'' (ha.lat _ u.2)
    · intro h
      exact ⟨v, h, rfl⟩
  let rep : Set (A ⧸ K) → GL (Fin r) E := fun T =>
    if h : ∃ a, QMatch X X' N a ∧ f a = T then h.choose else 1
  obtain ⟨S0, hS0⟩ := X'.Γ_index
  refine ⟨((Finset.univ ×ˢ S0).image fun p => p.2⁻¹ * rep p.1).filter (QMatch X X' N),
    fun s hs => (Finset.mem_filter.1 hs).2, fun a ha => ?_⟩
  have hex : ∃ a', QMatch X X' N a' ∧ f a' = f a := ⟨a, ha, rfl⟩
  have hrep : rep (f a) = hex.choose := dif_pos hex
  obtain ⟨ha', hfa⟩ := hex.choose_spec
  have hP : ∀ v ∈ X.Λ, InL X' N hex.choose v ↔ InL X' N a v := by
    intro v hv
    rw [← hf _ ha' ⟨v, hv⟩, ← hf a ha ⟨v, hv⟩, hfa]
  obtain ⟨s, hs, hsΓ⟩ := hS0 _ (isUStab_of_inL hN ha' ha hP)
  have hq := qmatch_stab_mul ha (X'.Γ_stab _ hsΓ)
  have e : s⁻¹ * (hex.choose * a⁻¹) * a = s⁻¹ * hex.choose := by group
  rw [e] at hq
  refine ⟨s⁻¹ * hex.choose, Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨(f a, s),
    Finset.mem_product.2 ⟨Finset.mem_univ _, hs⟩, ?_⟩, hq⟩, (s⁻¹ * (hex.choose * a⁻¹))⁻¹,
    X'.Γ.inv_mem hsΓ, by group⟩
  show s⁻¹ * rep (f a) = s⁻¹ * hex.choose
  rw [hrep]

end GlobalTheory.HeckeEx.QFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionThetaMatrixCoeffRationalTranslatStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierInversion_thetaMatrixCoeff_rationalTranslates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f f₀ : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ → ∀ w x : WO S T, Summable (fun γ : ratL T S => ‖thPair μ 𝓕 f (heisO ψ S T ((γ : WO S T) + w) f₀)‖) → ∑' γ : ratL T S, thPair μ 𝓕 f (heisO ψ S T ((γ : WO S T) + w) f₀) * heisO ψ S T ((γ : WO S T) + w) f₀ x = f x * star (heisO ψ S T w f₀ x) * heisO ψ S T w f₀ x := by
  first | exact @GlobalTheory.TranslateCoefInversion.sum_coef_mul_translate | exact GlobalTheory.TranslateCoefInversion.sum_coef_mul_translate | (intros; apply GlobalTheory.TranslateCoefInversion.sum_coef_mul_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodTypesOfTypesTrue
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LiftRows.Inh
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem goodTypes_of_typesTrue (hL : R.toLevCh.Is A.μ0) (h : GlobalTheory.Mem.Top.TypesTrue D.ntypes R.C.P R.C.W) :
    GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R := by
  intro k
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  refine ⟨_, (h.teich k).symm, h.ser k, fun v j PP hPP a u ha hu => Or.inl ?_⟩
  have hl := h.isCharLab k v j
  have hp := D.host.g_prime k
  have ha0 : (a : Formalism.CyclotomicNorms.Fbar (D.host.g k)) ≠ 0 := by
    rw [ha]; intro h0
    have := (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen_order 1 one_pos
    rw [h0, pow_one] at this
    have h2 := hp.two_le
    have h3 : orderOf (0 : Formalism.CyclotomicNorms.Fbar (D.host.g k)) = 0 := orderOf_eq_zero_iff'.2 fun n hn => by simp [hn.ne']
    omega
  have hcop : a.Coprime (D.host.g k) := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hd
    exact ha0 ((CharP.cast_eq_zero_iff _ (D.host.g k) a).2 hd)
  have han : a ≠ 0 := by rintro rfl; exact ha0 (by simp)
  have h1 := hl.2 (ZMod.unitOfCoprime a hcop) (by rw [ZMod.coe_unitOfCoprime, map_natCast, ha])
  rw [← h1]
  have hE : (a : D.host.E) ≠ 0 := by exact_mod_cast han
  have h2 := (R.C.isMu0 j).atg k PP hPP a hcop (Units.mk0 _ hE) rfl
  have h3 := hL.chi j PP ((hL.Pg PP).2 ⟨k, hPP⟩) (a : 𝓞 D.host.E) (Units.mk0 _ hE) u (by simp) (by rw [hu, map_natCast])
  rw [h2, MonoidHom.inv_apply, _root_.inv_inj] at h3
  rw [h3, MonoidHom.pow_apply]

end GlobalTheory.LiftRows.Inh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridConjugationWeilDataInverseCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.Asc

theorem conjRead_holds : ConjRead := GlobalTheory.Asc.FamilyModel.conjRead

end GlobalTheory.Asc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfBlockSumExistsInverseIntegralSplitPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfBlockSum_exists_inverse_integral_splitPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl (F := F)) (π : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b : GL (Fin d) (Fv F v)),
  (∀ a : AF F, π (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) →
  ∀ (g : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (v.adicCompletionIntegers F)),
  G.map (fun x => (x : Fv F v)) = Matrix.fromBlocks (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₁₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₁₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v)))
      (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₂₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₂₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) →
  ∀ X : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F),
  IsUnit (G.toBlocks₁₁ + G.toBlocks₁₂ + G.toBlocks₂₁ + G.toBlocks₂₂ +
    X * (G.toBlocks₁₁ + G.toBlocks₁₂ - G.toBlocks₂₁ - G.toBlocks₂₂)).det →
  ∀ Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), Y.map π = (b : Matrix (Fin d) (Fin d) (Fv F v)) * X.map (fun x => (x : Fv F v)) * ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) →
  ∃ N : Matrix (Fin d) (Fin d) (Fv F v), N * (⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ + (g).toBlocks₂₁ + (g).toBlocks₂₂) +
      Y * (⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ - (g).toBlocks₂₁ - (g).toBlocks₂₂))).map π = 1 ∧ (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * N * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) := by
  first | exact @GlobalTheory.Twist.halfBlockSum_inv_conj_integral | exact GlobalTheory.Twist.halfBlockSum_inv_conj_integral | (intros; apply GlobalTheory.Twist.halfBlockSum_inv_conj_integral <;> assumption)
end

