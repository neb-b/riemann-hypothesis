module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0251
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0250
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0244
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.QcohLocal
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.RedMk
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import GroundTheory.AutomorphicForms.Bundle0024

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemRestrictionSubobject
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.ImageOpen

lemma secs_mk {X : Scheme.{0}} {E F : X.Modules} (m : F ⟶ E) [Mono m] (W : X.Opens) :
    secs (Subobject.mk m) W = Set.range (m.app W) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    refine ⟨(Subobject.underlyingIso m).hom.app W x, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Subobject.underlyingIso_hom_comp_eq_mk]
  · rintro _ ⟨x, rfl⟩
    refine ⟨(Subobject.underlyingIso m).inv.app W x, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Subobject.underlyingIso_arrow]

lemma isQuasicoherent_image {X : Scheme.{0}} {F E : X.Modules} [F.IsQuasicoherent]
    [E.IsQuasicoherent] (g : F ⟶ E) :
    ((Subobject.mk (kernel.ι (cokernel.π g)) : Subobject E) : X.Modules).IsQuasicoherent :=
  haveI := isQuasicoherent_kernel (cokernel.π g)
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Subobject.underlyingIso (kernel.ι (cokernel.π g))).symm inferInstance

lemma secs_image {X : Scheme.{0}} {F E : X.Modules} [F.IsQuasicoherent]
    [E.IsQuasicoherent] (g : F ⟶ E) (W : X.Opens) (hW : IsAffineOpen W) :
    secs (Subobject.mk (kernel.ι (cokernel.π g))) W = Set.range (g.app W) := by
  rw [secs_mk]
  haveI := isQuasicoherent_kernel (cokernel.π g)
  have hs : Function.Surjective ((Abelian.factorThruImage g).app W) :=
    GlobalTheory.QCoh.app_surjective_of_epi_of_isAffineOpen (Abelian.factorThruImage g) hW
  have h : ∀ y, (kernel.ι (cokernel.π g)).app W ((Abelian.factorThruImage g).app W y) =
      g.app W y := fun y => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app]
    exact congrArg (fun φ : F ⟶ E => φ.app W y) (Abelian.image.fac g)
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hs x
    exact ⟨y, (h y).symm⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨(Abelian.factorThruImage g).app W x, h x⟩

end GlobalTheory.CompanionTheory.GE.ImageOpen

namespace GlobalTheory.CompanionTheory.GE.ImageOpen

attribute [local instance] algebraOfOver

lemma toFunctions_open {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] (O : X.Opens) :
    letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩
    ∀ (U : (O : Scheme.{0}).Opens) (r : A),
      (O.ι.appIso U).hom (toFunctions (A := A) (O.ι ''ᵁ U) r) = toFunctions (A := A) U r := by
  intro U r
  change (O.ι.appIso U).hom (X.presheaf.map (homOfLE le_top).op
      ((X ↘ Spec (.of A)).appTop ((Scheme.ΓSpecIso (.of A)).inv r))) =
    (O : Scheme.{0}).presheaf.map (homOfLE le_top).op
      ((O.ι ≫ (X ↘ Spec (.of A))).appTop ((Scheme.ΓSpecIso (.of A)).inv r))
  rw [Scheme.Hom.comp_appTop]
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
  rfl

end GlobalTheory.CompanionTheory.GE.ImageOpen

namespace GlobalTheory.CompanionTheory.GE.ImageOpen

lemma map_mem_secs_powSub {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] (O : X.Opens) :
    letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩
    ∀ {P : X.Modules} {E : (O : Scheme.{0}).Modules}, P.IsQuasicoherent → E.IsQuasicoherent →
      ∀ (f : P.restrict O.ι ⟶ E) (n : ℕ) (U : (O : Scheme.{0}).Opens), IsAffineOpen U →
      ∀ x : Γ(P, O.ι ''ᵁ U), x ∈ secs (powSub I P n) (O.ι ''ᵁ U) →
        f.app U ((P.restrictAppIso O.ι U).inv x) ∈ secs (powSub I E n) U := by
  letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩
  intro P E hP hE f n U hU x hx
  have hU' : IsAffineOpen (O.ι ''ᵁ U) := hU.image_of_isOpenImmersion O.ι
  rw [secs_powSub I P hP n _ hU'] at hx
  rw [secs_powSub I E hE n U hU]
  have hmul : ∀ (a : Γ(X, O.ι ''ᵁ U)) (m : Γ(P, O.ι ''ᵁ U)),
      f.app U ((P.restrictAppIso O.ι U).inv (a • m)) =
        (O.ι.appIso U).hom a • f.app U ((P.restrictAppIso O.ι U).inv m) := by
    intro a m
    rw [Scheme.Modules.smul_restrictAppIso_inv_apply, Scheme.Modules.Hom.app_smul]
  have hJ : ∀ a ∈ Ideal.map (toFunctions (A := A) (O.ι ''ᵁ U)) (I ^ n),
      (O.ι.appIso U).hom a ∈ Ideal.map (toFunctions (A := A) U) (I ^ n) := by
    intro a ha
    have := Ideal.mem_map_of_mem (O.ι.appIso U).hom.hom ha
    rw [Ideal.map_map] at this
    convert this using 2
    ext r
    exact (toFunctions_open O U r).symm
  change x ∈ (Ideal.map (toFunctions (A := A) (O.ι ''ᵁ U)) (I ^ n) • ⊤ :
    Submodule Γ(X, O.ι ''ᵁ U) Γ(P, O.ι ''ᵁ U)) at hx
  refine Submodule.smul_induction_on
    (p := fun x => f.app U ((P.restrictAppIso O.ι U).inv x) ∈
      (Ideal.map (toFunctions (A := A) U) (I ^ n) • ⊤ : Submodule Γ((O : Scheme.{0}), U) Γ(E, U)))
    hx ?_ ?_
  · intro a ha m _
    show _ ∈ _
    rw [hmul]
    exact Submodule.smul_mem_smul (hJ a ha) Submodule.mem_top
  · intro y z hy hz
    show _ ∈ _
    rw [map_add (f := _), map_add (f := _)]
    exact Submodule.add_mem _ hy hz

end GlobalTheory.CompanionTheory.GE.ImageOpen

namespace GlobalTheory.CompanionTheory.GE.ImageOpen

lemma isQuasicoherent_powSub {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {Y : Scheme.{0}} [Y.Over (Spec (.of A))] (M : Y.Modules) [M.IsQuasicoherent] (n : ℕ) :
    ((powSub I M (n + 1) : Subobject M) : Y.Modules).IsQuasicoherent :=
  (closedSys_pow I M).qcoh n

theorem image_on_open : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (O : X.Opens), letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩; ∀ {P : X.Modules} {E : (O : Scheme.{0}).Modules}, IsCoherent P → IsCoherent E → ∀ f : P.restrict O.ι ⟶ E, Epi f → ∀ S : ℕ → Subobject E, ClosedSys I E S → ∀ Sb : ℕ → Subobject P, (∀ e (W : (O : Scheme.{0}).Opens), IsAffineOpen W → ∀ x : Γ(P, O.ι ''ᵁ W), x ∈ secs (Sb e) (O.ι ''ᵁ W) ↔ f.app W ((P.restrictAppIso O.ι W).inv x) ∈ secs (S e) W) → ∀ Bb : Subobject P, (Bb : X.Modules).IsQuasicoherent → (∀ e, Bb ⊔ powSub I P (e + 1) = Sb e) → ∃ B : Subobject E, (B : (O : Scheme.{0}).Modules).IsQuasicoherent ∧ (∀ e, B ⊔ powSub I E (e + 1) = S e) ∧ ∀ (W : (O : Scheme.{0}).Opens), IsAffineOpen W → secs B W = (fun x => f.app W ((P.restrictAppIso O.ι W).inv x)) '' secs Bb (O.ι ''ᵁ W) := by
  intro A _ _ I X _ _ O
  letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩
  intro P E hP hE f hf S hS Sb hSb Bb hBb hBS
  haveI := hP.1
  haveI := hE.1
  haveI : (Bb : X.Modules).IsQuasicoherent := hBb
  haveI : Epi f := hf
  haveI : ((Bb : X.Modules).restrict O.ι).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  haveI : (P.restrict O.ι).IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  let g : (Bb : X.Modules).restrict O.ι ⟶ E := (Scheme.Modules.restrictFunctor O.ι).map Bb.arrow ≫ f
  let B : Subobject E := Subobject.mk (kernel.ι (cokernel.π g))
  have hBq : (B : (O : Scheme.{0}).Modules).IsQuasicoherent := isQuasicoherent_image g
  have hsecs : ∀ (W : (O : Scheme.{0}).Opens), IsAffineOpen W → secs B W =
      (fun x => f.app W ((P.restrictAppIso O.ι W).inv x)) '' secs Bb (O.ι ''ᵁ W) := by
    intro W hW
    rw [secs_image g W hW]
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨Bb.arrow.app _ z, ⟨z, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
  refine ⟨B, hBq, fun e => ?_, hsecs⟩
  have hBle : Bb ≤ Sb e := hBS e ▸ le_sup_left
  apply le_antisymm
  · refine sup_le ?_ (hS.pow_le e)
    rw [le_iff_secs_subset]
    rintro ⟨W, hW⟩ y hy
    rw [hsecs W hW] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx' : x ∈ secs (Sb e) (O.ι ''ᵁ W) :=
      (le_iff_secs_subset _ _).1 hBle ⟨_, hW.image_of_isOpenImmersion O.ι⟩ hx
    exact (hSb e W hW x).1 hx'
  · rw [le_iff_secs_subset]
    rintro ⟨W, hW⟩ y hy
    change y ∈ secs (S e) W at hy
    change y ∈ secs (B ⊔ powSub I E (e + 1)) W
    have hW' : IsAffineOpen (O.ι ''ᵁ W) := hW.image_of_isOpenImmersion O.ι
    rw [(supsecs hE.1 B (powSub I E (e + 1)) hBq (isQuasicoherent_powSub I E e)).2 W hW]
    obtain ⟨z, rfl⟩ := GlobalTheory.QCoh.app_surjective_of_epi_of_isAffineOpen f hW y
    have hx : (P.restrictAppIso O.ι W).hom z ∈ secs (Sb e) (O.ι ''ᵁ W) := (hSb e W hW _).2 hy
    rw [← hBS e, (supsecs hP.1 Bb (powSub I P (e + 1)) hBb (isQuasicoherent_powSub I P e)).2 _ hW']
      at hx
    obtain ⟨s, hs, t, ht, hst⟩ := hx
    refine ⟨f.app W ((P.restrictAppIso O.ι W).inv s), (hsecs W hW).symm ▸ ⟨s, hs, rfl⟩,
      f.app W ((P.restrictAppIso O.ι W).inv t),
      map_mem_secs_powSub I O hP.1 hE.1 f (e + 1) W hW t ht, ?_⟩
    rw [← map_add (f := _), ← map_add (f := _), ← hst]
    rfl

end GlobalTheory.CompanionTheory.GE.ImageOpen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompareQuotientBijective
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsQ

namespace GlobalTheory.CompanionTheory.LsCmp

theorem cmpq_bijective (R : Type) [CommRing R] (C : Type 1) [Category.{0} C]
    (A : C ⥤ CommAlgCat.{0} R) (l n i : ℕ) : Function.Bijective ((cmpq A l n).f i) := by
  have hmk := cmpq_mk A l n i
  constructor
  · rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [hmk] at hq
    rw [Submodule.Quotient.mk_eq_zero]
    have hy : ∀ s : ComposableArrows C i, ∃ a : ↑(A.obj (s.obj (Fin.last i))),
        a * algebraMap R ↑(A.obj (s.obj (Fin.last i))) ((l : R) ^ n) = y s := by
      intro s
      have h1 : ((qM A l n).pullC i y) s = 0 := by
        rw [hq]
        rfl
      have h2 : Ideal.Quotient.mk (Ideal.span {algebraMap R ↑(A.obj (s.obj (Fin.last i))) ((l : R) ^ n)}) (y s) = 0 :=
        congrArg Subtype.val h1
      exact Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h2)
    choose a ha using hy
    rw [CrystallineSemistableComparison.Ls.lpow, LinearMap.mem_range]
    refine ⟨a, ?_⟩
    funext s
    show ((l : R) ^ n) • a s = y s
    rw [Algebra.smul_def, mul_comm]
    exact ha s
  · intro g
    have hx : ∀ s : ComposableArrows C i, ∃ x : ↑(A.obj (s.obj (Fin.last i))),
        Ideal.Quotient.mk (Ideal.span {algebraMap R ↑(A.obj (s.obj (Fin.last i))) ((l : R) ^ n)}) x =
          Subtype.val (g s) := fun s => Ideal.Quotient.mk_surjective _
    choose x hx using hx
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    rw [hmk]
    funext s
    apply Subtype.ext
    exact hx s

end GlobalTheory.CompanionTheory.LsCmp

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegBasisOfDegBasisG
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DegreeBasis

theorem degBasis_of_degBasisG : DegBasisG → DegBasis := by
  intro h E _ _ _ n k x M hM
  rw [← degG_eq x M]
  exact h E n (Fin k) x M hM

end GlobalTheory.CompanionTheory.DegreeBasis
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeBasisGeneral
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DegBasisGen

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

theorem ultra (w : HeightOneSpectrum (𝓞 E)) : IsUltrametricDist (w.adicCompletion E) :=
  inferInstanceAs (@IsUltrametricDist (w.adicCompletion E)
    (Valued.toNormedField (w.adicCompletion E) (WithZero (Multiplicative ℤ))).toDist)

theorem exists_left_inv {K ι κ : Type} [Field K] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (P : Matrix ι κ K) (hP : LinearIndependent K Pᵀ) : ∃ Y : Matrix κ ι K, Y * P = 1 := by
  have inj : LinearMap.ker P.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have h0 := hv
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_eq_sum] at h0
    simp only [op_smul_eq_smul] at h0
    funext i
    exact Fintype.linearIndependent_iff.1 hP v h0 i
  obtain ⟨f, hf⟩ := P.mulVecLin.exists_leftInverse_of_injective inj
  refine ⟨LinearMap.toMatrix' f, ?_⟩
  have h := congrArg LinearMap.toMatrix' hf
  rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin',
    LinearMap.toMatrix'_id] at h

theorem degG_reindex (hF : WedgeF) (hI : WedgeI) {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ']
    [DecidableEq κ'] (e : κ' ≃ κ) (x : GA E n) (M : Matrix (Fin n) κ E) :
    degG x (M.submatrix id e) = degG x M := by
  have hfr : (x⁻¹ : GA E n).val * (M.submatrix id e).map (algebraMap E (Ad E)) =
      ((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E))).submatrix id e := by
    ext i j
    simp [Matrix.mul_apply]
  obtain ⟨A, hA⟩ : ∃ A, A = (x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E)) := ⟨_, rfl⟩
  have hv : ∀ v, nI ((A.submatrix id e).map (cV v)) = nI (A.map (cV v)) := fun v => by
    rw [← Matrix.submatrix_map]
    exact (hI (Fin n)).reindex κ κ' e (A.map (cV v))
  have hw : ∀ w, nF ((A.submatrix id e).map (cW w)) = nF (A.map (cW w)) := fun w => by
    haveI := ultra w
    rw [← Matrix.submatrix_map]
    exact (hF (w.adicCompletion E) (Fin n)).reindex κ κ' e (A.map (cW w))
  simp only [degG, hfr, ← hA, hv, hw]

theorem degG_mul (mF : MulF) (mI : MulI) (lg : LogAbsBasic) (fs : FinSupp) {κ : Type} [Fintype κ] [DecidableEq κ]
    (x : GA E n) (P : Matrix (Fin n) κ E) (hP : LinearIndependent E Pᵀ) (s : Matrix κ κ E) (hs : s.det ≠ 0) :
    degG x (P * s) = degG x P := by
  obtain ⟨A, hA⟩ : ∃ A, A = (x⁻¹ : GA E n).val * P.map (algebraMap E (Ad E)) := ⟨_, rfl⟩
  have hfr : (x⁻¹ : GA E n).val * (P * s).map (algebraMap E (Ad E)) = A * s.map (algebraMap E (Ad E)) := by
    rw [hA, Matrix.map_mul, Matrix.mul_assoc]
  obtain ⟨Y₀, hY₀⟩ := exists_left_inv P hP
  have hYA : (Y₀.map (algebraMap E (Ad E)) * x.val) * A = 1 := by
    rw [hA, Matrix.mul_assoc, ← Matrix.mul_assoc x.val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul, ← Matrix.map_mul, hY₀, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨h1, h2, h3⟩ := (lg E).1, (lg E).2.1, (lg E).2.2
  obtain ⟨f1, f2, f3⟩ := fs E (Fin n) κ A _ hYA
  have hu : IsUnit (algebraMap E (Ad E) s.det) := (IsUnit.mk0 _ hs).map _
  have hdet : ∀ {R : Type} [CommRing R] (f : Ad E →+* R),
      ((s.map (algebraMap E (Ad E))).map f).det = f (algebraMap E (Ad E) s.det) := fun f => by
    rw [RingHom.map_det, RingHom.map_det]
    rfl
  have hv : ∀ v, Real.log (nI ((A * s.map (algebraMap E (Ad E))).map (cV v))) =
      Real.log (nI (A.map (cV v))) + Real.log (‖cV v (algebraMap E (Ad E) s.det)‖ ^ 2) := fun v => by
    have hne : ‖cV v (algebraMap E (Ad E) s.det)‖ ^ 2 ≠ 0 :=
      pow_ne_zero _ (norm_ne_zero_iff.2 (hu.map (cV v)).ne_zero)
    rw [Matrix.map_mul, (mI (Fin n) (Fin n) κ _).2.1, hdet, Real.log_mul (f1 v) hne]
  have hw : ∀ w, Real.log (nF ((A * s.map (algebraMap E (Ad E))).map (cW w))) =
      Real.log (nF (A.map (cW w))) + Real.log ‖cW w (algebraMap E (Ad E) s.det)‖ := fun w => by
    haveI := ultra w
    have hne : ‖cW w (algebraMap E (Ad E) s.det)‖ ≠ 0 := norm_ne_zero_iff.2 (hu.map (cW w)).ne_zero
    rw [Matrix.map_mul, (mF _ (Fin n) (Fin n) κ _).2.1, hdet, Real.log_mul (f2 w) hne]
  have hsupp : (Function.support fun w => Real.log (nF (A.map (cW w)))).Finite :=
    f3.subset fun w hw' h => hw' (by simp [h])
  have hprod := h3 s.det hs
  simp only [degG, hfr, ← hA, hv, hw]
  rw [Finset.sum_add_distrib, finsum_add_distrib hsupp (h1 _ hu)]
  unfold logAbs at hprod
  linarith

theorem degBasisG_of : WedgeF → WedgeI → MulF → MulI → LogAbsBasic → FinSupp → DegBasisG := by
  intro hF hI mF mI lg fs E _ _ _ n κ _ _ x M hM
  obtain ⟨W, hW⟩ : ∃ W, W = Submodule.span E (Set.range Mᵀ) := ⟨_, rfl⟩
  rw [← hW]
  have hcard : Module.finrank E W = Fintype.card κ := by
    rw [hW]
    exact finrank_span_eq_card hM
  have hsub : ∀ k, (fun i => M i k) ∈ W := fun k => by
    rw [hW]
    exact Submodule.subset_span ⟨k, rfl⟩
  let e : Fin (Module.finrank E W) ≃ κ := (Fintype.equivFinOfCardEq hcard.symm).symm
  have hcol : ∀ j, (fun i => M i (e j)) ∈ W := fun j => hsub (e j)
  let b := Module.finBasis E W
  let s : Matrix (Fin (Module.finrank E W)) (Fin (Module.finrank E W)) E :=
    Matrix.of fun i j => b.repr ⟨fun i' => M i' (e j), hcol j⟩ i
  have hfac : M.submatrix id e = basisMat W * s := by
    ext i j
    have h := congrArg (fun y : W => (y : Fin n → E) i) (b.sum_repr ⟨fun i' => M i' (e j), hcol j⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h
    simp only [Matrix.mul_apply, basisMat, Matrix.of_apply, Matrix.submatrix_apply, id, s]
    rw [← h]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hlin : LinearIndependent E (M.submatrix id e)ᵀ := hM.comp e e.injective
  have hs : s.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have h1 : M.submatrix id e *ᵥ v = 0 := by
      rw [hfac, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
    rw [Matrix.mulVec_eq_sum] at h1
    simp only [op_smul_eq_smul] at h1
    exact hv0 (funext fun i => Fintype.linearIndependent_iff.1 hlin v h1 i)
  have hP : LinearIndependent E (basisMat W)ᵀ :=
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  calc degG x M = degG x (M.submatrix id e) := (degG_reindex hF hI e x M).symm
    _ = degG x (basisMat W * s) := by rw [hfac]
    _ = degG x (basisMat W) := degG_mul mF mI lg fs x _ hP s hs
    _ = deg x W := rfl

end GlobalTheory.CompanionTheory.DegBasisGen

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeRationalSubspace
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.Degree

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

theorem basisMat_transpose_eq (W : Submodule E (Fin n → E)) :
    ((basisMat W)ᵀ : Fin (Module.finrank E W) → Fin n → E) =
      W.subtype ∘ (Module.finBasis E W) := by
  funext j i
  rfl

theorem basisMat_linearIndependent (W : Submodule E (Fin n → E)) :
    LinearIndependent E (basisMat W)ᵀ := by
  rw [basisMat_transpose_eq]
  exact (Module.finBasis E W).linearIndependent.map' W.subtype W.ker_subtype

theorem span_basisMat (W : Submodule E (Fin n → E)) :
    Submodule.span E (Set.range (basisMat W)ᵀ) = W := by
  rw [basisMat_transpose_eq, Set.range_comp, ← Submodule.map_span, (Module.finBasis E W).span_eq,
    Submodule.map_top, Submodule.range_subtype]

theorem mul_transpose_apply {κ : Type} [Fintype κ] (g : GL (Fin n) E) (M : Matrix (Fin n) κ E) (j : κ) :
    (g.val * M)ᵀ j = Matrix.toLin' g.val (Mᵀ j) := by
  funext i
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem ker_toLin'_eq_bot (g : GL (Fin n) E) : LinearMap.ker (Matrix.toLin' g.val) = ⊥ := by
  refine LinearMap.ker_eq_bot.2 fun a b hab => ?_
  have h := congrArg (Matrix.toLin' (g⁻¹ : GL (Fin n) E).val) hab
  simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using h

theorem frame_rat {κ : Type} [Fintype κ] (x : GA E n) (g : GL (Fin n) E) (M : Matrix (Fin n) κ E) :
    ((ratGL E n g * x)⁻¹ : GA E n).val * (g.val * M).map (algebraMap E (Ad E)) =
      (x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E)) := by
  have hr : (g.val * M).map (algebraMap E (Ad E)) =
      (ratGL E n g).val * M.map (algebraMap E (Ad E)) := by
    rw [Matrix.map_mul]
    rfl
  rw [hr, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (ratGL E n g)⁻¹.val,
    Units.inv_mul, Matrix.one_mul]

theorem degG_rat {κ : Type} [Fintype κ] [DecidableEq κ] (x : GA E n) (g : GL (Fin n) E)
    (M : Matrix (Fin n) κ E) : degG (ratGL E n g * x) (g.val * M) = degG x M := by
  simp only [degG, frame_rat]

theorem degRat_of_degBasisG : DegBasisG → DegRat := by
  intro h E _ _ _ n x g W
  have hli : LinearIndependent E (g.val * basisMat W)ᵀ := by
    have e : (fun j => (g.val * basisMat W)ᵀ j) = Matrix.toLin' g.val ∘ fun j => (basisMat W)ᵀ j :=
      funext (mul_transpose_apply g (basisMat W))
    have l : LinearIndependent E (fun j => (g.val * basisMat W)ᵀ j) :=
      e ▸ (basisMat_linearIndependent W).map' _ (ker_toLin'_eq_bot g)
    exact l
  have hspan : Submodule.span E (Set.range (g.val * basisMat W)ᵀ) = img g W := by
    have e : Set.range (g.val * basisMat W)ᵀ = Matrix.toLin' g.val '' Set.range (basisMat W)ᵀ :=
      Set.ext fun y => ⟨fun ⟨j, hj⟩ => ⟨(basisMat W)ᵀ j, ⟨j, rfl⟩,
          (mul_transpose_apply g (basisMat W) j).symm.trans hj⟩,
        fun ⟨_, ⟨j, hj⟩, hy⟩ => ⟨j, (mul_transpose_apply g (basisMat W) j).trans (hj ▸ hy)⟩⟩
    rw [e, ← Submodule.map_span, span_basisMat]
    rfl
  have key := h E n (Fin (Module.finrank E W)) (ratGL E n g * x) (g.val * basisMat W) hli
  rw [hspan] at key
  rw [← key, degG_rat]
  rfl

end GlobalTheory.CompanionTheory.Degree

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictBlockOrder
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.Twist

theorem exists_nat_labelling_blk : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N), ∃ β : Fin N → ℕ, ∀ x y, β x < β y ↔ blk e x < blk e y := by
  intro α _ _ N m _ _ e
  let o := (Fintype.orderIsoFinOfCardEq α rfl).symm
  refine ⟨fun x => (o (blk e x)).val, fun x y => ?_⟩
  exact Fin.lt_def.symm.trans (OrderIso.lt_iff_lt o)

end GlobalTheory.CompanionTheory.Twist
end

