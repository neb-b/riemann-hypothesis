module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormMulLeOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPosIsGreatestNormMulVecOnKer
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightSpaceIrreducibleResidue
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolAVDescendsToCountableSubfield
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PolCountableDescent

theorem countable_closure {K : Type} [Field K] (s : Finset K) :
    Countable (Subfield.closure (s : Set K)) := by
  rw [← Cardinal.mk_le_aleph0_iff]
  refine (Subfield.cardinalMk_closure_le_max _).trans ?_
  exact max_le (Cardinal.mk_le_aleph0_iff.2 s.countable_toSet.to_subtype) le_rfl

theorem subset_closure_of_subset {K : Type} [Field K] {s s' : Finset K} (h : s ⊆ s') :
    (s : Set K) ⊆ Subfield.closure (s' : Set K) :=
  fun _ hx => Subfield.subset_closure (h hx)

theorem spMap_subtype_comp {K : Type} [Field K] {K₀ K₁ : Subfield K} (h : K₀ ≤ K₁) :
    spMap K₁.subtype ≫ spMap (Subfield.inclusion h) = spMap K₀.subtype := by
  rw [← Spec.map_comp]; rfl

theorem polAV_descends_to_countable_subfield :
    ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (J I : Type) [Finite J] [Finite I] (a : J → (P.A ⟶ P.A)) (x : I → (𝟙_ (Over (Sp K)) ⟶ P.A)), ∃ (K₀ : Subfield K) (P₀ : PolAV (Sp K₀)) (Φ : P.A.left ⟶ P₀.A.left) (a₀ : J → (P₀.A ⟶ P₀.A)) (x₀ : I → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A)), Countable K₀ ∧ IsGrpPullback P.A P₀.A (spMap K₀.subtype) Φ ∧ LBIso P.L (P₀.L.pull Φ) ∧ (∀ j, (a j).left ≫ Φ = Φ ≫ (a₀ j).left) ∧ ∀ i, (x i).left ≫ Φ = spMap K₀.subtype ≫ (x₀ i).left := by
  intro K _ P J I _ _ a x
  classical
  obtain ⟨s₀, H₀⟩ := GlobalTheory.exists_finset_isProjOver_descends K ⊥ P.A.left P.A.hom
    (GlobalTheory.ProjSpace.isProjOver_of_relAmple P.ample)
  let K₀ : Subfield K := Subfield.closure (s₀ : Set K)
  obtain ⟨X₀, p₀, φ, hp₀, sq⟩ := H₀ K₀ bot_le Subfield.subset_closure
  have : IsProper p₀ := by
    obtain ⟨N, i, hi, rfl⟩ := hp₀
    have := isProper_str K₀ N
    infer_instance
  have : LocallyOfFinitePresentation p₀ := inferInstance
  have : QuasiCompact (Over.mk p₀).hom := inferInstanceAs (QuasiCompact p₀)
  have : QuasiSeparated (Over.mk p₀).hom := inferInstanceAs (QuasiSeparated p₀)
  have : LocallyOfFinitePresentation (Over.mk p₀).hom := inferInstanceAs (LocallyOfFinitePresentation p₀)
  obtain ⟨s₁, H₁⟩ := GlobalTheory.grpObj_descends_to_large_subfield K K₀ (Over.mk p₀) P.A φ sq
  obtain ⟨s₂, H₂⟩ := GlobalTheory.LBDescent.exists_lb_subfield K K₀ X₀ P.A.left p₀ P.A.hom φ P.L P.isLB sq
  obtain ⟨s₃, H₃⟩ := GlobalTheory.morphisms_descend_to_large_subfield K K₀ X₀ P.A.left p₀ P.A.hom φ X₀ p₀ J
    (fun j => (a j).left ≫ φ) sq
    (fun j => by rw [Category.assoc, sq.w, ← Category.assoc, Over.w])
  obtain ⟨s₄, H₄⟩ := GlobalTheory.morphisms_descend_to_large_subfield K K₀ (Sp K₀) (Sp K) (𝟙 _) (𝟙 _)
    (spMap K₀.subtype) X₀ p₀ I (fun i => (x i).left ≫ φ) (IsPullback.of_vert_isIso ⟨by simp⟩)
    (fun i => by
      have e : (x i).left ≫ P.A.hom = 𝟙 _ := Over.w (x i)
      rw [Category.assoc, sq.w, ← Category.assoc, e]; simp)
  let s : Finset K := s₀ ∪ s₁ ∪ s₂ ∪ s₃ ∪ s₄
  let K₁ : Subfield K := Subfield.closure (s : Set K)
  have h : K₀ ≤ K₁ := Subfield.closure_mono (Finset.coe_subset.2 (fun y hy => by simp [s, hy]))
  let inc := spMap (Subfield.inclusion h)
  let A₁ : Over (Sp K₁) := Over.mk (pullback.snd p₀ inc)
  let φ₁ : A₁.left ⟶ X₀ := pullback.fst p₀ inc
  have sq₁ : IsPullback φ₁ A₁.hom p₀ inc := IsPullback.of_hasPullback p₀ inc
  let ψ : P.A.left ⟶ A₁.left := sq₁.lift φ (P.A.hom ≫ spMap K₁.subtype)
    (by rw [Category.assoc, spMap_subtype_comp h, sq.w])
  have hψ₁ : ψ ≫ φ₁ = φ := sq₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = P.A.hom ≫ spMap K₁.subtype := sq₁.lift_snd _ _ _
  obtain ⟨gr₁, hG⟩ := H₁ K₁ h (subset_closure_of_subset (fun y hy => by simp [s, hy])) A₁ φ₁ ψ sq₁ hψ₁ hψ₂
  obtain ⟨L₁, hL₁, hL⟩ := H₂ K₁ h (subset_closure_of_subset (fun y hy => by simp [s, hy])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨f₁, hf₁⟩ := H₃ K₁ h (subset_closure_of_subset (fun y hy => by simp [s, hy])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨x₁, hx₁⟩ := H₄ K₁ h (subset_closure_of_subset (fun y hy => by simp [s, hy])) (Sp K₁) (𝟙 _) inc
    (spMap K₁.subtype) (IsPullback.of_vert_isIso ⟨by simp [inc]⟩) (spMap_subtype_comp h) (by simp)
  let act₁ : J → (A₁ ⟶ A₁) := fun j =>
    Over.homMk (sq₁.lift (f₁ j) A₁.hom (by rw [(hf₁ j).2, sq₁.w])) (sq₁.lift_snd _ _ _)
  let pt₁ : I → (𝟙_ (Over (Sp K₁)) ⟶ A₁) := fun i =>
    Over.homMk (sq₁.lift (x₁ i) (𝟙 _) (by rw [(hx₁ i).2]; simp)) (sq₁.lift_snd _ _ _)
  obtain ⟨hab, hdim⟩ := GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend K₁ K K₁.subtype A₁ P.A ψ hG P.isAb
  obtain ⟨hrig, hsym, hkt⟩ := GlobalTheory.PolDescent.rigidified_sym_kTriv_descend K₁ K K₁.subtype A₁ P.A ψ L₁ P.L
    hab hG hL₁ P.isLB hL
  have hamp := GlobalTheory.AmpleDescent.relAmple_of_fieldExtension K₁ K K₁.subtype A₁ P.A ψ L₁ P.L
    hab hG hL₁ P.isLB hL P.ample
  let P₁ : PolAV (Sp K₁) :=
    { A := A₁, grp := gr₁, isAb := hab, g := P.g, smoothDim := hdim P.g P.smoothDim, L := L₁,
      isLB := hL₁, rigid := hrig P.rigid, sym := hsym P.sym, ample := hamp, ktriv := hkt P.ktriv }
  refine ⟨K₁, P₁, ψ, act₁, pt₁, countable_closure s, hG, hL, fun j => ?_, fun i => ?_⟩
  · change (a j).left ≫ ψ = ψ ≫ (act₁ j).left
    have e₁ : (act₁ j).left ≫ φ₁ = f₁ j := sq₁.lift_fst _ _ _
    apply sq₁.hom_ext
    · rw [Category.assoc, hψ₁, Category.assoc, e₁, (hf₁ j).1]
    · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w, Category.assoc, Over.w, hψ₂]
  · change (x i).left ≫ ψ = spMap K₁.subtype ≫ (pt₁ i).left
    have e : (x i).left ≫ P.A.hom = 𝟙 _ := Over.w (x i)
    have e₁ : (pt₁ i).left ≫ φ₁ = x₁ i := sq₁.lift_fst _ _ _
    have e₂ : (pt₁ i).left ≫ A₁.hom = 𝟙 _ := sq₁.lift_snd _ _ _
    apply sq₁.hom_ext
    · rw [Category.assoc, hψ₁]
      exact ((hx₁ i).1.symm.trans (congrArg _ e₁.symm)).trans (Category.assoc _ _ _).symm
    · rw [Category.assoc, hψ₂, ← Category.assoc, e]
      refine (Category.id_comp _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
      exact ((congrArg _ e₂).trans (Category.comp_id _)).symm

end GlobalTheory.PolCountableDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RatTors
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.Ex.Trait

def Along {O' R : Type} [CommRing O'] [IsDomain O'] [CommRing R] [IsDomain R] (f : O' →+* R) (C : Type) [Field C]
    [Algebra (FractionRing O') C] [Algebra (FractionRing R) C] : Prop :=
  ∀ x, algebraMap (FractionRing R) C (algebraMap _ _ (f x)) = algebraMap (FractionRing O') C (algebraMap _ _ x)

def RatTors {R : Type} [CommRing R] [IsDomain R] (B : PolAV (Sp R)) (C : Type) [Field C] [Algebra (FractionRing R) C]
    (n : ℕ) : Prop :=
  ∀ x : TF (R := R) C ⟶ B.A, x ^ n = 1 → ∃ x₀ : TK R ⟶ B.A, x.left = jFK (R := R) C ≫ x₀.left

def wVal {R O' : Type} [CommRing R] [IsDomain R] [CommRing O'] [IsDomain O'] {P : DegPre R} {D₀ : DegPre O'} {C : Type}
    [Field C] [Algebra (FractionRing R) C] [Algebra (FractionRing O') C] {N' N : NumD C} (ν' : NumOf P C N')
    (ν : NumOf D₀ C N) {ψ : P.P.A.left ⟶ D₀.P.A.left} (w : LB.Iso P.P.L (D₀.P.L.pull ψ)) (x : N'.A) : C :=
  valF (ν'.eA x).left _ (w.s (fun _ => ν.J ((ν'.eA x).left ≫ ψ), ν'.J (ν'.eA x).left)).val
section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
  {a : ArcIn D l β O' b} {C : Type} [NontriviallyNormedField C] [Algebra (FractionRing O') C]

def Labels (A : Lift a C) (u : Cˣ) (r : ℕ → Cˣ) {o : Full D C} (M : Mdl o) {N' : NumD C} (ν' : NumOf M.P.D.toPre C N')
    (J : NumD.Iso (A.N.twist A.be u) N') (k : ℕ) : Prop :=
  ∀ x (p : (A.N.twist A.be u).QT k) (q' : N'.QT k) p' z, TwRel A.be u (r k) (A.q _ x) p →
    q'.1.1.toAdd = J.e p.1.1.toAdd → J.Rel p.1.2 q'.1.2 → ν'.QPt p' q' → z.left = (o.I.ev k x).left ≫ M.φ →
    M.P.ToA C k p' z

def Fit (A : Lift a C) (u : Cˣ) {o : Full D C} (M : Mdl o) (f : O' →+* M.W) {N' : NumD C} (ν' : NumOf M.P.D.toPre C N')
    (J : NumD.Iso (A.N.twist A.be u) N') (ψ : M.P.D.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (w : LB.Iso M.P.D.toPre.P.L (a.D₀.P.L.pull ψ)) (e : a.D₀.X ≃ₗ[𝓞 E] M.P.D.toPre.X) : Prop :=
  IsGrpPullback M.P.D.toPre.P.A a.D₀.P.A (spMap f) ψ ∧ w.IsGen ∧
    (∀ x : A.N.A, (ν'.eA (J.φ x)).left ≫ ψ = (A.ν.eA x).left) ∧ (∀ y : A.N.X, e (A.ν.eX y) = ν'.eX (J.e y)) ∧
    (∀ x, wVal ν' A.ν w x ≠ 0) ∧ ∀ x : A.N.A, (J.h x : C) * wVal ν' A.ν w (J.φ x) = wVal ν' A.ν w 1
end

def AllS (P : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
    (a : ArcIn D l β O' b) {C : Type} [NontriviallyNormedField C] [Algebra (FractionRing O') C] (A : Lift a C) (u : Cˣ)
    (_ : ℕ → Cˣ) {o : Full D C} (M : Mdl o) (_ : O' →+* M.W) {N' : NumD C} (_ : NumOf M.P.D.toPre C N'),
    NumD.Iso (A.N.twist A.be u) N' → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (c : Coeff l)
    (O : Type) [CommRing O] (β : O →+* c.F) (O' : Type) [CommRing O'] [IsDomain O'] [IsNoetherianRing O'] (b : O →+* O')
    (a : ArcIn D l β O' b) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
    [CharZero C] [Algebra (FractionRing O') C] (A : Lift a C) (u : Cˣ) (r : ℕ → Cˣ) (o : Full D C) (M : Mdl o)
    (f : O' →+* M.W) (N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (J : NumD.Iso (A.N.twist A.be u) N'),
    Roots u r → Along f C → P a A u r M f ν' J
end GlobalTheory.Ex.Trait
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestLatticeEqSpanModelSections
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH


open TestSpan in
theorem testLattice_eq_span_sections : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (τ : S.Test p y₀) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (md : Mod p u.j u.G S.g S.N l.q (u.H S.N) σ cls) (b : Matrix S.J S.J (FractionRing u.V)), S.Big → (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → l.Match τ → u.Link σ b → b.det ≠ 0 → ∃ c : FractionRing u.V, c ≠ 0 ∧ τ.E = Submodule.span (OO p) (Set.range ((c • b).map (algebraMap _ (PadicAlgCl p)))) := by
  intro hLL o Ω _ _ _ _ S ρ p _ y₀ u l τ σ cls md b hbig hint hmt hlink hdet
  obtain ⟨κ, hκ, hfr⟩ := FrameNorm.exists_pos_isGreatest_norm_mulVec_on_ker hLL o Ω S ρ p y₀ u l σ cls md b hbig hint hlink
  have hΛ := LatChar.mem_lattice_iff hLL o Ω S ρ p y₀ u l σ cls md b κ hbig hint hlink hdet hκ hfr
  let φ : o →+* OO p := (y₀.comp (algebraMap o S.R)).codRestrict (OO p) fun a => (mem_OO_iff _).2 (hint a)
  have hE := E_eq_bdd τ φ (fun _ => rfl) (EvCrd.ev_crd_act hLL o Ω S ρ).2
    (GlobalTheory.weightSpace_irreducible_residue hLL o Ω S ρ p φ _ τ.isoFree)
  have hker : ∀ a, a ∈ l.yy.ker ↔ a ∈ τ.yy.ker := fun a => by
    obtain ⟨e, -, he⟩ := hmt
    have h1 := he a 0
    rw [map_zero] at h1
    exact h1.symm
  obtain ⟨x, hx⟩ := τ.δ_max.1
  obtain ⟨i, hi⟩ := (hfr 0 (zero_mem _)).1
  let em := algebraMap (FractionRing u.V) (PadicAlgCl p)
  have hy : ∀ a, y₀ a = em (u.yK a) := fun a => (DFunLike.congr_fun u.fac a).symm
  let d : FractionRing u.V := u.yK ⟨S.th x, S.th_mem x⟩
  let k : FractionRing u.V := b.mulVec (fun i => u.yK ⟨S.ev 0 i, S.ev_mem 0 i⟩) i
  have hd : ‖em d‖ = τ.δ := (congrArg norm (hy _)).symm.trans hx
  have hk : ‖em k‖ = κ := by
    refine Eq.trans ?_ hi
    simp only [hy]
    exact congrArg norm (congrFun (map_mulVec' em b _) i).symm
  have hc : ‖em (d / k)‖ = τ.δ / κ := by rw [map_div₀, norm_div, hd, hk]
  have hc0 : em (d / k) ≠ 0 := norm_pos_iff.1 (hc ▸ div_pos τ.δ_pos hκ)
  refine ⟨d / k, fun h => hc0 (by rw [h, map_zero]), ?_⟩
  generalize d / k = c at hc hc0
  let m : (S.J → PadicAlgCl p) →ₗ[OO p] (S.J → PadicAlgCl p) :=
    (LinearMap.lsmul (PadicAlgCl p) (S.J → PadicAlgCl p) (em c)).restrictScalars (OO p)
  have hm : ∀ e, m e = em c • e := fun _ => rfl
  have hr : Set.range ((c • b).map em) = m '' Set.range (b.map em) := by
    have h1 : ∀ i, (c • b).map em i = m (b.map em i) := fun i => by
      rw [hm]
      funext j
      simp only [Matrix.map_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul]
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, (h1 i).symm⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, h1 i⟩
  clear_value m
  rw [hE]
  refine Eq.trans ?_ (congrArg (Submodule.span (OO p)) hr).symm
  rw [Submodule.span_image]
  ext e
  constructor
  · intro he
    refine ⟨(em c)⁻¹ • e, (hΛ _).2 fun a ha => ?_, by rw [hm, smul_inv_smul₀ hc0]⟩
    rw [smul_dotProduct, smul_eq_mul, norm_mul, norm_inv, hc, inv_div, div_mul_eq_mul_div, div_le_iff₀ τ.δ_pos]
    exact mul_le_mul_of_nonneg_left (he a ((hker a).1 ha)) hκ.le
  · rintro ⟨e, he, rfl⟩ a ha
    rw [hm, smul_dotProduct, smul_eq_mul, norm_mul, hc, div_mul_eq_mul_div, div_le_iff₀ hκ]
    exact mul_le_mul_of_nonneg_left ((hΛ _).1 he a ((hker a).2 ha)) τ.δ_pos.le

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionClassesDescendFiniteAlgebra
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.TorsDesc

theorem s_mem_of_basis {F : Type} [CommRing F] (N : NumD F) (U : Subgroup Fˣ) (g : N.Gt) {ι : Type}
    (e : Module.Basis ι ℤ N.X) (hθ : ∀ χ χ', N.θ (N.c χ) (N.c χ') g.b ∈ U) (he : ∀ l, g.s (e l) ∈ U) (χ : N.X) :
    g.s χ ∈ U := by
  have hχ : χ ∈ Submodule.span ℤ (Set.range e) := by rw [e.span_eq]; trivial
  rw [← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure] at hχ
  induction hχ using AddSubgroup.closure_induction with
  | mem x hx => obtain ⟨l, rfl⟩ := hx; exact he l
  | zero => rw [NumD.Gt.s_zero]; exact U.one_mem
  | add x y _ _ hx hy =>
    rw [eq_div_iff_mul_eq'.2 (g.mult x y)]
    exact U.div_mem (U.mul_mem hx hy) (hθ _ _)
  | neg x _ hx =>
    have := g.mult x (-x)
    rw [add_neg_cancel, NumD.Gt.s_zero, one_mul] at this
    exact (U.mul_mem_cancel_left hx).1 (this ▸ hθ _ _)

theorem s_mem_of_root {F : Type} [CommRing F] (N : NumD F) (U : Subgroup Fˣ)
    (hθ : ∀ x y u, N.θ x y u ∈ U) (hψ : ∀ χ, N.ψ χ ∈ U) {k : ℕ} (hU : ∀ u : Fˣ, u ^ k ∈ U → u ∈ U) (p : N.QT k)
    (χ : N.X) : p.1.2.s χ ∈ U := by
  refine hU _ ?_
  rw [← NumD.Gt.pow_s, N.mem_QT.1 p.2, NumD.io_s]
  exact U.mul_mem (U.div_mem (U.div_mem (hψ _) (hψ _)) (hψ _)) (U.prod_mem fun _ _ => hθ _ _ _)

theorem exists_finite_subalgebra (O F : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O]
    [CharZero O] [Field F] [Algebra (FractionRing O) F] [Algebra O F] [IsScalarTower O (FractionRing O) F]
    (K : IntermediateField (FractionRing O) F) [FiniteDimensional (FractionRing O) K] :
    ∃ O₁ : Subalgebra O F, Module.Finite O O₁ ∧ ∀ x ∈ K, IsIntegral O x → x ∈ O₁ := by
  have : CharZero (FractionRing O) := IsFractionRing.charZero_of_isFractionRing O
  have : Module.Finite O (integralClosure O K) := IsIntegralClosure.finite O (FractionRing O) K _
  let v : K →ₐ[O] F := { K.val.toRingHom with commutes' := fun _ => rfl }
  have hv : Function.Injective v := Subtype.val_injective
  refine ⟨(integralClosure O K).map v, Module.Finite.equiv ((integralClosure O K).equivMapOfInjective v hv).toLinearEquiv,
    fun x hx hi => ⟨⟨x, hx⟩, ?_, rfl⟩⟩
  exact (isIntegral_algHom_iff v hv).1 hi

theorem descend : ∀ (O F : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [CharZero O] [Field F] [Algebra (FractionRing O) F] [Algebra O F] [IsScalarTower O (FractionRing O) F] [Algebra.IsAlgebraic (FractionRing O) F] (S : ValuationSubring F), (∀ x, x ∈ S ↔ IsIntegral O x) → ∀ (N : NumD F) (K₁ : IntermediateField (FractionRing O) F) (A₀ : Subgroup N.A), FiniteDimensional (FractionRing O) K₁ → (∀ χ, N.c χ ∈ A₀) → (∀ x ∈ A₀, ∀ y ∈ A₀, ∀ u ∈ A₀, (N.θ x y u : F) ∈ K₁) → (∀ x ∈ A₀, (N.σ x : F) ∈ K₁) → (∀ x ∈ A₀, N.th x ∈ K₁) → (∀ χ, (N.ψ χ : F) ∈ K₁) → (∀ x y u, S.valuation (N.θ x y u : F) = 1) → (∀ x, S.valuation (N.σ x : F) = 1) → (∀ x, N.th x ∈ S) → (∀ χ, S.valuation (N.ψ χ : F) = 1) → ∀ (Ix : Type) [Finite Ix] (k : Ix → ℕ) (p : ∀ i, N.QT (k i)), (∀ i, 0 < k i) → (∀ i, (p i).1.2.b ∈ A₀) → ∃ O₁ : Subalgebra O F, Module.Finite O O₁ ∧ ∃ (N₀ : NumD O₁) (I : NumD.Hom O₁.val.toRingHom N₀ N), I.lam = 1 ∧ ∀ i (p' : N.QT (k i)), N.QEq (p i) p' → ∃ p₀ : N₀.QT (k i), p'.1.1.toAdd = I.e p₀.1.1.toAdd ∧ I.Rel p₀.1.2 p'.1.2 := by
  intro O F _ _ _ _ _ _ _ _ _ _ S hS N K₁ A₀ hK hc hθ hσ hth hψ vθ vσ vth vψ Ix _ k p hk hp
  let e := Module.Free.chooseBasis ℤ N.X
  let T : Set F := Set.range fun il : Ix × Module.Free.ChooseBasisIndex ℤ N.X => ((p il.1).1.2.s (e il.2) : F)
  have : Finite T := (Set.finite_range _).to_subtype
  have : FiniteDimensional (FractionRing O) (IntermediateField.adjoin (FractionRing O) T) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  let K₂ := K₁ ⊔ IntermediateField.adjoin (FractionRing O) T
  have : FiniteDimensional (FractionRing O) K₂ := IntermediateField.finiteDimensional_sup _ _
  have h12 : K₁ ≤ K₂ := le_sup_left
  obtain ⟨O₁, hfin, hO⟩ := exists_finite_subalgebra O F K₂
  have hunit : ∀ u : Fˣ, (u : F) ∈ K₂ → S.valuation (u : F) = 1 → ∃ a : O₁ˣ, O₁.val.toRingHom a = u := by
    intro u hu hv
    have h1 : (u : F) ∈ O₁ := hO _ hu ((hS _).1 ((S.valuation_le_one_iff _).1 hv.le))
    have h2 : ((u⁻¹ : Fˣ) : F) ∈ O₁ := by
      rw [Units.val_inv_eq_inv_val]
      exact hO _ (K₂.inv_mem hu) ((hS _).1 ((S.valuation_le_one_iff _).1 (by rw [map_inv₀, hv, inv_one])))
    exact ⟨⟨⟨_, h1⟩, ⟨_, h2⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩, rfl⟩
  let U : Subgroup Fˣ :=
    { carrier := {u | (u : F) ∈ K₂}
      mul_mem' := fun ha hb => K₂.mul_mem ha hb
      one_mem' := K₂.one_mem
      inv_mem' := fun {u} hu => by
        change ((u⁻¹ : Fˣ) : F) ∈ K₂
        rw [Units.val_inv_eq_inv_val]
        exact K₂.inv_mem hu }
  let V : Subgroup Fˣ := (S.valuation.toMonoidWithZeroHom.toMonoidHom.comp (Units.coeHom F)).ker
  obtain ⟨N₀, I, hI, h⟩ := GlobalTheory.Ex.NumD.exists_descent_subring O₁ F O₁.val.toRingHom Subtype.val_injective N A₀ hc
    (fun x hx y hy u hu => hunit _ (h12 (hθ x hx y hy u hu)) (vθ _ _ _))
    (fun x hx => hunit _ (h12 (hσ x hx)) (vσ _))
    (fun x hx => ⟨⟨_, hO _ (h12 (hth x hx)) ((hS _).1 (vth x))⟩, rfl⟩)
    (fun χ => hunit _ (h12 (hψ χ)) (vψ _))
  refine ⟨O₁, hfin, N₀, I, hI, fun i p' ⟨z, _, hz⟩ => h _ p' ?_ fun χ => hunit _ ?_ ?_⟩
  · rw [hz]
    exact A₀.mul_mem (hp i) (hc z)
  · have h1 : (p i).1.2.s χ ∈ U := s_mem_of_basis N U _ e (fun χ χ' => h12 (hθ _ (hc _) _ (hc _) _ (hp i)))
      (fun l => (le_sup_right : _ ≤ K₂) (IntermediateField.subset_adjoin _ _ ⟨(i, l), rfl⟩)) χ
    have hψU : ∀ χ, N.ψ χ ∈ U := fun χ => h12 (hψ χ)
    change p'.1.2.s χ ∈ U
    rw [hz, NumD.Gt.mul_s]
    exact U.div_mem (U.mul_mem h1 (U.div_mem (U.div_mem (hψU _) (hψU _)) (hψU _)))
      (h12 (hθ _ (hc _) _ (hp i) _ (hc z)))
  · refine s_mem_of_root N V vθ vψ (fun u hu => ?_) p' χ
    have : S.valuation (u : F) ^ k i = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val]; exact hu
    exact (pow_eq_one_iff_of_nonneg zero_le (hk i).ne').1 this

end GlobalTheory.Ex.TorsDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPairingValuesOfFamiliesValues
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.WeilValues

section Val
variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem top_le_chart {J : (Sp F ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) (φ : K → (Y ⟶ X))
    (r : Sp F ⟶ Y) : ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ (fun k => J (r ≫ φ k)) := fun z _ =>
  Good.mem (L := L) (z := z) (J := J) (fun ψ => hJ ψ trivial) φ r

theorem vF_ne_zero {J : (Sp F ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) : vF t r J ≠ 0 := by
  refine fun h => ?_
  exact (((Units.isUnit _).map _).map _).ne_zero ((dif_pos (top_le_chart hJ φ r)).symm.trans h)

theorem valF_const_mul (r : Sp F ⟶ Y) (π : Y ⟶ Sp F) (h : r ≫ π = 𝟙 _) (U : Y.Opens) (hU : ⊤ ≤ r ⁻¹ᵁ U) (z : F)
    (a : Γ(Y, U)) : valF r U (resTop U (π.appTop.hom (fnOf z)) * a) = z * valF r U a := by
  rw [valF, valF, dif_pos hU, dif_pos hU, map_mul, map_mul]
  congr 1
  have e : (r.appLE U ⊤ hU).hom (resTop U (π.appTop.hom (fnOf z))) = (r ≫ π).appTop.hom (fnOf z) := by
    simp only [resTop]
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE, Scheme.Hom.comp_appTop,
      CommRingCat.hom_comp, RingHom.comp_apply]
    exact congrArg (fun g : Γ(Y, ⊤) ⟶ Γ(Sp F, ⊤) => g.hom (π.appTop.hom (fnOf z))) (Scheme.Hom.appLE_eq_app r (U := ⊤))
  rw [e, h]
  exact (Scheme.ΓSpecIso (CommRingCat.of F)).inv_hom_id_apply z
end Val

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N : NumD F}

theorem famV_smul (ν : NumOf D F N) {k : ℕ} {s : Fam D F k} {f : N.X → N.A → F} (h : ν.FamV s f) (z : F) :
    ν.FamV (z • s) (z • f) := by
  intro α x
  have e : (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst, Over.id_left]
  refine Eq.trans ?_ (valF_const_mul _ _ e _ (top_le_chart ν.good _ _) z _).symm
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, h α x]
  rfl

theorem exists_phiRel (hB : D.TauBimult) {k : ℕ} (p : QkPt D F k)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (hw : w.IsGen) (s : Fam D F k) :
    ∃ t, PhiRel D F k p w s t := by
  obtain ⟨t, ht⟩ := DVR.exists_phi GlobalTheory.globalFns_holds p w hw hB s
  exact ⟨t, (DVR.phiRel_iff GlobalTheory.globalFns_holds p w hw s t).2 ht⟩

theorem phi_ne_zero {k : ℕ} (q : N.QT k) (w : Fˣ) {f : N.X → N.A → F} (hf : f ≠ 0) : N.phi q w f ≠ 0 := by
  intro h
  refine hf (funext fun α => funext fun x => ?_)
  have := congrFun (congrFun h (α + q.1.1.toAdd)) (x * q.1.2.b⁻¹)
  simp only [NumD.phi, add_sub_cancel_right, inv_mul_cancel_right, Pi.zero_apply, Units.mul_right_eq_zero] at this
  exact this

theorem weil_eq_values : BrGtSt → BrFamSt → BrWpSt := by
  intro _ hF R _ _ D hE hB F _ _ _ N ν k hk p p' q q' z hq hq'
  obtain ⟨h1, h2, -, ⟨s₀, f₀, hs₀, hf₀⟩, -, h6⟩ := hF R D hE hB F N ν k hk
  have key : ∀ w w', w.IsGen → w'.IsGen → ∀ s s₁ s₂ s₃ s₄ : Fam D F k,
      PhiRel D F k p' w' s s₁ → PhiRel D F k p w s₁ s₂ → PhiRel D F k p w s s₃ → PhiRel D F k p' w' s₃ s₄ →
      ∀ f, ν.FamV s f → ∃ f₄, ν.FamV s₄ f₄ ∧ ν.FamV s₂ ((N.wp q q' : F) • f₄) ∧ (f ≠ 0 → f₄ ≠ 0) := by
    intro w w' hw hw' s s₁ s₂ s₃ s₄ r₁ r₂ r₃ r₄ f hf
    obtain ⟨f₁, a₁, -⟩ := h1 s₁
    obtain ⟨f₂, a₂, -⟩ := h1 s₂
    obtain ⟨f₃, a₃, -⟩ := h1 s₃
    obtain ⟨f₄, a₄, -⟩ := h1 s₄
    let u : Fˣ := Units.mk0 _ (vF_ne_zero ν.good w (𝟙 (Sp F)))
    let u' : Fˣ := Units.mk0 _ (vF_ne_zero ν.good w' (𝟙 (Sp F)))
    have e₁ := (h6 p' q' w' u' s s₁ f f₁ hq' hw' rfl hf a₁).1 r₁
    have e₂ := (h6 p q w u s₁ s₂ f₁ f₂ hq hw rfl a₁ a₂).1 r₂
    have e₃ := (h6 p q w u s s₃ f f₃ hq hw rfl hf a₃).1 r₃
    have e₄ := (h6 p' q' w' u' s₃ s₄ f₃ f₄ hq' hw' rfl a₃ a₄).1 r₄
    refine ⟨f₄, a₄, ?_, fun h => ?_⟩
    · rw [e₄, e₃, ← (GlobalTheory.Ex.PhiOp.phi_main F N k q q' u u' f).2.2.1, ← e₁, ← e₂]
      exact a₂
    · rw [e₄, e₃]
      exact phi_ne_zero _ _ (phi_ne_zero _ _ h)
  constructor
  · intro H
    obtain ⟨w, hw⟩ := DVR.exists_gen_of_local (V := F) D.P.L D.P.isLB (DegPre.lineφ D F p.g.b) (DegPre.lineε k)
    obtain ⟨w', hw'⟩ := DVR.exists_gen_of_local (V := F) D.P.L D.P.isLB (DegPre.lineφ D F p'.g.b) (DegPre.lineε k)
    obtain ⟨s₁, r₁⟩ := exists_phiRel hB p' w' hw' s₀
    obtain ⟨s₂, r₂⟩ := exists_phiRel hB p w hw s₁
    obtain ⟨s₃, r₃⟩ := exists_phiRel hB p w hw s₀
    obtain ⟨s₄, r₄⟩ := exists_phiRel hB p' w' hw' s₃
    obtain ⟨f₄, a₄, a₂, hne⟩ := key w w' hw hw' s₀ s₁ s₂ s₃ s₄ r₁ r₂ r₃ r₄ f₀ hs₀
    have e := (DVR.isSmul_iff z s₄ s₂).1 (H w w' hw hw' s₀ s₁ s₂ s₃ s₄ r₁ r₂ r₃ r₄)
    have b := famV_smul ν a₄ z
    rw [← e] at b
    exact smul_left_injective F (hne hf₀) ((h1 s₂).unique b a₂)
  · rintro rfl w w' hw hw' s s₁ s₂ s₃ s₄ r₁ r₂ r₃ r₄
    obtain ⟨f, hf, -⟩ := h1 s
    obtain ⟨f₄, a₄, a₂, -⟩ := key w w' hw hw' s s₁ s₂ s₃ s₄ r₁ r₂ r₃ r₄ f hf
    exact (DVR.isSmul_iff _ s₄ s₂).2 (h2 _ _ _ a₂ (famV_smul ν a₄ _))

end GlobalTheory.WeilValues
end

