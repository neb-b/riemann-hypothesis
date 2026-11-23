module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtDatumOfSplitTorusExtension
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.GtBaseChangeSharp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreUniformisationDataIsEvenCubicalOnClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.PreEven
open GlobalTheory.UU GlobalTheory.ClosedPol


set_option maxHeartbeats 1000000 in
theorem evenOn_preU : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), EvenOn U.P := by
  intro R _ _ _ D A G _ _ U
  have hG := GlobalTheory.firstFiveLaws.1.globalFns
  set g := U.gt 0 with hg
  have := g.q_hom
  have := g.i_hom
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have hB : IsAbelianScheme (thickObj R (maximalIdeal R) 0 D.P.A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ _ D.P.isAb
  have := hB.comm
  obtain ⟨O, h₁, h₂, h₃, hd⟩ := GlobalTheory.exists_gtDatum_of_splitTorus_extension _ D.X (thickObj R (maximalIdeal R) 0 G)
    (thickObj R (maximalIdeal R) 0 D.P.A) hB g.q g.i g.q_hom g.i_hom g.q_flat g.q_surj inferInstance g.isKernel
  obtain ⟨d, hdq, hdi⟩ := hd hB
  let Q : TQ (thickObj R (maximalIdeal R) 0 G) D.X :=
    { B := thickObj R (maximalIdeal R) 0 D.P.A
      isAb := hB
      q := g.q
      i := g.i
      q_hom := g.q_hom
      i_hom := g.i_hom
      q_flat := g.q_flat
      q_surj := g.q_surj
      q_affine := g.q_affine
      isKernel := g.isKernel
      loc := by
        have l := (TQ.ofGtDatum d).loc
        rw [show (TQ.ofGtDatum d).q = g.q from hdq, show (TQ.ofGtDatum d).i = g.i from hdi] at l
        exact l }
  obtain ⟨P₀, hlev⟩ := exists_isLevelCP (maximalIdeal R) 0 U.P
  obtain ⟨w₀, h₀⟩ := hlev
  obtain ⟨rig, hr, c, σ, h₁, h₂, h₃, H⟩ := exists_isCPMap U.P (toBase_mul_pullback G (thick R (maximalIdeal R) 0)) _
    (pull_isLB U.P.L.isLB _) _ (pullIso_isGen U.P.L.isLB (pullback.fst G.hom (thick R (maximalIdeal R) 0)))
  obtain ⟨w₁, k₁⟩ := cpMap_congr (Category.id_comp _).symm (Category.id_comp _).symm h₀
    (by rw [Category.id_comp, Category.id_comp]; exact pullback.condition)
  obtain ⟨w₂, k₂, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ P₀ _ _ _ (𝟙 _) (by simp) _ H).2
    (toBase_mul_of_isMonHom (𝟙 _) _) w₁ k₁
  have H' := isCPMap_w hG U 0 H
  obtain ⟨w₃, -, k₃⟩ := H'.exists_comp k₂ (by rw [Category.id_comp, Category.id_comp]; exact Over.w (U.gt 0).pG)
  obtain ⟨M, wM, hM⟩ := exists_isLevelCP (maximalIdeal R) 0 (CP.ofDegPre hG D)
  obtain ⟨w₄, k₄⟩ := cpMap_congr rfl (Category.id_comp _) k₃
    (by rw [Category.assoc, pullback.condition, Category.id_comp]; simpa using Over.w g.pG)
  obtain ⟨w₅, k₅, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ M P₀ _ _ _ g.q.left
    ((Over.w g.q).trans (Category.comp_id _).symm) _ hM).2
    (toBase_mul_of_isMonHom g.q _) w₄ k₄
  have De : Q.Desc P₀ := ⟨M, w₅, k₅⟩
  exact ⟨D.X, inferInstance, inferInstance, inferInstance, Q, P₀, ⟨w₀, h₀⟩,
    GlobalTheory.UniformizationSetting.exists_even_of_desc De⟩

end GlobalTheory.Mum.PreEven
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrecompleteOfPowLe
section
noncomputable section

open IsLocalRing

namespace GlobalTheory.FiniteCompletionLocalHom

theorem isLocalHom_of_finite {R R₂ V : Type*} [CommRing R] [IsLocalRing R] [CommRing R₂] [IsLocalRing R₂]
    [CommRing V] [IsLocalRing V] (ρ : R →+* R₂) (hρ : ρ.Finite) (ψ : R₂ →+* V)
    (h : IsLocalHom (ψ.comp ρ)) : IsLocalHom ψ := by
  letI := ρ.toAlgebra
  haveI : Module.Finite R R₂ := hρ
  haveI : Algebra.IsIntegral R R₂ := Algebra.IsIntegral.of_finite R R₂

  have hc : (maximalIdeal V).comap (ψ.comp ρ) = maximalIdeal R :=
    ((IsLocalRing.local_hom_tfae (ψ.comp ρ)).out 1 5).mp h
  have hP : ((maximalIdeal V).comap ψ).IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R)
    have hc' : ((maximalIdeal V).comap ψ).comap (algebraMap R R₂) = maximalIdeal R := hc
    change (((maximalIdeal V).comap ψ).comap (algebraMap R R₂)).IsMaximal
    rw [hc']
    infer_instance
  exact ((IsLocalRing.local_hom_tfae ψ).out 1 5).mpr (IsLocalRing.eq_maximalIdeal hP)

theorem exists_extension : ∀ (R R₂ W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₂] [IsDomain R₂]
    [IsLocalRing R₂] [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), IsLocalHom φ →
    ∀ (ρ : R →+* R₂), RingHom.Finite ρ → ∀ (Ω : Type) [Field Ω] (j : FractionRing W →+* Ω) (m : R₂ →+* Ω),
    Function.Injective m → (∀ r : R, m (ρ r) = j (algebraMap W (FractionRing W) (φ r))) →
    ∃ (W₂ : Type) (_ : CommRing W₂) (_ : IsDomain W₂) (_ : IsLocalRing W₂) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂)
      (j₂ : FractionRing W₂ →+* Ω), GlobalTheory.LN.CDvr W₂ ∧ GlobalTheory.Mum.FinExt σ ∧ IsLocalHom σ ∧ Function.Injective φ₂ ∧
      IsLocalHom φ₂ ∧ φ₂.comp ρ = σ.comp φ ∧
      (∀ w : W, j₂ (algebraMap W₂ (FractionRing W₂) (σ w)) = j (algebraMap W (FractionRing W) w)) ∧
      ∀ r : R₂, j₂ (algebraMap W₂ (FractionRing W₂) (φ₂ r)) = m r := by
  intro R R₂ W _ _ _ _ _ _ _ _ _ hW φ hφ ρ hρ Ω _ j m hm hcomp
  obtain ⟨hdvr, hcompl, hchar⟩ := (GlobalTheory.LN.cDvr_iff W).mp hW
  haveI := hdvr
  haveI := hcompl
  haveI := hchar
  letI : Algebra (FractionRing W) Ω := j.toAlgebra
  letI : Algebra W Ω := (j.comp (algebraMap W (FractionRing W))).toAlgebra
  haveI : IsScalarTower W (FractionRing W) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl

  obtain ⟨s₀, hs₀int, hs₀⟩ := GlobalTheory.ArcPointDescent.exists_finset ρ hρ φ m (fun r => hcomp r)
  have hmint : ∀ r, IsIntegral W (m r) := fun r =>
    hs₀ (integralClosure W Ω) (fun x hx => hs₀int x hx) r

  let F : IntermediateField (FractionRing W) Ω := algebraicClosure (FractionRing W) Ω
  have hmF : ∀ r, m r ∈ F := fun r =>
    ((hmint r).tower_top : IsIntegral (FractionRing W) (m r))
  letI : Algebra W F := ((algebraMap (FractionRing W) F).comp (algebraMap W (FractionRing W))).toAlgebra
  haveI : IsScalarTower W (FractionRing W) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic W F := (IsFractionRing.comap_isAlgebraic_iff (K := FractionRing W)).mpr inferInstance
  haveI : FaithfulSMul W F := (faithfulSMul_iff_algebraMap_injective W F).mpr
    ((algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective W (FractionRing W)))
  let mF : R₂ →+* F := m.codRestrict F hmF
  obtain ⟨s, hsint, hs⟩ := GlobalTheory.ArcPointDescent.exists_finset ρ hρ φ mF (fun r => Subtype.ext (hcomp r))

  obtain ⟨W', hdvr', hc₁, -, hfin, -, hloc, -, hmem⟩ := GlobalTheory.exists_complete_dvr_finite_subalgebra W F s
  haveI := hdvr'
  have hWs : ∀ a, mF a ∈ W' := hs W' fun x hx => hmem x hx (hsint x hx)
  let φ₂ : R₂ →+* W' := mF.codRestrict W' hWs
  let σ : W →+* W' := algebraMap W W'
  have hσinj : Function.Injective σ := fun a b hab =>
    FaithfulSMul.algebraMap_injective W F (congrArg Subtype.val hab)
  let ι : W' →+* Ω := (algebraMap F Ω).comp (algebraMap W' F)
  have hιinj : Function.Injective ι := fun a b hab => Subtype.ext (Subtype.ext hab)
  let j₂ : FractionRing W' →+* Ω := IsFractionRing.lift hιinj
  have hC : GlobalTheory.LN.CDvr W' :=
    (GlobalTheory.LN.cDvr_iff W').mpr ⟨hdvr', hc₁, charZero_of_injective_algebraMap hσinj⟩
  have hcomm : φ₂.comp ρ = σ.comp φ := RingHom.ext fun r => Subtype.ext (Subtype.ext (hcomp r))
  haveI : IsLocalHom σ := hloc
  have hloc₂ : IsLocalHom (φ₂.comp ρ) := by
    rw [hcomm]
    exact RingHom.isLocalHom_comp σ φ
  refine ⟨W', inferInstance, inferInstance, inferInstance, σ, φ₂, j₂, hC,
    (⟨GlobalTheory.ArcPointDescent.admissibleBase_maximalIdeal_completeDVR hC, hσinj, RingHom.finite_algebraMap.mpr hfin⟩ : _ ∧ _ ∧ _),
    hloc, fun a b hab => hm (congrArg (fun x : W' => ((x : F) : Ω)) hab),
    isLocalHom_of_finite ρ hρ φ₂ hloc₂, hcomm, fun w => IsFractionRing.lift_algebraMap hιinj (σ w),
    fun r => IsFractionRing.lift_algebraMap hιinj (φ₂ r)⟩

end GlobalTheory.FiniteCompletionLocalHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreconnectedSpaceOfFinGenSubfieldBaseChanges
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.GeomConnDesc

theorem flat_spec_field {K : Type} [Field K] {Z : Scheme.{0}} (f : Z ⟶ Sp K) : Flat f := by
  haveI : IsIntegral (Sp K) := by unfold Sp; infer_instance
  haveI : Subsingleton (Sp K) := by unfold Sp; infer_instance
  infer_instance

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (i : A →+* B) (j : B →+* C) :
    spMap (j.comp i) = spMap j ≫ spMap i := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem appTop_spMap_injective {A B : Type} [CommRing A] [CommRing B] (j : A →+* B)
    (hj : Function.Injective j) : Function.Injective (spMap j).appTop.hom := by
  intro a b h
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom j)
  have h3 : ∀ x, (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((spMap j).appTop.hom x) =
      j ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom x) := fun x => congrArg (fun f => f.hom x) e
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom h
  rw [h3, h3] at h2
  have h4 := hj h2
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom h4
  simpa using this

theorem appTop_spMap_inv {A B : Type} [CommRing A] [CommRing B] (j : A →+* B) (y : A) :
    (spMap j).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom y) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (j y) := by
  have e := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j)
  exact (congrArg (fun f => f.hom y) e).symm

variable {F : Type} [CommRing F] {X : Scheme.{0}} (f : X ⟶ Sp F)

def bc {K A : Type} [CommRing K] [CommRing A] (i₀ : F →+* K) (i : F →+* A) (j : A →+* K) (hji : j.comp i = i₀) :
    pullback f (spMap i₀) ⟶ pullback f (spMap i) :=
  pullback.map f (spMap i₀) f (spMap i) (𝟙 X) (spMap j) (𝟙 _) (by simp)
    (by rw [Category.comp_id, ← hji, spMap_comp])

theorem bc_fst {K A : Type} [CommRing K] [CommRing A] (i₀ : F →+* K) (i : F →+* A) (j : A →+* K) (hji : j.comp i = i₀) :
    bc f i₀ i j hji ≫ pullback.fst f (spMap i) = pullback.fst f (spMap i₀) := by
  simp only [bc, pullback.map, Category.comp_id]
  exact pullback.lift_fst _ _ _

theorem bc_snd {K A : Type} [CommRing K] [CommRing A] (i₀ : F →+* K) (i : F →+* A) (j : A →+* K) (hji : j.comp i = i₀) :
    bc f i₀ i j hji ≫ pullback.snd f (spMap i) = pullback.snd f (spMap i₀) ≫ spMap j := by
  simp only [bc, pullback.map, Category.comp_id]
  exact pullback.lift_snd _ _ _

theorem isPullback_bc {K A : Type} [CommRing K] [CommRing A] (i₀ : F →+* K) (i : F →+* A) (j : A →+* K) (hji : j.comp i = i₀) :
    IsPullback (bc f i₀ i j hji) (pullback.snd f (spMap i₀)) (pullback.snd f (spMap i)) (spMap j) := by
  have s : IsPullback (bc f i₀ i j hji ≫ pullback.fst f (spMap i)) (pullback.snd f (spMap i₀)) f
      (spMap j ≫ spMap i) := by
    rw [bc_fst, ← spMap_comp, hji]
    exact IsPullback.of_hasPullback f (spMap i₀)
  exact IsPullback.of_right s (bc_snd f i₀ i j hji) (IsPullback.of_hasPullback f (spMap i))

theorem bc_trans {K A B : Type} [CommRing K] [CommRing A] [CommRing B] (i₀ : F →+* K) (i₁ : F →+* A) (j₁ : A →+* K) (h₁ : j₁.comp i₁ = i₀)
    (i₂ : F →+* B) (j₂ : B →+* K) (h₂ : j₂.comp i₂ = i₀) (k : A →+* B) (hk : k.comp i₁ = i₂)
    (hk' : j₂.comp k = j₁) :
    bc f i₀ i₁ j₁ h₁ = bc f i₀ i₂ j₂ h₂ ≫ bc f i₂ i₁ k hk := by
  apply pullback.hom_ext
  · simp [bc_fst]
  · rw [Category.assoc, bc_snd, bc_snd, ← Category.assoc, bc_snd, Category.assoc, ← spMap_comp, hk']

theorem mem_of_isPushout {R A B P : CommRingCat.{0}} {φ : R ⟶ A} {ψ : R ⟶ B} {inl : A ⟶ P} {inr : B ⟶ P}
    (H : IsPushout φ ψ inl inr) (S : Subring P) (hA : ∀ a, inl.hom a ∈ S) (hB : ∀ b, inr.hom b ∈ S)
    (x : P) : x ∈ S := by
  let inl' : A ⟶ CommRingCat.of S := CommRingCat.ofHom (inl.hom.codRestrict S hA)
  let inr' : B ⟶ CommRingCat.of S := CommRingCat.ofHom (inr.hom.codRestrict S hB)
  have w : φ ≫ inl' = ψ ≫ inr' := by
    ext r
    exact congrArg (fun g => g.hom r) H.w
  have hd : H.desc inl' inr' w ≫ CommRingCat.ofHom S.subtype = 𝟙 P := by
    apply H.hom_ext
    · rw [H.inl_desc_assoc, Category.comp_id]; rfl
    · rw [H.inr_desc_assoc, Category.comp_id]; rfl
  have := congrArg (fun g => g.hom x) hd
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at this
  rw [← this]
  exact ((H.desc inl' inr' w).hom x).2

theorem isClosed_basicOpen_idem {Y : Scheme.{0}} {e : Γ(Y, ⊤)} (he : IsIdempotentElem e) :
    IsClosed (Y.basicOpen e : Set Y) := by
  have : (Y.basicOpen e : Set Y) = (Y.basicOpen (1 - e) : Set Y)ᶜ := by
    ext x
    constructor
    · intro h h'
      have hx : x ∈ Y.basicOpen (e * (1 - e)) := by rw [Scheme.basicOpen_mul]; exact ⟨h, h'⟩
      rw [he.mul_one_sub_self, Scheme.basicOpen_zero] at hx
      exact hx
    · intro h
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (Y.presheaf.germ ⊤ x trivial e) with h' | h'
      · exact (Y.mem_basicOpen e x trivial).2 h'
      · exact absurd ((Y.mem_basicOpen (U := ⊤) (1 - e) x trivial).2 (by rwa [map_sub, map_one])) h
  rw [this]
  exact (Y.basicOpen (1 - e)).isOpen.isClosed_compl

end GlobalTheory.GeomConnDesc

end

noncomputable section

namespace GlobalTheory.GeomConnDesc

theorem appTop_comp_apply {X Y Z : Scheme.{0}} (g : X ⟶ Y) (h : Y ⟶ Z) (x : Γ(Z, ⊤)) :
    (g ≫ h).appTop.hom x = g.appTop.hom (h.appTop.hom x) := by
  rw [Scheme.Hom.comp_appTop]; rfl

variable {F : Type} [Field F] {X : Scheme.{0}} (f : X ⟶ Sp F) {K : Type} [Field K] (i₀ : F →+* K)

def Lc {n : ℕ} (c : Fin n → K) : Subfield K := Subfield.closure (Set.range i₀ ∪ Set.range c)

theorem mem_Lc {n : ℕ} (c : Fin n → K) (x : F) : i₀ x ∈ Lc i₀ c :=
  Subfield.subset_closure (Or.inl ⟨x, rfl⟩)

theorem mem_Lc' {n : ℕ} (c : Fin n → K) (k : Fin n) : c k ∈ Lc i₀ c :=
  Subfield.subset_closure (Or.inr ⟨k, rfl⟩)

theorem hji_L (L : Subfield K) (hL : ∀ x, i₀ x ∈ L) : L.subtype.comp (i₀.codRestrict L hL) = i₀ :=
  RingHom.ext fun _ => rfl

def hcL (L : Subfield K) (hL : ∀ x, i₀ x ∈ L) :
    pullback f (spMap i₀) ⟶ pullback f (spMap (i₀.codRestrict L hL)) :=
  bc f i₀ (i₀.codRestrict L hL) L.subtype (hji_L i₀ L hL)

theorem hcL_factor {L₁ L₂ : Subfield K} (hL₁ : ∀ x, i₀ x ∈ L₁) (hL₂ : ∀ x, i₀ x ∈ L₂) (hle : L₁ ≤ L₂)
    (y : Γ(pullback f (spMap (i₀.codRestrict L₁ hL₁)), ⊤)) :
    ∃ y', (hcL f i₀ L₁ hL₁).appTop.hom y = (hcL f i₀ L₂ hL₂).appTop.hom y' := by
  have e : hcL f i₀ L₁ hL₁ = hcL f i₀ L₂ hL₂ ≫ bc f (i₀.codRestrict L₂ hL₂)
      (i₀.codRestrict L₁ hL₁) (Subfield.inclusion hle) (RingHom.ext fun _ => rfl) :=
    bc_trans f i₀ (i₀.codRestrict L₁ hL₁) L₁.subtype (hji_L i₀ L₁ hL₁)
      (i₀.codRestrict L₂ hL₂) L₂.subtype (hji_L i₀ L₂ hL₂) (Subfield.inclusion hle)
      (RingHom.ext fun _ => rfl) (RingHom.ext fun _ => rfl)
  exact ⟨_, by rw [e, appTop_comp_apply]⟩

def hc {n : ℕ} (c : Fin n → K) :
    pullback f (spMap i₀) ⟶ pullback f (spMap (i₀.codRestrict (Lc i₀ c) (mem_Lc i₀ c))) :=
  hcL f i₀ (Lc i₀ c) (mem_Lc i₀ c)

theorem hc_factor {n m : ℕ} (c : Fin n → K) (d : Fin m → K) (hle : Lc i₀ c ≤ Lc i₀ d)
    (y : Γ(pullback f (spMap (i₀.codRestrict (Lc i₀ c) (mem_Lc i₀ c))), ⊤)) :
    ∃ y', (hc f i₀ c).appTop.hom y = (hc f i₀ d).appTop.hom y' :=
  hcL_factor f i₀ (mem_Lc i₀ c) (mem_Lc i₀ d) hle y

theorem Lc_le_append_left {n m : ℕ} (c : Fin n → K) (d : Fin m → K) : Lc i₀ c ≤ Lc i₀ (Fin.append c d) :=
  Subfield.closure_mono (Set.union_subset_union_right _
    (Set.range_subset_iff.2 fun k => ⟨Fin.castAdd m k, Fin.append_left _ _ _⟩))

theorem Lc_le_append_right {n m : ℕ} (c : Fin n → K) (d : Fin m → K) : Lc i₀ d ≤ Lc i₀ (Fin.append c d) :=
  Subfield.closure_mono (Set.union_subset_union_right _
    (Set.range_subset_iff.2 fun k => ⟨Fin.natAdd n k, Fin.append_right _ _ _⟩))

theorem gen [QuasiCompact f] [QuasiSeparated f] (x : Γ(pullback f (spMap i₀), ⊤)) :
    ∃ (n : ℕ) (c : Fin n → K) (y : Γ(pullback f (spMap (i₀.codRestrict (Lc i₀ c) (mem_Lc i₀ c))), ⊤)),
      (hc f i₀ c).appTop.hom y = x := by
  haveI : Flat (spMap i₀) := flat_spec_field _
  let S : Subring Γ(pullback f (spMap i₀), ⊤) :=
    { carrier := {x | ∃ (n : ℕ) (c : Fin n → K)
        (y : Γ(pullback f (spMap (i₀.codRestrict (Lc i₀ c) (mem_Lc i₀ c))), ⊤)), (hc f i₀ c).appTop.hom y = x}
      zero_mem' := ⟨0, Fin.elim0, 0, map_zero _⟩
      one_mem' := ⟨0, Fin.elim0, 1, map_one _⟩
      neg_mem' := by
        rintro _ ⟨n, c, y, rfl⟩
        exact ⟨n, c, -y, map_neg _ _⟩
      add_mem' := by
        rintro _ _ ⟨n, c, y, rfl⟩ ⟨m, d, z, rfl⟩
        obtain ⟨y', hy'⟩ := hc_factor f i₀ c (Fin.append c d) (Lc_le_append_left i₀ c d) y
        obtain ⟨z', hz'⟩ := hc_factor f i₀ d (Fin.append c d) (Lc_le_append_right i₀ c d) z
        exact ⟨_, Fin.append c d, y' + z', by rw [map_add (f := _), hy', hz']⟩
      mul_mem' := by
        rintro _ _ ⟨n, c, y, rfl⟩ ⟨m, d, z, rfl⟩
        obtain ⟨y', hy'⟩ := hc_factor f i₀ c (Fin.append c d) (Lc_le_append_left i₀ c d) y
        obtain ⟨z', hz'⟩ := hc_factor f i₀ d (Fin.append c d) (Lc_le_append_right i₀ c d) z
        exact ⟨_, Fin.append c d, y' * z', by rw [map_mul, hy', hz']⟩ }
  have H := ProperFunctions.isPushout_appTop (IsPullback.of_hasPullback f (spMap i₀))
  refine mem_of_isPushout H S (fun a => ?_) (fun b => ?_) x
  · refine ⟨0, Fin.elim0, (pullback.fst f _).appTop.hom a, ?_⟩
    rw [← appTop_comp_apply]
    exact congrArg (fun g => g.appTop.hom a) (bc_fst f i₀ (i₀.codRestrict (Lc i₀ Fin.elim0) (mem_Lc i₀ Fin.elim0)) (Lc i₀ Fin.elim0).subtype (hji_L i₀ _ (mem_Lc i₀ Fin.elim0)))
  · let c : Fin 1 → K := ![(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom b]
    refine ⟨1, c, (pullback.snd f _).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (Lc i₀ c))).inv.hom ⟨c 0, mem_Lc' i₀ c 0⟩), ?_⟩
    rw [← appTop_comp_apply]
    rw [show hc f i₀ c ≫ pullback.snd f _ = pullback.snd f (spMap i₀) ≫ spMap (Lc i₀ c).subtype from
      bc_snd f i₀ (i₀.codRestrict (Lc i₀ c) (mem_Lc i₀ c)) (Lc i₀ c).subtype (hji_L i₀ _ (mem_Lc i₀ c)), appTop_comp_apply, appTop_spMap_inv]
    change (pullback.snd f (spMap i₀)).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom b)) = _
    simp

theorem preconnectedSpace_of_finGen : ∀ (F : Type) [Field F] (X : Scheme.{0}) (f : X ⟶ Sp F),
    QuasiCompact f → QuasiSeparated f →
      ∀ (K : Type) [Field K] (i₀ : F →+* K),
        (∀ (L : Subfield K) (hL : ∀ x, i₀ x ∈ L) (n : ℕ) (c : Fin n → K),
          L = Subfield.closure (Set.range i₀ ∪ Set.range c) →
          PreconnectedSpace (pullback f (spMap (i₀.codRestrict L hL)) : Scheme.{0})) →
        PreconnectedSpace (pullback f (spMap i₀) : Scheme.{0}) := by
  intro F _ X f _ _ K _ i₀ hyp
  haveI : Flat f := flat_spec_field f
  refine preconnectedSpace_iff_clopen.2 fun U hU => ?_
  obtain ⟨e, he, hUe⟩ := GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen _ U hU
  obtain ⟨n, c, y, rfl⟩ := gen f i₀ e
  have hinj : Function.Injective (hc f i₀ c).appTop.hom :=
    ProperFunctions.injective_appTop_of_isPullback (isPullback_bc f i₀ (i₀.codRestrict (Lc i₀ c) (mem_Lc i₀ c)) (Lc i₀ c).subtype (hji_L i₀ _ (mem_Lc i₀ c)))
      (appTop_spMap_injective _ (Lc i₀ c).subtype.injective)
  have hy : IsIdempotentElem y := hinj (by rw [map_mul]; exact he)
  have hcl : IsClopen (SetLike.coe (Scheme.basicOpen _ y)) :=
    ⟨isClosed_basicOpen_idem hy, (Scheme.basicOpen _ y).isOpen⟩
  haveI := hyp (Lc i₀ c) (mem_Lc i₀ c) n c rfl
  have hU' : U = (hc f i₀ c) ⁻¹' (SetLike.coe (Scheme.basicOpen _ y)) := by
    rw [← hUe, ← Scheme.preimage_basicOpen_top]; rfl
  rcases isClopen_iff.1 hcl with h0 | h1
  · left; rw [hU', h0]; rfl
  · right; rw [hU', h1]; rfl

end GlobalTheory.GeomConnDesc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.E8Fibration

theorem isPPFib_baseChange : ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] (g : ℕ) (M : RigLB G), E8Fibration.IsPPFib G g M → ∃ M' : RigLB ((Over.pullback f).obj G), M'.L = M.L.pull (pullback.fst G.hom f) ∧ E8Fibration.IsPPFib ((Over.pullback f).obj G) g M' := by
  intro S S' f G _ g M hM
  obtain ⟨hA, hg, ⟨c⟩, ha, hK⟩ := hM
  have hA' : IsAbelianScheme ((Over.pullback f).obj G) := by
    have := hA.comm
    have := hA.smooth
    have := hA.proper
    have := hA.geomConnected
    refine ⟨inferInstance, ?_, ?_, ?_⟩
    · change Smooth (pullback.snd G.hom f)
      infer_instance
    · change IsProper (pullback.snd G.hom f)
      infer_instance
    · change GeometricallyConnected (pullback.snd G.hom f)
      infer_instance
  have := hA.comm
  have := hA'.comm
  have := hA.proper
  have h := isGrpPullback_pullback G f
  obtain ⟨hL, hr, c', -⟩ := GlobalTheory.PullSharp.cube_pull_sharp (ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubeMapOf h) M c
  obtain ⟨w, hw⟩ := GlobalTheory.PolBaseChange.lbIso_refl hL
  exact ⟨(ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubeMapOf h).rigLB M hL hr, rfl, hA',
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 hg, ⟨c'⟩,
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback M.isLB ha h.1,
    kTriv_pull h M.isLB hL ((isGen_iff w).1 hw) hK⟩

end GlobalTheory.Poinc.Sep.E8Fibration

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientPointCharacterValuePowIsUnitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientPoint_characterValue_pow_isUnit : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Subring F) [IsLocalRing T] (φ₁ : R →+* T), (∀ r, (φ₁ r : F) = algebraMap (FractionRing R) F (algebraMap R _ r)) → ∀ (J₀ : D.P.A.left → D.P.L.ι), (∀ x, x ∈ D.P.L.U (J₀ x)) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → (∀ ψ : Sp T ⟶ D.P.A.left, J (spMap T.subtype ≫ ψ) = J₀ (ψ (closedPoint T))) → (∀ χ, ∃ u : Tˣ, (GlobalTheory.BXOf.sig F (val (D.psi χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F) J) : F) = ((u : T) : F)) → ∀ (k : ℕ) (p : QkPt D F k) (b : Sp T ⟶ D.P.A.left), spMap T.subtype ≫ b = p.g.b.left → b ≫ D.P.A.hom = spMap φ₁ → ∀ χ, ∃ u : Tˣ, (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal p.g χ (closedPoint F) J) : F) ^ k = ((u : T) : F) := by
  first | exact @GlobalTheory.UnramCharPow.charVal_pow_unit | exact GlobalTheory.UnramCharPow.charVal_pow_unit | (intros; apply GlobalTheory.UnramCharPow.charVal_pow_unit <;> assumption)
end

