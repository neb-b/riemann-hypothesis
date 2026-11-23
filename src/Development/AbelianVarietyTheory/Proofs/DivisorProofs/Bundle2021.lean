module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1802
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1972
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvOfHeisInv
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertVacLag

theorem inv_of_heisInv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (m : ℕ) (C : Matrix (Fin (a + a')) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), GlobalTheory.InertVacLag.IsLagrAt σ G.W v C →
    ∀ l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l →
    ∀ g ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om' (g, 1)) φ φ₁ → l φ₁ = l φ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin hv m C hC l hl g hg φ hφ φ₁ hφ₁ hA
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (F := F) (Fin a' × Fin (a + a')) v
  have htadd : ∀ f f' : (Fin a' × Fin (a + a') → Fv F v) → ℂ,
      tens (evFin F v) (f + f') R = tens (evFin F v) f R + tens (evFin F v) f' R := fun f f' => by
    funext x; simp [tens, add_mul]
  have htsmul : ∀ (c : ℂ) (f : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      tens (evFin F v) (c • f) R = c • tens (evFin F v) f R := fun c f => by
    funext x; simp [tens, mul_assoc]
  let Sop : UA σ G.V'.J → (((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ((Fin a' × Fin (a + a') → Fv F v) → ℂ)) :=
    fun g =>
    { toFun := fun f t => (R 0)⁻¹ * om' (g, 1) (tens (evFin F v) f R) (fun i => GlobalTheory.LatVac.liftV v (t i))
      map_add' := fun f f' => by
        funext t; simp only [htadd, map_add (f := _), Pi.add_apply]; ring
      map_smul' := fun c f => by
        funext t; simp only [htsmul, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hSop : ∀ g f t, Sop g f t = (R 0)⁻¹ * om' (g, 1) (tens (evFin F v) f R) (fun i => GlobalTheory.LatVac.liftV v (t i)) :=
    fun _ _ _ => rfl
  have huniq : ∀ (T : ((Fin a' × Fin (a + a') → AF F) → ℂ) → (Fin a' × Fin (a + a') → AF F) → ℂ)
      (f f₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ), f ∈ SB _ → Acts (evFin F v) T f f₁ →
      ∀ t, f₁ t = (R 0)⁻¹ * T (tens (evFin F v) f R) (fun i => GlobalTheory.LatVac.liftV v (t i)) := by
    intro T f f₁ hf hA t
    rw [hA R (hR f hf)]
    have hat : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i)) := by
      intro u hu; funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu
    have h1 : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
      simpa using (hR f hf).1 0 _ hat
    simp only [tens, h1, GlobalTheory.LatVac.evFin_liftV]
    field_simp
  have hS : ∀ g ∈ UAt σ G.V' (evFin F v), ∀ f ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      Sop g f ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧ Acts (evFin F v) (om' (g, 1)) f (Sop g f) := by
    intro g hg f hf
    obtain ⟨S₀, hS₀⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' B G X om om' hT v g hg
    have e : S₀ f = Sop g f := funext fun t => (huniq _ f _ hf (hS₀ f hf).2 t).trans (hSop g f t).symm
    rw [← e]; exact hS₀ f hf
  obtain ⟨φ₀, hφ₀, hline⟩ := GlobalTheory.T.heisenberg_invariant_form_vanishes_lagrangian_test F E σ a' (a + a') G.V' G.W G.M' B.ψ v (hT.base.inert v w hin).2.2 m C hC
  by_cases hz : ∀ f ∈ SB (Fin a' × Fin (a + a') → Fv F v), l f = 0
  · rw [hz φ₁ hφ₁, hz φ hφ]
  push_neg at hz
  have hl0 : l φ₀ ≠ 0 := fun h => by
    obtain ⟨f, hf, hne⟩ := hz; exact hne (hline l hl h f hf)
  let c : UA σ G.V'.J → ℂ := fun g => l (Sop g φ₀) / l φ₀
  have hlaw : ∀ g ∈ UAt σ G.V' (evFin F v), ∀ f ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∀ f₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (g, 1)) f f₁ → l f₁ = c g * l f := by
    intro g hg f hf f₁ hf₁ hA
    have hf₁eq : f₁ = Sop g f := funext fun t => (huniq _ f f₁ hf hA t).trans (hSop g f t).symm
    have hE := GlobalTheory.T.heisenbergInvariantForm_comp_localWeilOperator F E σ B a a' G X om om' hT v m C l hl g hg (Sop g) (hS g hg)
    have hl' : GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C (l ∘ₗ Sop g - c g • l) := by
      intro u hu f hf f₁ hf₁ hA'
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hE u hu f hf f₁ hf₁ hA', hl u hu f hf f₁ hf₁ hA']
    have h0 : (l ∘ₗ Sop g - c g • l) φ₀ = 0 := by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply, c]
      field_simp
      ring
    have h1 := hline _ hl' h0 f hf
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply] at h1
    rw [hf₁eq]
    linear_combination h1
  have hc := GlobalTheory.T.inert_place_transforming_character_eq_one F E σ B a a' G X om om' hT v w hin hv m C hC l hl hz c hlaw g hg
  rw [hlaw g hg φ hφ φ₁ hφ₁ hA, hc, one_mul]

end GlobalTheory.InertVacLag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleComponentsClopenPartition
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

open TopologicalSpace

namespace GlobalTheory.CompPart

theorem isIrreducible_generizations {Z : Scheme.{0}} (hd : ∀ x : Z, IsDomain (Z.presheaf.stalk x)) (x : Z) :
    IsIrreducible {y : Z | y ⤳ x} := by
  haveI := hd x
  rw [← Scheme.range_fromSpecStalk, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ (Spec (Z.presheaf.stalk x))).image _
    (Z.fromSpecStalk x).continuous.continuousOn

theorem eq_closure_generizations {Z : Scheme.{0}} (hd : ∀ x : Z, IsDomain (Z.presheaf.stalk x))
    {C : Set Z} (hC : C ∈ irreducibleComponents Z) {x : Z} (hx : x ∈ C) :
    C = closure {y : Z | y ⤳ x} := by
  have hcl : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  obtain ⟨η, hη⟩ := QuasiSober.sober hC.1 hcl
  have hηx : η ⤳ x := by
    rw [specializes_iff_mem_closure, hη.def]; exact hx
  have hsub : C ⊆ closure {y : Z | y ⤳ x} := by
    rw [← hη.def]
    exact closure_mono (Set.singleton_subset_iff.2 hηx)
  exact hsub.antisymm (hC.2 (isIrreducible_generizations hd x).closure hsub)

theorem existsUnique_mem {Z : Scheme.{0}} (hd : ∀ x : Z, IsDomain (Z.presheaf.stalk x)) (x : Z) :
    ∃! C : irreducibleComponents Z, x ∈ (C : Set Z) :=
  ⟨⟨_, irreducibleComponent_mem_irreducibleComponents x⟩, mem_irreducibleComponent, fun C hC =>
    Subtype.ext ((eq_closure_generizations hd C.2 hC).trans
      (eq_closure_generizations hd (irreducibleComponent_mem_irreducibleComponents x)
        mem_irreducibleComponent).symm)⟩

theorem isOpen_of_mem {Z : Scheme.{0}} [NoetherianSpace Z] (hd : ∀ x : Z, IsDomain (Z.presheaf.stalk x))
    {C : Set Z} (hC : C ∈ irreducibleComponents Z) : IsOpen C := by
  have hfin : (irreducibleComponents Z).Finite := NoetherianSpace.finite_irreducibleComponents
  have hcompl : Cᶜ = ⋃ D ∈ {D ∈ irreducibleComponents Z | D ≠ C}, D := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hy
      exact ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y,
        fun h => hy (h ▸ mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩
    · rintro ⟨D, ⟨hD, hne⟩, hyD⟩ hyC
      exact hne (congrArg Subtype.val ((existsUnique_mem hd y).unique (y₁ := ⟨D, hD⟩) (y₂ := ⟨C, hC⟩) hyD hyC))
  rw [← isClosed_compl_iff, hcompl]
  exact (hfin.subset (by exact fun D hD => hD.1)).isClosed_biUnion fun D hD =>
    isClosed_of_mem_irreducibleComponents D hD.1

end GlobalTheory.CompPart

theorem GlobalTheory.irreducibleComponents_clopen_partition : ∀ (n : ℕ) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)),
    IsProjOver z → GlobalTheory.IsNormalScheme Z → ∃ (ι : Type) (_ : Fintype ι) (W : ι → Set Z),
      (∀ c, IsClopen (W c)) ∧ (∀ c, IsIrreducible (W c)) ∧ ∀ x, ∃! c, x ∈ W c := by
  intro n Z z hz hN
  haveI : IsNoetherianRing (cycAway n) :=
    is_noetherian_subring_closure _ (Set.toFinite _)
  haveI : AlgebraicGeometry.IsNoetherian Z := GlobalTheory.isNoetherian_of_isProjOver hz
  have hd : ∀ x : Z, IsDomain (Z.presheaf.stalk x) := fun x => hN.isDomain_stalk x
  have hfin : (irreducibleComponents Z).Finite := NoetherianSpace.finite_irreducibleComponents
  exact ⟨irreducibleComponents Z, hfin.fintype, fun C => (C : Set Z),
    fun C => ⟨isClosed_of_mem_irreducibleComponents _ C.2, GlobalTheory.CompPart.isOpen_of_mem hd C.2⟩,
    fun C => C.2.1, GlobalTheory.CompPart.existsUnique_mem hd⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageAddInfPreimageSubGrpScheme
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SumAffine

theorem isIso_shear {C : Type*} [Category C] [CartesianMonoidalCategory C] (A T : C) [GrpObj A]
    (b : T ⟶ A) : IsIso (lift (fst A T * (snd A T ≫ b)) (snd A T)) := by
  refine ⟨lift (fst A T * (snd A T ≫ b⁻¹)) (snd A T), ?_, ?_⟩
  · ext
    · simp [MonObj.comp_mul, GrpObj.comp_inv, mul_assoc]
    · simp
  · ext
    · simp [MonObj.comp_mul, GrpObj.comp_inv, mul_assoc]
    · simp

theorem isAffineOpen_preimage_translate (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (V : A.left.Opens) (hV : IsAffineOpen V) (T : Over (Sp R)) [IsAffine T.left] (b : T ⟶ A) :
    IsAffineOpen ((fst A T * (snd A T ≫ b)).left ⁻¹ᵁ V) := by
  haveI : IsAffine (Sp R) := by unfold Sp; infer_instance
  haveI : IsAffineHom T.hom := inferInstance
  haveI : IsAffineHom (fst A T).left := by
    change IsAffineHom (pullback.fst A.hom T.hom)
    exact isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback A.hom T.hom).flip inferInstance
  haveI := isIso_shear A T b
  have h : fst A T * (snd A T ≫ b) = lift (fst A T * (snd A T ≫ b)) (snd A T) ≫ fst A T := by simp
  haveI : IsAffineHom (fst A T * (snd A T ≫ b)).left := by
    rw [h, Over.comp_left]
    haveI : IsIso (lift (fst A T * (snd A T ≫ b)) (snd A T)).left :=
      inferInstanceAs (IsIso ((Over.forget (Sp R)).map (lift (fst A T * (snd A T ≫ b)) (snd A T))))
    infer_instance
  exact hV.preimage _

theorem isAffineOpen_preimage_add_inf_preimage_sub (R : Type) [CommRing R] (A : Over (Sp R))
    [GrpObj A] [IsSeparated A.hom] (V : A.left.Opens) (hV : IsAffineOpen V) (T : Over (Sp R))
    [IsAffine T.left] (a : T ⟶ A) :
    IsAffineOpen ((fst A T * (snd A T ≫ a)).left ⁻¹ᵁ V ⊓
      (fst A T * (snd A T ≫ a)⁻¹).left ⁻¹ᵁ V) := by
  have h1 := isAffineOpen_preimage_translate R A V hV T a
  have h2 := isAffineOpen_preimage_translate R A V hV T a⁻¹
  rw [GrpObj.comp_inv] at h2
  haveI : IsSeparated (snd A T).left := by
    change IsSeparated (pullback.snd A.hom T.hom)
    infer_instance
  haveI : (A ⊗ T).left.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from (snd A T).left]
    infer_instance
  exact h1.inf h2

end GlobalTheory.SumAffine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCellOfIsFrameMat
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.LogPole

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

section Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X0 : Scheme.{0}}


open MonObj in
theorem isCombAtG_perm (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {m : ℕ} (p : Equiv.Perm (Fin m))
    (v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)) (cf : Fin m → S) (w : Sp (DualNumber S) ⟶ t.G.left)
    (h : IsCombAtG t x0 v cf w) : IsCombAtG t x0 (fun j => v (p j)) (fun j => cf (p j)) w := by
  obtain ⟨u, hu, hp⟩ := h
  refine ⟨fun j => u (p j), fun j => hu (p j), ?_⟩
  rw [← hp]
  letI : CommMonoid (tEpsG x0 ⟶ t.G) := Hom.commMonoid
  exact congrArg Over.Hom.left ((List.prod_ofFn (f := fun j => u (p j))).trans
    ((Equiv.prod_comp p u).trans (List.prod_ofFn (f := u)).symm))

end Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def permE {n : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (p : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) :
    (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n :=
  (Equiv.sigmaCongrRight p).trans e

theorem permE_apply {n : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
    (p : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (σ : E →+* ℂ) (j : Fin (Dw.mult σ)) :
    permE e p ⟨σ, j⟩ = e ⟨σ, p σ j⟩ := rfl

def IsFrameMat (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) {n : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left))
    (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J)
    (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) : Prop :=
  ∀ (S : Type) [CommRing S] (z : Sp S ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) (hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1)
    (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z)
    (σ : E →+* ℂ) (i : Fin (Dw.mult σ)),
    IsCombAtG TF.Y.t (z ≫ toBase TF Z)
      (fun j => spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩))
      (fun j => ev z W hz (C σ i j)) (tv (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)).left

variable {TF : TorFlag Xo c} {Z : Comp Xo c} {U : TF.Y.X.affineOpens} {n : ℕ}
  {e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n} {v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)}

theorem isEigBasis_permE (p : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (h : IsEigBasis TF U e v) :
    IsEigBasis TF U (permE e p) v :=
  ⟨h.1, h.2.1, fun a τ i => h.2.2 a τ (p τ i)⟩

theorem isFrameMat_mono {W W₀ : (Y₀ TF.X Z).Opens} (hW : W ≤ W₀) {k : TF.X.F.J}
    {C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W₀)}
    (h : IsFrameMat TF Z U e v W₀ k C) :
    IsFrameMat TF Z U e v W k (fun σ => (C σ).map (resG (Y₀ TF.X Z) hW)) := by
  intro S _ z hz hU hk hx σ i
  have hz₀ : ⊤ ≤ z ⁻¹ᵁ W₀ := FlagMod.le_preimage_mono hW hz
  have h1 := h S z hz₀ hU hk hx σ i
  have e1 : (fun j => ev z W₀ hz₀ (C σ i j)) = fun j => ev z W hz (((C σ).map (resG (Y₀ TF.X Z) hW)) i j) :=
    funext fun j => (FlagMod.ev_res z hW hz hz₀ _).symm
  rw [e1] at h1
  exact h1

theorem isFrameMat_permE (p : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) {W : (Y₀ TF.X Z).Opens} {k : TF.X.F.J}
    {C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)}
    (h : IsFrameMat TF Z U e v W k C) :
    IsFrameMat TF Z U (permE e p) v W k (fun σ => (C σ).submatrix id (p σ)) := by
  intro S _ z hz hU hk hx σ i
  simp only [permE_apply, Matrix.submatrix_apply, id]
  exact isCombAtG_perm TF.Y.t (z ≫ toBase TF Z) (p σ)
    (fun j => spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩)) (fun j => ev z W hz (C σ i j))
    (tv (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)).left (h S z hz hU hk hx σ i)

theorem isCell_of_isFrameMat {W : (Y₀ TF.X Z).Opens} {k : TF.X.F.J}
    {L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)} (hW : IsAffineOpen W)
    (hWU : W ≤ toBase TF Z ⁻¹ᵁ U.1) (hWk : W ≤ inc₀ TF.X Z ⁻¹ᵁ TF.X.F.U k) (hL : ∀ σ i j, i < j → L σ i j = 0)
    (hLd : ∀ σ i, IsUnit (L σ i i)) (hN : ∀ σ i j, j < i → N σ i j = 0) (hNd : ∀ σ i, N σ i i = 1)
    (h : IsFrameMat TF Z U e v W k fun σ => L σ * N σ) : IsCell TF Z U e v W k L N :=
  ⟨hW, hWU, hWk, hL, hLd, hN, hNd, h⟩

end GlobalTheory.LogPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacter
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharKer

variable {S : Scheme.{0}}

def pullTop {X Y : Scheme.{0}} (f : X ⟶ Y) : Γ(Y, ⊤)ˣ →* Γ(X, ⊤)ˣ := Units.map f.appTop.hom

def pmap {A A' : Over S} (q : A ⟶ A') (T : Over S) : A ⊗ T ⟶ A' ⊗ T := lift (fst A T ≫ q) (snd A T)

def actMap {A N : Over S} [GrpObj A] (i : N ⟶ A) (T : Over S) : A ⊗ (N ⊗ T) ⟶ A ⊗ T :=
  lift (fst A (N ⊗ T) * (snd A (N ⊗ T) ≫ fst N T ≫ i)) (snd A (N ⊗ T) ≫ snd N T)

def prMap (A N T : Over S) : A ⊗ (N ⊗ T) ⟶ A ⊗ T := lift (fst A (N ⊗ T)) (snd A (N ⊗ T) ≫ snd N T)

def IsCharacter {N T : Over S} [GrpObj N] (χ : Γ((N ⊗ T).left, ⊤)ˣ) : Prop :=
  pullTop (lift (fst N (N ⊗ T) * (snd N (N ⊗ T) ≫ fst N T)) (snd N (N ⊗ T) ≫ snd N T)).left χ =
    pullTop (lift (fst N (N ⊗ T)) (snd N (N ⊗ T) ≫ snd N T)).left χ * pullTop (snd N (N ⊗ T)).left χ

def IsPullGen {X Y : Scheme.{0}} (p : X ⟶ Y) (M : LB Y) (e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ) : Prop :=
  ∀ (k l : M.ι) (W : X.Opens) (h₁ : W ≤ p ⁻¹ᵁ M.U k) (h₂ : W ≤ p ⁻¹ᵁ M.U l) (h₃ : W ≤ p ⁻¹ᵁ (M.U k ⊓ M.U l)),
    res h₁ (e k) = res h₃ (pullU p _ (M.g k l)) * res h₂ (e l)

def IsEquivGen {A A' N T : Over S} [GrpObj A] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ)
    (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ) : Prop :=
  IsPullGen (pmap q T).left M e ∧
    ∀ (k : M.ι) (W : (A ⊗ (N ⊗ T)).left.Opens)
      (h₁ : W ≤ (actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k))
      (h₂ : W ≤ (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k)),
      res h₁ (pullU (actMap i T).left _ (e k)) =
        res le_top (pullTop (snd A (N ⊗ T)).left χ) * res h₂ (pullU (prMap A N T).left _ (e k))

end GlobalTheory.CharKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenGeometricPointsRootOfUnityEqUnitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClopen_geometricPoints_rootOfUnity_eq_unit : ∀ (X : Scheme.{0}) (N : ℕ) (c₀ u : Γ(X, ⊤)ˣ), IsUnit (N : Γ(X, ⊤)) → c₀ ^ N = 1 → (∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X), Units.map g.appTop.hom.toMonoidHom u ^ N = 1) → GlobalTheory.HkClopen.Loc (S := X) (fun (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X) => Units.map g.appTop.hom.toMonoidHom c₀ = Units.map g.appTop.hom.toMonoidHom u) := by
  first | exact @GlobalTheory.loc_units_eq | exact GlobalTheory.loc_units_eq | (intros; apply GlobalTheory.loc_units_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombAtZeroSectionEigenBlockFlattenedFrame
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv


attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory in
open MonObj in
theorem isCombAtG_extend {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X0 : Scheme.{0}} (t : SAB H X0) {R : Type} [CommRing R] (x : Sp R ⟶ X0) {m n : ℕ}
    (f : Fin m → Fin n) (hf : Function.Injective f)
    {v : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} {v' : Fin n → (Sp (DualNumber R) ⟶ t.G.left)}
    (hv : ∀ j, IsTanAtG t x (v' j)) {cf : Fin m → R} {cf' : Fin n → R}
    (hvf : ∀ k, v' (f k) = v k) (hcf : ∀ k, cf' (f k) = cf k) (hz : ∀ c, (¬ ∃ k, f k = c) → cf' c = 0)
    {w : Sp (DualNumber R) ⟶ t.G.left} (h : IsCombAtG t x v cf w) : IsCombAtG t x v' cf' w := by
  classical
  have h0 : spMap (epsMul (0 : R)) =
      spMap (algebraMap R (DualNumber R)) ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
    have e : epsMul (0 : R) = (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom :=
      RingHom.ext fun z => by ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
    rw [← Spec.map_comp, e]
    rfl
  obtain ⟨u, hu, hw⟩ := h
  refine ⟨Function.extend f u 1, fun c => ?_, ?_⟩
  · by_cases hc : ∃ k, f k = c
    · obtain ⟨k, rfl⟩ := hc
      rw [hf.extend_apply, hu, hvf, hcf]
    · let p : tEpsG x ⟶ Over.mk x := Over.homMk (spMap (algebraMap R (DualNumber R))) rfl
      rw [Function.extend_apply' _ _ _ hc, hz c hc, h0, Category.assoc, (hv c).2, Pi.one_apply,
        ← MonObj.comp_one p]
      rfl
  · rw [← hw]
    congr 1
    letI : CommMonoid (tEpsG x ⟶ t.G) := Hom.commMonoid
    rw [List.prod_ofFn, List.prod_ofFn]
    symm
    refine Finset.prod_of_injOn f hf.injOn (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_ ?_
    · intro c _ hc
      rw [Function.extend_apply' _ _ _ ?_, Pi.one_apply]
      rintro ⟨k, rfl⟩
      exact hc ⟨k, by simp, rfl⟩
    · intro k _
      rw [hf.extend_apply]

theorem isCombAtG_flatFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (X : Scheme.{0}) (t : SAB H X) (S : Type) [CommRing S] (x : Sp S ⟶ X) (n n' : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n') (w' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ t.G.left)) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (w : Sp (DualNumber S) ⟶ t.G.left), (∀ τ k, IsTanAtG t x (w' τ k)) → IsCombAtG t x (w' σ) (A σ i) w → IsCombAtG t x (fun c => w' (e'.symm c).1 (e'.symm c).2) (fun c => GlobalTheory.LogKSDiv.flatFrame A e e' (e ⟨σ, i⟩) c) w := by
  classical
  intro E _ _ _ H Dw X t S _ x n n' e e' w' A σ i w htan h
  refine isCombAtG_extend t x (fun k => e' ⟨σ, k⟩) (fun a b hab => ?_) (fun c => htan _ _) (fun k => ?_)
    (fun k => flatFrame_apply A e e' σ i k) (fun c hc => ?_) h
  · exact sigma_mk_injective (β := fun τ : E →+* ℂ => Fin (Dw.mult τ)) (e'.injective hab)
  · show (fun z : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => w' z.1 z.2) (e'.symm (e' ⟨σ, k⟩)) = _
    rw [Equiv.symm_apply_apply]
  · obtain ⟨⟨τ, k⟩, rfl⟩ := e'.surjective c
    have hne : σ ≠ τ := by
      rintro rfl
      exact hc ⟨k, rfl⟩
    simp [flatFrame, Matrix.blockDiagonal'_apply_ne _ _ _ hne]

end GlobalTheory.LogKSDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDVRValuationSubringComapOfFiniteDimensionalStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDVR_valuationSubring_comap_of_finiteDimensional : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V], IsDiscreteValuationRing (V.comap φ) := by
  first | exact @GlobalTheory.RestrictDVR.main | exact GlobalTheory.RestrictDVR.main | (intros; apply GlobalTheory.RestrictDVR.main <;> assumption)
end

