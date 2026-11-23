module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecMInvariantEqBotOrUnivAtGeometricPoint
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeDescentSmoothDimension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.FieldDescentAb

set_option backward.isDefEq.respectTransparency.types false

theorem fpqc_spMap {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (spMap i) := by
  refine ⟨⟨⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩, ?_⟩, inferInstance⟩
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact RingHom.Flat.of_isField (Field.toIsField K₀) _

theorem isSeparated_of_isPullback {X Y S T : Scheme.{0}} {f : T ⟶ S} {g : Y ⟶ X}
    {p : X ⟶ S} {q : Y ⟶ T} (H : IsPullback g q p f)
    (hf : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) f)
    [IsSeparated q] : IsSeparated p := by
  have h : (MorphismProperty.diagonal @UniversallyClosed) p :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.diagonal @UniversallyClosed) H.flip hf
      (show UniversallyClosed (pullback.diagonal q) from inferInstance)
  have h' : UniversallyClosed (pullback.diagonal p) := h
  exact ⟨IsClosedImmersion.of_isPreimmersion _ (pullback.diagonal p).isClosedMap.isClosed_range⟩

theorem geometricallyConnected_of_isPullback {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K)
    {X Y : Scheme.{0}} {g : Y ⟶ X} {p : X ⟶ Sp K₀} {q : Y ⟶ Sp K}
    (H : IsPullback g q p (spMap i)) [hq : GeometricallyConnected q] :
    GeometricallyConnected p := by
  refine ⟨fun K' _ y Z fst snd h => ?_⟩
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective y
  obtain ⟨Ω, _, _, j, j', e⟩ := GlobalTheory.exists_algClosed_join_of_two_field_extensions K₀ K K' i ψ.hom
  have e' : spMap j ≫ spMap i = spMap j' ≫ Spec.map ψ := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext e
  have h₁ : IsPullback (pullback.fst snd (spMap j') ≫ fst) (pullback.snd snd (spMap j')) p
      (spMap j ≫ spMap i) := by
    rw [e']
    exact (IsPullback.of_hasPullback snd (spMap j')).paste_horiz h
  have h₂ : IsPullback (H.lift (pullback.fst snd (spMap j') ≫ fst)
      (pullback.snd snd (spMap j') ≫ spMap j) (by rw [h₁.w, Category.assoc]))
      (pullback.snd snd (spMap j')) q (spMap j) :=
    IsPullback.of_right (by rw [H.lift_fst]; exact h₁) (H.lift_snd _ _ _) H
  have hc : ConnectedSpace ↥(pullback snd (spMap j')) :=
    hq.geometrically_connectedSpace _ _ _ h₂
  have : Surjective (spMap j') := (fpqc_spMap j').1.1
  exact (pullback.fst snd (spMap j')).surjective.connectedSpace
    (pullback.fst snd (spMap j')).continuous

theorem isCommMonObj_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} (A₀ : Over S)
    (A : Over S') [GrpObj A₀] [GrpObj A] {φ : A.left ⟶ A₀.left} (H : IsGrpPullback A A₀ f φ)
    [Flat f] [Surjective f] [IsCommMonObj A] : IsCommMonObj A₀ := by
  have key : ∀ (T₀ : Over S) (x₀ y₀ : T₀ ⟶ A₀), x₀ * y₀ = y₀ * x₀ := by
    intro T₀ x₀ y₀
    let T : Over S' := Over.mk (pullback.snd T₀.hom f)
    let r : Over.mk (T.hom ≫ f) ⟶ T₀ :=
      Over.homMk (pullback.fst T₀.hom f) pullback.condition
    let up : (T₀ ⟶ A₀) → (T ⟶ A) := fun x => Over.homMk
      (H.1.lift (pullback.fst T₀.hom f ≫ x.left) (pullback.snd T₀.hom f)
        (by rw [Category.assoc, Over.w x, pullback.condition])) (H.1.lift_snd _ _ _)
    have hup : ∀ x : T₀ ⟶ A₀, (r ≫ x).left = (up x).left ≫ φ := fun x =>
      (H.1.lift_fst _ _ _).symm
    have h₁ := H.2 T (up x₀) (up y₀) _ _ (hup x₀) (hup y₀)
    have h₂ := H.2 T (up y₀) (up x₀) _ _ (hup y₀) (hup x₀)
    rw [mul_comm (up y₀), ← h₁, ← MonObj.comp_mul, ← MonObj.comp_mul] at h₂
    have : Epi (pullback.fst T₀.hom f) := Flat.epi_of_flat_of_surjective _
    ext1
    rw [← cancel_epi (pullback.fst T₀.hom f)]
    exact h₂.symm
  constructor
  have := key _ (fst A₀ A₀) (snd A₀ A₀)
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, lift_snd_fst] at this
  exact this.symm

theorem isAbelianScheme_and_relDim_descend : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A₀] [GrpObj A] (φ : A.left ⟶ A₀.left), IsGrpPullback A A₀ (spMap i) φ → IsAbelianScheme A → IsAbelianScheme A₀ ∧ ∀ g : ℕ, SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g A₀.hom := by
  intro K₀ K _ _ i A₀ A _ _ φ H hA
  have hf := fpqc_spMap i
  have := hf.1.1
  have := hf.1.2
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have hsep : IsSeparated A₀.hom := isSeparated_of_isPullback H.1 hf
  have huc : UniversallyClosed A₀.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) H.1.flip hf
      inferInstance
  have hsm : Smooth A₀.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) H.1.flip hf inferInstance
  have h₀ : IsAbelianScheme A₀ :=
    { comm := isCommMonObj_of_isGrpPullback A₀ A H
      smooth := hsm
      proper := {}
      geomConnected := geometricallyConnected_of_isPullback i H.1 }
  refine ⟨h₀, fun g hg => ?_⟩
  obtain ⟨g', hg'⟩ := GlobalTheory.AbelianDim.exists_relDim K₀ A₀ h₀
  have h' : SmoothOfRelativeDimension g' A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback H.1 hg'
  obtain ⟨x, -⟩ := A.hom.surjective (Nonempty.some inferInstance)
  rw [ReciprocityTheory.ChartRestriction.G.H1.dim_unique A.hom hg h' x]
  exact hg'

end GlobalTheory.FieldDescentAb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EmbeddingSectionsSpanGeometricFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.EmbSpan

open ReciprocityTheory.ChartRestriction.G.Out

theorem pt_pow_and_surjective (hL : Laws) {S S' : Scheme.{0}} [IsLocallyNoetherian S'] (P : PolAV S) (f : S' ⟶ S)
    (n : ℕ) (hn : 1 ≤ n) : (∀ θ : ThetaGrp P.A P.L n (Over.mk f), θ.pt ^ n = 1) ∧
      Surjective (mulT P.A (Over.mk f) n).left := by
  obtain ⟨P', g, hg, -, hmul, hiso⟩ := hL.polBaseChange S S' f P
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  have hw' := (isGen_iff w).1 hw
  obtain ⟨h, k, hk, -, hs, hf, -⟩ := GeomPointSections.exists_totalIso hg hmul
  let Φ : ∀ T : Over S', (T ⟶ P'.A) →* (Over.mk (T.hom ≫ f) ⟶ P.A) := fun T =>
    MonoidHom.mk' (toBase hg.w) (hmul T)
  have c' : (fst (baseOver S') P'.A).left = (baseOver S' ⊗ P'.A).hom :=
    (Category.comp_id _).symm.trans (Over.w (fst (baseOver S') P'.A))
  let H : Over.mk ((baseOver S' ⊗ P'.A).hom ≫ f) ⟶ Over.mk f ⊗ P.A := Over.homMk h (by
    have e := Over.w (fst (Over.mk f) P.A)
    exact (congrArg (h ≫ ·) e.symm).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ f) (hf.trans c'))))
  have Hs : H ≫ snd (Over.mk f) P.A = Φ _ (snd (baseOver S') P'.A) := Over.OverMorphism.ext hs.symm
  constructor
  · intro θ
    have sq : θ.pt.left ≫ P.A.hom = 𝟙 S' ≫ f := (Over.w θ.pt).trans (Category.id_comp f).symm
    let x' : baseOver S' ⟶ P'.A := Over.homMk (hg.lift _ _ sq) (hg.lift_snd _ _ _)
    have ex : x'.left ≫ g = θ.pt.left := hg.lift_fst _ _ _
    have e₀ : H ≫ fst (Over.mk f) P.A ≫ θ.pt = Φ _ (fst (baseOver S') P'.A ≫ x') :=
      Over.OverMorphism.ext ((Category.assoc h _ _).symm.trans ((congrArg₂ (· ≫ ·) hf ex.symm).trans
        (Category.assoc _ _ _).symm))
    have e₁ : H ≫ translPt P.A θ.pt = Φ _ (translPt P'.A x') := by
      refine (MonObj.comp_mul H (fst (Over.mk f) P.A ≫ θ.pt) (snd (Over.mk f) P.A)).trans
        (Eq.trans ?_ (map_mul (Φ _) (fst (baseOver S') P'.A ≫ x') (snd (baseOver S') P'.A)).symm)
      rw [e₀, Hs]
    have e₂ : h ≫ (translPt P.A θ.pt).left = (translPt P'.A x').left ≫ g := congrArg (fun q => q.left) e₁
    obtain ⟨t₁, h₁⟩ := KerPow.HasGen.pull (L := P.L)
      (φ := ![(snd (Over.mk f) P.A).left, (translPt P.A θ.pt).left]) (ε := ![(n : ℤ), -n]) ⟨θ.φ, θ.isGen⟩ h
      (φ' := fun i => ![(snd (baseOver S') P'.A).left, (translPt P'.A x').left] i ≫ g)
      (fun i => by fin_cases i; exacts [hs.symm, e₂])
    obtain ⟨t₂, h₂⟩ := exists_down hw' P.isLB P'.isLB t₁ h₁
    have hx : x' ^ n = 1 := (hL.kerPow S' P' n hn _ x').1 fun _ =>
      ⟨⊤, trivial, _, LB.isGen_genPull _ t₂ h₂ _⟩
    let j : Over.mk ((baseOver S').hom ≫ f) ⟶ Over.mk f := Over.homMk (𝟙 S') rfl
    have ej : j ≫ θ.pt = Φ _ x' := Over.OverMorphism.ext ((Category.id_comp _).trans ex.symm)
    have : j ≫ θ.pt ^ n = j ≫ 1 := by
      rw [MonObj.comp_pow, ej, ← map_pow, hx, map_one, MonObj.comp_one]
    exact Over.OverMorphism.ext ((Category.id_comp _).symm.trans
      ((congrArg (fun q => q.left) this).trans (Category.id_comp _)))
  · have s₁ := VVRank.surjective_mulT P'.A n (hL.mulN S' P' n hn).2.2.1 (baseOver S')
    have s₂ : Surjective h := by
      have : Surjective (k ≫ h) := by rw [hk]; infer_instance
      exact Surjective.of_comp k h
    have t₁ : (mulT P.A (Over.mk f) n).left ≫ (fst (Over.mk f) P.A).left = (fst (Over.mk f) P.A).left :=
      congrArg (fun q => q.left) (lift_fst (fst (Over.mk f) P.A) (snd (Over.mk f) P.A ^ n))
    have t₂ : (mulT P.A (Over.mk f) n).left ≫ (snd (Over.mk f) P.A).left = (snd (Over.mk f) P.A ^ n).left :=
      congrArg (fun q => q.left) (lift_snd (fst (Over.mk f) P.A) (snd (Over.mk f) P.A ^ n))
    have t₁' : (mulT P'.A (baseOver S') n).left ≫ (fst (baseOver S') P'.A).left = (fst (baseOver S') P'.A).left :=
      congrArg (fun q => q.left) (lift_fst (fst (baseOver S') P'.A) (snd (baseOver S') P'.A ^ n))
    have t₂' : (mulT P'.A (baseOver S') n).left ≫ (snd (baseOver S') P'.A).left =
        (snd (baseOver S') P'.A ^ n).left :=
      congrArg (fun q => q.left) (lift_snd (fst (baseOver S') P'.A) (snd (baseOver S') P'.A ^ n))
    have e₁ : H ≫ snd (Over.mk f) P.A ^ n = Φ _ (snd (baseOver S') P'.A ^ n) := by
      rw [MonObj.comp_pow, Hs, map_pow]
    have e₂ : h ≫ (snd (Over.mk f) P.A ^ n).left = (snd (baseOver S') P'.A ^ n).left ≫ g :=
      congrArg (fun q => q.left) e₁
    have ext₁ : ∀ {Z : Scheme.{0}} {r r' : Z ⟶ (Over.mk f ⊗ P.A).left},
        r ≫ (fst (Over.mk f) P.A).left = r' ≫ (fst (Over.mk f) P.A).left →
        r ≫ (snd (Over.mk f) P.A).left = r' ≫ (snd (Over.mk f) P.A).left → r = r' :=
      fun e e' => pullback.hom_ext e e'
    have e : (mulT P'.A (baseOver S') n).left ≫ h = h ≫ (mulT P.A (Over.mk f) n).left := ext₁
      (by rw [Category.assoc, Category.assoc, t₁, hf, t₁'])
      (by rw [Category.assoc, Category.assoc, t₂, ← hs, ← Category.assoc, t₂', e₂])
    have : Surjective (h ≫ (mulT P.A (Over.mk f) n).left) := by rw [← e]; infer_instance
    exact Surjective.of_comp h _

theorem exists_pow_eq {G : Type} [CommGroup G] {r N u v : ℕ} (hN : N = u * v) (hN0 : N ≠ 0) (p : Fin r → G)
    (hp : ∀ i, p i ^ N = 1) (hb : ∀ y : G, y ^ N = 1 → ∃! c : Fin r → ZMod N, ∏ i, p i ^ (c i).val = y)
    (y : G) (hy : y ^ u = 1) : ∃ a : Fin r → ZMod N, (∏ i, p i ^ (a i).val) ^ v = y := by
  have : NeZero N := ⟨hN0⟩
  have hu : u ≠ 0 := fun h => hN0 (by rw [hN, h, zero_mul])
  obtain ⟨c, hc, -⟩ := hb y (by rw [hN, pow_mul, hy, one_pow])
  have h0 : (fun i => (((c i).val * u : ℕ) : ZMod N)) = 0 := by
    refine (hb 1 (one_pow _)).unique ?_ (by simp)
    rw [← hy, ← hc, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (hp i), pow_mul]
  have hd : ∀ i, v ∣ (c i).val := fun i => by
    have := (ZMod.natCast_eq_zero_iff _ _).1 (congrFun h0 i)
    exact Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero hu)
      ((dvd_of_eq (hN.trans (mul_comm u v)).symm).trans this)
  refine ⟨fun i => (((c i).val / v : ℕ) : ZMod N), ?_⟩
  rw [← hc, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (hp i), ← pow_mul, Nat.div_mul_cancel (hd i)]

theorem span_eq_top (hL : Laws) {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K] [IsAlgClosed K]
    (x : Sp K ⟶ S) {k : ℤ} {n : ℕ} (hk : k = n) (h4 : 4 ≤ n) (hn : (n : K) ≠ 0) {I : Type} [Nonempty I]
    (U : I → ThetaGrp P.A P.L k (Over.mk x)) (hU : ∀ y : Over.mk x ⟶ P.A, y ^ n = 1 → ∃ c, (U c).pt = y)
    (s₁ : LB.Sec (LPow P.A P.L k (Over.mk x))) (σ : I → LB.Sec (LPow P.A P.L k (Over.mk x)))
    (hσ : ∀ c, IsActOf P.A P.L k (U c) s₁ (σ c)) (h0 : (SecM.ofSec P.A s₁ : SecM P.A P.L k (Over.mk x)) ≠ 0) :
    Submodule.span Γ((Over.mk x).left, ⊤)
      (Set.range fun c => (SecM.ofSec P.A (σ c) : SecM P.A P.L k (Over.mk x))) = ⊤ := by
  subst hk
  obtain ⟨ρ, k₁, -, k₃, k₄⟩ := thetaGrp_acts_linearly hL.globalFns S P n (Over.mk x)
  have e : (fun c => (SecM.ofSec P.A (σ c) : SecM P.A P.L n (Over.mk x))) =
      fun c => ρ (U c) (SecM.ofSec P.A s₁) := funext fun c => ((k₁ _ _ _).1 (hσ c)).symm
  rw [e]
  exact VVRank.span_translates_eq_top P.A
    ((secM_invariant_eq_bot_or_univ_at_geometric_point hL.polBaseChange).2 hL.irred S P K x n (Or.inr h4) hn) ρ k₁ k₃ k₄ U
    (fun θ => hU _ ((pt_pow_and_surjective hL P x n (by omega)).1 θ)) _ h0

theorem ne_zero_of_isGenSec (hL : Laws) {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K] [IsAlgClosed K]
    (x : Sp K ⟶ S) (th : LB.Sec (LPow P.A P.L 1 (Over.mk x))) (h : IsGenSec P.A P.L 1 th) :
    (SecM.ofSec P.A th : SecM P.A P.L 1 (Over.mk x)) ≠ 0 := by
  intro h0
  have hnt : Nontrivial Γ((Over.mk x).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.domain_nontrivial
  have hr : Module.finrank Γ((Over.mk x).left, ⊤) (SecM P.A P.L 1 (Over.mk x)) = 1 ^ P.g :=
    (secM_invariant_eq_bot_or_univ_at_geometric_point hL.polBaseChange).1 hL.globalSectionsRank S P K x 1 le_rfl
  have z : ∀ v : SecM P.A P.L 1 (Over.mk x), v = 0 := fun v => by
    obtain ⟨r, hr⟩ := h (SecM.toSec P.A v)
    have : v = r • (SecM.ofSec P.A th : SecM P.A P.L 1 (Over.mk x)) := Subtype.ext (funext hr)
    rw [this, h0, smul_zero]
  have : Subsingleton (SecM P.A P.L 1 (Over.mk x)) := ⟨fun a b => (z a).trans (z b).symm⟩
  rw [Module.finrank_zero_of_subsingleton, one_pow] at hr
  exact zero_ne_one hr

theorem emb_span_eq_top : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) σ, Odd N' → m ∣ N' → 2 ≤ m → t.Emb m (Over.mk x) σ → Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun a => (Out.SecM.ofSec t.A (σ a) : Out.SecM t.A t.L ((m : ℤ) ^ 2) (Over.mk x))) = ⊤ := by
  rintro hL - o _ g N' J b S s t m K _ _ x σ hodd ⟨d, hd⟩ hm ⟨th, s₁, α, U, hth, -, htw, hU, hσ⟩
  have := t.ab.comm
  have hN0 : N' ≠ 0 := hodd.pos.ne'
  have hdiv : N' / m = d := by rw [hd, Nat.mul_div_cancel_left _ (by omega)]
  have hK : ((N' ^ 2 : ℕ) : K) ≠ 0 := VVRank.natCast_ne_zero (x ≫ s) (by
    simpa using b.unit.map (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom)
  have hN : N' ^ 2 = m ^ 2 * d ^ 2 := by rw [hd, mul_pow]
  refine span_eq_top hL t.pol x (n := m ^ 2) (Nat.cast_pow m 2).symm (by nlinarith)
    (fun h => hK (by rw [hN, Nat.cast_mul, h, zero_mul])) U (fun y hy => ?_) s₁ σ hσ fun h0 => ?_
  · obtain ⟨a, ha⟩ := exists_pow_eq (G := (Over.mk x ⟶ t.A)) hN (pow_ne_zero _ hN0)
      (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ t.pt i)
      (fun i => by rw [← MonObj.comp_pow, t.torsion, MonObj.comp_one])
      (fun z hz => by simpa only [linComb, List.prod_ofFn] using t.bij K x z hz) y hy
    refine ⟨a, (hU a).pt_eq.trans (Eq.trans ?_ ha)⟩
    rw [hdiv, TObj.lab, VVRank.comp_linComb, linComb, List.prod_ofFn]
    rfl
  · have hint : IsIntegral (Over.mk x ⊗ t.A).left :=
      (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ t.A.hom t.ab.smooth
        t.ab.geomConnected).geometrically_isIntegral x _ _ (IsPullback.of_hasPullback x t.A.hom).flip
    exact ne_zero_of_isGenSec hL t.pol x th hth (VVRank.ofSec_eq_zero_of_twist t.A t.isLB
      (pt_pow_and_surjective hL t.pol x m (by omega)).2 htw h0)

end GlobalTheory.EmbSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfInvariant
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.IsoDescent

variable {X X' Y Y' : Scheme.{0}}

theorem exists_gen_of_invariant (M : LB Y) (m : Y' ⟶ Y) {I : Type} (t : I → (Y' ⟶ Y')) (ht : ∀ i, t i ≫ m = m)
    (hd : ∀ (U : Y.Opens) (f : Γ(Y', m ⁻¹ᵁ U)),
      (∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), ((t i).appLE _ _ e).hom f = f) →
      ∃! g : Γ(Y, U), (m.app U).hom g = f)
    (a : ∀ j, Γ(Y', m ⁻¹ᵁ M.U j)ˣ)
    (hc : ∀ (y : Y') i j, m y ∈ M.U i → m y ∈ M.U j →
      gm (𝟙 Y') y _ (a i) = gm m y (M.U i ⊓ M.U j) (M.g i j) * gm (𝟙 Y') y _ (a j))
    (hinv : ∀ i (y : Y') j, m y ∈ M.U j → m (t i y) ∈ M.U j → gm (t i) y _ (a j) = gm (𝟙 Y') y _ (a j)) :
    ∃ v : LB.Gen M, v.IsGen := by
  have hinj : ∀ U : Y.Opens, Function.Injective (m.app U).hom := by
    intro U g g' h
    refine (hd U ((m.app U).hom g) fun i e => fn_ext fun y hy => ?_).unique rfl h.symm
    refine (gs_res (𝟙 Y') y e hy _).trans ((gs_pull (𝟙 Y') (t i) y (m ⁻¹ᵁ U) (e hy) _).trans
      ((gs_pull (𝟙 Y' ≫ t i) m y U (e hy) _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') m y _ hy _).symm)))
    rw [Category.assoc, ht]
  have hunit : ∀ (U : Y.Opens) (a : Γ(Y', m ⁻¹ᵁ U)ˣ),
      (∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), res e (pullU (t i) _ a) = a) →
      ∃ b : Γ(Y, U)ˣ, pullU m U b = a := by
    intro U a ha
    obtain ⟨g, hg, -⟩ := hd U a.val fun i e => congrArg Units.val (ha i e)
    obtain ⟨g', hg', -⟩ := hd U (a⁻¹).val fun i e => congrArg Units.val
      (show res e (pullU (t i) _ a⁻¹) = a⁻¹ by rw [map_inv, map_inv, ha i e])
    have h1 : g * g' = 1 := hinj U (by rw [map_mul, map_one, hg, hg']; exact a.mul_inv)
    exact ⟨⟨g, g', h1, (mul_comm _ _).trans h1⟩, Units.ext hg⟩
  have hex : ∀ j, ∃ b : Γ(Y, M.U j)ˣ, pullU m _ b = a j := by
    intro j
    refine hunit _ _ fun i e => unit_ext fun y hy => ?_
    refine (gm_res (𝟙 Y') y e hy _).trans ((gm_pull (𝟙 Y') (t i) y (m ⁻¹ᵁ M.U j) (e hy) _).trans ?_)
    rw [Category.id_comp]
    exact hinv i y j hy (e hy)
  choose b hb using hex
  refine ⟨⟨b⟩, fun i j => Units.ext (hinj _ (congrArg Units.val
    (show pullU m _ _ = pullU m _ _ from unit_ext fun y hy => ?_)))⟩
  have val : ∀ j, y ∈ m ⁻¹ᵁ M.U j → gm (𝟙 Y' ≫ m) y _ (b j) = gm (𝟙 Y') y _ (a j) := fun j hj =>
    (gm_pull (𝟙 Y') m y _ hj _).symm.trans (congrArg _ (hb j))
  refine (gm_pull (𝟙 Y') m y _ hy _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') m y _ hy _).symm)
  refine ((gm_res _ y _ hy _).trans (val i hy.1)).trans ((hc y i j hy.1 hy.2).trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (by rw [Category.id_comp])
    ((gm_res _ y _ hy _).trans (val j hy.2)))

variable {L : LB X} {L' : LB X'} {K K' : Type} [Fintype K] [Fintype K']

theorem lbIso_of_invariant (hL : L.IsLB) (hL' : L'.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X'))
    (ε' : K' → ℤ) (m : Y' ⟶ Y) {I : Type} (t : I → (Y' ⟶ Y')) (ht : ∀ i, t i ≫ m = m)
    (hd : ∀ (U : Y.Opens) (f : Γ(Y', m ⁻¹ᵁ U)),
      (∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), ((t i).appLE _ _ e).hom f = f) →
      ∃! g : Γ(Y, U), (m.app U).hom g = f)
    (u : LB.Gen (LB.LinComb L (fun k => m ≫ φ k) ε)) (hu : u.IsGen)
    (u' : LB.Gen (LB.LinComb L' (fun k => m ≫ φ' k) ε')) (hu' : u'.IsGen)
    (hinv : ∀ i y J J', Good L y J → Good L' y J' →
      val u' (t i) y J' * (val u (t i) y J)⁻¹ = val u' (𝟙 Y') y J' * (val u (𝟙 Y') y J)⁻¹) :
    LBIso (LB.LinComb L φ ε) (LB.LinComb L' φ' ε') := by
  have l₁ : ∀ p : (K' → L'.ι) × (K → L.ι), m ⁻¹ᵁ (LB.wchart L' φ' p.1 ⊓ LB.wchart L φ p.2) ≤
      LB.wchart L' (fun k => m ≫ φ' k) p.1 := fun p y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 k
  have l₂ : ∀ p : (K' → L'.ι) × (K → L.ι), m ⁻¹ᵁ (LB.wchart L' φ' p.1 ⊓ LB.wchart L φ p.2) ≤
      LB.wchart L (fun k => m ≫ φ k) p.2 := fun p y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k
  have v : ∀ (r : Y' ⟶ Y') (y : Y') (p : (K' → L'.ι) × (K → L.ι)),
      r y ∈ m ⁻¹ᵁ (LB.wchart L' φ' p.1 ⊓ LB.wchart L φ p.2) →
      gm r y _ (res (l₁ p) (u'.s p.1) * (res (l₂ p) (u.s p.2))⁻¹) =
        gm r y (LB.wchart L' (fun k => m ≫ φ' k) p.1) (u'.s p.1) *
          (gm r y (LB.wchart L (fun k => m ≫ φ k) p.2) (u.s p.2))⁻¹ := fun r y p h =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r y _ h _)
      ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res r y _ h _))))
  refine exists_gen_of_invariant (LB.div (LB.LinComb L' φ' ε') (LB.LinComb L φ ε)) m t ht hd
    (fun p => res (l₁ p) (u'.s p.1) * (res (l₂ p) (u.s p.2))⁻¹) (fun y p q hp hq => ?_) (fun i y p hp hp' => ?_)
  · refine (v (𝟙 Y') y p hp).trans (Eq.trans ?_ (congrArg₂ (· * ·) ((gm_div _ _ m y p q ⟨hp, hq⟩).trans
      (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb L' φ' ε' m y p.1 q.1 hp.1 hq.1)
        (gm_linComb L φ ε m y p.2 q.2 hp.2 hq.2))) (v (𝟙 Y') y q hq)).symm)
    rw [gen_trans hu' (𝟙 Y') y (l₁ p hp) (l₁ q hq), gen_trans hu (𝟙 Y') y (l₂ p hp) (l₂ q hq), mul_inv,
      mul_mul_mul_comm]
    simp only [trF, Category.id_comp]
  · choose J hJ using fun χ : Y' ⟶ X => exists_chart hL (χ y)
    choose J' hJ' using fun χ : Y' ⟶ X' => exists_chart hL' (χ y)
    have gJ : Good L y J := hJ
    have gJ' : Good L' y J' := hJ'
    refine (v (t i) y p hp').trans (Eq.trans ?_ (v (𝟙 Y') y p hp).symm)
    rw [gen_trans hu' (t i) y (l₁ p hp') (gJ'.mem _ _), gen_trans hu (t i) y (l₂ p hp') (gJ.mem _ _),
      gen_trans hu' (𝟙 Y') y (l₁ p hp) (gJ'.mem _ _), gen_trans hu (𝟙 Y') y (l₂ p hp) (gJ.mem _ _),
      mul_inv, mul_inv, mul_mul_mul_comm, mul_mul_mul_comm (trF _ _ (𝟙 Y') _ _ _)]
    refine congrArg₂ (· * ·) ?_ (hinv i y J J' gJ gJ')
    have e : ∀ {W : Scheme.{0}} (χ : Y ⟶ W), t i ≫ m ≫ χ = 𝟙 Y' ≫ m ≫ χ := fun χ => by
      rw [reassoc_of% ht i, Category.id_comp]
    exact congrArg₂ (fun a b => a * b⁻¹) (Finset.prod_congr rfl fun k _ => congrArg
      (fun ψ : Y' ⟶ X' => gm ψ y (L'.U (p.1 k) ⊓ L'.U (J' ψ)) (L'.g (p.1 k) (J' ψ)) ^ ε' k) (e (φ' k)))
      (Finset.prod_congr rfl fun k _ => congrArg
        (fun ψ : Y' ⟶ X => gm ψ y (L.U (p.2 k) ⊓ L.U (J ψ)) (L.g (p.2 k) (J ψ)) ^ ε k) (e (φ k)))

theorem lbIso_of_gens (hL : L.IsLB) (hL' : L'.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X'))
    (ε' : K' → ℤ) (u : LB.Gen (LB.LinComb L φ ε)) (hu : u.IsGen) (u' : LB.Gen (LB.LinComb L' φ' ε'))
    (hu' : u'.IsGen) : LBIso (LB.LinComb L φ ε) (LB.LinComb L' φ' ε') :=
  lbIso_of_invariant hL hL' φ ε φ' ε' (𝟙 Y) (I := PEmpty) PEmpty.elim (fun i => i.elim)
    (fun _ f _ => ⟨f, rfl, fun _ h => h⟩) _ (DVR.pullGen_isGen _ _ _ u hu (𝟙 Y)) _
    (DVR.pullGen_isGen _ _ _ u' hu' (𝟙 Y)) (fun i => i.elim)

def chartPullDiv (M N : LB Y) (f : Y' ⟶ Y) :
    ChartPull ((LB.div M N).pull f) (LB.div (M.pull f) (N.pull f)) (𝟙 Y') :=
  have le : ∀ J : PUnit → M.ι × N.ι, ((LB.div M N).pull f).U J ≤
      (M.pull f).U (fun _ => (J PUnit.unit).1) ⊓ (N.pull f).U (fun _ => (J PUnit.unit).2) := fun J y hy =>
    ⟨mem_pull.2 ((mem_pull (L := LB.div M N)).1 hy).1, mem_pull.2 ((mem_pull (L := LB.div M N)).1 hy).2⟩
  { idx := fun J => (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
    le := le
    g := fun y J J' hJ hJ' => by
      refine (gm_pull_g (LB.div M N) f (𝟙 Y') y J J' hJ hJ').trans ((gm_div N M (𝟙 Y' ≫ f) y _ _
        ⟨(mem_pull (L := LB.div M N)).1 hJ, (mem_pull (L := LB.div M N)).1 hJ'⟩).trans (Eq.symm ((gm_div (N.pull f) (M.pull f) (𝟙 Y') y
          (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
          (fun _ => (J' PUnit.unit).1, fun _ => (J' PUnit.unit).2) ⟨le J hJ, le J' hJ'⟩).trans ?_)))
      exact congrArg₂ (fun a b => a * b⁻¹) (gm_pull_g M f (𝟙 Y') y _ _ (le J hJ).1 (le J' hJ').1)
        (gm_pull_g N f (𝟙 Y') y _ _ (le J hJ).2 (le J' hJ').2) }

def chartPullFlat (L : LB X) (F : X' ⟶ X) (e : ℤ) (ψ : K → (Y ⟶ X')) (ε : K → ℤ) (f : Y' ⟶ Y) :
    ChartPull ((LB.LinComb (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε).pull f)
      (LB.LinComb L (fun k => f ≫ ψ k ≫ F) (fun k => ε k * e)) (𝟙 Y') :=
  have mem : ∀ (J : PUnit → K → PUnit → L.ι) (y : Y'),
      y ∈ ((LB.LinComb (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε).pull f).U J →
      ∀ k, ψ k (f y) ∈ LB.wchart L (fun _ : PUnit => F) (J PUnit.unit k) := fun J y hy k =>
    Set.mem_iInter.1 ((mem_pull (L := LB.LinComb (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε)).1 hy) k
  have le : ∀ J : PUnit → K → PUnit → L.ι,
      ((LB.LinComb (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε).pull f).U J ≤
        LB.wchart L (fun k => f ≫ ψ k ≫ F) (fun k => J PUnit.unit k PUnit.unit) := fun J y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 (mem J y hy k) PUnit.unit
  { idx := fun J k => J PUnit.unit k PUnit.unit
    le := le
    g := fun y J J' hJ hJ' => by
      refine (gm_pull_g _ f (𝟙 Y') y J J' hJ hJ').trans ((gm_linComb
        (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε (𝟙 Y' ≫ f) y (J PUnit.unit) (J' PUnit.unit)
        (Set.mem_iInter.2 (mem J y hJ)) (Set.mem_iInter.2 (mem J' y hJ'))).trans (Eq.trans
          (Finset.prod_congr rfl fun k _ => ?_) (gm_linComb L _ _ (𝟙 Y') y _ _ (le J hJ) (le J' hJ')).symm))
      refine (congrArg (· ^ ε k) (gm_linComb L (fun _ : PUnit => F) (fun _ => e) ((𝟙 Y' ≫ f) ≫ ψ k) y _ _
        (mem J y hJ k) (mem J' y hJ' k))).trans ?_
      rw [Fintype.prod_unique, ← zpow_mul, mul_comm e]
      simp only [Category.assoc] }

theorem exists_gen_div_pull {W : Scheme.{0}} (L : LB X) (L' : LB X') (F : W ⟶ X) (F' : W ⟶ X') (e e' : ℤ)
    (ψ : K → (Y ⟶ W)) (ε : K → ℤ) (f : Y' ⟶ Y)
    (H : LBIso (LB.LinComb L (fun k => f ≫ ψ k ≫ F) (fun k => ε k * e))
      (LB.LinComb L' (fun k => f ≫ ψ k ≫ F') (fun k => ε k * e'))) :
    ∃ t : LB.Gen ((LB.div (LB.LinComb (LB.LinComb L' (K := PUnit) (fun _ => F') (fun _ => e')) ψ ε)
      (LB.LinComb (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε)).pull f), t.IsGen := by
  obtain ⟨w, hw⟩ := H.chartPull (chartPullFlat L F e ψ ε f) (chartPullFlat L' F' e' ψ ε f)
  exact gen_chartPull (chartPullDiv _ _ f) w hw

end GlobalTheory.IsoDescent
end
end

