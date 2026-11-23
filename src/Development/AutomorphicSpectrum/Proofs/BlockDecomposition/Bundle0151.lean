module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0118
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0145
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0129
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0146
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemOfMk
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0120
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0117
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0140
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativeFormsMapMemSpan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0138
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0122
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0125
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.TopologicalKrullDimLeOfIrreducibleCloseds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeResApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NaturalDegreeZeroHomologyIso
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0136
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0141
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0148
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartPropertyPropagates
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeSite

theorem wK_rel : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {N m : ℕ}
    (i : X ⟶ PSpace K N) (y : Fin m → MvPolynomial (Fin (N + 1)) K) (s : ℕ) (k : Fin m) ⦃T T' : Thick (smFun X q)⦄,
    (T ⟶ T') → wK q i y s k T → (∃ β, wK q i y s β T') → wK q i y s k T' := by
  intro K _ X q N m i y s k T T' φ h h'
  obtain ⟨β, hQ, -⟩ := h'
  obtain ⟨-, V, hV, hT⟩ := h
  exact ⟨hQ, V, hV, GlobalTheory.CompanionTheory.ThickPt.inU_map V φ hT⟩

end GlobalTheory.CompanionTheory.ConeSite
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocycleOnProductFromSecondFactorStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_on_product_from_second_factor : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), USt F →
    ∀ f : Z1 (box F), (∀ (a a' b : C) (φ : a ⟶ a'), f.1 (a, b) (a', b) (φ, 𝟙 b) = 0) →
      ∃ y : Z1 F, (boxR F).pullbackOneCocycle y = f := by
  first | exact @GlobalTheory.CompanionTheory.Axis.exists_pull_of_vanish_fst | exact GlobalTheory.CompanionTheory.Axis.exists_pull_of_vanish_fst | (intros; apply GlobalTheory.CompanionTheory.Axis.exists_pull_of_vanish_fst <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocycleTensorCoboundaryClassZeroStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_tensor_coboundary_class_zero : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] [Finite C] [Quiver.IsThin C] (F : C ⥤ CommAlgCat.{0} R)
    (N : Type) [AddCommGroup N] [Module R N] [Module.Flat R N] (t : Z1 F ⊗[R] N) (g : ∀ T : C, F.obj T ⊗[R] N),
    (∀ (T T' : C) (φ : T ⟶ T'), (evZ F φ).rTensor N t = g T' - (mp F φ).toLinearMap.rTensor N (g T)) →
    (H1.mk F).rTensor N t = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Axis.KFlat.class_eq_zero_of_coboundary | exact GlobalTheory.CompanionTheory.Axis.KFlat.class_eq_zero_of_coboundary | (intros; apply GlobalTheory.CompanionTheory.Axis.KFlat.class_eq_zero_of_coboundary <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingOfTrivialFrame
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FramedSite

theorem cohomology_subsingleton_of_frame_zero {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}
    (E : Frame Φ 0) (F : C ⥤ ModuleCat.{0} R) (hD : Subsingleton (F.obj E.D)) (n : ℕ) :
    Subsingleton (CH.H F n) := by
  obtain ⟨-, -, hex0, hex⟩ := CrystallineSemistableComparison.P.initial F E.D (Frame.initial E)
  have key : ∀ x : CH.H F n, x = 0 := by
    intro x
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).1 x
    refine ((CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).2.1 a ha).2 ?_
    cases n with
    | zero =>
      obtain ⟨m, hm⟩ := hex0 a ha
      rw [one_smul] at hm
      have hm0 : m = 0 := Subsingleton.elim _ _
      rw [hm0, map_zero] at hm
      exact hm.symm
    | succ n =>
      obtain ⟨y, hy⟩ := hex n a ha
      rw [one_smul] at hy
      exact ⟨y, hy⟩
  exact ⟨fun x y => by rw [key x, key y]⟩

end GlobalTheory.CompanionTheory.FramedSite
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingShortExact
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Cohomology

theorem subsingleton_H_of_ses {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]
    {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R} (α : F₁ ⟶ F₂) (β : F₂ ⟶ F₃)
    (hi : ∀ T, Function.Injective (α.app T).hom)
    (he : ∀ T, Function.Exact (α.app T).hom (β.app T).hom)
    (hs : ∀ T, Function.Surjective (β.app T).hom)
    (h₂ : ∀ n, Subsingleton (CH.H F₂ n)) (h₃ : ∀ n, Subsingleton (CH.H F₃ n)) :
    ∀ n, Subsingleton (CH.H F₁ n) := by
  obtain ⟨c₁, c₂, c₃⟩ := CrystallineSemistableComparison.P.ses_cochains α β hi he hs
  obtain ⟨δ, -, hinj, -, -, hex⟩ :=
    CrystallineSemistableComparison.P.les (CH.Mor.ofNatTrans α).hom (CH.Mor.ofNatTrans β).hom c₁ c₂ c₃
  intro n
  cases n with
  | zero =>
    haveI : Subsingleton ((CH.cx F₂).H 0) := h₂ 0
    exact ⟨fun x y => hinj (Subsingleton.elim _ _)⟩
  | succ n =>
    haveI : Subsingleton ((CH.cx F₂).H (n + 1)) := h₂ (n + 1)
    haveI : Subsingleton ((CH.cx F₃).H n) := h₃ n
    have key : ∀ x : (CH.cx F₁).H (n + 1), x = 0 := fun x => by
      obtain ⟨y, rfl⟩ := (hex n x).1 (Subsingleton.elim _ _)
      rw [Subsingleton.elim y 0, map_zero]
    exact ⟨fun x y => (key x).trans (key y).symm⟩

end GlobalTheory.CompanionTheory.Cohomology
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverCupActionBasisStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_cup_action_basis : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} (str : ∀ V : X.Opens, O →+* Γ(X, V)) {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} O) {ι : Type}
    (U : ι → X.Opens) (U' : ι → ObjectProperty C) (m : ℕ) (κ : ι → Type) [∀ α, Fintype (κ α)]
    (act : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Γ(X, capO U i) →+* AddMonoid.End (HU F (capT U' i) m))
    (b : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (a : Fin (n + 1)), κ (i a) → HU F (capT U' i) m)
    (g : ∀ α β, κ α → κ β → Γ(X, U α ⊓ U β))
    (hfree : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (a : Fin (n + 1)) (h : HU F (capT U' i) m),
      ∃! f : κ (i a) → Γ(X, capO U i), h = ∑ k, act i (f k) (b i a k))
    (hstr : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (c : O) (h : HU F (capT U' i) m), act i (str _ c) h = c • h)
    (hres : ∀ (n : ℕ) (i : Fin (n + 2) → ι) (j : Fin (n + 2)) (f : Γ(X, capO U (i ∘ j.succAbove))) (h : HU F (capT U' (i ∘ j.succAbove)) m),
      (resU F (U := capT U' (i ∘ j.succAbove)) (V := capT U' i) (fun _ h _ => h _)).pull m (act (i ∘ j.succAbove) f h) =
        act i (rs (capO_comp U i j.succAbove) f) ((resU F (U := capT U' (i ∘ j.succAbove)) (V := capT U' i) (fun _ h _ => h _)).pull m h))
    (hb : ∀ (n : ℕ) (i : Fin (n + 2) → ι) (j : Fin (n + 2)) (a : Fin (n + 1)) (k : κ (i (j.succAbove a))),
      (resU F (U := capT U' (i ∘ j.succAbove)) (V := capT U' i) (fun _ h _ => h _)).pull m (b (i ∘ j.succAbove) a k) = b i (j.succAbove a) k)
    (hg : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (a a' : Fin (n + 1)) (k' : κ (i a')),
      b i a' k' = ∑ k, act i (rs (le_inf (capO_le U i a) (capO_le U i a')) (g (i a) (i a') k k')) (b i a k)),
    Nonempty (VB str U (CrystallineSemistableComparison.Pb.cechH F U' m)) := by
  first | exact @GlobalTheory.CompanionTheory.CechVB.vb_basis | exact GlobalTheory.CompanionTheory.CechVB.vb_basis | (intros; apply GlobalTheory.CompanionTheory.CechVB.vb_basis <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerFiltrationSpanPowStatement
section
open DividedPowers CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divided_power_filtration_span_pow : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (r : ℕ), pdP (Lat.γB f ξ) r = Ideal.span {f ξ ^ r} := by
  first | exact @GlobalTheory.CompanionTheory.DPFiltration.pdP_γB | exact GlobalTheory.CompanionTheory.DPFiltration.pdP_γB | (intros; apply GlobalTheory.CompanionTheory.DPFiltration.pdP_γB <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalRestrictSection
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeEval

theorem ev_rs_eq : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} (T : Thick (smFun X q))
    {V W : X.Opens} (h : V ≤ W) (hT : InU V T) (hT' : InU W T) (s : Γ(X, W)), ev T hT (rs h s) = ev T hT' s := by
  intro K _ X q T V W h hT hT' s
  have e : X.presheaf.map (homOfLE h).op ≫ (pt T).appLE V ⊤ hT = (pt T).appLE W ⊤ hT' :=
    Scheme.Hom.map_appLE _ _ _
  unfold ev rs GlobalTheory.Cris.evalAt
  rw [← e]
  rfl

end GlobalTheory.CompanionTheory.ConeEval
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTheta
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4
open CrystallineSemistableComparison.Onto

variable {K : Type} [Field K] {n d : ℕ}

theorem exists_theta {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) :
    ∃ (θ : ∀ S, R0 K n d S →ₐ[K] C.R S) (hθ : ∀ S b, θ S (poly n K S b) = toR C S (phi C b)),
      (∀ {S T : Finset (Fin d)} (h : S ⊆ T) y, C.res h (θ S y) = θ T (incl (cone_mono h) y)) ∧
      ∀ S, IsBaseChange (Aa C) (thetaLin C (θ S) (hθ S)) := by
  have key : ∀ S, ∃ (θ : R0 K n d S →ₐ[K] C.R S) (hθ : ∀ b, θ (poly n K S b) = toR C S (phi C b)),
      IsBaseChange (Aa C) (thetaLin C θ hθ) := by
    intro S
    rcases S.eq_empty_or_nonempty with rfl | ⟨k, hk⟩
    · exact _root_.GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaEmpty.theta_empty C
    · obtain ⟨θ₁, h₁, hu, hb⟩ := _root_.GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaOne.theta_one C k
      exact _root_.GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaLoc.theta_loc C S k hk θ₁ h₁ hu hb
  choose θ hθ bc using key
  refine ⟨θ, hθ, ?_, bc⟩
  intro S T h y
  have := GlobalTheory.T.chart_base_change_map_unique C ((C.res h).comp (θ S)) ((θ T).comp (incl (cone_mono h)))
    (fun b => by rw [AlgHom.comp_apply, hθ, res_toR]) (fun b => by rw [AlgHom.comp_apply, incl_poly h, hθ]) (θ T) (hθ T) (bc T)
  exact DFunLike.congr_fun this y

theorem Tset_ne_univ (g : Gam n d) (D : Finset (E n d)) (h : good g D) : Tset g D ≠ Finset.univ := by
  intro hu
  have hneg : ∀ j, g (Sum.inr j) ≤ 0 := fun j => by
    have : j ∈ Tset g D := hu ▸ Finset.mem_univ j
    rcases (Finset.mem_filter.1 this).2 with h | h
    · exact h.le
    · exact h.1.le
  have : tdeg g ≤ 0 := Finset.sum_nonpos fun j _ => hneg j
  have := h.2
  omega

theorem model_ex (a : ℕ) : ExP (fun S : Finset (Fin d) => relOm K (I0 n K S) a)
    (fun {S T} h => relMap (incl (cone_mono h)) (cone_ideal_map_mono (S := S) (T := T) h) a) := by
  obtain ⟨b, hb⟩ := _root_.GlobalTheory.CompanionTheory.SurjectionOntoH4.BasisW.monW_basis (K := K) (n := n) (d := d) a
  refine _root_.GlobalTheory.CompanionTheory.SurjectionOntoH4.Exc.exP_of_basis (K := K) b (fun p => good p.1 p.2.1) (fun p => Tset p.1 p.2.1) (fun p h => Tset_ne_univ _ _ h) _ _
    (fun S => ((omMap (K := K) (incl (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)) a).toAddMonoidHom).comp
      (relOm K (I0 n K S) a).subtype.toAddMonoidHom) ?_ ?_ ?_
  · intro S x y hxy
    exact Subtype.ext (GlobalTheory.T.cone_forms_map_injective S a hxy)
  · intro S S' h x
    change omMap _ a (omMap _ a (x : Om K (R0 K n d S) a)) = omMap _ a (x : Om K (R0 K n d S) a)
    rw [omMap_comp, incl_comp]
  · intro S w
    have hset : (b '' {l | good l.1 l.2.1 ∧ Tset l.1 l.2.1 ⊆ S}) =
        {w | ∃ (g : Gam n d) (D : {D : Finset (E n d) // D.card = a}), good g D.1 ∧ Tset g D.1 ⊆ S ∧ w = monW K g D} := by
      ext w
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p.1, p.2, hp.1, hp.2, hb p⟩
      · rintro ⟨g, D, h1, h2, rfl⟩
        exact ⟨(g, D), ⟨h1, h2⟩, hb _⟩
    rw [hset]
    constructor
    · rintro ⟨x, rfl⟩
      exact _root_.GlobalTheory.CompanionTheory.SurjectionOntoH4.RelSub.relOm_image_mem_span S a _ x.2
    · intro hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨g, D, h1, h2, rfl⟩ := hw
        obtain ⟨ω, hω, e⟩ := GlobalTheory.T.monomial_form_in_relative_image (K := K) S a g D h1 h2
        exact ⟨⟨ω, hω⟩, e⟩
      | zero => exact ⟨0, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨x', rfl⟩ := hx
        obtain ⟨y', rfl⟩ := hy
        exact ⟨x' + y', map_add _ _ _⟩
      | smul c x _ hx =>
        obtain ⟨x', rfl⟩ := hx
        exact ⟨c • x', map_smul (omMap (K := K) (incl (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)) a) c _⟩

theorem h4a : ChartFormsCechExact := by
  intro K _ _ A _ _ n d hd C a P e he
  obtain ⟨θ, hθ, nat, bc⟩ := exists_theta C
  haveI := etale_Aa C
  have h1 := model_ex (K := K) (n := n) (d := d) a
  have h2 : ExP (fun S => relA C S a) (fun {S T} h => relMap (C.res h) (res_mem_I C (S := S) (T := T) h) a) := by
    refine _root_.GlobalTheory.CompanionTheory.SurjectionOntoH4.ExFlat.exP_flat (B := Bp K n d) (A := Aa C) (fun S => relOm K (I0 n K S) a) (fun S => relA C S a) _ ?_ _ ?_
      (fun S => psi C (θ S) (hθ S) a) (fun S => GlobalTheory.T.chart_forms_base_change C (θ S) (hθ S) (bc S) a) ?_ h1
    · intro S T h
      refine ⟨map_add _, fun b ω => Subtype.ext ?_⟩
      change omMap (incl (cone_mono h)) a ((b • ω : relOm K (I0 n K S) a) : Om K (R0 K n d S) a) =
        ((b • relMap (incl (cone_mono h)) (cone_ideal_map_mono h) a ω : relOm K (I0 n K T) a) : Om K (R0 K n d T) a)
      have e1 : ∀ (U : Finset (Fin d)) (ω' : relOm K (I0 n K U) a), ((b • ω' : relOm K (I0 n K U) a) : Om K (R0 K n d U) a) =
          poly n K U b • (ω' : Om K (R0 K n d U) a) := fun U ω' =>
        (algebraMap_smul (R0 K n d U) b (ω' : Om K (R0 K n d U) a)).symm
      rw [e1, e1, omMap_smul, incl_poly h]
      rfl
    · intro S T h
      refine ⟨map_add _, fun c y => Subtype.ext ?_⟩
      change omMap (C.res h) a (toR C S c • (y : relOm K (C.I S) a).1) = toR C T c • omMap (C.res h) a (y : relOm K (C.I S) a).1
      rw [omMap_smul]
      exact congrArg (· • omMap (C.res h) a (y : relOm K (C.I S) a).1) (res_toR C h c)
    · intro S T h ω
      refine Subtype.ext ?_
      change omMap (C.res h) a (omMap (θ S) a (ω : Om K (R0 K n d S) a)) =
        omMap (θ T) a (omMap (incl (cone_mono h)) a (ω : Om K (R0 K n d S) a))
      have e2 : (C.res h).comp (θ S) = (θ T).comp (incl (cone_mono h)) := AlgHom.ext fun y => nat h y
      rw [omMap_comp, omMap_comp, e2]
  refine _root_.GlobalTheory.CompanionTheory.SurjectionOntoH4.ex_of_exP P (_root_.GlobalTheory.CompanionTheory.SurjectionOntoH4.exP_of_addEquiv _ _ (fun {S T} h => relMap (C.res h) (res_mem_I C (S := S) (T := T) h) a) _
    (fun S => ((e S).symm.toAddEquiv : relA C S a ≃+ P.M S)) ?_ h2)
  intro S T h x
  apply (e T).injective
  refine Subtype.ext ?_
  have := he h ((e S).symm x)
  simp only [LinearEquiv.apply_symm_apply] at this
  have h3 := LinearEquiv.apply_symm_apply (e T) (relMap (C.res h) (res_mem_I C h) a x)
  exact (congrArg Subtype.val h3).trans this.symm

end GlobalTheory.CompanionTheory.SurjectionOntoH4
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsToCoindShortExact
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.Hodge.Nerve

theorem nerveCx_shortExact {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    (S : ShortComplex (C ⥤ ModuleCat.{0} R))
    (hS : ∀ a : C, (S.map ((evaluation _ _).obj a)).ShortExact) : (S.map nerveCx).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun p ↦ ?_
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · change Function.Exact ((nerveCx.map S.f).f p).hom ((nerveCx.map S.g).f p).hom
    have h := fun a : C ↦ (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hS a).exact
    intro y
    constructor
    · intro hy
      choose x hx using fun c : Fin (p + 1) ⥤ C ↦ (h _ (y c)).1 (congrFun hy c)
      exact ⟨x, funext hx⟩
    · rintro ⟨x, rfl⟩
      exact funext fun c ↦ (h _ _).2 ⟨x c, rfl⟩
  · change Function.Injective ((nerveCx.map S.f).f p).hom
    exact fun x y hxy ↦ funext fun c ↦ (hS _).moduleCat_injective_f (congrFun hxy c)
  · change Function.Surjective ((nerveCx.map S.g).f p).hom
    intro y
    choose x hx using fun c : Fin (p + 1) ⥤ C ↦ (hS _).moduleCat_surjective_g (y c)
    exact ⟨x, funext hx⟩

theorem cechOf_shortExact {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] {κ : Type} [LinearOrder κ] (e : κ → P)
    (S : ShortComplex (Pᵒᵖ ⥤ ModuleCat.{0} R))
    (hS : ∀ a : Pᵒᵖ, (S.map ((evaluation _ _).obj a)).ShortExact) : (S.map (cechOf e)).ShortExact := by
  refine (cechFunctor_shortExact (S.map (cubeOfFunctor e)) fun s hs ↦ ?_ : ((S.map (cubeOfFunctor e)).map (cechFunctor κ R)).ShortExact)
  have hs' : ∀ (hs : PLift s.Nonempty), _ := fun hs : PLift s.Nonempty ↦ hS (op (s.inf' hs.down e))
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · intro y
    have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hs' ⟨hs⟩).exact
    constructor
    · intro hy
      obtain ⟨x, hx⟩ := (h (y ⟨hs⟩)).1 (congrFun hy ⟨hs⟩)
      exact ⟨fun _ ↦ x, funext fun _ ↦ hx⟩
    · rintro ⟨x, rfl⟩
      exact funext fun t ↦ (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hs' t).exact _ |>.2 ⟨x t, rfl⟩
  · exact fun x y hxy ↦ funext fun t ↦ (hs' t).moduleCat_injective_f (congrFun hxy t)
  · intro y
    choose x hx using fun t : PLift s.Nonempty ↦ (hs' t).moduleCat_surjective_g (y t)
    exact ⟨x, funext hx⟩

theorem exists_toCoind_shortExact {R : Type} [CommRing R] {P : Type} [SemilatticeInf P]
    (G : Pᵒᵖ ⥤ ModuleCat.{0} R) :
    ∃ (Q : Pᵒᵖ ⥤ ModuleCat.{0} R) (p : (coind fun b ↦ G.obj (op b)) ⟶ Q) (w : toCoind G ≫ p = 0),
      ∀ a : Pᵒᵖ, ((ShortComplex.mk _ _ w).map ((evaluation _ _).obj a)).ShortExact := by
  have : Mono (toCoind G) := by
    refine (NatTrans.mono_iff_mono_app _).2 fun a ↦ (ModuleCat.mono_iff_injective _).2 fun x y h ↦ ?_
    have h1 := congrFun h ⟨a.unop, le_rfl⟩
    have e : ∀ z : G.obj a, (G.map (homOfLE (le_refl a.unop)).op).hom z = z := fun z ↦ by
      have : (homOfLE (le_refl a.unop)).op = 𝟙 a := rfl
      rw [this, G.map_id]
      rfl
    exact (e x).symm.trans (h1.trans (e y))
  have hS : (ShortComplex.mk _ _ (cokernel.condition (toCoind G))).ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  exact ⟨_, _, _, fun a ↦ hS.map_of_exact _⟩

theorem nonempty_iso {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] {κ : Type} [LinearOrder κ] (e : κ → P)
    (he : Function.Bijective e) (n : ℕ) (G : Pᵒᵖ ⥤ ModuleCat.{0} R) :
    Nonempty ((nerveCx.obj G).homology n ≅ ((cechOf e).obj G).homology n) := by
  obtain ⟨ε, h1, h2⟩ := _root_.GlobalTheory.CompanionTheory.Hodge.Nerve.DegZero.degZero (R := R) e he
  refine _root_.GlobalTheory.CompanionTheory.Hodge.DimShift.homology_nonempty_iso nerveCx (cechOf e) ε h1 h2 (fun G ↦ ?_) n G
  obtain ⟨Q, p, w, h⟩ := exists_toCoind_shortExact G
  exact ⟨_, Q, toCoind G, p, w, nerveCx_shortExact _ h, cechOf_shortExact e _ h,
    fun n ↦ ⟨_root_.GlobalTheory.CompanionTheory.Hodge.Nerve.isZero_homology_coind _ n, GlobalTheory.T.coinduced_cech_acyclic e he.2 _ n⟩⟩

set_option maxHeartbeats 1000000 in
theorem cmpSt_of_cxSt : CxSt → CmpSt := by
  intro _ R _ X s _ P _ _ S
  letI := GlobalTheory.algebraΓOfHom s
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin P
  let e' : Fin m → P := e.symm
  have he' : Function.Bijective e' := e.symm.bijective
  have hc : ⨆ i, (S.u (e' i)).1 = ⊤ := by
    rw [← S.cover]
    exact e.symm.iSup_comp (g := fun a ↦ (S.u a).1)
  have hinf : ∀ (t : Finset (Fin m)) (ht : t.Nonempty), (⨅ i ∈ t, (S.u (e' i)).1) = (S.u (t.inf' ht e')).1 := by
    intro t ht
    induction ht using Finset.Nonempty.cons_induction with
    | singleton i => simp
    | cons i t hi ht ih =>
      rw [Finset.inf'_cons ht, S.map_inf, Finset.cons_eq_insert, Finset.iInf_insert, ih]
  have hD : ∀ t : Finset (Fin m), t.Nonempty → IsAffineOpen (⨅ i ∈ t, (S.u (e' i)).1) := fun t ht ↦ by
    rw [hinf t ht]
    exact (S.u _).2
  have key : ∀ n, Nonempty ((nerveCx.obj (toMod (OSys s S))).homology n ≃ₗ[R] GlobalTheory.coh (GlobalTheory.structureModule X) n) := by
    intro n
    obtain ⟨i⟩ := nonempty_iso e' he' n (toMod (OSys s S))
    obtain ⟨f⟩ := GlobalTheory.T.cech_structure_sheaf_comparison R X s P S e' n
    letI : (GlobalTheory.structureModule X).IsQuasicoherent := GlobalTheory.QCoh.IsFiniteQC.isQuasicoherent
    exact ⟨i.toLinearEquiv ≪≫ₗ f ≪≫ₗ GlobalTheory.cechHEquivCoh R hc hD (GlobalTheory.structureModule X) n⟩
  obtain ⟨⟨a⟩, b⟩ := GlobalTheory.T.cochain_cohomology_nerve_homology_equiv (OSys s S)
  obtain ⟨k⟩ := key 0
  refine ⟨⟨a ≪≫ₗ k⟩, fun n ↦ ?_⟩
  obtain ⟨b'⟩ := b n
  obtain ⟨k'⟩ := key (n + 1)
  exact ⟨b' ≪≫ₗ k'⟩

end GlobalTheory.CompanionTheory.Hodge.Nerve
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueConstantOfCompatibleFamilyStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_constant_of_compatible_family : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (M : Type) [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (F' : C ⥤ CommAlgCat.{0} (TrivSqZeroExt R M)) (_ : BC F F'),
    Stein F' → ∀ z : ∀ T : C, M ⊗[R] F.obj T,
      (∀ (T T' : C) (φ : T ⟶ T'), z T' = (mp F φ).toLinearMap.lTensor M (z T)) →
      ∃! m : M, ∀ T, z T = m ⊗ₜ[R] (1 : F.obj T) := by
  first | exact @GlobalTheory.CompanionTheory.Axis.existsUnique_const_of_trivSqZeroExt | exact GlobalTheory.CompanionTheory.Axis.existsUnique_const_of_trivSqZeroExt | (intros; apply GlobalTheory.CompanionTheory.Axis.existsUnique_const_of_trivSqZeroExt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KrullDimQuotientEqTrdegSuccStatement
section
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.krull_dim_quotient_eq_trdeg_succ : ∀ (Y : Scheme.{0}) (B : Type) [CommRing B] [Algebra ℤ B] [Algebra.FiniteType ℤ B] (j : Spec (.of B) ⟶ Y) [IsOpenImmersion j] (q : PrimeSpectrum B), CharZero (Y.residueField (j q)) → ringKrullDim (B ⧸ q.asIdeal) = (((Algebra.trdeg ℤ (Y.residueField (j q))).toENat + 1 : ℕ∞) : WithBot ℕ∞) := by
  first | exact @GlobalTheory.CompanionTheory.DimChart.ringKrullDim_quotient_eq | exact GlobalTheory.CompanionTheory.DimChart.ringKrullDim_quotient_eq | (intros; apply GlobalTheory.CompanionTheory.DimChart.ringKrullDim_quotient_eq <;> assumption)
end

