module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0576
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2109
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1984
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2408

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoOriginOneOfGenericOriginDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.GenOrigin

theorem jK_appTop_inj (R : Type) [CommRing R] [IsDomain R] : Function.Injective (jK R).appTop.hom := by
  have hs := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2
  have hi := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv).1
  intro x y h
  obtain ⟨a, rfl⟩ := hs x
  obtain ⟨b, rfl⟩ := hs y
  have e := fun c => congrArg (fun q => q.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  have := hi ((e a).trans (h.trans (e b).symm))
  rw [IsFractionRing.injective R (FractionRing R) this]

theorem exists_unit_along {S X X' B B' : Scheme.{0}} (M : LB B) (M' : LB B') (hM : M.IsLB) (hM' : M'.IsLB)
    {K : Type} [Fintype K] (φ : K → (X ⟶ B)) (φ' : K → (X' ⟶ B')) (ε : K → ℤ) (hε : ∑ k, ε k = 0) (F : X' ⟶ X)
    (e : S ⟶ X') (q : S ⟶ B) (q' : S ⟶ B') (hq : ∀ k, (e ≫ F) ≫ φ k = q)
    (hq' : ∀ k, e ≫ φ' k = q') (w : LB.Iso (LB.LinComb M' φ' ε) ((LB.LinComb M φ ε).pull F)) (hw : w.IsGen) :
    ∃ u : Γ(S, ⊤)ˣ, ∀ (Z : Scheme.{0}) (t : Z ⟶ S) (z : Z) (a : M.ι) (b : M'.ι), q (t z) ∈ M.U a →
      q' (t z) ∈ M'.U b → gw w (t ≫ e) z (fun _ => a) (fun _ => b) = gm t z ⊤ u := by
  let C : M.ι × M'.ι → X'.Opens := fun i =>
    ((LB.LinComb M φ ε).pull F).U (fun _ _ => i.1) ⊓ (LB.LinComb M' φ' ε).U (fun _ => i.2)
  have mem : ∀ (x : S) (a : M.ι) (b : M'.ι), q x ∈ M.U a → q' x ∈ M'.U b → e x ∈ C (a, b) := fun x a b ha hb =>
    ⟨mem_pull.2 (NormIso.mem_const M φ (e ≫ F) q hq x a ha), NormIso.mem_const M' φ' e q' hq' x b hb⟩
  obtain ⟨u, hu⟩ := glue_unit (⊤ : S.Opens) (fun i => e ⁻¹ᵁ C i) (fun _ => le_top) (fun x _ => by
      obtain ⟨a, ha⟩ := exists_chart hM (q x)
      obtain ⟨b, hb⟩ := exists_chart hM' (q' x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a, b), mem x a b ha hb⟩)
    (fun i => pullU e (C i) (w.s (fun _ _ => i.1, fun _ => i.2))) (fun i j x hx => by
      have hi : e x ∈ C i := hx.1
      have hj : e x ∈ C j := hx.2
      refine (gm_pull (𝟙 S) e x (C i) hi _).trans (Eq.trans ?_ (gm_pull (𝟙 S) e x (C j) hj _).symm)
      rw [Category.id_comp]
      have h := (isGen_iff w).1 hw S e x (fun _ => i.1) (fun _ => j.1) (fun _ => i.2) (fun _ => j.2)
        (mem_pull.1 hi.1) (mem_pull.1 hj.1) hi.2 hj.2
      refine h.trans ((congrArg (· * _) ((congrArg₂ (fun s t => s * t⁻¹)
        (NormIso.gm_const M φ ε hε (e ≫ F) q hq x i.1 j.1 (mem_pull.1 hi.1) (mem_pull.1 hj.1))
        (NormIso.gm_const M' φ' ε hε e q' hq' x i.2 j.2 hi.2 hj.2)).trans (mul_inv_cancel 1))).trans (_root_.one_mul _)))
  refine ⟨u, fun Z t z a b ha hb => ?_⟩
  have hm : e (t z) ∈ C (a, b) := mem (t z) a b ha hb
  exact (gm_pull t e z (C (a, b)) hm _).symm.trans ((congrArg (gm t z (e ⁻¹ᵁ C (a, b))) (hu (a, b)).symm).trans
    (gm_res t z le_top hm u))

theorem lamVal_origin_of_generic : ∀ {S : Scheme.{0}} {V : Type} [CommRing V] [IsDomain V] (B : Over S) (B' : Over (Sp V)) [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (M : LB B.left) (M' : LB B'.left), M.IsLB → M'.IsLB → ∀ (f : Sp V ⟶ S) (β : B'.left ⟶ B.left) (β₂ : (G2 B').left ⟶ (G2 B).left) (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)), IsGrpPullback B' B f β → IsSquare β β₂ → w.IsGen → (∀ (z : (TK V).left) (J : ((TK V).left ⟶ B.left) → M.ι) (J' : ((TK V).left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift (1 : TK V ⟶ B') (1 : TK V ⟶ B')).left z J J' = 1) → ∀ (T : Over (Sp V)) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1 := by
  intro S V _ _ B B' _ _ _ _ M M' hM hM' f β β₂ w hpb hs hw hgen
  let O : Over (Sp V) := 𝟙_ (Over (Sp V))
  let e : O.left ⟶ (G2 B').left := (lift (1 : O ⟶ B') 1).left
  let q : O.left ⟶ B.left := (1 : Over.mk (O.hom ≫ f) ⟶ B).left
  let q' : O.left ⟶ B'.left := (1 : O ⟶ B').left
  have hq : ∀ I : ULift.{0} (Finset (Fin 2)), (e ≫ β₂) ≫ (psum B (x2 B) I.down).left = q := fun I =>
    (congrArg (· ≫ (psum B (x2 B) I.down).left) (NormIso.origin_square hpb hs O)).trans
      (congrArg (fun z => z.left) (NormIso.lift_one_psum B (T := Over.mk (O.hom ≫ f)) I.down))
  have hq' : ∀ I : ULift.{0} (Finset (Fin 2)), e ≫ (psum B' (x2 B') I.down).left = q' := fun I =>
    congrArg (fun z => z.left) (NormIso.lift_one_psum B' (T := O) I.down)
  obtain ⟨u, hu⟩ := exists_unit_along M M' hM hM' (K := ULift.{0} (Finset (Fin 2)))
    (fun I => (psum B (x2 B) I.down).left) (fun I => (psum B' (x2 B') I.down).left)
    (fun I => (-1) ^ (2 - I.down.card)) (by decide) β₂ e q q' hq hq' w hw
  have hval : ∀ (T : Over (Sp V)) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι),
      Good M z J → Good M' z J' →
      lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = gm (toUnit T).left z ⊤ u := by
    intro T z J J' hJ hJ'
    have hp : (lift (1 : T ⟶ B') (1 : T ⟶ B')).left = (toUnit T).left ≫ e := by
      show _ = (toUnit T ≫ lift (1 : O ⟶ B') 1).left
      rw [comp_lift, MonObj.comp_one]
    have key : ∀ (p : T.left ⟶ (G2 B').left) (j : (abelian₂ B M).ι) (k : (abelian₂ B' M').ι),
        (fun I : ULift.{0} (Finset (Fin 2)) => J (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)) = j →
        (fun I : ULift.{0} (Finset (Fin 2)) => J' (p ≫ (psum B' (x2 B') I.down).left)) = k →
        lamVal w p z J J' = gw (L := abelian₂ B M) (L' := abelian₂ B' M') w p z j k := by
      rintro p _ _ rfl rfl
      rfl
    rw [hp]
    refine (key _ (fun _ => J ((toUnit T).left ≫ q)) (fun _ => J' ((toUnit T).left ≫ q')) (funext fun I => ?_)
      (funext fun I => ?_)).trans (hu T.left (toUnit T).left z _ _ (hJ ((toUnit T).left ≫ q)) (hJ' ((toUnit T).left ≫ q')))
    · rw [← hq I, Category.assoc, Category.assoc]
    · rw [← hq' I, Category.assoc]
  have hK : (toUnit (TK V)).left = jK V := by simpa using Over.w (toUnit (TK V))
  have h1 : (Units.map (jK V).appTop.hom.toMonoidHom u : Γ((TK V).left, ⊤)ˣ) = 1 := unit_ext fun x _ => by
    choose a ha using fun χ : (TK V).left ⟶ B.left => exists_chart hM (χ x)
    choose b hb using fun χ : (TK V).left ⟶ B'.left => exists_chart hM' (χ x)
    have h := (hval (TK V) x a b ha hb).symm.trans (hgen x a b ha hb)
    rw [hK] at h
    rw [map_one]
    exact (gm_pull (𝟙 _) (jK V) x ⊤ trivial u).trans ((congrArg (fun g => gm g x ⊤ u) (Category.id_comp _)).trans h)
  have hu1 : u = 1 := Units.ext (jK_appTop_inj V (by
    have := congrArg Units.val h1
    simpa using this))
  intro T z J J' hJ hJ'
  rw [hval T z J J' hJ hJ', hu1]; exact map_one _

end GlobalTheory.GenOrigin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoValuesEqOfRigidified
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle

namespace GlobalTheory.TautUniq

theorem lamVal_eq_of_rig : ∀ {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] {M : LB B.left} {M' : LB B'.left} {β₂ : (G2 B').left ⟶ (G2 B).left}, M.IsLB → M'.IsLB → IsAbelianScheme B' → ∀ (w₁ w₂ : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)), w₁.IsGen → w₂.IsGen → (∀ (T : Over S') (z : T.left) J J', Good M z J → Good M' z J' → lamVal w₁ (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → (∀ (T : Over S') (z : T.left) J J', Good M z J → Good M' z J' → lamVal w₂ (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 B').left) (z : Z) J J', Good M z J → Good M' z J' → lamVal w₁ p z J J' = lamVal w₂ p z J J' := by
  intro S S' B B' _ _ _ _ M M' β₂ hM hM' hB' w₁ w₂ h₁ h₂ n₁ n₂ Z p z J J' hJ hJ'
  have hG := GlobalTheory.globalFns_holds
  have he2 : (lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ (snd B' B').left ≫ B'.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift (1 : 𝟙_ (Over S') ⟶ B') 1)
  have hp := surj_comp (surj_snd hG hB' _) (hG _ _ hB').2
  have mem : ∀ {Y : Scheme.{0}} (q : Y ⟶ (G2 B').left) (y : Y) {J₀ : (Y ⟶ B.left) → M.ι}
      {J₀' : (Y ⟶ B'.left) → M'.ι}, Good M y J₀ → Good M' y J₀' →
      q y ∈ (LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U
        (fun _ I => J₀ (q ≫ β₂ ≫ (psum B (x2 B) I.down).left), fun I => J₀' (q ≫ (psum B' (x2 B') I.down).left)) :=
    fun q y J₀ J₀' h h' => TopologicalSpace.Opens.mem_inf.2
      ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun I => h (q ≫ β₂ ≫ (psum B (x2 B) I.down).left),
       h'.mem (fun I : ULift (Finset (Fin 2)) => (psum B' (x2 B') I.down).left) q⟩
  have hw : w₁ = w₂ := by
    refine gen_eq_of_eq_along_section (fun y => ?_) _ _ he2 hp h₁ h₂ (fun s a ha => ?_)
    · obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt hM y
      obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt hM' y
      exact ⟨_, mem (𝟙 _) y hJ₁ hJ₁'⟩
    · obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt hM s
      obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt hM' s
      have hb := mem (lift (1 : 𝟙_ (Over S') ⟶ B') 1).left s hJ₁ hJ₁'
      have tr : ∀ {w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)}, w.IsGen → lamVal w (lift (1 : 𝟙_ (Over S') ⟶ B') 1).left s J₁ J₁' = 1 →
          gm (lift (1 : 𝟙_ (Over S') ⟶ B') 1).left s ((LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U a) (w.s a) =
            gm (lift (1 : 𝟙_ (Over S') ⟶ B') 1).left s
              ((LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U a ⊓ (LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U
                (fun _ I => J₁ ((lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ β₂ ≫ (psum B (x2 B) I.down).left),
                 fun I => J₁' ((lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ (psum B' (x2 B') I.down).left)))
              ((LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).g a
                (fun _ I => J₁ ((lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ β₂ ≫ (psum B (x2 B) I.down).left),
                 fun I => J₁' ((lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ (psum B' (x2 B') I.down).left))) := by
        intro w hw hv
        have := congrArg (gm (lift (1 : 𝟙_ (Over S') ⟶ B') 1).left s _) (hw a
          (fun _ I => J₁ ((lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ β₂ ≫ (psum B (x2 B) I.down).left),
           fun I => J₁' ((lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ (psum B' (x2 B') I.down).left)))
        rw [map_mul, gm_res _ s _ (TopologicalSpace.Opens.mem_inf.2 ⟨ha, hb⟩),
          gm_res _ s _ (TopologicalSpace.Opens.mem_inf.2 ⟨ha, hb⟩)] at this
        rw [this]
        unfold lamVal at hv
        rw [hv, _root_.mul_one]
      rw [tr h₁ (n₁ _ s J₁ J₁' hJ₁ hJ₁'), tr h₂ (n₂ _ s J₁ J₁' hJ₁ hJ₁')]
  rw [hw]

end GlobalTheory.TautUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegOfSameTorusTwist
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.Uniq

section General

variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {J : Type} [Fintype J]

theorem exists_cancel_linComb (hL : L.IsLB) (hL' : L'.IsLB) (hL'' : L''.IsLB) (pr : J → (X' ⟶ X)) (ε : J → ℤ)
    (F : X'' ⟶ X') (pr'' : J → (X'' ⟶ X)) (hpr : ∀ i, pr'' i = F ≫ pr i)
    (w : LB.Iso L' (LB.LinComb L pr ε)) (hw : w.IsGen) (w'' : LB.Iso L'' (LB.LinComb L pr'' ε)) (hw'' : w''.IsGen) :
    ∃ w' : LB.Iso L'' (L'.pull F), PGen w' ∧ ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (j : J → L.ι) (i : L'.ι) (k : L''.ι),
      f y ∈ LB.wchart L pr'' j → F (f y) ∈ L'.U i → f y ∈ L''.U k →
      gv w'' f y j k = gv w (f ≫ F) y j i * gw w' f y i k := by
  obtain rfl : pr'' = fun i => F ≫ pr i := funext hpr
  have hN := DVR.linComb_isLB L hL pr ε
  have up : ∀ (x : X'') (j : J → L.ι), F x ∈ LB.wchart L pr j → x ∈ LB.wchart L (fun i => F ≫ pr i) j :=
    fun x j h => Set.mem_iInter.2 fun i => Set.mem_iInter.1 h i
  have down : ∀ (x : X'') (j : J → L.ι), x ∈ LB.wchart L (fun i => F ≫ pr i) j → F x ∈ LB.wchart L pr j :=
    fun x j h => Set.mem_iInter.2 fun i => Set.mem_iInter.1 h i
  let v : LB.Iso L'' ((LB.LinComb L pr ε).pull (F ≫ 𝟙 X')) :=
    ⟨fun p => res (fun y hy => ⟨up y _ (mem_pull₂.1 hy.1), hy.2⟩ :
      ((LB.LinComb L pr ε).pull (F ≫ 𝟙 X')).U p.1 ⊓ L''.U p.2 ≤
        LB.wchart L (fun i => F ≫ pr i) (p.1 PUnit.unit) ⊓ L''.U p.2) (w''.s (p.1 PUnit.unit, p.2))⟩
  have hv : ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (j : J → L.ι) (k : L''.ι), F (f y) ∈ LB.wchart L pr j →
      f y ∈ L''.U k → gw v f y j k = gv w'' f y j k := fun Y f y j k hj hk =>
    gm_res f y _ (show f y ∈ ((LB.LinComb L pr ε).pull (F ≫ 𝟙 X')).U (fun _ => j) ⊓ L''.U k from
      ⟨mem_pull₂.2 hj, hk⟩) _
  have gv' : PGen v := by
    intro Y f y j j' k k' hj hj' hk hk'
    have hj₀ : F (f y) ∈ LB.wchart L pr j := hj
    have hj₀' : F (f y) ∈ LB.wchart L pr j' := hj'
    rw [hv Y f y j k hj₀ hk, hv Y f y j' k' hj₀' hk']
    refine (gm_isGen hw'' f y j j' k k' (up _ _ hj₀) (up _ _ hj₀') hk hk').trans ?_
    refine congrArg (fun a => a * _ * _) ?_
    refine (gm_linComb L _ ε f y j j' (up _ _ hj₀) (up _ _ hj₀')).trans
      (Eq.trans ?_ (gm_linComb L pr ε (f ≫ F ≫ 𝟙 X') y j j' hj₀ hj₀').symm)
    simp only [Category.comp_id, Category.assoc]
  obtain ⟨w', T⟩ := exists_cancel hN (isoPullId w rfl) v (isoPullId_pgen hw rfl) gv' hL' hL''
  refine ⟨w', T.pgen_cancel hN (isoPullId_pgen hw rfl) gv', fun Y f y j i k hj hi hk => ?_⟩
  have e := T Y f y j i k (down _ _ hj) hi hk
  rwa [hv Y f y j k (down _ _ hj) hk, gw_isoPullId w rfl (f ≫ F) y j i (down _ _ hj) hi] at e

theorem gm_mapsAtExp {Y : Scheme.{0}} {pr : J → (X' ⟶ X)} {ε : J → ℤ} {w : LB.Iso L' (LB.LinComb L pr ε)} {p : Y ⟶ X'}
    {n : ℤ} {a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p) (fun _ => n))}
    {b : LB.Gen (LB.LinComb L (K := J) (fun i => p ≫ pr i) (fun i => n * ε i))} (h : MapsAtExp L L' pr ε w p n a b)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (j : J → L.ι) (i : L'.ι) (hj : p (r z) ∈ LB.wchart L pr j)
    (hi : p (r z) ∈ L'.U i) :
    gm r z (LB.wchart L (fun i => p ≫ pr i) j) (b.s j) =
      gv w (r ≫ p) z j i ^ n * gm r z (LB.wchart L' (fun _ : PUnit => p) (fun _ => i)) (a.s (fun _ => i)) := by
  have hm : r z ∈ p ⁻¹ᵁ (LB.div (LB.LinComb L pr ε) L').U (j, i) := ⟨hj, hi⟩
  have e := congrArg (gm r z _) (h j i)
  refine (gm_res r z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res r z _ hm _))))
  exact (map_zpow _ _ _).trans (congrArg (· ^ n) (gm_pull r p z _ hm _))

theorem pmaps_of_mapsAtExp (hL : L.IsLB) {pr : J → (X' ⟶ X)} {ε : J → ℤ} {F : X'' ⟶ X'} {pr'' : J → (X'' ⟶ X)}
    (hpr : ∀ i, pr'' i = F ≫ pr i) {w : LB.Iso L' (LB.LinComb L pr ε)} {w'' : LB.Iso L'' (LB.LinComb L pr'' ε)}
    {w' : LB.Iso L'' (L'.pull F)}
    (T : ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (j : J → L.ι) (i : L'.ι) (k : L''.ι),
      f y ∈ LB.wchart L pr'' j → F (f y) ∈ L'.U i → f y ∈ L''.U k →
      gv w'' f y j k = gv w (f ≫ F) y j i * gw w' f y i k)
    {Y : Scheme.{0}} {p : Y ⟶ X'} {p'' : Y ⟶ X''} (hp : p'' ≫ F = p) {n : ℤ}
    {a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p) (fun _ => n))}
    {a'' : LB.Gen (LB.LinComb L'' (K := PUnit) (fun _ => p'') (fun _ => n))}
    {b : LB.Gen (LB.LinComb L (K := J) (fun i => p ≫ pr i) (fun i => n * ε i))}
    {b'' : LB.Gen (LB.LinComb L (K := J) (fun i => p'' ≫ pr'' i) (fun i => n * ε i))}
    (h : MapsAtExp L L' pr ε w p n a b) (h'' : MapsAtExp L L'' pr'' ε w'' p'' n a'' b'')
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (I : (Z ⟶ X) → L.ι), Good L z I → val b r z I = val b'' r z I) :
    PMaps w' (K := PUnit) (fun _ => p'') (fun _ => p) (fun _ => n) a'' a (𝟙 Y) := by
  obtain rfl : pr'' = fun i => F ≫ pr i := funext hpr
  subst hp
  intro Z r z P Q hP hQ
  choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
  have e := H Z r z I hI
  rw [val_of b r z I (fun i => I (r ≫ p'' ≫ F ≫ pr i)) (fun i => by rw [Category.assoc]),
    val_of b'' r z I (fun i => I (r ≫ p'' ≫ F ≫ pr i)) (fun i => rfl)] at e
  have m : ∀ i, pr i (F (p'' (r z))) ∈ L.U (I (r ≫ p'' ≫ F ≫ pr i)) := fun i => hI (r ≫ p'' ≫ F ≫ pr i)
  rw [gm_mapsAtExp h r z _ (P PUnit.unit) (Set.mem_iInter.2 m) (hP PUnit.unit),
    gm_mapsAtExp h'' r z _ (Q PUnit.unit) (Set.mem_iInter.2 m) (hQ PUnit.unit),
    T Z (r ≫ p'') z _ (P PUnit.unit) (Q PUnit.unit) (Set.mem_iInter.2 m) (hP PUnit.unit) (hQ PUnit.unit),
    mul_zpow, Category.assoc, _root_.mul_assoc] at e
  rw [Category.comp_id, Fintype.prod_unique]
  exact mul_left_cancel e

theorem pmaps_of_dense {Y Z₀ : Scheme.{0}} [IsReduced Y] (h : Z₀ ⟶ Y) (z₀ : Z₀)
    (hd : ∀ V : Y.Opens, (V : Set Y).Nonempty → h z₀ ∈ V) {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)} {φ' : Y ⟶ X'}
    {φ : Y ⟶ X} (hφ : φ' ≫ F = φ) {a : LB.Gen (L'.pull φ')} {t : LB.Gen (L.pull φ)}
    (H : ∀ (p : L.ι) (q : L'.ι), φ (h z₀) ∈ L.U p → φ' (h z₀) ∈ L'.U q →
      gm h z₀ (LB.wchart L (fun _ : PUnit => φ) (fun _ => p)) (t.s (fun _ => p)) =
        gw w (h ≫ φ') z₀ p q * gm h z₀ (LB.wchart L' (fun _ : PUnit => φ') (fun _ => q)) (a.s (fun _ => q))) :
    PMaps w (K := PUnit) (fun _ => φ') (fun _ => φ) (fun _ => 1) a t (𝟙 Y) := by
  subst hφ
  intro Z r z P Q hP hQ
  let V : Y.Opens := LB.wchart L (fun _ : PUnit => φ' ≫ F) P ⊓ LB.wchart L' (fun _ : PUnit => φ') Q
  have l : V ≤ φ' ⁻¹ᵁ ((L.pull F).U (fun _ => P PUnit.unit) ⊓ L'.U (Q PUnit.unit)) := fun y hy =>
    ⟨mem_pull.2 (Set.mem_iInter.1 hy.1 PUnit.unit), Set.mem_iInter.1 hy.2 PUnit.unit⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ V →
      gm r z V (res (inf_le_left : V ≤ _) (t.s P)) = gm r z (LB.wchart L (fun _ : PUnit => φ' ≫ F) P) (t.s P) ∧
      gm r z V (res l (pullU φ' _ (w.s (fun _ => P PUnit.unit, Q PUnit.unit))) * res (inf_le_right : V ≤ _) (a.s Q)) =
        gw w (r ≫ φ') z (P PUnit.unit) (Q PUnit.unit) * gm r z (LB.wchart L' (fun _ : PUnit => φ') Q) (a.s Q) :=
    fun Z r z hz => ⟨gm_res r z _ hz _, (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res r z l hz _).trans (gm_pull r φ' z _ (l hz) _)) (gm_res r z _ hz _))⟩
  have hz : r z ∈ V := ⟨Set.mem_iInter.2 hP, Set.mem_iInter.2 hQ⟩
  have hz₀ : h z₀ ∈ V := hd V ⟨_, hz⟩
  have e := TauPull.gm_injective_of_dense h z₀ hd V hz₀ ((key _ h z₀ hz₀).1.trans
    ((H (P PUnit.unit) (Q PUnit.unit) (Set.mem_iInter.1 hz₀.1 PUnit.unit) (Set.mem_iInter.1 hz₀.2 PUnit.unit)).trans
      (key _ h z₀ hz₀).2.symm))
  rw [Category.comp_id, Fintype.prod_unique, zpow_one]
  exact (key _ r z hz).1.symm.trans ((congrArg (gm r z V) e).trans (key _ r z hz).2)

end General

variable {R : Type} [CommRing R] [IsDomain R]

theorem xK_zero (D : DegPre R) : D.xK 0 = jK R ≫ eSec D.P.A := by
  have c0 : (D.c 0).left = eSec D.P.A := by
    have := PsiZero.cPoint_zero' D (𝟙_ _)
    rw [DVR.cP, toUnit_unit, Category.id_comp, Hom.one_def, toUnit_unit, Category.id_comp] at this
    rw [this]; rfl
  rw [← c0]; rfl

theorem gm_psi_zero {D : DegPre R} (hB : D.TauBimult) (χ : D.X) (hχ : χ = 0) (y : (TK R).left) (j : D.P.L.ι)
    (hj : eSec D.P.A (jK R y) ∈ D.P.L.U j) :
    gm (𝟙 _) y (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) (fun _ => j)) ((D.psi χ).s (fun _ => j)) =
      (gm (jK R) y (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => j)) (D.rig.s (fun _ => j)))⁻¹ := by
  subst hχ
  have hx := xK_zero D
  obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB y (K := PUnit) (fun _ => D.xK 0) (fun _ => j) (fun _ _ _ => rfl)
    (fun k => by rw [hx]; exact hj)
  have e := PsiZero.val_psi_zero hB hJ
  rwa [val_of (D.psi 0) _ y J (fun _ => j) (fun k => (congrArg J (Category.id_comp (D.xK 0))).trans (eJ k)),
    val_of D.rig _ y J (fun _ => j) (fun k => (congrArg J hx.symm).trans (eJ k))] at e

theorem twφ_comp (D₀ D₂ D : DegPre R) (Φ : D₂.P.A ⟶ D₀.P.A) (β : D₀.P.A ⟶ D.P.A) (b : 𝟙_ (Over (Sp R)) ⟶ D.P.A)
    (i : Fin 3) : twφ D₂ D (Φ ≫ β) b i = Φ.left ≫ twφ D₀ D β b i := by
  have hu : Φ ≫ toUnit D₀.P.A = toUnit D₂.P.A := toUnit_unique _ _
  fin_cases i
  · show (padd D.P.A (Φ ≫ β) (toUnit D₂.P.A ≫ b)).left = (Φ ≫ padd D.P.A β (toUnit D₀.P.A ≫ b)).left
    rw [padd, padd, ← Category.assoc Φ, comp_lift, ← Category.assoc Φ, hu]
  · show (toUnit D₂.P.A ≫ b).left = (Φ ≫ toUnit D₀.P.A ≫ b).left
    rw [← hu, Category.assoc]
  · show (toUnit D₂.P.A ≫ η[D.P.A]).left = (Φ ≫ toUnit D₀.P.A ≫ η[D.P.A]).left
    rw [← hu, Category.assoc]

theorem nonempty_isPullDeg_of_isTwist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D₂ D : DegData R (maximalIdeal R)) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), GlobalTheory.MumCmp.IsTwist D₀.toPre D.toPre g → GlobalTheory.MumCmp.IsTwist D₂.toPre D.toPre g → Nonempty (IsPullDeg (RingHom.id R) D₀.toPre D₂.toPre) := by
  intro R _ _ _ hR D₀ D₂ D g ⟨β₀, x₀, m₀, c₀, w₀, g₀, ψ₀⟩ ⟨β₂, x₂, m₂, c₂, w₂, g₂, ψ₂⟩
  let Φ : D₂.toPre.P.A ≅ D₀.toPre.P.A := β₂ ≪≫ β₀.symm
  have mΦ : IsMonHom Φ.hom := inferInstanceAs (IsMonHom (β₂.hom ≫ β₀.inv))
  have hβ : β₂.hom = Φ.hom ≫ β₀.hom := by simp [Φ]
  have gp : IsGrpPullback D₂.toPre.P.A D₀.toPre.P.A (specOf (RingHom.id R)) Φ.hom.left :=
    (isGrpPullback_of_iso Φ).congr (specOf_id R).symm rfl
  obtain ⟨e, me, hF⟩ := grpPullback_iso gp (isGrpPullback_pullback D₀.toPre.P.A (specOf (RingHom.id R)))
  have hF' : e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf (RingHom.id R)) = Φ.hom.left := hF
  have hpr : ∀ i, twφ D₂.toPre D.toPre β₂.hom g.b i =
      (e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf (RingHom.id R))) ≫ twφ D₀.toPre D.toPre β₀.hom g.b i :=
    fun i => by rw [hF', hβ]; exact twφ_comp _ _ _ _ _ _ i
  obtain ⟨w, gw', T⟩ := exists_cancel_linComb D.toPre.P.isLB D₀.toPre.P.isLB D₂.toPre.P.isLB _ twε _ _ hpr w₀ g₀ w₂ g₂
  let xe : D₂.toPre.X ≃+ D₀.toPre.X := x₂.trans x₀.symm
  have hxe : ∀ χ, x₀ (xe χ) = x₂ χ := fun χ => x₀.apply_symm_apply _
  have hc : ∀ χ, D₂.toPre.c χ ≫ Φ.hom = D₀.toPre.c (xe χ) := fun χ => by
    rw [← cancel_mono β₀.hom, Category.assoc, ← hβ, c₂, c₀, hxe]
  have hc' : ∀ χ, (D₂.toPre.c χ).left ≫ e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf (RingHom.id R)) =
      (D₀.toPre.c (xe χ)).left := fun χ => by rw [hF', ← Over.comp_left, hc]
  have hx : ∀ χ, D₂.toPre.xK χ ≫ e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf (RingHom.id R)) =
      D₀.toPre.xK (xe χ) := fun χ => by
    show (jK R ≫ (D₂.toPre.c χ).left) ≫ _ = jK R ≫ (D₀.toPre.c (xe χ)).left
    rw [Category.assoc, hc']
  have hE : eSec D₂.toPre.P.A ≫ e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf (RingHom.id R)) =
      eSec D₀.toPre.P.A := by
    rw [hF', eSec, eSec, ← Over.comp_left, IsMonHom.one_hom]
  have hψ : ∀ χ, PMaps w (K := PUnit) (fun _ => D₂.toPre.xK χ) (fun _ => D₀.toPre.xK (xe χ)) (fun _ => -1)
      (D₂.toPre.psi χ) (D₀.toPre.psi (xe χ)) (𝟙 _) := fun χ => by
    obtain ⟨t₀, a₀, b₀⟩ := ψ₀ (xe χ)
    obtain ⟨t₂, a₂, b₂⟩ := ψ₂ χ
    refine pmaps_of_mapsAtExp D.toPre.P.isLB hpr T (hx χ) a₀ a₂ fun Z r z I hI => ?_
    rw [val_corr hI b₀ r, val_corr hI b₂ r]
    have : ∀ a b : D.toPre.X, a = b →
        val (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi a) (LB.pullGen D.toPre.P.L _ _ (g.s a) (toUnit (TK R)).left)) r z I =
        val (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi b) (LB.pullGen D.toPre.P.L _ _ (g.s b) (toUnit (TK R)).left)) r z I := by
      rintro a b rfl; rfl
    exact this _ _ (hxe χ)
  obtain ⟨z₀⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  have red : IsReduced (𝟙_ (Over (Spec (CommRingCat.of R)))).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of R)))
  have hr : PMaps w (K := PUnit) (fun _ => eSec D₂.toPre.P.A) (fun _ => eSec D₀.toPre.P.A) (fun _ => 1)
      D₂.toPre.rig D₀.toPre.rig (𝟙 _) := by
    refine pmaps_of_dense (Z₀ := (TK R).left) (jK R) z₀ (TauPull.jK_mem z₀) hE fun p q hp hq => ?_
    have e := hψ 0 _ (𝟙 _) z₀ (fun _ => p) (fun _ => q)
      (fun _ => by
        show (D₂.toPre.xK 0 ≫ e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf (RingHom.id R))) z₀ ∈ _
        rw [hx, map_zero, xK_zero]; exact hp)
      (fun _ => by rw [xK_zero]; exact hq)
    rw [Category.id_comp, Fintype.prod_unique, gm_psi_zero D₀.tau_bimult _ (map_zero xe) z₀ p hp,
      gm_psi_zero D₂.tau_bimult _ rfl z₀ q hq, Category.id_comp, xK_zero, zpow_neg, zpow_one, ← mul_inv, inv_inj] at e
    exact e
  obtain ⟨W, hW, ⟨ψW⟩⟩ := psiOnExists R _ hR.1 D₀
  obtain ⟨hD, -⟩ := UnifUniq.exists_isPullDeg_id D₀.toPre D₂.toPre W hW ψW e me w ((isGen_iff _).2 gw') hE hr xe hc' hψ
  exact ⟨hD⟩

end GlobalTheory.MumCmp.Uniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySiegelLevelLoweringQuotientFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLev

theorem nonempty_sQuot : ∀ (h n N : ℕ) (F : SFam h N (zetaAway N)) (j : cycAway n →+* cycAway N), 3 ≤ n → Odd N → n ∣ N →
    j (zetaAway n) = zetaAway N ^ (N / n) → IsFinite (spMap j) → Etale (spMap j) → Nonempty (SQuot F n (zetaAway n) j) := by
  intro h n N F j hn hN hdvd hj hfin het
  have hn0 : n ≠ 0 := by omega
  have hN0 : N ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hN)
  haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n
  obtain ⟨Ga, _, _, ρ, ν, h1, hmul, hν1, hνmul, hover, hlow, hfree, htrans⟩ := GlobalTheory.T.siegelFamily_similitudeGroup_action_free_transitive h n N F j hn hN hdvd hj
  have hjf : j.Finite := (IsFinite.SpecMap_iff _).1 hfin
  have hq : IsQProjOver (F.s ≫ spMap j) :=
    (GlobalTheory.isQProjOver_baseChange_and_finite_restrict _ _ j F.X (F.s ≫ spMap j)).2 F.s hjf F.qproj
  obtain ⟨Y, π, sY, hπ, hG, hsep, hft, -⟩ :=
    _root_.GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver_noetherian (cycAway n) F.X (F.s ≫ spMap j) Ga ρ hq h1 hmul hover hfree
  have hqY : IsQProjOver sY := _root_.GlobalTheory.GaloisQuotientRing.isQProjOver_of_isGaloisCover (cycAway n) F.X Y π sY Ga ρ hG hsep hft (by rw [hπ]; exact hq)
  have hsm : SmoothOfRelativeDimension (h * (h + 1) / 2) (π ≫ sY) := by
    rw [hπ]
    haveI := F.smooth
    haveI : SmoothOfRelativeDimension 0 (spMap j) := inferInstance
    have := smoothOfRelativeDimension_comp (h * (h + 1) / 2) 0 F.s (spMap j)
    rwa [Nat.add_zero] at this
  have hsY : SmoothOfRelativeDimension (h * (h + 1) / 2) sY :=
    _root_.GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover_noetherian (cycAway n) F.X Y π sY _ hG.etale hG.onto hft hsm
  obtain ⟨c, hc, hlowc⟩ := _root_.GlobalTheory.PrincipalDescent.principal_descends h n N (cycAway n) (cycAway N) (cycBase hn0) (zetaAway N) j F.X Y F.s π sY F.univ
    Ga ρ ν hN0 (isUnit_natCast hN0) hdvd (by rw [cycBase_ζ]; exact hj) hπ hG (by rw [hπ]; exact hq) hft F.princ hν1
    hνmul hlow
  refine ⟨⟨Y, sY, hsY, hqY, c, hc, π, hπ, hG.fin, hG.etale, hG.onto, hlowc, ?_⟩⟩
  intro R _ _ y y' s' c' h₀ h₁ h₂
  obtain ⟨a, rfl⟩ := htrans R y y' s' c' h₀ h₁ h₂
  rw [Category.assoc, hG.inv]

end GlobalTheory.SiegLev

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareBundleDescendsQuotientFiniteSubgroup
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PoincareDescent

theorem descends : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B N : Over (Sp K)) [GrpObj A] [GrpObj A']
    [GrpObj B] [GrpObj N] (P : LB (A ⊗ B).left) (i : N ⟶ A) (q : A ⟶ A'), IsAbelianScheme A →
    IsAbelianScheme A' → IsAbelianScheme B → IsDual A B P → IsMonHom i → IsMonHom q → IsFinite q.left →
    Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → Triv (ev P (fst N B ≫ i) (snd N B)) →
    ∃ P' : LB (A' ⊗ B).left, P'.IsLB ∧ IsAdditive P' ∧ LBIso (ev P' (fst A B ≫ q) (snd A B)) P := by
  intro K _ _ A A' B N _ _ _ _ P i q hA hA' hB hD hi hq hfin hfl hsurj hker hN
  obtain ⟨P₀, hP₀, e⟩ := _root_.GlobalTheory.PoincareDescent.descend_torsor K A A' B N P i q hA hA' hB hD.isLB hD.additive hD.zero hi hq hfin hfl
    hsurj (torsor_square i q hker) hN
  have key : ∀ (Y : Over (Sp K)) (a : Y ⟶ A) (b : Y ⟶ B), evc hP₀ (a ≫ q) b = evc hD.isLB a b := by
    intro Y a b
    have c := congrArg (CechPic.pull (lift a b).left) ((cls_eq_iff (pull_isLB hP₀ _) hD.isLB).2 e)
    rw [cls_ev hP₀, pull_evc, lift_fst_assoc, lift_snd] at c
    exact c
  let φ : Fin 2 → ((A' ⊗ B).left ⟶ (A' ⊗ B).left) :=
    ![(lift (fst A' B) (snd A' B)).left, (lift (fst A' B) (1 : A' ⊗ B ⟶ B)).left]
  have hP' : (LB.LinComb P₀ φ ![1, -1]).IsLB := LB.isLB_linComb hP₀ _ _
  have ev' : ∀ (Y : Over (Sp K)) (a : Y ⟶ A') (b : Y ⟶ B), evc hP' a b = evc hP₀ a b - evc hP₀ a 1 := by
    intro Y a b
    rw [evc, cls_linComb hP₀, Fin.sum_univ_two, map_add (f := _), map_zsmul, map_zsmul, ← pull_comp, ← pull_comp]
    simp only [φ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, ← Over.comp_left, comp_lift,
      lift_fst, lift_snd, MonObj.comp_one, one_smul, neg_smul, evc, sub_eq_add_neg]
  have one : ∀ (Y : Over (Sp K)) (b : Y ⟶ B), evc hP₀ (1 : Y ⟶ A') b = 0 := fun Y b ↦ by
    have : (1 : Y ⟶ A) ≫ q = 1 := by simp
    rw [← this, key]
    exact hD.additive.evc_one hD.isLB b
  refine ⟨_, hP', CubeNoeth.isAdditive_of_triv_axes hA' hB hP' ?_ ?_, ?_⟩
  · rw [triv_ev_iff hP', ev', one, one, sub_self]
  · rw [triv_ev_iff hP', ev', sub_self]
  · refine (cls_eq_iff (pull_isLB hP' _) hD.isLB).1 ?_
    rw [cls_ev hP', ev', key, key, evc_one_right hD.isLB hD.zero, sub_zero, evc, lift_fst_snd, Over.id_left,
      pull_id]

end GlobalTheory.PoincareDescent
end

