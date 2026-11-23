module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.AlgebraLevelSetting
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyMumfordTorusQuotientTower
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0119
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0122
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.SharpPull

section
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A C : Over S} {A' C' : Over S'}
  [GrpObj A] [GrpObj C] [GrpObj A'] [GrpObj C'] {φ : A'.left ⟶ A.left} {ψ : C'.left ⟶ C.left}

theorem push_inj (h : IsGrpPullback A' A f φ) {T : Over S'} {x y : T ⟶ A'}
    (e : pushHom h T x = pushHom h T y) : x = y :=
  Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))

theorem push_left (h : IsGrpPullback A' A f φ) {T : Over S'} (x : T ⟶ A') :
    (pushHom h T x).left = x.left ≫ φ := rfl

theorem push_surj (h : IsGrpPullback A' A f φ) {T : Over S'} (y : Over.mk (T.hom ≫ f) ⟶ A) :
    ∃ x : T ⟶ A', pushHom h T x = y :=
  ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem push_comp (h : IsGrpPullback A' A f φ) (h' : IsGrpPullback C' C f ψ) {p : A ⟶ C} {p' : A' ⟶ C'}
    (e : p'.left ≫ ψ = φ ≫ p.left) {T : Over S'} (x : T ⟶ A') :
    pushHom h' T (x ≫ p') = pushHom h T x ≫ p :=
  Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, e, Category.assoc])

theorem exists_lift (h : IsGrpPullback A' A f φ) (h' : IsGrpPullback C' C f ψ) (p : A ⟶ C) :
    ∃ p' : A' ⟶ C', p'.left ≫ ψ = φ ≫ p.left :=
  ⟨Over.homMk (h'.1.lift (φ ≫ p.left) A'.hom (by rw [Category.assoc, Over.w, h.1.w])) (h'.1.lift_snd _ _ _),
    h'.1.lift_fst _ _ _⟩

theorem isMonHom_lift (h : IsGrpPullback A' A f φ) (h' : IsGrpPullback C' C f ψ) {p : A ⟶ C} [IsMonHom p]
    {p' : A' ⟶ C'} (e : p'.left ≫ ψ = φ ≫ p.left) : IsMonHom p' := by
  have h1 : (1 : 𝟙_ (Over S') ⟶ A') ≫ p' = 1 := by
    apply push_inj h'
    rw [push_comp h h' e, map_one, map_one, MonObj.one_comp]
  have h2 : (fst A' A' * snd A' A') ≫ p' = (fst A' A' ≫ p') * (snd A' A' ≫ p') := by
    apply push_inj h'
    rw [push_comp h h' e, map_mul, map_mul, MonObj.mul_comp, push_comp h h' e, push_comp h h' e]
  constructor
  · simpa [Hom.one_def] using h1
  · rw [Hom.mul_def, Hom.mul_def] at h2
    have e1 : lift (fst A' A' ≫ p') (snd A' A' ≫ p') = p' ⊗ₘ p' := by ext <;> simp
    simpa [e1] using h2
end

theorem sharp_pull : ∀ (h g k : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (o : Type) [CommRing o] (b : TBase o k) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s) (t' : TObj g k J b s') (c : SiegPre h k (b.ζ : o) s), f ≫ s = s' → TMap t' t f → c.Principal → IsSharp W a bas t c → ∃ c' : SiegPre h k (b.ζ : o) s', c'.Principal ∧ IsSharp W a bas t' c' := by
  intro h g k W J a bas o _ b S S' s s' f t t' c hf ⟨φ, hφ, hL, hpt, hact⟩ hc ⟨pr, hmon, huniv, hiso, hmat, hlev⟩
  obtain ⟨⟨c', hpb⟩, hprin⟩ := _root_.GlobalTheory.siegPre_pullback h k o (b.ζ : o) S S' s s' f c hf
  refine ⟨c', hprin c' hpb hc, ?_⟩
  obtain ⟨ψ, ψ₂, hψ, hsq, ⟨w, hw⟩, hlv⟩ := hpb
  choose pr' hpr using fun u => exists_lift hφ hψ (pr u)
  refine ⟨pr', fun u => ?_, fun T y => ?_, ?_, fun j u => ?_, fun i u => ?_⟩
  · have := hmon u
    exact isMonHom_lift hφ hψ (hpr u)
  · obtain ⟨x₀, hx₀, hu⟩ := huniv (Over.mk (T.hom ≫ f)) (fun u => pushHom hψ T (y u))
    obtain ⟨x, rfl⟩ := push_surj hφ x₀
    refine ⟨x, fun u => push_inj hψ ?_, fun x' hx' => push_inj hφ (hu _ fun u => ?_)⟩
    · rw [push_comp hφ hψ (hpr u), hx₀ u]
    · rw [← push_comp hφ hψ (hpr u), hx' u]
  · have hc : ∀ uv : Fin 8 × Fin 8, (lift (pr' uv.1) (pr' uv.2)).left ≫ ψ₂ = φ ≫ (lift (pr uv.1) (pr uv.2)).left := by
      intro uv
      apply pullback.hom_ext
      · show (_ ≫ ψ₂) ≫ (fst c.A c.A).left = (φ ≫ _) ≫ (fst c.A c.A).left
        rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, hpr, Category.assoc,
          ← Over.comp_left, lift_fst]
      · show (_ ≫ ψ₂) ≫ (snd c.A c.A).left = (φ ≫ _) ≫ (snd c.A c.A).left
        rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, hpr, Category.assoc,
          ← Over.comp_left, lift_snd]
    have H₁ := iso_linComb ((isGen_iff w).1 hw)
      (fun uv : Fin 8 × Fin 8 => (lift (pr' uv.1) (pr' uv.2)).left) (fun uv => W uv.1 uv.2)
    have H₂ : LBIso (t.L.pull φ) (LB.LinComb c.P
        (fun uv : Fin 8 × Fin 8 => (lift (pr' uv.1) (pr' uv.2)).left ≫ ψ₂) (fun uv => W uv.1 uv.2)) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull t.L φ φ rfl) (chartPullSame c.P _ _ _ φ hc) hiso
    exact LBIso.trans t'.isLB (DVR.linComb_isLB _ c.isLB _ _) (DVR.linComb_isLB _ c'.isLB _ _)
      (LBIso.trans t'.isLB (DVR.linComb_isLB _ t.isLB _ _) (DVR.linComb_isLB _ c.isLB _ _) hL H₂) H₁.symm
  · apply push_inj hψ
    have e : ∀ v, pushHom hψ t'.A (pr' v) = preHom (pushHom hφ t'.A (𝟙 _)) (pr v) := fun v =>
      (congrArg _ (Category.id_comp _).symm).trans (push_comp hφ hψ (hpr v) (𝟙 _))
    have e₂ : pushHom hφ t'.A (t'.act j) = pushHom hφ t'.A (𝟙 _) ≫ t.act j :=
      (congrArg _ (Category.id_comp _).symm).trans (push_comp hφ hφ (hact j) (𝟙 _))
    rw [push_comp hφ hψ (hpr u), e₂, Category.assoc, hmat j u]
    refine (map_list_prod (preHom (pushHom hφ t'.A (𝟙 _))) _).trans (Eq.trans ?_ (map_list_prod _ _).symm)
    rw [List.map_ofFn, List.map_ofFn]
    congr 2
    funext v
    simp only [Function.comp_apply, map_zpow, e]
  · apply hψ.1.hom_ext
    · rw [hlv, ← hlev i u, Over.comp_left, Over.comp_left, Category.assoc, hpr, ← Category.assoc, hpt, Category.assoc]
    · rw [Over.w, Over.w]; rfl

end GlobalTheory.SharpPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSemiAbelianOfLevel
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UU
open GlobalTheory.IndefiniteRowSideFullHecke.AlgebraLevelSetting (SymTriv Level Step FormalTorus Lv pr torus_w)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UniformizationSetting

section Weights
variable {S A Y₁ Y₂ : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G}
  {L : LB A}

end Weights

section Packages
variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G''] {X : Type} [AddCommGroup X]

variable {P : CP G} {P' : CP G'} {P'' : CP G''} {f : S' ⟶ S} {f' : S'' ⟶ S'} {f'' : S'' ⟶ S}
  {F : G'.left ⟶ G.left} {F' : G''.left ⟶ G'.left} {F'' : G''.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}

end Packages

section Triv
variable {S S' : Scheme.{0}} {G : Over S} {G' H : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  [GrpObj H] {P : CP G} {P' : CP G'} {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
  {w : LB.Iso P'.L.L (P.L.L.pull F)} {i : H ⟶ G'}

variable {S'' : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem exists_even_of_desc {Q : TQ G X} (D : Q.Desc P) : ∃ σ : CubTriv P.c Q.i, σ.Even := by
  have := Q.i_hom
  obtain ⟨s, hs, v⟩ := exists_gen D.M.L.isLB (φ := (PEmpty.elim : PEmpty → ((splitTorus S X).left ⟶ Q.B.left)))
    (ε := PEmpty.elim) (K' := Fin 2) (φ' := ![(1 : splitTorus S X ⟶ Q.B).left, (1 : splitTorus S X ⟶ Q.B).left])
    (ε' := ![1, -1]) (fun U _ h => by simp [Fin.prod_univ_two]) (LB.oneGen D.M.L.L)
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  have v' : ∀ (Z : Scheme.{0}) r (z : Z) J, Good D.M.L.L z J → val s r z J = 1 := fun Z r z J hJ =>
    (v Z r z J hJ).trans (val_one _)
  have e : Q.i ≫ Q.q = 1 := Q.isKernel.w
  refine TowerEx.exists_even_pull D.map (e ▸ TorusCompat.of_comp Q.i Q.q : TorusCompat _ _ Q.i 1)
    ⟨s, hs, fun T x y u z J hJ => ?_⟩ fun T x z J hJ => ?_
  · simp only [v' _ _ z J hJ, MonObj.comp_one, _root_.mul_one]
    exact ((isCub_cubV D.M.c (T := T) hJ).face 1 1).symm
  · show val s _ z J = _ * val s _ z J
    rw [v' _ _ z J hJ, v' _ _ z J hJ, MonObj.comp_one, D.M.val_sym_one hJ, _root_.mul_one]

end Triv

theorem exists_tq_lift {A A' : Type} [CommRing A] [IsLocalRing A] [CommRing A'] [Nontrivial A']
    (hA : IsNilpotent (IsLocalRing.maximalIdeal A)) (φ : A →+* A') (hφ : Function.Surjective φ)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (G' : Over (Spec (CommRingCat.of A'))) [GrpObj G']
    [IsCommMonObj G'] {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom φ)) F)
    (Q' : TQ G' X) : ∃ Q : TQ G X, TorusCompat (Spec.map (CommRingCat.ofHom φ)) F Q'.i Q.i := by
  obtain ⟨Q, hQ, -⟩ := TowerEx.exists_lift hA φ hφ G G' hF (P := CP.triv G) (P' := CP.triv G')
    (IsCPMap.triv (hw := hF.1.w) (TowerEx.toBase_mul hF _)) Q' ⟨CubTriv.triv _, CubTriv.triv_even _⟩
  exact ⟨Q, hQ⟩

section Levels
variable {S S₁ S₂ : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : CP G} {X : Type} [AddCommGroup X]
  [Module.Free ℤ X] [Module.Finite ℤ X] {f₁ : S₁ ⟶ S} {f₂ : S₂ ⟶ S}
  {G₁ : Over S₁} [GrpObj G₁] [IsCommMonObj G₁] {F₁ : G₁.left ⟶ G.left} {h₁ : F₁ ≫ G.hom = G₁.hom ≫ f₁}
  {G₂ : Over S₂} [GrpObj G₂] [IsCommMonObj G₂] {F₂ : G₂.left ⟶ G.left} {h₂ : F₂ ≫ G.hom = G₂.hom ≫ f₂}
  [ConnectedSpace S₁] {L₁ : Level P X f₁ G₁ F₁ h₁} {L₂ : Level P X f₂ G₂ F₂ h₂} {t : S₁ ⟶ S₂} {m : G₁.left ⟶ G₂.left}


variable {B : Over S} [GrpObj B] [IsCommMonObj B] {M : CP B}




end Levels

end GlobalTheory.UniformizationSetting
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSharpDescends
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.SharpDescent

theorem univ_descend {S S₁ : Scheme.{0}} (i : S ⟶ S₁) [Surjective i] [Flat i] [QuasiCompact i]
    {A C : Over S} {A₁ C₁ : Over S₁} {ψ : A.left ⟶ A₁.left} {χ : C.left ⟶ C₁.left}
    (hψ : IsPullback ψ A.hom A₁.hom i) (hχ : IsPullback χ C.hom C₁.hom i) {I : Type} [Finite I]
    (pr : I → (A ⟶ C)) (pr₁ : I → (A₁ ⟶ C₁)) (hc : ∀ u, ψ ≫ (pr₁ u).left = (pr u).left ≫ χ)
    (hU : ∀ (T : Over S) (y : I → (T ⟶ C)), ∃! x : T ⟶ A, ∀ u, x ≫ pr u = y u)
    (T : Over S₁) (y : I → (T ⟶ C₁)) : ∃! x : T ⟶ A₁, ∀ u, x ≫ pr₁ u = y u := by
  let Q₁ : Over S₁ := ∏ᶜ (fun _ : I => C₁)
  let π : I → (Q₁ ⟶ C₁) := fun u => Pi.π (fun _ : I => C₁) u
  let m₁ : A₁ ⟶ Q₁ := Pi.lift pr₁
  have hm₁ : ∀ u, m₁ ≫ π u = pr₁ u := fun u => Pi.lift_comp_π _ _
  have ext₁ : ∀ {Z : Scheme.{0}} (a b : Z ⟶ Q₁.left), a ≫ Q₁.hom = b ≫ Q₁.hom →
      (∀ u, a ≫ (π u).left = b ≫ (π u).left) → a = b := by
    intro Z a b h1 h2
    have : (Over.homMk a rfl : Over.mk (a ≫ Q₁.hom) ⟶ Q₁) = Over.homMk b h1.symm :=
      Pi.hom_ext _ _ fun u => Over.OverMorphism.ext (h2 u)
    exact congrArg (fun z => z.left) this
  let Q : Over S := Over.mk (pullback.snd Q₁.hom i)
  let q : I → (Q ⟶ C) := fun u => Over.homMk (hχ.lift (pullback.fst Q₁.hom i ≫ (π u).left) (pullback.snd Q₁.hom i)
    (by rw [Category.assoc, Over.w, pullback.condition])) (hχ.lift_snd _ _ _)
  have hq : ∀ u, (q u).left ≫ χ = pullback.fst Q₁.hom i ≫ (π u).left := fun u => hχ.lift_fst _ _ _
  let m : A ⟶ Q := Over.homMk (pullback.lift (ψ ≫ m₁.left) A.hom (by rw [Category.assoc, Over.w, hψ.w]))
    (pullback.lift_snd _ _ _)
  have hm : m.left ≫ pullback.fst Q₁.hom i = ψ ≫ m₁.left := pullback.lift_fst _ _ _
  have hm' : m.left ≫ pullback.snd Q₁.hom i = A.hom := pullback.lift_snd _ _ _
  have hmq : ∀ u, m ≫ q u = pr u := fun u => Over.OverMorphism.ext (hχ.hom_ext
    (by rw [Over.comp_left, Category.assoc, hq, ← Category.assoc, hm, Category.assoc, ← Over.comp_left, hm₁, hc])
    (by rw [Over.w, Over.w]))
  obtain ⟨n, hn, -⟩ := hU Q q
  have h1 : m ≫ n = 𝟙 A := (hU A pr).unique (fun u => by rw [Category.assoc, hn, hmq]) (fun u => Category.id_comp _)
  have h2 : n.left ≫ m.left = 𝟙 Q.left := by
    have hs : (n.left ≫ m.left) ≫ pullback.snd Q₁.hom i = 𝟙 Q.left ≫ pullback.snd Q₁.hom i := by
      rw [Category.assoc, hm', Over.w, Category.id_comp]; rfl
    refine pullback.hom_ext (ext₁ _ _ ?_ fun u => ?_) hs
    · rw [Category.assoc, Category.assoc (𝟙 _), pullback.condition, ← Category.assoc, hs, Category.assoc]
    · rw [Category.assoc, Category.assoc (𝟙 _), ← hq, Category.id_comp, ← Category.assoc, ← Over.comp_left,
        ← Over.comp_left, Category.assoc, hmq, hn]
  have hI : IsIso m.left := ⟨⟨n.left, by rw [← Over.comp_left, h1, Over.id_left], h2⟩⟩
  have hp : IsPullback m.left ψ (pullback.fst Q₁.hom i) m₁.left := by
    refine IsPullback.of_right (h₁₂ := pullback.snd Q₁.hom i) (v₁₃ := i) (h₂₂ := Q₁.hom) ?_ hm
      (IsPullback.of_hasPullback Q₁.hom i).flip
    rw [hm', Over.w]; exact hψ.flip
  have hI₁ : IsIso m₁.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme.{0})
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hp ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hI
  have : IsIso ((Over.forget S₁).map m₁) := hI₁
  have : IsIso m₁ := isIso_of_reflects_iso m₁ (Over.forget S₁)
  refine ⟨Pi.lift y ≫ inv m₁, fun u => ?_, fun x hx => ?_⟩
  · rw [← hm₁, Category.assoc, IsIso.inv_hom_id_assoc]; exact Pi.lift_comp_π _ _
  · rw [IsIso.eq_comp_inv]
    refine Pi.hom_ext _ _ fun u => ?_
    rw [Category.assoc, hm₁]
    exact (hx u).trans (Pi.lift_comp_π _ _).symm

theorem prod_descend {S S₁ : Scheme.{0}} {i : S ⟶ S₁} {A C : Over S} {A₁ C₁ : Over S₁} [GrpObj C] [GrpObj C₁]
    {ψ : A.left ⟶ A₁.left} {χ : C.left ⟶ C₁.left} [Epi ψ] (hψ : ψ ≫ A₁.hom = A.hom ≫ i)
    (hχ : IsGrpPullback C C₁ i χ) {n : ℕ} (pr : Fin n → (A ⟶ C)) (pr₁ : Fin n → (A₁ ⟶ C₁))
    (hc : ∀ u, ψ ≫ (pr₁ u).left = (pr u).left ≫ χ) (e : Fin n → ℤ) (z : A ⟶ C) (z₁ : A₁ ⟶ C₁)
    (hz : ψ ≫ z₁.left = z.left ≫ χ) (h : z = (List.ofFn fun v => pr v ^ e v).prod) :
    z₁ = (List.ofFn fun v => pr₁ v ^ e v).prod := by
  let U : Over.mk (A.hom ≫ i) ⟶ A₁ := Over.homMk ψ hψ
  have key : ∀ (x : A ⟶ C) (x₁ : A₁ ⟶ C₁), ψ ≫ x₁.left = x.left ≫ χ → preHom U x₁ = pushHom hχ A x :=
    fun x x₁ hx => Over.OverMorphism.ext hx
  have E : preHom U z₁ = preHom U (List.ofFn fun v => pr₁ v ^ e v).prod := by
    rw [key z z₁ hz, h, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
    congr 2
    funext v
    simp only [Function.comp_apply, map_zpow, key _ _ (hc v)]
  exact Over.OverMorphism.ext ((cancel_epi ψ).1 (congrArg (fun w => w.left) E))

theorem iso_pull_cancel {X X₁ X₀ : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₀ : LB X₀} (hL : L.IsLB) (hL₁ : L₁.IsLB)
    (hL₀ : L₀.IsLB) {φ : X ⟶ X₀} {φ₁ : X₁ ⟶ X₀} {ψ : X ⟶ X₁} (e : ψ ≫ φ₁ = φ) (h : LBIso L (L₀.pull φ))
    (h₁ : LBIso L₁ (L₀.pull φ₁)) : LBIso L (L₁.pull ψ) := by
  obtain ⟨w, hw⟩ := h₁
  have := iso_linComb ((isGen_iff w).1 hw) (fun _ : PUnit => ψ) (fun _ => 1)
  subst e
  exact LBIso.trans hL (LB.isLB_pull hL₀ _) (LB.isLB_pull hL₁ _) h (LBIso.symm this)

theorem isSharp_descends : ∀ (h g k : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (o : Type) [CommRing o] (b : TBase o k) (K : Type) [Field K] (K₀ : Subfield K) (β₀ : o →+* K₀) (s : Sp K ⟶ Sp o) (t : TObj g k J b s) (c : SiegPre h k (b.ζ : o) s) (t₀ : TObj g k J b (spMap β₀)) (c₀ : SiegPre h k (b.ζ : o) (spMap β₀)), s = spMap K₀.subtype ≫ spMap β₀ → TMap t t₀ (spMap K₀.subtype) → SiegPB c c₀ (spMap K₀.subtype) → c₀.Principal → IsSharp W a bas t c → ∃ (F : Finset K) (β₁ : o →+* Subfield.closure ((K₀ : Set K) ∪ F)) (t₁ : TObj g k J b (spMap β₁)) (c₁ : SiegPre h k (b.ζ : o) (spMap β₁)), s = spMap (Subfield.subtype _) ≫ spMap β₁ ∧ TMap t t₁ (spMap (Subfield.subtype _)) ∧ c₁.Principal ∧ IsSharp W a bas t₁ c₁ := by
  intro h g k W J a bas o _ b K _ K₀ β₀ s t c t₀ c₀ hs ⟨φ, hφ, hφL, hφp, hφa⟩ ⟨ξ, ξ₂, hξ, hξs, hξL, hξl⟩ hP
    ⟨pr, hm, hU, hL, hA, hp⟩
  have := t₀.ab.proper
  have := c₀.ab.smooth
  have hf : ∀ u, ((pr u).left ≫ ξ) ≫ c₀.A.hom = φ ≫ t₀.A.hom := fun u => by
    rw [Category.assoc, hξ.1.w, ← Category.assoc, Over.w, hφ.1.w]
  obtain ⟨F, hF⟩ := _root_.GlobalTheory.morphisms_descend_to_large_subfield K K₀ _ _ t₀.A.hom t.A.hom φ _ c₀.A.hom (Fin 8) (fun u => (pr u).left ≫ ξ) hφ.1 hf
  refine ⟨F, ?_⟩
  have hle : K₀ ≤ Subfield.closure ((K₀ : Set K) ∪ F) := fun x hx => Subfield.subset_closure (Or.inl hx)
  have hFs : (F : Set K) ⊆ Subfield.closure ((K₀ : Set K) ∪ F) := fun x hx => Subfield.subset_closure (Or.inr hx)
  have hF₁ := hF _ hle hFs
  generalize Subfield.closure ((K₀ : Set K) ∪ F) = K₁ at hle hF₁ ⊢
  clear hF hFs
  have e₁ : spMap (Subfield.inclusion hle) ≫ spMap β₀ = spMap ((Subfield.inclusion hle).comp β₀) :=
    (Spec.map_comp _ _).symm
  have e₂ : spMap K₁.subtype ≫ spMap (Subfield.inclusion hle) = spMap K₀.subtype := (Spec.map_comp _ _).symm
  obtain ⟨t₁, φ₁, hφ₁, hφ₁L, hφ₁p, hφ₁a⟩ := _root_.GlobalTheory.tObj_pull o g k J b _ _ _ _ _ t₀ e₁
  obtain ⟨⟨c₁, hc₁⟩, hc₁P⟩ := _root_.GlobalTheory.siegPre_pullback h k o (b.ζ : o) _ _ _ _ _ c₀ e₁
  have hP₁ := hc₁P c₁ hc₁ hP
  obtain ⟨ξ₁, ξ₁₂, hξ₁, hξ₁s, hξ₁L, hξ₁l⟩ := hc₁

  obtain ⟨ψ, hψ, hψw⟩ : ∃ ψ : t.A.left ⟶ t₁.A.left, ψ ≫ φ₁ = φ ∧ ψ ≫ t₁.A.hom = t.A.hom ≫ spMap K₁.subtype :=
    ⟨hφ₁.1.lift φ (t.A.hom ≫ spMap K₁.subtype) (by rw [Category.assoc, e₂, hφ.1.w]), hφ₁.1.lift_fst _ _ _,
      hφ₁.1.lift_snd _ _ _⟩
  obtain ⟨χ, hχ, hχw⟩ : ∃ χ : c.A.left ⟶ c₁.A.left, χ ≫ ξ₁ = ξ ∧ χ ≫ c₁.A.hom = c.A.hom ≫ spMap K₁.subtype :=
    ⟨hξ₁.1.lift ξ (c.A.hom ≫ spMap K₁.subtype) (by rw [Category.assoc, e₂, hξ.1.w]), hξ₁.1.lift_fst _ _ _,
      hξ₁.1.lift_snd _ _ _⟩
  have gψ : IsGrpPullback t.A t₁.A (spMap K₁.subtype) ψ := hφ₁.cancel (hφ.congr e₂.symm hψ.symm) hψw
  have gχ : IsGrpPullback c.A c₁.A (spMap K₁.subtype) χ := hξ₁.cancel (hξ.congr e₂.symm hχ.symm) hχw
  obtain ⟨f₁, hf₁⟩ := hF₁ _ t₁.A.hom φ₁ ψ hφ₁.1 hψ hψw
  obtain ⟨pr₁, hpr₁⟩ : ∃ pr₁ : Fin 8 → (t₁.A ⟶ c₁.A), ∀ u, (pr₁ u).left ≫ ξ₁ = f₁ u :=
    ⟨fun u => Over.homMk (hξ₁.1.lift (f₁ u) t₁.A.hom ((hf₁ u).2.trans hφ₁.1.w)) (hξ₁.1.lift_snd _ _ _),
      fun u => hξ₁.1.lift_fst _ _ _⟩
  have hc : ∀ u, ψ ≫ (pr₁ u).left = (pr u).left ≫ χ := fun u => hξ₁.1.hom_ext
    (by rw [Category.assoc, hpr₁, (hf₁ u).1, Category.assoc, hχ])
    (by rw [Category.assoc, Over.w, hψw, Category.assoc, hχw, ← Category.assoc, Over.w])
  obtain ⟨D₁, D₂⟩ := GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K₁ K K₁.subtype
  obtain ⟨i₁, i₂, i₃, i₄, -⟩ := D₁ _ _ (𝟙 _) (𝟙 _) (spMap K₁.subtype) (IsPullback.of_vert_isIso ⟨by simp⟩)
  obtain ⟨j₁, -⟩ := D₁ _ _ _ _ ψ gψ.1
  have hψL : LBIso t.L (t₁.L.pull ψ) := iso_pull_cancel t.isLB t₁.isLB t₀.isLB hψ hφL hφ₁L
  have hψp : ∀ i, (t.pt i).left ≫ ψ = spMap K₁.subtype ≫ (t₁.pt i).left := fun i => hφ₁.1.hom_ext
    (by rw [Category.assoc, hψ, hφp, Category.assoc, hφ₁p, ← Category.assoc, e₂])
    (by rw [Category.assoc, hψw, ← Category.assoc, Over.w, Category.assoc, Over.w]; simp)
  have hψa : ∀ j, (t.act j).left ≫ ψ = ψ ≫ (t₁.act j).left := fun j => hφ₁.1.hom_ext
    (by rw [Category.assoc, hψ, hφa, Category.assoc, hφ₁a, ← Category.assoc, hψ])
    (by rw [Category.assoc, hψw, ← Category.assoc, Over.w, Category.assoc, Over.w, hψw])
  have hχl : ∀ v, (c.lev v).left ≫ χ = spMap K₁.subtype ≫ (c₁.lev v).left := fun v => hξ₁.1.hom_ext
    (by rw [Category.assoc, hχ, hξl, Category.assoc, hξ₁l, ← Category.assoc, e₂])
    (by rw [Category.assoc, hχw, ← Category.assoc, Over.w, Category.assoc, Over.w]; simp)
  refine ⟨_, t₁, c₁, by rw [hs, ← e₁, ← Category.assoc, e₂], ⟨ψ, gψ, hψL, hψp, hψa⟩, hP₁, pr₁,
    fun u => (D₂ _ _ _ _ ψ χ (pr₁ u) (pr u) gψ gχ (hc u)).1 (hm u), univ_descend _ gψ.1 gχ.1 pr pr₁ hc hU, ?_,
    fun j u => prod_descend hψw gχ pr pr₁ hc _ (t.act j ≫ pr u) _ ?_ (hA j u), fun i u => ?_⟩
  · have lb := fun {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) (φ : Fin 8 × Fin 8 → (Y ⟶ X)) =>
      DVR.linComb_isLB L hL φ (fun uv => W uv.1 uv.2)
    refine (_root_.GlobalTheory.lb_gen_iso_descend_field K₁ K K₁.subtype _ _ _ _ ψ t₁.ab.smooth t₁.ab.proper t₁.ab.geomConnected gψ.1).2 _ _ t₁.isLB
      (lb _ c₁.isLB _) ?_
    obtain ⟨w, hw⟩ := hξL
    obtain ⟨w₁, hw₁⟩ := hξ₁L
    have a₁ := iso_linComb ((isGen_iff w).1 hw) (fun uv : Fin 8 × Fin 8 => (lift (pr uv.1) (pr uv.2)).left)
      (fun uv => W uv.1 uv.2)
    have a₂ := iso_linComb ((isGen_iff w₁).1 hw₁) (fun uv : Fin 8 × Fin 8 => ψ ≫ (lift (pr₁ uv.1) (pr₁ uv.2)).left)
      (fun uv => W uv.1 uv.2)
    have e : (fun uv : Fin 8 × Fin 8 => (ψ ≫ (lift (pr₁ uv.1) (pr₁ uv.2)).left) ≫ ξ₁₂) =
        fun uv => (lift (pr uv.1) (pr uv.2)).left ≫ ξ₂ := by
      funext uv
      apply pullback.hom_ext
      · show (_ ≫ ξ₁₂) ≫ (fst c₀.A c₀.A).left = (_ ≫ ξ₂) ≫ (fst c₀.A c₀.A).left
        rw [Category.assoc, hξ₁s.1, Category.assoc, Category.assoc, hξs.1, ← Over.comp_left_assoc,
          ← Over.comp_left_assoc, lift_fst, lift_fst, hpr₁, (hf₁ _).1]
      · show (_ ≫ ξ₁₂) ≫ (snd c₀.A c₀.A).left = (_ ≫ ξ₂) ≫ (snd c₀.A c₀.A).left
        rw [Category.assoc, hξ₁s.2, Category.assoc, Category.assoc, hξs.2, ← Over.comp_left_assoc,
          ← Over.comp_left_assoc, lift_snd, lift_snd, hpr₁, (hf₁ _).1]
    rw [e] at a₂
    have a₃ := LBIso.trans t.isLB (lb _ c.isLB _) (lb _ c₀.isLB _) hL a₁
    have a₄ := LBIso.trans t.isLB (lb _ c₀.isLB _) (lb _ c₁.isLB _) a₃ a₂.symm
    have a₅ := LBIso.trans (LB.isLB_pull t₁.isLB ψ) t.isLB (lb _ c₁.isLB _) hψL.symm a₄
    exact LBIso.chartPull (chartPullId _) (chartPullOut c₁.P _ _ ψ _ fun _ => rfl) a₅
  · rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← hψa, Category.assoc, hc, Category.assoc]
  · rw [← cancel_epi (spMap K₁.subtype), Over.comp_left, ← Category.assoc, ← hψp, Category.assoc, hc,
      ← Category.assoc, ← Over.comp_left, hp]
    exact hχl _

end GlobalTheory.SharpDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoPullOfIsConst
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.SymRigid

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem sym_iff_cls {L : LB A.left} (hL : L.IsLB) : Out.Sym A L ↔ ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
    pull ((A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left) (cls L hL) = pull (A.hom ⁻¹ᵁ U).ι (cls L hL) := by
  refine forall_congr' fun s => exists_congr fun U => and_congr_right fun _ => ?_
  rw [← cls_eq_zero_iff (LB.isLB_linComb hL _ _), cls_linComb hL, Fin.sum_univ_two]
  change (1 : ℤ) • pull ((A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left) (cls L hL) +
    (-1 : ℤ) • pull (A.hom ⁻¹ᵁ U).ι (cls L hL) = 0 ↔ _
  rw [one_zsmul, neg_one_zsmul, add_neg_eq_zero]

theorem pull_restrict {U V : S.Opens} (h : V ≤ U) {c : Pic A.left}
    (e : pull ((A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left) c = pull (A.hom ⁻¹ᵁ U).ι c) :
    pull ((A.hom ⁻¹ᵁ V).ι ≫ (GrpObj.inv : A ⟶ A).left) c = pull (A.hom ⁻¹ᵁ V).ι c := by
  have hle : A.hom ⁻¹ᵁ V ≤ A.hom ⁻¹ᵁ U := fun _ hx => h hx
  rw [← Scheme.homOfLE_ι A.left hle, Category.assoc, pull_comp, e, ← pull_comp]

theorem sym_of_cls_eq_sub {L M Q : LB A.left} (hL : L.IsLB) (hM : M.IsLB) (hQ : Q.IsLB)
    (e : cls Q hQ = cls L hL - cls M hM) (sL : Out.Sym A L) (sM : Out.Sym A M) : Out.Sym A Q := by
  refine (sym_iff_cls hQ).2 fun s => ?_
  obtain ⟨U, hU, eU⟩ := (sym_iff_cls hL).1 sL s
  obtain ⟨V, hV, eV⟩ := (sym_iff_cls hM).1 sM s
  refine ⟨U ⊓ V, ⟨hU, hV⟩, ?_⟩
  rw [e, map_sub, map_sub, pull_restrict inf_le_left eU, pull_restrict inf_le_right eV]

theorem lbIso_pull_of_isConst : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ : A'.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ A'.left), IsConst A' P₀.A ρ j → ∀ M : LB A'.left, M.IsLB → Out.Sym A' M → LBIso P₀.L (M.pull j) → LBIso M (P₀.L.pull ρ) := by
  intro laws P₀ u Hm χ hu A' _ ρ j hc M hM sM H
  have hL := pull_isLB P₀.isLB ρ
  have hQ : (LB.div (P₀.L.pull ρ) M).IsLB := LB.isLB_div hL hM
  have e₀ : cls _ P₀.isLB = pull j (cls M hM) := (cls_eq_iff _ (pull_isLB hM j)).2 H
  have triv : ∃ t : ((LB.div (P₀.L.pull ρ) M).pull j).Gen, t.IsGen := by
    rw [← cls_eq_zero_iff (pull_isLB hQ j), cls_pull hQ, cls_div hL hM, map_sub, cls_pull P₀.isLB, ← pull_comp,
      hc.2.2, pull_id, e₀, sub_self]
  obtain ⟨Q, k, hQ', iso, hk⟩ := _root_.GlobalTheory.EpsCocycle.exists_cocycle_one_add_eps _ _ P₀.A.hom A'.hom ρ j hc.1.1 hc.2.2 hc.2.1.1.w _ hQ triv
  have e : cls Q hQ' = cls _ hL - cls M hM := ((cls_eq_iff hQ hQ').2 iso).symm.trans (cls_div hL hM hQ)
  have z := (cls_eq_zero_iff hQ').2 (_root_.GlobalTheory.KS.EpsSym.trivial_of_symmetric laws P₀ u Hm χ hu A' ρ j hc Q k hQ' hk
    (sym_of_cls_eq_sub hL hM hQ' e (PolBaseChange.sym_pull hc.1 P₀.sym) sM))
  exact (cls_eq_iff hM hL).1 (sub_eq_zero.1 (e.symm.trans z)).symm

end GlobalTheory.SymRigid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingDiagonalBundleOfEighthPowerFormStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_diagonal_bundle_of_eighthPower_form : Out.GlobalFnsSt → ∀ (h k : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (P : LB (G2 A).left) (K : Type) [Field K] (p : Sp K ⟶ S) (lev : (Fin h ⊕ Fin h → ℤ) → (Over.mk p ⟶ A)) (c : Γ((Over.mk p).left, ⊤)ˣ), IsE8 W → IsAbelianScheme G → IsAbelianScheme A → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → (∀ x y, lev (x + y) = lev x * lev y) → (∀ x, lev x ^ k = 1) → (∀ (X Y : Fin 8 → (Fin h ⊕ Fin h → ℤ)) (y y' : Over.mk p ⟶ G), (∀ u, y ≫ pr u = lev (X u)) → (∀ u, y' ≫ pr u = lev (Y u)) → Out.WeilIs G L k y y' (c ^ ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (X u) (Y v))) → ∀ x y, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (lev x) (lev y) (c ^ (2 * omegaStd x y)) := by
  first | exact @GlobalTheory.WeilDown.weilIs_diag | exact GlobalTheory.WeilDown.weilIs_diag | (intros; apply GlobalTheory.WeilDown.weilIs_diag <;> assumption)
end

