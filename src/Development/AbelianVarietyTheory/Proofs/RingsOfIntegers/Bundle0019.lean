module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProductUniformizationTorusIsPower
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PowTorus

section Box

variable {X X' Y Z : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

private theorem units_map_stalkMap_gm_eq_gm_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (s : Y ⟶ X) (z : Z) (U : X.Opens)
    (a : Γ(X, U)ˣ) :
    Units.map ((r.stalkMap z).hom : Y.presheaf.stalk (r z) →* Z.presheaf.stalk z) (gm s (r z) U a) =
      gm (r ≫ s) z U a := by
  unfold gm
  by_cases h : s (r z) ∈ U
  · have h' : (r ≫ s) z ∈ U := h
    rw [dite_eq_left h, dite_eq_left h']
    apply Units.ext
    simp only [Units.coe_map, MonoidHom.coe_coe]
    unfold pullU
    simp only [Units.coe_map, MonoidHom.coe_coe, MonoidHom.comp_apply]
    have key := congrArg (fun φ => φ.hom ((s.app U).hom a.val)) (Scheme.Hom.germ_stalkMap r (s ⁻¹ᵁ U) z h)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at key
    exact key
  · have h' : ¬ (r ≫ s) z ∈ U := h
    rw [dite_eq_right h, dite_eq_right h']
    simp

private theorem units_map_stalkMap_bw_eq_bw_comp {X X' Y Z : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}
    (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (r : Z ⟶ Y) (ψ : Y ⟶ X') (z : Z) (jN : Fin j → M.ι) (k : M'.ι) :
    Units.map ((r.stalkMap z).hom : Y.presheaf.stalk (r z) →* Z.presheaf.stalk z) (bw w ψ (r z) jN k) =
      bw w (r ≫ ψ) z jN k := by
  unfold bw
  exact units_map_stalkMap_gm_eq_gm_comp r ψ z _ _

private theorem units_map_stalkMap_val_eq_val_comp {X Y Y₁ Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y₁ ⟶ X)}
    {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (s : Y ⟶ Y₁) (z : Z) (J : (Z ⟶ X) → L.ι) :
    Units.map ((r.stalkMap z).hom : Y.presheaf.stalk (r z) →* Z.presheaf.stalk z)
        (val t s (r z) (fun ψ => J (r ≫ ψ))) = val t (r ≫ s) z J := by
  rw [val_of t (r ≫ s) z J (fun k => J (r ≫ s ≫ φ k)) (fun k => by rw [Category.assoc]),
    val_of t s (r z) _ (fun k => J (r ≫ s ≫ φ k)) (fun k => rfl)]
  exact units_map_stalkMap_gm_eq_gm_comp r s z _ _

theorem box_gen_val_along (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K] {Y₀ : Scheme.{0}}
    {φ' : K → (Y ⟶ X')} {φ : Fin j → K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (t' : LB.Gen (LB.LinComb M' φ' ε)) (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε))
    (H : LB.Gen.Maps (LB.linCombIso w φ' ε) t'
      (GeneratorPullback.boxGen M pr φ' ε (fun i => GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i))))
    (r : Z ⟶ Y) (y : Z) {J J'} (hJ : Good M y J) (hJ' : Good M' y J') :
    (∏ a, bw w (r ≫ φ' a) y (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a) * val t' r y J' =
      ∏ i, val (t i) (r ≫ ρ i) y J := by
  have E := box_gen_val w hψ t' t H (r y) (J := fun ψ => J (r ≫ ψ)) (J' := fun ψ => J' (r ≫ ψ))
    (fun ψ => hJ (r ≫ ψ)) (fun ψ => hJ' (r ≫ ψ))
  have E2 := congrArg (Units.map ((r.stalkMap y).hom : Y.presheaf.stalk (r y) →* Z.presheaf.stalk y)) E
  rw [map_mul, map_prod, map_prod] at E2
  simp only [map_zpow, units_map_stalkMap_bw_eq_bw_comp, units_map_stalkMap_val_eq_val_comp, Category.comp_id] at E2
  simp only [Category.assoc]
  exact E2

end Box

section Coord

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem val_on_torus {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (χ : D.X) {z : Z.left}
    {J : (Z.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (τ : Z ⟶ splitTorus _ D.X) :
    val (g.t χ) (τ ≫ g.i).left z J = gm τ.left z ⊤ (charUnit _ D.X χ) := by
  have h1 := GlobalTheory.TorusCoord.val_torus g χ hJ τ 1
  rw [_root_.mul_one] at h1
  rw [h1, GlobalTheory.TorusCoord.val_unit g χ hJ, _root_.mul_one]

theorem prod_on_torus (χ : D.X) {V : Type} [CommGroup V]
    (f : ((splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left ⟶ D.P.A.left) → V) :
    ∏ k, f (g.i.left ≫ D.Oφ g.pG χ k) ^ Oinvε k = 1 := by
  have k0 : g.i ≫ g.q = (1 : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ⟶ thickObj R I e G) ≫ g.q := by
    have := g.q_hom
    rw [g.isKernel.w, MonObj.one_comp]
    rfl
  have k1 : (Over.map (thick R I e)).map g.i ≫ g.pG = 1 := by
    have h := GlobalTheory.TorusCoord.im_congr g k0
    rw [GlobalTheory.TorusCoord.im_one] at h
    exact h
  have e0 : g.i.left ≫ (padd D.P.A g.pG (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ D.c χ)).left =
      g.i.left ≫ (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ D.c χ).left := by
    change ((Over.map (thick R I e)).map g.i ≫ _).left = ((Over.map (thick R I e)).map g.i ≫ _).left
    have hp : padd D.P.A g.pG (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ D.c χ) =
        g.pG * (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ D.c χ) := rfl
    rw [hp, MonObj.comp_mul, k1, _root_.one_mul]
  have e2 : g.i.left ≫ g.pG.left = g.i.left ≫ (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ η).left := by
    change ((Over.map (thick R I e)).map g.i ≫ _).left = ((Over.map (thick R I e)).map g.i ≫ _).left
    rw [k1, ← Category.assoc, toUnit_unique ((Over.map (thick R I e)).map g.i ≫ toUnit _) (toUnit _)]
    rfl
  simp only [Fin.prod_univ_four, Oinvε, DegPre.Oφ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  erw [e0, e2]
  group

end Coord

theorem gm_char_zero {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S} (τ : Z ⟶ splitTorus S X)
    (z : Z.left) : gm τ.left z ⊤ (charUnit S X 0) = 1 := by
  have h := GlobalTheory.splitTorusPointsEquiv_val S X (splitTorus S X) (𝟙 _) 0
  rw [ofAdd_zero, map_one, Units.val_one] at h
  have h2 : charUnit S X 0 = 1 := by
    ext
    rw [Units.val_one, h]
    simp
  rw [h2, map_one]

theorem torus_ext {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S} (τ τ' : Z ⟶ splitTorus S X)
    (h : ∀ χ z, gm τ.left z ⊤ (charUnit S X χ) = gm τ'.left z ⊤ (charUnit S X χ)) : τ = τ' := by
  apply (splitTorusPointsEquiv S X Z).injective
  refine MonoidHom.ext fun χ => Units.ext ?_
  obtain ⟨x, rfl⟩ := Multiplicative.ofAdd.surjective χ
  rw [GlobalTheory.splitTorusPointsEquiv_val, GlobalTheory.splitTorusPointsEquiv_val]
  exact GlobalTheory.TorusCoord.appTop_eq_of_gm _ _ _ (h x)

section Pow

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {pD : IsPowDeg D'.toPre D.toPre j} {pA : IsPowPolAV A' A j} {pG : IsPowGrp G' G j}
  {U' : Unif I D' A' G'} {U : Unif I D A G}

theorem exists_factor (P : UnifPowOf3 pD pA pG U' U) (e : ℕ) (i : Fin j) :
    ∃ h : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X ⟶
        splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X,
      h ≫ (U.gt e).i = (U'.gt e).i ≫ (Over.pullback (thick R I e)).map (pG.pr i) := by
  have hk := (U.gt e).isKernel
  have hη : (η : 𝟙_ _ ⟶ thickObj R I e D'.toPre.P.A) ≫ (Over.pullback (thick R I e)).map (pD.pw.pr i) = η := by
    have hm := pD.pw.hom i
    change (_ ≫ _) ≫ _ = _ ≫ _
    rw [Category.assoc, ← Functor.map_comp, hm.one_hom]
  have hc : ((U'.gt e).i ≫ (Over.pullback (thick R I e)).map (pG.pr i)) ≫ (U.gt e).q =
      toUnit _ ≫ η := by
    rw [Category.assoc, ← P.q_pr e i, ← Category.assoc, (U'.gt e).isKernel.w, Category.assoc, hη]
  exact ⟨hk.lift _ _ hc, hk.lift_fst _ _ hc⟩


set_option maxHeartbeats 800000 in
theorem char_prod (P : UnifPowOf3 pD pA pG U' U) (e : ℕ)
    (h : Fin j → (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X ⟶
        splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X))
    (hh : ∀ i, h i ≫ (U.gt e).i = (U'.gt e).i ≫ (Over.pullback (thick R I e)).map (pG.pr i))
    (x : D'.toPre.X) (z : (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X).left) :
    gm (𝟙 _) z ⊤ (charUnit _ D'.toPre.X x) = ∏ i, gm (h i).left z ⊤ (charUnit _ D.toPre.X (pD.xe x i)) := by
  obtain ⟨J, hJ, -⟩ := exists_good D.toPre.P.L D.toPre.P.isLB z (K := PEmpty) (fun k => k.elim)
    (fun k => k.elim) (fun a => a.elim) (fun k => k.elim)
  obtain ⟨J', hJ', -⟩ := exists_good D'.toPre.P.L D'.toPre.P.isLB z (K := PEmpty) (fun k => k.elim)
    (fun k => k.elim) (fun a => a.elim) (fun k => k.elim)
  obtain ⟨hψ, H⟩ := P.t_pr e x
  have B := box_gen_val_along pD.w hψ ((U'.gt e).t x) (fun i => (U.gt e).t (pD.xe x i)) H
    (U'.gt e).i.left z hJ hJ'
  have hP := prod_on_torus (U'.gt e) x (fun ψ => bw pD.w ψ z (fun i => J (ψ ≫ (pD.pw.pr i).left)) (J' ψ))
  rw [hP, _root_.one_mul] at B
  have L1 := val_on_torus (U'.gt e) x hJ' (𝟙 _)
  rw [Category.id_comp] at L1
  rw [L1] at B
  refine B.trans (Finset.prod_congr rfl fun i _ => ?_)
  rw [← val_on_torus (U.gt e) (pD.xe x i) hJ (h i), hh i]
  rfl

end Pow

theorem torus_isPow : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : Unif I D' A' G') (U : Unif I D A G) (P : UnifPowOf3 pD pA pG U' U) (e : ℕ), ∃ pT : IsPowGrp (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X) (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X) j, (∀ i, (U'.gt e).i ≫ (Over.pullback (thick R I e)).map (pG.pr i) = pT.pr i ≫ (U.gt e).i) ∧ ∀ (i : Fin j) (χ : D.toPre.X), res (fun x _ => show (pT.pr i).left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial) (pullU (pT.pr i).left ⊤ (charUnit _ D.toPre.X χ)) = charUnit _ D'.toPre.X (pD.xe.symm (Pi.single i χ)) := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U' U P e
  obtain ⟨p, hp⟩ := GlobalTheory.exists_isPowGrp_splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X
    D'.toPre.X j pD.xe
  choose h hh using fun i => exists_factor P e i
  refine ⟨p, fun i => ?_, hp⟩
  have key : h i = p.pr i := by
    apply torus_ext
    intro χ z
    have c := char_prod P e h hh (pD.xe.symm (Pi.single i χ)) z
    rw [Finset.prod_eq_single i] at c
    · rw [AddEquiv.apply_symm_apply, Pi.single_eq_same] at c
      rw [← c]
      have hz := (gm_rp₁ (p.pr i).left z ⊤ ⊤ _ trivial (charUnit _ D.toPre.X χ)).symm.trans
        (congrArg (gm (𝟙 _) z ⊤) (hp i χ))
      exact hz.symm
    · intro b _ hb
      rw [AddEquiv.apply_symm_apply, Pi.single_eq_of_ne hb, gm_char_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [← hh i, key]

end GlobalTheory.PowTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecScalBoxSecGPre
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ExpandsBoxPre


set_option maxHeartbeats 2000000 in
theorem secScal_boxSecG_pre : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pG : IsPowGrp G' G j) (U' : UnifPre I D' A' G') (U : UnifPre I D A G) (wL : LB.Iso U'.LG.L (boxLB U.LG.L pG.pr)) (hw : wL.IsGen) (k : ℕ) (s : Fin j → U.SecK k) (σ : Fin j → H0 U.LG.L k) (r : Fin j → R), (∀ i, GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ)) (s i) (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) (σ i) (pullback.fst G.hom (jK R)) (scal (pullback.snd G.hom (jK R) ≫ jK R) (r i))) → ∀ s' : U'.SecK k, IsBoxSecK pG wL k s' s → GeneratorPullback.SecScal U'.LG.L (fun _ : Fin 1 => pullback.fst G'.hom (jK R)) (fun _ => (k : ℤ)) s' (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => (k : ℤ)) (boxSecG pG wL hw U.LG.isLB U'.LG.isLB k σ) (pullback.fst G'.hom (jK R)) (scal (pullback.snd G'.hom (jK R) ≫ jK R) (∏ i, r i)) := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pG U' U wL hw k s σ r hσ s' hs'
  intro j₁ j₂ hcoh
  have hj0 : j₁ 0 = j₂ 0 := hcoh (Sum.inl 0) (Sum.inr 0) (by simp)
  obtain ⟨jL, rfl⟩ : ∃ jL, j₁ = fun _ => jL := ⟨j₁ 0, funext fun x => by fin_cases x; rfl⟩
  obtain rfl : j₂ = fun _ => jL := funext fun x => by fin_cases x; exact hj0.symm
  set fst' := pullback.fst G'.hom (jK R) with hfst'
  set W := LB.wchart U'.LG.L (fun _ : Fin 1 => fst') (fun _ => jL) ⊓
    LB.wchart U'.LG.L (fun k => fst' ≫ (fun _ : Fin 1 => 𝟙 G'.left) k) (fun _ => jL) with hWdef
  have hcov : W ≤ ⨆ jN : Fin j → U.LG.L.ι, W ⊓ fst' ⁻¹ᵁ (boxLB U.LG.L pG.pr).U jN := by
    intro y hy
    have : fst'.base y ∈ (⨆ jN, (boxLB U.LG.L pG.pr).U jN : G'.left.Opens) := by
      rw [(linComb_isLB _ U.LG.isLB _ _).cover]; trivial
    obtain ⟨jN, hjN⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨jN, hy, hjN⟩
  apply sec_ext_cover W (fun jN => W ⊓ fst' ⁻¹ᵁ (boxLB U.LG.L pG.pr).U jN) (fun _ => inf_le_left) hcov
  intro jN
  apply ReciprocityTheory.ChartRestriction.G.Geo.Tor.fn_ext
  intro y hy
  have hyW : y ∈ W := hy.1
  have hyB : fst'.base y ∈ (boxLB U.LG.L pG.pr).U jN := hy.2
  have hyL : fst'.base y ∈ U'.LG.L.U jL := Set.mem_iInter.1 hyW.1 0
  have hyV : fst'.base y ∈ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jN, jL) := ⟨hyB, hyL⟩
  set snd' := pullback.snd G'.hom (jK R) ≫ jK R with hsnd'

  set u := Geo.Tor.gs fst' y ((LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jN, jL)) ((wL.s (jN, jL)) ^ k).val with hu
  set Lσ := Geo.Tor.gs fst' y (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL))
    ((boxSecG pG wL hw U.LG.isLB U'.LG.isLB k σ).f (fun _ => jL)) with hLσ
  set S := Geo.Tor.gs (𝟙 _) y (LB.wchart U'.LG.L (fun _ : Fin 1 => fst') (fun _ => jL)) (s'.f (fun _ => jL)) with hS
  set C := Geo.Tor.gs (𝟙 _) y ⊤ (scal snd' (∏ i, r i)) with hC
  have hA : u * Lσ = ∏ i, Geo.Tor.gs (fst' ≫ (pG.pr i).left) y (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jN i))
      ((σ i).f (fun _ => jN i)) := by
    have E := congrArg (Geo.Tor.gs fst' y ((LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jN, jL)))
      (isBoxSecG_boxSecG pG wL hw U.LG.isLB U'.LG.isLB k σ jN jL)
    refine (congrArg (u * ·) (Geo.Tor.gs_res _ _ (boxG_le_b pG jN jL) hyV _).symm).trans ?_
    refine (Geo.Tor.gs_mul _ _ _ hyV _ _).symm.trans (E.trans ?_)
    refine (gs_prod _ _ _ hyV _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
    exact (Geo.Tor.gs_res _ _ _ hyV _).trans
      (Geo.Tor.gs_pull _ _ _ _ (Set.mem_iInter.2 fun _ => by simpa using Set.mem_iInter.1 hyB i) _)
  have hB : ∀ i, Geo.Tor.gs (fst' ≫ (pG.pr i).left) y (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jN i))
      ((σ i).f (fun _ => jN i)) = Geo.Tor.gs (𝟙 _) y ⊤ (scal snd' (r i)) *
        Geo.Tor.gs (prK pG i) y (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => jN i))
          ((s i).f (fun _ => jN i)) := by
    intro i
    have hcoh_i : LB.Coh U.LG.L (Sum.elim (fun _ : Fin 1 => pullback.fst G.hom (jK R))
        (fun k => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k))
        (Sum.elim (fun _ : Fin 1 => jN i) (fun _ : Fin 1 => jN i)) := by
      intro a b _; rcases a with a | a <;> rcases b with b | b <;> rfl
    have hmemK : (pullback.fst G.hom (jK R)).base ((prK pG i).base y) ∈ U.LG.L.U (jN i) := by
      rw [← Scheme.Hom.comp_apply, prK_fst, Scheme.Hom.comp_apply]
      exact Set.mem_iInter.1 hyB i
    have hyi : (prK pG i).base y ∈ LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => jN i) ⊓
        LB.wchart U.LG.L (fun k => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k) (fun _ => jN i) :=
      ⟨Set.mem_iInter.2 fun _ => hmemK, Set.mem_iInter.2 fun _ => by simpa using hmemK⟩
    have E := congrArg (Geo.Tor.gs (prK pG i) y _) (hσ i (fun _ => jN i) (fun _ => jN i) hcoh_i)
    rw [← prK_fst]
    refine (Geo.Tor.gs_pull _ _ _ _ ?_ _).symm.trans ?_
    · exact Set.mem_iInter.2 fun _ => by simpa using hmemK
    refine (Geo.Tor.gs_res _ _ _ hyi _).symm.trans (E.trans ?_)
    refine (Geo.Tor.gs_mul _ _ _ hyi _ _).trans ?_
    congr 1
    · refine (Geo.Tor.gs_res _ _ _ hyi _).trans ?_
      show Geo.Tor.gs (prK pG i) y ⊤ (((pullback.snd G.hom (jK R) ≫ jK R).app ⊤).hom _) =
        Geo.Tor.gs (𝟙 _) y ⊤ ((snd'.app ⊤).hom _)
      refine (Geo.Tor.gs_pull (prK pG i) (pullback.snd G.hom (jK R) ≫ jK R) y ⊤ (by trivial) _).trans ?_
      refine Eq.trans ?_ (Geo.Tor.gs_pull (𝟙 _) snd' y ⊤ (by trivial) _).symm
      rw [← Category.assoc, boxScal_prK_snd, Category.id_comp]
    · exact Geo.Tor.gs_res _ _ _ hyi _
  have hCc : u * S = ∏ i, Geo.Tor.gs (prK pG i) y
      (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => jN i)) ((s i).f (fun _ => jN i)) := by
    have hyV' : (𝟙 (pullback G'.hom (jK R)) : _ ⟶ _) y ∈ fst' ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jN, jL) := hyV
    have E := congrArg (Geo.Tor.gs (𝟙 _) y (fst' ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jN, jL))) (hs' jN jL)
    have hu' : Geo.Tor.gs (𝟙 _) y (fst' ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jN, jL))
        ((pullU (Y := pullback G'.hom (jK R)) fst' _ (wL.s (jN, jL))) ^ k).val = u := by
      have e1 : ((pullU (Y := pullback G'.hom (jK R)) fst' _ (wL.s (jN, jL))) ^ k).val =
          (fst'.app _).hom ((wL.s (jN, jL)) ^ k).val := by
        rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow]; rfl
      rw [e1]
      exact (Geo.Tor.gs_pull _ _ _ _ hyV _).trans (by rw [Category.id_comp])
    refine (congrArg₂ (· * ·) hu'.symm (Geo.Tor.gs_res _ _ (boxSec_le_a pG jN jL) hyV' _).symm).trans ?_
    refine (Geo.Tor.gs_mul _ _ _ hyV' _ _).symm.trans (E.trans ?_)
    refine (gs_prod _ _ _ hyV' _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
    refine (Geo.Tor.gs_res _ _ _ hyV' _).trans
      ((Geo.Tor.gs_pull (𝟙 _) (prK pG i) y
        (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => jN i))
        (boxSec_le_b pG jN jL i hyV') _).trans ?_)
    rw [Category.id_comp]
  have hD : C = ∏ i, Geo.Tor.gs (𝟙 _) y ⊤ (scal snd' (r i)) := by
    rw [hC, show scal snd' (∏ i, r i) = ∏ i, scal snd' (r i) by simp [scal, map_prod],
      gs_prod _ _ _ (by trivial)]
  have hU : IsUnit u := by
    rw [hu, Geo.Tor.gs_unit _ _ _ hyV]; exact Units.isUnit _
  have hmain : Lσ = C * S := by
    apply hU.mul_left_cancel
    rw [hA, Finset.prod_congr rfl (fun i _ => hB i), Finset.prod_mul_distrib, ← hD, ← hCc]
    ring
  have hLg : Geo.Tor.gs (𝟙 _) y (W ⊓ fst' ⁻¹ᵁ (boxLB U.LG.L pG.pr).U jN) (rs (inf_le_left : W ⊓ fst' ⁻¹ᵁ (boxLB U.LG.L pG.pr).U jN ≤ W)
      (rs (inf_le_right.trans (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) :
        W ≤ fst' ⁻¹ᵁ LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL))
        ((fst'.app (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL))).hom
          ((boxSecG pG wL hw U.LG.isLB U'.LG.isLB k σ).f (fun _ => jL))))) = Lσ := by
    refine (Geo.Tor.gs_res _ _ _ hy _).trans ((Geo.Tor.gs_res _ _ _ hyW _).trans
      ((Geo.Tor.gs_pull _ _ _ _ ?_ _).trans ?_))
    · exact Set.mem_iInter.2 fun _ => by simpa using hyL
    · rw [Category.id_comp]
  have hRg : Geo.Tor.gs (𝟙 _) y (W ⊓ fst' ⁻¹ᵁ (boxLB U.LG.L pG.pr).U jN) (rs (inf_le_left : W ⊓ fst' ⁻¹ᵁ (boxLB U.LG.L pG.pr).U jN ≤ W)
      (resTop W (scal snd' (∏ i, r i)) * rs (inf_le_left : W ≤ LB.wchart U'.LG.L (fun _ : Fin 1 => fst') (fun _ => jL))
        (s'.f (fun _ => jL)))) = C * S := by
    refine (Geo.Tor.gs_res _ _ _ hy _).trans ((Geo.Tor.gs_mul _ _ _ hyW _ _).trans ?_)
    congr 1
    · exact Geo.Tor.gs_res _ _ _ hyW _
    · exact Geo.Tor.gs_res _ _ _ hyW _
  exact hLg.trans (hmain.trans hRg.symm)


set_option maxHeartbeats 1000000 in
theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : UnifPre I D' A' G') (U : UnifPre I D A G) (wL : LB.Iso U'.LG.L (boxLB U.LG.L pG.pr)), (∀ i, U'.gen.hom ≫ pA.pr i = (Over.pullback (jK R)).map (pG.pr i) ≫ U.gen.hom) ∧ wL.IsGen ∧ (∃ b : LB.Gen (LB.LinComb U.LG.L (K := Fin j) (fun i => eSec G' ≫ (pG.pr i).left) (fun _ => 1)), GeneratorPullback.MapsAt U.LG.L U'.LG.L (fun i => (pG.pr i).left) wL (eSec G') 1 U'.LG.rig b ∧ LB.Gen.Corr U.LG.L _ _ _ _ b (GeneratorPullback.finProdGen U.LG.L (J := Fin j) (fun _ _ => eSec G) (fun _ _ => 1) (fun _ => U.LG.rig))) ∧ (∀ (e : ℕ) (i : Fin j), (U'.gt e).q ≫ (Over.pullback (thick R I e)).map (pD.pw.pr i) = (Over.pullback (thick R I e)).map (pG.pr i) ≫ (U.gt e).q) ∧ (∀ (e : ℕ) (x : D'.toPre.X), ∃ hψ : ∀ (i : Fin j) (k : Fin 4), D'.toPre.Oφ ((Over.map (thick R I e)).map (U'.gt e).q ≫ D'.toPre.prBe I e) x k ≫ (pD.pw.pr i).left = ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫ D.toPre.Oφ ((Over.map (thick R I e)).map (U.gt e).q ≫ D.toPre.prBe I e) (pD.xe x i) k, LB.Gen.Maps (LB.linCombIso pD.w _ Oinvε) ((U'.gt e).t x) (GeneratorPullback.boxGen D.toPre.P.L (fun i => (pD.pw.pr i).left) _ Oinvε (fun i => GeneratorPullback.pullAlong D.toPre.P.L (pD.pw.pr i).left ((Over.pullback (thick R I e)).map (pG.pr i)).left _ Oinvε _ (hψ i) ((U.gt e).t (pD.xe x i))))) ∧ (∀ (e : ℕ) (jNM : Fin j → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL' : U'.LG.L.ι) (jNL : Fin j → U.LG.L.ι), res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_left) : (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM') ⊓ (LB.div (D'.toPre.P.L.pull (U'.gt e).pG.left) (U'.LG.L.pull (fstG I e G').left)).U (fun _ => jM', fun _ => jL') ⊓ (⨅ i, ((Over.pullback (thick R I e)).map (pG.pr i)).left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left) (U.LG.L.pull (fstG I e G).left)).U (fun _ => jNM i, fun _ => jNL i)) ⊓ (fstG I e G').left ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jNL, jL') ≤ (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM')) (pullU (U'.gt e).pG.left _ (pD.w.s (jNM, jM'))) * res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_right)) ((U'.w e).s (fun _ => jM', fun _ => jL')) = (∏ i, res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_right.trans (iInf_le _ i))) (pullU ((Over.pullback (thick R I e)).map (pG.pr i)).left _ ((U.w e).s (fun _ => jNM i, fun _ => jNL i)))) * res (X := (thickObj R I e G').left) inf_le_right (pullU (Y := (thickObj R I e G').left) (fstG I e G').left _ (wL.s (jNL, jL')))) → ∀ (k : ℕ) (s : Fin j → U.SecK k) (Fs : Fin j → Fam D.toPre (FractionRing R) k), (∀ i, U.Expands k (s i) (Fs i)) → ∀ (s' : U'.SecK k) (F' : Fam D'.toPre (FractionRing R) k), IsBoxSecK pG wL k s' s → IsBoxFam pD (FractionRing R) k F' Fs → U'.Expands k s' F' := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U' U wL h k s Fs hs s' F' hs' hF'
  choose r hr σ f hσ hf hE using hs
  refine ⟨∏ i, r i, Finset.prod_ne_zero_iff.2 fun i _ => hr i,
    boxSecG pG wL h.2.1 U.LG.isLB U'.LG.isLB k σ, boxFamB pD k f,
    secScal_boxSecG_pre R I j D D' A A' G G' pG U' U wL h.2.1 k s σ r hσ s' hs',
    fun α' => GlobalTheory.BoxFamScalar.main R I j D D' pD k Fs f r hf F' hF' α', fun e => ?_⟩
  exact GlobalTheory.BoxExpPre.expandsAt_box_unifPre R I j D D' A A' G G' pD pA pG U' U wL h k e σ f (fun i => hE i e) _ _
    (isBoxSecG_boxSecG pG wL h.2.1 U.LG.isLB U'.LG.isLB k σ) (isBoxFamB_boxFamB pD k f)

end GlobalTheory.ExpandsBoxPre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymBox
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PsiEvenBox

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily

theorem sym_box (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D D' : DegPre R}
    (pD : IsPowDeg D' D j) {Z : Scheme.{0}} (r : Z ⟶ D'.P.A.left) (y : Z) {J J'} (hJ : Good D.P.L y J)
    (hJ' : Good D'.P.L y J') :
    om pD.w y J J' (r ≫ (ι[D'.P.A]).left) * (om pD.w y J J' r)⁻¹ * val D'.sym r y J' =
      ∏ i, val D.sym (r ≫ (pD.pw.pr i).left) y J := by
  have hψ : ∀ (i : Fin j) (a : Fin 2), (![(ι[D'.P.A]).left, 𝟙 D'.P.A.left] : Fin 2 → _) a ≫ (pD.pw.pr i).left =
      (pD.pw.pr i).left ≫ (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → _) a := by
    intro i a
    have := pD.pw.hom i
    fin_cases a
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      rw [← Over.comp_left, ← Over.comp_left, GrpObj.inv_hom]
    · simp
  have he : eSec D'.P.A ≫ D'.P.A.hom = 𝟙 _ := Over.w η[D'.P.A]
  have hp : Function.Surjective D'.P.A.hom.appTop.hom := (hG _ D'.P.A D'.P.isAb).2
  have hinv : eSec D'.P.A ≫ (ι[D'.P.A]).left = eSec D'.P.A := by
    unfold eSec
    rw [← Over.comp_left, GrpObj.one_inv]
  have hpr : ∀ i, eSec D'.P.A ≫ (pD.pw.pr i).left = eSec D.P.A := fun i => by
    have := pD.pw.hom i
    unfold eSec
    rw [← Over.comp_left, IsMonHom.one_hom]
  have hone : ∀ (E : DegPre R) (z : ↥(𝟙_ (Over (Spec (CommRingCat.of R)))).left)
      (K : ((𝟙_ (Over (Spec (CommRingCat.of R)))).left ⟶ E.P.A.left) → E.P.L.ι), Good E.P.L z K →
      val E.sym (eSec E.P.A) z K = 1 := by
    intro E z K hK
    have h := val_corr hK E.sym_rig (𝟙 _)
    rw [val_pull hK, Category.id_comp, val_one] at h
    exact h
  have key := GlobalTheory.CubBox.box_unique (φ' := ![(ι[D'.P.A]).left, 𝟙 D'.P.A.left]) (φ := ![(ι[D.P.A]).left, 𝟙 D.P.A.left])
    (ε := ![1, -1]) (ρ := fun i => (pD.pw.pr i).left) D.P.isLB D'.P.isLB pD.w pD.w_gen hψ D'.sym_gen D.sym_gen
    D'.P.A.hom (eSec D'.P.A) he hp
  specialize key (by
    intro z K K' hK hK'
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg_one,
      Category.comp_id, hinv, hpr, mul_inv_cancel]
    rw [hone D' z K' hK', hone D z K hK, Finset.prod_const_one, _root_.mul_one]) Z r y J J' hJ hJ'
  rw [Fin.prod_univ_two] at key
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg_one,
    Category.comp_id] at key
  exact key

private theorem mul_mul_eq_mul_mul_mul_inv_mul {G : Type*} [CommGroup G] (a b c s : G) :
    b * c * s = a * (c * (b * a⁻¹ * s)) := by
  rw [← mul_inv_cancel_left a (b * c * s)]
  ac_rfl

theorem main : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j), D.PsiEven → D'.PsiEven := by
  intro hG R _ _ j D D' pD hE χ
  refine corr_of_val D'.P.isLB (fun y J' hJ' => ?_)
  obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
  have ha : D'.xK (-χ) = D'.xK χ ≫ (ι[D'.P.A]).left := by
    show ptK (D'.c (-χ)) = ptK (D'.c χ) ≫ (ι[D'.P.A]).left
    rw [GlobalTheory.PsiEvenPull.c_neg]
    unfold ptK
    rw [← Over.comp_left, Category.assoc]
  have hb : ∀ i, D'.xK χ ≫ (pD.pw.pr i).left = D.xK (pD.xe χ i) := by
    intro i
    have h := cPoint_pr pD (TK R) χ i
    unfold cP at h
    show ptK (D'.c χ) ≫ (pD.pw.pr i).left = ptK (D.c (pD.xe χ i))
    unfold ptK
    rw [← Over.comp_left, h]
  have hc : ∀ i, pD.xe (-χ) i = -pD.xe χ i := fun i => by
    rw [map_neg, Pi.neg_apply]
  have h4 : ∀ i, val (D.psi (pD.xe (-χ) i)) (𝟙 _) y J * val D.sym (D'.xK χ ≫ (pD.pw.pr i).left) y J =
      val (D.psi (pD.xe χ i)) (𝟙 _) y J := fun i => by
    have h := val_corr hJ (hE (pD.xe χ i)) (𝟙 _)
    rw [val_mul hJ, val_pull hJ, Category.id_comp] at h
    rw [hc, hb]
    exact h
  have h1 := psi_val pD hJ hJ' χ (𝟙 _)
  have h2 := psi_val pD hJ hJ' (-χ) (𝟙 _)
  have h3 := sym_box hG pD (D'.xK χ) y hJ hJ'
  rw [Category.id_comp, inv_mul_eq_iff_eq_mul] at h1 h2
  rw [ha] at h2
  rw [val_mul hJ', val_pull hJ', Category.id_comp, h1, h2]
  simp only [← h4, Finset.prod_mul_distrib]
  rw [← h3]
  exact mul_mul_eq_mul_mul_mul_inv_mul _ _ _ _

end GlobalTheory.PsiEvenBox
end
end

