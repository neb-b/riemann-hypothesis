module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2314
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2421
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesian
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0117
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2456
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2357
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOffClosedFibreDescended
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.OffClosed

theorem nonempty_preimage {S : Scheme.{0}} {G X : Over S} (O : G.left.Opens) (w w' : G ⊗ X ⟶ G)
    (h : lift w' (snd G X) ≫ w = fst G X) (z : (G ⊗ X).left) (hz : (fst G X).left z ∈ O) :
    ((w.left ⁻¹ᵁ O : (G ⊗ X).left.Opens) : Set (G ⊗ X).left).Nonempty := by
  refine ⟨(lift w' (snd G X)).left z, ?_⟩
  rw [← h] at hz
  simpa using hz

theorem exists_section (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsAdicComplete (maximalIdeal R) R) (G : Over (Sp R)) [GrpObj G] (hG : IsSemiAbelian G)
    (Ω : Type) [Field Ω] (x : Sp Ω ⟶ Sp R) (hx : closedPoint R ∉ Set.range x) (O : G.left.Opens) (pt : Sp Ω)
    (hO : ∃ g ∈ O, G.hom g = x pt) {J : Type} [Finite J] (k : J → (Over.mk x ⟶ G)) :
    ∃ a : 𝟙_ (Over (Sp R)) ⟶ G, ∀ i, (k i * (toUnit (Over.mk x) ≫ a)).left pt ∈ O ∧
      (k i * (toUnit (Over.mk x) ≫ a)⁻¹).left pt ∈ O := by
  have hirr : IrreducibleSpace (pullback G.hom x : Scheme.{0}) := _root_.GlobalTheory.SemiAbFibre.irreducibleSpace_fibre _ G hG Ω x
  obtain ⟨g, hg, hgx⟩ := hO
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := x) g pt hgx
  let X : Over (Sp R) := Over.mk x
  have hz' : (fst G X).left z ∈ O := by
    change pullback.fst G.hom x z ∈ O
    rw [hz]; exact hg
  let w : J × Bool → (G ⊗ X ⟶ G) := fun j =>
    match j.2 with
    | true => (snd G X ≫ k j.1) * fst G X
    | false => (snd G X ≫ k j.1) * (fst G X)⁻¹
  have hw : ∀ j, (((w j).left ⁻¹ᵁ O : (G ⊗ X).left.Opens) : Set (G ⊗ X).left).Nonempty := by
    rintro ⟨i, _ | _⟩
    · refine nonempty_preimage O _ ((fst G X)⁻¹ * (snd G X ≫ k i)) ?_ z hz'
      simp only [w, MonObj.comp_mul, GrpObj.comp_inv, lift_snd_assoc, lift_fst]
      group
    · refine nonempty_preimage O _ ((snd G X ≫ k i)⁻¹ * fst G X) ?_ z hz'
      simp only [w, MonObj.comp_mul, GrpObj.comp_inv, lift_snd_assoc, lift_fst]
      group
  have hirr' : IrreducibleSpace (G ⊗ X).left := hirr
  let U : (G ⊗ X).left.Opens :=
    ⟨⋂ j, (((w j).left ⁻¹ᵁ O : (G ⊗ X).left.Opens) : Set (G ⊗ X).left),
      isOpen_iInter_of_finite fun j => ((w j).left ⁻¹ᵁ O).isOpen⟩
  have hU : (U : Set (G ⊗ X).left).Nonempty := by
    refine ⟨genericPoint (G ⊗ X).left, Set.mem_iInter.2 fun j => ?_⟩
    exact ((genericPoint_spec (G ⊗ X).left).mem_open_set_iff ((w j).left ⁻¹ᵁ O).isOpen).2 (by simpa using hw j)
  obtain ⟨a, aΩ, ha, h1, h2, h3⟩ := _root_.GlobalTheory.DenseSec.dense_sections R hR G hG.smooth (η[G]).left (Over.w η[G]) Ω x hx hirr U hU
  let a' : 𝟙_ (Over (Sp R)) ⟶ G := Over.homMk a ha
  let u : X ⟶ G := toUnit X ≫ a'
  have hu : (lift u (𝟙 X)).left = aΩ := by
    apply pullback.hom_ext
    · refine Eq.trans ?_ h1.symm
      have : (lift u (𝟙 X)).left ≫ (fst G X).left = u.left := by rw [← Over.comp_left, lift_fst]
      exact this
    · refine Eq.trans ?_ h2.symm
      have : (lift u (𝟙 X)).left ≫ (snd G X).left = (𝟙 X : X ⟶ X).left := by rw [← Over.comp_left, lift_snd]
      exact this
  have key : ∀ j, (lift u (𝟙 X) ≫ w j).left pt ∈ O := by
    intro j
    have := Set.mem_iInter.1 (h3 ⟨pt, rfl⟩) j
    rw [← hu] at this
    exact this
  refine ⟨a', fun i => ⟨?_, ?_⟩⟩
  · have := key (i, true)
    simp only [w, MonObj.comp_mul, lift_snd_assoc, lift_fst, Category.id_comp] at this
    exact this
  · have := key (i, false)
    simp only [w, MonObj.comp_mul, GrpObj.comp_inv, lift_snd_assoc, lift_fst, Category.id_comp] at this
    exact this

theorem exists_ten (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsAdicComplete (maximalIdeal R) R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (O : G.left.Opens) (hO : ∃ g ∈ O, G.hom g = closedPoint R) (y : G.left) (hy : G.hom y ≠ closedPoint R) :
    ∃ a b c : G ⟶ G, ∀ f ∈ cubeTen (𝟙 G) a b c, f.left y ∈ O := by
  have := hG.smooth
  let Ω : Type := G.left.residueField y
  let yy : Sp Ω ⟶ G.left := G.left.fromSpecResidueField y
  let x : Sp Ω ⟶ Sp R := yy ≫ G.hom
  have hyy : ∀ p, yy p = y := fun p => by
    have : yy p ∈ Set.range (G.left.fromSpecResidueField y) := ⟨p, rfl⟩
    rw [Scheme.range_fromSpecResidueField] at this
    exact this
  have hx : ∀ p, x p = G.hom y := fun p => congrArg G.hom (hyy p)
  have hx' : closedPoint R ∉ Set.range x := by
    rintro ⟨p, hp⟩
    exact hy ((hx p).symm.trans hp)
  let pt : Sp Ω := closedPoint Ω
  have hO' : ∃ g ∈ O, G.hom g = x pt := by
    obtain ⟨g, hg, hgc⟩ := hO
    have hs : x pt ⤳ G.hom g := by rw [hgc]; exact specializes_closedPoint _
    obtain ⟨g', h1, h2⟩ := Flat.generalizingMap G.hom hs
    exact ⟨g', h1.mem_open O.isOpen hg, h2⟩
  let X : Over (Sp R) := Over.mk x
  let yh : X ⟶ G := Over.homMk yy rfl
  obtain ⟨a, ha⟩ := exists_section R hR G hG Ω x hx' O pt hO' ![(1 : Over.mk x ⟶ G), yh]
  obtain ⟨b, hb⟩ := exists_section R hR G hG Ω x hx' O pt hO' ![(1 : Over.mk x ⟶ G), yh]
  obtain ⟨c, hc⟩ := exists_section R hR G hG Ω x hx' O pt hO'
    ![(1 : Over.mk x ⟶ G), yh, (toUnit X ≫ b)⁻¹, yh * (toUnit X ≫ b)⁻¹]
  refine ⟨toUnit G ≫ a, toUnit G ≫ b, toUnit G ≫ c, fun f hf => ?_⟩
  have e : f.left y = (yh ≫ f).left pt := (congrArg f.left (hyy pt)).symm
  rw [e]
  have ht : ∀ d : 𝟙_ (Over (Sp R)) ⟶ G, yh ≫ toUnit G ≫ d = toUnit X ≫ d := fun d => by
    rw [← Category.assoc, comp_toUnit]
  have a0 := ha 0
  have a1 := ha 1
  have b0 := hb 0
  have b1 := hb 1
  have c0 := hc 0
  have c1 := hc 1
  have c2 := hc 2
  have c3 := hc 3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at a0 a1 b0 b1 c0 c1 c2 c3
  rw [_root_.one_mul, _root_.one_mul] at a0 b0 c0
  simp only [cubeTen, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, ht, mul_inv, ← _root_.mul_assoc]
  exacts [a1.1, a1.2, a0.1, a0.2, b1.1, c1.1, c3.2, b0.1, c0.1, c2.2]

theorem exists_gen_off_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G M.π β → ∀ (θ : P'.L.L.Sec) (O : G.left.Opens), (∃ g ∈ O, G.hom g = closedPoint R) → (∀ g : G'.left, β g ∈ O → G.hom (β g) = closedPoint R → ∃ i, g ∈ G'.left.basicOpen (θ.f i)) → ∀ y : G.left, G.hom y ≠ closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ t : LB.Gen (P'.L.L.pull (β ⁻¹ᵁ V).ι), t.IsGen := by
  intro R _ _ _ hR M G' _ _ _ P' G _ _ β hG hpb θ O hO hθ y hy
  have := hR.1
  have hβ : IsProper β := MorphismProperty.of_isPullback (P := @IsProper) hpb.1.flip M.proper
  let O' : G.left.Opens := ⟨farSet β θ, isOpen_farSet β β.isClosedMap θ⟩
  have hO' : ∃ g ∈ O', G.hom g = closedPoint R := by
    obtain ⟨g, hg, hgc⟩ := hO
    refine ⟨g, fun g' hg' => ?_, hgc⟩
    subst hg'
    exact TopologicalSpace.Opens.mem_iSup.2 (hθ g' hg hgc)
  obtain ⟨a, b, c, h⟩ := exists_ten R hR.2.2.2 G hG O' hO' y hy
  let V : G.left.Opens := ⟨⋂ f ∈ {f | f ∈ cubeTen (𝟙 G) a b c}, ((f.left ⁻¹ᵁ O' : G.left.Opens) : Set G.left),
    (List.finite_toSet _).isOpen_biInter fun f _ => (f.left ⁻¹ᵁ O').isOpen⟩
  refine ⟨V, Set.mem_iInter₂.2 h, ?_⟩
  obtain ⟨hl, hm⟩ := _root_.GlobalTheory.Mum.grpPullback_points_lift_mul_inv _ _ M.π G G' β hpb G' G β hpb.1.w
  obtain ⟨a', ha⟩ := hl a
  obtain ⟨b', hb⟩ := hl b
  obtain ⟨c', hc⟩ := hl c
  have h1 : (𝟙 G' : G' ⟶ G').left ≫ β = β ≫ (𝟙 G : G ⟶ G).left := by simp
  have mul := fun u v u' v' hu hv => (hm u v u' v' hu hv).1
  have inv := fun u u' hu => (hm u u u' u' hu hu).2
  have hten : ∀ f' ∈ cubeTen (𝟙 G') a' b' c', ∃ f ∈ cubeTen (𝟙 G) a b c, f'.left ≫ β = β ≫ f.left := by
    intro f' hf
    simp only [cubeTen, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 ha⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 (inv _ _ ha)⟩
    · exact ⟨_, by simp [cubeTen], ha⟩
    · exact ⟨_, by simp [cubeTen], inv _ _ ha⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 hb⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 hc⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 (inv _ _ (mul _ _ _ _ hb hc))⟩
    · exact ⟨_, by simp [cubeTen], hb⟩
    · exact ⟨_, by simp [cubeTen], hc⟩
    · exact ⟨_, by simp [cubeTen], inv _ _ (mul _ _ _ _ hb hc)⟩
  have := GlobalTheory.T.exists_generator_of_theoremOfCube_ten_points M.S G' P' θ G' (𝟙 G') a' b' c' (β ⁻¹ᵁ V) (by
    intro f' hf' g hg
    obtain ⟨f, hf, e⟩ := hten f' hf'
    have h2 : f.left (β g) ∈ farSet β θ := Set.mem_iInter₂.1 hg f hf
    refine h2 (f'.left g) ?_
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply])
  have e : (β ⁻¹ᵁ V).ι ≫ (𝟙 G' : G' ⟶ G').left = (β ⁻¹ᵁ V).ι := by simp
  rw [e] at this
  exact this

end GlobalTheory.Mum.OffClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorThetaConstantsFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.FibThetaMove

open GlobalTheory.Ex.OneGen GlobalTheory.ThetaPtMove GlobalTheory.ThetaPtUp GlobalTheory.UMin.ThMove

theorem exists_gen_thG_fibre : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K)
  (o : Type) [CommRing o] (g m : ℕ) (J : Type) (b : TBase o (m ^ 2)) (s : Sp K ⟶ Sp o) (t : TObj g (m ^ 2) J b s)
  (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
  IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ →
  LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) →
  ∀ v : Ix g (m ^ 2) → K, t.HasTh (𝟙 _) v →
  ∃ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))) (κ : K), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th ∧ κ ≠ 0 ∧
    ∀ a, ∃ y : Over.mk (spMap ev) ⟶ D.P.A, GlobalTheory.Ex.OneGen.ThG D.P.A D.P.L D.rig m th y (GlobalTheory.Ex.fnOf (κ * v a)) := by
  intro V₁ _ _ D K _ _ ev o _ g m J b s t ψ hψ hLB v H
  obtain ⟨w, hw⟩ := hLB
  have := t.ab.comm
  have := D.P.isAb.comm
  let F := (Over.pullback (spMap ev)).obj D.P.A
  have : IsCommMonObj F := Functor.isCommMonObj_obj
  let φF := pullback.fst D.P.A.hom (spMap ev)
  have hpD : IsGrpPullback F D.P.A (spMap ev) φF := isGrpPullback_pullback D.P.A (spMap ev)
  have hLD : D.P.L.IsLB := D.P.isLB
  have hLF : (D.P.L.pull φF).IsLB := pull_isLB hLD φF
  have hLt : t.L.IsLB := t.isLB
  have hw₁ : (idIso (D.P.L.pull φF)).IsGen := idIso_isGen hLF
  obtain ⟨ρF, hρF, hrF⟩ := exists_rigidificationPullbackCompatibleIso (w := idIso (D.P.L.pull φF)) (ρ₀ := D.rig) hpD hw₁ hLD hLF D.rig_gen

  have hE : eSec F ≫ ψ = 𝟙 _ ≫ eSec t.A := by
    have := over_one hψ (T := baseOver _) (T₀ := baseOver _) (𝟙 _) ((Category.comp_id _).trans (Category.id_comp _).symm)
    exact ((Category.id_comp _).symm.trans (Category.assoc _ _ _).symm).trans
      (this.symm.trans (congrArg (𝟙 _ ≫ ·) (Category.id_comp _)))
  obtain ⟨ρt, hρt, hrt'⟩ := exists_gen_up_iso (K := PUnit) (φ' := fun _ => eSec F) (φ := fun _ => eSec t.A)
    (ε := fun _ => 1) (h := 𝟙 _) (χ := 𝟙 _) hw hLt hLF (Category.id_comp _) (Category.id_comp _) (fun _ => hE) ρF hρF
  have hrt : IsRigidificationPullbackCompatibleIso w (𝟙 _) ρF ρt := fun Z r z J J' hJ hJ' =>
    (hrt' Z r z J J' hJ hJ').trans (by rw [Fintype.prod_unique, zpow_one])

  let x : Ix g (m ^ 2) → (baseOver (Sp K) ⟶ t.pol.A) := fun a =>
    (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ baseOver (Sp K)) ≫ t.lab a
  have hx : ∀ a, x a ^ (m ^ 2) = 1 := fun a => by
    show ((Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ baseOver (Sp K)) ≫ t.lab a) ^ (m ^ 2) = 1
    rw [← MonObj.comp_pow, lab_pow, MonObj.comp_one]
  obtain ⟨tht, hgt, hTt⟩ := exists_gen_thG_of_isThetaPt K t.pol ρt hρt m (Ix g (m ^ 2)) x v hx H

  have hτ₁ : 𝟙 (Sp K) ≫ (baseOver (Sp K)).hom = (baseOver (Sp K)).hom ≫ 𝟙 (Sp K) := by simp
  choose xF hxF hnF using fun a => torsion_down hψ (T := baseOver (Sp K)) (T₀ := baseOver (Sp K)) (𝟙 _) hτ₁ (x a) (hx a)
  obtain ⟨thF, hsF⟩ := exists_secRel hψ (T := baseOver (Sp K)) (T₀ := baseOver (Sp K)) (𝟙 _) hτ₁ hw hLt hLF tht
  have hgF := isGenSec_down hψ (𝟙 _) hτ₁ hw hLt hLF hsF hgt
  have hTF := fun a =>
    ThG.move hψ (𝟙 _) hτ₁ hw hLt hLF hrt (hxF a) (hnF a) hsF (hTt a)

  have hτ₂ : 𝟙 (Sp K) ≫ (Over.mk (spMap ev)).hom = (baseOver (Sp K)).hom ≫ spMap ev := by simp
  choose x₀ hx₀ hn₀ using fun a => torsion_up hpD (T := baseOver (Sp K)) (T₀ := Over.mk (spMap ev)) (𝟙 _) hτ₂ (xF a) (hnF a)
  obtain ⟨th₀, hs₀⟩ := exists_secRel_up hpD (T := baseOver (Sp K)) (T₀ := Over.mk (spMap ev)) (𝟙 _) hτ₂ hw₁ hLD hLF thF
  have hg₀ : IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th₀ := isGenSec_up hpD (T := baseOver (Sp K)) (T₀ := Over.mk (spMap ev)) (𝟙 _) hτ₂ hw₁ hLD hLF hs₀ hgF
  refine ⟨th₀, 1, hg₀, one_ne_zero, fun a => ⟨x₀ a, ?_⟩⟩
  have q := ThG.up hpD (T := baseOver (Sp K)) (T₀ := Over.mk (spMap ev)) (𝟙 _) hτ₂ hw₁ hLD hLF hrF (hx₀ a) (hn₀ a) hs₀ (hTF a)
  simpa using q

end GlobalTheory.FibThetaMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransportLinCombIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GenTransport

theorem exists_unflat {X X' Y : Scheme.{0}} {L : LB X} {J K : Type} [Fintype J] [Fintype K]
    (F : J → (X' ⟶ X)) (ε : J → ℤ) (ψ : K → (Y ⟶ X')) (δ : K → ℤ)
    (T : LB.Gen (LB.LinComb (LB.LinComb L F ε) ψ δ)) (hT : T.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L (K := K × J) (fun p => ψ p.1 ≫ F p.2) (fun p => δ p.1 * ε p.2)), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (I : (Z ⟶ X) → L.ι), Good L z I →
        val t r z I = val T r z (fun χ j => I (χ ≫ F j)) := by
  have le : ∀ p : K × J → L.ι, LB.wchart L (K := K × J) (fun p => ψ p.1 ≫ F p.2) p ≤
      LB.wchart (LB.LinComb L F ε) ψ (fun k j => p (k, j)) := fun p y hy =>
    Set.mem_iInter.2 fun k => by
      have h1 : ψ k y ∈ LB.wchart L F (fun j => p (k, j)) :=
        Set.mem_iInter.2 fun j => Set.mem_iInter.1 hy (k, j)
      exact h1
  let t : LB.Gen (LB.LinComb L (K := K × J) (fun p => ψ p.1 ≫ F p.2) (fun p => δ p.1 * ε p.2)) :=
    ⟨fun p => res (le p) (T.s fun k j => p (k, j))⟩
  refine ⟨t, isGen_of_gm _ fun y p q hp hq => ?_, fun Z r z I hI => ?_⟩
  · refine (gm_res _ y (le p) hp _).trans (Eq.trans ?_ (congrArg _ (gm_res _ y (le q) hq _)).symm)
    refine (gen_trans hT (𝟙 Y) y (le p hp) (le q hq)).trans (congrArg (· * _) ?_)
    refine (Finset.prod_congr rfl fun k _ => congrArg (· ^ δ k)
      (gm_linComb L F ε (𝟙 Y ≫ ψ k) y (fun j => p (k, j)) (fun j => q (k, j)) (Set.mem_iInter.1 (le p hp) k)
        (Set.mem_iInter.1 (le q hq) k))).trans ?_
    simp only [trF, Fintype.prod_prod_type, ← Finset.prod_zpow, ← zpow_mul, Category.assoc, mul_comm]
  · refine (gm_res r z (le _) (hI.mem (fun p : K × J => ψ p.1 ≫ F p.2) r) _).trans ?_
    exact (val_of T r z (fun χ j => I (χ ≫ F j)) _ fun k => funext fun j => congrArg I (Category.assoc _ _ _)).symm

theorem exists_transport : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {J K : Type} [Fintype J] [Fintype K], L.IsLB → L'.IsLB → ∀ (pr : J → (X' ⟶ X)) (ε : J → ℤ) (w : LB.Iso L' (LB.LinComb L pr ε)), w.IsGen → ∀ (φ' : K → (Y ⟶ X')) (δ : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' δ)), a.IsGen → ∃ t : LB.Gen (LB.LinComb L (fun p : K × J => φ' p.1 ≫ pr p.2) (fun p => δ p.1 * ε p.2)), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (I : (Z ⟶ X) → L.ι) (I' : (Z ⟶ X') → L'.ι), Good L z I → Good L' z I' → val t r z I = (∏ k, gv w (r ≫ φ' k) z (fun j => I ((r ≫ φ' k) ≫ pr j)) (I' (r ≫ φ' k)) ^ δ k) * val a r z I' := by
  intro X X' Y L L' J K _ _ hL hL' pr ε w hw φ' δ a ha
  obtain ⟨T, hT, hv⟩ := GlobalTheory.WtTower.exists_gen_of_iso (LB.isLB_linComb hL' φ' δ)
    (LB.isLB_linComb (LB.isLB_linComb hL pr ε) φ' δ) (LB.linCombIso w φ' δ) (DVR.linCombIso_isGen w hw _ _) a ha
  obtain ⟨t, ht, hv'⟩ := exists_unflat pr ε φ' δ T hT
  refine ⟨t, ht, fun Z r z I I' hI hI' => (hv' Z r z I hI).trans ?_⟩
  have hI'' : Good (LB.LinComb L pr ε) z (fun χ j => I (χ ≫ pr j)) := fun χ => hI.mem pr χ
  refine (hv Z r z _ (fun k => I' (r ≫ φ' k)) (hI''.mem φ' r) (hI'.mem φ' r)).trans (congrArg₂ (· * ·) ?_ rfl)
  exact GlobalTheory.WtTower.gm_linCombIso w φ' δ (fun k j => I ((r ≫ φ' k) ≫ pr j), fun k => I' (r ≫ φ' k)) r z
    ⟨hI''.mem φ' r, hI'.mem φ' r⟩

end GlobalTheory.Mum.GenTransport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedLineBundleSectionOverCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ThBdl

theorem resG_resG_glue {X : Scheme.{0}} {A B C : X.Opens} (h : B ≤ A) (h' : C ≤ B) (f : Γ(X, A)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem locSec_glue : ∀ (S : Scheme.{0}) (G : Over S) (L : LB G.left) (V : S.Opens) (κ : Type) (N : κ → S.Opens)
    (s : ∀ k, LocSec G L (N k)) (hN : ∀ k, N k ≤ V), (⨆ k, N k) = V → (∀ k, IsLocSec (s k)) →
    (∀ k k' i, resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N k ⊓ N k') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N k) (s k i) =
      resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N k ⊓ N k') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N k') (s k' i)) →
    ∃ s' : LocSec G L V, IsLocSec s' ∧ ∀ k i,
      resG _ (fun _ hx => ⟨hx.1, hN k hx.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ V) (s' i) = s k i := by
  intro S G L V κ N s hN hV hs hc
  have hmem : ∀ x : G.left, G.hom.base x ∈ V → ∃ k, G.hom.base x ∈ N k := by
    intro x hx
    have : G.hom.base x ∈ (⨆ k, N k) := by rw [hV]; exact hx
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have hcov : ∀ i, L.U i ⊓ G.hom ⁻¹ᵁ V ≤ ⨆ k, (L.U i ⊓ G.hom ⁻¹ᵁ N k) := by
    intro i x hx
    obtain ⟨k, hk⟩ := hmem x hx.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx.1, hk⟩
  have hWV : ∀ i k, L.U i ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ V := fun i k _ hx => ⟨hx.1, hN k hx.2⟩
  have hglue : ∀ i, ∃! t : Γ(G.left, L.U i ⊓ G.hom ⁻¹ᵁ V), ∀ k, resG _ (hWV i k) t = s k i := by
    intro i
    refine G.left.sheaf.existsUnique_gluing' (fun k => L.U i ⊓ G.hom ⁻¹ᵁ N k) (L.U i ⊓ G.hom ⁻¹ᵁ V)
      (fun k => homOfLE (hWV i k)) (hcov i) (fun k => s k i) ?_
    intro k k'
    have hle : (L.U i ⊓ G.hom ⁻¹ᵁ N k) ⊓ (L.U i ⊓ G.hom ⁻¹ᵁ N k') ≤ L.U i ⊓ G.hom ⁻¹ᵁ (N k ⊓ N k') :=
      fun _ hx => ⟨hx.1.1, hx.1.2, hx.2.2⟩
    have e := congrArg (resG _ hle) (hc k k' i)
    exact (resG_resG_glue _ _ _).symm.trans (e.trans (resG_resG_glue _ _ _))
  choose s' hs' _ using hglue
  refine ⟨s', ?_, fun k i => hs' i k⟩
  intro i j
  have hTV : ∀ k, L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ V := fun k _ hx => ⟨hx.1, hN k hx.2⟩
  refine G.left.sheaf.eq_of_locally_eq' (fun k => L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N k) (L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ V)
    (fun k => homOfLE (hTV k)) ?_ _ _ ?_
  · intro x hx
    obtain ⟨k, hk⟩ := hmem x hx.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx.1, hk⟩
  · intro k
    have hi1 : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ N k := fun _ hx => ⟨hx.1.1, hx.2⟩
    have hj1 : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N k ≤ L.U j ⊓ G.hom ⁻¹ᵁ N k := fun _ hx => ⟨hx.1.2, hx.2⟩
    have e1 : resG _ (hi1.trans (hWV i k)) (s' i) = resG _ hi1 (s k i) := by
      rw [← hs' i k, resG_resG_glue]
    have e2 : resG _ (hj1.trans (hWV j k)) (s' j) = resG _ hj1 (s k j) := by
      rw [← hs' j k, resG_resG_glue]
    change resG _ (hTV k) (resG _ _ (s' i)) =
      resG _ (hTV k) (resG _ _ (L.g i j : Γ(G.left, L.U i ⊓ L.U j)) * resG _ _ (s' j))
    rw [map_mul]
    refine ((resG_resG_glue _ _ _).trans e1).trans ((hs k i j).trans ?_)
    congr 1
    · exact (resG_resG_glue _ _ _).symm
    · exact ((resG_resG_glue _ _ _).trans e2).symm

end GlobalTheory.UMin.ThBdl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodHermPairAdaptedTwist
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem exists_good_pair_twist : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L N : HermLB p, ∃ (P : Pair p) (b : ℕ) (s t : X.functionField) (c : ℕ),
    P.L = L ∧ P.Good D b s t ∧ GenAt P c ∧ Regime P D ∧ Le ((P.A.pow c).dual) N := by
  intro hAC hHS k _ X _ p D hX L N
  obtain ⟨P₀, b, s, t, hL, hG⟩ := GlobalTheory.VolBr.exists_good_pair hAC k X p D hX L
  obtain ⟨c₀, hc₀, hgen⟩ := _root_.GlobalTheory.HSNef.AmpleGen.exists_genAt_mul k X p D hX P₀ hG.ample
  obtain ⟨c₁, hc₁⟩ := _root_.GlobalTheory.HSNef.TwistSmall.le_dual_pow_shift k X p D hX P₀ N s hG.ample hG.s_mem.1 hG.s_ne
  have hc : c₁ ≤ c₀ * (c₁ + 1) := by nlinarith
  have hcpos : 0 < c₀ * (c₁ + 1) := Nat.mul_pos hc₀ (Nat.succ_pos _)
  obtain ⟨u₁, hu₁⟩ := hc₁ (c₀ * (c₁ + 1)) hc hcpos
  obtain ⟨u₂, hu₂⟩ := _root_.GlobalTheory.HSNef.regime_shiftA hAC hHS k X p D hX P₀ hG.ample hG.nef.semiPos
  refine ⟨shiftA P₀ (max 0 (max u₁ u₂)), b, s, t, c₀ * (c₁ + 1), hL, ?_, ?_, ?_, ?_⟩
  · exact _root_.GlobalTheory.HSNef.good_shiftA k X p D hX P₀ b s t _ (le_max_left _ _) hG
  · exact (_root_.GlobalTheory.HSNef.shiftA_props k X p P₀ _).2.2 _ (hgen (c₁ + 1))
  · exact hu₂ _ (le_trans (le_max_right _ _) (le_max_right _ _))
  · exact hu₁ _ (le_trans (le_max_left _ _) (le_max_right _ _))

end GlobalTheory.HSNef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectionsEighthPowerGrpObj
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem eighthPower_inj_exists : ∀ {S : Scheme.{0}} (P C : Over S) [GrpObj P] [IsCommMonObj P] [GrpObj C] (pr : Fin 8 → (P ⟶ C)) (hpr : ∀ a, IsMonHom (pr a)) (huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ C)), ∃! x : T ⟶ P, ∀ a, x ≫ pr a = y a), ∃ inj : Fin 8 → (C ⟶ P), (∀ a, IsMonHom (inj a)) ∧ (∀ a b, inj a ≫ pr b = if a = b then 𝟙 C else 1) ∧ ∏ a, (pr a ≫ inj a) = 𝟙 P := by
  intro S P C _ _ _ pr hpr huniv
  have hext : ∀ {T : Over S} (f g : T ⟶ P), (∀ b, f ≫ pr b = g ≫ pr b) → f = g :=
    fun f g h => (huniv _ (fun b => g ≫ pr b)).unique h (fun _ => rfl)
  choose inj hinj using fun a => (huniv C (fun b => if a = b then 𝟙 C else 1)).exists
  have hmon : ∀ a, IsMonHom (inj a) := by
    intro a
    constructor
    · apply hext
      intro b
      haveI := hpr b
      rw [Category.assoc, hinj a b, IsMonHom.one_hom (pr b)]
      split_ifs
      · simp
      · rw [MonObj.comp_one, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    · apply hext
      intro b
      haveI := hpr b
      simp only [Category.assoc]
      rw [hinj a b, IsMonHom.mul_hom (pr b), tensorHom_comp_tensorHom_assoc, hinj a b]
      split_ifs
      · simp
      · rw [MonObj.comp_one, ← lift_fst_comp_snd_comp, ← Hom.mul_def, MonObj.comp_one, MonObj.comp_one, _root_.one_mul]
  refine ⟨inj, hmon, hinj, ?_⟩
  apply hext
  intro b
  haveI := hpr b
  rw [Fin.prod_univ_eight]
  simp only [MonObj.mul_comp, Category.assoc, hinj, MonObj.comp_one, Category.id_comp, Category.comp_id]
  fin_cases b <;> simp

end GlobalTheory
end

