module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2978
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2477
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2600
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2735
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2579
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2595
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2995
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2973
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChernExistsUniqueAndIso
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2976
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2894
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2407
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3003
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodGens
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealPowLe
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.KerIdeal

theorem maximalIdeal_pow_le : ∀ (k : Type) [Field k] [IsAlgClosed k] (A B : Over (Sp k)) [GrpObj A] [IsCommMonObj A] [GrpObj B]
    [IsCommMonObj B] (π : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsMonHom π → IsIsogDeg π d →
    ∀ x₀ : A.left, x₀ ∈ Set.range (η[A]).left.base → ∀ J : Ideal (A.left.presheaf.stalk x₀),
    (∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'),
      (∃ z : Sp R' ⟶ Sp k, z ≫ (η[B]).left = (Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ≫ π.left) ↔
        J ≤ RingHom.ker ψ) →
    ∃ M : ℕ, IsLocalRing.maximalIdeal (A.left.presheaf.stalk x₀) ^ M ≤ J := by
  intro k _ _ A B _ _ _ _ π d hA hB hπ hiso x₀ hx₀ J hJ
  have := hA.smooth
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have := hiso.fin
  obtain ⟨s, rfl⟩ := hx₀
  have key : ∀ P : Ideal (A.left.presheaf.stalk ((η[A]).left.base s)), P.IsPrime → J ≤ P →
      P = IsLocalRing.maximalIdeal _ := by
    intro P hP hJP
    haveI := hP
    obtain ⟨z, hz⟩ := (hJ (A.left.presheaf.stalk ((η[A]).left.base s) ⧸ P) (Ideal.Quotient.mk P)).2
      (by rw [Ideal.mk_ker]; exact hJP)
    let q : Sp (A.left.presheaf.stalk ((η[A]).left.base s) ⧸ P) := ⟨⊥, Ideal.isPrime_bot⟩
    set g := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P)) with hg
    have hgq : g q = ⟨P, hP⟩ := by
      apply PrimeSpectrum.ext
      show Ideal.comap (Ideal.Quotient.mk P) ⊥ = P
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    set x₀ := (η[A]).left.base s with hx₀
    have hy : A.left.fromSpecStalk x₀ (g q) ⤳ x₀ := by
      have : A.left.fromSpecStalk x₀ (g q) ∈ Set.range (A.left.fromSpecStalk x₀) := ⟨_, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have h1 : π.left.base (A.left.fromSpecStalk x₀ (g q)) = (η[B]).left.base (z q) := by
      have := congrArg (fun m => m.base q) hz
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
      exact this.symm
    have h2 : π.left.base x₀ = (η[B]).left.base s := by
      have e : (η[A] ≫ π).left = (η[B]).left := by rw [IsMonHom.one_hom]
      have := congrArg (fun m => m.base s) e
      simpa only [Over.comp_left, Scheme.Hom.comp_base, TopCat.comp_app] using this
    have hzs : z q = s := Subsingleton.elim _ _
    have hyx : A.left.fromSpecStalk x₀ (g q) = x₀ :=
      GlobalTheory.eq_of_specializes_of_isIntegralHom π.left hy (by rw [h1, h2, hzs])
    have hgc : g q = IsLocalRing.closedPoint _ := by
      apply (A.left.fromSpecStalk x₀).isEmbedding.injective
      rw [hyx, Scheme.fromSpecStalk_closedPoint]
    have := congrArg PrimeSpectrum.asIdeal (hgq.symm.trans hgc)
    exact this
  have hrad : IsLocalRing.maximalIdeal _ ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    exact le_sInf fun P ⟨hJP, hP⟩ => (key P hP hJP).ge
  exact Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)

end GlobalTheory.KerIdeal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberLatticesIsoOfSpecialisingClosedPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

theorem exists_eq_nsmul_of_forall_dvd {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (L : ℕ) (x : X)
    (h : ∀ c : X →+ ℤ, (L : ℤ) ∣ c x) : ∃ w, x = L • w := by
  let b := Module.Free.chooseBasis ℤ X
  choose w hw using fun k => h (b.coord k).toAddMonoidHom
  refine ⟨∑ k, w k • b k, ?_⟩
  rw [Finset.smul_sum, ← b.sum_repr x]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : b.repr x k = L * w k := hw k
  rw [this, mul_smul, natCast_zsmul]

theorem injective_of_ker_le {X Y : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup Y]
    [Module.Free ℤ Y] (ρ : X →+ Y) (L : ℕ) (hL : 2 ≤ L) (h : ∀ x, ρ x = 0 → ∃ w, x = L • w) : Function.Injective ρ := by
  refine (injective_iff_map_eq_zero ρ).2 fun x hx => ?_
  have key : ∀ k : ℕ, ∃ w, ρ w = 0 ∧ x = L ^ k • w := by
    intro k
    induction k with
    | zero => exact ⟨x, hx, by simp⟩
    | succ k ih =>
      obtain ⟨w, hw, rfl⟩ := ih
      obtain ⟨w', rfl⟩ := h w hw
      refine ⟨w', ?_, by rw [smul_smul, pow_succ]⟩
      rw [map_nsmul, ← natCast_zsmul] at hw
      exact (smul_eq_zero.1 hw).resolve_left (by omega)
  let b := Module.Free.chooseBasis ℤ X
  refine b.repr.injective (Finsupp.ext fun k => ?_)
  obtain ⟨w, -, hw⟩ := key (b.repr x k).natAbs
  rw [map_zero, Finsupp.zero_apply]
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (d := ((L ^ (b.repr x k).natAbs : ℕ) : ℤ)) ⟨b.repr w k, ?_⟩ ?_
  · conv_lhs => rw [hw]
    rw [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
  · rw [Int.natAbs_natCast]
    exact Nat.lt_pow_self (by omega)

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {Y : RatModel X₁.o₁ X₁.Ω₁} {πY : Y.Z ⟶ X₁.M.Z} {U₀ : Y.Z.Opens} {EE : Y.Lat X₁.S.J} (FinalForm : ZHOut X₁.ρ Y U₀ EE)
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
  (𝔫 : UMem X₁ z₁ act V ev X t δ) {ξ : Sp V ⟶ Y.Z}


include 𝔫 in
theorem base_of_uMem : GlobalTheory.Mum.Base V :=
  ⟨⟨𝔫.cn.1, inferInstance, 𝔫.cn.2.1, 𝔫.cn.2.2.1⟩, 𝔫.cn.2.2.2⟩

theorem exists_link (hO : X₁.S.Over₀ Y U₀) (hπ : X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY)
    (hξ : ξ ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) :
    ∃ β : 𝔫.G.left ⟶ FinalForm.G.left, IsGrpPullback 𝔫.G FinalForm.G ξ β ∧
      Link FinalForm (jK V ≫ ξ) (spMap 𝔫.yK) 𝔫.A.A 𝔫.φ (genMap 𝔫.U ≫ β) ∧
      ∀ (f : X₁.ρ.P.A ⟶ X₁.ρ.P.A) (Fm : FinalForm.G ⟶ FinalForm.G), EndOn FinalForm f Fm → ∀ E : EndU 𝔫.U.toUnifPre,
        E.aA.left ≫ 𝔫.φ = 𝔫.φ ≫ f.left → E.aG.left ≫ β = β ≫ Fm.left := by
  have e : (jK V ≫ ξ) ≫ πY = jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ := by rw [Category.assoc, hξ]
  have hreg : ∀ a ∈ X₁.S.R, a ∈ X₁.M.O (πY ((jK V ≫ ξ) (closedPoint (FractionRing V)))) := fun a ha => by
    have := 𝔫.reg a ha
    rw [← e] at this
    exact this
  obtain ⟨O, _, _, _, _, _, _, xO, u, v, h₁, h₂, h₃, h₄⟩ := _root_.GlobalTheory.Poinc.Sep.Spz.exists_stalk_factor X₁.o₁ X₁.Ω₁ Y hO.normal X₁.S.R (FractionRing V)
    (jK V ≫ ξ) 𝔫.yK (fun a ha => hπ.map_mem_O (hreg a ha)) (fun a => by
      rw [𝔫.yK_eq, ← e]
      exact hπ.val_comp _ _ (hreg a a.2))
  obtain ⟨gm, hgm⟩ := _root_.GlobalTheory.Poinc.Sep.Spz.link_of_normal X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ Y U₀ EE FinalForm hO.ne O xO u h₁ h₂
  have e₂ : spMap v ≫ spMap u = spMap 𝔫.yK := (GlobalTheory.SpreadTrait.spMap_comp' u v).trans (congrArg spMap h₄)
  obtain ⟨w, hw, hwφ⟩ := GlobalTheory.SpreadTrait.pull_cancel (isGrpPullback_pullback X₁.ρ.P.A (spMap u)) (spMap v)
    (𝔫.cart.congr e₂.symm rfl)
  have hl := hgm.pull FinalForm hw
  rw [h₃, e₂, hwφ] at hl
  obtain ⟨β, hβ, hβg, hE⟩ := _root_.GlobalTheory.Poinc.Sep.Spz.exists_ext Y.Z FinalForm.G FinalForm.semi V (base_of_uMem 𝔫) 𝔫.G 𝔫.semi 𝔫.D 𝔫.A 𝔫.U ξ _ hl.1
  refine ⟨β, hβ, hβg ▸ hl, fun f Fm hf E h => hE E Fm ?_⟩
  have := hl.2.1 f Fm hf _ (𝟙 _) E.aA.left ((Over.w E.aA).trans (Category.id_comp _).symm)
    (h.trans (Category.id_comp _).symm)
  exact this.trans (Category.id_comp _)

theorem yK_algebraMap (hπ : X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY)
    (hξ : ξ ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) :
    ∃ oV : X₁.o₁ →+* V, ξ ≫ Y.s = spMap oV ∧
      ∀ a, 𝔫.yK (algebraMap X₁.o₁ X₁.S.R a) = algebraMap V (FractionRing V) (oV a) := by
  have h : ξ ≫ Y.s = spMap (Spec.preimage (ξ ≫ Y.s)).hom := (Spec.map_preimage _).symm
  refine ⟨_, h, fun a => ?_⟩
  rw [𝔫.yK_eq, ← hξ]
  refine RatModel.val_algebraMap (σ := (algebraMap V (FractionRing V)).comp (Spec.preimage (ξ ≫ Y.s)).hom) ?_ a
  rw [Category.assoc, Category.assoc, hπ.inducedModelMorphism_comp_structureMap]
  exact (congrArg (jK V ≫ ·) h).trans (GlobalTheory.SpreadTrait.spMap_comp' _ _)

theorem pow_eq_one_of_qkToAkU {K : Type} [Field K] [Algebra (FractionRing V) K] {k : ℕ} {q : QkPt 𝔫.D.toPre K k}
    {x : TFK (R := V) K ⟶ 𝔫.A.A} (h : QkToAkU 𝔫.U.toUnifPre K k q x) : x ^ k = 1 := by
  obtain ⟨w, hw⟩ := 𝔫.U.ext
  exact (h w hw).1

theorem pt_eq_sec {β : 𝔫.G.left ⟶ FinalForm.G.left}
    (hl : Link FinalForm (jK V ≫ ξ) (spMap 𝔫.yK) 𝔫.A.A 𝔫.φ (genMap 𝔫.U ≫ β)) {a : X₁.S.Gam} {Wo : Y.Z.Opens}
    {h : Wo.toScheme ⟶ FinalForm.G.left} (hs : SecOn FinalForm a Wo h) {ξ' : Sp V ⟶ Wo.toScheme} (hξ' : ξ' ≫ Wo.ι = ξ)
    (K : Type) [Field K] [Algebra (FractionRing V) K] (x : TFK (R := V) K ⟶ 𝔫.A.A)
    (hx : x.left ≫ 𝔫.φ = spMap ((algebraMap (FractionRing V) K).comp 𝔫.yK) ≫ (X₁.ρ.pt a).left) :
    x.left ≫ genMap 𝔫.U ≫ β = spMap (algebraMap (FractionRing V) K) ≫ jK V ≫ ξ' ≫ h := by
  have e : x.left ≫ 𝔫.A.A.hom = spMap (algebraMap (FractionRing V) K) := Over.w x
  have := hl.2.2 a Wo h hs _ x.left (spMap (algebraMap (FractionRing V) K) ≫ jK V ≫ ξ') (by
    rw [reassoc_of% e]
    simp only [Category.assoc, hξ']) (by
    rw [reassoc_of% e, hx, ← GlobalTheory.SpreadTrait.spMap_comp', Category.assoc])
  simpa only [Category.assoc] using this

end GlobalTheory.Poinc.Sep.Spz

theorem GlobalTheory.Poinc.Sep.Spz.latTo_of_specializes : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] [IsDiscreteValuationRing V₁] (ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (X₀ : Type) [AddCommGroup X₀] (m₁ : ℕ) (t₁ : Fin m₁ → V₁) (δ₁ : Fin m₁ → LinearMap.BilinForm ℤ X₀) (𝔫₁ : UMem X₁ z₁ act V₁ ev₁ X₀ t₁ δ₁) (ξ₁ : Sp V₁ ⟶ Y.Z) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] [IsDiscreteValuationRing V₂] (ev₂ : X₁.M.Z.presheaf.stalk z₁ →+* V₂) (X : Type) [AddCommGroup X] (m₂ : ℕ) (t₂ : Fin m₂ → V₂) (δ₂ : Fin m₂ → LinearMap.BilinForm ℤ X) (𝔫₂ : UMem X₁ z₁ act V₂ ev₂ X t₂ δ₂) (ξ₂ : Sp V₂ ⟶ Y.Z), ξ₁ ≫ πY = spMap ev₁ ≫ X₁.M.Z.fromSpecStalk z₁ → ξ₂ ≫ πY = spMap ev₂ ≫ X₁.M.Z.fromSpecStalk z₁ → ξ₁ (closedPoint V₁) ⤳ ξ₂ (closedPoint V₂) → Cmp.LatTo 𝔫₁ 𝔫₂ := by
  intro g n F W Z i X₁ z₁ act hact Y πY hZ V₁ _ _ _ _ ev₁ X₀ _ m₁ t₁ δ₁ 𝔫₁ ξ₁ V₂ _ _ _ _ ev₂ X _ m₂ t₂ δ₂ 𝔫₂ ξ₂ hξ₁ hξ₂ hsp
  obtain ⟨U₀, EE, ⟨FinalForm⟩, hO, -, hπ, -⟩ := hZ
  obtain ⟨β₁, hβ₁, hl₁, hE₁⟩ := exists_link FinalForm 𝔫₁ hO hπ hξ₁
  obtain ⟨β₂, hβ₂, hl₂, hE₂⟩ := exists_link FinalForm 𝔫₂ hO hπ hξ₂
  obtain ⟨o₁, ho₁, hy₁⟩ := yK_algebraMap 𝔫₁ hπ hξ₁
  obtain ⟨o₂, ho₂, hy₂⟩ := yK_algebraMap 𝔫₂ hπ hξ₂
  have b₁ := base_of_uMem 𝔫₁
  have b₂ := base_of_uMem 𝔫₂
  obtain ⟨ρ, hρ⟩ := _root_.GlobalTheory.Poinc.Sep.Spz.exists_spread₂ Y.Z FinalForm.G FinalForm.semi V₁ b₁ 𝔫₁.G 𝔫₁.semi 𝔫₁.D 𝔫₁.A 𝔫₁.U ξ₁ β₁ hβ₁ V₂ b₂ 𝔫₂.G 𝔫₂.semi 𝔫₂.D 𝔫₂.A
    𝔫₂.U ξ₂ β₂ hβ₂ inferInstance (by
      haveI := ArithBase.ded (o := X₁.o₁) (Ω := X₁.Ω₁)
      haveI := Y.lft
      exact LocallyOfFiniteType.isLocallyNoetherian Y.s) hsp
  have onto := _root_.GlobalTheory.Poinc.Sep.Spz.spread₂_surjective Y.Z FinalForm.G FinalForm.semi V₁ b₁ 𝔫₁.G 𝔫₁.semi 𝔫₁.D 𝔫₁.A 𝔫₁.U ξ₁ β₁ hβ₁ V₂ b₂ 𝔫₂.G 𝔫₂.semi 𝔫₂.D 𝔫₂.A
    𝔫₂.U ξ₂ β₂ hβ₂ ρ hρ
  have eqv := _root_.GlobalTheory.Poinc.Sep.Spz.spread₂_endU_comm Y.Z FinalForm.G FinalForm.semi V₁ b₁ 𝔫₁.G 𝔫₁.semi 𝔫₁.D 𝔫₁.A 𝔫₁.U ξ₁ β₁ hβ₁ V₂ b₂ 𝔫₂.G 𝔫₂.semi 𝔫₂.D 𝔫₂.A
    𝔫₂.U ξ₂ β₂ hβ₂ ρ hρ
  have tor := GlobalTheory.T.toricTorsionSection_of_spread_through_latticeMap Y.Z FinalForm.G FinalForm.semi V₁ b₁ 𝔫₁.G 𝔫₁.semi 𝔫₁.D 𝔫₁.A 𝔫₁.U ξ₁ β₁ hβ₁ V₂ b₂ 𝔫₂.G 𝔫₂.semi 𝔫₂.D 𝔫₂.A
    𝔫₂.U ξ₂ β₂ hβ₂ ρ hρ X₁.o₁ Y.s o₁ o₂ ho₁ ho₂
  obtain ⟨tot₁, sur₁, cong₁, -⟩ := GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i X₁ z₁ act V₁ ev₁ X₀ m₁ t₁ δ₁ 𝔫₁
  obtain ⟨tot₂, sur₂, cong₂, -⟩ := GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i X₁ z₁ act V₂ ev₂ X m₂ t₂ δ₂ 𝔫₂
  obtain ⟨x₀, hx₀⟩ := X₁.div z₁
  have int₁ := _root_.GlobalTheory.Poinc.Sep.mem_HH_iff_yy_zero g n F W Z i X₁ z₁ act x₀ hx₀ V₁ ev₁ X₀ m₁ t₁ δ₁ 𝔫₁
  have int₂ := _root_.GlobalTheory.Poinc.Sep.mem_HH_iff_yy_zero g n F W Z i X₁ z₁ act x₀ hx₀ V₂ ev₂ X m₂ t₂ δ₂ 𝔫₂
  obtain ⟨sg, weil⟩ := GlobalTheory.T.toricTorsionPoint_character_eq_weilPairing_label g n F W Z i X₁ z₁ act
  have hL : 2 ≤ X₁.S.r * X₁.S.N := le_trans X₁.S.N_ge (Nat.le_mul_of_pos_left _ X₁.S.r_pos)
  have hζ : (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) ^ (X₁.S.r * X₁.S.N) = 1 := by
    rw [← pow_mul, ← sq]; exact X₁.S.prim.pow_eq_one

  have hy : πY (ξ₂ (closedPoint V₂)) = z₁ := by
    haveI := 𝔫₂.loc
    have : (ξ₂ ≫ πY) (closedPoint V₂) = z₁ := by
      rw [hξ₂]
      exact (congrArg (X₁.M.Z.fromSpecStalk z₁) (IsLocalRing.comap_closedPoint ev₂)).trans
        Scheme.fromSpecStalk_closedPoint
    exact this
  have hHH : X₁.S.HH X₁.M z₁ ≤ X₁.S.HH Y (ξ₂ (closedPoint V₂)) :=
    AddSubgroup.closure_mono fun a ha => hπ.div (t := X₁.S.th) (hy.symm ▸ ha)

  have lab : ∀ a mu₁ mu₂, 𝔫₁.YY a mu₁ → 𝔫₂.YY a mu₂ →
      ∃ w, 𝔫₁.e₈ mu₁ - ρ (𝔫₂.e₈ mu₂) = (X₁.S.r * X₁.S.N) • w := by
    intro a mu₁ mu₂ h₁ h₂
    refine exists_eq_nsmul_of_forall_dvd _ _ fun c => ?_
    obtain ⟨x₁, hx₁⟩ := GlobalTheory.T.exists_toric_torsion_point_of_lattice_character V₁ b₁ 𝔫₁.G 𝔫₁.semi 𝔫₁.D 𝔫₁.A 𝔫₁.U (AlgebraicClosure (FractionRing V₁))
      (X₁.S.r * X₁.S.N) (algebraMap (FractionRing V₁) _ (algebraMap V₁ _ (o₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))))) (by omega)
      (by rw [← map_pow, ← map_pow, ← map_pow, hζ, map_one, map_one, map_one]) c
    obtain ⟨τ', q, hτ', hq, hq', hQ⟩ := id hx₁
    obtain ⟨τ, hτ⟩ := GlobalTheory.Poinc.IntTerm.torsion_has_label g n F W Z i X₁ z₁ act V₁ ev₁ X₀ m₁ t₁ δ₁ 𝔫₁ x₁ (pow_eq_one_of_qkToAkU 𝔫₁ hQ)
    have hH : τ ∈ X₁.S.HH X₁.M z₁ := (int₁ τ).2 ⟨q, x₁, hq.trans (map_zero _).symm, hQ, hτ⟩
    obtain ⟨Wo, h, hW, hs⟩ := FinalForm.sec _ τ (hHH hH)
    have lift : ∀ {V : Type} [CommRing V] [IsLocalRing V] (ξ : Sp V ⟶ Y.Z), ξ (closedPoint V) ∈ Wo →
        ∃ ξ' : Sp V ⟶ Wo.toScheme, ξ' ≫ Wo.ι = ξ := fun ξ hξ =>
      ⟨IsOpenImmersion.lift Wo.ι ξ (by
        rintro _ ⟨w, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact ((IsLocalRing.specializes_closedPoint w).map ξ.continuous).mem_open Wo.isOpen hξ),
        IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨ξ₁', hξ₁'⟩ := lift ξ₁ (hsp.mem_open Wo.isOpen hW)
    obtain ⟨ξ₂', hξ₂'⟩ := lift ξ₂ hW
    obtain ⟨-, q₂, x₂, -, hQ₂, hx₂'⟩ := tot₂ τ
    have hx₂ := pow_eq_one_of_qkToAkU 𝔫₂ hQ₂
    have ht := tor _ _ (by omega) X₁.S.unit hζ Wo h ξ₁' ξ₂' hs.1 hξ₁' hξ₂' _ _ c x₁ x₂ hx₁
      (pt_eq_sec FinalForm 𝔫₁ hl₁ hs hξ₁' _ x₁ hτ) hx₂ (pt_eq_sec FinalForm 𝔫₂ hl₂ hs hξ₂' _ x₂ hx₂')
    rw [← hy₁] at hx₁
    rw [← hy₂] at ht
    have w₁ := weil V₁ ev₁ X₀ m₁ t₁ δ₁ 𝔫₁ τ c x₁ hx₁ hτ a mu₁ h₁
    have w₂ := weil V₂ ev₂ X m₂ t₂ δ₂ 𝔫₂ τ _ x₂ ht hx₂' a mu₂ h₂
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, map_sub, Int.cast_sub, w₁, sub_eq_zero]
    exact w₂.symm
  have vec : ∀ {X' : Type} [AddCommGroup X'] (mu mu' w : Fin 8 → X'), mu' = mu + (X₁.S.r * X₁.S.N) • w →
      ∀ v, CongMod (X₁.S.r * X₁.S.N) (mu' v) (mu v) := fun mu mu' w h v => ⟨w v, congrFun h v⟩
  have inj : Function.Injective ρ := by
    refine injective_of_ker_le ρ _ hL fun y hy0 => ?_
    obtain ⟨mu, rfl⟩ := 𝔫₂.e₈.surjective y
    obtain ⟨a, ha⟩ := sur₂ mu
    obtain ⟨mu₁, h₁⟩ := tot₁ a
    obtain ⟨w, hw⟩ := lab a mu₁ mu h₁ ha
    have h0 : 𝔫₁.YY a 0 := (cong₁ a mu₁ 0 h₁).2 (vec _ _ (-𝔫₁.e₈.symm w) (𝔫₁.e₈.injective (by
      rw [hy0, sub_zero] at hw
      simp [hw])))
    have h0' := (cong₂ a 0 mu ((int₂ a).1 ((int₁ a).2 h0))).1 ha
    choose w' hw' using h0'
    exact ⟨𝔫₂.e₈ w', by rw [← map_nsmul]; exact congrArg _ (funext fun v => by simpa using hw' v)⟩
  let e := AddEquiv.ofBijective ρ ⟨inj, onto⟩
  let K : (Fin 8 → X₀) ≃+ (Fin 8 → X) := (𝔫₁.e₈.trans e.symm).trans 𝔫₂.e₈.symm
  have hK : ∀ mu, ρ (𝔫₂.e₈ (K mu)) = 𝔫₁.e₈ mu := fun mu => by
    simp only [K, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
    exact e.apply_symm_apply _
  refine ⟨K, fun a' mu => ?_, fun a mu h₁ => ?_⟩
  · have hdet : (W + W.transpose).det = 1 := X₁.e8.2
    have ha : (W + W.transpose) * a' = ((W + W.transpose) * a' * (W + W.transpose).adjugate).transpose.transpose *
        (W + W.transpose) := by
      rw [Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.adjugate_mul, hdet, one_smul, Matrix.mul_one]
    obtain ⟨E₁, h₁, h₁'⟩ := 𝔫₁.equiv _ a' ha
    obtain ⟨E₂, h₂, h₂'⟩ := 𝔫₂.equiv _ a' ha
    obtain ⟨Fm, hF⟩ := _root_.GlobalTheory.Poinc.Sep.Spz.endOn_exists X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ Y U₀ EE FinalForm hO.ne _ (hact.isMonHom _)
    apply 𝔫₂.e₈.injective
    apply inj
    rw [hK, ← h₂', eqv Fm E₁ E₂ (hE₁ _ Fm hF E₁ h₁) (hE₂ _ Fm hF E₂ h₂), hK, h₁']
  · obtain ⟨mu₂, h₂⟩ := tot₂ a
    obtain ⟨w, hw⟩ := lab a mu mu₂ h₁ h₂
    obtain ⟨w', rfl⟩ := onto w
    refine (cong₂ a mu₂ _ h₂).2 (vec _ _ (𝔫₂.e₈.symm w') (𝔫₂.e₈.injective (inj ?_)))
    rw [hK, map_add (f := _), map_add (f := _), map_nsmul, map_nsmul, AddEquiv.apply_symm_apply, ← hw, add_sub_cancel]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NsmulZarhinDiagonalClassEqFormStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nsmul_zarhinDiagonalClass_eq_form : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 0 < d → d • GlobalTheory.CechPic.pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left (GlobalTheory.ZarhinFam.zCls c.A B c.isLB hZ.2.1.isLB d mu) = ∑ kl : Fin 8 × Fin 8, GlobalTheory.ZarhinFam.zW d kl.1 kl.2 • GlobalTheory.CechPic.pull (lift (GlobalTheory.ZarhinFam.zpr c.A B mu kl.1) (GlobalTheory.ZarhinFam.zpr c.A B mu kl.2)).left (GlobalTheory.CechPic.cls c.P c.isLB) := by
  first | (exact @GlobalTheory.ZarhinFam.nsmul_pull_diag_zCls) | (exact GlobalTheory.ZarhinFam.nsmul_pull_diag_zCls) | (intros; apply GlobalTheory.ZarhinFam.nsmul_pull_diag_zCls  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingIsPerfectAbelianSchemesBothKernelsZero
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AbDual.isPerfPair_of_abelianHodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → φ.IsPerfPair := by
  intro H R _ A B _ _ g hA hB hgA hgB P hP φ hφ
  obtain ⟨Fr, -, BC⟩ := _root_.GlobalTheory.abelianDeRham_free_hodge_baseChange H
  obtain ⟨fA, pA, -⟩ := Published.AbelianDeRham.Free.prim Fr hA hgA
  obtain ⟨fB, pB, -⟩ := Published.AbelianDeRham.Free.prim Fr hB hgB
  refine _root_.GlobalTheory.PairFibres.isPerfPair_of_fibres₂ R (primDR A) (primDR B) φ ?_
  intro Ω _ _ _
  have iA := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback A (spMap (algebraMap R Ω))
  have iB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback B (spMap (algebraMap R Ω))
  obtain ⟨h, h₁, h₂⟩ := AbDual.exists_prod_pullback iA iB
  have hP' := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hP.isLB h
  have perf' := AbDual.IsPerfect.baseChange iA iB h₁ h₂ hP' (Cris.ChernExists.lbIso_refl hP') hP
  obtain ⟨φ', hφ', hcorr⟩ := hφ.pull hP.isLB (Published.AbelianDeRham.bcMor iA) (Published.AbelianDeRham.bcMor iB) h₁ h₂ hP'
    (Cris.ChernExists.lbIso_refl hP')
  have hA' := isAbelianScheme_pullback_obj (spMap (algebraMap R Ω)) A hA
  have hB' := isAbelianScheme_pullback_obj (spMap (algebraMap R Ω)) B hB
  have hgA' : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R Ω))).obj A).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hgA
  have hgB' : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R Ω))).obj B).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hgB
  exact ⟨primDR _, primDR _, inferInstance, inferInstance, inferInstance, inferInstance,
    (Published.AbelianDeRham.bcMor iA).pull, (Published.AbelianDeRham.bcMor iB).pull, φ',
    (BC R A g hA hgA Ω _ _ iA).1, (BC R B g hB hgB Ω _ _ iB).1,
    _root_.GlobalTheory.FieldPerf.isPerfPair H Ω _ _ g hA' hB' hgA' hgB' _ perf' φ' hφ', fun x x' y y' hx hy ↦ hcorr x x' y y' hx hy⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodGeneratorsValLocalUnitsMulSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory.USep.EvG.AtPoint

theorem gm_stalkMap {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (a : Γ(X, U)ˣ) :
    Units.map (r.stalkMap z).hom.toMonoidHom (gm f (r z) U a) = gm (r ≫ f) z U a := by
  by_cases h : f (r z) ∈ U
  · apply Units.ext
    rw [Units.coe_map, gm_val f (r z) U h, gm_val (r ≫ f) z U h]
    exact Scheme.Hom.germ_stalkMap_apply r (f ⁻¹ᵁ U) z h _
  · have h' : (r ≫ f) z ∉ U := h
    rw [gm, dite_eq_right h, gm, dite_eq_right h']
    simp

theorem val_stalkMap {X Y Y' Z : Scheme.{0}} {L : LB X} {Ix : Type} [Fintype Ix] {φ : Ix → (Y ⟶ X)} {ε : Ix → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (g : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) (J : (Z ⟶ X) → L.ι) :
    Units.map (r.stalkMap z).hom.toMonoidHom (val t g (r z) (fun ψ => J (r ≫ ψ))) = val t (r ≫ g) z J := by
  rw [val_of t (r ≫ g) z J (fun k => J (r ≫ g ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gm_stalkMap r g z _ _

end GlobalTheory.USep.EvG.AtPoint

open GlobalTheory.USep.EvG.AtPoint in
theorem GlobalTheory.USep.EvG.fromBase_tau_val : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ a b : D.X, ∃ c ∈ k₀, (val (τ₀ a b) (spMap ev) z J).val =
      (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c (a + b)).left) * (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a).left))⁻¹ *
        (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c b).left))⁻¹ * GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c 0).left)).val * toStk z c := by
  intro V₁ _ _ _ _ _ D τ₀ W₀ _ ib B₀ _ M₀ c₀ τ₁ β w hFB K _ _ ev k₀ _ hk z J J₀ hJ hJ₀ a b
  obtain ⟨-, -, -, -, -, -, hlast⟩ := hFB
  have hJ' : Good D.P.L ((spMap ev) z) (fun ψ => J (spMap ev ≫ ψ)) := fun ψ => hJ (spMap ev ≫ ψ)
  have hJ₀' : Good M₀ ((spMap ev) z) (fun ψ => J₀ (spMap ev ≫ ψ)) := fun ψ => hJ₀ (spMap ev ≫ ψ)
  have E := congrArg (Units.map ((spMap ev).stalkMap z).hom.toMonoidHom) (hlast a b ((spMap ev) z) _ _ hJ' hJ₀')
  simp only [map_mul, map_inv, val_stalkMap, gm_stalkMap, Category.comp_id] at E
  have hg : ∀ x : D.X, gm (spMap ev ≫ UChart.cpt D x) z
      (((M₀.pull β).div D.P.L).U (fun _ => J₀ (spMap ev ≫ UChart.cpt D x ≫ β), J (spMap ev ≫ UChart.cpt D x)))
      (w.s (fun _ => J₀ (spMap ev ≫ UChart.cpt D x ≫ β), J (spMap ev ≫ UChart.cpt D x))) =
      GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c x).left) := by
    intro x
    show _ = gw w _ z _ _
    rw [Category.assoc]
    rfl
  rw [hg (a + b), hg a, hg b, hg 0, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp] at E
  obtain ⟨c, hc, hv⟩ := GlobalTheory.Poinc.Sep.val_spMap_mem k₀ (τ₁ a b) (ev.comp ib) hk z hJ₀
  refine ⟨c, hc, ?_⟩
  rw [E, Units.val_mul, hv]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowLeftOfIsGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FamTorsion

theorem one_left_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  let u : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    simp only [Over.mk_hom, Category.assoc]
    rw [h.1.w, ← Category.assoc, Over.w])
  have hu : u * u = u := Over.OverMorphism.ext (by
    rw [h.2 T 1 1 u u rfl rfl, _root_.mul_one]; rfl)
  have : u = 1 := mul_eq_left.1 hu
  rw [← this]
  rfl

theorem pow_left_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ f) ⟶ G)
    (hx : x₀.left = x.left ≫ φ) (n : ℕ) : (x₀ ^ n).left = (x ^ n).left ≫ φ := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact one_left_of_isGrpPullback h T
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact h.2 T _ _ _ _ ih hx

end GlobalTheory.FamTorsion
end

