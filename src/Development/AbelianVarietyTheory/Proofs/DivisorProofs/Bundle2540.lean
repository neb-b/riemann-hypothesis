module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2473
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2457
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2416
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRelationKillsMixedSectionSumsLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange GlobalTheory.Mum.Two.Mix

noncomputable section
namespace GlobalTheory.Mum.Two.Mix


set_option maxHeartbeats 1000000 in
theorem level : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Over₀ U₁ U₂ a b → ∀ (u : ∀ χ, LB.Gen (CmpLB D₁.toPre D₂.toPre b (h χ) χ)), (∀ χ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J → val ((U₂.gt e).t χ) (x ≫ ((Over.pullback (thick R I e)).map a).left) z (rr J) = val ((U₁.gt e).t (h χ)) x z (rl J) * val (u χ) (x ≫ (U₁.gt e).pG.left) z J) → ∀ (j j' e : ℕ) (N : Type) [Fintype N] (ρ : N → R) (σ : N → H0 U₂.LG.L j) (σ' : N → H0 U₁.LG.L j') (f : N → ∀ α : D₂.toPre.X, D₂.toPre.SecB j α) (f' : N → ∀ α : D₁.toPre.X, D₁.toPre.SecB j' α), (∀ ν, U₂.ExpandsAt e j (σ ν) (f ν)) → (∀ ν, U₁.ExpandsAt e j' (σ' ν) (f' ν)) → (∀ (Z : Scheme.{0}) (r : Z ⟶ G₁.left) (z : Z) (J₁ J₂), Good U₁.LG.L z J₁ → Good U₂.LG.L z J₂ → ∑ ν, constVal (r ≫ G₁.hom) z (ρ ν) * (sval (σ ν) (r ≫ a.left) z J₂ * sval (σ' ν) r z J₁) = 0) → ∀ (m : ∀ α, {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} → LB.Sec (LB.LinComb (JN D₁.toPre D₂.toPre) (mixφ D₁.toPre D₂.toPre b α) (MixedConv.mixε j j'))), (∀ α p (Z : Scheme.{0}) (r : Z ⟶ D₁.toPre.P.A.left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J → sval (m α p) r z J = ∑ ν, constVal (r ≫ D₁.toPre.P.A.hom) z (ρ ν) * (sval (f ν p.1.1) (r ≫ b.left) z (rr J) * sval (f' ν p.1.2) r z (rl J) * (val (u p.1.1) r z J * val (MixedConv.cubB D₁.toPre (h p.1.1) p.1.2) r z (rl J)).val)) → ∀ (α : D₁.toPre.X), ∃ S : Finset {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α}, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D₁.toPre.P.A).left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J → (∀ i ∉ S, sval (m α i) (r ≫ (D₁.toPre.prBe I e).left) z J = 0) ∧ ∑ i ∈ S, sval (m α i) (r ≫ (D₁.toPre.prBe I e).left) z J = 0 := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a b h hO u hu j j' e N _ ρ σ σ' f f' hE hE' hrel m hm α
  classical
  obtain ⟨S, hS⟩ := MixedConv.expand_common U₂ e j σ f hE
  obtain ⟨S', hS'⟩ := MixedConv.expand_common U₁ e j' σ' f' hE'
  have pl := isPart_inl D₁.toPre.P.L D₂.toPre.P.L
  have pr := isPart_inr D₁.toPre.P.L D₂.toPre.P.L
  let ae := ((Over.pullback (thick R I e)).map a).left
  have hpe : ae ≫ pGl U₂ e = pGl U₁ e ≫ b.left := by
    have h₁ := congrArg (fun q => q.left) (hO e)
    have h₂ : ((Over.pullback (thick R I e)).map b).left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ b.left :=
      pullback.lift_fst _ _ _
    show _ ≫ (U₂.gt e).q.left ≫ pullback.fst _ _ = ((U₁.gt e).q.left ≫ pullback.fst _ _) ≫ _
    rw [← Category.assoc]
    exact (congrArg (· ≫ pullback.fst _ _) h₁).trans ((Category.assoc _ _ _).trans
      ((congrArg ((U₁.gt e).q.left ≫ ·) h₂).trans (Category.assoc _ _ _).symm))
  have hfe : ae ≫ fGl I G₂ e = fGl I G₁ e ≫ a.left := pullback.lift_fst _ _ _
  have hp : ∀ {Z : Scheme.{0}} (x : Z ⟶ (thickObj R I e G₁).left),
      (x ≫ ae) ≫ pGl U₂ e = (x ≫ pGl U₁ e) ≫ b.left :=
    fun x => by rw [Category.assoc, Category.assoc, hpe]
  have hf : ∀ {Z : Scheme.{0}} (x : Z ⟶ (thickObj R I e G₁).left),
      (x ≫ ae) ≫ fGl I G₂ e = (x ≫ fGl I G₁ e) ≫ a.left :=
    fun x => by rw [Category.assoc, Category.assoc, hfe]
  let d : ∀ α, SecOver D₁.toPre.P.A.hom
      (LB.LinComb (JN D₁.toPre D₂.toPre) (mixφ D₁.toPre D₂.toPre b α) (MixedConv.mixε j j')) := fun α =>
    ∑ p ∈ (S ×ˢ S').subtype (fun p => h p.1 + p.2 = α), (m α p : SecOver D₁.toPre.P.A.hom _)
  have lift : ∀ n : LB.Sec (LB.LinComb (JN D₁.toPre D₂.toPre) (mixφ D₁.toPre D₂.toPre b α) (MixedConv.mixε j j')),
      (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J →
        sval n (x ≫ pGl U₁ e) z J = 0) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D₁.toPre.P.A).left) (z : Z) (J),
        Good (JN D₁.toPre D₂.toPre) z J → sval n (r ≫ (D₁.toPre.prBe I e).left) z J = 0 := fun n hn Z r z J hJ =>
    GlobalTheory.LiftTest.main R I D₁.toPre e G₁ (U₁.gt e) D₁.toPre.P.A (𝟙 _) _ (JN D₁.toPre D₂.toPre)
      (jn_isLB D₁.toPre D₂.toPre) _ _ _ n
      (fun Z x r hr z J hJ => by
        obtain rfl : r = x ≫ pGl U₁ e := (Category.comp_id r).symm.trans hr
        exact hn Z x z J hJ) Z _
      ⟨r ≫ pullback.snd _ _, by
        rw [Category.assoc, Category.assoc]; exact congrArg (r ≫ ·) pullback.condition.symm⟩ z J hJ
  refine ⟨(S ×ˢ S').subtype (fun p => h p.1 + p.2 = α), fun Z r z J hJ => ⟨fun i hi => ?_, ?_⟩⟩
  · refine lift _ (fun Z x z J hJ => ?_) Z r z J hJ
    rw [hm α i _ _ z J hJ]
    refine Finset.sum_eq_zero fun ν _ => ?_
    rw [Finset.mem_subtype, Finset.mem_product, not_and_or] at hi
    rcases hi with hi | hi
    · rw [← hp, (hS ν Z (x ≫ ae) z (rr J) (pr.good hJ)).1 _ hi, zero_mul, zero_mul, mul_zero]
    · rw [(hS' ν Z x z (rl J) (pl.good hJ)).1 _ hi, mul_zero, zero_mul, mul_zero]
  · refine (sval_sum' (π := D₁.toPre.P.A.hom) hJ _ _ _).symm.trans (lift (d α) (fun Z x z J hJ => ?_) Z r z J hJ)
    refine _root_.GlobalTheory.sval_eq_zero_of_sum_mul_coord_part R I D₁.toPre e G₁ (U₁.gt e) D₁.toPre.P.A (𝟙 _) _ (JN D₁.toPre D₂.toPre)
      (jn_isLB D₁.toPre D₂.toPre) coprod.inl Prod.fst pl _
      (mixφ D₁.toPre D₂.toPre b) (MixedConv.mixε j j') d (insert α ((S ×ˢ S').image fun p => h p.1 + p.2)) ?_ α
      (Finset.mem_insert_self _ _) Z x _ (Category.comp_id _) z J hJ
    intro Z x r hr z J hJ
    obtain rfl : r = x ≫ pGl U₁ e := (Category.comp_id r).symm.trans hr
    have hJl : Good D₁.toPre.P.L z (rl J) := pl.good hJ
    have hJr : Good D₂.toPre.P.L z (rr J) := pr.good hJ
    obtain ⟨J₁, hJ₁⟩ := CoefBasic.exists_good' U₁.LG.isLB z
    obtain ⟨J₂, hJ₂⟩ := CoefBasic.exists_good' U₂.LG.isLB z
    let T : D₂.toPre.X × D₁.toPre.X → Z.presheaf.stalk z := fun p =>
      ∑ ν, constVal ((x ≫ pGl U₁ e) ≫ D₁.toPre.P.A.hom) z (ρ ν) *
      ((sval (f ν p.1) ((x ≫ ae) ≫ pGl U₂ e) z (rr J) * (val (tG U₂ e p.1) (x ≫ ae) z (rr J)).val) *
        (sval (f' ν p.2) (x ≫ pGl U₁ e) z (rl J) * (val (tG U₁ e p.2) x z (rl J)).val))
    have k₁ : ∀ β, sval (d β) (x ≫ pGl U₁ e) z J * (val ((U₁.gt e).t β) x z (rs coprod.inl Prod.fst J)).val =
        ∑ p ∈ (S ×ˢ S').filter (fun p => h p.1 + p.2 = β), T p := fun β => by
      refine (congrArg (· * _) (sval_sum' (π := D₁.toPre.P.A.hom) hJ _ _ _)).trans ?_
      rw [← Finset.sum_subtype_eq_sum_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      obtain ⟨⟨χ, δ⟩, rfl⟩ := p
      rw [hm _ _ _ _ z J hJ, Finset.sum_mul]
      refine Finset.sum_congr rfl fun ν _ => ?_
      have a₁ := congrArg Units.val (MixedConv.t_mul_val U₁ e (h χ) δ x z hJl)
      have a₂ := congrArg Units.val (hu χ e Z x z J hJ)
      simp only [Units.val_mul] at a₁ a₂ ⊢
      rw [hp]
      linear_combination (constVal ((x ≫ pGl U₁ e) ≫ D₁.toPre.P.A.hom) z (ρ ν) *
        sval (f ν χ) ((x ≫ pGl U₁ e) ≫ b.left) z (rr J) * sval (f' ν δ) (x ≫ pGl U₁ e) z (rl J) *
        (val (u χ) (x ≫ pGl U₁ e) z J).val) * a₁ -
        (constVal ((x ≫ pGl U₁ e) ≫ D₁.toPre.P.A.hom) z (ρ ν) *
        sval (f ν χ) ((x ≫ pGl U₁ e) ≫ b.left) z (rr J) * sval (f' ν δ) (x ≫ pGl U₁ e) z (rl J) *
        (val (tG U₁ e δ) x z (rl J)).val) * a₂
    refine (Finset.sum_congr rfl fun β _ => k₁ β).trans ((Finset.sum_fiberwise_of_maps_to (fun p hp =>
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hp)) T).trans ?_)
    have hc : (x ≫ pGl U₁ e) ≫ D₁.toPre.P.A.hom = (x ≫ fGl I G₁ e) ≫ G₁.hom := by
      rw [Category.assoc, Category.assoc]
      exact congrArg (x ≫ ·) ((Over.w (U₁.gt e).pG).trans (Over.w (fstG I e G₁)).symm)
    have k₂ := hrel Z (x ≫ fGl I G₁ e) z J₁ J₂ hJ₁ hJ₂
    rw [Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl fun ν _ => ?_) ((Finset.mul_sum _ _ _).symm.trans
      ((congrArg (((wv U₂ e (x ≫ ae) z (rr J ((x ≫ ae) ≫ pGl U₂ e)) (J₂ (((x ≫ ae) ≫ fGl I G₂ e) ≫ 𝟙 _)) ^ j).val *
        (wv U₁ e x z (rl J (x ≫ pGl U₁ e)) (J₁ ((x ≫ fGl I G₁ e) ≫ 𝟙 _)) ^ j').val) * ·) k₂).trans (mul_zero _)))
    rw [← Finset.mul_sum, Finset.sum_product]
    dsimp only
    rw [← Finset.sum_mul_sum, ← (hS ν Z (x ≫ ae) z (rr J) hJr).2 J₂ hJ₂,
      ← (hS' ν Z x z (rl J) hJl).2 J₁ hJ₁, hc, ← hf]
    ring

end GlobalTheory.Mum.Two.Mix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBiextensionComparisonGeneratorOfAdjoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

noncomputable section

namespace GlobalTheory.Mum.PowData.CmpTwoProof

theorem oneGen_isGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := by
  intro i j
  have e : (LB.LinComb L (Y := Y) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim).g i j = 1 := by
    dsimp only [LB.LinComb]
    erw [Fintype.prod_empty]
    rfl
  show res _ (1 : Γ(Y, _)ˣ) = _ * res _ (1 : Γ(Y, _)ˣ)
  rw [map_one, map_one, e, _root_.one_mul]

theorem pull_cls_of_isPart {X X₁ : Scheme.{0}} {N : LB X} {M : LB X₁} {e : X₁ ⟶ X} {π : N.ι → M.ι}
    (h : IsPart N M e π) (hN : N.IsLB) (hM : M.IsLB) : CechPic.pull e (cls N hN) = cls M hM := by
  have h1 := LB.isLB_linComb hN (fun _ : PUnit.{1} => 𝟙 X₁ ≫ e) (fun _ => 1)
  have h2 := LB.isLB_linComb hM (fun _ : PUnit.{1} => 𝟙 X₁) (fun _ => 1)
  have a := cls_linComb hN _ _ h1
  have b := cls_linComb hM _ _ h2
  have c := (cls_eq_iff h1 h2).2 (iso_of_chart h2 (h.up (fun _ : PUnit.{1} => 𝟙 X₁) (fun _ => 1)))
  have := (a.symm.trans c).trans b
  simpa only [Fintype.sum_unique, one_smul, Category.id_comp, pull_id] using this

theorem comp_one_pt {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (u ≫ toUnit X) (toUnit Y)]

theorem one_comp_hom {S : Scheme.{0}} {X M N : Over S} [GrpObj M] [GrpObj N] (f : M ⟶ N) [IsMonHom f] :
    (1 : X ⟶ M) ≫ f = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]

end GlobalTheory.Mum.PowData.CmpTwoProof

open GlobalTheory.Mum.PowData.CmpTwoProof in
theorem GlobalTheory.Mum.PowData.cmpTwo_of_adjCls : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₀ : DegPre R) (q : D.P.A ⟶ D₀.P.A) (j : D₀.P.A ⟶ D.P.A), IsMonHom q → IsMonHom j → AdjCls (cls D.P.L D.P.isLB) (cls D₀.P.L D₀.P.isLB) q j → CmpTwo D D₀ q j := by
  intro R _ _ D D₀ q j hq hj hadj
  haveI := hq
  haveI := hj
  have hN : (JN D D₀).IsLB := jn_isLB D D₀
  have hG := GlobalTheory.globalFns_holds
  have pl := pull_cls_of_isPart (isPart_inl D.P.L D₀.P.L) hN D.P.isLB
  have pr := pull_cls_of_isPart (isPart_inr D.P.L D₀.P.L) hN D₀.P.isLB
  let φΓ : Fin 4 ⊕ Fin 4 → ((D.P.A ⊗ D₀.P.A).left ⟶ (D.P.A.left ⨿ D₀.P.A.left : Scheme.{0})) :=
    Sum.elim (fun k => lamPts (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A ≫ j) k ≫ coprod.inl)
      (fun k => lamPts (fst D.P.A D₀.P.A ≫ q) (snd D.P.A D₀.P.A) k ≫ coprod.inr)
  let εΓ : Fin 4 ⊕ Fin 4 → ℤ := Sum.elim Oε Oinvε
  have hL1 := LB.isLB_linComb hN φΓ εΓ

  have h0 : cls _ hL1 = 0 := by
    rw [cls_linComb hN _ _ hL1, Fintype.sum_sum_type, Fin.sum_univ_four, Fin.sum_univ_four]
    simp only [φΓ, εΓ, Sum.elim_inl, Sum.elim_inr, pull_comp, pl, pr]
    refine Eq.trans ?_ (sub_eq_zero.2 (hadj _ (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A)))
    simp only [lam, lamPts, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    abel
  obtain ⟨Γ₀, hΓ₀⟩ := (cls_eq_zero_iff hL1).1 h0

  let o : (D.P.A ⊗ D₀.P.A).left ⟶ (D.P.A ⊗ D₀.P.A).left :=
    (toUnit (D.P.A ⊗ D₀.P.A) ≫ lift (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A)).left
  have hz : ∀ k, o ≫ φΓ k = Sum.elim (fun _ : Fin 4 => (1 : D.P.A ⊗ D₀.P.A ⟶ D.P.A).left ≫ coprod.inl)
      (fun _ : Fin 4 => (1 : D.P.A ⊗ D₀.P.A ⟶ D₀.P.A).left ≫ coprod.inr) k := by
    rintro (k | k) <;> simp only [φΓ, Sum.elim_inl, Sum.elim_inr, ← Category.assoc] <;> congr 1 <;>
      fin_cases k <;>
      simp only [lamPts, o, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons, ← Over.comp_left, Category.assoc, MonObj.comp_mul, lift_fst, lift_snd,
        lift_fst_assoc, lift_snd_assoc, comp_one_pt, one_comp_hom, _root_.mul_one, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  have fe0 : FormEq (Sum.elim φΓ (fun k => o ≫ φΓ k)) (Sum.elim εΓ (fun k => - εΓ k)) φΓ εΓ := by
    intro U _ h
    have hQ : ∏ k, h (o ≫ φΓ k) ^ (- εΓ k) = 1 := by
      simp only [hz]
      rw [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four]
      simp only [Sum.elim_inl, Sum.elim_inr, εΓ, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_one]
      simp only [neg_neg, one_smul, neg_smul]
      abel
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [hQ, _root_.mul_one]
  obtain ⟨Γ, hΓ, hΓv⟩ := exists_gen hN fe0 (LB.mulGen _ _ _ _ _ Γ₀ (LB.invGen _ _ _ (LB.pullGen _ _ _ Γ₀ o)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hΓ₀ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hΓ₀ o)))
  have hone : ∀ (Z : Scheme.{0}) (r : Z ⟶ (D.P.A ⊗ D₀.P.A).left) (z : Z) (J), Good (JN D D₀) z J → r ≫ o = r →
      val Γ r z J = 1 := by
    intro Z r z J hJ hr
    rw [hΓv Z r z J hJ, val_mul hJ, val_inv, val_pull hJ, hr, mul_inv_cancel]
  have o₀ : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) = η[D₀.P.A] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have o' : (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) = η[D.P.A] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

  let ι₀ : D₀.P.A.left ⟶ (D.P.A ⊗ D₀.P.A).left := (lift (1 : D₀.P.A ⟶ D.P.A) (𝟙 D₀.P.A)).left
  have fe1 : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (fun k => ι₀ ≫ φΓ k) εΓ := by
    intro U _ h
    rw [Fintype.prod_empty, Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four]
    simp only [φΓ, εΓ, Sum.elim_inl, Sum.elim_inr, lamPts, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, ι₀, ← Category.assoc,
      ← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd, comp_one_pt, one_comp_hom, Category.id_comp,
      _root_.one_mul]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    simp only [one_smul, neg_smul]
    abel
  have e0 : (η[D₀.P.A] ≫ lift (1 : D₀.P.A ⟶ D.P.A) (𝟙 D₀.P.A)) ≫ toUnit _ ≫
      lift (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) =
      η[D₀.P.A] ≫ lift (1 : D₀.P.A ⟶ D.P.A) (𝟙 D₀.P.A) := by
    rw [← Category.assoc, toUnit_unique (_ ≫ toUnit _) (𝟙 _), Category.id_comp, comp_lift, comp_one_pt,
      Category.comp_id, o₀]
  have key1 := gen_unique' hN (u := LB.pullGen _ _ _ Γ ι₀) (u' := LB.oneGen (JN D D₀) (Y := D₀.P.A.left)) fe1
    D₀.P.A.hom (eSec D₀.P.A) (Over.w η[D₀.P.A]) (hG _ _ D₀.P.isAb).2 (DVR.pullGen_isGen _ _ _ _ hΓ ι₀)
    (oneGen_isGen _) (fun y J hJ => by
      rw [val_pull hJ, val_one]
      refine hone _ _ y J hJ ?_
      have := congrArg (fun f => f.left) e0
      simpa only [eSec, ι₀, o, Over.comp_left] using this)
  have hΓ1 : ∀ (T : Over (Sp R)) (w : T ⟶ D₀.P.A) (y : T.left) (J), Good (JN D D₀) y J →
      val Γ (lift (1 : T ⟶ D.P.A) w).left y J = 1 := by
    intro T w y J hJ
    have := key1 T.left w.left y J hJ
    rw [val_pull hJ, val_one] at this
    rwa [show w.left ≫ ι₀ = (lift (1 : T ⟶ D.P.A) w).left by
      rw [← Over.comp_left, comp_lift, comp_one_pt, Category.comp_id]] at this
  refine ⟨Γ, hΓ, ?_⟩
  intro χ' χ hc u hu T x z J hJ
  let m : D.P.A.left ⟶ (D.P.A ⊗ D₀.P.A).left := (lift (𝟙 D.P.A) (toUnit D.P.A ≫ D₀.c χ)).left
  have pm : ∀ {X Y : Over (Sp R)} [GrpObj Y] (a b : X ⟶ Y), padd Y a b = a * b := fun _ _ => rfl
  have fe2 : FormEq (fun k => m ≫ φΓ k) εΓ
      (Sum.elim (fun k => D.Oφ (𝟙 _) χ' k ≫ coprod.inl) (fun k => D₀.Oφ q χ k ≫ coprod.inr)) (Sum.elim Oε Oinvε) := by
    intro U _ h
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four, Fin.prod_univ_four,
      Fin.prod_univ_four]
    simp only [φΓ, εΓ, Sum.elim_inl, Sum.elim_inr, lamPts, DegPre.Oφ, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, m, pm, ← Hom.one_def, hc,
      ← Category.assoc, ← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd, Category.id_comp, Category.comp_id, comp_one_pt]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    simp only [one_smul, neg_smul]
    abel
  have ev2 : ∀ y I, Good (JN D D₀) y I → val u (eSec D.P.A) y I = val (LB.pullGen _ _ _ Γ m) (eSec D.P.A) y I := by
    intro y I hI
    rw [val_pull hI]
    have c := hu.2 _ (𝟙 _) y I hI
    rw [Category.id_comp] at c
    have e2 : eSec D.P.A ≫ m = (lift (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) (toUnit _ ≫ D₀.c χ)).left := by
      rw [eSec, ← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc,
        toUnit_unique (η[D.P.A] ≫ toUnit _) (toUnit _), o']
    rw [c, e2, hΓ1 _ _ y I hI]
  have key := gen_unique' hN (u := u) (u' := LB.pullGen _ _ _ Γ m) fe2 D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A])
    (hG _ _ D.P.isAb).2 hu.1 (DVR.pullGen_isGen _ _ _ _ hΓ m) ev2 T.left x.left z J hJ
  rw [key, val_pull hJ]
  congr 1
  rw [← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit T)]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClassSumOfAdicSumUnitSmulTerms
section
open IsLocalRing GlobalTheory.Poinc GlobalTheory.UT

namespace GlobalTheory.Poinc

theorem isClassSum_of_sumI : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (y : Φ.Y) (N : ℕ), 1 ≤ N → ∀ (κ : Fin s → Φ.X y) (c : Φ.Q) (V' : Type) [CommRing V'] [IsLocalRing V'] (io : Φ.V y →+* V') (e : V'ˣ) (x : V'), SumI (maximalIdeal V') (fun nu : Fin s → Φ.X y => (e : V') * io (Φ.term y (κ + N • nu) c)) x → Φ.IsClassSum y N κ c io (((e⁻¹ : V'ˣ) : V') * x) := by
  intro O _ bar q s W A _ _ Φ y N hN κ c V' _ _ io e x hx j
  classical
  have hinj : Function.Injective (fun nu : Fin s → Φ.X y => κ + N • nu) := by
    intro a b h
    have h1 : N • a = N • b := add_left_cancel h
    funext v
    have h2 : (N : ℤ) • a v = (N : ℤ) • b v := by
      rw [natCast_zsmul, natCast_zsmul]; exact congrFun h1 v
    exact smul_right_injective (Φ.X y) (by omega : (N : ℤ) ≠ 0) h2
  obtain ⟨N', -, -, -, hx⟩ := hx
  obtain ⟨S₀, hS₀⟩ := hx j
  have hF : ((fun nu : Fin s → Φ.X y => κ + N • nu) ⁻¹'
      {mu | True ∧ ∑ i, qW W (Φ.δ y i) mu < (j : ℤ)}).Finite :=
    (PreModel.low_finite Φ y (fun _ => True) j).preimage hinj.injOn
  refine ⟨(S₀ ∪ hF.toFinset).image (fun nu => κ + N • nu), ?_, ?_, ?_⟩
  · intro mu hmu v
    obtain ⟨nu, -, rfl⟩ := Finset.mem_image.1 hmu
    exact ⟨nu v, rfl⟩
  · intro mu hmu hn
    choose nu hnu using hmu
    have e1 : mu = κ + N • nu := funext hnu
    by_contra hlt
    refine hn (Finset.mem_image.2 ⟨nu, Finset.mem_union_right _ ?_, e1.symm⟩)
    rw [Set.Finite.mem_toFinset]
    exact ⟨trivial, by show ∑ i, qW W (Φ.δ y i) (κ + N • nu) < _; rw [← e1]; omega⟩
  · have h := Submodule.smul_mono le_rfl (le_top : N' ≤ ⊤) (hS₀ (S₀ ∪ hF.toFinset) Finset.subset_union_left)
    rw [smul_eq_mul, Ideal.mul_top, ← Finset.mul_sum] at h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_image hinj.injOn, map_sum]
    have h' := Ideal.mul_mem_left _ ((e⁻¹ : V'ˣ) : V') h
    rwa [mul_sub, Units.inv_mul_cancel_left] at h'

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormOneAddMulSmul
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.CxForm.HolAtlas

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem loc_one {i : A.ι} {v : V n} (hv : v ∈ (A.e i).target) : A.loc 1 i v = 1 := by
  rw [HolAtlas.loc, dite_eq_left hv]; rfl

theorem loc_add (α β : A.Fld) (i : A.ι) (v : V n) : A.loc (α + β) i v = A.loc α i v + A.loc β i v := by
  by_cases hv : v ∈ (A.e i).target
  · rw [HolAtlas.loc, HolAtlas.loc, HolAtlas.loc, dite_eq_left hv, dite_eq_left hv, dite_eq_left hv]; rfl
  · rw [HolAtlas.loc, HolAtlas.loc, HolAtlas.loc, dite_eq_right hv, dite_eq_right hv, dite_eq_right hv, add_zero]

theorem loc_mul (α β : A.Fld) (i : A.ι) (v : V n) : A.loc (α * β) i v = A.loc α i v * A.loc β i v := by
  by_cases hv : v ∈ (A.e i).target
  · rw [HolAtlas.loc, HolAtlas.loc, HolAtlas.loc, dite_eq_left hv, dite_eq_left hv, dite_eq_left hv]; rfl
  · rw [HolAtlas.loc, HolAtlas.loc, HolAtlas.loc, dite_eq_right hv, dite_eq_right hv, dite_eq_right hv, mul_zero]

theorem loc_smul (c : ℂ) (α : A.Fld) (i : A.ι) (v : V n) : A.loc (c • α) i v = c • A.loc α i v := by
  by_cases hv : v ∈ (A.e i).target
  · rw [HolAtlas.loc, HolAtlas.loc, dite_eq_left hv, dite_eq_left hv]; rfl
  · rw [HolAtlas.loc, HolAtlas.loc, dite_eq_right hv, dite_eq_right hv, smul_zero]

theorem isForm_algebra : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n), A.IsForm 1 ∧
    ∀ (c : ℂ) (α β : A.Fld), A.IsForm α → A.IsForm β → A.IsForm (α + β) ∧ A.IsForm (α * β) ∧ A.IsForm (c • α) := by
  intro M _ n A
  refine ⟨⟨fun i S => ?_, fun x x' _ => ?_⟩, fun c α β hα hβ => ⟨⟨fun i S => ?_, fun x x' h => ?_⟩,
    ⟨fun i S => ?_, fun x x' h => ?_⟩, ⟨fun i S => ?_, fun x x' h => ?_⟩⟩⟩
  · exact (contDiffOn_const (c := (bas n).repr (1 : Alt n) S)).congr fun v hv => by
      rw [loc_one A hv]
  · exact (map_one _).symm
  · exact ((hα.smooth i S).add (hβ.smooth i S)).congr fun v _ => by
      rw [loc_add, map_add (f := _), Finsupp.add_apply]
  · change α x + β x = pull _ (α x' + β x')
    rw [map_add (f := _), ← hα.compat x x' h, ← hβ.compat x x' h]
  · exact ((_root_.GlobalTheory.CxForm.contDiff_coeff_mul n n (A.loc α i) (A.loc β i)).1 _ (hα.smooth i) (hβ.smooth i) S).congr fun v _ => by
      rw [loc_mul]
  · change α x * β x = pull _ (α x' * β x')
    rw [map_mul, ← hα.compat x x' h, ← hβ.compat x x' h]
  · exact ((hα.smooth i S).const_smul c).congr fun v _ => by
      rw [loc_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  · change c • α x = pull _ (c • α x')
    rw [map_smul, ← hα.compat x x' h]

end GlobalTheory.CxForm.HolAtlas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackPasteFactorisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GrpPullbackPaste

theorem mul_left_congr {B : Scheme.{0}} (Gb : Over B) [GrpObj Gb] {X : Scheme.{0}} (a b : X ⟶ B) (hab : a = b)
    (x y : Over.mk a ⟶ Gb) (x' y' : Over.mk b ⟶ Gb) (hx : x.left = x'.left) (hy : y.left = y'.left) :
    (x * y).left = (x' * y').left := by
  subst hab
  have h1 : x = x' := Over.OverMorphism.ext hx
  have h2 : y = y' := Over.OverMorphism.ext hy
  rw [h1, h2]

end GlobalTheory.GrpPullbackPaste

open GlobalTheory.GrpPullbackPaste in
theorem GlobalTheory.isGrpPullback_paste : ∀ {B S T T' : Scheme.{0}} (Gb : Over B) [GrpObj Gb] (Gs : Over S) [GrpObj Gs] (Gt : Over T) [GrpObj Gt] (Gt' : Over T') [GrpObj Gt'] (fS : S ⟶ B) (fT : T ⟶ B) (g : T' ⟶ T) (h : T' ⟶ S) (φS : Gs.left ⟶ Gb.left) (φT : Gt.left ⟶ Gb.left) (ψ : Gt'.left ⟶ Gt.left), IsGrpPullback Gs Gb fS φS → IsGrpPullback Gt Gb fT φT → IsGrpPullback Gt' Gt g ψ → h ≫ fS = g ≫ fT → ∃ φ : Gt'.left ⟶ Gs.left, IsGrpPullback Gt' Gs h φ ∧ φ ≫ φS = ψ ≫ φT := by
  intro B S T T' Gb _ Gs _ Gt _ Gt' _ fS fT g h φS φT ψ hS hT hψ hcomm
  have hsq : (ψ ≫ φT) ≫ Gb.hom = (Gt'.hom ≫ h) ≫ fS := by
    rw [Category.assoc, hT.1.w, ← Category.assoc, hψ.1.w, Category.assoc, Category.assoc, hcomm]
  refine ⟨hS.1.lift (ψ ≫ φT) (Gt'.hom ≫ h) hsq, ⟨?_, ?_⟩, hS.1.lift_fst _ _ hsq⟩
  · have hpaste := hψ.1.paste_horiz hT.1
    refine IsPullback.of_right ?_ (hS.1.lift_snd _ _ hsq) hS.1
    rw [hS.1.lift_fst _ _ hsq, hcomm]
    exact hpaste
  · intro X x y x₀ y₀ hx hy
    set φ := hS.1.lift (ψ ≫ φT) (Gt'.hom ≫ h) hsq with hφ
    have hφ1 : φ ≫ φS = ψ ≫ φT := hS.1.lift_fst _ _ hsq
    have hφ2 : φ ≫ Gs.hom = Gt'.hom ≫ h := hS.1.lift_snd _ _ hsq
    let mk1 (z : Over.mk (X.hom ≫ h) ⟶ Gs) : Over.mk ((Over.mk (X.hom ≫ h)).hom ≫ fS) ⟶ Gb :=
      Over.homMk (z.left ≫ φS) (by
        simp only [Over.mk_hom, Category.assoc]
        rw [hS.1.w, ← Category.assoc, Over.w z]
        rfl)
    let mk2 (z : X ⟶ Gt') : Over.mk (X.hom ≫ g) ⟶ Gt :=
      Over.homMk (z.left ≫ ψ) (by
        simp only [Over.mk_hom, Category.assoc]
        rw [hψ.1.w, ← Category.assoc, Over.w z])
    let mk3 (z : Over.mk (X.hom ≫ g) ⟶ Gt) : Over.mk ((Over.mk (X.hom ≫ g)).hom ≫ fT) ⟶ Gb :=
      Over.homMk (z.left ≫ φT) (by
        simp only [Over.mk_hom, Category.assoc]
        rw [hT.1.w, ← Category.assoc, Over.w z]
        rfl)
    have e1 := hS.2 (Over.mk (X.hom ≫ h)) x₀ y₀ (mk1 x₀) (mk1 y₀) rfl rfl
    have e2 := hψ.2 X x y (mk2 x) (mk2 y) rfl rfl
    have e3 := hT.2 (Over.mk (X.hom ≫ g)) (mk2 x) (mk2 y) (mk3 (mk2 x)) (mk3 (mk2 y)) rfl rfl
    have hab : (Over.mk (X.hom ≫ h)).hom ≫ fS = (Over.mk (X.hom ≫ g)).hom ≫ fT := by
      simp only [Over.mk_hom, Category.assoc, hcomm]
    have e4 := mul_left_congr Gb _ _ hab (mk1 x₀) (mk1 y₀) (mk3 (mk2 x)) (mk3 (mk2 y))
      (by simp only [mk1, mk2, mk3, Over.homMk_left, hx, Category.assoc, hφ1])
      (by simp only [mk1, mk2, mk3, Over.homMk_left, hy, Category.assoc, hφ1])
    apply hS.1.hom_ext
    · rw [Category.assoc, hφ1, ← e1, e4, e3, ← Category.assoc, e2]
    · rw [Category.assoc, hφ2, ← Category.assoc, Over.w (x * y), Over.w (x₀ * y₀)]
      rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNoetherianFunctionFieldModelArithBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem ratModel_isNoetherian_of_arithBase : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), AlgebraicGeometry.IsNoetherian M.Z := by
  intro o Ω _ _ _ h M
  haveI := h.ded
  haveI := M.lft
  haveI := M.qc
  haveI : IsNoetherianRing (CommRingCat.of o) := inferInstanceAs (IsNoetherianRing o)
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  haveI : CompactSpace M.Z := QuasiCompact.compactSpace_of_compactSpace M.s
  exact {}

end GlobalTheory
end

