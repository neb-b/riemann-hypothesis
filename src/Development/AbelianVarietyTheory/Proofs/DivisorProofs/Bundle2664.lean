module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2583
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2612
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2613
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2601
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegenerationDataIsoOfPolarisedIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2618
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightUniqueRestrictClosedSubscheme
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

namespace GlobalTheory.MixHt.Uniq

variable {k : Type} [CommRing k]

theorem isometric_of_refines {X : Scheme.{0}} {p : X ⟶ Sp k} {N L : HermLB p} {π : N.B.ι → L.B.ι}
    (h : TwistTop.Refines N L π 0) : N.Isometric L :=
  HermLB.isometric_of_chart π h.le (fun x j j' hj hj' => h.g X (𝟙 X) x j j' hj hj')
    fun σ j y hy => ((h.φ σ j y hy).trans (add_zero _)).symm

theorem card_residueField {X Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] (z : Z) :
    Nat.card (X.residueField (i z)) = Nat.card (Z.residueField z) := by
  refine Nat.card_eq_of_bijective (i.residueFieldMap z) ⟨(i.residueFieldMap z).hom.injective, fun a => ?_⟩
  obtain ⟨b, rfl⟩ := Z.residue_surjective z a
  obtain ⟨c, rfl⟩ := i.stalkMap_surjective z b
  exact ⟨X.residue _ c, (ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i z) c :)⟩

end GlobalTheory.MixHt.Uniq


open GlobalTheory.MixHt.Uniq in
theorem GlobalTheory.MixHt.eq_of_isMix : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p →
    ∀ (i : Y ⟶ X) [IsClosedImmersion i] (hi : i ≫ p = q) (m m' : ℕ) T T', IsMix p m T → IsMix q m' T' →
    ∀ d : ℕ, d ≤ m → d ≤ m' → ∀ (L : Fin d → HermLB p) (L' : Fin d → HermLB q),
    (∀ a, ((L a).pull i hi).Isometric (L' a)) → ∀ y : Y, HasDim y d → T d L (i y) = T' d L' y := by
  intro k _ X Y p q hp i _ hi m m' T T' hT hT' d
  have hq : IsAmb q := hi ▸ hp.sub i
  have DX := _root_.GlobalTheory.MixHt.hasDim_basic k X p hp
  have DY := _root_.GlobalTheory.MixHt.hasDim_basic k Y q hq
  haveI : IsNoetherian Y := hq.isNoetherian
  induction d with
  | zero =>
    intro _ _ L L' _ y hy
    have hy' : HasDim (i y) 0 := (DX.2.2.2.2.1 Y i y 0).2 hy
    rw [hT.zero L (i y) hy', hT'.zero L' y hy, card_residueField i y]
  | succ e ih =>
    intro hm hm' L L' hL y hy
    have hW : IsAmb (cloι y ≫ q) := hq.sub (cloι y)
    have hgen : HasDim (genericPoint (clo y)) (e + 1) :=
      (DY.2.2.2.2.1 (clo y) (cloι y) (genericPoint (clo y)) (e + 1)).1 (by rw [cloι_genericPoint]; exact hy)
    have hdim : topologicalKrullDim (clo y) = ((e + 1 : ℕ) : WithBot ℕ∞) :=
      (DY.2.2.2.2.2 (clo y) (e + 1)).1 hgen
    obtain ⟨r, hr⟩ := exists_isRatSec ((L' 0).pull (cloι y) rfl).isLB
    have hij : (cloι y ≫ i) ≫ p = cloι y ≫ q := by rw [Category.assoc, hi]
    have hiso : ∀ (A : HermLB p) (A' : HermLB q), (A.pull i hi).Isometric A' →
        (A.pull (cloι y ≫ i) hij).Isometric (A'.pull (cloι y) rfl) := fun A A' h =>
      (isometric_of_refines (HermLB.refines_pull_pull A i hi (cloι y) rfl hij)).symm.trans (h.pull (cloι y) rfl)
    have h1 := hT'.recur (clo y) (cloι y ≫ q) (cloι y) rfl e hm' hdim (L' 0) (Fin.tail L')
      ((L' 0).pull (cloι y) rfl) (fun a => (L' a.succ).pull (cloι y) rfl) (HermLB.Isometric.refl _)
      (fun a => HermLB.Isometric.refl _) r hr
    have h2 := hT.recur (clo y) (cloι y ≫ q) (cloι y ≫ i) hij e hm hdim (L 0) (Fin.tail L)
      ((L' 0).pull (cloι y) rfl) (fun a => (L' a.succ).pull (cloι y) rfl) (hiso _ _ (hL 0))
      (fun a => hiso _ _ (hL a.succ)) r hr
    rw [Fin.cons_self_tail, cloι_genericPoint] at h1
    rw [Fin.cons_self_tail, Scheme.Hom.comp_apply, cloι_genericPoint] at h2
    rw [h1, h2]
    unfold recVal
    congr 1
    refine finsum_congr fun z => ?_
    by_cases hz : ((((L' 0).pull (cloι y) rfl)).div hr).mult z = 0
    · simp [hz]
    · have hz1 := CartierDiv.coheight_eq_one_of_mult_ne_zero hz
      have hzd : HasDim z e := ((_root_.GlobalTheory.MixHt.dimOne k (clo y) (cloι y ≫ q) hW e hdim).1 z).1 hz1
      have hjz : HasDim (cloι y z) e := (DY.2.2.2.2.1 (clo y) (cloι y) z e).2 hzd
      dsimp only
      rw [Scheme.Hom.comp_apply, ih (by omega) (by omega) (Fin.tail L) (Fin.tail L') (fun a => hL a.succ) _ hjz]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralPullbackGenericallyFinite
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.PushInt

theorem mixInt_pull : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ), Measurable f → (Intg (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) ↔ Intg L f) ∧ Mix.int (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) = π.residueDegree (genericPoint Y) * Mix.int L f := by
  intro F _ X Y _ _ p q σ D h1 h2 h3 π hπ hg hk L f hf
  have hm : Measurable (ptMap π hπ σ) := (PtsOver.continuous_map π hπ (spMap σ)).measurable
  have key := fun ε => _root_.GlobalTheory.Mix.map_part_pull_of_genFinite F X Y p q σ D h1 h2 h3 π hπ hg hk L ε
  have hc0 : ((π.residueDegree (genericPoint Y) : ENNReal)) ≠ 0 := by exact_mod_cast hk
  have hcT : ((π.residueDegree (genericPoint Y) : ENNReal)) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hI : ∀ ε, Integrable (fun y => f (ptMap π hπ σ y)) (part (fun i => (L i).pull π hπ) ε) ↔
      Integrable f (part L ε) := by
    intro ε
    have e := integrable_map_measure (μ := part (fun i => (L i).pull π hπ) ε) hf.aestronglyMeasurable hm.aemeasurable
    rw [key ε, integrable_smul_measure hc0 hcT] at e
    exact e.symm
  have hJ : ∀ ε, ∫ y, f (ptMap π hπ σ y) ∂(part (fun i => (L i).pull π hπ) ε) =
      (π.residueDegree (genericPoint Y) : ℝ) * ∫ y, f y ∂(part L ε) := by
    intro ε
    rw [← integral_map hm.aemeasurable hf.aestronglyMeasurable, key ε, integral_smul_measure]
    simp
  refine ⟨?_, ?_⟩
  · simp only [Intg, hI]
  · simp only [Mix.int, hJ]
    ring

end GlobalTheory.PushInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoComparisonNormalisedGenerator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem lamVal_cmp : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (ω : W →+* V) (D₁ D₂ : DegPre V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A), D₁.TauBimult → D₂.TauBimult → From T ω s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → IsMonHom b → b.left ≫ β₂ = β₁ → ∀ (χ₁ : D₁.X) (χ₂ : D₂.X), e₁ χ₁ = e₂ χ₂ → ∀ u : LB.Gen (CmpLB D₁ D₂ b χ₁ χ₂), Nrm u → ∀ (Z : Over (Sp V)) (x : Z ⟶ D₁.P.A) (z : Z.left) (J : (Z.left ⟶ (D₁.P.A.left ⨿ D₂.P.A.left : Scheme.{0})) → (JN D₁ D₂).ι) J₀, Good (JN D₁ D₂) z J → Good T.M.L z J₀ → lamVal w₂ (lift (toUnit Z ≫ D₂.c χ₂) (x ≫ b)).left z J₀ (rr J) = lamVal w₁ (lift (toUnit Z ≫ D₁.c χ₁) x).left z J₀ (rl J) * val u x.left z J := by
  intro o W _ _ _ T I _ ε n V _ _ ω D₁ D₂ s₁ e₁ β₁ ββ₁ w₁ s₂ e₂ β₂ ββ₂ w₂ b hB₁ hB₂ hF₁ hF₂ hb hbβ χ₁ χ₂ hχ u hu Z x z J J₀ hJ hJ₀
  haveI : Nonempty D₁.P.A.left := nonempty_av D₁.P
  haveI : Nonempty D₂.P.A.left := nonempty_av D₂.P
  haveI : Nonempty (D₁.P.A.left ⨿ D₂.P.A.left : Scheme.{0}) :=
    ⟨(coprod.inl : D₁.P.A.left ⟶ (D₁.P.A.left ⨿ D₂.P.A.left : Scheme.{0})) (Classical.arbitrary _)⟩
  haveI : Nonempty T.B.left := ⟨β₁ (Classical.arbitrary _)⟩
  have hJN : (JN D₁ D₂).IsLB := jn_isLB D₁ D₂
  have hN : (join (JN D₁ D₂) T.M.L).IsLB := join_isLB hJN T.M.isLB
  have pJ := isPart_inl (JN D₁ D₂) T.M.L
  have pT := isPart_inr (JN D₁ D₂) T.M.L
  have p₁ := pJ.trans (isPart_inl D₁.P.L D₂.P.L)
  have p₂ := pJ.trans (isPart_inr D₁.P.L D₂.P.L)
  obtain ⟨t₁, ht₁, ht₁v⟩ := exists_gen_of_iso pT p₁ w₁ hF₁.2.2.1
  obtain ⟨t₂, ht₂, ht₂v⟩ := exists_gen_of_iso pT p₂ w₂ hF₂.2.2.1
  let m₁ : D₁.P.A.left ⟶ (G2 D₁.P.A).left := (lift (toUnit _ ≫ D₁.c χ₁) (𝟙 _)).left
  let m₂ : D₁.P.A.left ⟶ (G2 D₂.P.A).left := (lift (toUnit _ ≫ D₂.c χ₂) b).left
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨J', hJ', eJl, eJr⟩ := exists_good_join hJN T.M.isLB hJ hJ₀
  have key := gen_unique' hN (u := LB.pullGen _ _ _ t₂ m₂)
    (u' := LB.mulGen _ _ _ _ _ (LB.pullGen _ _ _ t₁ m₁) (pJ.gen u)) ?fe D₁.P.A.hom (eSec D₁.P.A) (Over.w η[D₁.P.A])
    (hG _ _ D₁.P.isAb).2 (DVR.pullGen_isGen _ _ _ _ ht₂ m₂)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht₁ m₁) (pJ.gen_isGen hu.1)) ?ev Z.left x.left z J' hJ'
  · rw [val_pull hJ', ht₂v _ _ z J' hJ', val_mul hJ', val_pull hJ', ht₁v _ _ z J' hJ', pJ.val_gen _ _ z hJ'] at key
    have e₁ : x.left ≫ m₁ = (lift (toUnit Z ≫ D₁.c χ₁) x).left := by
      rw [← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit Z)]
    have e₂ : x.left ≫ m₂ = (lift (toUnit Z ≫ D₂.c χ₂) (x ≫ b)).left := by
      rw [← Over.comp_left, comp_lift, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit Z)]
    have r₁ : rs (M := D₁.P.L) (coprod.inl ≫ coprod.inl) (Prod.fst ∘ Prod.fst) J' = rl J := by
      rw [← eJl]; funext ψ
      show Prod.fst (Prod.fst (J' (ψ ≫ coprod.inl ≫ coprod.inl))) = Prod.fst (Prod.fst (J' ((ψ ≫ coprod.inl) ≫ coprod.inl)))
      rw [Category.assoc]
    have r₂ : rs (M := D₂.P.L) (coprod.inr ≫ coprod.inl) (Prod.snd ∘ Prod.fst) J' = rr J := by
      rw [← eJl]; funext ψ
      show Prod.snd (Prod.fst (J' (ψ ≫ coprod.inr ≫ coprod.inl))) = Prod.snd (Prod.fst (J' ((ψ ≫ coprod.inr) ≫ coprod.inl)))
      rw [Category.assoc]
    rw [e₁, e₂] at key
    convert key using 3 <;> first | exact r₁.symm | exact r₂.symm | exact eJl.symm | exact eJr.symm | exact congrArg₂ (isoVal w₂ _ z) eJr.symm r₂.symm | exact congrArg₂ (isoVal w₁ _ z) eJr.symm r₁.symm
  case fe =>
    have g2 : ∀ {a c : D₁.P.A.left ⟶ (G2 T.B).left}, a ≫ (fst T.B T.B).left = c ≫ (fst T.B T.B).left →
        a ≫ (snd T.B T.B).left = c ≫ (snd T.B T.B).left → a = c := fun h1 h2 => pullback.hom_ext h1 h2
    have hT0 : (lift (toUnit _ ≫ D₁.c χ₁) (𝟙 _)).left ≫ ββ₁ = (lift (toUnit _ ≫ D₂.c χ₂) b).left ≫ ββ₂ := by
      refine g2 ?_ ?_
      · rw [Category.assoc, Category.assoc, hF₁.2.1.1, hF₂.2.1.1, ← Category.assoc, ← Category.assoc,
          ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, Over.comp_left, Over.comp_left, Category.assoc,
          Category.assoc, hF₁.2.2.2.1, hF₂.2.2.2.1, hχ]
      · rw [Category.assoc, Category.assoc, hF₁.2.1.2, hF₂.2.1.2, ← Category.assoc, ← Category.assoc,
          ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd, Over.id_left, Category.id_comp, hbβ]
    have hT : m₁ ≫ ββ₁ = m₂ ≫ ββ₂ := hT0
    have eT : ∀ (X : Scheme.{0}) (g : (G2 T.B).left ⟶ X), m₁ ≫ ββ₁ ≫ g = m₂ ≫ ββ₂ ≫ g := fun _ g => by
      rw [← Category.assoc, hT, Category.assoc]
    intro U _ h
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, eT]
    letI := D₁.P.isAb.comm
    letI := D₂.P.isAb.comm
    have hc₁ : (toUnit D₁.P.A ≫ D₁.c χ₁) * 𝟙 D₁.P.A = 𝟙 D₁.P.A * (toUnit D₁.P.A ≫ D₁.c χ₁) := mul_comm _ _
    have hc₂ : (toUnit D₁.P.A ≫ D₂.c χ₂) * b = b * (toUnit D₁.P.A ≫ D₂.c χ₂) := mul_comm _ _
    have A1 : ∏ a₂ : ULift.{0} (Finset (Fin 2)),
        h (m₁ ≫ (psum D₁.P.A (x2 D₁.P.A) a₂.down).left ≫ coprod.inl ≫ coprod.inl) ^ (-(-1 : ℤ) ^ (2 - a₂.down.card)) =
        (h ((𝟙 D₁.P.A * (toUnit _ ≫ D₁.c χ₁)).left ≫ coprod.inl ≫ coprod.inl) *
          (h ((toUnit _ ≫ D₁.c χ₁).left ≫ coprod.inl ≫ coprod.inl))⁻¹ *
          (h ((𝟙 D₁.P.A : D₁.P.A ⟶ D₁.P.A).left ≫ coprod.inl ≫ coprod.inl))⁻¹ *
          h ((1 : D₁.P.A ⟶ D₁.P.A).left ≫ coprod.inl ≫ coprod.inl))⁻¹ := by
      rw [← hc₁, ← GlobalTheory.PrimCocycle.prod_lam (toUnit _ ≫ D₁.c χ₁) (𝟙 _) (fun g => h (g ≫ coprod.inl ≫ coprod.inl)),
        ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [zpow_neg, ← Category.assoc]
    have A2 : ∏ a₂ : ULift.{0} (Finset (Fin 2)),
        h (m₂ ≫ (psum D₂.P.A (x2 D₂.P.A) a₂.down).left ≫ coprod.inr ≫ coprod.inl) ^ (-(-1 : ℤ) ^ (2 - a₂.down.card)) =
        (h ((b * (toUnit _ ≫ D₂.c χ₂)).left ≫ coprod.inr ≫ coprod.inl) *
          (h ((toUnit _ ≫ D₂.c χ₂).left ≫ coprod.inr ≫ coprod.inl))⁻¹ *
          (h (b.left ≫ coprod.inr ≫ coprod.inl))⁻¹ *
          h ((1 : D₁.P.A ⟶ D₂.P.A).left ≫ coprod.inr ≫ coprod.inl))⁻¹ := by
      rw [← hc₂, ← GlobalTheory.PrimCocycle.prod_lam (toUnit _ ≫ D₂.c χ₂) b (fun g => h (g ≫ coprod.inr ≫ coprod.inl)),
        ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [zpow_neg, ← Category.assoc]
    rw [A1, A2, Fin.prod_univ_four, Fin.prod_univ_four]
    have pm : ∀ {X Y : Over (Sp V)} [GrpObj Y] (a c : X ⟶ Y), padd Y a c = a * c := fun _ _ => rfl
    simp only [DegPre.Oφ, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, pm, ← Hom.one_def, Category.assoc]
    simp only [zpow_one, zpow_neg]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  case ev =>
    intro y I hI
    haveI := hb
    rw [val_pull hI, ht₂v _ _ y I hI, val_mul hI, val_pull hI, ht₁v _ _ y I hI, pJ.val_gen _ _ y hI]
    have o₁ : (1 : 𝟙_ (Over (Sp V)) ⟶ D₁.P.A) = η[D₁.P.A] := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have o₂ : (1 : 𝟙_ (Over (Sp V)) ⟶ D₂.P.A) = η[D₂.P.A] := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have f₁ : eSec D₁.P.A ≫ m₁ = (lift (toUnit (𝟙_ (Over (Sp V))) ≫ D₁.c χ₁) (1 : 𝟙_ _ ⟶ D₁.P.A)).left := by
      rw [eSec, ← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc,
        toUnit_unique (η[D₁.P.A] ≫ toUnit _) (toUnit _), o₁]
    have f₂ : eSec D₁.P.A ≫ m₂ = (lift (toUnit (𝟙_ (Over (Sp V))) ≫ D₂.c χ₂) (1 : 𝟙_ _ ⟶ D₂.P.A)).left := by
      have hbη : η[D₁.P.A] ≫ b = η[D₂.P.A] := IsMonHom.one_hom b
      rw [eSec, ← Over.comp_left, comp_lift, hbη, ← Category.assoc,
        toUnit_unique (η[D₁.P.A] ≫ toUnit _) (toUnit _), o₂]
    rw [f₁, f₂]
    have a₂ := (_root_.GlobalTheory.TInj.lamVal_axes_one T ε n V D₂ ω s₂ e₂ β₂ ββ₂ w₂ hB₂ hF₂ (𝟙_ _) (toUnit _ ≫ D₂.c χ₂) y _ _ (pT.good hI)
      (p₂.good hI)).2
    have a₁ := (_root_.GlobalTheory.TInj.lamVal_axes_one T ε n V D₁ ω s₁ e₁ β₁ ββ₁ w₁ hB₁ hF₁ (𝟙_ _) (toUnit _ ≫ D₁.c χ₁) y _ _ (pT.good hI)
      (p₁.good hI)).2
    have c := hu.2 (𝟙_ (Over (Sp V))).left (𝟙 _) y _ (pJ.good hI)
    rw [Category.id_comp] at c
    refine a₂.trans (Eq.symm ?_)
    exact (congrArg₂ (· * ·) a₁ c).trans (_root_.mul_one 1)

end GlobalTheory.TInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorPairingFactorInclusionPeriods
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem pairing_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W) (i₀ : Fin r), letI := T.mod (symUnitOf W h); ∃ w : LB.Iso (abelian₂ D.toPre.P.A D.toPre.P.L) ((abelian₂ D'.toPre.P.A D'.toPre.P.L).pull (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left), w.IsGen ∧ ∀ a b z J J', Good D'.toPre.P.L z J → Good D.toPre.P.L z J' → val (D.toPre.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b)).left z J J' * val (D'.toPre.tau (T.xi i₀ a) (TensO.binv (symUnitOf W h) • T.xi i₀ b)) (𝟙 _) z J := by
  intro R _ _ _ hA D D' r W h hP T i₀
  exact GlobalTheory.T.tensor_data_factor_pairing_pullback R hA D D' W h hP T (_root_.GlobalTheory.Mum.tens_lam_core R _ D D' W T) i₀

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyEqOfSeparableCommutantComm
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.RegCommutant

theorem exists_not_commute_of_two_le_finrank {K E : Type} [Field K] [AddCommGroup E]
    [Module K E] [FiniteDimensional K E] (h : 2 ≤ Module.finrank K E) :
    ∃ S₁ S₂ : Module.End K E, S₁ * S₂ ≠ S₂ * S₁ := by
  let b := Module.finBasis K E
  let e := LinearMap.toMatrixAlgEquiv b
  let i0 : Fin (Module.finrank K E) := ⟨0, by omega⟩
  let i1 : Fin (Module.finrank K E) := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  refine ⟨e.symm (Matrix.single i0 i1 1), e.symm (Matrix.single i1 i0 1), ?_⟩
  intro hc
  have h2 := congrArg e hc
  simp only [map_mul, AlgEquiv.apply_symm_apply] at h2
  have h3 := congrFun (congrFun h2 i0) i0
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same] at h3
  simp [Matrix.single_apply, hne.symm] at h3

theorem finrank_le_natDegree_minpoly (K V : Type) [Field K] [IsAlgClosed K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (T : Module.End K V) (hs : (minpoly K T).Separable)
    (hc : ∀ a b : Module.End K V, Commute a T → Commute b T → Commute a b) :
    Module.finrank K V ≤ (minpoly K T).natDegree := by
  classical
  set f := minpoly K T with hf
  have hmon : f.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral T)
  obtain ⟨hsum, -⟩ := GlobalTheory.EigSum.finrank_eigenspaces_of_separable_minpoly K V T f hmon hs
    (minpoly.aeval K T) (fun g hg => minpoly.dvd K T hg)
  have hcard : f.roots.toFinset.card = f.natDegree := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hs)]
    exact ((IsAlgClosed.splits f).natDegree_eq_card_roots).symm
  by_contra hlt
  push_neg at hlt
  obtain ⟨μ, hμ, h2⟩ : ∃ μ ∈ f.roots.toFinset, 2 ≤ Module.finrank K (T.eigenspace μ) := by
    by_contra hno
    push_neg at hno
    have : ∑ z ∈ f.roots.toFinset, Module.finrank K (T.eigenspace z) ≤
        ∑ z ∈ f.roots.toFinset, 1 :=
      Finset.sum_le_sum fun z hz => Nat.lt_succ_iff.mp (hno z hz)
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at this
    omega
  have hroot : f.IsRoot μ := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hmon.ne_zero] at hμ; exact hμ
  set q := f /ₘ (Polynomial.X - Polynomial.C μ) with hq
  have hfq : (Polynomial.X - Polynomial.C μ) * q = f :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hqμ : q.eval μ ≠ 0 := by
    intro h0
    have hq' : (Polynomial.X - Polynomial.C μ) * (q /ₘ (Polynomial.X - Polynomial.C μ)) = q :=
      Polynomial.mul_divByMonic_eq_iff_isRoot.mpr h0
    obtain ⟨q2, hq2⟩ : ∃ q2, (Polynomial.X - Polynomial.C μ) * q2 = q := ⟨_, hq'⟩
    have hu : IsUnit (Polynomial.X - Polynomial.C μ) :=
      hs.squarefree _ ⟨q2, by rw [← hfq, ← hq2]; ring⟩
    exact Polynomial.not_isUnit_X_sub_C μ hu
  set c := q.eval μ with hc_def
  set Q := Polynomial.aeval T q with hQ
  set E := T.eigenspace μ with hE
  have hTQ : ∀ v, T (Q v) = μ • Q v := by
    intro v
    have h0 : Polynomial.aeval T ((Polynomial.X - Polynomial.C μ) * q) = 0 := by
      rw [hfq]; exact minpoly.aeval K T
    have h1 := congrArg (fun g : Module.End K V => g v) h0
    simp only [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Module.End.mul_apply,
      LinearMap.sub_apply, Module.algebraMap_end_apply, LinearMap.zero_apply] at h1
    exact sub_eq_zero.mp h1
  have hQT : ∀ v, Q (T v) = T (Q v) := by
    intro v
    have h := congrArg (Polynomial.aeval T) (mul_comm q Polynomial.X)
    simp only [map_mul, Polynomial.aeval_X] at h
    exact congrArg (fun g : Module.End K V => g v) h
  have hQE : ∀ v, Q v ∈ E := by
    intro v
    rw [hE, Module.End.mem_eigenspace_iff]
    exact hTQ v
  have hQid : ∀ u ∈ E, Q u = c • u := by
    intro u hu
    by_cases hu0 : u = 0
    · simp [hu0]
    · exact Module.End.aeval_apply_of_hasEigenvector ⟨hu, hu0⟩
  let π : V →ₗ[K] E := Q.codRestrict E hQE
  let ι : E →ₗ[K] V := E.subtype
  have hπι : ∀ x : E, π (ι x) = c • x := by
    intro x; apply Subtype.ext; simp [π, ι, hQid x.1 x.2]
  have hπT : ∀ v, π (T v) = μ • π v := by
    intro v; apply Subtype.ext; simp [π, hQT v, hTQ v]
  have hcomm : ∀ S : Module.End K E, Commute (ι ∘ₗ S ∘ₗ π) T := by
    intro S
    apply LinearMap.ext
    intro v
    have hm : T (S (π v) : V) = μ • (S (π v) : V) := Module.End.mem_eigenspace_iff.mp (S (π v)).2
    simp only [Module.End.mul_apply, LinearMap.comp_apply, hπT v, map_smul]
    simp [ι, hm]
  obtain ⟨S₁, S₂, hS⟩ := exists_not_commute_of_two_le_finrank h2
  have hab := hc _ _ (hcomm S₁) (hcomm S₂)
  apply hS
  apply LinearMap.ext
  intro w
  have h1 := congrArg (fun g : Module.End K V => g (ι (c⁻¹ • c⁻¹ • w))) hab.eq
  simp only [Module.End.mul_apply, LinearMap.comp_apply, map_smul, hπι, smul_smul] at h1
  apply Subtype.ext
  simpa [ι, mul_inv_cancel₀ hqμ, inv_mul_cancel₀ hqμ, mul_assoc, mul_left_comm] using h1

theorem natDegree_minpoly_eq_of_commutant_comm : ∀ (K : Type) [Field K] [IsAlgClosed K] (k : ℕ)
    (N : Matrix (Fin k) (Fin k) K), (minpoly K N).Separable →
    (∀ A B : Matrix (Fin k) (Fin k) K, Commute A N → Commute B N → Commute A B) →
    (minpoly K N).natDegree = k := by
  intro K _ _ k N hs hc
  have hmin : minpoly K (Matrix.toLin' N) = minpoly K N := Matrix.minpoly_toLin' N
  apply le_antisymm
  · calc (minpoly K N).natDegree ≤ N.charpoly.natDegree :=
          Polynomial.natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly N) (Matrix.charpoly_monic N).ne_zero
      _ = k := by rw [Matrix.charpoly_natDegree_eq_dim]; simp
  · have h := finrank_le_natDegree_minpoly K (Fin k → K) (Matrix.toLin' N) (hmin ▸ hs) ?_
    · simpa [hmin] using h
    · intro a b ha hb
      let e : Matrix (Fin k) (Fin k) K ≃ₐ[K] Module.End K (Fin k → K) := Matrix.toLinAlgEquiv'
      have hN : e.symm (Matrix.toLin' N) = N := by
        rw [AlgEquiv.symm_apply_eq]; rfl
      have hA := ha.map e.symm
      have hB := hb.map e.symm
      rw [hN] at hA hB
      simpa only [AlgEquiv.apply_symm_apply] using (hc _ _ hA hB).map e

end GlobalTheory.RegCommutant
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareClassAdditiveInDualVariableStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareClass_additive_in_dual_variable : ∀ (K : Type) [Field K] (A A' : AbVar K) (P : LB (A.X ⊗ A'.X).left) (hP : AbDual.IsDual A.X A'.X P) (Y : Over (Sp K)) (a : Y ⟶ A.X) (b b' : Y ⟶ A'.X), AbDual.evc hP.isLB a (b * b') = AbDual.evc hP.isLB a b + AbDual.evc hP.isLB a b' := by
  first | (exact @GlobalTheory.AbDual.poincare_evc_mul_right) | (exact GlobalTheory.AbDual.poincare_evc_mul_right) | (intros; apply GlobalTheory.AbDual.poincare_evc_mul_right  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegenerationDataIsoOfPolarisedIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_degeneration_data_iso_of_polarised_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X] (o : D.toPre.OAct O) (o' : D'.toPre.OAct O) (w : O), TraceFormTwistIso D.toPre o w → TraceFormTwistIso D'.toPre o' w → ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (xe : D'.toPre.X ≃+ D.toPre.X), IsMonHom Φ.hom → ((∀ a, o'.onB.act a ≫ Φ.hom = Φ.hom ≫ o.onB.act a) ∧ (∀ (a : O) x, xe (a • x) = a • xe x) ∧ (∀ x, D'.toPre.c x ≫ Φ.hom = D.toPre.c (xe x))) → (∃ wΛ : (letI := D.toPre.P.isAb.comm; letI := D'.toPre.P.isAb.comm; LB.Iso (abelian₂ D'.toPre.P.A D'.toPre.P.L) ((abelian₂ D.toPre.P.A D.toPre.P.L).pull (lift (fst D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom) (snd D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom) : G2 D'.toPre.P.A ⟶ G2 D.toPre.P.A).left)), wΛ.IsGen ∧ ∀ a b z J J', Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal wΛ (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z J J' * val (D.toPre.tau (xe a) (xe b)) (𝟙 _) z J) → ∃ hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre, hD.xe = xe ∧ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = Φ.hom.left := by
  first | exact @GlobalTheory.PrimPull.isPullDeg_of_primitive | exact GlobalTheory.PrimPull.isPullDeg_of_primitive | (intros; apply GlobalTheory.PrimPull.isPullDeg_of_primitive <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiTwistedEqPsiMulCharacterOfPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_twisted_eq_psi_mul_character_of_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₂ : DegData R (maximalIdeal R)) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (β : D₂.toPre.P.A ≅ D.toPre.P.A), IsMonHom β.hom → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → (∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK 0 ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK 0) (-1) (D₂.toPre.psi 0) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi 0) (LB.pullGen D.toPre.P.L _ _ (g.s 0) (toUnit (TK R)).left))) → ∀ (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB 1 α) (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1])), ν.IsGen → GlobalTheory.PsiCompare.LevelOneEq D.toPre f → GlobalTheory.PsiCompare.LevelOneEq D₂.toPre f₂ → (¬ ∀ mu j, (f₂ mu).f j = 0) → (∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.toPre.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.toPre.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.toPre.famφB χ κ) z (fun i => J ((r ≫ D₂.toPre.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ D₂.toPre.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J') → ∀ χ : D₂.toPre.X, ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK χ ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK χ) (-1) (D₂.toPre.psi χ) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi (xe χ)) (LB.pullGen D.toPre.P.L _ _ (g.s (xe χ)) (toUnit (TK R)).left)) := by
  first | exact @GlobalTheory.MumCmp.psi_maps_twist | exact GlobalTheory.MumCmp.psi_maps_twist | (intros; apply GlobalTheory.MumCmp.psi_maps_twist <;> assumption)
end

