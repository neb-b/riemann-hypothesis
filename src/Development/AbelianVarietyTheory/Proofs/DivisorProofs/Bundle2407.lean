module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2314
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ActionProductEqOne
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValMemOfCorrPull
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem valF_spMap_comp {F F' : Type} [Field F] [Field F'] (σ : F →+* F') {X : Scheme.{0}} (x : Sp F ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : valF (spMap σ ≫ x) U f = σ (valF x U f) := by
  classical
  have h' : ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U := fun y _ => h (show (spMap σ).base y ∈ (⊤ : (Sp F).Opens) from trivial)
  rw [valF, valF, dite_eq_left h, dite_eq_left h', ← Scheme.Hom.appLE_comp_appLE (spMap σ) x U ⊤ ⊤ h le_top]
  exact congrArg (fun q => q.hom ((Scheme.Hom.appLE x U ⊤ h).hom f)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ))

theorem toStk_valF_gs {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) (h : x z ∈ U)
    (a : Γ(X, U)) : toStk z (valF x U a) = gs x z U a := by
  classical
  rw [valF, dite_eq_left ((top_le_iff_mem x U z).2 h), gs_eq x z U h]
  show ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE ((top_le_iff_mem x U z).2 h)) z trivial _

variable {K : Type} [Field K] (k₀ : Subfield K) {X Y Y' : Scheme.{0}}

theorem valF_mem_of_defOver {x : Sp K ⟶ X} (hx : DefOver k₀ x) (U : X.Opens) (z : Sp K) (h : x z ∈ U)
    (a : Γ(X, U)) : valF x U a ∈ k₀ := by
  obtain ⟨P₀, rfl⟩ := hx
  have h₀ : ⊤ ≤ P₀ ⁻¹ᵁ U := (top_le_iff_mem P₀ U ((spMap k₀.subtype).base z)).2 h
  rw [valF_spMap_comp k₀.subtype P₀ U h₀ a]
  exact (valF P₀ U a).2

theorem gs_mem_of_defOver {x : Sp K ⟶ X} (hx : DefOver k₀ x) (U : X.Opens) (z : Sp K) (h : x z ∈ U)
    (a : Γ(X, U)) : ∃ c ∈ k₀, gs x z U a = toStk z c :=
  ⟨valF x U a, valF_mem_of_defOver k₀ hx U z h a, (toStk_valF_gs x U z h a).symm⟩

variable {L : LB X} {Ix : Type} [Fintype Ix] {φ : Ix → (Y ⟶ X)} {ε : Ix → ℤ}

theorem val_mem_of_defOver (t : LB.Gen (LB.LinComb L φ ε)) {r : Sp K ⟶ Y} (hr : DefOver k₀ r) (z : Sp K)
    {J : (Sp K ⟶ X) → L.ι} (hJ : Good L z J) : ∃ c ∈ k₀, (val t r z J).val = toStk z c := by
  have hm := hJ.mem φ r
  obtain ⟨c, hc, e⟩ := gs_mem_of_defOver k₀ hr _ z hm (t.s fun k => J (r ≫ φ k)).val
  exact ⟨c, hc, (gs_unit r z _ hm _).symm.trans e⟩

end GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory
variable {K : Type} [Field K] (k₀ : Subfield K)

theorem spMap_subtype_cancel {R : Type} [CommRing R] {a b : Sp k₀ ⟶ Sp R}
    (h : spMap k₀.subtype ≫ a = spMap k₀.subtype ≫ b) : a = b := by
  rw [← Spec.map_preimage a, ← Spec.map_preimage b] at h ⊢
  congr 1
  simp only [spMap, ← Spec.map_comp] at h
  have e := Spec.map_injective h
  ext y
  exact congrArg (fun q => q.hom y) e
end GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep
variable {K : Type} [Field K] (k₀ : Subfield K)

theorem defOver_comp {X Y : Scheme.{0}} {P : Sp K ⟶ X} (hP : DefOver k₀ P) (g : X ⟶ Y) : DefOver k₀ (P ≫ g) := by
  obtain ⟨P₀, rfl⟩ := hP
  exact ⟨P₀ ≫ g, (Category.assoc _ _ _).symm⟩

theorem defOver_spMap {R : Type} [CommRing R] (f : R →+* K) (hf : ∀ a, f a ∈ k₀) : DefOver k₀ (spMap f) :=
  ⟨spMap (f.codRestrict k₀ hf), by simp only [spMap, ← Spec.map_comp]; rfl⟩

theorem defOver_pullback {R : Type} [CommRing R] {A B : Scheme.{0}} {f : A ⟶ Sp R} {g : B ⟶ Sp R}
    {x : Sp K ⟶ pullback f g} (h₁ : DefOver k₀ (x ≫ pullback.fst f g)) (h₂ : DefOver k₀ (x ≫ pullback.snd f g)) :
    DefOver k₀ x := by
  obtain ⟨Q₁, hQ₁⟩ := h₁
  obtain ⟨Q₂, hQ₂⟩ := h₂
  have hw : Q₁ ≫ f = Q₂ ≫ g := spMap_subtype_cancel k₀ (by
    rw [← Category.assoc, hQ₁, ← Category.assoc, hQ₂, Category.assoc, Category.assoc, pullback.condition])
  refine ⟨pullback.lift Q₁ Q₂ hw, pullback.hom_ext ?_ ?_⟩
  · rw [Category.assoc, pullback.lift_fst, hQ₁]
  · rw [Category.assoc, pullback.lift_snd, hQ₂]

variable {X Y : Scheme.{0}} {L : LB X} {Ix : Type} [Fintype Ix] {φ : Ix → (Y ⟶ X)} {ε : Ix → ℤ}

theorem val_spMap_mem {R : Type} [CommRing R] {L : LB X} {φ : Ix → (Sp R ⟶ X)} (t : LB.Gen (LB.LinComb L φ ε))
    (f : R →+* K) (hf : ∀ a, f a ∈ k₀) (z : Sp K) {J : (Sp K ⟶ X) → L.ι} (hJ : Good L z J) :
    ∃ c ∈ k₀, (val t (spMap f) z J).val = toStk z c :=
  val_mem_of_defOver k₀ t (defOver_spMap k₀ f hf) z hJ

end GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValRImageModelSectionSemilinear
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.ImageModel

theorem valR_algX_cxPts {k : Type} [CommRing k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) (τ : k →+* ℂ)
    (U : Y.Opens) (y : GlobalTheory.CxPts p τ) (h : ⊤ ≤ y.1 ⁻¹ᵁ U) (a : k) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR y.1 U (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U a) = τ a := by
  have h1 := GlobalTheory.Points.valR_appLE y.1 p (U := ⊤) (V := U) (by simp) h
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)
  have h2 : y.1 ≫ p = Spec.map (CommRingCat.ofHom τ) := y.2
  rw [h2] at h1
  exact h1.trans (GlobalTheory.Points.valR_specMap (CommRingCat.ofHom τ) a)

theorem valR_section_sum : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → ∀ (τ : 𝓞 K →+* ℂ) (i : L.B.ι) (y : GlobalTheory.CxPts p τ), y ∈ GlobalTheory.CxPts.ptsIn p τ (L.B.U i) → ∀ (m : ℕ) (β : Fin m → 𝓞 K) (u : Fin m → W) (x : W), (x : V) = ∑ k, β k • (u k : V) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR y.1 (L.B.U i) ((s x).f i) = ∑ k, τ (β k) * ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR y.1 (L.B.U i) ((s (u k)).f i) := by
  intro K V Ω _ _ _ _ _ _ _ _ Nm W ev D X _ p L ψ s hM hev τ i y hy m β u x hx
  have h : ⊤ ≤ y.1 ⁻¹ᵁ L.B.U i := hy
  set_option synthInstance.maxHeartbeats 100000 in
    rw [_root_.GlobalTheory.ImageModel.sec_linear K V Ω Nm W ev D X p L ψ s hM hev m β u x hx i, GlobalTheory.Points.valR_eq _ _ h, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← GlobalTheory.Points.valR_eq _ _ h, GlobalTheory.Points.valR_mul _ _ h, valR_algX_cxPts p τ _ y h]

end GlobalTheory.ImageModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenBijectiveSchwartz
section
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

theorem GlobalTheory.ModelTr.exists_isWeil_trans_of_bijOn : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) → ∃ om₁ : Rep σ X W, M₁.IsWeil B.ψ χX χW om₁ ∧ ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), e (om x Φ) = om₁ x (e Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij
  obtain ⟨T, hTe, hTs⟩ := GlobalTheory.ModelTr.extEquiv (schA F (Fin n × Fin d)) e hbij
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hgood : IsGoodInt (adeleClass F) B.ψ M.co M₁.co T := by
    refine ⟨hTs, fun w Φ hΦ => ?_, fun l => ?_, fun μ hμ => ?_⟩
    · have hm : M.co.rho B.ψ w Φ ∈ schA F (Fin n × Fin d) :=
        _root_.GlobalTheory.SchrKeepsSchA.schr_mem_schA F B.ψ hpair.base.std _ (M.co.e w) Φ hΦ
      have := hev.Heisenberg₂ w Φ hΦ
      rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at this
      rw [hTe _ hm, hTe _ hΦ, this]
    · refine (_root_.GlobalTheory.ModelAdmUnconditional.model_admissible_iff_evaluation F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij l).trans (GlobalTheory.ModelTr.adm_congr ?_)
      intro Φ hΦ
      simp [hTe Φ hΦ]
    · obtain ⟨c, hc⟩ := _root_.GlobalTheory.EvalUnitUnconditional.exists_const F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij μ hμ
      exact ⟨c, fun Φ hΦ => by rw [hTe Φ hΦ]; exact hc Φ hΦ⟩
  refine ⟨trRep T om, isUWeilPair_trRep hgood
    (_root_.GlobalTheory.DblGoodInt.main F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T hTe)
    (GlobalTheory.T.weil_eigen_bijective_regular F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T hTe) hpair.weil, fun x Φ hΦ => ?_⟩
  have hpres : om x Φ ∈ schA F (Fin n × Fin d) := hpair.weil.isUSplitting.pres x Φ hΦ
  rw [trRep_apply, ← hTe Φ hΦ, LinearEquiv.symm_apply_apply, hTe _ hpres]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingE8PowerDependsOnForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.E8Fibration.PairVal

open GlobalTheory.PairingOfLam GlobalTheory.DescentPairing GlobalTheory.AdjointOfPairing

variable {S : Scheme.{0}}

theorem weilIs_of_lbIso {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {N : RigLB A}
    (cN : CubicalStr A N) (f g f' g' : B ⟶ A) [IsMonHom f] [IsMonHom g] [IsMonHom f'] [IsMonHom g']
    (H : LBIso (cubeLB A ![fst B B ≫ f, snd B B ≫ g] N.L) (cubeLB A ![fst B B ≫ f', snd B B ≫ g'] N.L))
    {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (n : ℕ) (y z : T ⟶ B) (hy : y ^ n = 1) (hz : z ^ n = 1)
    (e : Γ(T.left, ⊤)ˣ) (he : WeilIs A N.L n (y ≫ f') (z ≫ g') e) : WeilIs A N.L n (y ≫ f) (z ≫ g) e := by
  have hyf : (y ≫ f) ^ n = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have hyc : (y ≫ f') ^ n = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have hzg : (z ≫ g) ^ n = 1 := by rw [← MonObj.pow_comp, hz, MonObj.one_comp]
  obtain ⟨e', hr⟩ := WeilCube.exists_isRatio cN n _ _ hyf hzg
  have he' := (WeilCube.weilIs_iff cN hG hA hyf hzg hr e').2 rfl
  refine (WeilCube.weilIs_iff cN hG hA hyf hzg hr e).2 (unit_ext fun p _ => ?_)
  obtain ⟨t, ht, v⟩ := exists_gen_lam hG hA cN p₀ hT f' g' n y hyc
  obtain ⟨t', ht', v'⟩ := exists_gen_lam hG hA cN p₀ hT f g n y hyf
  choose J hJ using fun χ : T.left ⟶ A.left => exists_chart N.isLB (χ p)
  have r := val_ratio N.isLB N.isLB H _ t ht t' ht' (fst T B).left (WeilCube.surj_fst hG hB T)
    (lift (𝟙 T) z).left (lift (𝟙 T) (1 : T ⟶ B)).left
    (by rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift, lift_fst_assoc, lift_fst_assoc,
      MonObj.comp_pow, MonObj.comp_pow, lift_snd, lift_snd, hz, one_pow])
    (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]) p hJ hJ
  rw [v z e hz he p J hJ, v' z e' hz he' p J hJ] at r
  apply Additive.ofMul.injective
  have r' := congrArg Additive.ofMul r
  simp only [ofMul_mul, ofMul_inv] at r'
  linear_combination (norm := abel) r'

theorem exists_hom {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj B] {pr : Fin 8 → (A ⟶ B)} (hP : IsProd pr)
    (s : Fin 8 → ℤ) : ∃ f : B ⟶ A, IsMonHom f ∧ ∀ (T : Over S) (x : T ⟶ B) (a : Fin 8), (x ≫ f) ≫ pr a = x ^ s a := by
  obtain ⟨f, hf, -⟩ := hP.2 B (fun a => 𝟙 B ^ s a)
  have h : ∀ (T : Over S) (x : T ⟶ B) (a : Fin 8), (x ≫ f) ≫ pr a = x ^ s a := fun T x a => by
    rw [Category.assoc, hf a]
    exact (map_zpow (PrimPic.preH (G := B) x) _ _).trans (congrArg (· ^ s a) (Category.comp_id x))
  refine ⟨f, isMonHom_of_mul f fun T x y => ?_, h⟩
  refine (hP.2 T fun a => ((x * y) ≫ f) ≫ pr a).unique (fun a => rfl) fun a => ?_
  haveI := hP.1 a
  rw [MonObj.mul_comp, h, h, h, mul_zpow]

theorem bil_zpow {B : Over S} [GrpObj B] [IsCommMonObj B] (M : RigLB B) (cub : CubicalStr B M) {T : Over S}
    (m : Matrix (Fin 8) (Fin 8) ℤ) (s t : Fin 8 → ℤ) (x y : T ⟶ B) :
    PrimPic.bil (GlobalTheory.CechPic.cls M.L M.isLB) m (fun a => x ^ s a) (fun b => y ^ t b) =
      dotProduct s (m.mulVec t) • PrimPic.lam (GlobalTheory.CechPic.cls M.L M.isLB) x y := by
  have hl : ∀ (k : ℤ) (u v : T ⟶ B), PrimPic.lam (GlobalTheory.CechPic.cls M.L M.isLB) (u ^ k) v =
      k • PrimPic.lam (GlobalTheory.CechPic.cls M.L M.isLB) u v := fun k u v =>
    map_zsmul (PrimPic.lamHom M cub v) k (Additive.ofMul u)
  have hr : ∀ (k : ℤ) (u v : T ⟶ B), PrimPic.lam (GlobalTheory.CechPic.cls M.L M.isLB) u (v ^ k) =
      k • PrimPic.lam (GlobalTheory.CechPic.cls M.L M.isLB) u v := fun k u v => by
    rw [PrimPic.lam_comm, hl, PrimPic.lam_comm]
  simp only [PrimPic.bil, hl, hr, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_smul, smul_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  ring

theorem weilIs_of_form_eq : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ) (K : Type) [Field K] [IsAlgClosed K] (P' : PolAV (Sp K))
  (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
  E8Fibration.IsPPFib B gQ M → E8Fibration.IsProd pr → E8Fibration.IsE8WeightedBundle W pr P'.L M.L → ∀ (N : ℕ), 0 < N → ∀ (s t s' t' : Fin 8 → ℤ),
  dotProduct s ((E8Fibration.e8 W).mulVec t) = dotProduct s' ((E8Fibration.e8 W).mulVec t') →
  ∀ (p q : Out.baseOver (Sp K) ⟶ B), p ^ N = 1 → q ^ N = 1 →
  ∀ (x y x' y' : Out.baseOver (Sp K) ⟶ P'.A), (∀ u, x ≫ pr u = p ^ s u) → (∀ u, y ≫ pr u = q ^ t u) →
    (∀ u, x' ≫ pr u = p ^ s' u) → (∀ u, y' ≫ pr u = q ^ t' u) →
    ∀ c, Out.WeilIs P'.A P'.L N x y c → Out.WeilIs P'.A P'.L N x' y' c := by
  intro W _ gQ K _ _ P' B _ _ M pr hF hP hE N _ s t s' t' hst p q hp hq x y x' y' hx hy hx' hy' c hc
  letI := P'.isAb.comm
  obtain ⟨cub⟩ := hF.2.2.1
  obtain ⟨r, hr, ⟨cL⟩⟩ := GlobalTheory.PolAV_exists_cubical GlobalTheory.abelianSchemeLaws_all.1.cube P'
  obtain ⟨f, hfm, hf⟩ := exists_hom hP s
  obtain ⟨g, hgm, hg⟩ := exists_hom hP t
  obtain ⟨f', hfm', hf'⟩ := exists_hom hP s'
  obtain ⟨g', hgm', hg'⟩ := exists_hom hP t'
  have ex : x = p ≫ f := (hP.2 _ fun u => p ^ s u).unique hx (hf _ p)
  have ey : y = q ≫ g := (hP.2 _ fun u => q ^ t u).unique hy (hg _ q)
  have ex' : x' = p ≫ f' := (hP.2 _ fun u => p ^ s' u).unique hx' (hf' _ p)
  have ey' : y' = q ≫ g' := (hP.2 _ fun u => q ^ t' u).unique hy' (hg' _ q)
  subst ex ey ex' ey'
  have hc₁ : (cubeLB P'.A ![fst B B ≫ f', snd B B ≫ g'] P'.L).IsLB := LB.isLB_linComb P'.isLB _ _
  have hc₂ : (cubeLB P'.A ![fst B B ≫ f, snd B B ≫ g] P'.L).IsLB := LB.isLB_linComb P'.isLB _ _
  have H : LBIso (cubeLB P'.A ![fst B B ≫ f', snd B B ≫ g'] P'.L) (cubeLB P'.A ![fst B B ≫ f, snd B B ≫ g] P'.L) := by
    refine (GlobalTheory.CechPic.cls_eq_iff hc₁ hc₂).1 ?_
    rw [PrimPic.cube_class_e8Bundle_eighth_power W pr hP.1 P'.L P'.isLB M cub hE, PrimPic.cube_class_e8Bundle_eighth_power W pr hP.1 P'.L P'.isLB M cub hE,
      funext (hf _ (fst B B)), funext (hg _ (snd B B)), funext (hf' _ (fst B B)), funext (hg' _ (snd B B)),
      bil_zpow M cub, bil_zpow M cub, hst]
  have : Subsingleton (Out.baseOver (Sp K)).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  exact weilIs_of_lbIso GlobalTheory.abelianSchemeLaws_all.1.globalFns P'.isAb hF.1 cL f' g' f g H
    (T := Out.baseOver (Sp K)) (default : PrimeSpectrum K) (fun _ => Subsingleton.elim _ _) N p q hp hq c hc

end GlobalTheory.Poinc.Sep.E8Fibration.PairVal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingMumfordLambdaSquare
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LamPairing

section Coords

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

theorem finset_fin_two (I : Finset (Fin 2)) : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by
  revert I; decide

theorem psum_empty : psum G (x2 G) ∅ = 1 := by
  simp [psum, pzero]; rfl

theorem psum_zero : psum G (x2 G) {0} = fst G G := by
  simp [psum, padd, pzero, x2, List.finRange]

theorem psum_one : psum G (x2 G) {1} = snd G G := by
  simp [psum, padd, pzero, x2, List.finRange]

theorem psum_both : psum G (x2 G) {0, 1} = fst G G * snd G G := by
  simp [psum, padd, pzero, x2, List.finRange]
  show μ[G] = lift (fst G G) (snd G G) ≫ μ[G]
  rw [lift_fst_snd, Category.id_comp]

theorem squareGroupPartialSum_isMonHom (I : Finset (Fin 2)) : IsMonHom (psum G (x2 G) I) := by
  rcases finset_fin_two I with rfl | rfl | rfl | rfl
  · rw [psum_empty]; exact inferInstanceAs (IsMonHom (toUnit (G2 G) ≫ η[G]))
  · rw [psum_zero]; infer_instance
  · rw [psum_one]; infer_instance
  · rw [psum_both]
    show IsMonHom (lift (fst G G) (snd G G) ≫ μ[G])
    rw [lift_fst_snd, Category.id_comp]
    infer_instance

end Coords

theorem prod_ulift_finset_fin_two {M : Type} [CommMonoid M] (f : ULift.{0} (Finset (Fin 2)) → M) :
    ∏ I, f I = f ⟨∅⟩ * f ⟨{0}⟩ * f ⟨{1}⟩ * f ⟨{0, 1}⟩ := by
  rw [← Fintype.prod_equiv Equiv.ulift.symm (fun I => f (Equiv.ulift.symm I)) f (fun _ => rfl)]
  have h : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [h, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  simp only [Equiv.ulift_symm_apply]
  ac_rfl

theorem weilIs_lam (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ) (T : Over S)
    (x₁ x₂ y₁ y₂ : T ⟶ P.A) (hx₁ : x₁ ^ n = 1) (hx₂ : x₂ ^ n = 1) (hy₁ : y₁ ^ n = 1) (hy₂ : y₂ ^ n = 1)
    (c₁ c₂ : Γ(T.left, ⊤)ˣ) (h₁ : WeilIs P.A P.L n x₁ y₂ c₁) (h₂ : WeilIs P.A P.L n x₂ y₁ c₂) :
    WeilIs (G2 P.A) (abelian₂ P.A P.L) n (lift x₁ x₂) (lift y₁ y₂) (c₁ * c₂) := by
  have hW : WeilSt := GlobalTheory.firstFiveLaws.1.weil
  obtain ⟨a, ha, -⟩ := (hW S P n T).1 x₁ y₁ hx₁ hy₁
  obtain ⟨b, hb, -⟩ := (hW S P n T).1 x₂ y₂ hx₂ hy₂
  have hmul := (hW S P n T).2.1
  have h₀ : WeilIs P.A P.L n 1 1 1 := (hW S P n T).2.2.1 1 (one_pow n)

  have hr : ∀ (x y y' : T ⟶ P.A) (c c' : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L n x y c → WeilIs P.A P.L n x y' c' →
      WeilIs P.A P.L n x (y * y') (c * c') := fun x y y' c c' hc hc' => by
    have := CommPairing.weilIs_symm P.isLB
      (hmul _ _ _ _ _ (CommPairing.weilIs_symm P.isLB hc) (CommPairing.weilIs_symm P.isLB hc'))
    rwa [← mul_inv, inv_inv] at this
  have h₁₂ : WeilIs P.A P.L n (x₁ * x₂) (y₁ * y₂) (a * c₁ * (c₂ * b)) :=
    hmul _ _ _ _ _ (hr _ _ _ _ _ ha h₁) (hr _ _ _ _ _ h₂ hb)
  have hA : IsAbelianScheme (G2 P.A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ P.isAb P.isAb
  let c : ULift.{0} (Finset (Fin 2)) → Γ(T.left, ⊤)ˣ := fun I =>
    (if (0 : Fin 2) ∈ I.down then a else 1) * (if (1 : Fin 2) ∈ I.down then b else 1) *
      (if (0 : Fin 2) ∈ I.down ∧ (1 : Fin 2) ∈ I.down then c₁ * c₂ else 1)
  have key := PairingComb.weilIs_linComb (D := P.L) GlobalTheory.globalFns_holds hA P.isLB
    (fun I : ULift.{0} (Finset (Fin 2)) => psum P.A (x2 P.A) I.down) (fun I => squareGroupPartialSum_isMonHom P.A I.down)
    (fun I => (-1) ^ (2 - I.down.card)) (n := n) (x := lift x₁ x₂) (y := lift y₁ y₂) c (by
      rintro ⟨I⟩
      rcases finset_fin_two I with rfl | rfl | rfl | rfl
      · simp only [c, psum_empty, MonObj.comp_one]
        simpa using h₀
      · simp only [c, psum_zero, lift_fst]
        simpa using ha
      · simp only [c, psum_one, lift_snd]
        simpa using hb
      · simp only [c, psum_both, MonObj.comp_mul, lift_fst, lift_snd]
        convert h₁₂ using 1
        simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, and_self, if_true]
        ac_rfl)
  have e : ∏ I, c I ^ ((-1 : ℤ) ^ (2 - I.down.card)) = c₁ * c₂ := by
    rw [prod_ulift_finset_fin_two]
    simp [c]
    rw [← mul_inv, inv_mul_cancel_left]
  rw [e] at key
  exact key

end GlobalTheory.LamPairing
end
end

