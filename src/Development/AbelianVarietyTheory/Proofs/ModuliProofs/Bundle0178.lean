module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0171
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsGrowthBasicPropertiesAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KernelTrivialOfEveryPointCovered
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.KTrivGlob

private theorem mul_left_congr_of_base_eq {S T : Scheme.{0}} {G : Over S} [GrpObj G] {a b : T ⟶ S} (hab : a = b)
    (u v : Over.mk a ⟶ G) (u' v' : Over.mk b ⟶ G) (hu : u.left = u'.left) (hv : v.left = v'.left) :
    (u * v).left = (u' * v').left := by
  subst hab
  have h1 : u = u' := Over.OverMorphism.ext hu
  have h2 : v = v' := Over.OverMorphism.ext hv
  subst h1 h2
  rfl

private theorem exists_isGrpPullback_factor {S S₁ S₂ : Scheme.{0}} {G : Over S} {G₁ : Over S₁} {G₂ : Over S₂}
    [GrpObj G] [GrpObj G₁] [GrpObj G₂] {f₁ : S₁ ⟶ S} {g : S₂ ⟶ S₁} {φ₁ : G₁.left ⟶ G.left}
    {φ₂ : G₂.left ⟶ G.left} (h₁ : IsGrpPullback G₁ G f₁ φ₁) (h₂ : IsGrpPullback G₂ G (g ≫ f₁) φ₂) :
    ∃ ψ : G₂.left ⟶ G₁.left, ψ ≫ φ₁ = φ₂ ∧ IsGrpPullback G₂ G₁ g ψ := by
  obtain ⟨hp₁, hm₁⟩ := h₁
  obtain ⟨hp₂, hm₂⟩ := h₂
  have hw : φ₂ ≫ G.hom = (G₂.hom ≫ g) ≫ f₁ := by rw [hp₂.w]; simp
  refine ⟨hp₁.lift φ₂ (G₂.hom ≫ g) hw, hp₁.lift_fst _ _ _, ?_, ?_⟩
  · refine IsPullback.of_right ?_ (hp₁.lift_snd _ _ _) hp₁
    rw [hp₁.lift_fst]
    exact hp₂
  · intro T x y x₀ y₀ hx hy
    apply hp₁.hom_ext
    · have ex : (x₀.left ≫ φ₁) ≫ G.hom = (T.hom ≫ g) ≫ f₁ := by
        rw [Category.assoc, hp₁.w, ← Category.assoc, Over.w x₀]; rfl
      have ey : (y₀.left ≫ φ₁) ≫ G.hom = (T.hom ≫ g) ≫ f₁ := by
        rw [Category.assoc, hp₁.w, ← Category.assoc, Over.w y₀]; rfl
      have fx : (x.left ≫ φ₂) ≫ G.hom = T.hom ≫ g ≫ f₁ := by
        rw [Category.assoc, hp₂.w, ← Category.assoc, Over.w x]
      have fy : (y.left ≫ φ₂) ≫ G.hom = T.hom ≫ g ≫ f₁ := by
        rw [Category.assoc, hp₂.w, ← Category.assoc, Over.w y]
      have A := hm₁ (Over.mk (T.hom ≫ g)) x₀ y₀ (Over.homMk (x₀.left ≫ φ₁) ex) (Over.homMk (y₀.left ≫ φ₁) ey) rfl rfl
      have B := hm₂ T x y (Over.homMk (x.left ≫ φ₂) fx) (Over.homMk (y.left ≫ φ₂) fy) rfl rfl
      have C := mul_left_congr_of_base_eq (Category.assoc T.hom g f₁) (Over.homMk (x₀.left ≫ φ₁) ex)
        (Over.homMk (y₀.left ≫ φ₁) ey) (Over.homMk (x.left ≫ φ₂) fx) (Over.homMk (y.left ≫ φ₂) fy)
        (by simp [hx, hp₁.lift_fst]) (by simp [hy, hp₁.lift_fst])
      rw [← A, C, B, Category.assoc, hp₁.lift_fst]
    · rw [Over.w (x₀ * y₀), Category.assoc, hp₁.lift_snd, ← Category.assoc, Over.w (x * y)]
      rfl

private theorem isGrpPullback_comp' {S S₁ S₂ : Scheme.{0}} {G : Over S} {G₁ : Over S₁} {G₂ : Over S₂}
    [GrpObj G] [GrpObj G₁] [GrpObj G₂] {f : S₁ ⟶ S} {g : S₂ ⟶ S₁} {φ : G₁.left ⟶ G.left}
    {ψ : G₂.left ⟶ G₁.left} (h₂ : IsGrpPullback G₂ G₁ g ψ) (h₁ : IsGrpPullback G₁ G f φ) :
    IsGrpPullback G₂ G (g ≫ f) (ψ ≫ φ) := by
  obtain ⟨hp₁, hm₁⟩ := h₁
  obtain ⟨hp₂, hm₂⟩ := h₂
  refine ⟨hp₂.paste_horiz hp₁, ?_⟩
  intro T x y x₀ y₀ hx hy
  have ex : (x.left ≫ ψ) ≫ G₁.hom = T.hom ≫ g := by
    rw [Category.assoc, hp₂.w, ← Category.assoc, Over.w x]
  have ey : (y.left ≫ ψ) ≫ G₁.hom = T.hom ≫ g := by
    rw [Category.assoc, hp₂.w, ← Category.assoc, Over.w y]
  have ex' : ((x.left ≫ ψ) ≫ φ) ≫ G.hom = (T.hom ≫ g) ≫ f := by
    rw [Category.assoc, hp₁.w, ← Category.assoc, ex]
  have ey' : ((y.left ≫ ψ) ≫ φ) ≫ G.hom = (T.hom ≫ g) ≫ f := by
    rw [Category.assoc, hp₁.w, ← Category.assoc, ey]
  have A := hm₂ T x y (Over.homMk (x.left ≫ ψ) ex) (Over.homMk (y.left ≫ ψ) ey) rfl rfl
  have B := hm₁ (Over.mk (T.hom ≫ g)) (Over.homMk (x.left ≫ ψ) ex) (Over.homMk (y.left ≫ ψ) ey)
    (Over.homMk ((x.left ≫ ψ) ≫ φ) ex') (Over.homMk ((y.left ≫ ψ) ≫ φ) ey') rfl rfl
  have C := mul_left_congr_of_base_eq (Category.assoc T.hom g f).symm x₀ y₀ (Over.homMk ((x.left ≫ ψ) ≫ φ) ex')
    (Over.homMk ((y.left ≫ ψ) ≫ φ) ey') (by simp [hx]) (by simp [hy])
  rw [C, B, A, Category.assoc]

theorem kTriv_transfer {S S₁ S₂ : Scheme.{0}} {G : Over S} {G₁ : Over S₁} {G₂ : Over S₂} [GrpObj G] [GrpObj G₁]
    [GrpObj G₂] {f₁ : S₁ ⟶ S} {g : S₂ ⟶ S₁} {φ₁ : G₁.left ⟶ G.left} {φ₂ : G₂.left ⟶ G.left} {L : LB G.left}
    {L₁ : LB G₁.left} {L₂ : LB G₂.left} (hL : L.IsLB) (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB)
    (h₁ : IsGrpPullback G₁ G f₁ φ₁) (h₂ : IsGrpPullback G₂ G (g ≫ f₁) φ₂)
    (e₁ : LBIso L₁ (L.pull φ₁)) (e₂ : LBIso L₂ (L.pull φ₂)) (hK : Out.KTriv G₁ L₁) : Out.KTriv G₂ L₂ := by
  obtain ⟨ψ, hψ, hG⟩ := exists_isGrpPullback_factor h₁ h₂
  have e₃ : LBIso (L₁.pull ψ) (L.pull φ₂) := GlobalTheory.GenSpread.lbIso_pull_of_lbIso e₁ ψ hψ.symm
  have hψL : (L₁.pull ψ).IsLB := pull_isLB hL₁ ψ
  have e₄ : LBIso L₂ (L₁.pull ψ) := LBIso.trans hL₂ (pull_isLB hL φ₂) hψL e₂ (LBIso.symm e₃)
  obtain ⟨w, hw⟩ := e₄
  exact kTriv_pull hG hL₁ hL₂ ((isGen_iff w).1 hw) hK

set_option maxHeartbeats 400000 in
private theorem exists_open_kTriv_restrict_of_kTriv_fibre {S S' : Scheme.{0}} [IsLocallyNoetherian S] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hG : IsAbelianScheme G) (hA : Out.RelAmple G L) (h : IsGrpPullback G' G f φ) (e : LBIso L' (L.pull φ))
    (hK : Out.KTriv G' L') (q : S') :
    ∃ U : S.Opens, f q ∈ U ∧ Out.KTriv ((Over.pullback U.ι).obj G) (L.pull (pullback.fst G.hom U.ι)) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hfqV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f q)) isOpen_univ
  replace hV : IsAffineOpen V := hV
  haveI : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hAp : IsGrpPullback ((Over.pullback hV.fromSpec).obj G) G hV.fromSpec (pullback.fst G.hom hV.fromSpec) :=
    isGrpPullback_pullback G hV.fromSpec
  have hLA : (L.pull (pullback.fst G.hom hV.fromSpec)).IsLB := pull_isLB hL _
  obtain ⟨hAb, hAamp, -⟩ := GlobalTheory.pol_pull S _ G ((Over.pullback hV.fromSpec).obj G) hV.fromSpec _ L _ hL hLA hG hAp
    (PolBaseChange.lbIso_refl hLA)
  have hrange : Set.range (S'.fromSpecResidueField q ≫ f) ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨z, rfl⟩
    rw [hV.range_fromSpec]
    simpa using hfqV
  obtain ⟨m, hm⟩ : ∃ m : Spec (S'.residueField q) ⟶ Spec Γ(S, V),
      m ≫ hV.fromSpec = S'.fromSpecResidueField q ≫ f :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hrange⟩
  have hx : spMap (Spec.preimage m).hom = m := Spec.map_preimage m
  have hpt : spMap (Spec.preimage m).hom ≫ hV.fromSpec = S'.fromSpecResidueField q ≫ f := by rw [hx, hm]
  have h₂ := IsGrpPullback.congr (isGrpPullback_comp'
    (isGrpPullback_pullback ((Over.pullback hV.fromSpec).obj G) (spMap (Spec.preimage m).hom)) hAp) hpt rfl
  have hK₀ := kTriv_transfer hL hL' (pull_isLB hLA _) h h₂ e
    (LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_pull hL _ rfl)) hK
  obtain ⟨r, hr, hsp⟩ := _root_.GlobalTheory.KTrivSpread.exists_kTriv_of_isUnit Γ(S, V) ((Over.pullback hV.fromSpec).obj G)
    (L.pull (pullback.fst G.hom hV.fromSpec)) (S'.residueField q) (Spec.preimage m).hom
    ((Over.pullback (spMap (Spec.preimage m).hom)).obj ((Over.pullback hV.fromSpec).obj G))
    (pullback.fst ((Over.pullback hV.fromSpec).obj G).hom (spMap (Spec.preimage m).hom)) hAb hLA (hAamp hA)
    (isGrpPullback_pullback ((Over.pullback hV.fromSpec).obj G) (spMap (Spec.preimage m).hom)) hK₀
  have hmem : f q ∈ S.basicOpen r := by
    let z : Spec (S'.residueField q) := IsLocalRing.closedPoint (S'.residueField q)
    have e1 : (m ≫ hV.fromSpec) z = (S'.fromSpecResidueField q ≫ f) z := by rw [hm]
    simp only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] at e1
    rw [← e1]
    show m z ∈ hV.fromSpec ⁻¹ᵁ S.basicOpen r
    rw [hV.fromSpec_preimage_basicOpen]
    have hmz : m z = PrimeSpectrum.comap (Spec.preimage m).hom z :=
      (congrArg (fun k : Spec (S'.residueField q) ⟶ Spec Γ(S, V) => k z) (Spec.map_preimage m)).symm
    rw [hmz]
    show r ∉ (PrimeSpectrum.comap (Spec.preimage m).hom z).asIdeal
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    intro hin
    apply hr
    have : ¬ IsUnit ((Spec.preimage m).hom r) := (IsLocalRing.mem_maximalIdeal _).1 hin
    simpa using this
  have hU := hV.basicOpen r
  refine ⟨S.basicOpen r, hmem, ?_⟩
  have hunit : IsUnit ((S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom r) :=
    S.toRingedSpace.isUnit_res_basicOpen r
  have hK' := hsp Γ(S, S.basicOpen r) (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom
    ((Over.pullback (spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom)).obj
      ((Over.pullback hV.fromSpec).obj G))
    (pullback.fst ((Over.pullback hV.fromSpec).obj G).hom (spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom))
    hunit (isGrpPullback_pullback ((Over.pullback hV.fromSpec).obj G) (spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom))
  have h₁' := isGrpPullback_comp' (isGrpPullback_pullback ((Over.pullback hV.fromSpec).obj G)
    (spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom)) hAp
  have hιeq : (S.basicOpen r).ι = hU.isoSpec.hom ≫
      (spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom ≫ hV.fromSpec) := by
    rw [show spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom ≫ hV.fromSpec = hU.fromSpec from
      hV.map_fromSpec hU (homOfLE (S.basicOpen_le r)).op, hU.isoSpec_hom_fromSpec]
  have h₂' := IsGrpPullback.congr (isGrpPullback_pullback G (S.basicOpen r).ι) hιeq rfl
  exact kTriv_transfer hL (pull_isLB hLA _) (pull_isLB hL _) h₁' h₂'
    (LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_pull hL _ rfl)) (PolBaseChange.lbIso_refl (pull_isLB hL _)) hK'

theorem exists_open {S S' : Scheme.{0}} [IsLocallyNoetherian S] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hG : IsAbelianScheme G) (hA : Out.RelAmple G L) (h : IsGrpPullback G' G f φ) (e : LBIso L' (L.pull φ))
    (hK : Out.KTriv G' L') (q : S') :
    ∃ U : S.Opens, f q ∈ U ∧ Out.KTriv ((Over.pullback U.ι).obj G) (L.pull (pullback.fst G.hom U.ι)) := exists_open_kTriv_restrict_of_kTriv_fibre hL hL' hG hA h e hK q

theorem kTriv_of_forall_point : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → (∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (_ : SABMap t' t f), p ∈ Set.range f ∧ Out.KTriv t'.G t'.PP.L) → Out.KTriv t.G t.PP.L := by
  intro hLaws E _ _ _ H S _ t hP hA h
  haveI : IsProper t.G.hom := hP
  have hAb : IsAbelianScheme t.G := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
  have hL : t.PP.L.IsLB := t.PP.isLB
  have hU : ∀ p : S, ∃ U : S.Opens, p ∈ U ∧
      Out.KTriv ((Over.pullback U.ι).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom U.ι)) := by
    intro p
    obtain ⟨S', f, t', ⟨cm, cart, -, -, lin⟩, ⟨q, rfl⟩, hk⟩ := h p
    obtain ⟨w, hw, -⟩ := lin
    exact exists_open hL t'.PP.isLB hAb hA cart ⟨w, hw⟩ hk q
  choose U hpU hKU using hU
  exact GlobalTheory.CoverGlue.kTriv_of_cover S S U t.G (fun p => (Over.pullback (U p).ι).obj t.G)
    (fun p => pullback.fst t.G.hom (U p).ι)
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hpU x⟩)
    (fun p => isGrpPullback_pullback t.G (U p).ι) t.PP.L (fun p => t.PP.L.pull (pullback.fst t.G.hom (U p).ι))
    hL (fun p => pull_isLB hL _) (fun p => PolBaseChange.lbIso_refl (pull_isLB hL _)) hAb
    (fun p => (GlobalTheory.pol_pull S (U p).toScheme t.G _ (U p).ι _ t.PP.L _ hL (pull_isLB hL _) hAb
      (isGrpPullback_pullback t.G (U p).ι) (PolBaseChange.lbIso_refl (pull_isLB hL _))).1) hKU

end GlobalTheory.KTrivGlob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarizedAbelianAmpleExistsPositiveVolume
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV Filter Topology

namespace GlobalTheory.VolEx

theorem tendsto_pow_div_pow {i k : ℕ} (h : i ≤ k) :
    Tendsto (fun e : ℕ => (e : ℝ) ^ i / (e : ℝ) ^ k) atTop (𝓝 (if i = k then 1 else 0)) := by
  split_ifs with hik
  · subst hik
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with e he
    rw [div_self (by positivity)]
  · exact (tendsto_pow_div_pow_atTop_zero (𝕜 := ℝ) (lt_of_le_of_ne h hik)).comp tendsto_natCast_atTop_atTop

theorem tendsto_eval_div_pow (Q : Polynomial ℚ) {k : ℕ} (h : Q.natDegree ≤ k) :
    Tendsto (fun e : ℕ => ((Q.eval (e : ℚ) : ℚ) : ℝ) / (e : ℝ) ^ k) atTop (𝓝 (Q.coeff k : ℝ)) := by
  have h1 : Tendsto (fun e : ℕ => ∑ i ∈ Finset.range (k + 1), (Q.coeff i : ℝ) * ((e : ℝ) ^ i / (e : ℝ) ^ k)) atTop
      (𝓝 (∑ i ∈ Finset.range (k + 1), (Q.coeff i : ℝ) * (if i = k then 1 else 0))) :=
    tendsto_finsetSum _ fun i hi =>
      (tendsto_pow_div_pow (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).const_mul _
  simp only [mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_self, if_true] at h1
  refine h1.congr fun e => ?_
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le h)]
  push_cast
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => (mul_div_assoc _ _ _).symm

variable {K : Type} [Field K] {X : Scheme.{0}}

theorem vAmp_of_veryAmpleBy {p : X ⟶ Sp K} {M : LB X} {m : ℕ} {s : Fin (m + 1) → M.Sec}
    (h : AbLaw.VeryAmpleBy p M s) : VAmp p M s := by
  refine ⟨h.1, fun i => ⟨(h.2 i).1, ?_⟩⟩
  obtain ⟨r, hr, hs⟩ := (h.2 i).2
  refine ⟨r, hr, fun f => ?_⟩
  obtain ⟨F, hF⟩ := hs f
  exact ⟨F, hF.symm⟩

theorem vol_of_eventually {p : X ⟶ Sp K} {M : LB X} (hex : ∀ e, ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r) (φ : ℕ → ℝ)
    (hφ : ∀ᶠ e : ℕ in atTop, ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ (r : ℝ) = φ e) {k : ℕ} {δ : ℝ}
    (hδ : Tendsto (fun e : ℕ => φ e / (e : ℝ) ^ k) atTop (𝓝 δ)) : Vol p M k δ := by
  have : ∀ e, ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ ((∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ (r : ℝ) = φ e) → (r : ℝ) = φ e) := by
    intro e
    by_cases h : ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ (r : ℝ) = φ e
    · obtain ⟨r, h1, h2⟩ := h
      exact ⟨r, h1, fun _ => h2⟩
    · obtain ⟨r, h1⟩ := hex e
      exact ⟨r, h1, fun h' => absurd h' h⟩
  choose h h1 h2 using this
  refine ⟨h, h1, hδ.congr' ?_⟩
  filter_upwards [hφ] with e he
  rw [h2 e he]

theorem vol_nonneg {p : X ⟶ Sp K} {M : LB X} {k : ℕ} {δ : ℝ} (h : Vol p M k δ) : 0 ≤ δ := by
  obtain ⟨h, -, hh⟩ := h
  exact ge_of_tendsto' hh fun e => by positivity

theorem exists_vol : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left), M.IsLB → Out.RelAmple P.A M → ∃ δ : ℝ, 0 < δ ∧ Vol P.A.hom M P.g δ := by
  intro hL _ K _ _ P M hM hA
  have hex : ∀ (N : LB P.A.left), N.IsLB → ∀ e, ∃ r, SectionsHaveFiniteDimension P.A.hom (lbPow N e) r := fun N hN e =>
    (_root_.GlobalTheory.VolBasic.vol_basic K P (lbPow N e) 0 (LB.isLB_linComb hN _ _)).1
  have : IsProper P.A.hom := P.isAb.proper
  obtain ⟨d, hd, m, s, hs⟩ :=
    ((relAmple_iff_isAmpleLB_of_isAffine P.A hM).1 hA).exists_veryAmpleBy (R := K) P.A.hom
  have hH : (lbPow M d).IsLB := LB.isLB_linComb hM _ _
  obtain ⟨Q, hQ⟩ := _root_.GlobalTheory.ZV.HilbFn.hilbertFunction_idealOf K (Fin (m + 1)) _ P.A.hom (lbPow M d) s hH (vAmp_of_veryAmpleBy hs)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have volM : ∀ k, Q.natDegree ≤ k → Vol P.A.hom M k ((Q.coeff k : ℝ) / (d : ℝ) ^ k) := by
    intro k hk
    refine (_root_.GlobalTheory.VolBasic.vol_basic K P M k hM).2.2.2.2.1 d _ hd hA ?_
    rw [mul_div_cancel₀ _ (by positivity)]
    refine vol_of_eventually (hex _ hH) _ ?_ (tendsto_eval_div_pow Q hk)
    filter_upwards [hQ] with e ⟨r, h1, h2, _⟩
    exact ⟨r, h1, by rw [← h2]; norm_cast⟩
  have volL : ∀ k, P.g ≤ k → Vol P.A.hom P.L k (if P.g = k then 1 else 0) := by
    intro k hk
    refine vol_of_eventually (hex _ P.isLB) (fun e => (e : ℝ) ^ P.g) ?_ (tendsto_pow_div_pow hk)
    filter_upwards [eventually_ge_atTop 1] with e he
    exact ⟨e ^ P.g, PowSec.exists_basis_sections hL.globalSectionsRank K P e he, by push_cast; rfl⟩
  have dom : ∀ (A B : LB P.A.left), A.IsLB → B.IsLB → Out.RelAmple P.A A → ∃ c : ℕ, ∀ k δ δ',
      Vol P.A.hom B k δ → Vol P.A.hom A k δ' → δ ≤ (c : ℝ) ^ k * δ' := by
    intro A B hA hB ha
    obtain ⟨c, ⟨⟨t, ht⟩, -⟩, hc⟩ := ((_root_.GlobalTheory.AmpleDominates.eventually_sec_and_relAmple K P A B hA hB ha).and (eventually_ge_atTop 1)).exists
    refine ⟨c, fun k δ δ' h1 h2 => ?_⟩
    exact ((_root_.GlobalTheory.VolBasic.vol_basic K P B k hB).2.2.2.2.2 (lbPow A c) t (LB.isLB_linComb hA _ _) ht).2 _ _ h1
      ((_root_.GlobalTheory.VolBasic.vol_basic K P A k hA).2.2.2.1 c δ' hc h2)
  have hdeg : Q.natDegree ≤ P.g := by
    by_contra hlt
    push Not at hlt
    obtain ⟨c, hc⟩ := dom P.L M P.isLB hM P.ample
    have h1 := hc _ _ _ (volM _ le_rfl) (volL _ hlt.le)
    rw [if_neg hlt.ne, mul_zero] at h1
    have h2 := le_antisymm h1 (vol_nonneg (volM _ le_rfl))
    rw [div_eq_zero_iff] at h2
    rcases h2 with h2 | h2
    · have h3 : Q.leadingCoeff = 0 := by exact_mod_cast h2
      rw [Polynomial.leadingCoeff_eq_zero] at h3
      rw [h3] at hlt
      simp at hlt
    · exact absurd h2 (by positivity)
  refine ⟨_, ?_, volM _ hdeg⟩
  obtain ⟨c, hc⟩ := dom M P.L hM P.isLB hA
  have h1 := hc _ _ _ (volL _ le_rfl) (volM _ hdeg)
  rw [if_pos rfl] at h1
  refine lt_of_le_of_ne (vol_nonneg (volM _ hdeg)) fun h => ?_
  rw [← h, mul_zero] at h1
  exact absurd h1 (by norm_num)

end GlobalTheory.VolEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SerreLemmaSemiAbelian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory
namespace SerreLemma

variable {k : Type} [Field k] [IsAlgClosed k]

theorem exists_lift {X Y : Over (Sp k)} (m : X ⟶ Y) [LocallyOfFiniteType m.left]
    (x : 𝟙_ (Over (Sp k)) ⟶ Y) (hx : x.left (IsLocalRing.closedPoint k) ∈ Set.range m.left) :
    ∃ a : 𝟙_ (Over (Sp k)) ⟶ X, a ≫ m = x := by
  let x' : Spec (CommRingCat.of k) ⟶ Y.left := x.left
  have hJ : JacobsonSpace ↥(pullback m.left x') :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd m.left x')
  obtain ⟨w, hw⟩ := hx
  obtain ⟨z₀, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := m.left) (g := x') w _ hw
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback m.left x')))
    ⟨z₀, trivial⟩ isClosed_univ.isLocallyClosed
  replace hz : IsClosed {z} := hz
  have e : (pointOfClosedPoint (pullback.snd m.left x') z hz ≫ pullback.fst _ _) ≫ m.left = x' := by
    rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
  refine ⟨Over.homMk (pointOfClosedPoint (pullback.snd m.left x') z hz ≫ pullback.fst _ _) ?_,
    Over.OverMorphism.ext e⟩
  rw [← Over.w m, ← Category.assoc, e]
  exact Over.w x

theorem exists_pow_eq (G : Over (Sp k)) [GrpObj G] (hG : IsSemiAbelian G) (n : ℕ) (hn : (n : k) ≠ 0)
    (x : 𝟙_ (Over (Sp k)) ⟶ G) : ∃ y : 𝟙_ (Over (Sp k)) ⟶ G, y ^ n = x := by
  have := hG.comm
  have := hG.smooth
  have : IsIntegral G.left := isIntegral_left_of_isSemiAbelian G
  have hu : IsUnit (n : Γ(Sp k, ⊤)) := by
    simpa using (Ne.isUnit hn).map (Scheme.ΓSpecIso (.of k)).inv.hom
  have := GrpTangent.etale_mulN G hu
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  set U : Set G.left := Set.range (mulN G n).left with hU
  have hUo : IsOpen U := (mulN G n).left.isOpenMap.isOpen_range
  have hone : (1 : 𝟙_ _ ⟶ G).left (IsLocalRing.closedPoint k) ∈ U := by
    refine ⟨(1 : 𝟙_ _ ⟶ G).left (IsLocalRing.closedPoint k), ?_⟩
    exact congrArg (fun z : 𝟙_ (Over (Sp k)) ⟶ G => z.left (IsLocalRing.closedPoint k))
      (MonObj.one_comp (mulN G n))
  have hVo : IsOpen ((GrpObj.mulRight x).hom.left ⁻¹' U) := hUo.preimage (Scheme.Hom.continuous _)
  have hV : ((GrpObj.mulRight x).hom.left ⁻¹' U).Nonempty := by
    refine ⟨(x⁻¹).left (IsLocalRing.closedPoint k), ?_⟩
    rw [Set.mem_preimage, OpenSubgroupScheme.mulRight_apply, inv_mul_cancel]
    exact hone
  obtain ⟨y, ⟨hyU, hyV⟩, hyc⟩ := nonempty_inter_closedPoints
    (nonempty_preirreducible_inter hUo hVo ⟨_, hone⟩ hV) (hUo.inter hVo).isLocallyClosed
  obtain ⟨z, rfl⟩ := OpenSubgroupScheme.exists_point y hyc
  rw [Set.mem_preimage, OpenSubgroupScheme.mulRight_apply] at hyV
  obtain ⟨a, ha⟩ := exists_lift _ z hyU
  obtain ⟨b, hb⟩ := exists_lift _ _ hyV
  rw [GrpTangent.comp_mulN] at ha hb
  refine ⟨a⁻¹ * b, ?_⟩
  rw [mul_pow, inv_pow, ha, hb, inv_mul_cancel_left]

end SerreLemma

theorem serre_lemma_semiAbelian :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G],
      IsSemiAbelian G → ∀ (N r : ℕ) (u : Aut G), Odd N → 3 ≤ N → (N : k) ≠ 0 →
        0 < r → IsMonHom u.asIso.hom → u ^ r = 1 →
        (∀ x : 𝟙_ (Over (Sp k)) ⟶ G, x ^ N = 1 → x ≫ u.asIso.hom = x) → u = 1 := by
  intro k _ _ G _ hG N r u hodd h3 hN hr hu hur hfix
  have := hG.comm
  obtain ⟨l, hl, hlN⟩ := Nat.exists_prime_and_dvd (n := N) (by omega)
  have hlo : Odd l := Odd.of_dvd_nat hodd hlN
  have hlk : (l : k) ≠ 0 := by
    obtain ⟨c, rfl⟩ := hlN
    rw [Nat.cast_mul] at hN
    exact left_ne_zero_of_mul hN
  let e : (𝟙_ (Over (Sp k)) ⟶ G) ≃* (𝟙_ (Over (Sp k)) ⟶ G) :=
    { toFun x := x ≫ u.asIso.hom
      invFun x := x ≫ u.asIso.inv
      left_inv x := (Category.assoc _ _ _).trans
        ((congrArg (x ≫ ·) u.asIso.hom_inv_id).trans (Category.comp_id x))
      right_inv x := (Category.assoc _ _ _).trans
        ((congrArg (x ≫ ·) u.asIso.inv_hom_id).trans (Category.comp_id x))
      map_mul' x y := MonObj.mul_comp x y u.asIso.hom }
  have hit : ∀ (n : ℕ) x, e^[n] x = x ≫ (u ^ n).asIso.hom := by
    intro n
    induction n with
    | zero => intro x; exact (Category.comp_id x).symm
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', ih, pow_succ', Aut.mul_asIso]
      exact Category.assoc x (u ^ n).asIso.hom u.asIso.hom
  have key := minkowski_divisible _ l e r hl hlo hr (SerreLemma.exists_pow_eq G hG l hlk)
    (fun x => by rw [hit, hur]; exact Category.comp_id x)
    (fun x hx => hfix x (by obtain ⟨c, rfl⟩ := hlN; rw [pow_mul, hx, one_pow]))
  have hm : IsMonHom (u.asIso.hom * (𝟙 G)⁻¹) :=
    { one_hom := by
        rw [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, IsMonHom.one_hom, mul_inv_cancel,
          one_eq_one]
      mul_hom := by
        rw [mul_eq_mul, MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, MonObj.mul_comp,
          MonObj.comp_mul, mul_inv, _root_.mul_mul_mul_comm]
        congr 1 <;> simp [MonObj.comp_mul, GrpObj.comp_inv] }
  have h1 := GlobalTheory.TorsionDense.eq_one_of_torsion_comp_eq_one k G G hG hG l hl hlk
    (u.asIso.hom * (𝟙 G)⁻¹) hm (fun _ _ y a hy => by
    rw [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id]
    exact mul_inv_eq_one.mpr (key y a hy))
  exact Aut.ext (Iso.ext (mul_inv_eq_one.mp h1))

end GlobalTheory
end

