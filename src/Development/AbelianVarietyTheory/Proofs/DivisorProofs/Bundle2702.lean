module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2666
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0095
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.NotRelAmpleOfNotIsProper
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2637
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsSeparateQuotientGenericFibreDescends
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormBasepointFreeSectionsLeOneFubiniStudy
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem canNorms : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ (n : ℕ) (u : SmFn p), 1 ≤ n → IsCan P e n x u → (∀ l (σ : k →+* ℂ) (y : CxPts p σ), (upperParabolic P u).nu e 0 σ y (x l) ≤ 1) ∧ (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ l, Real.exp (-(Real.log (D + 1) / (2 * n))) ≤ (upperParabolic P u).nu e 0 σ y (x l)) ∧ Gens (upperParabolic P u) D e x ∧ Gens P D (e * n) (fun l => x l ^ n) ∧ IsCan P (e * n) 1 (fun l => x l ^ n) u := by
  intro k _ X _ p D _ P e x hx n u hn hu
  have he : (0 : ℝ) < e := by exact_mod_cast hx.pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : 2 * n ≠ 0 := by omega
  have hup := _root_.GlobalTheory.HSAmp.upAtPrime_groups_values_norms k X p P u (e : ℤ) 0
  have hnn : ∀ (Q : Pair p) σ (y : CxPts p σ) f, 0 ≤ Q.nu e 0 σ y f := fun Q σ y f => by
    rw [← norm_val]; exact norm_nonneg _
  have hS : ∀ σ (y : CxPts p σ), 0 < ∑ l, P.nu e 0 σ y (x l) ^ (2 * n) := by
    intro σ y
    obtain ⟨l, hl⟩ := hx.cover (under y)
    have h := ((_root_.GlobalTheory.HSAmp.nv_rules k X p P e 0 (x l) (hx.mem l)).2.2.2.2 (x l) (hx.mem l) σ y hl).2
    exact lt_of_lt_of_le (pow_pos h _) (Finset.single_le_sum (f := fun l => P.nu e 0 σ y (x l) ^ (2 * n))
      (fun i _ => pow_nonneg (hnn P σ y _) _) (Finset.mem_univ l))
  have key : ∀ σ (y : CxPts p σ) f, (upperParabolic P u).nu e 0 σ y f ^ (2 * n) =
      P.nu e 0 σ y f ^ (2 * n) / ∑ l, P.nu e 0 σ y (x l) ^ (2 * n) := by
    intro σ y f
    rw [(hup.2.2 σ y f).2, mul_pow, ← Real.exp_nat_mul, hu σ y]
    have : ((2 * n : ℕ) : ℝ) * (-(((e : ℤ) : ℝ) * (((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n)))) / 2)
        = -Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n)) := by
      push_cast; field_simp
    rw [this, Real.exp_neg, Real.exp_log (hS σ y), div_eq_mul_inv]
  refine ⟨fun l σ y => ?_, fun σ y => ?_, ⟨hx.pos, fun l => hup.1 ▸ hx.mem l, fun z => ?_⟩, ⟨?_, fun l => ?_, fun z => ?_⟩, ?_⟩
  · rw [← pow_le_pow_iff_left₀ (hnn _ σ y _) zero_le_one hn0, one_pow, key, div_le_one (hS σ y)]
    exact Finset.single_le_sum (f := fun l => P.nu e 0 σ y (x l) ^ (2 * n))
      (fun i _ => pow_nonneg (hnn P σ y _) _) (Finset.mem_univ l)
  · obtain ⟨l, -, hl⟩ := Finset.exists_max_image Finset.univ (fun l => P.nu e 0 σ y (x l)) Finset.univ_nonempty
    refine ⟨l, ?_⟩
    rw [← pow_le_pow_iff_left₀ (Real.exp_pos _).le (hnn _ σ y _) hn0, key, ← Real.exp_nat_mul]
    have e1 : ((2 * n : ℕ) : ℝ) * -(Real.log (D + 1) / (2 * n)) = -Real.log (D + 1) := by
      push_cast; field_simp
    have hD : (0 : ℝ) < D + 1 := by positivity
    rw [e1, Real.exp_neg, Real.exp_log hD, inv_eq_one_div, div_le_div_iff₀ hD (hS σ y), one_mul]
    calc ∑ i, P.nu e 0 σ y (x i) ^ (2 * n) ≤ ∑ _i : Fin (D + 1), P.nu e 0 σ y (x l) ^ (2 * n) :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (hnn P σ y _) (hl i (Finset.mem_univ i)) _
      _ = P.nu e 0 σ y (x l) ^ (2 * n) * (D + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  · obtain ⟨l, hl⟩ := hx.cover z
    exact ⟨l, (hup.2.1 (x l)).symm ▸ hl⟩
  · exact Nat.mul_pos hx.pos hn
  · have h := (GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e 0 (x l) (hx.mem l) n).1
    convert h using 2 <;> push_cast <;> ring
  · obtain ⟨l, hl⟩ := hx.cover z
    refine ⟨l, ?_⟩
    have h := (_root_.GlobalTheory.HSAmp.nv_rules k X p P e 0 (x l) (hx.mem l)).2.2.1 n hn
    have e2 : ((e * n : ℕ) : ℤ) = (n : ℤ) * (e : ℤ) := by push_cast; ring
    have e3 : (0 : ℤ) = (n : ℤ) * 0 := by ring
    show z ∈ NV P ((e * n : ℕ) : ℤ) 0 (x l ^ n)
    rw [e2, e3, h]; exact hl
  · intro σ y
    have hp : ∀ l, P.nu ((e * n : ℕ) : ℤ) 0 σ y (x l ^ n) = P.nu e 0 σ y (x l) ^ n := fun l => by
      have h := (GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e 0 (x l) (hx.mem l) n).2 σ y
      convert h using 2 <;> push_cast <;> ring
    rw [hu σ y]
    simp only [hp, ← pow_mul]
    push_cast
    ring_nf

end GlobalTheory.HSAmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianIsoDescendsFromAlgebraicExtensio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolIsoDescent

open GlobalTheory.Spread GlobalTheory.HomPairDescent

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem model_descends : ∀ (k K : Type) [Field k] [Field K] (σ : k →+* K), (∀ z : K, ∃ f : Polynomial k, f ≠ 0 ∧ Polynomial.eval₂ σ z f = 0) → ∀ (B₁ B₂ : PolAV (Sp k)) (P₀ : PolAV (Sp K)) (c₁ : P₀.A.left ⟶ B₁.A.left) (c₂ : P₀.A.left ⟶ B₂.A.left), IsGrpPullback P₀.A B₁.A (spMap σ) c₁ → IsGrpPullback P₀.A B₂.A (spMap σ) c₂ → LBIso P₀.L (B₁.L.pull c₁) → LBIso P₀.L (B₂.L.pull c₂) → ∃ s : Finset K, ∀ (k₁ : Type) [Field k₁] (α : k →+* k₁) (β : k₁ →+* K), β.comp α = σ → (s : Set K) ⊆ Set.range β → ∀ (C : PolAV (Sp k₁)) (χ : C.A.left ⟶ B₁.A.left), IsGrpPullback C.A B₁.A (spMap α) χ → LBIso C.L (B₁.L.pull χ) → ∃ χ₂ : C.A.left ⟶ B₂.A.left, IsGrpPullback C.A B₂.A (spMap α) χ₂ ∧ LBIso C.L (B₂.L.pull χ₂) ∧ ∀ d : P₀.A.left ⟶ C.A.left, d ≫ χ = c₁ → d ≫ C.A.hom = P₀.A.hom ≫ spMap β → d ≫ χ₂ = c₂ := by
  classical
  intro k K _ _ σ hσ B₁ B₂ P₀ c₁ c₂ h₁ h₂ hL₁ hL₂
  letI : Algebra k K := σ.toAlgebra
  haveI := B₁.isAb.proper
  haveI := B₂.isAb.proper
  haveI := B₁.isAb.smooth
  haveI := B₂.isAb.smooth
  have g₁ : IsGrpPullback ((Over.pullback (spMap (algebraMap k K))).obj B₁.A) B₁.A (spMap σ) (pullback.fst _ _) :=
    isGrpPullback_pullback B₁.A (spMap σ)
  have g₂ : IsGrpPullback ((Over.pullback (spMap (algebraMap k K))).obj B₂.A) B₂.A (spMap σ) (pullback.fst _ _) :=
    isGrpPullback_pullback B₂.A (spMap σ)
  obtain ⟨e₁, m₁, he₁⟩ := grpPullback_iso h₁ g₁
  obtain ⟨e₂, m₂, he₂⟩ := grpPullback_iso h₂ g₂
  let f := e₁.inv ≫ e₂.hom
  let r := e₂.inv ≫ e₁.hom
  have mf : IsMonHom f := inferInstance
  obtain ⟨sf, hsf⟩ := exists_descend B₁.A B₂.A f
  obtain ⟨sr, hsr⟩ := exists_descend B₂.A B₁.A r
  let L₁ : IntermediateField k K := IntermediateField.adjoin k ((sf ∪ sr : Finset K) : Set K)
  have hL : ((sf ∪ sr : Finset K) : Set K) ⊆ L₁ := IntermediateField.subset_adjoin _ _
  obtain ⟨θf, hθf⟩ := hsf L₁ ((Finset.coe_subset.2 Finset.subset_union_left).trans hL)
  obtain ⟨θr, hθr⟩ := hsr L₁ ((Finset.coe_subset.2 Finset.subset_union_right).trans hL)
  have gA := isGrpPullback_bcMap B₁.A L₁.val
  have gB := isGrpPullback_bcMap B₂.A L₁.val
  obtain ⟨hepi, hmon⟩ := FieldBaseChange.epi_and_isMonHom_iff L₁ K L₁.val.toRingHom
  haveI := (hepi _ _ _ _ _ gA.1).1
  haveI := (hepi _ _ _ _ _ gB.1).1
  haveI mθ : IsMonHom θf := (hmon _ _ _ _ _ _ θf f gA gB hθf).1 mf
  have r1 : θf ≫ θr = 𝟙 _ := by
    have := comp_eq_pow_of_epi gA hθf hθr 1 (by rw [pow_one]; simp [f, r])
    rwa [pow_one] at this
  have r2 : θr ≫ θf = 𝟙 _ := by
    have := comp_eq_pow_of_epi gB hθr hθf 1 (by rw [pow_one]; simp [f, r])
    rwa [pow_one] at this
  let θ : (Over.pullback (spMap (algebraMap k L₁))).obj B₁.A ≅ (Over.pullback (spMap (algebraMap k L₁))).obj B₂.A :=
    ⟨θf, θr, r1, r2⟩
  haveI : IsMonHom θ.hom := mθ
  haveI := m₁
  let φP : P₀.A.left ⟶ ((Over.pullback (spMap (algebraMap k L₁))).obj B₁.A).left :=
    e₁.hom.left ≫ bcMap B₁.A.hom L₁.val
  have hφP : IsGrpPullback P₀.A ((Over.pullback (spMap (algebraMap k L₁))).obj B₁.A) (spMap L₁.val.toRingHom) φP :=
    ((isGrpPullback_of_iso e₁).comp gA).congr (Category.id_comp _) rfl
  have hfst : φP ≫ pullback.fst _ _ = c₁ := by
    simp only [φP, Category.assoc, bcMap_fst]; exact he₁
  have hc₂ : φP ≫ θf.left ≫ pullback.fst _ _ = c₂ := by
    simp only [φP, Category.assoc]
    rw [reassoc_of% hθf, bcMap_fst]
    show e₁.hom.left ≫ (e₁.inv ≫ e₂.hom).left ≫ _ = _
    rw [← Category.assoc, ← Over.comp_left, Iso.hom_inv_id_assoc, he₂]
  have HP : LBIso (B₁.L.pull c₁) (B₂.L.pull c₂) :=
    LBIso.trans (pull_isLB B₁.isLB c₁) P₀.isLB (pull_isLB B₂.isLB c₂) hL₁.symm hL₂
  have HX := LBIso.chartPull
    (chartPullOut B₁.L (fun _ => pullback.fst B₁.A.hom (spMap (algebraMap k L₁))) (fun _ => 1) φP (fun _ => c₁)
      (fun _ => hfst.symm))
    (chartPullOut B₂.L (fun _ => θf.left ≫ pullback.fst B₂.A.hom (spMap (algebraMap k L₁))) (fun _ => 1) φP
      (fun _ => c₂) (fun _ => hc₂.symm)) HP
  obtain ⟨s₂, hs₂⟩ := lbIso_descends_to_subfield_containing_finset L₁ K L₁.val.toRingHom
    ((Over.pullback (spMap (algebraMap k L₁))).obj B₁.A) P₀.A φP
    (B₁.L.pull (pullback.fst B₁.A.hom (spMap (algebraMap k L₁))))
    (B₂.L.pull (θf.left ≫ pullback.fst B₂.A.hom (spMap (algebraMap k L₁)))) hφP.1
    (by change QuasiCompact (pullback.snd _ _); infer_instance)
    (by change QuasiSeparated (pullback.snd _ _); infer_instance) (pull_isLB B₁.isLB _) (pull_isLB B₂.isLB _) HX
  refine ⟨sf ∪ sr ∪ s₂, ?_⟩
  intro k₁ _ α β hαβ hs C χ hχ hCL
  let E : IntermediateField k K :=
    { β.fieldRange with algebraMap_mem' := fun r => RingHom.mem_fieldRange.2 ⟨α r, RingHom.congr_fun hαβ r⟩ }
  have hle : L₁ ≤ E := IntermediateField.adjoin_le_iff.2 fun x hx => by
    obtain ⟨y, hy⟩ := hs (Finset.coe_subset.2 Finset.subset_union_left hx)
    exact RingHom.mem_fieldRange.2 ⟨y, hy⟩
  have hran : ∀ x : L₁, ∃ y, β y = x := fun x => RingHom.mem_fieldRange.1 (hle x.2)
  choose ρ₀ hρ₀ using hran
  let α₁ : L₁ →+* k₁ :=
    { toFun := ρ₀
      map_one' := β.injective (by simp [hρ₀])
      map_mul' := fun x y ↦ β.injective (by simp [hρ₀])
      map_zero' := β.injective (by simp [hρ₀])
      map_add' := fun x y ↦ β.injective (by simp [hρ₀]) }
  have hα₁β : β.comp α₁ = L₁.val.toRingHom := RingHom.ext fun x => hρ₀ x
  have hα₁ : α₁.comp (algebraMap k L₁) = α := RingHom.ext fun r => β.injective
    ((hρ₀ _).trans (RingHom.congr_fun hαβ r).symm)
  have hsp : spMap α₁ ≫ spMap (algebraMap k L₁) = spMap α := by rw [spMap_comp', hα₁]
  have hw : χ ≫ B₁.A.hom = (C.A.hom ≫ spMap α₁) ≫ spMap (algebraMap k L₁) := by
    rw [hχ.1.w, Category.assoc, hsp]
  let j : C.A.left ⟶ ((Over.pullback (spMap (algebraMap k L₁))).obj B₁.A).left := pullback.lift χ (C.A.hom ≫ spMap α₁) hw
  have hj₁ : j ≫ pullback.fst _ _ = χ := pullback.lift_fst _ _ _
  have hj₂ : j ≫ pullback.snd _ _ = C.A.hom ≫ spMap α₁ := pullback.lift_snd _ _ _
  have hj : IsGrpPullback C.A ((Over.pullback (spMap (algebraMap k L₁))).obj B₁.A) (spMap α₁) j :=
    (isGrpPullback_pullback B₁.A _).cancel (hχ.congr hsp.symm hj₁.symm) hj₂
  refine ⟨j ≫ θf.left ≫ pullback.fst _ _, ?_, ?_, ?_⟩
  · exact (hj.comp ((isGrpPullback_of_iso θ).comp (isGrpPullback_pullback B₂.A _))).congr
      (by rw [Category.id_comp, hsp]) rfl
  · have H := hs₂ k₁ α₁ β hα₁β ((Finset.coe_subset.2 Finset.subset_union_right).trans hs) C.A j hj.1
    have H' : LBIso (B₁.L.pull χ) (B₂.L.pull (j ≫ θf.left ≫ pullback.fst _ _)) :=
      LBIso.chartPull
        (chartPullSame B₁.L (fun _ => χ) (fun _ => j ≫ pullback.fst _ _) (fun _ => 1) (𝟙 _)
          (fun _ => by rw [Category.id_comp, hj₁]))
        (chartPullSame B₂.L (fun _ => j ≫ θf.left ≫ pullback.fst _ _) (fun _ => j ≫ θf.left ≫ pullback.fst _ _)
          (fun _ => 1) (𝟙 _) (fun _ => by rw [Category.id_comp]))
        (LBIso.chartPull (chartPullIn B₁.L (fun _ => pullback.fst _ _) (fun _ => 1) j)
          (chartPullIn B₂.L (fun _ => θf.left ≫ pullback.fst _ _) (fun _ => 1) j) H)
    exact LBIso.trans C.isLB (pull_isLB B₁.isLB _) (pull_isLB B₂.isLB _) hCL H'
  · intro d hd₁ hd₂
    have hdj : d ≫ j = φP := by
      apply pullback.hom_ext
      · rw [Category.assoc, hj₁, hd₁, hfst]
      · rw [Category.assoc, hj₂, ← Category.assoc, hd₂, Category.assoc, spMap_comp', hα₁β]
        exact hφP.1.w.symm
    rw [reassoc_of% hdj]
    exact hc₂

end GlobalTheory.PolIsoDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianPointLiftsThroughIntermediatePul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolLift

theorem lift_of_pullback_comp : ∀ {S₀ S₁ S₂ : Scheme.{0}} (f₁ : S₁ ⟶ S₀) (f₂ : S₂ ⟶ S₁) (A : PolAV S₀) (B : PolAV S₁) (P : PolAV S₂) (b : B.A.left ⟶ A.A.left) (a : P.A.left ⟶ A.A.left), IsGrpPullback B.A A.A f₁ b → IsGrpPullback P.A A.A (f₂ ≫ f₁) a → ∃ c : P.A.left ⟶ B.A.left, c ≫ b = a ∧ c ≫ B.A.hom = P.A.hom ≫ f₂ ∧ IsGrpPullback P.A B.A f₂ c ∧ (LBIso P.L (A.L.pull a) → LBIso B.L (A.L.pull b) → LBIso P.L (B.L.pull c)) := by
  intro S₀ S₁ S₂ f₁ f₂ A B P b a hB hP
  have w : a ≫ A.A.hom = (P.A.hom ≫ f₂) ≫ f₁ := by
    rw [hP.1.w, Category.assoc]
  refine ⟨hB.1.lift a (P.A.hom ≫ f₂) w, hB.1.lift_fst _ _ w, hB.1.lift_snd _ _ w, ?_, ?_⟩
  · exact IsGrpPullback.cancel hB (hP.congr rfl (hB.1.lift_fst _ _ w).symm) (hB.1.lift_snd _ _ w)
  · intro hPa hBb
    have e : hB.1.lift a (P.A.hom ≫ f₂) w ≫ b = a := hB.1.lift_fst _ _ w
    have h2 : LBIso (B.L.pull (hB.1.lift a (P.A.hom ≫ f₂) w)) (A.L.pull a) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull B.L _ _ rfl)
        (chartPullSame A.L (fun _ => a) (fun _ => b) _ _ fun _ => e.symm) hBb
    exact LBIso.trans P.isLB (pull_isLB A.isLB a) (pull_isLB B.isLB _) hPa h2.symm

end GlobalTheory.PolLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianRelDimEqOfGrpPullbackField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDim

theorem g_eq_of_isGrpPullback : ∀ (K : Type) [Field K] (S : Scheme.{0}) (f : Sp K ⟶ S) (P : PolAV S)
    (P' : PolAV (Sp K)) (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ → P'.g = P.g := by
  intro K _ S f P P' φ h
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := P.g)
  have hd : SmoothOfRelativeDimension P.g P'.A.hom :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension P.g) h.1 P.smoothDim
  obtain ⟨s⟩ : Nonempty (Sp K) := inferInstance
  exact GlobalTheory.PolTest.dim_eq_of_nonempty s P' hd

end GlobalTheory.PolDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelDescendsFiniteTypeSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

namespace GlobalTheory.SiegFG

theorem siegPre_descends_fg : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (R : Type) [CommRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ (R₀ : Subring R) (β₀ : cycAway n →+* R₀) (c₀ : SiegPre g n (zetaAway n) (spMap β₀)), Algebra.FiniteType ℤ R₀ ∧ R₀.subtype.comp β₀ = β ∧ c₀.Principal ∧ SiegPB c c₀ (spMap R₀.subtype) := by
  intro g n hn hodd R _ β c hc
  have hn0 : n ≠ 0 := by omega
  obtain ⟨R₀, β₀, A₀, _, P₀, lv₀, hft, hβ, hsym, hadd, hamp, hpb⟩ := GlobalTheory.SiegFGData.data g n hn hodd R β c hc
  have : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  have hpb' := hpb
  obtain ⟨φ, φ₂, hφ, s₁, s₂, iso, hl⟩ := hpb
  have hpr : IsPrincipal A₀ P₀ :=
    GlobalTheory.PrincSubring.isPrincipal_of_subring g R R₀ c.A c.P A₀ P₀ φ φ₂ hsym hamp hφ ⟨s₁, s₂⟩ iso ((principal_iff c).1 hc)
  let u : (cycAway n)ˣ := Units.ofPowEqOne (zetaAway n) n (zetaAway_pow_self hn0) hn0
  have hζ : u ^ n = 1 := Units.ext (by simp [u])
  have hunit : IsUnit (n : R₀) := by simpa using (isUnit_natCast hn0).map β₀
  have hlevR : IsLevel c.A (lvOf c) := isLevel_lvOf (ζ := u) c
  have hlev₀ : IsLevel A₀ lv₀ :=
    GlobalTheory.LevelDescent.isLevel_of_subring g n R R₀ c.A A₀ φ (lvOf c) lv₀ (by omega) hunit hsym.1 hφ hl hadd hlevR
  have hsympR : IsSymplectic u (spMap β) c.A c.P (lvOf c) :=
    isSymplectic_of_translFixed (ζ := u) hn0 hζ (isUnit_natCast hn0) c (translFixed_of_ample c hc.1)
  have hsymp₀ : IsSymplectic u (spMap β₀) A₀ P₀ lv₀ :=
    GlobalTheory.SympDescent.isSymplectic_of_subring g n (cycAway n) R u R₀ (spMap β₀) c.A c.P (lvOf c) A₀ P₀ lv₀ (by omega) hζ hunit hsym hpr hlev₀
      c.isLB hpb' (by rw [← GlobalTheory.SiegelTypings.spMap_comp, hβ]; exact hsympR)
  let c₀ : SiegPre g n (zetaAway n) (spMap β₀) := ofTriple (ζ := u) hn0 hζ A₀ P₀ lv₀ hsym hlev₀ hsymp₀
  refine ⟨R₀, β₀, c₀, hft, hβ, ?_, (siegPB_iff c c₀ _).2 ?_⟩
  · apply (principal_iff c₀).2
    change IsPrincipal A₀ P₀
    exact hpr
  · change IsPullbackTriple c.A c.P (lvOf c) A₀ P₀ (lvOf (ofTriple (ζ := u) hn0 hζ A₀ P₀ lv₀ hsym hlev₀ hsymp₀)) (spMap R₀.subtype)
    rw [lvOf_ofTriple]
    exact hpb'

end GlobalTheory.SiegFG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdAevalPadicRootsCharpolyEqDet
section
namespace GlobalTheory
open Polynomial

theorem aeval_int_eq_eval₂ {A : Type} [Ring A] [inst : Algebra ℤ A] (x : A) (R : ℤ[X]) :
    @aeval ℤ A _ _ inst x R = eval₂ (Int.castRingHom A) x R := by
  rw [aeval_def]
  congr 1
  exact RingHom.ext_int _ _

theorem prod_aeval_aroots_padic_eq_det : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [IsDomain S] (N : Type) [AddCommGroup N] [Module S N] [Module.Free S N] [Module.Finite S N] (ψ : ℤ_[p] →+* S) (u : N →ₗ[S] N) (P : Polynomial ℤ_[p]) (R : Polynomial ℤ) (d : ℤ_[p]), Function.Injective ψ → P.map ψ = u.charpoly → LinearMap.det (Polynomial.aeval u R) = ψ d → (((P.map (algebraMap ℤ_[p] ℚ_[p])).aroots (PadicAlgCl p)).map (fun a => Polynomial.aeval a R)).prod = algebraMap ℚ_[p] (PadicAlgCl p) (d : ℚ_[p]) := by
  intro p _ S _ _ N _ _ _ _ ψ u P R d hψ hP hd
  let K := FractionRing S
  have hg : Function.Injective ((algebraMap S K).comp ψ) :=
    (IsFractionRing.injective S K).comp hψ
  let ψ' : ℚ_[p] →+* K := IsFractionRing.lift hg
  have hψ' : ψ'.comp (algebraMap ℤ_[p] ℚ_[p]) = (algebraMap S K).comp ψ :=
    IsLocalization.lift_comp _
  let Ω := AlgebraicClosure K
  letI : Algebra ℚ_[p] Ω := ((algebraMap K Ω).comp ψ').toAlgebra
  have hΩ : algebraMap ℚ_[p] Ω = (algebraMap K Ω).comp ψ' := rfl
  let j : PadicAlgCl p →ₐ[ℚ_[p]] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hj : Function.Injective j := j.toRingHom.injective
  let uK : Module.End K (TensorProduct S K N) := u.baseChange K
  have key := GlobalTheory.T.det_aeval_eq_prod_aroots_charpoly' K Ω (TensorProduct S K N) uK (R.map (Int.castRingHom K))
  have hF : ∀ {A : Type} [Ring A] [Algebra K A] (x : A), aeval x (R.map (Int.castRingHom K)) = aeval x R := by
    intro A _ _ x
    rw [← algebraMap_int_eq, aeval_map_algebraMap]
  simp only [hF] at key
  have hbc : aeval uK R = (aeval u R).baseChange K := by
    have := aeval_algHom_apply (Module.End.baseChangeHom S K N).toRingHom.toIntAlgHom u R
    exact this
  rw [hbc, LinearMap.det_baseChange, hd] at key
  have hch : uK.charpoly.aroots Ω = (P.map (algebraMap ℤ_[p] ℚ_[p])).aroots Ω := by
    rw [LinearMap.charpoly_baseChange, ← hP, aroots_def, aroots_def, map_map, map_map, map_map, hΩ]
    simp only [RingHom.comp_assoc, hψ']
  rw [hch] at key
  apply hj
  set Q := P.map (algebraMap ℤ_[p] ℚ_[p])
  have hroots : Q.aroots Ω = (Q.aroots (PadicAlgCl p)).map j := by
    have h := (IsAlgClosed.splits (Q.map (algebraMap ℚ_[p] (PadicAlgCl p)))).roots_map (j : PadicAlgCl p →+* Ω)
    rw [map_map, AlgHom.comp_algebraMap] at h
    rw [aroots_def, aroots_def, h]
    rfl
  rw [hroots, Multiset.map_map] at key
  rw [map_multiset_prod, Multiset.map_map, AlgHom.commutes]
  simp only [aeval_int_eq_eval₂] at key ⊢
  have e1 : ∀ a : PadicAlgCl p, j (eval₂ (Int.castRingHom _) a R) = eval₂ (Int.castRingHom Ω) (j a) R := by
    intro a
    change (j : PadicAlgCl p →+* Ω) (eval₂ (Int.castRingHom _) a R) = _
    rw [Polynomial.hom_eval₂]
    congr 1
    exact RingHom.ext_int _ _
  simp only [Function.comp_def, e1] at key ⊢
  refine key.symm.trans ?_
  rw [hΩ, RingHom.comp_apply]
  congr 1
  exact (RingHom.congr_fun hψ' d).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiCoordinateNormInvariantDegDataPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UnifTorsK.psiNormAt_pull : ∀ (p : ℕ) [Fact p.Prime] (V V' : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'] [Algebra (FractionRing V) (PadicAlgCl p)] [Algebra (FractionRing V') (PadicAlgCl p)] (φ : V →+* V'), (∀ v : V, algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V _ v) = algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ (φ v))) → (∀ v : V', ‖algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ v)‖ ≤ 1) → ∀ (D : DegPre V) (D' : DegPre V') (hD : IsPullDeg φ D D') (χ : D'.X) (r : ℝ), GlobalTheory.UnifTorsK.PsiNormAt p D (hD.xe χ) r ↔ GlobalTheory.UnifTorsK.PsiNormAt p D' χ r := by
  intro p _ V V' _ _ _ _ _ _ _ _ φ hφ hn D D' hD χ r
  have key := _root_.GlobalTheory.ZH.PsiNormPull.norm_psi_pull p V V' φ hφ hn D D' hD χ
  refine ⟨fun H j' hj' => ?_, fun H j hj => ?_⟩
  · obtain ⟨i, hi⟩ := exists_chart D.P.isLB ((D.c (hD.xe χ)).left (IsLocalRing.closedPoint V))
    have hi' := ((IsLocalRing.closedPoint_mem_iff (R := V) ((D.c (hD.xe χ)).left ⁻¹ᵁ D.P.L.U i)).1 hi).ge
    exact (key i (j' PUnit.unit) hi' hj').trans (H (fun _ => i) hi')
  · obtain ⟨i, hi⟩ := exists_chart D'.P.isLB ((D'.c χ).left (IsLocalRing.closedPoint V'))
    have hi' := ((IsLocalRing.closedPoint_mem_iff (R := V') ((D'.c χ).left ⁻¹ᵁ D'.P.L.U i)).1 hi).ge
    exact (key (j PUnit.unit) i hj hi').symm.trans (H (fun _ => i) hi')
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeRigOfOmegaLeRangeRigExtMapVerschiebungStatement
section
open GlobalTheory

theorem _root_.GlobalTheory.T.range_rigOfOmega_le_range_rigExtMap_verschiebung'
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K) :
    LinearMap.range (PDivGroup.frobTwist h G).rigOfOmega ≤
      LinearMap.range (PDivGroup.rigExtMap (PDivGroup.verschiebung h G)) :=
  PDivGroup.range_rigOfOmega_le_range_rigExtMap_verschiebung p K h G
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsSeparateQuotientGenericFibreDescendsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_separate_quotient_generic_fibre_descends : GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [NumberField F] (σ : F →+* ℂ) (X X' W V : Scheme.{0}) [IsIntegral X] [IsIntegral X'] [IsIntegral W] (sX : X ⟶ Sp F) (n : ℕ) [SmoothOfRelativeDimension n sX] (φ : X' ⟶ X) (q : X' ⟶ W) (sW : W ⟶ Sp F) (i : V ⟶ X) (ℓ : V ⟶ X'), IsProjOver sX → GeometricallyConnected sX → 1 ≤ n → IsProjOver (φ ≫ sX) → IsProjOver sW → IsFinite q → Surjective q → q ≫ sW = φ ≫ sX → IsOpenImmersion i → IsOpenImmersion ℓ → ℓ ≫ φ = i → letI := algebraΓOfHom sX; ∀ (K : CanonLB sX n) (δ N' B : LB X) (hδ : δ.IsLB) (hN' : N'.IsLB) (hB : B.IsLB) (N : LB W) (hN : N.IsLB) (m : ℕ), CechPic.pull q (cls N hN) = CechPic.pull φ (cls δ hδ) → IsNef F δ → IsBig F δ → IsNef F N' → (n + 1).choose 2 < m → cls B hB = m • cls δ hδ + cls N' hN' → ∀ (J : Type) [Fintype J] (v : J → (Sp ℂ ⟶ V)), Function.Injective v → (∀ j, v j ≫ i ≫ sX = spMap σ) → (∀ j j', v j ≫ ℓ ≫ q = v j' ≫ ℓ ≫ q) → (∃ j, ∀ s, (v j ≫ i) s = genericPoint X) → ∀ (k : J → (tens K.bundle B).ι) (hk : ∀ j, ⊤ ≤ (v j ≫ i) ⁻¹ᵁ (tens K.bundle B).U (k j)) (a : J → ℂ), (∀ g : H0 sX (tens K.bundle B) ⊤, ∑ j, a j * H0.val (v j ≫ i) (k j) le_top (hk j) g = 0) → a = 0 := by
  first | exact @GlobalTheory.QuotSep.sections_separate_quotient_fibre | exact GlobalTheory.QuotSep.sections_separate_quotient_fibre | (intros; apply GlobalTheory.QuotSep.sections_separate_quotient_fibre <;> assumption)
end

