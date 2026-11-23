module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEPf
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculus
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2245
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SurjectiveCubeOfGeneric
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2246
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSmallSectionsMulLeQuotientPowerTwist
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef

theorem encard_mul_le_at_level_twist : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ, ∀ (N m : ℕ), (P.Bl N (m - c) 1).encard * (P.Bl 0 (b * N - c) 1).encard ≤ {f | f ∈ P.H N (-c) ∧ f * s ^ m ∈ P.Bl N (m - c) 2}.encard * (P.Bl 0 (b * N + m - c) 2).encard := by
  intro k _ X _ p D hD P b s t hG c N m
  have hfin := _root_.GlobalTheory.HSNef.bl_finite k X p D hD P N ((m : ℤ) - c) 1
  have bf := _root_.GlobalTheory.VolBr.Pair.isBallFam k X p P
  have hmul := _root_.GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P
  have hpow := _root_.GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P
  have hreg := _root_.GlobalTheory.VolBr.Pair.div_pow_mem_H_of_mul_pow_sub k X p D hD P b s t hG c N m
  have nu_nn : ∀ (a c : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), 0 ≤ P.nu a c σ y f := by
    intro a c σ y f
    unfold Pair.nu
    exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hsm : s ^ m ≠ 0 := pow_ne_zero m hG.s_ne
  obtain ⟨hsH, hsν⟩ := hpow 0 1 s hG.s_mem.1 m
  obtain ⟨htH, htν⟩ := hpow (-1) b t hG.t_mem.1 N
  have hsν1 : ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu ((m : ℤ) * 0) ((m : ℤ) * 1) σ y (s ^ m) ≤ 1 := by
    intro σ y
    rw [hsν]
    exact pow_le_one₀ (nu_nn _ _ _ _ _) (hG.s_mem.2 σ y)
  have htν1 : ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu ((N : ℤ) * -1) ((N : ℤ) * b) σ y (t ^ N) ≤ 1 := by
    intro σ y
    rw [htν]
    exact pow_le_one₀ (nu_nn _ _ _ _ _) (hG.t_mem.2 σ y)
  let Ts : X.functionField →+ X.functionField := AddMonoidHom.mulRight (s ^ m)
  let Tt : X.functionField →+ X.functionField := AddMonoidHom.mulRight (t ^ N)
  let Λ₀ : AddSubgroup X.functionField := (P.H N (-(c : ℤ))).map Ts
  let Λ₀' : AddSubgroup X.functionField := (P.H 0 ((b : ℤ) * N - c)).map Ts

  have hT : ∀ u ∈ P.Bl N ((m : ℤ) - c) 1, Tt u ∈ P.Bl 0 ((b : ℤ) * N + m - c) 1 := by
    intro u hu
    obtain ⟨hH, hν⟩ := hmul _ _ _ _ u (t ^ N) hu.1 htH
    have e1 : (N : ℤ) + N * -1 = 0 := by ring
    have e2 : ((m : ℤ) - c) + N * b = b * N + m - c := by ring
    rw [e1, e2] at hH hν
    refine ⟨hH, fun σ y => ?_⟩
    show P.nu 0 ((b : ℤ) * N + m - c) σ y (u * t ^ N) ≤ 1
    rw [hν]
    have := mul_le_mul (hu.2 σ y) (htν1 σ y) (nu_nn _ _ _ _ _) zero_le_one
    simpa using this

  have hpull : ∀ u ∈ P.H N ((m : ℤ) - c), Tt u ∈ Λ₀' → u ∈ Λ₀ := by
    intro u hu hmem
    obtain ⟨g, hg, hgu⟩ := AddSubgroup.mem_map.mp hmem
    have hgu' : g * s ^ m = u * t ^ N := hgu
    have hdiv : u * t ^ N / s ^ m ∈ P.H 0 ((b : ℤ) * N - c) := by
      rw [← hgu', mul_div_assoc, div_self hsm, mul_one]; exact hg
    have := hreg u hu hdiv
    refine AddSubgroup.mem_map.mpr ⟨u / s ^ m, this, ?_⟩
    show u / s ^ m * s ^ m = u
    exact div_mul_cancel₀ u hsm
  have key := GlobalTheory.VolBr.encard_mul_le_of_quot_embed X.functionField (P.H N ((m : ℤ) - c))
    (P.H 0 ((b : ℤ) * N + m - c)) Λ₀ Λ₀' (P.Bl N ((m : ℤ) - c)) (P.Bl 0 ((b : ℤ) * N + m - c)) Tt (bf _ _) (bf _ _)
    hT hpull hfin

  have hA : (P.Bl 0 ((b : ℤ) * N - c) 1).encard ≤
      (P.Bl 0 ((b : ℤ) * N + m - c) 1 ∩ (Λ₀' : Set X.functionField)).encard := by
    refine Set.encard_le_encard_of_injOn (f := fun f => f * s ^ m) ?_ ?_
    · intro f hf
      obtain ⟨hH, hν⟩ := hmul _ _ _ _ f (s ^ m) hf.1 hsH
      have e1 : (0 : ℤ) + m * 0 = 0 := by ring
      have e2 : ((b : ℤ) * N - c) + m * 1 = b * N + m - c := by ring
      rw [e1, e2] at hH hν
      refine ⟨⟨hH, fun σ y => ?_⟩, AddSubgroup.mem_map.mpr ⟨f, hf.1, rfl⟩⟩
      rw [hν]
      have := mul_le_mul (hf.2 σ y) (hsν1 σ y) (nu_nn _ _ _ _ _) zero_le_one
      simpa using this
    · intro f _ g _ h
      exact mul_right_cancel₀ hsm h

  have hB : (P.Bl N ((m : ℤ) - c) 2 ∩ (Λ₀ : Set X.functionField)).encard ≤
      {f | f ∈ P.H N (-(c : ℤ)) ∧ f * s ^ m ∈ P.Bl N ((m : ℤ) - c) 2}.encard := by
    refine le_trans (Set.encard_le_encard
      (t := (fun f => f * s ^ m) '' {f | f ∈ P.H N (-(c : ℤ)) ∧ f * s ^ m ∈ P.Bl N ((m : ℤ) - c) 2}) ?_)
      (Set.encard_image_le _ _)
    rintro x ⟨hx, hx0⟩
    obtain ⟨f, hf, rfl⟩ := AddSubgroup.mem_map.mp hx0
    exact ⟨f, ⟨hf, hx⟩, rfl⟩
  calc (P.Bl N ((m : ℤ) - c) 1).encard * (P.Bl 0 ((b : ℤ) * N - c) 1).encard
      ≤ (P.Bl N ((m : ℤ) - c) 1).encard *
          (P.Bl 0 ((b : ℤ) * N + m - c) 1 ∩ (Λ₀' : Set X.functionField)).encard := mul_le_mul' le_rfl hA
    _ ≤ (P.Bl N ((m : ℤ) - c) 2 ∩ (Λ₀ : Set X.functionField)).encard * (P.Bl 0 ((b : ℤ) * N + m - c) 2).encard := key
    _ ≤ {f | f ∈ P.H N (-(c : ℤ)) ∧ f * s ^ m ∈ P.Bl N ((m : ℤ) - c) 2}.encard *
          (P.Bl 0 ((b : ℤ) * N + m - c) 2).encard := mul_le_mul' hB le_rfl

end GlobalTheory.HSNef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndDataOfAdj
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.AdjEnd

section Iso

variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}

theorem wchart_le (j : K' ⊕ K → L.ι) :
    LB.wchart L (Sum.elim φ' φ) j ≤ LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inr) := fun _ hy =>
  ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k), Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)⟩

def isoGen (w : LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε')) :
    LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k))) :=
  ⟨fun j => res (wchart_le j) (w.s (j ∘ Sum.inl, j ∘ Sum.inr))⟩

theorem isoGen_isGen {w : LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε')} (hw : w.IsGen) : (isoGen w).IsGen := by
  intro p q
  refine unit_ext fun y hy => ?_
  have le := fun j : K' ⊕ K → L.ι => (wchart_le (φ := φ) (φ' := φ') j)
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ' (p ∘ Sum.inl) ⊓ LB.wchart L φ (p ∘ Sum.inr) ⊓
      (LB.wchart L φ' (q ∘ Sum.inl) ⊓ LB.wchart L φ (q ∘ Sum.inr)) := ⟨le p hy.1, le q hy.2⟩
  have e := congrArg (gm (𝟙 Y) y (LB.wchart L φ' (p ∘ Sum.inl) ⊓ LB.wchart L φ (p ∘ Sum.inr) ⊓
      (LB.wchart L φ' (q ∘ Sum.inl) ⊓ LB.wchart L φ (q ∘ Sum.inr))))
    (hw (p ∘ Sum.inl, p ∘ Sum.inr) (q ∘ Sum.inl, q ∘ Sum.inr))
  have e' := (gm_res (𝟙 Y) y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div (LB.LinComb L φ ε) (LB.LinComb L φ' ε') (𝟙 Y) y (p ∘ Sum.inl, p ∘ Sum.inr) (q ∘ Sum.inl, q ∘ Sum.inr) hm)
    (gm_res (𝟙 Y) y _ hm _))))
  refine ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le p) hy.1 _)).trans (e'.trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L _ _ (𝟙 Y) y p q hy.1 hy.2).trans ?_)
    ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le q) hy.2 _)))
  refine (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (gm_linComb L φ' ε' (𝟙 Y) y _ _ hm.1.1 hm.2.1).symm ?_)
  refine Eq.trans ?_ (congrArg (·⁻¹) (gm_linComb L φ ε (𝟙 Y) y _ _ hm.1.2 hm.2.2).symm)
  simp only [Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, Function.comp_apply]
  rfl

theorem val_isoGen (w : LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε')) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (isoGen w) r z J = gm r z _ (w.s (fun k => J (r ≫ φ' k), fun k => J (r ≫ φ k))) :=
  gm_res r z _ (hJ.mem _ r) _

end Iso

end GlobalTheory.MumFam.AdjEnd

namespace GlobalTheory.MumFam.AdjEnd

theorem endData_of_adj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), Adj (pol D) (pol D) a a' h h' → EndData D.toPre a a' h h' := by
  intro R _ _ _ _ D a a' h h' H
  obtain ⟨ha, ha', hc, hc', w, hw, hτ⟩ := H
  have hL := D.toPre.P.isLB
  let B := D.toPre.P.A
  let t := isoGen w
  have ht : t.IsGen := isoGen_isGen hw
  let ℓ : (B ⊗ B).left ⟶ (B ⊗ B).left := (lift (1 : B ⊗ B ⟶ B) 1).left
  let v := LB.mulGen _ _ _ _ _ (LB.invGen _ _ _ t) (LB.pullGen _ _ _ t ℓ)
  have hv : v.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ ht) (DVR.pullGen_isGen _ _ _ _ ht _)
  let φ₀ : ULift.{0} (Finset (Fin 2)) → ((B ⊗ B).left ⟶ B.left) := fun I => (psum B ![fst B B ≫ a, snd B B] I.down).left
  let φ₁ : ULift.{0} (Finset (Fin 2)) → ((B ⊗ B).left ⟶ B.left) := fun I => (psum B ![fst B B, snd B B ≫ a'] I.down).left
  let e₂ : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)
  have hF : FormEq (Sum.elim (Sum.elim φ₁ φ₀) (fun k => ℓ ≫ Sum.elim φ₁ φ₀ k))
      (Sum.elim (fun k => - Sum.elim e₂ (fun k => - e₂ k) k) (Sum.elim e₂ (fun k => - e₂ k))) (rosatiφ B a a') rosatiε := by
    intro U _ k
    haveI : IsMonHom a := ha
    haveI : IsMonHom a' := ha'
    have p := prod_ros a a' (fst B B) (snd B B) k
    rw [lift_fst_snd] at p
    rw [(Finset.prod_congr rfl fun i _ => by erw [Over.id_left, Category.id_comp]).trans p]
    have one : ∀ q : B ⊗ B ⟶ B, lift (1 : B ⊗ B ⟶ B) 1 ≫ q = 1 → k (ℓ ≫ q.left) = k (1 : B ⊗ B ⟶ B).left :=
      fun q hq => by rw [← hq]; rfl
    have o1 : lift (1 : B ⊗ B ⟶ B) 1 ≫ fst B B = 1 := lift_fst _ _
    have o2 : lift (1 : B ⊗ B ⟶ B) 1 ≫ snd B B = 1 := lift_snd _ _
    have o3 : lift (1 : B ⊗ B ⟶ B) 1 ≫ fst B B ≫ a = 1 := by rw [← Category.assoc, o1, MonObj.one_comp]
    have o4 : lift (1 : B ⊗ B ⟶ B) 1 ≫ snd B B ≫ a' = 1 := by rw [← Category.assoc, o2, MonObj.one_comp]
    have o5 : lift (1 : B ⊗ B ⟶ B) 1 ≫ (1 : B ⊗ B ⟶ B) = 1 := MonObj.comp_one _
    have o6 : lift (1 : B ⊗ B ⟶ B) 1 ≫ ((fst B B ≫ a) * snd B B) = 1 := by
      rw [MonObj.comp_mul, o3, o2, _root_.mul_one]
    have o7 : lift (1 : B ⊗ B ⟶ B) 1 ≫ (fst B B * (snd B B ≫ a')) = 1 := by
      rw [MonObj.comp_mul, o1, o4, _root_.mul_one]
    have s1 : ∏ I, k (φ₁ I) ^ e₂ I = _ := GlobalTheory.NormRos.prod_square (fst B B) (snd B B ≫ a') k
    have s0 : ∏ I, k (φ₀ I) ^ e₂ I = _ := GlobalTheory.NormRos.prod_square (fst B B ≫ a) (snd B B) k
    have s1' : ∏ I, k (ℓ ≫ φ₁ I) ^ e₂ I = _ := GlobalTheory.NormRos.prod_square (fst B B) (snd B B ≫ a') (fun ψ => k (ℓ ≫ ψ))
    have s0' : ∏ I, k (ℓ ≫ φ₀ I) ^ e₂ I = _ := GlobalTheory.NormRos.prod_square (fst B B ≫ a) (snd B B) (fun ψ => k (ℓ ≫ ψ))
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, neg_neg, zpow_neg, Finset.prod_inv_distrib]
    rw [s1, s0, s1', s0']
    simp only [one _ o1, one _ o2, one _ o3, one _ o4, one _ o5, one _ o6, one _ o7]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  refine ⟨ha, ha', ?_, hc, hc', ?_⟩
  · obtain ⟨u, hu, -⟩ := exists_gen hL hF v hv
    exact fun _ => ⟨⊤, trivial, LB.pullGen _ _ _ u _, DVR.pullGen_isGen _ _ _ _ hu _⟩
  · intro u hu h₀ y y'
    haveI : IsMonHom a := ha
    haveI : IsMonHom a' := ha'
    have o : ∀ {T : Over (Spec (CommRingCat.of R))} (x x' : T ⟶ B), (lift x x').left ≫ ℓ = (lift (1 : T ⟶ B) 1).left :=
      fun x x' => by rw [← Over.comp_left, comp_lift, MonObj.comp_one]
    have hvv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (B ⊗ B).left) (z : Z) (J), Good D.toPre.P.L z J →
        val v r z J = (val t r z J)⁻¹ * val t (r ≫ ℓ) z J := fun Z r z J hJ =>
      (val_mul hJ _ _ r).trans (congrArg₂ (· * ·) (val_inv _ _) (val_pull hJ _ _ _))
    have hn : ∀ (yy : (𝟙_ (Over (Spec (CommRingCat.of R)))).left) (J), Good D.toPre.P.L yy J →
        val v (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B) 1).left yy J = 1 := fun yy J hJ =>
      (hvv _ _ yy J hJ).trans (by erw [o, inv_mul_cancel])
    have eq := DVR.gen_unique₂ GlobalTheory.globalFns_holds D.toPre.P.isAb hL hF hu hv (fun yy J hJ =>
      (DVR.val₂_one h₀ hJ).trans (hn yy J hJ).symm)
    have c0 : D.toPre.c 0 = 1 := mul_eq_left.1 ((D.toPre.c_add 0 0).symm.trans (by rw [add_zero]))
    refine corr_of_val hL fun z J hJ => ?_
    have hp : ∀ a b, val ((pol D).tau a b) (𝟙 _) z J = val (D.toPre.tau a b) (𝟙 _) z J :=
      fun a b => (Wit.exists_tau D.toPre a b).choose_spec.2 _ _ z J hJ
    have h00 : val t (D.toPre.pt2 0 0) z J = 1 := by
      have e := hτ 0 0 z J J hJ hJ
      erw [map_zero h, map_zero h', Data.val_tau_zero (pol D) 0 z J hJ] at e
      refine (val_isoGen w _ z hJ).trans ?_
      exact (_root_.mul_one _).symm.trans e.symm
    have e2 : D.toPre.pt2 y y' ≫ ℓ = D.toPre.pt2 0 0 := by rw [DegPre.pt2, o, DegPre.pt2, c0, MonObj.comp_one]
    have k1 : val v (D.toPre.pt2 y y') z J = (val t (D.toPre.pt2 y y') z J)⁻¹ :=
      (hvv _ _ z J hJ).trans (by erw [e2, h00, _root_.mul_one])
    have k2 : val t (D.toPre.pt2 y y') z J = adjVal w (D.toPre.pt2 y y') z J J := val_isoGen w _ z hJ
    have k4 : val (D.toPre.tau (h y) y') (𝟙 _) z J =
        adjVal w (D.toPre.pt2 y y') z J J * val (D.toPre.tau y (h' y')) (𝟙 _) z J :=
      (hp _ _).symm.trans ((hτ y y' z J J hJ hJ).trans (congrArg _ (hp _ _)))
    rw [val_mul hJ, val_pull hJ, Category.id_comp]
    refine (congrArg (_ * ·) ((eq _ _ z J hJ).trans (k1.trans (congrArg (·⁻¹) k2)))).trans ?_
    rw [k4, mul_comm, inv_mul_cancel_left]

end GlobalTheory.MumFam.AdjEnd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismCharacterActionConjugate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

theorem endChar_act : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (a : 𝓞 E), EndChar P.U (t.act.act a) (DistribSMul.toAddMonoidHom P.D.toPre.X (H.bar a)) := by
  intro E _ _ _ H R _ _ _ _ t P a κ _ ρ hρ G₀ _ φ h f₀ hf
  letI := H.starRing
  obtain ⟨τ, hτ, hi⟩ := P.lin.i_lin 0 a
  have e : τ = GlobalTheory.SplitTorus.torusMap _ (DistribSMul.toAddMonoidHom P.D.toPre.X (H.bar a)) :=
    (GlobalTheory.SplitTorus.eq_torusMap_iff _ _).2 fun x =>
      (GlobalTheory.SplitTorus.res_pullU_charUnit τ x _).symm.trans
        ((congrArg Units.val (hτ x)).trans (GlobalTheory.SplitTorus.charUnit_val _))
  have k := GlobalTheory.TorusPart.isGrpPullback_thickLift hρ h
  have c : f₀.left ≫ GlobalTheory.TorusPart.thickLift hρ h =
      GlobalTheory.TorusPart.thickLift hρ h ≫
        ((Over.pullback (Out.thick R (maximalIdeal R) 0)).map (t.act.act a)).left := by
    apply pullback.hom_ext
    · refine (Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (GlobalTheory.TorusPart.thickLift_fst _ _)).trans (hf.trans ?_))
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine Eq.trans ?_ (congrArg (_ ≫ ·) (GlobalTheory.ExtUnique.pullback_map_left_fst _ _).symm)
      exact (congrArg (· ≫ _) (GlobalTheory.TorusPart.thickLift_fst _ _).symm).trans (Category.assoc _ _ _)
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) k.1.w).trans ?_)
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine Eq.trans ?_ (congrArg (_ ≫ ·)
        (Over.w ((Over.pullback (Out.thick R (maximalIdeal R) 0)).map (t.act.act a))).symm)
      refine Eq.trans ?_ k.1.w.symm
      rw [← Category.assoc, Over.w]
  exact (GlobalTheory.TorusPart.pullTorus_comp k k _ _ c (P.U.gt 0).i).symm.trans
    ((congrArg (GlobalTheory.TorusPart.pullTorus k) (hi.trans (congrArg (· ≫ _) e))).trans
      (GlobalTheory.TorusPart.pullTorus_torusMap_comp k _ _))

end GlobalTheory.UPoinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismMovesTorsionLatticeByAdjoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.EndLattice

open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem congMod_y_of_end : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (E E' : GlobalTheory.UT.EndU U.toUnifPre), LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing R) K] (m : ℕ) (pk pk' : QkPt D.toPre K m) (x : TFK (R := R) K ⟶ A.A), 1 ≤ m → QkToAkU U.toUnifPre K m pk x → QkToAkU U.toUnifPre K m pk' (x ≫ E.aA) → CongMod m pk'.y (E'.h pk.y) := by
  intro R _ _ _ hBase G _ _ hG D A U E E' hE K _ _ _ m pk pk' x hm h1 h2
  haveI : CharZero R := hBase.2
  have hAdm := hBase.1
  obtain ⟨-, hFE⟩ := GlobalTheory.UT.functorial_of_unif R (maximalIdeal R) hAdm D A G hG U
  obtain ⟨-, hK⟩ := hFE E E' hE
  obtain ⟨hex, hiota, hmap⟩ := hK K
  have hcalc := (GlobalTheory.EndCalc.end_calculus GlobalTheory.firstFiveLaws R (maximalIdeal R) hAdm D A G hG U K E E E).2.1
  choose φ hφ using fun g => (hex g).exists
  have hadd : ∀ g g' : GtPtF D.toPre K, φ (g + g') = φ g + φ g' := fun g g' =>
    (isAdd_iff_eq _ _ _).1 (hcalc g g' (g + g') _ _ _ ((isAdd_iff_eq _ _ _).2 rfl) (hφ g) (hφ g') (hφ _))
  let φh : GtPtF D.toPre K →+ GtPtF D.toPre K :=
    AddMonoidHom.mk' φ hadd
  obtain ⟨h, hns, hio⟩ := pk.eq
  have hh : h = m • pk.g := (isNsmul_iff_eq _ _ _).1 hns
  let p' : QkPt D.toPre K m :=
    ⟨E'.h pk.y, φ pk.g, φ h, (isNsmul_iff_eq _ _ _).2 (by rw [hh]; exact map_nsmul φh m pk.g), hiota _ _ _ hio (hφ h)⟩
  have h3 : QkToAkU U.toUnifPre K m p' (x ≫ E.aA) := hmap m hm pk p' x rfl (hφ pk.g) h1
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hAdm D A G hG U K m hm
  have e : f p' = f pk' := ((hf.1 _ _).1 h3).symm.trans ((hf.1 _ _).1 h2)
  obtain ⟨z, hz, -⟩ := (hf.2.2.1 _ _).1 e
  exact ⟨z, hz⟩

end GlobalTheory.EndLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSpecializesSemiAbelianSquareSameProjections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem eq_of_specializes_of_fst_eq_of_snd_eq :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G →
      ∀ x : G.left, G.hom x = closedPoint R → IsClosed ({x} : Set G.left) →
      ∀ p q : (G ⊗ G).left, (fst G G).left p = x → (fst G G).left q = x →
        (snd G G).left p = (snd G G).left q → p ⤳ q → p = q := by
  intro R _ _ G _ hG x hx hxc p q hp hq hpq hs
  haveI : Smooth G.hom := hG.smooth
  have hfin : IsFinite (G.left.fromSpecResidueField x ≫ G.hom) := _root_.GlobalTheory.isFinite_fromSpecResidueField_comp_of_isClosed_of_closedPoint R G inferInstance x hx hxc

  let j : pullback (pullback.fst G.hom G.hom) (G.left.fromSpecResidueField x) ⟶ pullback G.hom G.hom :=
    pullback.fst _ _
  let e := pullbackSymmetry (pullback.fst G.hom G.hom) (G.left.fromSpecResidueField x) ≪≫
    pullbackRightPullbackFstIso G.hom G.hom (G.left.fromSpecResidueField x)
  have hk : j ≫ pullback.snd G.hom G.hom = e.hom ≫ pullback.snd _ _ := by
    simp [e, j, pullbackRightPullbackFstIso_hom_snd]
  have hkf : IsFinite (j ≫ pullback.snd G.hom G.hom) := by rw [hk]; infer_instance
  have hr : Set.range j = (pullback.fst G.hom G.hom) ⁻¹' {x} := by
    simp only [j, Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
  obtain ⟨p', rfl⟩ : p ∈ Set.range j := by rw [hr]; exact hp
  obtain ⟨q', rfl⟩ : q ∈ Set.range j := by rw [hr]; exact hq
  have hs' : p' ⤳ q' := (j.isEmbedding.toIsInducing.specializes_iff).mp hs
  have := (GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite _ _ _ hkf
    ((j ≫ pullback.snd G.hom G.hom) q')).2 p' q' (by simpa using hpq) rfl hs'
  rw [this]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalisationOfEtaleAffineFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_localisation_of_etale_affine_fibre' : ∀ (A C B : CommRingCat.{0}) (φ : A ⟶ C) (ψ : C ⟶ B) (Ω : Type) [Field Ω] (ω : A ⟶ CommRingCat.of Ω) (W : (pullback (Spec.map (φ ≫ ψ)) (Spec.map ω)).Opens) (w : ↥(pullback (Spec.map (φ ≫ ψ)) (Spec.map ω))), w ∈ W → Etale (W.ι ≫ pullback.map (Spec.map (φ ≫ ψ)) (Spec.map ω) (Spec.map φ) (Spec.map ω) (Spec.map ψ) (𝟙 _) (𝟙 _) (by simp [Spec.map_comp]) (by simp)) → letI := φ.hom.toAlgebra; letI := ψ.hom.toAlgebra; letI := (φ ≫ ψ).hom.toAlgebra; letI := ω.hom.toAlgebra; letI : IsScalarTower A C B := IsScalarTower.of_algebraMap_eq (fun _ => rfl); ∃ (Q' : Ideal (TensorProduct A Ω B)) (_ : Q'.IsPrime) (f : TensorProduct A Ω B), Q'.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] TensorProduct A Ω B) = (pullback.fst (Spec.map (φ ≫ ψ)) (Spec.map ω) w).asIdeal ∧ f ∉ Q' ∧ ((algebraMap (TensorProduct A Ω B) (Localization.Away f)).comp (Algebra.TensorProduct.map (AlgHom.id A Ω) (IsScalarTower.toAlgHom A C B)).toRingHom).Etale := by
  first | exact @GlobalTheory.Mum.etale_localisation_of_etale_affine_fibre | exact GlobalTheory.Mum.etale_localisation_of_etale_affine_fibre | (intros; apply GlobalTheory.Mum.etale_localisation_of_etale_affine_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenOnTorusDescendsAlongLocalHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum


set_option maxHeartbeats 4000000 in
theorem evenOn_of_local : ∀ (R W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W), IsLocalHom φ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap φ) β → IsProper (pullback.snd G'.hom (jK W)) → ∀ (P : GlobalTheory.UU.CP G) (P' : GlobalTheory.UU.CP G'), LBIso P'.L.L (P.L.L.pull β) → EvenOn P' → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X], Nonempty (GlobalTheory.UU.TQ (thickObj R (maximalIdeal R) 0 G) X) → EvenOn P := by
  intro R W _ _ _ _ _ _ φ hφ G _ _ hG G' _ _ β hβ hp P P' hL hE X _ _ _ ⟨Q₀⟩
  have hG' := _root_.GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square _ _ _ G G' β hβ hG
  have h3 := GlobalTheory.EvenTriv.surjective_cube_of_generic G' hG' hp
  obtain ⟨w, hw⟩ := _root_.GlobalTheory.PkgBaseChange.exists_isCPMap_of_lbIso _ _ _ G G' β hβ.1.w (GlobalTheory.UU.TowerEx.toBase_mul hβ hβ.1.w) h3 P P' hL
  obtain ⟨X', _, _, _, Q'₀, P'₀, hlev', σ', hσ'⟩ := hE
  obtain ⟨P₀, hlev⟩ := GlobalTheory.UU.exists_isLevelCP (maximalIdeal R) 0 P
  obtain ⟨ρ, β₀, hβ₀, w₀, hw₀⟩ := _root_.GlobalTheory.UU.ClosedFib.exists_isCPMap_closedFibre R W φ hφ G G' β hβ P P' w hw P₀ P'₀ hlev hlev'
  have hk : IsField (R ⧸ maximalIdeal R ^ (0 + 1)) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp (by rw [zero_add, pow_one]; exact IsLocalRing.maximalIdeal.isMaximal R)
  have hk' : IsField (W ⧸ maximalIdeal W ^ (0 + 1)) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp (by rw [zero_add, pow_one]; exact IsLocalRing.maximalIdeal.isMaximal W)
  obtain ⟨i₁, e, he, rfl, hc⟩ := _root_.GlobalTheory.Mum.exists_torus_factor _ _ hk' ρ _ _ β₀ hβ₀ X X' Q₀ Q'₀
  obtain ⟨σ₁, hσ₁⟩ := GlobalTheory.T.exists_even_cubicalTrivialisation_comp_monHom _ _ _ _ P'₀ Q'₀.i e he σ' hσ'
  have := Q₀.i_hom
  have hi₁ : IsMonHom (e ≫ Q'₀.i) := GlobalTheory.UU.TorusCompat.isMonHom hβ₀ hc
  obtain ⟨σ⟩ := @_root_.GlobalTheory.Mum.TorusCubTriv.exists_cubTriv _ _ hk _ _ _ X _ _ _ P₀ Q₀.i Q₀.i_hom
  obtain ⟨χ, hχ⟩ := @GlobalTheory.T.exists_character_symmetricDefect_twice_fieldExt _ _ _ _ hk hk' ρ _ _ _ _ _ _ β₀ hβ₀ P₀ P'₀ w₀ hw₀ X _ _ _ Q₀.i (e ≫ Q'₀.i) Q₀.i_hom hi₁ hc σ σ₁ hσ₁
  exact ⟨X, inferInstance, inferInstance, inferInstance, Q₀, P₀, hlev, _, hχ⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNonzeroLocusFlatLocalBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_nonzeroLocus_flat_local_baseChange : (∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsLocalRing R'] (G' : Over (Sp R')) [GrpObj G'], IsSemiAbelian G' → IsAbelianScheme ((Over.pullback (jK R')).obj G') → ∀ N : LB G'.left, N.IsLB → ∀ a : 𝟙_ (Over (Sp R')) ⟶ G', ∃ t : LB.Gen (LB.LinComb N (K := Fin 3) ![(𝟙 G' * (toUnit G' ≫ a)).left, (𝟙 G' * (toUnit G' ≫ a⁻¹)).left, 𝟙 G'.left] ![1, 1, -2]), t.IsGen) → ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ (M₀ : LB G.left), M₀.IsLB → ∀ s₀ : M₀.Sec, IsAffineOpen (nonzeroLocus s₀) → (∃ y₀ ∈ nonzeroLocus s₀, G.hom y₀ = closedPoint R) → ∀ y : G.left, ∃ (R' : Type) (_ : CommRing R') (ρ : R →+* R'), ρ.Flat ∧ ∃ x' : ↥(pullback G.hom (spMap ρ)), pullback.fst G.hom (spMap ρ) x' = y ∧ ∃ n, 1 ≤ n ∧ ∃ s : (lbPow (M₀.pull (pullback.fst G.hom (spMap ρ))) n).Sec, x' ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s) := by
  first | exact @GlobalTheory.AmplePt.exists_affine_nonzeroLocus_of_square | exact GlobalTheory.AmplePt.exists_affine_nonzeroLocus_of_square | (intros; apply GlobalTheory.AmplePt.exists_affine_nonzeroLocus_of_square <;> assumption)
end

