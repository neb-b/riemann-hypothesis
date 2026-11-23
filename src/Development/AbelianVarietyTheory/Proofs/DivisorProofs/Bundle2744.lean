module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2701
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1140
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2061
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2718
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0095
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2735
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2731
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2719
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2717
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2155
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2136
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldBasisOfSections
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.FBasis

theorem exists_ne_zero_mem_H (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsArithVar p D) (P : Pair p) (hL : IsAmpleLB P.L.B) (e : ℕ) (he : 0 < e) (a b : ℤ) :
    ∃ (c : ℕ) (γ : X.functionField), γ ≠ 0 ∧ γ ∈ P.H ((e : ℤ) * c + a) b := by
  obtain ⟨M, hM⟩ := Pair.exists_rep k X p P a b
  have hLe : IsAmpleLB (P.L.pow e).B := (isAmpleLB_pow_iff hL.isLB he).2 hL
  obtain ⟨c, -, u, hu⟩ := exists_sec_finite_subset_nonzeroLocus k X p D hX M (P.L.pow e) hLe {genericPoint X}
    (Set.finite_singleton _)
  have h1 := (Pair.rep_base k X p P).1
  have h2 := Pair.rep_pow k X p P 1 0 P.L e h1
  have h3 := Pair.rep_pow k X p P _ _ _ c h2
  have hN := Pair.rep_tens k X p P a b _ _ M _ hM h3
  have e1 : a + (c : ℤ) * ((e : ℤ) * 1) = (e : ℤ) * c + a := by ring
  have e2 : b + (c : ℤ) * ((e : ℤ) * 0) = b := by ring
  rw [e1, e2] at hN
  obtain ⟨f, -, hrange, -, hloc⟩ := RepDict.rep_dict k X p P _ _ _ hN
  have hmem : f u ∈ P.H ((e : ℤ) * c + a) b := by
    have : f u ∈ Set.range f := Set.mem_range_self u
    rw [hrange] at this
    exact this
  obtain ⟨i, hi⟩ : ∃ i, genericPoint X ∈ P.L.B.U i :=
    Opens.mem_iSup.1 (P.L.isLB.cover.ge (Opens.mem_top _))
  obtain ⟨j, hj⟩ : ∃ j, genericPoint X ∈ P.A.B.U j :=
    Opens.mem_iSup.1 (P.A.isLB.cover.ge (Opens.mem_top _))
  have hU := (hloc u (genericPoint X) i j hi hj).1 (hu rfl)
  refine ⟨c, f u, fun h0 => ?_, hmem⟩
  rw [h0] at hU
  have z : P.loc ((e : ℤ) * c + a) b 0 i j = 0 := by simp [Pair.loc]
  rw [z] at hU
  have hz : ∀ x : X, ¬ UnitAt x (0 : X.functionField) := by
    rintro x ⟨w, hw, h⟩
    exact (hw.map (algebraMap _ X.functionField)).ne_zero h
  exact hz _ hU

theorem exists_linearIndependent_of_frac {K : Type} [Field K] (F : Subfield K) [FiniteDimensional F K] (R : Subring K)
    (hR : ∀ w : K, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ w = a / b) :
    ∃ β : Fin (Module.finrank F K) → K, (∀ i, β i ∈ R) ∧ LinearIndependent F β := by
  have hS : Algebra.adjoin F (R : Set K) = ⊤ := by
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨a, ha, b, hb, hb0, rfl⟩ := hR w
    have hbS : b ∈ Algebra.adjoin F (R : Set K) := Algebra.subset_adjoin hb
    have hinv : b⁻¹ ∈ Algebra.adjoin F (R : Set K) :=
      (Algebra.adjoin F (R : Set K)).inv_mem_of_algebraic (x := ⟨b, hbS⟩) (Algebra.IsAlgebraic.isAlgebraic (b : K))
    rw [div_eq_mul_inv]
    exact mul_mem (Algebra.subset_adjoin ha) hinv
  have hspan : Submodule.span F (R : Set K) = ⊤ := by
    have := congrArg Subalgebra.toSubmodule hS
    rw [Algebra.adjoin_eq_span, Algebra.top_toSubmodule] at this
    have hc : (Submonoid.closure (R : Set K) : Set K) = (R : Set K) := by
      exact congrArg (fun s : Submonoid K => (s : Set K)) (Submonoid.closure_eq R.toSubmonoid)
    rw [hc] at this
    exact this
  obtain ⟨s, hsR, hsspan, hli⟩ := exists_linearIndependent F (R : Set K)
  rw [hspan] at hsspan
  let B : Module.Basis s F K := Module.Basis.mk hli (by rw [Subtype.range_coe, hsspan])
  let E : s ≃ Fin (Module.finrank F K) := B.indexEquiv (Module.finBasis F K)
  refine ⟨fun i => (E.symm i : K), fun i => hsR (E.symm i).2, ?_⟩
  exact hli.comp _ E.symm.injective

end GlobalTheory.HSAmp.FBasis

namespace GlobalTheory.HSAmp

theorem exists_linearIndependent_mem_H : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField),
    Gens P D e x → ∀ a b : ℤ, ∃ (c : ℕ) (g : Fin (Module.finrank (ratF x) X.functionField) → X.functionField),
    (∀ i, g i ∈ P.H (e * c + a) b) ∧ LinearIndependent (ratF x) g := by
  intro k _ X _ p D hX P hL e x hx a b
  obtain ⟨hne, -, hfin⟩ := _root_.GlobalTheory.HSAmp.gens_quot_trBasis k X p D hX P hL e x hx
  obtain ⟨U, hU, hUe, -, hreg, -, hfrac, -⟩ :=
    _root_.GlobalTheory.AffModel.main k X p D hX P hL e (x 0) hx.pos (hx.mem 0) (hne 0)
  obtain ⟨β, hβR, hβ⟩ := FBasis.exists_linearIndependent_of_frac (ratF x) (fnOf U hU).range hfrac
  obtain ⟨c₁, γ, hγ0, hγ⟩ := FBasis.exists_ne_zero_mem_H k X p D hX P hL e hx.pos a b
  have hext : ∀ i, ∀ᶠ c : ℕ in atTop, x 0 ^ c * β i ∈ P.H ((e : ℤ) * c + 0) 0 := by
    intro i
    refine _root_.GlobalTheory.HSAmp.eventually_pow_mul_mem_H k X p D hX P e 0 0 (x 0) (β i) (hx.mem 0) (hne 0) fun z hz i' j _ _ => ?_
    have e0 : P.loc 0 0 (β i) i' j = β i := by simp [Pair.loc]
    rw [e0]
    refine (hreg (β i)).2 (hβR i) z ?_
    rw [← SetLike.mem_coe, hUe]
    exact hz
  obtain ⟨c₂, hc₂⟩ := (Filter.eventually_all.2 hext).exists
  refine ⟨c₁ + c₂, fun i => γ * x 0 ^ c₂ * β i, fun i => ?_, ?_⟩
  · have h := (NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ γ (x 0 ^ c₂ * β i) hγ (hc₂ i)).1
    have e1 : (e : ℤ) * c₁ + a + ((e : ℤ) * c₂ + 0) = (e : ℤ) * ((c₁ + c₂ : ℕ) : ℤ) + a := by
      push_cast; ring
    rw [e1, add_zero, ← mul_assoc] at h
    exact h
  · have ht : γ * x 0 ^ c₂ ≠ 0 := mul_ne_zero hγ0 (pow_ne_zero _ (hne 0))
    exact hβ.map' (LinearMap.mulLeft (ratF x) (γ * x 0 ^ c₂))
      (LinearMap.ker_eq_bot.2 (mul_right_injective₀ ht))

end GlobalTheory.HSAmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianLiftLieSquareZeroHarrisTaylorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lagrangian_lift_lie_squareZero_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (I : Ideal C), I ^ 2 = ⊥ → ∀ (tR : R →+* C) (H : Type 1) [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H] (ρ : D.O →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf (ρ.comp (algebraMap (𝓞 D.F) D.O)); Module.Projective (C ⊗[ℤ] 𝓞 D.F) H) → ∀ (φ : LinearMap.BilinForm C H), (∀ x y, φ x y = -φ y x) → Function.Bijective φ → (∀ (c : D.O) x y, φ (ρ c x) y = φ x (ρ (D.star c).unop y)) → ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ (c : D.O), ∀ x ∈ F, ρ c x ∈ F) → (∀ x ∈ F, ∀ y ∈ F, φ x y ∈ I) → (∀ x, (∀ y ∈ F, φ x y ∈ I) → x ∈ F) → (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) → (∀ d, ρ (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d ∈ F → ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧ d - ∑ i, w i ∈ F) → ∃ E : Submodule C H, (∃ M : Submodule C H, IsCompl E M) ∧ E ⊔ I • ⊤ = F ∧ (∀ (c : D.O), ∀ x ∈ E, ρ c x ∈ E) ∧ (∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ ∀ d, ρ (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d ∈ E → ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ E) ∧ d - ∑ i, w i ∈ E := by
  first | exact @GlobalTheory.HTSummand.exists_lagrangian_lift_lie | exact GlobalTheory.HTSummand.exists_lagrangian_lift_lie | (intros; apply GlobalTheory.HTSummand.exists_lagrangian_lift_lie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeIsoOfTwoPadicAlgClUniformisations
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnifTorsK

theorem spComp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem bc {S S' : Scheme.{0}} (f : S' ⟶ S) (P : PolAV S) : ∃ (P' : PolAV S') (φ : P'.A.left ⟶ P.A.left),
    P'.g = P.g ∧ IsGrpPullback P'.A P.A f φ ∧ LBIso P'.L (P.L.pull φ) := by
  refine ⟨GlobalTheory.AmpleSpecialisation.baseChange P f, pullback.fst P.A.hom f, rfl, isGrpPullback_pullback P.A f, ?_⟩
  obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (pull_isLB P.isLB (pullback.fst P.A.hom f))
  exact ⟨w, hw⟩

theorem lbcomp {X Y Y' : Scheme.{0}} {L : LB X} {L' : LB Y} {L'' : LB Y'} (hL : L.IsLB) (hL' : L'.IsLB)
    (hL'' : L''.IsLB) {φ : Y ⟶ X} {ψ : Y' ⟶ Y} (h : LBIso L' (L.pull φ)) (h' : LBIso L'' (L'.pull ψ)) :
    LBIso L'' (L.pull (ψ ≫ φ)) := by
  have h₁ : LBIso (L'.pull ψ) ((L.pull φ).pull ψ) := GlobalTheory.RigidBundleGlue.LBIso.pull h ψ
  have h₂ : LBIso ((L.pull φ).pull ψ) (L.pull (ψ ≫ φ)) := GlobalTheory.OriginCohom.lbIso_pull_pull_comp hL φ ψ
  have h₃ : LBIso (L'.pull ψ) (L.pull (ψ ≫ φ)) :=
    LBIso.trans (pull_isLB hL' ψ) (pull_isLB (pull_isLB hL φ) ψ) (pull_isLB hL (ψ ≫ φ)) h₁ h₂
  exact LBIso.trans hL'' (pull_isLB hL' ψ) (pull_isLB hL (ψ ≫ φ)) h' h₃

theorem unit_norm (p : ℕ) [Fact p.Prime] (W : Type) [CommRing W] [IsDomain W] [Algebra (FractionRing W) (PadicAlgCl p)]
    (hn : ∀ x : FractionRing W, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W)))
    {r r' : W} (h : Associated r r') :
    ‖algebraMap (FractionRing W) (PadicAlgCl p) (algebraMap W _ r)‖ =
      ‖algebraMap (FractionRing W) (PadicAlgCl p) (algebraMap W _ r')‖ := by
  obtain ⟨u, rfl⟩ := h
  set emb : W →+* PadicAlgCl p := (algebraMap (FractionRing W) (PadicAlgCl p)).comp (algebraMap W (FractionRing W))
    with hemb
  have hle : ∀ v : W, ‖emb v‖ ≤ 1 := fun v => (hn _).2 ⟨v, rfl⟩
  have hprod : ‖emb (u : W)‖ * ‖emb ((u⁻¹ : Wˣ) : W)‖ = 1 := by
    rw [← norm_mul, ← map_mul, Units.mul_inv, _root_.map_one, norm_one]
  have hu : ‖emb (u : W)‖ = 1 :=
    le_antisymm (hle _) (by nlinarith [norm_nonneg (emb (u : W)), norm_nonneg (emb ((u⁻¹ : Wˣ) : W)), hle ((u⁻¹ : Wˣ) : W)])
  have e₁ : ∀ v : W, algebraMap (FractionRing W) (PadicAlgCl p) (algebraMap W _ v) = emb v := fun _ => rfl
  rw [e₁, e₁, map_mul, norm_mul, hu, _root_.mul_one]


set_option maxHeartbeats 1600000 in
theorem main : ∀ {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω'] (S : ThetaSys o Ω) (S' : ThetaSys o' Ω') (ρ : S.Real) (ρ' : S'.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (y₁ : S'.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (u' : ρ'.UTest p y₁) (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u'.A.A.left), IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a → IsGrpPullback P₀.A u'.A.A (spMap (algebraMap (FractionRing u'.V) (PadicAlgCl p))) a' → LBIso P₀.L (u.A.L.pull a) → LBIso P₀.L (u'.A.L.pull a') → ∃ e : u.D.toPre.X ≃+ u'.D.toPre.X, (∀ χ r, u.PsiNorm χ r ↔ u'.PsiNorm (e χ) r) ∧ ∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) (pk' : QkPt u'.D.toPre (PadicAlgCl p) m) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A) (w : Sp (PadicAlgCl p) ⟶ P₀.A.left), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk' x' → w ≫ P₀.A.hom = 𝟙 _ → w ≫ a = x.left → w ≫ a' = x'.left → CongMod m pk'.y (e pk.y) := by
  intro o Ω o' Ω' _ _ _ _ _ _ S S' ρ ρ' p _ y₀ y₁ u u' P₀ a a' ha ha' hLa hLa'

  obtain ⟨W₀, _, _, _, _, hW₀c, hW₀n, -, hW₀alg, ⟨φ₀, φK₀, hφK₀, hmax₀, hcp₀⟩,
      ⟨φ₀', φK₀', hφK₀', hmax₀', hcp₀'⟩⟩ :=
    _root_.GlobalTheory.UnifField.exists_common_ring p u.V u'.V u.complete u'.complete u.norm_le u'.norm_le ∅

  obtain ⟨B₁, b₁, -, hb₁, hLb₁⟩ := bc (spMap φK₀) u.A
  obtain ⟨B₂, b₂, -, hb₂, hLb₂⟩ := bc (spMap φK₀') u'.A
  have hpa : IsGrpPullback P₀.A u.A.A
      (spMap (algebraMap (FractionRing W₀) (PadicAlgCl p)) ≫ spMap φK₀) a :=
    ha.congr (by rw [spComp, hcp₀]) rfl
  have hpa' : IsGrpPullback P₀.A u'.A.A
      (spMap (algebraMap (FractionRing W₀) (PadicAlgCl p)) ≫ spMap φK₀') a' :=
    ha'.congr (by rw [spComp, hcp₀']) rfl
  obtain ⟨c₁, hc₁b, hc₁h, hc₁, hc₁L⟩ := _root_.GlobalTheory.PolLift.lift_of_pullback_comp (spMap φK₀)
    (spMap (algebraMap (FractionRing W₀) (PadicAlgCl p))) u.A B₁ P₀ b₁ a hb₁ hpa
  obtain ⟨c₂, hc₂b, hc₂h, hc₂, hc₂L⟩ := _root_.GlobalTheory.PolLift.lift_of_pullback_comp (spMap φK₀')
    (spMap (algebraMap (FractionRing W₀) (PadicAlgCl p))) u'.A B₂ P₀ b₂ a' hb₂ hpa'
  have hLc₁ := hc₁L hLa hLb₁
  have hLc₂ := hc₂L hLa' hLb₂

  obtain ⟨s, hs⟩ := _root_.GlobalTheory.PolIsoDescent.model_descends (FractionRing W₀) (PadicAlgCl p) (algebraMap _ _) hW₀alg B₁ B₂ P₀ c₁ c₂
    hc₁ hc₂ hLc₁ hLc₂

  obtain ⟨W, _, _, _, _, hWc, hWn, hsW, -, ⟨α₀, αK, hαK, hαmax, hαcp⟩, -⟩ :=
    _root_.GlobalTheory.UnifField.exists_common_ring p W₀ W₀ hW₀c hW₀c hW₀n hW₀n s
  have hcomm : (αK.comp φK₀).comp (algebraMap u.V (FractionRing u.V)) =
      (algebraMap W (FractionRing W)).comp (α₀.comp φ₀) := by
    ext v
    have h1 := RingHom.congr_fun hφK₀ v
    have h2 := RingHom.congr_fun hαK (φ₀ v)
    simp only [RingHom.comp_apply] at h1 h2 ⊢
    rw [h1, h2]
  have hcomm' : (αK.comp φK₀').comp (algebraMap u'.V (FractionRing u'.V)) =
      (algebraMap W (FractionRing W)).comp (α₀.comp φ₀') := by
    ext v
    have h1 := RingHom.congr_fun hφK₀' v
    have h2 := RingHom.congr_fun hαK (φ₀' v)
    simp only [RingHom.comp_apply] at h1 h2 ⊢
    rw [h1, h2]
  have hmax : (IsLocalRing.maximalIdeal u.V).map (α₀.comp φ₀) ≤ IsLocalRing.maximalIdeal W := by
    rw [← Ideal.map_map]
    exact (Ideal.map_mono hmax₀).trans hαmax
  have hmax' : (IsLocalRing.maximalIdeal u'.V).map (α₀.comp φ₀') ≤ IsLocalRing.maximalIdeal W := by
    rw [← Ideal.map_map]
    exact (Ideal.map_mono hmax₀').trans hαmax
  have hF : (algebraMap (FractionRing W) (PadicAlgCl p)).comp (αK.comp φK₀) =
      algebraMap (FractionRing u.V) (PadicAlgCl p) := by
    rw [← RingHom.comp_assoc, hαcp, hcp₀]
  have hF' : (algebraMap (FractionRing W) (PadicAlgCl p)).comp (αK.comp φK₀') =
      algebraMap (FractionRing u'.V) (PadicAlgCl p) := by
    rw [← RingHom.comp_assoc, hαcp, hcp₀']

  obtain ⟨C, ψ₁, hgC, hψ₁, hLψ₁⟩ := bc (spMap (αK.comp φK₀)) u.A
  have hψ₁' : IsGrpPullback C.A u.A.A (spMap αK ≫ spMap φK₀) ψ₁ := hψ₁.congr (spComp _ _).symm rfl
  obtain ⟨χ, hχb, -, hχ, hχL⟩ := _root_.GlobalTheory.PolLift.lift_of_pullback_comp (spMap φK₀) (spMap αK) u.A B₁ C b₁ ψ₁ hb₁ hψ₁'
  have hLχ := hχL hLψ₁ hLb₁
  obtain ⟨χ₂, hχ₂, hLχ₂, hd⟩ :=
    hs (FractionRing W) αK (algebraMap (FractionRing W) (PadicAlgCl p)) hαcp hsW C χ hχ hLχ
  have hψ₂ : IsGrpPullback C.A u'.A.A (spMap (αK.comp φK₀')) (χ₂ ≫ b₂) :=
    (hχ₂.comp hb₂).congr (spComp _ _) rfl
  have hLψ₂ : LBIso C.L (u'.A.L.pull (χ₂ ≫ b₂)) := lbcomp u'.A.isLB B₂.isLB C.isLB hLb₂ hLχ₂
  have hgC' : C.g = u'.A.g := _root_.GlobalTheory.PolDim.g_eq_of_isGrpPullback (FractionRing W) _ (spMap (αK.comp φK₀')) u'.A C (χ₂ ≫ b₂) hψ₂

  obtain ⟨D₁, hD₁, G₁, _, _, U₁, hG₁, htor₁⟩ :=
    GlobalTheory.T.uniformisation_moves_along_dvr_injection_given_fibre u.V W u.complete hWc (α₀.comp φ₀) (αK.comp φK₀) hcomm hmax u.D u.A u.G u.U C ψ₁ hψ₁ hLψ₁
      hgC (PadicAlgCl p) hF
  obtain ⟨D₂, hD₂, G₂, _, _, U₂, hG₂, htor₂⟩ :=
    GlobalTheory.T.uniformisation_moves_along_dvr_injection_given_fibre u'.V W u'.complete hWc (α₀.comp φ₀') (αK.comp φK₀') hcomm' hmax' u'.D u'.A u'.G u'.U C
      (χ₂ ≫ b₂) hψ₂ hLψ₂ hgC' (PadicAlgCl p) hF'
  haveI : CharZero (PadicAlgCl p) :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[p] (PadicAlgCl p)).injective
  haveI : CharZero W :=
    RingHom.charZero ((algebraMap (FractionRing W) (PadicAlgCl p)).comp (algebraMap W (FractionRing W)))

  obtain ⟨ε, hεψ, hεt⟩ := GlobalTheory.TwoUnifTors.main W hWc C G₁ G₂ hG₁ hG₂ D₁ D₂ U₁ U₂
  have hv₁ : ∀ v : u.V, algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ v) =
      algebraMap (FractionRing W) (PadicAlgCl p) (algebraMap W _ ((α₀.comp φ₀) v)) := by
    intro v
    have h1 := RingHom.congr_fun hcomm v
    have h2 := RingHom.congr_fun hF (algebraMap u.V (FractionRing u.V) v)
    simp only [RingHom.comp_apply] at h1 h2 ⊢
    rw [← h2, h1]
  have hv₂ : ∀ v : u'.V, algebraMap (FractionRing u'.V) (PadicAlgCl p) (algebraMap u'.V _ v) =
      algebraMap (FractionRing W) (PadicAlgCl p) (algebraMap W _ ((α₀.comp φ₀') v)) := by
    intro v
    have h1 := RingHom.congr_fun hcomm' v
    have h2 := RingHom.congr_fun hF' (algebraMap u'.V (FractionRing u'.V) v)
    simp only [RingHom.comp_apply] at h1 h2 ⊢
    rw [← h2, h1]
  have hW1 : ∀ v : W, ‖algebraMap (FractionRing W) (PadicAlgCl p) (algebraMap W _ v)‖ ≤ 1 :=
    fun v => (hWn _).2 ⟨v, rfl⟩
  refine ⟨hD₁.xe.symm.trans (ε.trans hD₂.xe), ?_, ?_⟩
  · intro χ r
    obtain ⟨y, rfl⟩ := hD₁.xe.surjective χ
    rw [psiNorm_iff, psiNorm_iff]
    have e1 := _root_.GlobalTheory.UnifTorsK.psiNormAt_pull p u.V W (α₀.comp φ₀) hv₁ hW1 u.D.toPre D₁.toPre hD₁ y r
    have e2 := _root_.GlobalTheory.UnifTorsK.psiNormAt_pull p u'.V W (α₀.comp φ₀') hv₂ hW1 u'.D.toPre D₂.toPre hD₂ (ε y) r
    obtain ⟨⟨r₁, hr₁⟩, n₁⟩ := _root_.GlobalTheory.PsiNormCoord.main p W hWn D₁ y
    obtain ⟨⟨r₂, hr₂⟩, n₂⟩ := _root_.GlobalTheory.PsiNormCoord.main p W hWn D₂ (ε y)
    have e3 : PsiNormAt p D₁.toPre y r ↔ PsiNormAt p D₂.toPre (ε y) r := by
      rw [n₁ r₁ hr₁ r, n₂ r₂ hr₂ r, unit_norm p W hWn (hεψ y r₁ r₂ hr₁ hr₂)]
    simp only [AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
    exact e1.trans (e3.trans e2.symm)
  · intro m pk pk' x x' w hm hx hx' hw hwx hwx'
    obtain ⟨q₁, x₁, hq₁, hx₁ψ, hx₁⟩ := htor₁ m hm pk x hx
    obtain ⟨q₂, x₂, hq₂, hx₂ψ, hx₂⟩ := htor₂ m hm pk' x' hx'

    have hsq : c₁ ≫ B₁.A.hom =
        (P₀.A.hom ≫ spMap (algebraMap (FractionRing W) (PadicAlgCl p))) ≫ spMap αK := by
      rw [hc₁h, Category.assoc, spComp, hαcp]
    obtain ⟨d, hdχ, hdh⟩ : ∃ d : P₀.A.left ⟶ C.A.left, d ≫ χ = c₁ ∧
        d ≫ C.A.hom = P₀.A.hom ≫ spMap (algebraMap (FractionRing W) (PadicAlgCl p)) :=
      ⟨hχ.1.lift _ _ hsq, hχ.1.lift_fst _ _ _, hχ.1.lift_snd _ _ _⟩
    have hdχ₂ : d ≫ χ₂ = c₂ := hd d hdχ hdh
    have hT : (TFK (R := W) (PadicAlgCl p)).hom = spMap (algebraMap (FractionRing W) (PadicAlgCl p)) := rfl
    have hbase : (w ≫ d) ≫ C.A.hom = (TFK (R := W) (PadicAlgCl p)).hom := by
      rw [Category.assoc, hdh, ← Category.assoc, hw, Category.id_comp, hT]
    have k₁ : x₁.left = w ≫ d := by
      apply hψ₁.1.hom_ext
      · rw [hx₁ψ, ← hχb, Category.assoc, reassoc_of% hdχ, hc₁b, hwx]
      · rw [Over.w x₁, hbase]
    have k₂ : x₂.left = w ≫ d := by
      apply hψ₂.1.hom_ext
      · rw [hx₂ψ, Category.assoc, reassoc_of% hdχ₂, hc₂b, hwx']
      · rw [Over.w x₂, hbase]
    have hxx : x₂ = x₁ := Over.OverMorphism.ext (k₂.trans k₁.symm)
    rw [hxx] at hx₂
    have hc := hεt (PadicAlgCl p) m q₁ q₂ x₁ hm hx₁ hx₂
    unfold CongMod at hc ⊢
    obtain ⟨z, hz⟩ := hc
    refine ⟨hD₂.xe z, ?_⟩
    rw [← hq₂, hz, map_add (f := _), map_nsmul, ← hq₁]
    simp

end GlobalTheory.UnifTorsK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearRingActionGenericFibreOfActsAs
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_oAct_oLinear_of_actsAs : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oG : RingAct G O), (∀ a, ActsAs U.toUnifPre (o.onB.act a) (fun χ => star a • χ) (oG.act a)) → ∃ oA : A.OAct O, U.toUnifPre.OLinear O o oA oG := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o oG hgA
  have hgen : IsMonHom U.gen.hom := U.gen_hom
  have hgeni : IsMonHom U.gen.inv := by infer_instance
  have hg := oG.hom
  have one := oG.map_one
  have mul := oG.map_mul
  have add := oG.map_add
  let F := Over.pullback (jK R)
  let fA : O → (A.A ⟶ A.A) := fun a => U.gen.inv ≫ F.map (oG.act a) ≫ U.gen.hom
  let oA : A.OAct O :=
    { act := fA
      hom := fun a => by haveI := hg a; dsimp [fA]; infer_instance
      map_one := by simp [fA, F, one]
      map_mul := fun a b => by simp [fA, F, mul]
      map_add := fun a b => by
        haveI := hg a; haveI := hg b
        simp only [fA, F, add, pull_padd]
        rw [padd_comp_hom, padd, padd, comp_lift_assoc]
      rosati := fun a => GlobalTheory.Mum.RosGeneric.rosatiAdj_generic_of_actsAs R hR D A G hG U O o a (oG.act a)
        (oG.act (star a)) (hg a) (hg (star a)) (hgA a) (hgA (star a)) }
  refine ⟨oA, ⟨fun a => ?_, fun e a => (hgA a e).1, fun e a => (hgA a e).2⟩⟩
  simp [oA, fA, F]
end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocallyClosedUniversalHomMatrixSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_locallyClosed_universal_hom_matrix_scheme : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∃ (X : Scheme.{0}) (cE : X ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (H : Scheme.{0}) (i : H ⟶ X) (AH : Over H) (_ : GrpObj AH) (BH : Over H) (_ : GrpObj BH) (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left) (Φ : AH ⟶ BH), IsClosedImmersion cE ∧ IsOpenImmersion i ∧ IsTest A B L M (i ≫ cE ≫ affπ Rg (mA * mB)) AH BH φA φB Φ ∧ (∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), IsTest A B L M t A' B' φA' φB' Φ' → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → ∃ h : Sp R ⟶ H, h ≫ i ≫ cE ≫ affπ Rg (mA * mB) = t ∧ matOf (h ≫ i ≫ cE) = c) ∧ ∀ (R : Type) [CommRing R] (h : Sp R ⟶ H) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsTest A B L M (h ≫ i ≫ cE ≫ affπ Rg (mA * mB)) A' B' φA' φB' Φ' → IsPullD φA φB Φ φA' φB' Φ' h → IsMat L M k bA bB eA eB (h ≫ i ≫ cE ≫ affπ Rg (mA * mB)) A' B' φA' φB' Φ' (matOf (h ≫ i ≫ cE)) := by
  first | (exact @GlobalTheory.HomFixUniv.exists_universal_matrix) | (exact GlobalTheory.HomFixUniv.exists_universal_matrix) | (intros; apply GlobalTheory.HomFixUniv.exists_universal_matrix  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordUniformisationUnitaryTypeTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mumfordUniformisation_unitaryTypeTrait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (D : DegData R (maximalIdeal R)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), Nontrivial D.toPre.X → PelOK Dm D.toPre o → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (G : Over (Sp R₁)) (_ : GrpObj G) (_ : IsCommMonObj G) (A : PolAV (Sp (FractionRing R₁))), GlobalTheory.LN.CDvr R₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ IsSemiAbelian G ∧ Nonempty (Unif (maximalIdeal R₁) D₁ A G) ∧ (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) := by
  first | exact @GlobalTheory.MumTrait.exists_unif_of_pelOK | exact GlobalTheory.MumTrait.exists_unif_of_pelOK | (intros; apply GlobalTheory.MumTrait.exists_unif_of_pelOK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveDeRhamClassTorsionCharacter
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.PtExt.exists_dat_chi_eq (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (N : ℕ) (hN : (p : R) ^ N = 0) (A : Over (Sp R)) [GrpObj A]
    (hA : IsAbelianScheme A) (hP : AllPrim (dp0 R) (𝟙 _) A)
    (hs : Function.Surjective (toH1O (A.hom ≫ 𝟙 _)))
    (G : PDivGroup p R) (t : G.TorsionTower A) (b : Fn0 A) (hb : IsTorsChar (p ^ N) b) :
    ∃ (c : primDR A) (d : Dat t c), ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D),
      (x ^ (p ^ N) : Pt A D) = 1 → GlobalTheory.PtExt.chi (p ^ N) d.g D x = b D x := by
  have : IsCommMonObj A := hA.comm
  have hn : ((p ^ N : ℕ) : R) = 0 := by
    simpa only [Nat.cast_pow] using hN
  have hR : GlobalTheory.PtExt.HasRoots A (p ^ N) := fun D _ _ x ↦
    GlobalTheory.PtCover.exists_faithfullyFlat_pow_eq R A hA (p ^ N) (pow_pos (Fact.out : p.Prime).pos N) D x
  obtain ⟨u, g, hu, hg, hchi⟩ := GlobalTheory.T.exists_pushout_torsor_nTorsion_character R A (p ^ N) hn hR b hb
  obtain ⟨f, hf⟩ := GlobalTheory.PtExt.cohom_fv_of_toH1O_surjective R A hs u hu
  obtain ⟨g', hg', hchi'⟩ := GlobalTheory.CobChi.exists_isAdd_chi_eq R A (p ^ N) hn u (fv f) g hg hf
  let c : primDR A := ⟨H1.mk _ f, by rw [show primDR A = ⊤ from hP]; exact Submodule.mem_top⟩
  obtain ⟨d, -, hd⟩ := GlobalTheory.PtExt.exists_dat_of_isAdd R A p G t c f rfl g' hg'
  refine ⟨c, d, fun D _ _ x hx ↦ ?_⟩
  rw [hd, hchi' D x hx, hchi D x hx]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTermsMumfordFormalSectionTranslatesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_terms_mumfordFormalSection_translates : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ N : ℕ, 1 ≤ N → GlobalTheory.MumMult.PosN D a h h' N → ∀ (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1])), ∃ (s₀ : SecT D.toPre a N (-1) 0) (s : ∀ ν, SecT D.toPre a N (-1) (shift h h' N (-1) ν)), (∀ ν, TRel h ν s₀ (s ν)) ∧ Small (maximalIdeal R) s ∧ (∀ ν, ν ≠ 0 → Van (maximalIdeal R) (s ν) 0) ∧ (∀ (Z : Scheme.{0}) (x : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval (s 0) x z J = sval σ₀ x z J) := by
  first | exact @GlobalTheory.TwFam.exists_terms | exact GlobalTheory.TwFam.exists_terms | (intros; apply GlobalTheory.TwFam.exists_terms <;> assumption)
end

