module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0541
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGaugeFiniteExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2479
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1976
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2481
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionMapWelldefinedAdditiveCharacters
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesTermsTorsionPointFiniteAdicCombinatio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

open GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.ThetaTermAdic

theorem decomp (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : ℕ) (hm : 0 < m) :
    ∃ (mu rh : X → X), (Set.range rh).Finite ∧ ∀ χ, χ = m • mu χ + rh χ := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  refine ⟨fun χ => ∑ i, (b.repr χ i / (m : ℤ)) • b i, fun χ => ∑ i, (b.repr χ i % (m : ℤ)) • b i, ?_, fun χ => ?_⟩
  · have hS : (Set.pi Set.univ fun _ : Module.Free.ChooseBasisIndex ℤ X => Set.Ico (0 : ℤ) m).Finite :=
      Set.Finite.pi fun _ => Set.finite_Ico _ _
    refine (hS.image fun f => ∑ i, f i • b i).subset ?_
    rintro _ ⟨χ, rfl⟩
    have hm' : (0 : ℤ) < m := by exact_mod_cast hm
    exact ⟨fun i => b.repr χ i % m, fun i _ => ⟨Int.emod_nonneg _ hm'.ne', Int.emod_lt_of_pos _ hm'⟩, rfl⟩
  · conv_lhs => rw [← b.sum_repr χ]
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Nat.cast_smul_eq_nsmul ℤ, smul_smul, ← add_smul, Int.mul_ediv_add_emod]

theorem mul_mem_smul_top {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R) (a s : S)
    (hs : s ∈ (I • ⊤ : Submodule R S)) : a * s ∈ (I • ⊤ : Submodule R S) := by
  rw [Ideal.smul_top_eq_map] at hs ⊢
  exact Ideal.mul_mem_left _ a hs

theorem core {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (N : GlobalTheory.Ex.NumD (Kb R))
    (S : Subalgebra R (Kb R)) [Module.Finite R S] (m : ℕ) (hm : 0 < m) (q : N.QT (m ^ 2))
    (hθ : ∀ x ∈ Subgroup.closure (Set.range N.c ∪ {(q.1.2 ^ m).b}), ∀ x' ∈ Subgroup.closure (Set.range N.c ∪ {(q.1.2 ^ m).b}),
      ∀ x'' ∈ Subgroup.closure (Set.range N.c ∪ {(q.1.2 ^ m).b}),
      (N.θ x x' x'' : Kb R) ∈ S ∧ (((N.θ x x' x'')⁻¹ : (Kb R)ˣ) : Kb R) ∈ S)
    (hσ : ∀ x ∈ Subgroup.closure (Set.range N.c ∪ {(q.1.2 ^ m).b}), (N.σ x : Kb R) ∈ S ∧ (((N.σ x)⁻¹ : (Kb R)ˣ) : Kb R) ∈ S)
    (hthS : ∀ χ, N.th (N.c χ * (q.1.2 ^ m).b) ∈ S) (hψS : ∀ χ, (N.ψ χ : Kb R) ∈ S)
    (hψn : ∀ n : ℕ, {χ | ¬ ∃ s ∈ (maximalIdeal R ^ n • ⊤ : Submodule R S), (s : Kb R) = N.ψ χ}.Finite) :
    ∃ (Jx : Type) (_ : Fintype Jx) (g : Jx → Kb R) (c : N.X → Jx → R),
      (∀ χ, N.txT m q χ = ∑ k, algebraMap (FractionRing R) (Kb R) (algebraMap R _ (c χ k)) * g k) ∧
      ∀ n : ℕ, {χ | ¬ ∀ k, c χ k ∈ maximalIdeal R ^ n}.Finite := by
  classical
  set h := q.1.2 ^ m with hdef
  set y := q.1.1.toAdd with hy
  have hh : h ^ m = N.io y := by rw [hdef, ← pow_mul, ← sq]; exact N.mem_QT.1 q.2
  obtain ⟨mu, rh, hrf, hχ⟩ := decomp N.X m hm
  choose w hwS hw using GlobalTheory.T.thetaSeriesTerm_smul_add_decomposition (Kb R) N S.toSubring m h y hh hθ hσ
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := S)
  obtain ⟨e, he⟩ : ∃ e, m ^ 2 = e + 1 := ⟨m ^ 2 - 1, by have := pow_pos hm 2; omega⟩
  let K : N.X → Kb R := fun b => ((N.wQ q / mulq N.θ N.σ m q.1.2.b : (Kb R)ˣ) : Kb R) *
    ((N.ψ b * h.s b * (N.ψ (m • b + y))⁻¹ : (Kb R)ˣ) : Kb R)
  let z0 : N.X → Kb R := fun χ => (w (mu χ) (rh χ) : Kb R) * (N.ψ (mu χ) : Kb R) ^ e * N.th (N.c χ * h.b) *
    N.ψ (mu χ + (m • rh χ + y))
  have key : ∀ χ, N.txT m q χ = K (rh χ) * z0 χ := fun χ => by
    have a := hw (mu χ) (rh χ)
    rw [← hχ χ, he, NumD.τ] at a
    simp only [NumD.txT, NumD.vt, K, z0]
    rw [← hdef, a]
    push_cast
    field_simp
    ring
  have hz0 : ∀ χ, z0 χ ∈ S := fun χ =>
    S.mul_mem (S.mul_mem (S.mul_mem (Subalgebra.mem_toSubring.1 (hwS _ _)) (S.pow_mem (hψS _) _)) (hthS χ)) (hψS _)
  let zS : N.X → S := fun χ => ⟨z0 χ, hz0 χ⟩
  have hzn : ∀ n : ℕ, {χ | zS χ ∉ (maximalIdeal R ^ n • ⊤ : Submodule R S)}.Finite := fun n => by
    refine (hrf.biUnion fun b _ => (hψn n).image fun χ' => m • (χ' - (m • b + y)) + b).subset ?_
    intro χ hχn
    refine Set.mem_biUnion (Set.mem_range_self χ) ⟨mu χ + (m • rh χ + y), ?_, ?_⟩
    · rintro ⟨s', hs', he'⟩
      refine hχn ?_
      have e1 : zS χ = (⟨(w (mu χ) (rh χ) : Kb R) * (N.ψ (mu χ) : Kb R) ^ e * N.th (N.c χ * h.b),
          S.mul_mem (S.mul_mem (Subalgebra.mem_toSubring.1 (hwS _ _)) (S.pow_mem (hψS _) _)) (hthS χ)⟩ : S) * s' :=
        Subtype.ext (by simp only [zS, z0, Subalgebra.coe_mul, he'])
      rw [e1]
      exact mul_mem_smul_top _ _ _ hs'
    · change m • (mu χ + (m • rh χ + y) - (m • rh χ + y)) + rh χ = χ
      rw [add_sub_cancel_right]; exact (hχ χ).symm
  obtain ⟨c, hc, hcn⟩ := _root_.GlobalTheory.adic_coeffs_tendsto_zero R S r s hs N.X zS hzn
  haveI : Fintype (Set.range rh) := hrf.fintype
  refine ⟨Fin r × Set.range rh, inferInstance, fun k => K k.2 * (s k.1 : Kb R),
    fun χ k => if (⟨rh χ, Set.mem_range_self χ⟩ : Set.range rh) = k.2 then c χ k.1 else 0, fun χ => ?_, fun n => ?_⟩
  · rw [key, Fintype.sum_prod_type]
    have hz : z0 χ = ∑ j, algebraMap R (Kb R) (c χ j) * (s j : Kb R) := by
      have := congrArg Subtype.val (hc χ)
      simpa [zS, Algebra.smul_def] using this
    rw [hz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [apply_ite, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← IsScalarTower.algebraMap_apply]
    ring
  · refine (hcn n).subset fun χ hχ hall => hχ fun k => ?_
    dsimp only
    split_ifs
    · exact hall _
    · exact zero_mem _

theorem terms : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (N : GlobalTheory.Ex.NumD (Kb R)) (ν : GlobalTheory.Ex.NumOf D.toPre (Kb R) N) (m : ℕ), Odd m → IsUnit (m : R) → ∀ (p : QkPt D.toPre (Kb R) (m ^ 2)) (q : N.QT (m ^ 2)), ν.QPt p q → ∃ (Jx : Type) (_ : Fintype Jx) (g : Jx → Kb R) (c : N.X → Jx → R), (∀ χ, N.txT m q χ = ∑ k, algebraMap (FractionRing R) (Kb R) (algebraMap R _ (c χ k)) * g k) ∧ ∀ n : ℕ, {χ | ¬ ∀ k, c χ k ∈ maximalIdeal R ^ n}.Finite := by
  intro R _ _ _ hB D N ν m hm hmu p q hq
  haveI : IsNoetherianRing R := hB.1.1
  obtain ⟨N', ν', q', S, hth, hq', hfin, hθ, hσ, hthS, hψS, hψn⟩ := _root_.GlobalTheory.FinGauge.gauge R hB D N ν m hm hmu p
  haveI := hfin
  obtain ⟨I, hl, -, hI⟩ := GlobalTheory.GaugeHom.exists_hom R D.toPre (Kb R) (Kb R) (RingHom.id _) (RingHom.id_comp _) N N' ν ν' hth
  obtain ⟨e1, e2⟩ := hI (m ^ 2) p p q q' (GlobalTheory.SeriesCompare.qkExt_id p) hq hq'
  have htx : ∀ χ, N.txT m q χ = N'.txT m q' (I.e χ) := fun χ => by
    rw [I.txT_eq hm q q' e1 e2 χ, hl, Units.val_one, _root_.one_mul, RingHom.id_apply]
  obtain ⟨Jx, fJ, g, c, hc, hcn⟩ := core N' S m hm.pos q' hθ hσ hthS hψS hψn
  exact ⟨Jx, fJ, g, fun χ => c (I.e χ), fun χ => by rw [htx, hc], fun n => (hcn n).preimage I.e.injective.injOn⟩

end GlobalTheory.ThetaTermAdic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupTowerSameGenericFibreRealisations
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem Tower.same : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ 𝔗 : Tower X₁ act, GlobalTheory.Poinc.Same X₁.ρ act 𝔗.X₂.ρ 𝔗.act₂ 𝔗.lam (algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁) := by
  intro g n F W Z i X₁ act hact 𝔗
  let f₂ : Sp 𝔗.X₂.Ω₁ ⟶ Sp 𝔗.X₂.S.R := spMap 𝔗.X₂.S.R.val.toRingHom
  let P₀ : PolAV (Sp 𝔗.X₂.Ω₁) :=
    { A := (Over.pullback f₂).obj 𝔗.X₂.ρ.P.A
      isAb := TLinPf.isAb_pullback f₂ _ 𝔗.X₂.ρ.P.isAb
      g := 𝔗.X₂.ρ.P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (isGrpPullback_pullback 𝔗.X₂.ρ.P.A f₂).1 𝔗.X₂.ρ.P.smoothDim
      L := 𝔗.X₂.ρ.P.L.pull (pullback.fst 𝔗.X₂.ρ.P.A.hom f₂)
      isLB := pull_isLB 𝔗.X₂.ρ.P.isLB _
      rigid := PolBaseChange.rigidified_pull (isGrpPullback_pullback 𝔗.X₂.ρ.P.A f₂) 𝔗.X₂.ρ.P.rigid
      sym := PolBaseChange.sym_pull (isGrpPullback_pullback 𝔗.X₂.ρ.P.A f₂) 𝔗.X₂.ρ.P.sym
      ample := by
        haveI := 𝔗.X₂.ρ.P.isAb.proper
        exact AmpleBaseChange.relAmple_of_isPullback 𝔗.X₂.ρ.P.isLB 𝔗.X₂.ρ.P.ample
          (IsPullback.of_hasPullback 𝔗.X₂.ρ.P.A.hom f₂)
      ktriv := by
        obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (pull_isLB 𝔗.X₂.ρ.P.isLB (pullback.fst 𝔗.X₂.ρ.P.A.hom f₂))
        exact kTriv_pull (isGrpPullback_pullback 𝔗.X₂.ρ.P.A f₂) 𝔗.X₂.ρ.P.isLB (pull_isLB 𝔗.X₂.ρ.P.isLB _) ((isGen_iff w).1 hw) 𝔗.X₂.ρ.P.ktriv }
  let a' : P₀.A.left ⟶ 𝔗.X₂.ρ.P.A.left := pullback.fst 𝔗.X₂.ρ.P.A.hom f₂
  have hring : (algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom = 𝔗.X₂.S.R.val.toRingHom.comp 𝔗.om := by
    ext x; exact (𝔗.om_eq x).symm
  have hsp : spMap ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom) = f₂ ≫ spMap 𝔗.om := by
    rw [hring]; exact Spec.map_comp (CommRingCat.ofHom 𝔗.om) (CommRingCat.ofHom 𝔗.X₂.S.R.val.toRingHom)
  have ha' : IsGrpPullback P₀.A 𝔗.X₂.ρ.P.A f₂ a' := isGrpPullback_pullback _ _
  have hr : LBIso P₀.L (𝔗.X₂.ρ.P.L.pull a') := ⟨idIso _, idIso_isGen P₀.isLB⟩
  refine ⟨P₀, a' ≫ 𝔗.φ, a', fun E => (Over.pullback f₂).map (𝔗.act₂ E), ?_, ha', ?_, hr, ?_, ?_⟩
  · exact (ha'.comp 𝔗.cart).congr hsp.symm rfl
  · exact LBIso.trans P₀.isLB (pull_isLB 𝔗.X₂.ρ.P.isLB _) (pull_isLB X₁.ρ.P.isLB _) hr (lbIso_pull_comp 𝔗.lb a')
  · intro E
    have h1 : ((Over.pullback f₂).map (𝔗.act₂ E)).left ≫ a' = a' ≫ (𝔗.act₂ E).left :=
      pullback.lift_fst _ _ _
    refine ⟨?_, h1⟩
    have h2 : (a' ≫ (𝔗.act₂ E).left) ≫ 𝔗.φ = a' ≫ 𝔗.φ ≫ (act E).left := by
      rw [Category.assoc, 𝔗.act_eq]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ 𝔗.φ) h1).trans h2)
  · intro x
    have hc : (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) ≫ 𝔗.X₂.ρ.P.A.hom = 𝟙 _ ≫ f₂ := by
      rw [Category.assoc, Over.w (𝔗.X₂.ρ.pt (𝔗.lam x))]
      simp [baseOver]
    refine ⟨pullback.lift (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) (𝟙 _) hc, ?_, ?_⟩
    · have hw : pullback.lift (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) (𝟙 _) hc ≫ a' = f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left :=
        pullback.lift_fst _ _ _
      have h3 : (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) ≫ 𝔗.φ =
          spMap ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom) ≫ (X₁.ρ.pt x).left := by
        rw [Category.assoc, 𝔗.lam_pt, hsp, Category.assoc]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ 𝔗.φ) hw).trans h3)
    · exact pullback.lift_fst _ _ _
end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDivPowFactorialIsUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UMin.symTup_div_pow_isUnit_of_dvd : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (A : Subalgebra k Ω) [IsLocalRing A] (N : ℕ) (c : Fin N → Ω) (a j : Fin N), c a ≠ 0 → (∀ b, c b / c a ∈ A) → symTup c j ≠ 0 → (∀ b, symTup c b / symTup c j ∈ A) → symTup c j / c a ^ N.factorial ≠ 0 ∧ symTup c j / c a ^ N.factorial ∈ A ∧ (symTup c j / c a ^ N.factorial)⁻¹ ∈ A := by
  intro k Ω _ _ _ A _ N c a j hca hcb hj hjb
  have hpow : c a ^ N.factorial ≠ 0 := pow_ne_zero _ hca
  let d : Fin N → A := fun b => ⟨c b / c a, hcb b⟩
  have hd : ∀ j' : Fin N, symTup c j' / c a ^ N.factorial = ((symTup d j' : A) : Ω) := by
    intro j'
    have h1 : c = fun b => c a * ((d b : A) : Ω) := by
      funext b; show c b = c a * (c b / c a); field_simp
    have h2 := (GlobalTheory.UMin.symTup_basic).1 Ω N (fun b => ((d b : A) : Ω)) (c a) j'
    have h3 := (GlobalTheory.UMin.symTup_basic).2.2.1 A Ω A.val.toRingHom N d j'
    have h4 : symTup c j' = c a ^ N.factorial * symTup (fun b => ((d b : A) : Ω)) j' := by
      rw [← h2, ← h1]
    rw [h4, mul_div_cancel_left₀ _ hpow]
    exact h3.symm
  have hda : d a = 1 := Subtype.ext (by show c a / c a = 1; exact div_self hca)
  obtain ⟨k0, hk1, hk2, hku⟩ := GlobalTheory.exists_isUnit_esymm_of_eq_one A (Fin N) d a hda
  rw [Fintype.card_fin] at hk2
  let j' : Fin N := ⟨k0 - 1, by omega⟩
  have hk0 : (j' : ℕ) + 1 = k0 := by show k0 - 1 + 1 = k0; omega
  have hu : IsUnit (symTup d j') := by
    unfold symTup; rw [hk0]; exact hku.pow _
  let x : A := ⟨symTup c j / c a ^ N.factorial, by rw [hd j]; exact (symTup d j).2⟩
  let z : A := ⟨symTup c j' / symTup c j, hjb j'⟩
  have hxz : symTup d j' = x * z := by
    apply Subtype.ext
    show ((symTup d j' : A) : Ω) = (symTup c j / c a ^ N.factorial) * (symTup c j' / symTup c j)
    rw [← hd j']
    field_simp
  rw [hxz] at hu
  have hx : IsUnit x := isUnit_of_mul_isUnit_left hu
  refine ⟨div_ne_zero hj hpow, x.2, ?_⟩
  obtain ⟨v, hv⟩ := hx.exists_right_inv
  have hv' : (symTup c j / c a ^ N.factorial) * (v : Ω) = 1 := by
    have := congrArg (fun t : A => (t : Ω)) hv
    simpa using this
  rw [← eq_inv_of_mul_eq_one_right hv']
  exact v.2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityComplexFormAevalDzWedgeDzbar
section
set_option autoImplicit false

noncomputable section

open MvPolynomial
open GlobalTheory.CxForm GlobalTheory.GoodMetric GlobalTheory.CxForm.DensPow GlobalTheory.GrassModel GlobalTheory.GrassModel.TopRead

namespace GlobalTheory.ChernCalc.DensTop

variable {n : ℕ}

theorem bas_mul_smul (S T : Finset (Fin (n + n))) : ∃ c : ℂ, bas n S * bas n T = c • bas n (S ∪ T) := by
  by_cases h : Disjoint S T
  · obtain ⟨ε, e⟩ := bas_mul h
    exact ⟨_, by rw [e, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ]⟩
  · have := ExteriorAlgebra.basis_mul_of_not_disjoint ((Pi.basisFun ℂ (Fin n ⊕ Fin n)).reindex finSumFinEquiv)
      (Set.powersetCard.ofCard (s := S) rfl) (Set.powersetCard.ofCard (s := T) rfl) h
    have e : bas n S * bas n T = 0 := this
    exact ⟨0, by rw [e, zero_smul]⟩

theorem prod_sym_eq {ι : Type} [DecidableEq ι] (x : ι → Fin n × Fin n) (s : Finset ι) :
    ∃ (c : ℂ) (S : Finset (Fin (n + n))), S.card ≤ 2 * s.card ∧ ((∏ j ∈ s, sym (x j) : Ev n) : Alt n) = c • bas n S := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, ∅, by simp, by simp [bas_empty]⟩
  | insert a s ha ih =>
    obtain ⟨c, S, hS, e⟩ := ih
    obtain ⟨c₁, h₁⟩ := bas_mul_smul {finSumFinEquiv (.inl (x a).1)} {finSumFinEquiv (.inr (x a).2)}
    obtain ⟨c₂, h₂⟩ := bas_mul_smul ({finSumFinEquiv (.inl (x a).1)} ∪ {finSumFinEquiv (.inr (x a).2)}) S
    refine ⟨c₁ * c * c₂, ({finSumFinEquiv (.inl (x a).1)} ∪ {finSumFinEquiv (.inr (x a).2)}) ∪ S, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem ha]
      refine (Finset.card_union_le _ _).trans ?_
      have := Finset.card_union_le ({finSumFinEquiv (.inl (x a).1)} : Finset (Fin (n + n)))
        {finSumFinEquiv (.inr (x a).2)}
      rw [Finset.card_singleton, Finset.card_singleton] at this
      omega
    · rw [Finset.prod_insert ha, Subalgebra.coe_mul, e,
        show (sym (x a) : Alt n) = dz (x a).1 * dzb (x a).2 from rfl, dz, dzb, ← bas_singleton,
        ← bas_singleton, h₁, smul_mul_smul_comm, h₂, smul_smul]

theorem prod_sym_not_inj {m : ℕ} (x : Fin m → Fin n × Fin n) (h : ¬ Function.Injective fun j => (x j).1) :
    (∏ j, sym (x j) : Ev n) = 0 := by
  simp only [Function.Injective, not_forall] at h
  obtain ⟨i, j, hij, hne⟩ := h
  have h0 : sym (x i) * sym (x j) = 0 := by
    apply Subtype.ext
    change dz (x i).1 * dzb (x i).2 * (dz (x j).1 * dzb (x j).2) = 0
    rw [hij]
    exact ι_mul_ι_mul_ι_mul_ι_left _ _ _
  rw [← Finset.mul_prod_erase Finset.univ (fun a => sym (x a)) (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) (fun a => sym (x a))
      (Finset.mem_erase.2 ⟨fun e => hne e.symm, Finset.mem_univ j⟩), ← mul_assoc, h0, zero_mul]

theorem dens_zero' : dens (0 : Alt n) = 0 := by simp [dens]

theorem dens_add' (x y : Alt n) : dens (x + y) = dens x + dens y := by simp [dens, add_div]

theorem dens_prod_diag : dens ((∏ a, sym (a, a) : Ev n) : Alt n) = ((Complex.I / 2) ^ n)⁻¹ := by
  have h1 := dens_vol n
  rw [vol_eq_smul_prod, Subalgebra.coe_smul, dens_smul] at h1
  exact eq_inv_of_mul_eq_one_right h1

theorem dens_prod {m : ℕ} (x : Fin m → Fin n × Fin n) :
    dens ((∏ j, sym (x j) : Ev n) : Alt n) =
      topForm n m (fun j => Pi.single (x j).1 1) * topForm n m (fun j => Pi.single (x j).2 1) /
        (Complex.I / 2) ^ n := by
  by_cases hm : m = n
  swap
  · have h0 : topForm n m = 0 := by simp [topForm, hm]
    rw [h0]
    simp only [AlternatingMap.zero_apply, mul_zero, zero_div]
    rcases lt_or_gt_of_ne hm with h | h
    · obtain ⟨c, S, hS, e⟩ := prod_sym_eq x Finset.univ
      have hne : S ≠ Finset.univ := by
        rintro rfl
        simp at hS
        omega
      rw [e]
      simp [dens, Finsupp.single_apply, hne]
    · rw [prod_sym_not_inj x, Subalgebra.coe_zero, dens_zero']
      intro hi
      have := Fintype.card_le_of_injective _ hi
      simp at this
      omega
  subst hm
  rw [topForm_self, topForm_self]
  by_cases ha : Function.Injective fun j => (x j).1
  swap
  · rw [prod_sym_not_inj x ha, Subalgebra.coe_zero, dens_zero', det_single_not_inj _ ha, zero_mul, zero_div]
  let π : Equiv.Perm (Fin m) := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp ha)
  have hπ : ∀ j, (x j).1 = π j := fun j => rfl
  have e1 : (∏ j, sym (x j) : Ev m) = ∏ c, row c (Pi.single (x (π.symm c)).2 1) := by
    rw [← Equiv.prod_comp π fun c => row c (Pi.single (x (π.symm c)).2 1)]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Equiv.symm_apply_apply, ← hπ]
    simp [row, Pi.single_apply]
  have e2 := prod_row (n := m) (Matrix.of fun c => Pi.single (x (π.symm c)).2 1)
  have e3 : (Matrix.of fun c => (Pi.single (x (π.symm c)).2 1 : Fin m → ℂ)).det =
      (Pi.basisFun ℂ (Fin m)).det ((fun j => Pi.single (x j).2 1) ∘ π.symm) := by
    rw [Pi.basisFun_det]; rfl
  rw [e1]
  refine (congrArg (fun z : Ev m => dens (z : Alt m)) e2).trans ?_
  simp only [hπ, det_single_perm]
  rw [Subalgebra.coe_smul, dens_smul, dens_prod_diag, e3, AlternatingMap.map_perm, Equiv.Perm.sign_symm,
    Units.smul_def, zsmul_eq_mul, ← div_eq_mul_inv]

theorem dens_aeval_sym (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ) :
    dens ((aeval sym P : Ev n) : Alt n) = topCoeff P / (Complex.I / 2) ^ n := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u c =>
    obtain ⟨l, hl⟩ : ∃ l : List (Fin n × Fin n), (l : Multiset _) = Finsupp.toMultiset u :=
      ⟨_, Multiset.coe_toList _⟩
    have hu : u = ∑ j, Finsupp.single (l.get j) 1 := by
      apply toMultiset_injective'
      rw [toMultiset_sum_single, Fin.univ_val_map, List.ofFn_get, hl]
    have hmon : (monomial u c : MvPolynomial (Fin n × Fin n) ℂ) = c • ∏ j, X (l.get j) := by
      rw [hu, show (∏ j, X (l.get j) : MvPolynomial (Fin n × Fin n) ℂ) = monomial (∑ j, Finsupp.single (l.get j) 1) 1 from
        (monomial_sum_one _ _).symm, smul_monomial, smul_eq_mul, mul_one]
    rw [hmon, map_smul, Subalgebra.coe_smul, dens_smul, map_prod]
    simp only [aeval_X]
    rw [dens_prod, ← topCoeff_prod, ← mul_div_assoc]
    congr 1
    unfold topCoeff
    simp only [coeff_smul, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => by ring
  | add p q hp hq =>
    rw [map_add (f := _), Subalgebra.coe_add, dens_add', hp, hq, ← add_div]
    congr 1
    unfold topCoeff
    simp only [MvPolynomial.coeff_add, mul_add, Finset.sum_add_distrib]

end GlobalTheory.ChernCalc.DensTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelEqWeilPairingToricTorsionPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionLabel_eq_weilPairing_toricTorsionPoint : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real), ∃ sg : ℤˣ, ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (τ' : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ) (b : S.Gam), τ' ^ (S.r * S.N) = 1 → (∀ (q : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), q.y = 0 → GlobalTheory.UT.IsTor τ' q.g → QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q x → x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt b).left) → ∀ (a : S.Gam) (β : u.D.toPre.X), l.yy a = QuotientAddGroup.mk β → ((τ' (Multiplicative.ofAdd β) : (PadicAlgCl p)ˣ) : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * ((sg : ℤ) • eStd S.g _ b a).val))) := by
  first | exact @GlobalTheory.Poinc.UTestLabel.char_eq_weil_of_label | exact GlobalTheory.Poinc.UTestLabel.char_eq_weil_of_label | (intros; apply GlobalTheory.Poinc.UTestLabel.char_eq_weil_of_label <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelingsEqOfThetaPointPairingsOrderNStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionLabelings_eq_of_thetaPoint_pairings_order_n : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (n j m : ℕ), n.Prime → Odd n → m = n ^ j * (n ^ 2) ^ 2 → ((n ^ 2) ^ 2) ^ A.g * A.g.factorial < m → ∀ (x₁ x₂ : QkPt D (Kb R) (m ^ 2) → (TFK (R := R) (Kb R) ⟶ A.A)), LabTors D A (m ^ 2) x₁ → LabTors D A (m ^ 2) x₂ → (∀ p, x₁ p ^ n = 1 → x₂ p = x₁ p) → ∀ v : QkPt D (Kb R) (m ^ 2) → Kb R, IsThetaPt A m x₁ (fun p => GlobalTheory.Ex.fnOf (v p)) → IsThetaPt A m x₂ (fun p => GlobalTheory.Ex.fnOf (v p)) → ∀ p, x₂ p = x₁ p := by
  first | exact @GlobalTheory.Mum.LabelRigid.labels_eq | exact GlobalTheory.Mum.LabelRigid.labels_eq | (intros; apply GlobalTheory.Mum.LabelRigid.labels_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPairImageLatticePartEqOfMatch
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj
attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem qImg_lattice : ∀ (V : Type) [CommRing V] [IsDomain V] [CharZero V] (J : Ideal V), AdmBase V J → ∀ (D₁ D₂ : DegData V J) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ : D₁.toPre.X ≃+ D₂.toPre.X) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F], Match D₁.toPre D₂.toPre b φ F → ∀ (k : ℕ) (p : QkPt D₁.toPre F k) (p' : QkPt D₂.toPre F k), Act D₁.toPre D₂.toPre b φ.symm.toAddMonoidHom p.g p'.g → p'.y = φ p.y := by
  intro V _ _ _ J hJ D₁ D₂ b φ F _ _ _ hM k p p' hA
  obtain ⟨hmon, -, -, hnrm, hlast⟩ := hM
  obtain ⟨hex, hadd, -⟩ := GlobalTheory.Mum.Two.act_two_hom V D₁.toPre D₂.toPre b φ.symm.toAddMonoidHom hmon hnrm F
  choose α hα hαu using hex
  let f : GtPtF D₁.toPre F →+ GtPtF D₂.toPre F := AddMonoidHom.mk' α fun x y =>
    (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1
      (hadd x y (x + y) (α x) (α y) (α (x + y)) ((GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 rfl) (hα x) (hα y) (hα _))
  obtain ⟨h₁, hn₁, hi₁⟩ := p.eq
  obtain ⟨h₂, hn₂, hi₂⟩ := p'.eq
  obtain ⟨g', hg'A, hg'I⟩ := hlast p.y h₁ hi₁
  have e₁ : h₁ = k • p.g := (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 hn₁
  have e₂ : h₂ = k • p'.g := (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 hn₂
  have ep : p'.g = f p.g := hαu p.g p'.g hA
  have eg : g' = f h₁ := hαu h₁ g' hg'A
  have : g' = h₂ := by rw [eg, e₁, map_nsmul, ← ep, e₂]
  rw [← this] at hi₂
  exact GlobalTheory.IotaInj.main GlobalTheory.firstFiveLaws V J hJ D₂ F p'.y (φ p.y) g' hi₂ hg'I

end GlobalTheory.TInj

end
end

