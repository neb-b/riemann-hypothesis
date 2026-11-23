module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBimultiplicativeOfSecondQuotConst
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisLatticeNear
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorusQuotientSchemeOverNilpotentThickening
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyTrivialTorusQuotientFlatSurjectiveCosets

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormLtOneOfIrreducible
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.PsiForm

open ReciprocityTheory.ChartRestriction.G.DVR

variable {V : Type} [CommRing V] [IsDomain V]

theorem hasVal_valF {ϖ : V} [IsDiscreteValuationRing V] {X : Scheme.{0}} (L : LB X)
    (x : Spec (CommRingCat.of V) ⟶ X) (x' : Spec (CommRingCat.of (FractionRing V)) ⟶ X) (hx : x' = jK V ≫ x)
    (ε : ℤ) (t : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => x') (fun _ => ε))) {n : ℤ}
    (hn : GenHasVal ϖ L (fun _ => x) (fun _ => x') (fun _ => hx) (fun _ => ε) t n)
    (j : PUnit → L.ι) (hj : ⊤ ≤ x ⁻¹ᵁ L.U (j PUnit.unit)) :
    HasVal ϖ (valF (𝟙 (Sp (FractionRing V))) _ (t.s j).val) n := by
  subst hx
  have htop : LB.wchart L (fun _ : PUnit => x) j = ⊤ :=
    eq_top_iff.2 fun y hy => Set.mem_iInter.2 fun _ => hj hy
  have hK : (⊤ : (Spec (CommRingCat.of (FractionRing V))).Opens) ≤ LB.wchart L (fun _ : PUnit => jK V ≫ x) j :=
    fun y _ => by
      have hy : (jK V).base y ∈ LB.wchart L (fun _ : PUnit => x) j := by rw [htop]; trivial
      exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  obtain ⟨c, hc, eV, hce⟩ := genHasVal_top L (fun _ : PUnit => x) (fun _ => ε) t hn j htop hK
  have e : valF (𝟙 (Sp (FractionRing V))) _ (t.s j).val = c * algebraMap V (FractionRing V) (eV : V) := by
    rw [← hce]
    exact (dif_pos hK).trans rfl
  rw [e]
  exact hasVal_mul_unit hc eV

variable {F : Type} [NormedField F] [Algebra (FractionRing V) F]
  (hle : ∀ x : FractionRing V, ‖algebraMap _ F x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)))

omit [IsDomain V] in
include hle in
theorem norm_unit (w : Vˣ) : ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (w : V))‖ = 1 := by
  have h1 := (hle _).2 ⟨(w : V), rfl⟩
  have h2 := (hle _).2 ⟨((w⁻¹ : Vˣ) : V), rfl⟩
  have h3 : ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (w : V))‖ *
      ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ((w⁻¹ : Vˣ) : V))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
  refine le_antisymm h1 ?_
  calc (1 : ℝ) = _ := h3.symm
    _ ≤ _ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = _ := mul_one _

theorem norm_pos_of_irreducible {ϖ : V} (hϖ : Irreducible ϖ) :
    0 < ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ)‖ :=
  norm_pos_iff.2 ((map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hϖ.ne_zero))

include hle in
theorem norm_lt_one_of_irreducible {ϖ : V} (hϖ : Irreducible ϖ) :
    ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ)‖ < 1 := by
  by_contra h
  have h0 : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hϖ.ne_zero
  obtain ⟨w, hw⟩ := (hle (algebraMap V (FractionRing V) ϖ)⁻¹).1 (by
    rw [map_inv₀, norm_inv]
    exact inv_le_one_of_one_le₀ (not_lt.1 h))
  refine hϖ.not_isUnit (IsUnit.of_mul_eq_one w (IsFractionRing.injective V (FractionRing V) ?_))
  rw [map_mul, hw, mul_inv_cancel₀ h0, map_one]

include hle in
theorem norm_of_hasVal {ϖ : V} (hϖ : Irreducible ϖ) {c : FractionRing V} {n : ℤ} (hc : HasVal ϖ c n) :
    ‖algebraMap (FractionRing V) F c‖ =
      Real.exp (-(-Real.log ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ)‖ * n)) := by
  obtain ⟨w, rfl⟩ := hc
  rw [map_mul, norm_mul, norm_unit hle, _root_.mul_one, map_zpow₀, norm_zpow, neg_mul, neg_neg,
    ← Real.rpow_def_of_pos (norm_pos_of_irreducible hϖ), Real.rpow_intCast]

theorem tendsto_val [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    (D : DegData V (IsLocalRing.maximalIdeal V)) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) :
    Filter.Tendsto Q Filter.cofinite Filter.atTop := by
  refine Filter.tendsto_atTop.2 fun b => Filter.eventually_cofinite.2 ((D.psi_tendsto b.toNat).subset fun χ hχ hin => hχ ?_)
  exact (Int.self_le_toNat b).trans (genHasVal_ge_of_in hϖ D.toPre.P.L D.toPre.P.isLB (D.toPre.c χ).left (D.toPre.xK χ)
    (QForm.ptK_eq D.toPre χ) (-1) (D.toPre.psi χ) b.toNat hin (hQ χ))

theorem exists_quadraticMap [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    (D : DegData V (IsLocalRing.maximalIdeal V)) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) (a : ℝ) :
    ∃ q : QuadraticMap ℤ D.toPre.X ℝ, ∀ χ, q χ = a * Q χ := by
  have h0 := QForm.Q_zero hϖ D hQ
  have hd : HasConstSecondDiff fun χ => a * (Q χ : ℝ) := by
    refine (hasConstSecondDiff_iff _).2 fun b m ν => ?_
    have h := QForm.bOf_add_left hϖ D hQ b m ν
    simp only [QForm.bOf] at h
    have h' : Q (b + m + ν) - Q (b + m) - Q (b + ν) + Q b = Q (m + ν) - Q m - Q ν + Q 0 := by rw [h0]; linarith
    have h'' := congrArg (fun z : ℤ => a * (z : ℝ)) h'
    push_cast at h''
    linarith
  refine ⟨hd.quadraticMap fun χ => by rw [QForm.Q_neg hϖ D hQ], fun χ => ?_⟩
  change a * (Q χ : ℝ) - a * (Q 0 : ℝ) = a * (Q χ : ℝ)
  simp [h0]

theorem main : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), ∃ q : QuadraticMap ℤ u.D.toPre.X ℝ, Filter.Tendsto q Filter.cofinite Filter.atTop ∧ ∀ χ, u.PsiNorm χ (Real.exp (-q χ)) := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible u.V
  choose Q hQ using QForm.exists_QVal hϖ u.D
  obtain ⟨q, hq⟩ := exists_quadraticMap hϖ u.D hQ
    (-Real.log ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) ϖ)‖)
  refine ⟨q, ?_, fun χ j hj => ?_⟩
  · refine Filter.Tendsto.congr (fun χ => (hq χ).symm) (Filter.Tendsto.const_mul_atTop ?_ ?_)
    · exact neg_pos.2 (Real.log_neg (norm_pos_of_irreducible hϖ) (norm_lt_one_of_irreducible u.norm_le hϖ))
    · exact tendsto_intCast_atTop_atTop.comp (tendsto_val hϖ u.D hQ)
  · rw [hq]
    exact norm_of_hasVal u.norm_le hϖ (hasVal_valF u.D.toPre.P.L _ _ (QForm.ptK_eq u.D.toPre χ) (-1) _ (hQ χ) j hj)

end GlobalTheory.ZH.PsiForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpanLatticeEqOfValuationRing
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem span_lattice_eq_of_valuationRing :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.admitted M U₀ → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N), S.FF (S.TT M ξ) c ≠ 0) → (∀ (z ξ : M.Z) (c : S.TT M z →+ ZMod S.N) (c' : S.TT M ξ →+ ZMod S.N) (k : _) (k' : _), IsClosed ({z} : Set M.Z) → ξ ⤳ z → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.TT M ξ), c ⟨t, h₁⟩ = c' ⟨t, h₂⟩) → M.Div (S.FF (S.TT M z) c) k z → M.Div (S.FF (S.TT M ξ) c') k' ξ → S.FF _ c k / S.FF _ c' k' ∈ M.O ξ) → (∀ (z ξ : M.Z) (c : S.TT M z →+ ZMod S.N) (c' : S.TT M ξ →+ ZMod S.N) (k : _) (k' : _), IsClosed ({z} : Set M.Z) → ξ ⤳ z → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.TT M ξ), c ⟨t, h₁⟩ = c' ⟨t, h₂⟩) → M.Div (S.FF (S.TT M z) c) k z → M.Div (S.FF (S.TT M ξ) c') k' ξ → IsDomain (M.O ξ) → ValuationRing (M.O ξ) → IsNoetherianRing (M.O ξ) → S.FF _ c' k' / S.FF _ c k ∈ M.O ξ) → (∀ z ξ : M.Z, IsClosed ({z} : Set M.Z) → ξ ⤳ z → ValuationRing (M.O ξ) → Submodule.span (M.O ξ) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)} = Submodule.span (M.O ξ) {v | ∃ (c : S.TT M ξ →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M ξ) c) k ξ ∧ x₀ ∈ S.supI M ξ ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)}) := by
  intro o Ω _ _ _ hA S M U₀ hAdm h0 hne hge hle z ξ hz hs hval
  haveI : IsDomain o := hA.inj.isDomain
  haveI := hA.ded
  have hnoeth : IsNoetherianRing (M.O ξ) := (normalModel_height_le_one o Ω M hAdm.1.normal ξ).2.1
  have hT := (h0.1 z).1
  have hT' := (h0.1 ξ).1
  have hsup := h0.2.1 ξ z hs
  have h : S.TT M ξ ≤ S.TT M z := fun a ha x hx => ha x (AddSubgroup.closure_mono hsup hx)
  haveI := FreeNear.finite_char S (S.TT M z)
  haveI := Fintype.ofFinite (S.TT M z →+ ZMod S.N)
  have hmul := (FreeNear.proj_orthogonal S _ hT).1
  have hsum : ∀ c' : S.TT M ξ →+ ZMod S.N, S.proj _ c' =
      ∑ c ∈ Finset.univ.filter fun c : S.TT M z →+ ZMod S.N => c.comp (AddSubgroup.inclusion h) = c',
        S.proj _ c := fun c' => by
    rw [(GlobalTheory.thetaSys_FF_mem_finite_perp_proj o Ω S).2.2.2 _ _ h hT hT' c', ← finsum_mem_coe_finset]
    simp
  have hcomp : ∀ (c : S.TT M z →+ ZMod S.N) (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.TT M ξ),
      c ⟨t, h₁⟩ = c.comp (AddSubgroup.inclusion h) ⟨t, h₂⟩ := fun _ _ _ _ => rfl
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨c, k, x₀, i, hk, hx, rfl⟩
    obtain ⟨k', hk'⟩ := hAdm.2 _ (c.comp (AddSubgroup.inclusion h)) hT' (hne ξ _) ξ
    have hu := hle z ξ c _ k k' hz hs (hcomp c) hk hk' inferInstance hval hnoeth
    have hp : S.proj _ (c.comp (AddSubgroup.inclusion h)) * S.proj _ c = S.proj _ c := by
      rw [hsum, Finset.sum_mul, Finset.sum_eq_single c]
      · rw [hmul, if_pos rfl]
      · intro b _ hb
        rw [hmul, if_neg hb]
      · simp
    have e : (fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)) =
        ∑ l, ((⟨_, hu⟩ : M.O ξ) * algebraMap o (M.O ξ) (S.proj _ c l i)) •
          fun j => S.th x₀ / S.FF _ (c.comp (AddSubgroup.inclusion h)) k' *
            algebraMap o Ω (S.proj _ (c.comp (AddSubgroup.inclusion h)) j l) := by
      funext j
      set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [← hp, Matrix.mul_apply, map_sum, Finset.mul_sum]
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      have h1 := hk.1
      have h2 := hk'.1
      simp only [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul, MulMemClass.coe_mul,
        Subalgebra.coe_algebraMap, map_mul]
      field_simp
    rw [SetLike.mem_coe, e]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, k', x₀, l, hk', hsup hx, rfl⟩)
  · rintro _ ⟨c', k', x', i, hk', hx', rfl⟩
    obtain ⟨x₀, hx₀⟩ := hAdm.1.div z
    choose k hk using fun c : S.TT M z →+ ZMod S.N => hAdm.2 _ c hT (hne z c) z
    have e : (fun j => S.th x' / S.FF _ c' k' * algebraMap o Ω (S.proj _ c' j i)) =
        ∑ c ∈ Finset.univ.filter fun c : S.TT M z →+ ZMod S.N => c.comp (AddSubgroup.inclusion h) = c',
          fun j => S.th x' / S.FF _ c' k' * algebraMap o Ω (S.proj _ c j i) := by
      funext j
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_apply, hsum, Matrix.sum_apply, map_sum, Finset.mul_sum]
    rw [SetLike.mem_coe, e]
    refine Submodule.sum_mem _ fun c hc => ?_
    obtain rfl := (Finset.mem_filter.1 hc).2
    have hu := mul_mem ((hsup hx₀).2 x') (hge z ξ c _ (k c) k' hz hs (hcomp c) (hk c) hk')
    have e' : (fun j => S.th x' / S.FF _ (c.comp (AddSubgroup.inclusion h)) k' * algebraMap o Ω (S.proj _ c j i)) =
        (⟨_, hu⟩ : M.O ξ) • fun j => S.th x₀ / S.FF _ c (k c) * algebraMap o Ω (S.proj _ c j i) := by
      funext j
      have h1 := (hk c).1
      have h2 := hk'.1
      have h3 := hx₀.1
      simp only [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]
      field_simp
    rw [e']
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, k c, x₀, i, hk c, hx₀, rfl⟩)

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitChartsTorusExtensionOverField
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.SplitChartsField

open GlobalTheory.UU GlobalTheory.AffineThickening GlobalTheory.TorusQuotientLift GlobalTheory.LocalWeightUnits

theorem geometricallyConnected_of_surjective {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z)
    [Surjective p] [GeometricallyConnected (p ≫ f)] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have : ConnectedSpace ↥(pullback (p ≫ f) x) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  let q := (pullbackRightPullbackFstIso f x p).inv ≫ pullback.snd p (pullback.fst f x)
  have : Surjective q := inferInstance
  exact q.surjective.connectedSpace q.continuous

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] {B : Scheme.{0}}
  {i : splitTorus S X ⟶ G} {q : G.left ⟶ B} [IsAffineHom q] {V : B.Opens} (hi : IsMonHom i) (hV : IsAffineOpen V)
  (h₀ : ∀ a : Γ(G.left, q ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (q.app V).hom c = a)
  (hinj : Function.Injective (q.app V).hom) (hS : Stable i (q ⁻¹ᵁ V))
include hi hV h₀ hS


include hinj in
theorem exists_mem_basicOpen (P : Γ(G.left, q ⁻¹ᵁ V) → Prop)
    (hP : ∀ x ∈ q ⁻¹ᵁ V, ∃ b, IsWt i _ b 0 ∧ x ∈ G.left.basicOpen b ∧ P b) {y : B} (hy : y ∈ V) :
    ∃ c : Γ(B, V), y ∈ B.basicOpen c ∧ P ((q.app V).hom c) := by
  have hG : Graded i (q ⁻¹ᵁ V) :=
    GlobalTheory.functions_graded_by_weights _ G _ i hi _ (hV.preimage q) (preimage_le_of_stable hS)
  let s : Set Γ(B, V) := {c | P ((q.app V).hom c)}
  let α : Γ(B, V) →+* wtZero i (q ⁻¹ᵁ V) := (q.app V).hom.codRestrict _ fun c => (h₀ _).2 ⟨c, rfl⟩
  have hα : Function.Bijective α := ⟨fun a b h => hinj (congrArg Subtype.val h), fun a => by
    obtain ⟨c, hc⟩ := (h₀ a.1).1 a.2
    exact ⟨c, Subtype.ext hc⟩⟩
  have h1 : Ideal.span ((q.app V).hom '' s) = ⊤ := by
    rw [← (hV.preimage q).self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨b, hb, hxb, hPb⟩ := hP x hx
    obtain ⟨c, rfl⟩ := (h₀ b).1 hb
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨_, c, hPb, rfl⟩, hxb⟩
  have h2 : (1 : wtZero i (q ⁻¹ᵁ V)) ∈ (Ideal.span s).map α := hG.mem_map _ α 1 (by
    rw [Ideal.map_span]
    exact h1.ge trivial)
  have h3 : Ideal.span s = ⊤ := by
    obtain ⟨c, hc, e⟩ := (Ideal.mem_map_iff_of_surjective α hα.2).1 h2
    rw [Ideal.eq_top_iff_one, ← hα.1 (e.trans (map_one α).symm)]
    exact hc
  obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1 (hV.self_le_iSup_basicOpen_iff.2 h3 hy)
  exact ⟨c.1, hc, c.2⟩

theorem isWt_basicOpen_iff (c : Γ(B, V)) (a : Γ(G.left, q ⁻¹ᵁ B.basicOpen c)) :
    IsWt i _ a 0 ↔ ∃ c', (q.app (B.basicOpen c)).hom c' = a := by
  have e : q ⁻¹ᵁ B.basicOpen c = G.left.basicOpen ((q.app V).hom c) := Scheme.preimage_basicOpen _ _
  have hle := B.basicOpen_le c
  have hG : Graded i (q ⁻¹ᵁ V) :=
    GlobalTheory.functions_graded_by_weights _ G _ i hi _ (hV.preimage q) (preimage_le_of_stable hS)
  have hS' : Stable i (q ⁻¹ᵁ B.basicOpen c) := e ▸ stable_basicOpen hS (hasWt_iff.2 ((h₀ _).2 ⟨c, rfl⟩))
  have hG' : Graded i (q ⁻¹ᵁ B.basicOpen c) :=
    GlobalTheory.functions_graded_by_weights _ G _ i hi _ ((hV.basicOpen c).preimage q) (preimage_le_of_stable hS')
  have hw : ∀ x, IsWt i _ ((q.app (B.basicOpen c)).hom (rs hle x)) 0 := fun x => by
    rw [app_rs]
    exact ((h₀ _).2 ⟨x, rfl⟩).res _
  obtain ⟨v, hv⟩ : IsUnit (rs hle c) := B.toRingedSpace.isUnit_res_basicOpen c
  constructor
  · intro ha
    obtain ⟨n, y, hy⟩ := exists_eq_pow_mul (hV.preimage q) (q.preimage_mono hle) _ a e
    rw [← app_rs q hle] at hy
    obtain ⟨x, hx, hx'⟩ := hG.exists_lift hG' (rs (q.preimage_mono hle)) (fun _ _ hx => hx.res _) y (χ := 0)
      (hy ▸ mul_mem (pow_mem (S := wtZero i _) (hw c) n) ha)
    obtain ⟨x, rfl⟩ := (h₀ x).1 hx
    refine ⟨(v⁻¹).val ^ n * rs hle x, ?_⟩
    rw [map_mul, app_rs, hx', hy, ← hv, ← map_pow _ v.val, ← _root_.mul_assoc, ← map_mul, ← mul_pow,
      Units.inv_mul, one_pow, map_one, _root_.one_mul]
  · rintro ⟨c', rfl⟩
    obtain ⟨n, y, hy⟩ := exists_eq_pow_mul hV hle c c' rfl
    have e' : c' = (v⁻¹).val ^ n * rs hle y := by
      rw [hy, ← hv, ← _root_.mul_assoc, ← mul_pow, Units.inv_mul, one_pow, _root_.one_mul]
    have h1 : IsWt i _ (Units.map (q.app (B.basicOpen c)).hom.toMonoidHom v).val 0 := by
      have := hw c
      rwa [← hv] at this
    have h2 := h1.inv
    rw [neg_zero] at h2
    rw [e', map_mul, map_pow]
    exact mul_mem (pow_mem (S := wtZero i _) h2 n) (hw y)


omit hi h₀ hS in
include hinj in
theorem injective_basicOpen (c : Γ(B, V)) : Function.Injective (q.app (B.basicOpen c)).hom := by
  have hle := B.basicOpen_le c
  obtain ⟨v, hv⟩ : IsUnit (rs hle c) := B.toRingedSpace.isUnit_res_basicOpen c
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul hV hle c a rfl
  obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero (hV.preimage q) (q.preimage_mono hle) ((q.app V).hom c)
    ((q.app V).hom y) (Scheme.preimage_basicOpen _ _) (by rw [← app_rs q hle, hy, map_mul, ha, mul_zero])
  rw [← map_pow, ← map_mul, map_eq_zero_iff _ hinj] at hm
  have := congrArg (rs hle) hm
  rwa [map_mul, map_pow, map_zero, hy, ← hv, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
    Units.mul_right_eq_zero, Units.mul_right_eq_zero] at this


omit hi hV h₀ hS in
theorem main : ∀ (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom] [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (i : splitTorus (Sp K) (Fin d → ℤ) ⟶ H), GeometricallyConnected H.hom → C.Torus c i → ∃ (B : Over (Sp K)) (_ : GrpObj B) (q : H ⟶ B), IsAbelianScheme B ∧ IsMonHom q ∧ Flat q.left ∧ Surjective q.left ∧ IsAffineHom q.left ∧ IsPullback i (toUnit _) q (η[B]) ∧ ∀ a, ∃ (V : B.left.Opens) (h : C.W a = q.left ⁻¹ᵁ V), IsAffineOpen V ∧ ∀ u, HasWt i (C.W a) u 0 ↔ u ∈ Set.range (q.left.appLE V (C.W a) h.le).hom := by
  intro K _ H _ _ _ _ _ C d c i hc hT
  obtain ⟨B, q, hp, ha, V, hcov, hV⟩ := Charts.Torus.exists_proper_quotient K H C d c i hT
  obtain ⟨hm, hf, hs, hsm, hfib⟩ := GlobalTheory.LocTriv.main (Sp K) (Fin d → ℤ) H B i q hT.hom ha fun y => by
    obtain ⟨a, hy⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge (Set.mem_univ y))
    obtain ⟨haff, h, hinj, h₀⟩ := hV a
    have hS := hT.stable a
    have hl := GlobalTheory.LocalWeightUnits.main K H C d c i hT a
    generalize C.W a = W at h hinj h₀ hS hl
    subst h
    rw [Scheme.Hom.appLE_eq_app] at hinj h₀
    have h₀' := fun u => hasWt_iff.symm.trans (h₀ u)
    obtain ⟨b, hb, hb₁, u, hu⟩ := exists_mem_basicOpen hT.hom haff h₀' hinj hS
      (fun b => Stable i (H.left.basicOpen b) ∧ ∃ u : Multiplicative (Fin d → ℤ) →* Γ(H.left, H.left.basicOpen b)ˣ,
        ∀ χ, HasWt i _ (u (Multiplicative.ofAdd χ)).val χ)
      (fun x hx => (hl x hx).imp fun b hb => ⟨hasWt_iff.1 hb.1, hb.2⟩) hy
    refine ⟨B.left.basicOpen b, hb, haff.basicOpen b, isWt_basicOpen_iff hT.hom haff h₀' hS b,
      injective_basicOpen haff hinj b, ?_⟩
    rw [Scheme.preimage_basicOpen]
    exact ⟨preimage_le_of_stable hb₁, u, fun χ => hasWt_iff.1 (hu χ)⟩
  obtain ⟨g, hcomm, hq, hker⟩ :=
    GlobalTheory.grpObj_of_flat_coset_quotient (Sp K) H _ B i q hT.hom hm hf hs inferInstance hfib
  have : GeometricallyConnected (q.left ≫ B.hom) := by rwa [Over.w]
  refine ⟨B, g, q, ⟨hcomm, hsm inferInstance, hp, geometricallyConnected_of_surjective q.left B.hom⟩, hq, hf, hs, ha,
    hker, fun a => ?_⟩
  obtain ⟨haff, h, -, h₀⟩ := hV a
  exact ⟨V a, h, haff, h₀⟩

end GlobalTheory.SplitChartsField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemNormWeightSumLeExpOfTest
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ThetaBound

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)

theorem proj_mul_proj (T T' : AddSubgroup S.Gam) (h : T' ≤ T) (hT : T ≤ S.perp T)
    (hT' : S.IsoFree T') (c : T →+ ZMod S.N) (c' : T' →+ ZMod S.N)
    (hc : ∀ t : T', c' t = c (AddSubgroup.inclusion h t)) :
    S.proj T' c' * S.proj T c = S.proj T c := by
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero S.N := ⟨by omega⟩
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  have := Fintype.ofFinite T
  have := Fintype.ofFinite T'
  obtain ⟨d, ⟨e⟩⟩ := hT'.2
  have hζ : IsPrimitiveRoot S.ζN S.N := S.prim.pow (NeZero.pos _) (by ring)
  let χ : AddChar (ZMod S.N) o := AddChar.zmodChar S.N hζ.pow_eq_one
  have hu : IsUnit (Nat.card T' : o) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.cast_pow]
    exact S.unit.pow _
  have h1 : S.proj T c = Ring.inverse (Nat.card T : o) • ∑ t : T, χ (-c t) • S.ρ t := by
    rw [← finsum_eq_sum_of_fintype]; rfl
  have h2 : S.proj T' c' = Ring.inverse (Nat.card T' : o) • ∑ t : T', χ (-c' t) • S.ρ t := by
    rw [← finsum_eq_sum_of_fintype]; rfl
  have h3 : ∀ u : T', (χ (-c' u) • S.ρ u) * ∑ t : T, χ (-c t) • S.ρ t
      = ∑ t : T, χ (-c t) • S.ρ t := fun u => by
    conv_rhs => rw [← Equiv.sum_comp (Equiv.addLeft (AddSubgroup.inclusion h u))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_mul_smul_comm, ← AddChar.map_add_eq_mul, S.ρ_add _ _ (by
      rw [hT (h u.2) t t.2, smul_zero]), hc]
    simp only [Equiv.coe_addLeft, map_add (f := _), neg_add]
    rfl
  have h4 : ∀ u : T', (χ (-c' u) • S.ρ u) * S.proj T c = S.proj T c := fun u => by
    rw [h1, mul_smul_comm, h3]
  rw [h2, smul_mul_assoc, Finset.sum_mul]
  simp_rw [h4]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul o,
    smul_smul, Ring.inverse_mul_cancel _ hu, one_smul]

theorem norm_FF_le {p : ℕ} [Fact p.Prime] (y : S.R →+* PadicAlgCl p)
    (hy : ∀ a : o, ‖y (algebraMap o S.R a)‖ ≤ 1) (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N)
    (k : _) (hk : S.FF T c k ∈ S.R) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ t : T, ‖∑ j, y (algebraMap o S.R (S.proj T c j k.1)) * y ⟨S.ev t j, S.ev_mem _ j⟩‖ ≤ B) :
    ‖y ⟨S.FF T c k, hk⟩‖ ≤ B := by
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have := Fintype.ofFinite T
  have h1 : (⟨S.FF T c k, hk⟩ : S.R) = ∑ t : T, algebraMap o S.R (S.ζ ^ (k.2 t).val) *
      ∑ j, algebraMap o S.R (S.proj T c j k.1) * ⟨S.ev t j, S.ev_mem _ j⟩ := by
    apply Subtype.ext
    simp only [ThetaSys.FF, finsum_eq_sum_of_fintype, AddSubmonoidClass.coe_finsetSum,
      MulMemClass.coe_mul, SubalgebraClass.coe_algebraMap]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB fun t _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, norm_mul, map_sum]
  simp_rw [map_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hy _)).trans (h t)

end GlobalTheory.ThetaBound

namespace GlobalTheory

open ThetaBound

theorem thetaSys_norm_FF_le_exp :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω), (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) (hk : S.FF T c k ∈ S.R), S.IsoFree T → (S.perp τ.yy.ker ≤ T → T ≤ τ.yy.ker → ∀ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N))) ∧ (T ≤ S.perp τ.yy.ker → ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) ∧ ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N)))) := by
  intro o Ω _ _ _ hA S H p _ y τ hy T c k hk hT
  obtain ⟨-, -, hperp, href⟩ := thetaSys_FF_mem_finite_perp_proj o Ω S
  have hpos : ∀ α : τ.X, 0 ≤ τ.δ * Real.exp (-(τ.q α / S.N)) := fun α =>
    mul_nonneg τ.δ_pos.le (Real.exp_pos _).le
  refine ⟨fun h1 h2 α hα hc => ?_, fun h1 => ?_⟩
  · refine norm_FF_le S y hy T c k hk (hpos α) fun t => ?_
    rw [← proj_mul_proj S T _ h1 hT.1 τ.isoFree c (τ.wt α) fun u => (hc u (h1 u.2) u.2).symm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hpos α) fun l _ => ?_
    simp_rw [mul_right_comm _ (y (algebraMap o S.R (S.proj T c l k.1)))]
    rw [← Finset.sum_mul, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hy _)).trans (τ.le α hα t (h2 t.2) l)
  · have hN := S.N_ge
    have hr := S.r_pos
    have : NeZero S.N := ⟨by omega⟩
    have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
    choose a ha hwa using (H p y τ).1
    obtain ⟨d, ⟨e⟩⟩ := hT.2
    obtain ⟨π, hπ⟩ := ThetaProj.exists_retraction T e
    have hfin : Finite (S.perp τ.yy.ker →+ ZMod S.N) := DFunLike.finite _
    set s := {c' : S.perp τ.yy.ker →+ ZMod S.N | c'.comp (AddSubgroup.inclusion h1) = c} with hs
    have hne : s.Nonempty := ⟨(c.comp π).comp (AddSubgroup.subtype _), by
      ext t
      exact congrArg c (hπ t)⟩
    obtain ⟨c₀, hc₀, hmax⟩ := Set.exists_max_image s
      (fun c' => τ.δ * Real.exp (-(τ.q (a c') / S.N))) (Set.toFinite _) hne
    refine ⟨a c₀, ha c₀, fun t h₁ h₂ => ?_, ?_⟩
    · rw [hwa, ← show _ = c from hc₀]
      rfl
    · refine norm_FF_le S y hy T c k hk (hpos _) fun t => ?_
      rw [href _ T h1 τ.isoFree hT c, finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp_rw [Matrix.sum_apply, map_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hpos _) fun c' hc' => ?_
      have ht : (t : S.Gam) ∈ τ.yy.ker := by
        rw [← hperp τ.yy.ker]
        exact τ.isoFree.1 (h1 t.2)
      have := τ.le (a c') (ha c') t ht k.1
      rw [hwa] at this
      exact this.trans (hmax c' ((Set.Finite.mem_toFinset _).mp hc'))

end GlobalTheory
end

