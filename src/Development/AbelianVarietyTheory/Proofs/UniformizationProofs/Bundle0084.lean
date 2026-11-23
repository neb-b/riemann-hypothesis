module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalSecScale
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0055
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsExpFOfFam
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.ExpOnto

theorem exists_sec_comb {X : Scheme.{0}} {L : LB X} {n : ℕ} (r : Fin n → Γ(X, ⊤)) (b : Fin n → LB.Sec L) :
    ∃ t : LB.Sec L, ∀ j, t.f j = ∑ i, resTop _ (r i) * (b i).f j := by
  induction n with
  | zero => exact ⟨DVR.SecOps.secZero, fun j => by simp [DVR.SecOps.secZero]⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih (fun i => r i.succ) (fun i => b i.succ)
    refine ⟨DVR.SecOps.secAdd (DVR.SecOps.secScale (r 0) (b 0)) t, fun j => ?_⟩
    rw [Fin.sum_univ_succ, ← ht j]
    rfl

theorem fam_sum_f {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} {K : Type} (S : Finset K) (s : K → Fam D F k) (α : D.X) (j) :
    ((∑ i ∈ S, s i).s α).f j = ∑ i ∈ S, ((s i).s α).f j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, DVR.add_f, ih]

theorem exists_expF_of_fam : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → U.FE F k → ∀ s : Fam D F k, ∃ t, U.ExpF F k t s.s := by
  intro hL hL2 V _ _ _ hV D A G _ _ U hB F _ _ k hk hFE s
  obtain ⟨b, hb⟩ := GlobalTheory.PowBasis.exists_basis_pow_field hL2.secTwist V A F k hk
  choose e he using fun i => _root_.GlobalTheory.UU.ExpTotal.expF_total hL hL2 V hV D A G U F k hk (b i)
  let f : Fin (k ^ A.g) → Fam D F k := fun i => ⟨e i, hFE _ _ (he i)⟩
  have comb : ∀ c : Fin (k ^ A.g) → F, ∃ t, (∀ j, t.f j = ∑ i,
      liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) * (b i).f j) ∧
      U.ExpF F k t (∑ i, c i • f i).s := fun c => by
    obtain ⟨t, ht⟩ := exists_sec_comb (fun i => (fst (TFK (R := V) F) A.A).left.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i))) b
    refine ⟨t, ht, ExpLinC.expF_lincomb V hV D A G U F k _ c b e t _ he ht fun α j => ?_⟩
    exact fam_sum_f _ _ α j
  have hli : LinearIndependent F f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    obtain ⟨t, ht, hE⟩ := comb c
    obtain ⟨t', ht', hE'⟩ := comb 0
    have h0 : (∑ i, (0 : Fin (k ^ A.g) → F) i • f i) = ∑ i, c i • f i := by
      rw [hc]; simp
    have htt : t = t' := (_root_.GlobalTheory.UU.ExpFUniq.main V hV D A G U F k t t' _ _ hE hE').2 (by rw [h0])
    subst htt
    exact congrFun ((hb t).unique ht ht')
  obtain ⟨hfin, hdim⟩ := finrank_fam_of_laws hL hL2 V D hB F k hk
  have hg : A.g = D.P.g + D.rank := PreU.dim_eq V hV D A G U
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by rw [hdim, Fintype.card_fin, hg])
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 (hsp ▸ Submodule.mem_top (x := s))
  obtain ⟨t, -, hE⟩ := comb c
  exact ⟨t, hc ▸ hE⟩

end GlobalTheory.UU.ExpOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFunctionalEquationSectionNonzeroClass
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.FESection

theorem main : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => D.TauBimult → ∀ k : ℕ, 1 ≤ k → U.FE (Kbar V) 1 → U.FE (Kbar V) k → (∃ β, U.Supp (Kbar V) 1 β) → (∃ β, U.Supp (Kbar V) k β) → ∀ α, ∃ t s, U.ExpF (Kbar V) (k + 1) t s ∧ DegPre.FamFE D (Kbar V) (k + 1) s ∧ ∃ j, (s α).f j ≠ 0 := by
  intro hL hL2 V _ _ _ hV D A G _ _ U hB k hk hF1 hFk ⟨β₁, hβ₁⟩ ⟨β₀, hβ₀⟩ α
  have hG := hL.globalFns
  obtain ⟨σ, f, sf, hσ, hpf, hfef, -, hf0⟩ := IntWit.integral_witness V hV D A G U (Kbar V) k β₀ hFk hβ₀
  obtain ⟨ϑ, g, sg, hϑ, hpg, hfeg, ⟨j₁, hs1⟩, -⟩ := IntWit.integral_witness V hV D A G U (Kbar V) 1 β₁ hF1 hβ₁
  have hg0 : ∃ j, (g (α - β₀)).f j ≠ 0 := by
    by_contra hn
    push_neg at hn
    have h1 : ∀ j, (sg (α - β₀)).f j = 0 := fun j =>
      sec_ext_val (s' := DVR.SecOps.secZero) D.P.isLB (fun y J hJ => by
        rw [hpg _ y J hJ, DVR.UUA.sval_zero_of hn _ y J (hJ.mem _ _),
          DVR.UUA.sval_zero_of (s := DVR.SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]) j
    exact hs1 (FamFree.zero_of_eq_add_nsmul hG (⟨sg, hfeg⟩ : Fam D (Kbar V) 1)
      ⟨β₁ - (α - β₀), by rw [one_smul, add_sub_cancel]⟩ h1 j₁)
  obtain ⟨W, _, _, _, φ, a, hW, hφ, hnv⟩ := GlobalTheory.UU.exists_twist_conv_ne_zero V hV D k f g α β₀
    (GlobalTheory.NullExp.main V _ D A G U _ k σ f hσ) hf0 hg0
  obtain ⟨σ', f', hσ', hff, hpf'⟩ := expT_pull V _ D A G U _ (TA V W) (toUnit _) k σ f hσ
  obtain ⟨ϑ', g', hϑ', hgg, hpg'⟩ := expT_pull V _ D A G U _ (TA V W) (toUnit _) 1 ϑ g hϑ
  have hu : φ ≫ toUnit _ = toUnit _ := toUnit_unique _ _
  obtain ⟨x, hx⟩ := TorPtEx.main V hV D A G U W hW a
  obtain ⟨σ'', hprod⟩ := GlobalTheory.UU.prodExp_opposite_translates hG V hV D A G U W hW a x hx k σ' ϑ' f' g' hσ' hϑ'
  obtain ⟨h, hh, hext⟩ := GlobalTheory.UU.ExpExt.main hL hL2 V hV D A G U W hW (k + 1) (by omega) σ''
  have hconv := GlobalTheory.ConvOfProd.main V _ D A G U _ k 1 _ _ h σ'' hprod hh
  obtain ⟨ht, hs⟩ := PullSec.pullEx V hV D A G U (Kbar V) (TA V W) φ (k + 1)
  obtain ⟨t, ht, -⟩ := ht σ''
  obtain ⟨s, hs, -⟩ := hs h
  refine ⟨t, s, hext _ φ t s ht hs, ?_, ?_⟩
  · refine GlobalTheory.ConvFE.conv_famFE hG V hV D hB W hW (Kbar V) φ hφ k 1 f' g' h sf sg s a (a ^ k)⁻¹ (fun mu => ?_)
      ((hpf' _ φ sf).2 (hu ▸ hpf)) ((hpg' _ φ sg).2 (hu ▸ hpg)) hs hfef hfeg hconv
    rw [one_smul, ofAdd_nsmul, map_pow, MonoidHom.inv_apply, MonoidHom.pow_apply, mul_inv_cancel]
  · obtain ⟨j, hj⟩ := hnv f' g' h hff hgg hconv
    by_contra hn
    push_neg at hn
    haveI := D.P.isAb.smooth
    haveI : Flat D.P.A.hom := inferInstance
    haveI : IsAffine (TA V W).left := inferInstanceAs (IsAffine (Spec _))
    haveI : IsAffine (TF (R := V) (Kbar V)).left := inferInstanceAs (IsAffine (Spec _))
    refine hj (sec_eq_zero_of_sval_whiskerRight_eq_zero _ D.P.A _ _ φ hφ _ D.P.L D.P.isLB _ _ _ (h α)
      (fun z J hJ => ?_) j)
    exact (hs α z J hJ).symm.trans (DVR.UUA.sval_zero_of hn _ z J (hJ.mem _ _))

end GlobalTheory.UU.FESection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLinearFourierJacobiExpansionFamily
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.ExpLinMap

theorem exists_linear_of_rel {F M X : Type} [Field F] [AddCommGroup M] [Module F M] {N : X → Type}
    [∀ α, AddCommGroup (N α)] [∀ α, Module F (N α)] (E : M → (∀ α, N α) → Prop)
    (tot : ∀ t, ∃ s, E t s) (uq : ∀ t t' s s', E t s → E t' s' → (t = t' ↔ s = s'))
    (lin : ∀ (c : F) t t' s s', E t s → E t' s' → E (c • t + t') (fun α => c • s α + s' α)) :
    ∃ ex : ∀ α, M →ₗ[F] N α, (∀ t, E t (fun α => ex α t)) ∧ (∀ t s, E t s → ∀ α, s α = ex α t) ∧
      (∀ t, (∀ α, ex α t = 0) → t = 0) ∧ ∀ α, ((∃ t s, E t s ∧ s α ≠ 0) ↔ ex α ≠ 0) := by
  choose e he using tot
  have hl : ∀ (c : F) t t' α, e (c • t + t') α = c • e t α + e t' α := fun c t t' α =>
    congrFun ((uq _ _ _ _ (he _) (lin c t t' _ _ (he t) (he t'))).1 rfl) α
  have h0 : ∀ α, e 0 α = 0 := fun α => by
    have h := hl 1 0 0 α
    simpa using h
  have hu : ∀ t s, E t s → ∀ α, s α = e t α := fun t s h α => congrFun ((uq _ _ _ _ h (he t)).1 rfl) α
  refine ⟨fun α => ⟨⟨fun t => e t α, fun t t' => ?_⟩, fun c t => ?_⟩, he, hu, fun t h => ?_, fun α => ⟨?_, fun h => ?_⟩⟩
  · simpa using hl 1 t t' α
  · simpa [h0] using hl c t 0 α
  · exact (uq _ _ _ _ (he t) (he 0)).2 (funext fun α => (h α).trans (h0 α).symm)
  · rintro ⟨t, s, h, hs⟩ hz
    exact hs ((hu t s h α).trans (LinearMap.congr_fun hz t))
  · by_contra hn
    refine h (LinearMap.ext fun t => ?_)
    by_contra ht
    exact hn ⟨t, e t, he t, ht⟩

theorem exists_expansion_linear : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∃ ex : ∀ α : D.X, EA A (jFK (R := V) F) k →ₗ[F] WB D F k α, (∀ t, U.ExpF F k t.sec (fun α => (ex α t).sec)) ∧ (∀ t s, U.ExpF F k t s → ∀ α, s α = (ex α (SecMod.mk _ t)).sec) ∧ (∀ t, (∀ α, ex α t = 0) → t = 0) ∧ ∀ α, (U.Supp F k α ↔ ex α ≠ 0)) := by
  intro h1 h2 V _ _ _ hV D A G _ _ U F _ _ k hk
  obtain ⟨ex, a, b, c, d⟩ := exists_linear_of_rel (F := F) (M := EA A (jFK (R := V) F) k) (N := fun α => WB D F k α)
    (fun t s => U.ExpF F k t.sec (fun α => (s α).sec))
    (fun t => _root_.GlobalTheory.UU.ExpTotal.expF_total h1 h2 V hV D A G U F k hk t.sec)
    (fun t t' s s' h h' => _root_.GlobalTheory.UU.ExpFUniq.main V hV D A G U F k t.sec t'.sec _ _ h h')
    (fun c t t' s s' h h' => ExpLin.expF_linear V hV D A G U F k t.sec t'.sec _ _ _ _ c h h'
      (fun _ => rfl) (fun _ _ => rfl))
  refine ⟨ex, a, fun t s h α => b (SecMod.mk _ t) (fun α => SecMod.mk _ (s α)) h α, c, fun α => Iff.trans ?_ (d α)⟩
  constructor
  · rintro ⟨t, s, h, j, hj⟩
    exact ⟨SecMod.mk _ t, fun α => SecMod.mk _ (s α), h, fun hz => hj ((SecMod.eq_zero_iff_coord _).1 hz j)⟩
  · rintro ⟨t, s, h, hs⟩
    exact ⟨t.sec, fun α => (s α).sec, h, not_forall.1 fun hz => hs ((SecMod.eq_zero_iff_coord _).2 hz)⟩

end GlobalTheory.UU.ExpLinMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPullbackSectionNonzeroLocus
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolTranslate

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

noncomputable def transl (x : 𝟙_ (Over S) ⟶ A) : A ⟶ A := 𝟙 A * (toUnit A ≫ x)

theorem comp_transl (x : 𝟙_ (Over S) ⟶ A) {T : Over S} (y : T ⟶ A) : y ≫ transl x = y * (toUnit T ≫ x) := by
  rw [transl, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem toUnit_mul_self {x : 𝟙_ (Over S) ⟶ A} (hx : x * x = 1) (T : Over S) :
    (toUnit T ≫ x) * (toUnit T ≫ x) = 1 := by
  rw [← MonObj.comp_mul, hx, MonObj.comp_one]

theorem transl_transl {x : 𝟙_ (Over S) ⟶ A} (hx : x * x = 1) : transl x ≫ transl x = 𝟙 A := by
  rw [comp_transl, transl, _root_.mul_assoc, toUnit_mul_self hx, _root_.mul_one]

theorem inv_transl [IsCommMonObj A] {x : 𝟙_ (Over S) ⟶ A} (hx : x * x = 1) :
    (GrpObj.inv : A ⟶ A) ≫ transl x = transl x ≫ (GrpObj.inv : A ⟶ A) := by
  rw [comp_transl, ← Hom.inv_def, transl, mul_inv, inv_eq_of_mul_eq_one_right (toUnit_mul_self hx A), Hom.inv_def,
    Category.id_comp]

theorem exists_restrict {X Y : Scheme.{0}} (p : X ⟶ Y) (h : X ⟶ X) (e : h ≫ p = p) (V : Y.Opens) :
    ∃ n : (p ⁻¹ᵁ V).toScheme ⟶ (p ⁻¹ᵁ V).toScheme, n ≫ (p ⁻¹ᵁ V).ι = (p ⁻¹ᵁ V).ι ≫ h :=
  ⟨IsOpenImmersion.lift _ ((p ⁻¹ᵁ V).ι ≫ h) (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (congrArg (fun q => q y.1 ∈ V) e).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩

theorem sym_transl [IsCommMonObj A] {x : 𝟙_ (Over S) ⟶ A} (hx : x * x = 1) {L : LB A.left} (h : Sym A L) :
    Sym A (L.pull (transl x).left) := by
  intro s
  obtain ⟨U, hU, t, ht⟩ := h s
  obtain ⟨n, hn⟩ := exists_restrict A.hom (transl x).left (Over.w _) U
  refine ⟨U, hU, _, LBxP.isGen_pullAlong L (transl x).left n _ _ _ (fun k => ?_) t ht⟩
  fin_cases k
  · show (_ ≫ _) ≫ _ = n ≫ _ ≫ _
    rw [← Category.assoc n, hn, Category.assoc, Category.assoc]
    exact congrArg (fun q => _ ≫ q.left) (inv_transl hx)
  · exact hn.symm

theorem kTriv_transl {x : 𝟙_ (Over S) ⟶ A} (hx : x * x = 1) {L : LB A.left} (hL : L.IsLB) (h : KTriv A L) :
    KTriv A (L.pull (transl x).left) := by
  intro R _ t y hy
  refine h R t y fun p => ?_
  obtain ⟨V, hV, c, hc⟩ := hy p
  refine ⟨V, hV, ?_⟩
  have hL' := pull_isLB hL (transl x).left
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let T : Over S := Over.mk t
  obtain ⟨n, hn⟩ := exists_restrict (fst T A).left (T ◁ transl x).left
    (congrArg (fun q => q.left) (whiskerLeft_fst T (transl x))) V
  have k₂ : T ◁ transl x ≫ snd T A ≫ transl x = snd T A := by
    rw [whiskerLeft_snd_assoc, transl_transl hx, Category.comp_id]
  have k₃ : T ◁ transl x ≫ ((fst T A ≫ y) * snd T A) ≫ transl x = (fst T A ≫ y) * snd T A := by
    rw [← Category.assoc, MonObj.comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd, comp_transl, comp_transl,
      _root_.mul_assoc, _root_.mul_assoc, toUnit_mul_self hx, _root_.mul_one]
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn (L.pull (transl x).left) _ _ _) c hc
  obtain ⟨c₂, h₂, -⟩ := exists_up hw hL hL' c₁ h₁
  refine gen_chartPull (chartPullOut L _ _ _ _ fun k => ?_) _ (pullGen_isGen _ _ _ c₂ h₂ n)
  show n ≫ (_ ≫ _) ≫ (transl x).left = _
  rw [Category.assoc, ← Category.assoc n, hn, Category.assoc]
  fin_cases k
  exacts [congrArg (fun q => _ ≫ q.left) k₃, congrArg (fun q => _ ≫ q.left) k₂]

end GlobalTheory.PolTranslate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijOfMatch
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ExpansionClause

theorem expBij_of_match : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : PreU (IsLocalRing.maximalIdeal V) D.toPre A G) (U' : UnifPre (IsLocalRing.maximalIdeal V) D A G), Match U U' → ∀ k : ℕ, 1 ≤ k → U.FE (FractionRing V) k → (∀ s : Fam D.toPre (FractionRing V) k, ∃ t, U.ExpF (FractionRing V) k t s.s) → U'.ExpBij k := by
  intro h1 h2 V _ _ _ hV D A G _ _ U U' hM k hk hFE hsurj
  have hT : U'.SecK k = LB.Sec (LB.LinComb U.P.L.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ))) := by
    unfold UnifPre.SecK
    rw [hM.LG]
  have hK := GlobalTheory.GenericFibreSections.sameK_bijective V _ D.toPre A G U k
  have hu := _root_.GlobalTheory.UU.ExpFUniq.main V hV D.toPre A G U (FractionRing V) k
  have ht := _root_.GlobalTheory.UU.ExpTotal.expF_total h1 h2 V hV D.toPre A G U (FractionRing V) k hk
  have e1 := GlobalTheory.T.valueExpansion_of_chartExpansion V _ D A G U U' hM k
  have e2 := GlobalTheory.T.chartExpansion_of_valueExpansion V _ D A G U U' hM k
  unfold UnifPre.ExpBij
  refine ⟨fun σ => ?_, fun s => ?_⟩
  · obtain ⟨t, hσt, -⟩ := hK.1 (cast hT σ)
    obtain ⟨s, hs⟩ := ht t
    refine ⟨⟨s, hFE t s hs⟩, e2 σ _ t _ (cast_heq hT σ).symm hσt hs, fun s' hs' => ?_⟩
    have h := (hu t t s'.s s (e1 σ _ t s' (cast_heq hT σ).symm hσt hs') hs).1 rfl
    obtain ⟨s', fe⟩ := s'
    cases h
    rfl
  · obtain ⟨t, hts⟩ := hsurj s
    obtain ⟨σ₀, hσt, huniq⟩ := hK.2 t
    refine ⟨cast hT.symm σ₀, e2 _ σ₀ t s (cast_heq hT.symm σ₀) hσt hts, fun σ hσ => ?_⟩
    obtain ⟨t', hσt', -⟩ := hK.1 (cast hT σ)
    have h := (hu t' t s.s s.s (e1 σ _ t' s (cast_heq hT σ).symm hσt' hσ) hts).2 rfl
    subst h
    rw [← huniq _ hσt']
    simp

end GlobalTheory.ExpansionClause
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FamilyFunctionalEquationFieldChangeStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyFunctionalEquation_field_change : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] (k : ℕ) (f : ∀ α, SecBT D T k α) (F F' : Type) [Field F] [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F'] (φ : TF (R := R) F ⟶ T) (φ' : TF (R := R) F' ⟶ T) (s : Raw D F k) (s' : Raw D F' k), Function.Injective φ.left.appTop.hom → PullB D F φ k f s → PullB D F' φ' k f s' → DegPre.FamFE D F k s → DegPre.FamFE D F' k s' := by
  first | exact @GlobalTheory.famFE_field_change | exact GlobalTheory.famFE_field_change | (intros; apply GlobalTheory.famFE_field_change <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InducesFrobeniusOnSectionsTranslationIffImage
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

theorem exists_twist_iff {S : Scheme.{0}} {A T : Over S} [GrpObj A] (L : LB A.left) (ψ : T ⊗ A ⟶ T ⊗ A)
    (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (n : ℤ) {W : Type} (g : W → Prop)
    (P : W → (LB.Sec (LPow A L n T) → LB.Sec (LPow A L n T) → Prop) → Prop) :
    (∃ (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (ψ ≫ snd _ _).left] ![n, -n])) (w : W),
      α.IsGen ∧ g w ∧ P w (IsTwistPull A L ψ (ψ ≫ snd _ _) rfl n n α)) ↔
    ∃ (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![n, -n])) (w : W),
      α.IsGen ∧ g w ∧ P w (IsTwistPull A L ψ m hm n n α) := by
  subst hm
  rfl

theorem exists_smul_of_pt_eq (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R]
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℤ)
    (x : TFK (R := R) F ⟶ A.A) (α β : LB.Gen (thetaLB A.A A.L n x)) (hα : α.IsGen) (hβ : β.IsGen) :
    ∃ c : F, c ≠ 0 ∧ ∀ (t : LB.Sec (LPow A.A A.L n (TFK (R := R) F)))
      (u u' : FieldBaseChange.SecOver (FieldBaseChange.abelianBase A F) (LPow A.A A.L n (TFK (R := R) F))),
      IsActOf A.A A.L n ⟨x, α, hα⟩ t u → IsActOf A.A A.L n ⟨x, β, hβ⟩ t u' → u' = c • u := by
  obtain ⟨a, ha⟩ := H1.exists_const A.L A.isLB (fst (TFK (R := R) F) A.A).left (BoxTheta.surj_fst hG A.isAb _)
    (LB.mulGen A.L ![(snd (TFK (R := R) F) A.A).left, (translPt A.A x).left] ![n, -n] _ _ β
      (LB.invGen A.L ![(snd (TFK (R := R) F) A.A).left, (translPt A.A x).left] ![n, -n] α))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hβ (DVR.invGen_isGen _ _ _ _ hα)) (fun U _ h => by
      simp [Fintype.prod_sum_type, Fin.prod_univ_two])
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a
  refine ⟨c, ?_, fun t u u' hu hu' => ?_⟩
  · rintro rfl
    let z : (TFK (R := R) F).left := (default : PrimeSpectrum F)
    choose J hJ using fun χ : (TFK (R := R) F).left ⟶ A.A.left => exists_chart A.isLB (χ z)
    refine Units.ne_zero _ ((ha _ (lift (𝟙 _) x).left z J hJ).trans ?_)
    exact (congrArg _ (map_zero _)).trans (FieldBaseChange.gs_zero' _ z ⊤ trivial)
  · refine FieldBaseChange.SecOver.ext _ _ fun j => sec_ext_val A.isLB (fun y J hJ => ?_) j
    have e := (congrArg Units.val ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _)))).symm.trans
      (ha _ (𝟙 _) y J hJ)
    refine (BoxTheta.act_val _ t u' hu' (𝟙 _) y hJ).trans (Eq.trans ?_
      (FieldBaseChange.sval_smul' hJ (𝟙 _) c u).symm)
    refine Eq.trans ?_ (congrArg₂ (· * ·) e (BoxTheta.act_val _ t u hu (𝟙 _) y hJ).symm)
    exact (congrArg (fun v : ((TFK (R := R) F ⊗ A.A).left.presheaf.stalk y)ˣ => v.val * _)
      (inv_mul_cancel_right _ _).symm).trans ((congrArg (· * _) (Units.val_mul _ _)).trans (_root_.mul_assoc _ _ _))

theorem indAt_translT_iff : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), 1 ≤ N → ∀ (p : QkPt D.toPre F N) (x : TFK (R := R) F ⟶ A.A), IndAt U.toUnifPre F N p (translT A.A x) ↔ QkToAkU U.toUnifPre F N p x := by
  intro hL R _ _ _ I _ D A G _ _ _ U F _ _ _ N hN p x
  have hG := hL.1.globalFns
  have key := fun w₀ : W0 U.toUnifPre => exists_twist_iff A.L (translT A.A x) (translPt A.A x) (lift_snd _ _) (N : ℤ)
    (W := Frm D.toPre F N p.g.b) (fun w => w.IsGen) (fun w Q => ∀ (t t' : SecA A F N) s s',
      U.toUnifPre.ExpandsF F N w₀ t s → U.toUnifPre.ExpandsF F N w₀ t' s' → Q t t' → PhiRel D.toPre F N p w s s')
  constructor
  · rintro ⟨-, H⟩ w₀ hw₀
    obtain ⟨α, w, hα, hw, h⟩ := (key w₀).1 (H w₀ hw₀)
    refine ⟨(hL.1.kerPow _ A N hN _ x).1 fun _ => ⟨⊤, trivial, exists_isGen_pull _ α hα _⟩, ?_⟩
    rintro ⟨y, β, hβ⟩ rfl
    obtain ⟨c, hc, hcs⟩ := exists_smul_of_pt_eq hG A F (N : ℤ) _ α β hα hβ
    obtain ⟨w', hw', hΦ⟩ := ProdTorsion.exists_phiRel_smul hG p w hw c hc
    obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀
    refine ⟨w', hw', fun t t' s s' hs hs' ht => ?_⟩
    obtain ⟨u, hu⟩ := VVRank.exists_isTwistPull A.A (hm := (lift_snd _ _ : translT A.A y ≫ _ = _)) A.isLB hα t
    have e₁ := hΦ _ _ (h t u s _ hs ((he u _).2 rfl) hu)
    have e₂ : s' = c • e u := ((he _ _).1 hs').symm.trans ((congrArg e (hcs t u t' hu ht)).trans (e.map_smul c u))
    exact e₂ ▸ e₁
  · intro H
    refine ⟨lift_fst _ _, fun w₀ hw₀ => (key w₀).2 ?_⟩
    haveI : Subsingleton (TFK (R := R) F).left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
    haveI : Nonempty (TFK (R := R) F).left := inferInstanceAs (Nonempty (PrimeSpectrum F))
    obtain ⟨θ, rfl⟩ := BoxTheta.exists_theta hL.1.kerPow A hN x (H w₀ hw₀).1
    obtain ⟨w, hw, h⟩ := (H w₀ hw₀).2 θ rfl
    exact ⟨θ.φ, w, θ.isGen, hw, h⟩

end GlobalTheory.UT
end

