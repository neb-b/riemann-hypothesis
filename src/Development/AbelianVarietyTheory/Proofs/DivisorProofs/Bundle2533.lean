module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2457
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubeFaceMiddleProjProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2451
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0498
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0467
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationDegenerationDataUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordLambdaBilinearIntegralCombinations
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoefficientsDescendFiniteFreeAffineOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FrameCoeff

variable {R R₁ : Type} [CommRing R] [CommRing R₁]

theorem exists_basis (ρ₁ : R →+* R₁) {d : ℕ} (b : Fin d → R₁)
    (hb : ∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) :
    letI := ρ₁.toAlgebra; ∃ B : Module.Basis (Fin d) R R₁, ⇑B = b := by
  letI := ρ₁.toAlgebra
  have hs : ∀ (c : R) (x : R₁), c • x = ρ₁ c * x := fun c x => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  have hli : LinearIndependent R b := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    have h1 : (0 : R₁) = ∑ l, ρ₁ (g l) * b l := by
      rw [← hg]; simp only [hs]
    have h2 : (0 : R₁) = ∑ l, ρ₁ ((0 : Fin d → R) l) * b l := by simp
    exact congrFun ((hb 0).unique h1 h2) i
  refine ⟨Module.Basis.mk hli ?_, Module.Basis.coe_mk _ _⟩
  intro r _
  obtain ⟨c, hc, -⟩ := hb r
  rw [hc]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [← hs]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

theorem gs_zero0 {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

variable {X Z : Scheme.{0}}

theorem aff_coeff (ρ₁ : R →+* R₁) {d : ℕ} (b : Fin d → R₁)
    (hb : ∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l)
    {f : X ⟶ Sp R} {q : Z ⟶ X} {p : Z ⟶ Sp R₁} (H : IsPullback q p f (spMap ρ₁))
    {V : X.Opens} (hV : IsAffineOpen V) :
    (∀ t : Γ(Z, q ⁻¹ᵁ V), ∃ a : Fin d → Γ(X, V),
      t = ∑ l, GlobalTheory.AbLaw.cst p (q ⁻¹ᵁ V) (b l) * (q.app V).hom (a l)) ∧
    (∀ a : Fin d → Γ(X, V), ∑ l, GlobalTheory.AbLaw.cst p (q ⁻¹ᵁ V) (b l) * (q.app V).hom (a l) = 0 → a = 0) := by
  classical
  letI := ρ₁.toAlgebra
  obtain ⟨B, hB⟩ := exists_basis ρ₁ b hb
  have hg : ρ₁.Flat := by
    have : Module.Free R R₁ := Module.Free.of_basis B
    exact (inferInstance : Module.Flat R R₁)
  letI : Algebra R Γ(X, V) := (GlobalTheory.AbLaw.cst f V).toAlgebra
  obtain ⟨e, he⟩ := GlobalTheory.FlatSec.exists_equiv_of_isPushout (R := R) (q.app V) (GlobalTheory.AbLaw.cst p (q ⁻¹ᵁ V))
    (GlobalTheory.FlatSec.isPushout_app hg H hV.isCompact hV.isQuasiSeparated)
  have hsum : ∀ a : Fin d → Γ(X, V), e (∑ l, B l ⊗ₜ[R] a l) =
      ∑ l, GlobalTheory.AbLaw.cst p (q ⁻¹ᵁ V) (b l) * (q.app V).hom (a l) := by
    intro a; rw [map_sum]; simp only [he, hB]
  constructor
  · intro t
    refine ⟨fun l => TensorProduct.equivFinsuppOfBasisLeft B (e.symm t) l, ?_⟩
    rw [← hsum]
    have h := TensorProduct.equivFinsuppOfBasisLeft_symm_apply B (TensorProduct.equivFinsuppOfBasisLeft B (e.symm t))
    rw [LinearEquiv.symm_apply_apply, Finsupp.sum_fintype _ _ (by simp)] at h
    rw [← h, AddEquiv.apply_symm_apply]
  · intro a ha
    rw [← hsum] at ha
    have h0 : ∑ l, B l ⊗ₜ[R] a l = 0 := e.injective (ha.trans (map_zero e).symm)
    funext k
    have := congrArg (fun w => TensorProduct.equivFinsuppOfBasisLeft B w k) h0
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, Module.Basis.repr_self,
      Finsupp.single_apply] using this

end GlobalTheory.FrameCoeff

namespace GlobalTheory.FrameCoeff

variable {R R₁ : Type} [CommRing R] [CommRing R₁] {X Z : Scheme.{0}}

theorem gs_cst_top (p : Z ⟶ Sp R₁) (z : Z) (c : R₁) :
    gs (𝟙 Z) z ⊤ (GlobalTheory.AbLaw.cst p ⊤ c) = gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom c) := by
  have h1 := gs_res (𝟙 Z) z (le_top : (⊤ : Z.Opens) ≤ p ⁻¹ᵁ ⊤) trivial ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom c))
  have h2 := gs_pull (𝟙 Z) p z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom c)
  rw [Category.id_comp] at h2
  exact h1.trans h2

theorem gs_comb_pt {d : ℕ} (b : Fin d → R₁) (p : Z ⟶ Sp R₁) (q : Z ⟶ X) (V : X.Opens) (z : Z) (hz : q z ∈ V)
    (a : Fin d → Γ(X, V)) :
    gs (𝟙 Z) z (q ⁻¹ᵁ V) (∑ l, GlobalTheory.AbLaw.cst p (q ⁻¹ᵁ V) (b l) * (q.app V).hom (a l)) =
      ∑ l, gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs q z V (a l) := by
  rw [GlobalTheory.FlatSec.gs_comb p q V z hz b a]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [gs_cst_top]

theorem exists_aff (U : X.Opens) (x : X) (hx : x ∈ U) : ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ U := by
  obtain ⟨V, hV, hxV, hVU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
  exact ⟨V, hV, hxV, hVU⟩

end GlobalTheory.FrameCoeff

namespace GlobalTheory.FrameCoeff

variable {R R₁ : Type} [CommRing R] [CommRing R₁] {X Z : Scheme.{0}}

theorem inj_gen (ρ₁ : R →+* R₁) {d : ℕ} (b : Fin d → R₁)
    (hb : ∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l)
    {f : X ⟶ Sp R} {q : Z ⟶ X} {p : Z ⟶ Sp R₁} (H : IsPullback q p f (spMap ρ₁))
    (U : X.Opens) (a : Fin d → Γ(X, U))
    (h : ∀ z : Z, q z ∈ U →
      ∑ l, gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs q z U (a l) = 0) :
    ∀ l, a l = 0 := by
  intro l
  apply fn_ext
  intro x hx
  obtain ⟨V, hV, hxV, hVU⟩ := exists_aff U x hx
  have h0 := (aff_coeff ρ₁ b hb H hV).2 (fun l => GlobalTheory.AbLaw.rs X hVU (a l)) (fn_ext fun z hz => by
    rw [gs_comb_pt b p q V z hz, gs_zero0]
    refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) (h z (hVU hz))
    rw [gs_res q z hVU hz])
  have e := congrFun h0 l
  have e2 := gs_res (𝟙 X) x hVU hxV (a l)
  simp only [Pi.zero_apply] at e
  rw [← e2]
  erw [e]
  rw [gs_zero0, gs_zero0]

theorem surj_gen (ρ₁ : R →+* R₁) {d : ℕ} (b : Fin d → R₁)
    (hb : ∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l)
    {f : X ⟶ Sp R} {q : Z ⟶ X} {p : Z ⟶ Sp R₁} (H : IsPullback q p f (spMap ρ₁))
    (U : X.Opens) (t : Γ(Z, q ⁻¹ᵁ U)) :
    ∃ a : Fin d → Γ(X, U), ∀ z : Z, q z ∈ U →
      gs (𝟙 Z) z (q ⁻¹ᵁ U) t =
        ∑ l, gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs q z U (a l) := by
  classical
  choose V hV hxV hVU using fun x : U => exists_aff U x.1 x.2
  have hle : ∀ x, q ⁻¹ᵁ V x ≤ q ⁻¹ᵁ U := fun x z hz => hVU x hz
  choose c hc using fun x : U => (aff_coeff ρ₁ b hb H (hV x)).1 (GlobalTheory.AbLaw.rs Z (hle x) t)
  have hcg : ∀ x z, q z ∈ V x → gs (𝟙 Z) z (q ⁻¹ᵁ U) t =
      ∑ l, gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs q z (V x) (c x l) := by
    intro x z hz
    rw [← gs_res (𝟙 Z) z (hle x) hz t, ← gs_comb_pt b p q (V x) z hz]
    exact congrArg _ (hc x)
  have hcomp : ∀ l x y, GlobalTheory.AbLaw.rs X (inf_le_left : V x ⊓ V y ≤ V x) (c x l) =
      GlobalTheory.AbLaw.rs X (inf_le_right : V x ⊓ V y ≤ V y) (c y l) := by
    intro l x y
    refine sub_eq_zero.1 (inj_gen ρ₁ b hb H (V x ⊓ V y)
      (fun l => GlobalTheory.AbLaw.rs X inf_le_left (c x l) - GlobalTheory.AbLaw.rs X inf_le_right (c y l)) (fun z hz => ?_) l)
    have e : ∀ l, gs q z (V x ⊓ V y) (GlobalTheory.AbLaw.rs X inf_le_left (c x l) - GlobalTheory.AbLaw.rs X inf_le_right (c y l)) =
        gs q z (V x) (c x l) - gs q z (V y) (c y l) := fun l => by
      rw [gs_eq q z _ hz, map_sub, map_sub, ← gs_eq q z _ hz, ← gs_eq q z _ hz, gs_res q z _ hz, gs_res q z _ hz]
    simp only [e, mul_sub, Finset.sum_sub_distrib]
    rw [← hcg x z hz.1, ← hcg y z hz.2, sub_self]
  have hcov : U ≤ iSup V := fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  choose s hs using fun l => X.sheaf.existsUnique_gluing' V U (fun x => homOfLE (hVU x)) hcov
    (fun x => c x l) (fun x y => hcomp l x y)
  refine ⟨s, fun z hz => ?_⟩
  rw [hcg ⟨q z, hz⟩ z (hxV ⟨q z, hz⟩)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← (hs l).1 ⟨q z, hz⟩]
  exact congrArg _ (gs_res q z (hVU ⟨q z, hz⟩) (hxV ⟨q z, hz⟩) (s l))

end GlobalTheory.FrameCoeff

namespace GlobalTheory.FrameCoeff

variable {R R₁ : Type} [CommRing R] [CommRing R₁] {X Z : Scheme.{0}}

theorem main_gen (ρ₁ : R →+* R₁) {d : ℕ} (b : Fin d → R₁)
    (hb : ∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l)
    {f : X ⟶ Sp R} {q : Z ⟶ X} {p : Z ⟶ Sp R₁} (H : IsPullback q p f (spMap ρ₁))
    (L : LB X) (W O : X.Opens) (hOW : O ≤ W)
    (τ : ∀ k : L.ι, Γ(Z, q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k)ˣ) (hτ : FrameAlong L q (q ⁻¹ᵁ W) τ) :
    ∃ s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k), (∀ l, IsSecOver L O (s l)) ∧
      ∀ (z : Z) (k : L.ι), q z ∈ O → q z ∈ L.U k →
        gs (𝟙 Z) z (q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k) (τ k).val =
          ∑ l, gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs q z (O ⊓ L.U k) (s l k) := by
  have hle : ∀ k, q ⁻¹ᵁ (O ⊓ L.U k) ≤ q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k := fun k z hz => ⟨hOW hz.1, hz.2⟩
  choose a ha using fun k => surj_gen ρ₁ b hb H (O ⊓ L.U k) (GlobalTheory.AbLaw.rs Z (hle k) (τ k).val)
  have hτg : ∀ k z, q z ∈ O ⊓ L.U k → gs (𝟙 Z) z (q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k) (τ k).val =
      ∑ l, gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs q z (O ⊓ L.U k) (a k l) := by
    intro k z hz
    rw [← gs_res (𝟙 Z) z (hle k) hz]
    exact ha k z hz
  refine ⟨fun l k => a k l, fun l => ?_, fun z k hO hk => hτg k z ⟨hO, hk⟩⟩
  intro x k k' hx hk hk'
  have hV : O ⊓ L.U k ≤ L.U k := inf_le_right
  have hW : O ⊓ L.U k' ≤ L.U k' := inf_le_right
  have h0 := inj_gen ρ₁ b hb H ((O ⊓ L.U k) ⊓ (O ⊓ L.U k'))
    (fun l => GlobalTheory.AbLaw.rs X inf_le_left (a k l) -
      GlobalTheory.AbLaw.rs X (inf_le_inf hV hW) (L.g k k').val * GlobalTheory.AbLaw.rs X inf_le_right (a k' l)) (fun z hz => ?_) l
  · have e := congrArg (gs (𝟙 X) x _) h0
    rw [GlobalTheory.FlatSec.gs_diff hV hW (a k l) (a k' l) (𝟙 X) x ⟨⟨hx, hk⟩, ⟨hx, hk'⟩⟩, gs_zero0] at e
    exact sub_eq_zero.1 e
  · have e1 : ∀ l, gs q z _ (GlobalTheory.AbLaw.rs X inf_le_left (a k l) -
        GlobalTheory.AbLaw.rs X (inf_le_inf hV hW) (L.g k k').val * GlobalTheory.AbLaw.rs X inf_le_right (a k' l)) =
        gs q z _ (a k l) - (gm q z (L.U k ⊓ L.U k') (L.g k k')).val * gs q z _ (a k' l) :=
      fun l => GlobalTheory.FlatSec.gs_diff hV hW _ _ q z hz
    simp only [e1, mul_sub, Finset.sum_sub_distrib]
    have hfr := congrArg Units.val (hτ z k k' (hOW hz.1.1) hz.1.2 hz.2.2)
    rw [Units.val_mul, ← gs_unit (𝟙 Z) z (q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k) ⟨hOW hz.1.1, hz.1.2⟩ (τ k),
      ← gs_unit (𝟙 Z) z (q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k') ⟨hOW hz.1.1, hz.2.2⟩ (τ k'),
      hτg k z hz.1, hτg k' z hz.2] at hfr
    rw [hfr, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun l _ => by ring

end GlobalTheory.FrameCoeff

theorem GlobalTheory.FrameCoeff.frame_coeff : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁), (∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) → ∀ (X : Scheme.{0}) (f : X ⟶ Sp R) (L : LB X), L.IsLB → ∀ (W O : X.Opens), O ≤ W → IsAffineOpen O → ∀ (τ : ∀ k : L.ι, Γ((pullback f (spMap ρ₁)), (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k)ˣ), FrameAlong L (pullback.fst f (spMap ρ₁)) ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W) τ → ∃ s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k), (∀ l, IsSecOver L O (s l)) ∧ ∀ (z : (pullback f (spMap ρ₁) : Scheme.{0})) (k : L.ι), (pullback.fst f (spMap ρ₁)) z ∈ O → (pullback.fst f (spMap ρ₁)) z ∈ L.U k → gs (𝟙 (pullback f (spMap ρ₁))) z ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z (O ⊓ L.U k) (s l k) := by
  intro R R₁ _ _ ρ₁ d b hb X f L hL W O hOW hO τ hτ
  exact GlobalTheory.FrameCoeff.main_gen ρ₁ b hb (IsPullback.of_hasPullback f (spMap ρ₁)) L W O hOW τ hτ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GAdjSndOfIsProdUnif
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd.SndAdj

open GlobalTheory.CechPic

theorem psum_comp_hom {S : Scheme.{0}} {T H H' : Over S} [GrpObj H] [IsCommMonObj H] [GrpObj H'] [IsCommMonObj H']
    (f : H ⟶ H') [IsMonHom f] {n : ℕ} (x : Fin n → (T ⟶ H)) (I : Finset (Fin n)) :
    psum H x I ≫ f = psum H' (fun i => x i ≫ f) I :=
  psum_hom (MonoidHom.mk' (· ≫ f) fun a b => MonObj.mul_comp a b f) x I

theorem sum_cube_zero {S : Scheme.{0}} {T H : Over S} [GrpObj H] [IsCommMonObj H] {M : Type*} [AddCommGroup M]
    (F : (T ⟶ H) → M) (y : Fin 2 → (T ⟶ H)) (hy : y 0 = 1) :
    ∑ I : ULift.{0} (Finset (Fin 2)), ((-1 : ℤ) ^ (2 - I.down.card)) • F (psum H y I.down) = 0 := by
  refine (Fintype.sum_equiv Equiv.ulift _ (fun I : Finset (Fin 2) => ((-1 : ℤ) ^ (2 - I.card)) • F (psum H y I))
    (fun _ => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide]
  simp only [ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums.psum_eq_prod]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [hy]

theorem gAdj_snd_of_isProdUnif : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂ → GAdj U₂.LG.L U.LG.L (lift 1 (𝟙 G₂)) (snd G₁ G₂) := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D A U p₁ p₂ q₁ q₂ a₁ a₂ hU
  obtain ⟨w, hw⟩ := hU.wL
  have hL := U.LG.isLB
  have hL₁ := U₁.LG.isLB
  have hL₂ := U₂.LG.isLB
  have hE : (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left).IsLB :=
    isLB_tens (pull_isLB hL₁ _) (pull_isLB hL₂ _)
  have cL : cls _ hL = CechPic.pull (fst G₁ G₂).left (cls _ hL₁) + CechPic.pull (snd G₁ G₂).left (cls _ hL₂) :=
    (cls_eq_iff hL hE).2 ⟨w, hw⟩
  unfold GAdj cubeLB
  refine (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL₂ _ _)).1 ?_
  rw [cls_linComb hL, cls_linComb hL₂, cL]
  simp only [map_add (f := _), ← CechPic.pull_comp, smul_add, Finset.sum_add_distrib]
  have h₁ : ∀ J : Finset (Fin 2), (psum (G₁ ⊗ G₂) ![fst G₂ (G₁ ⊗ G₂) ≫ lift 1 (𝟙 G₂), snd G₂ (G₁ ⊗ G₂)] J).left ≫
      (fst G₁ G₂).left = (psum G₁ ![1, snd G₂ (G₁ ⊗ G₂) ≫ fst G₁ G₂] J).left := fun J => by
    rw [← Over.comp_left, psum_comp_hom]
    congr 2
    funext i
    fin_cases i <;> simp
  have h₂ : ∀ J : Finset (Fin 2), (psum (G₁ ⊗ G₂) ![fst G₂ (G₁ ⊗ G₂) ≫ lift 1 (𝟙 G₂), snd G₂ (G₁ ⊗ G₂)] J).left ≫
      (snd G₁ G₂).left = (psum G₂ ![fst G₂ (G₁ ⊗ G₂), snd G₂ (G₁ ⊗ G₂) ≫ snd G₁ G₂] J).left := fun J => by
    rw [← Over.comp_left, psum_comp_hom]
    congr 2
    funext i
    fin_cases i <;> simp
  simp only [h₁, h₂]
  exact add_eq_right.2 (sum_cube_zero
    (fun u : G₂ ⊗ G₁ ⊗ G₂ ⟶ G₁ => CechPic.pull u.left (cls _ hL₁)) ![1, snd G₂ (G₁ ⊗ G₂) ≫ fst G₁ G₂] rfl)

end GlobalTheory.MumProd.SndAdj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisConjQExpansionFamilyDiagOneUnit
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam

namespace GlobalTheory.HilbFam.GalFamily

theorem ch_one (N : ℕ) [NeZero N] : ch N 1 = Complex.exp ((2 * Real.pi * Complex.I) / N) := by
  unfold ch
  rcases Nat.lt_or_ge 1 N with h | h
  · haveI : Fact (1 < N) := ⟨h⟩
    rw [ZMod.val_one]; simp
  · have hN : N = 1 := by have := NeZero.pos N; omega
    subst hN
    have : (1 : ZMod 1).val = 0 := rfl
    rw [this]; simp [Complex.exp_two_pi_mul_I]

theorem diag_eq {N : ℕ} [NeZero N] (a : (ZMod N)ˣ) :
    Matrix.diagonal ![1, ((((a : ZMod N).val : ℕ) : ℤ) : ZMod N)] = ((dg a : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg]

theorem qConj_family : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ) (κ κ' : Emb F → ℕ) (y : Fin 2 → ZMod N), ZetaAct g N a → (∀ i j : Emb F, (∀ x : F, g ((i x : ℝ) : ℂ) = ((j x : ℝ) : ℂ)) → κ' j = κ i) → y ≠ 0 → ∀ α : GL (Fin 2) (ZMod N), QConj g N (hfun (2 * s) (twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ (wB N (vmul y (α)))) (hfun (2 * s) (twist N L ((α * dg a : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ' (wB N (vmul y (α * dg a)))) := by
  intro hE F _ _ _ hf s N _ L hs hL z hz g a κ κ' y hg hκ hy α
  have hact := GlobalTheory.WpFam.Act.rightActions N
  have hy' : vmul y α ≠ 0 := fun h ↦ hy ((hact.2.2.2.2.1 y α).1 h)
  have hq := (_root_.GlobalTheory.WpFam.ConjExp.qConj_torsion N g a hg (vmul y α)).2.2 hy'
  rw [hact.2.2.1] at hq
  have hcop : IsCoprime (((a : ZMod N).val : ℕ) : ℤ) (N : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (ZMod.val_coe_unit_coprime a)
  have hz1 : g (Complex.exp ((2 * Real.pi * Complex.I) / N)) =
      Complex.exp ((2 * Real.pi * Complex.I) * ((((a : ZMod N).val : ℕ) : ℤ) : ℂ) / N) := by
    rw [← ch_one, hg 1, mul_one, ch, Int.cast_natCast]
  have h := _root_.GlobalTheory.HilbFam.qConj_hfun_twist hE F hf s N (twist N L (α : Matrix (Fin 2) (Fin 2) (ZMod N))) hs (NeZero.pos N)
    (GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel F N L _ hL) z hz g _ κ κ' _ _ hcop hz1 hκ hq
  rw [diag_eq, _root_.GlobalTheory.HilbFam.TwistMul.twist_twist F N L _ _ hL.2, ← Units.val_mul] at h
  exact h

end GlobalTheory.HilbFam.GalFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisFixesQuotientPointsOfRational
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GalFixQ

open GlobalTheory.TorusExt

theorem qkExt_equiv_of_rational : ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (D₂ : DegData R₂ (maximalIdeal R₂)) (n : ℕ), (∀ p : QkPt D₂.toPre (Kb R₂) n, ∃ (p₀ : QkPt D₂.toPre (FractionRing R₂) n) (p₁ : QkPt D₂.toPre (Kb R₂) n), QkExt (algebraMap (FractionRing R₂) (Kb R₂)) p₀ p₁ ∧ QkPt.Equiv D₂.toPre (Kb R₂) p₁ p) → ∀ σ : Kb R₂ →ₐ[FractionRing R₂] Kb R₂, ∀ p p' : QkPt D₂.toPre (Kb R₂) n, QkExt σ.toRingHom p p' → QkPt.Equiv D₂.toPre (Kb R₂) p p' := by
  intro R₂ _ _ _ D₂ n hrat σ p p' hpp'
  have hB := D₂.tau_bimult
  have hf : σ.toRingHom.comp (algebraMap (FractionRing R₂) (Kb R₂)) = algebraMap (FractionRing R₂) (Kb R₂) :=
    σ.comp_algebraMap
  have ha : (algebraMap (FractionRing R₂) (Kb R₂)).comp (algebraMap (FractionRing R₂) (FractionRing R₂)) =
      algebraMap (FractionRing R₂) (Kb R₂) := by
    rw [Algebra.algebraMap_self, RingHom.comp_id]
  obtain ⟨p₀, p₁, e₁, h₁⟩ := hrat p
  have hq : QkExt σ.toRingHom p₁ (qkExt hB σ.toRingHom hf p₁) := (qkExt_iff hB _ hf _ _).2 rfl
  have e₂ := GlobalTheory.LabTrans.qkExt_trans e₁ hq
  rw [hf] at e₂
  have hfix : qkExt hB σ.toRingHom hf p₁ = p₁ :=
    ((qkExt_iff hB _ ha _ _).1 e₂).trans ((qkExt_iff hB _ ha _ _).1 e₁).symm
  rw [hfix] at hq
  exact equiv_trans hB (equiv_symm hB h₁) (equiv_of_qkExt hB σ.toRingHom hf hq hpp' h₁)

end GlobalTheory.Mum.GalFixQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorValEqOneOfGenericSpecDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.GenOne

theorem unit_eq_one_of_generic (R : Type) [CommRing R] [IsDomain R] (V : (Spec (CommRingCat.of R)).Opens) (hV : V = ⊤)
    (a : Γ(Spec (CommRingCat.of R), V)ˣ) (h : ∀ z, gm (jK R) z V a = 1) : a = 1 := by
  subst hV
  have h1 : pullU (jK R) ⊤ a = 1 := by
    refine unit_ext fun x _ => ?_
    rw [map_one, gm_pull (𝟙 _) (jK R) x ⊤ trivial, Category.id_comp]
    exact h x
  have h2 : (jK R).appTop.hom (a : Γ(Spec (CommRingCat.of R), ⊤)) = 1 := congrArg Units.val h1
  have h3 := congrArg (fun f => f.hom (a : Γ(Spec (CommRingCat.of R), ⊤)))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h3
  rw [h2, map_one] at h3
  have h4 : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (a : Γ(Spec (CommRingCat.of R), ⊤)) = 1 :=
    IsFractionRing.injective R (FractionRing R) (by rw [map_one]; exact h3.symm)
  apply Units.ext
  apply (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective
  rw [Units.val_one, map_one]
  exact h4

theorem val_eq_one_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] {X : Scheme.{0}} (L : LB X), L.IsLB → ∀ {K : Type} [Fintype K] (φ : K → (Spec (CommRingCat.of R) ⟶ X)) (ε : K → ℤ), FormEq φ ε (PEmpty.elim : PEmpty → (Spec (CommRingCat.of R) ⟶ X)) (PEmpty.elim : PEmpty → ℤ) → ∀ t : LB.Gen (LB.LinComb L φ ε), t.IsGen → (∀ (z : (TK R).left) (J : ((TK R).left ⟶ X) → L.ι), Good L z J → val t (jK R) z J = 1) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J → val t r z J = 1 := by
  intro R _ _ X L hL K _ φ ε hF t ht hgen Z r z J hJ
  obtain ⟨t', -, hv⟩ := exists_gen hL hF t ht
  have htop : ∀ j : PEmpty → L.ι,
      L.wchart (PEmpty.elim : PEmpty → (Spec (CommRingCat.of R) ⟶ X)) j = ⊤ := by
    intro j
    simp [LB.wchart]
  have key : ∀ j, t'.s j = 1 := by
    intro j
    refine unit_eq_one_of_generic R _ (htop j) _ fun y => ?_
    choose J' hJ' using fun ψ : (TK R).left ⟶ X => exists_chart hL (ψ y)
    have h1 := (hv _ (jK R) y J' hJ').trans (hgen y J' hJ')
    have e : j = fun k => J' (jK R ≫ (PEmpty.elim : PEmpty → (Spec (CommRingCat.of R) ⟶ X)) k) :=
      funext fun k => k.elim
    subst e
    exact h1
  rw [← hv Z r z J hJ]
  exact (congrArg (gm r z _) (key _)).trans (map_one _)

end GlobalTheory.Mum.GenOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointMapOverRingHomUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem genPt_map_unique {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V)
    (κ κ' : Sp (FractionRing V) ⟶ Sp (FractionRing R)) (h : κ ≫ jK R = jK V ≫ spMap θ)
    (h' : κ' ≫ jK R = jK V ≫ spMap θ) : κ = κ' := by
  obtain ⟨a, rfl⟩ : ∃ a, Spec.map a = κ := ⟨_, Spec.map_preimage κ⟩
  obtain ⟨a', rfl⟩ : ∃ a, Spec.map a = κ' := ⟨_, Spec.map_preimage κ'⟩
  have e : Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ a) =
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ a') := by
    rw [Spec.map_comp, Spec.map_comp]
    exact h.trans h'.symm
  have e2 := Spec.map_injective e
  congr 1
  ext1
  apply IsLocalization.ringHom_ext (nonZeroDivisors R)
  exact congrArg CommRingCat.Hom.hom e2

end GlobalTheory.TInj
end

