module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0151

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjOfDescendedData
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaDescent

theorem map_prod_pow {M N : Type*} [Monoid M] [Monoid N] (P : M →* N) {n : ℕ} (p : Fin n → M) (a : Fin n → ℕ) :
    P (List.ofFn fun i => p i ^ a i).prod = (List.ofFn fun i => P (p i) ^ a i).prod := by
  simp only [map_list_prod, List.map_ofFn, Function.comp_def, map_pow]

theorem existsUnique_transfer {M M₀ N C : Type*} [Monoid M] [Monoid M₀] [Monoid N] (P : M →* N) (R : M₀ →* N)
    (hP : Function.Bijective P) (hR : Function.Injective R) {n : ℕ} (p : Fin n → M) (p₀ : Fin n → M₀)
    (h : ∀ i, P (p i) = R (p₀ i)) (k : ℕ) (e : C → Fin n → ℕ)
    (H : ∀ y : M, y ^ k = 1 → ∃! c : C, (List.ofFn fun i => p i ^ e c i).prod = y)
    (y₀ : M₀) (hy : y₀ ^ k = 1) : ∃! c : C, (List.ofFn fun i => p₀ i ^ e c i).prod = y₀ := by
  obtain ⟨y, hyR⟩ := hP.2 (R y₀)
  have hyk : y ^ k = 1 := hP.1 (by rw [map_pow, hyR, ← map_pow, hy, map_one, map_one])
  have key : ∀ c : C, (List.ofFn fun i => p₀ i ^ e c i).prod = y₀ ↔ (List.ofFn fun i => p i ^ e c i).prod = y := by
    intro c
    rw [← hR.eq_iff, ← hP.1.eq_iff, hyR, map_prod_pow, map_prod_pow]
    simp only [h]
  simpa only [key] using H y hyk

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem pushHom_left (h : IsGrpPullback G' G f φ) (T : Over S') (x : T ⟶ G') :
    (pushHom h T x).left = x.left ≫ φ := rfl

theorem pushHom_bijective (h : IsGrpPullback G' G f φ) (T : Over S') : Function.Bijective (pushHom h T) := by
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · have e := congrArg (fun u => u.left) hxy
    simp only [pushHom_left] at e
    exact Over.OverMorphism.ext (h.1.hom_ext e (by rw [Over.w x, Over.w y]))
  · refine ⟨Over.homMk (h.1.lift z.left T.hom (Over.w z)) (h.1.lift_snd _ _ _), ?_⟩
    ext1
    rw [pushHom_left]
    exact h.1.lift_fst _ _ _

theorem preHom_injective {T T' : Over S} (U : T' ⟶ T) [Epi U.left] :
    Function.Injective (preHom (G := G) U) := by
  intro x y hxy
  ext1
  rw [← cancel_epi U.left, ← Over.comp_left, ← Over.comp_left]
  exact congrArg (fun u => u.left) hxy

theorem weilIs_congr {Z : Scheme.{0}} {s s' : Z ⟶ S} (e : s = s') (L : LB G.left) (k : ℤ)
    (x y : Over.mk s ⟶ G) (x' y' : Over.mk s' ⟶ G) (hx : x.left = x'.left) (hy : y.left = y'.left)
    (c : Γ(Z, ⊤)ˣ) : Out.WeilIs G L k x y c ↔ Out.WeilIs G L k x' y' c := by
  subst e
  obtain rfl : x = x' := Over.OverMorphism.ext hx
  obtain rfl : y = y' := Over.OverMorphism.ext hy
  exact Iff.rfl

theorem unitS_spMap {o R : Type} [CommRing o] [CommRing R] (β : o →+* R) (u : oˣ) (n : ℤ) :
    unitS (spMap β) u ^ n = unitOn (Units.map β.toMonoidHom u ^ n) := by
  unfold unitS unitOn
  simp only [← map_zpow]
  ext1
  simp only [Units.coe_map]
  exact (congrArg (fun g => CommRingCat.Hom.hom g ((u ^ n : oˣ) : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm

theorem epi_spMap {K Ω : Type} [Field K] [Field Ω] (j : K →+* Ω) : Epi (spMap j) := by
  have := (GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K Ω j).1 (Sp K) (Sp Ω) (𝟙 _) (𝟙 _) (spMap j)
    (IsPullback.of_vert_isIso ⟨by simp⟩)
  exact this.1

end GlobalTheory.ThetaDescent

namespace GlobalTheory

open ThetaDescent

theorem exists_thetaObj_of_descended_data : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (β₀ : o →+* K₀) (β : o →+* K) (t : TObj g k J b (spMap β)) (A₀ : Over (Sp K₀)) [GrpObj A₀] (φ : t.A.left ⟶ A₀.left) (L₀ : LB A₀.left) (pt₀ : Fin (2 * g) → (Out.baseOver (Sp K₀) ⟶ A₀)) (act₀ : J → (A₀ ⟶ A₀)), i.comp β₀ = β → IsGrpPullback t.A A₀ (spMap i) φ → L₀.IsLB → LBIso t.L (L₀.pull φ) → (∀ a, (t.pt a).left ≫ φ = spMap i ≫ (pt₀ a).left) → (∀ j, (t.act j).left ≫ φ = φ ≫ (act₀ j).left) → ∃ t₀ : TObj g k J b (spMap β₀), TMap t t₀ (spMap i) := by
  intro o _ g k J b K₀ K _ _ i β₀ β t A₀ _ φ L₀ pt₀ act₀ hβ hpb hL₀ hLiso hpt hact
  obtain ⟨hab, hdim⟩ := _root_.GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend K₀ K i A₀ t.A φ hpb t.ab
  obtain ⟨hrig, hsym, hkt⟩ := _root_.GlobalTheory.PolDescent.rigidified_sym_kTriv_descend K₀ K i A₀ t.A φ L₀ t.L hab hpb hL₀ t.isLB hLiso
  have hamp := GlobalTheory.AmpleDescent.relAmple_of_fieldExtension K₀ K i A₀ t.A φ L₀ t.L hab hpb hL₀ t.isLB hLiso t.ample
  have hmon := (GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K₀ K i).2
  refine ⟨{ A := A₀, ab := hab, dim := hdim g t.dim, L := L₀, isLB := hL₀
            rigid := hrig t.rigid, sym := hsym (TObj.sym t), ample := hamp, ktriv := hkt t.ktriv
            pt := pt₀, torsion := ?_, bij := ?_, pairing := ?_, act := act₀
            hom := fun j => (hmon A₀ A₀ t.A t.A φ φ (act₀ j) (t.act j) hpb hpb (hact j).symm).1 (t.hom j) },
    φ, hpb, hLiso, hpt, hact⟩
  ·
    intro a
    obtain ⟨U0, hU0⟩ : ∃ U0 : Over.mk ((Out.baseOver (Sp K)).hom ≫ spMap i) ⟶ Out.baseOver (Sp K₀),
        U0.left = spMap i := ⟨Over.homMk (spMap i) (by simp), rfl⟩
    have hE : Epi U0.left := by rw [hU0]; exact epi_spMap i
    apply preHom_injective U0
    have e1 : preHom U0 (pt₀ a) = pushHom hpb _ (t.pt a) := by
      ext1
      show (U0 ≫ pt₀ a).left = _
      rw [Over.comp_left, hU0, pushHom_left, hpt a]
    rw [map_pow, map_one, e1, ← map_pow, t.torsion a, map_one]
  ·
    intro K' _ _ x y hy
    obtain ⟨χ, rfl⟩ : ∃ χ : K₀ →+* K', spMap χ = x := ⟨(Spec.preimage x).hom, by
      show Spec.map (CommRingCat.ofHom _) = x
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
    obtain ⟨Ω, _, _, jK, jL, hcomm⟩ : ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (jK : K →+* Ω) (jL : K' →+* Ω),
        jK.comp i = jL.comp χ := by
      let _ : Algebra K₀ K := i.toAlgebra
      let _ : Algebra K₀ K' := χ.toAlgebra
      have : Nontrivial (K ⊗[K₀] K') :=
        Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K₀ K K' i.injective χ.injective
      obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[K₀] K')
      let _ := Ideal.Quotient.field m
      refine ⟨AlgebraicClosure (K ⊗[K₀] K' ⧸ m), inferInstance, inferInstance,
        ((algebraMap (K ⊗[K₀] K' ⧸ m) (AlgebraicClosure (K ⊗[K₀] K' ⧸ m))).comp (Ideal.Quotient.mk m)).comp
          (Algebra.TensorProduct.includeLeft : K →ₐ[K₀] K ⊗[K₀] K').toRingHom,
        ((algebraMap (K ⊗[K₀] K' ⧸ m) (AlgebraicClosure (K ⊗[K₀] K' ⧸ m))).comp (Ideal.Quotient.mk m)).comp
          (Algebra.TensorProduct.includeRight : K' →ₐ[K₀] K ⊗[K₀] K').toRingHom, ?_⟩
      ext r
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      have h1 := (Algebra.TensorProduct.includeLeft : K →ₐ[K₀] K ⊗[K₀] K').commutes r
      have h2 := (Algebra.TensorProduct.includeRight : K' →ₐ[K₀] K ⊗[K₀] K').commutes r
      exact congrArg (fun z => algebraMap (K ⊗[K₀] K' ⧸ m) (AlgebraicClosure (K ⊗[K₀] K' ⧸ m))
        (Ideal.Quotient.mk m z)) (h1.trans h2.symm)
    have hw : spMap jL ≫ spMap χ = spMap jK ≫ spMap i := by
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomm]
    have hE : Epi (Over.Hom.left (Over.homMk (spMap jL) hw :
        Over.mk (spMap jK ≫ spMap i) ⟶ Over.mk (spMap χ))) := epi_spMap jL
    refine existsUnique_transfer (pushHom hpb (Over.mk (spMap jK)))
      (preHom (G := A₀) (Over.homMk (spMap jL) hw : Over.mk (spMap jK ≫ spMap i) ⟶ Over.mk (spMap χ)))
      (pushHom_bijective hpb _) (preHom_injective _)
      (fun a => (Over.homMk (spMap jK) (by simp) : Over.mk (spMap jK) ⟶ Out.baseOver (Sp K)) ≫ t.pt a)
      (fun a => (Over.homMk (spMap χ) (by simp) : Over.mk (spMap χ) ⟶ Out.baseOver (Sp K₀)) ≫ pt₀ a)
      ?_ k (fun (c : Ix g k) a => (c a).val) (fun z hz => t.bij Ω (spMap jK) z hz) y hy
    intro a
    ext1
    rw [pushHom_left]
    show ((Over.homMk (spMap jK) (by simp) : Over.mk (spMap jK) ⟶ Out.baseOver (Sp K)) ≫ t.pt a).left ≫ φ = ((Over.homMk (spMap jL) hw : Over.mk (spMap jK ≫ spMap i) ⟶ Over.mk (spMap χ)) ≫
      (Over.homMk (spMap χ) (by simp) : Over.mk (spMap χ) ⟶ Out.baseOver (Sp K₀)) ≫ pt₀ a).left
    simp only [Over.comp_left, Over.homMk_left, Category.assoc]
    rw [hpt a, ← Category.assoc, ← Category.assoc, hw]
  ·
    intro a a'
    subst hβ
    have := t.ab.comm
    have h1 := (GlobalTheory.weilIs_grpPullback_of_comm' (Sp K₀) (Sp K) A₀ t.A (spMap i) φ L₀ t.L hL₀ t.isLB hpb hLiso
      (Out.baseOver (Sp K)) (k : ℤ) (t.pt a) (t.pt a') (pushHom hpb _ (t.pt a)) (pushHom hpb _ (t.pt a')) _
      (pushHom_left hpb _ _) (pushHom_left hpb _ _)).1 (t.pairing a a')
    have e1 : unitS (spMap (i.comp β₀)) b.ζ ^ (Out.stdSymp g a a') =
        unitOn (Units.map i.toMonoidHom (Units.map β₀.toMonoidHom b.ζ ^ (Out.stdSymp g a a'))) := by
      rw [unitS_spMap, map_zpow]
      rfl
    rw [e1] at h1
    have hxa : ∀ c, (pushHom hpb (Out.baseOver (Sp K)) (t.pt c)).left =
        ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ 𝟙 (Sp K₀)) ⟶ Over.mk (𝟙 (Sp K₀))) ≫ pt₀ c).left := by
      intro c
      rw [pushHom_left, hpt c]
      rfl
    have h2 := (weilIs_congr (s' := spMap i ≫ 𝟙 (Sp K₀)) (by simp) L₀ (k : ℤ) _ _ _ _ (hxa a) (hxa a') _).1 h1
    have h3 := (_root_.GlobalTheory.weilIs_fieldExt_iff (Sp K₀) A₀ K₀ K i (𝟙 _) L₀ k (pt₀ a) (pt₀ a')
      (Units.map β₀.toMonoidHom b.ζ ^ Out.stdSymp g a a') hab hL₀).1 h2
    rw [unitS_spMap]
    exact h3

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeometricallyConnectedOpenConditionSmoothProject
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.ConnOpen

open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw ReciprocityTheory.ChartRestriction.G.Out

theorem preconnectedSpace_of_functions (Y : Scheme.{0})
    (H : ∀ s : Γ(Y, ⊤), Y.basicOpen s = ⊥ ∨ Y.basicOpen s = ⊤) : PreconnectedSpace Y := by
  refine ⟨fun U W hU hW hc ⟨u, _, hu⟩ ⟨w, _, hw⟩ => ?_⟩
  by_contra hne
  let O : Bool → Y.Opens := fun i => bif i then ⟨U, hU⟩ else ⟨W, hW⟩
  have hd : O true ⊓ O false = ⊥ := le_bot_iff.1 fun y hy => hne ⟨y, trivial, hy⟩
  have hcov : ⨆ i, O i = ⊤ := top_unique fun y _ => by
    rcases hc (Set.mem_univ y) with h | h
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨true, h⟩
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨false, h⟩
  obtain ⟨s, hs⟩ := TLinPf.glue O hcov (fun i => bif i then 1 else 0) (fun i j => by
    have sub : ∀ T : Y.Opens, T = ⊥ → Subsingleton Γ(Y, T) := fun T hT => by
      subst hT; infer_instance
    cases i <;> cases j
    · exact (map_zero _).trans (map_zero _).symm
    · exact (sub _ ((inf_comm _ _).trans hd)).elim _ _
    · exact (sub _ hd).elim _ _
    · exact (map_one _).trans (map_one _).symm)
  rcases H s with h | h
  · have h₁ : u ∈ Y.basicOpen s := (mem_basicOpen_rs (le_top : O true ≤ ⊤) s hu).1 (by
      rw [show rs Y (le_top : O true ≤ ⊤) s = 1 from hs true]
      exact mem_of_isUnit isUnit_one hu)
    rw [h] at h₁
    exact h₁
  · have h₁ := (mem_basicOpen_rs (le_top : O false ≤ ⊤) s hw).2 (h.ge (Set.mem_univ w))
    rw [show rs Y (le_top : O false ≤ ⊤) s = 0 from hs false, Scheme.basicOpen_zero] at h₁
    exact h₁

theorem surjective_appTop {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}}
    (p : X ⟶ Spec (.of k)) [IsIntegral X] [UniversallyClosed p] :
    Function.Surjective p.appTop.hom := by
  let F := (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop
  have hF : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed p
  algebraize [F.hom]
  have h : Function.Surjective F.hom :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(X, ⊤))).2
  intro s
  obtain ⟨c, hc⟩ := h s
  exact ⟨_, hc⟩

variable {X X' : Scheme.{0}}

def fnSec (π : X' ⟶ X) (s : Γ(X', ⊤)) : LB.Sec ((Inh.trivLB X).pull π) where
  f := fun _ => rs X' le_top s
  compat := fun i j => by
    rw [Inh.linComb_triv_g, Units.val_one, _root_.one_mul]
    exact (rs_rs _ _ s).trans (rs_rs _ _ s).symm

theorem triv_pull (π : X' ⟶ X) : Triv ((Inh.trivLB X).pull π) :=
  ⟨⟨fun _ => 1⟩, fun i j => by
    erw [Inh.linComb_triv_g, _root_.one_mul]
    exact (map_one _).trans (map_one _).symm⟩

theorem preconnectedSpace_of_line {R F : Type} [CommRing R] [Field F]
    {f : X ⟶ Spec (CommRingCat.of R)} (P : Perf f (Inh.trivLB X)) {g : R →+* F} {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of F)} (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    (v : Fin P.a → F) (hv : ∀ w, (P.D₀.map g).mulVec w = 0 → ∃ c : F, w = c • v) :
    PreconnectedSpace X' := by
  obtain ⟨E, hE⟩ := P.sec F g X' π f' h
  have key : ∀ s : Γ(X', ⊤), ∃ c : F, ∀ i,
      rs X' (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s = GlobalTheory.AbLaw.cst f' _ c * loc P π f' v i := fun s => by
    obtain ⟨w, hw⟩ := E.surjective (fnSec π s)
    obtain ⟨c, hc⟩ := hv w.1 w.2
    refine ⟨c, fun i => ?_⟩
    have e := hE w i
    rw [hw] at e
    refine ((rs_rs _ _ s).symm.trans e).trans ?_
    rw [← loc_smul, ← hc]
    rfl
  obtain ⟨c₁, h₁⟩ := key 1
  have hu : ∀ i, IsUnit (loc P π f' v i) := fun i =>
    isUnit_of_mul_isUnit_right (by rw [← h₁ i, map_one]; exact isUnit_one)
  refine preconnectedSpace_of_functions X' fun s => ?_
  obtain ⟨c, hc⟩ := key s
  by_cases h0 : c = 0
  · refine Or.inl (le_bot_iff.1 fun y hy => ?_)
    obtain ⟨i, hi⟩ := exists_mem P (π y)
    have := (mem_basicOpen_rs (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s hi).2 hy
    rwa [hc, h0, map_zero, zero_mul, Scheme.basicOpen_zero] at this
  · refine Or.inr (top_unique fun y _ => ?_)
    obtain ⟨i, hi⟩ := exists_mem P (π y)
    refine (mem_basicOpen_rs (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s hi).1 ?_
    rw [hc]
    exact mem_of_isUnit (((IsUnit.mk0 c h0).map _).mul (hu i)) hi

theorem exists_nonempty_fibre {R K : Type} [CommRing R] [Field K] {Z Z₀ : Scheme.{0}} (s : Z ⟶ Sp R)
    (hs : IsOpenMap s) (x : R →+* K) {π : Z₀ ⟶ Z} {q : Z₀ ⟶ Sp K} (h : π ≫ s = q ≫ spMap x) (z : Z₀) :
    ∃ e : R, x e ≠ 0 ∧ ∀ p : PrimeSpectrum R, e ∉ p.asIdeal → ∃ y : Z, s y = p := by
  have hz : s (π z) ∈ Set.range s := ⟨_, rfl⟩
  obtain ⟨_, ⟨e, rfl⟩, he, hle⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hz hs.isOpen_range
  refine ⟨e, fun h0 => ?_, fun p hp => hle hp⟩
  have e' : s (π z) = spMap x (q z) := congrArg (fun t => t z) h
  rw [e'] at he
  refine he ?_
  change x e ∈ (q z).asIdeal
  rw [h0]
  exact zero_mem _

theorem geometricallyConnected_near : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (K : Type) [Field K] (x : R →+* K), IsProjOver s → Smooth s → GeometricallyConnected (pullback.snd s (spMap x)) → ∃ f : R, x f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → GeometricallyConnected (pullback.snd s (spMap φ)) := by
  intro R _ Z s K _ x hp hs hc
  have hp' := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver s).2 hp
  obtain ⟨P⟩ := _root_.GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy R Z s hs hp' _ (Inh.trivLB_isLB _)
  have hpr : IsProper s := GlobalTheory.AbLaw.isProper_of_isProjBy R Z s hp'
  let L := AlgebraicClosure K
  let g₀ : R →+* L := (algebraMap K L).comp x
  let q := pullback.snd s (spMap x)
  let y₀ : Sp L ⟶ Sp K := spMap (algebraMap K L)
  have h₀ : IsPullback (pullback.fst q y₀ ≫ pullback.fst s (spMap x)) (pullback.snd q y₀) s
      (Spec.map (CommRingCat.ofHom g₀)) := by
    have := (IsPullback.of_hasPullback q y₀).paste_horiz (IsPullback.of_hasPullback s (spMap x))
    rwa [← Spec.map_comp] at this
  have hi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ q inferInstance hc
  have hint : IsIntegral (pullback q y₀) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback q y₀)
  have hpr₀ : IsProper (pullback.snd q y₀) := MorphismProperty.of_isPullback h₀ hpr
  obtain ⟨v, -, hu, hline⟩ := loc_of_triv P h₀ (Inh.trivLB_isLB _) (triv_pull _)
  obtain ⟨x₀⟩ : Nonempty ↥(pullback q y₀) := inferInstance
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := exists_mem P ((pullback.fst q y₀ ≫ pullback.fst s (spMap x)) x₀)
    have h₁ := mem_of_isUnit (hu i) (y := x₀) hi
    rw [← zero_smul L (0 : Fin P.a → L), loc_smul, map_zero, zero_mul, Scheme.basicOpen_zero] at h₁
    exact h₁
  obtain ⟨δ, v₀, hδ, hker⟩ := exists_kernel_vector g₀ P.D₀ v hv0 (hline (surjective_appTop _))
  obtain ⟨e, he, him⟩ := exists_nonempty_fibre s s.isOpenMap g₀ h₀.w x₀
  refine ⟨δ * e, fun h0 => mul_ne_zero hδ he ?_, fun R' _ φ hφ => ?_⟩
  · rw [← map_mul]
    exact (congrArg (algebraMap K L) h0).trans (map_zero _)
  refine ⟨geometrically_iff_of_commRing.2 fun F _ _ Y fst snd h => ?_⟩
  let g : R →+* F := (algebraMap R' F).comp φ
  have h₁ : IsPullback (fst ≫ pullback.fst s (spMap φ)) snd s (Spec.map (CommRingCat.ofHom g)) := by
    have := h.paste_horiz (IsPullback.of_hasPullback s (spMap φ))
    rwa [← Spec.map_comp] at this
  have hg : IsUnit (g δ * g e) := by
    rw [← map_mul]
    exact hφ.map (algebraMap R' F)
  have := preconnectedSpace_of_line P h₁ _ (hker F g (isUnit_of_mul_isUnit_left hg))
  obtain ⟨y, hy⟩ := him (PrimeSpectrum.comap g ⊥) fun hm =>
    (isUnit_of_mul_isUnit_right hg).ne_zero hm
  obtain ⟨z, -⟩ := Scheme.exists_preimage_of_isPullback h₁ y (⊥ : PrimeSpectrum F) hy
  exact ⟨⟨z⟩⟩

end GlobalTheory.ConnOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelDataPullbackOfLevelMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.SiegelDataPull

open GlobalTheory.SiegelPullComp

theorem isSquare_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {ψ : G''.left ⟶ G'.left} {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {ψ₂ : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : Geo.Tor.IsSquare ψ ψ₂) (h : Geo.Tor.IsSquare φ φ₂) : Geo.Tor.IsSquare (ψ ≫ φ) (ψ₂ ≫ φ₂) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc]
  · rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]

theorem siegData_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (O : Type) [CommRing O] (T T' : Scheme.{0}) (sT : T ⟶ Sp O) (f : T' ⟶ T) (t : SAB H T) (t' : SAB H T') (ν : SABMap t' t f) (lev : D.La → (𝟙_ (Over T) ⟶ t.G)) (lev' : D.La → (𝟙_ (Over T') ⟶ t'.G)) (g p N : ℕ) (Ag : SiegelFamily g p N) (z : ZP p N →+* O) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (w : T ⟶ pullback Ag.s (spMap z)), (∀ x, (lev' x).left ≫ ν.φ = f ≫ (lev x).left) → SiegData sT t lev Ag z bas w → SiegData (f ≫ sT) t' lev' Ag z bas (f ≫ w) := by
  intro E _ _ _ H D O _ T T' sT f t t' ν lev lev' g p N Ag z bas w hlev hw
  obtain ⟨o, φ, φ₂, hpb, hsq, hiso, hlv, hsnd, hSPB⟩ := hw
  obtain ⟨⟨o', ho'⟩, -⟩ := GlobalTheory.siegPre_pullback _ _ _ _ _ _ _ ((f ≫ sT) ≫ spMap z) f o
    (Category.assoc f sT (spMap z)).symm
  have hpbo := ho'
  obtain ⟨φ₁, φ₁₂, hpb₁, hsq₁, hiso₁, hlv₁⟩ := hpbo
  have hν : IsGrpPullback t'.G t.G f ν.φ := ν.cart
  have hc : IsGrpPullback o'.A t.G f (φ₁ ≫ φ) := (hpb₁.comp hpb).congr (Category.comp_id f) rfl
  obtain ⟨e, he, hel⟩ := grpPullback_iso hc hν
  haveI := he
  have hpb' : IsGrpPullback o'.A t'.G (𝟙 T') e.hom.left := isGrpPullback_of_iso e
  have hsq' := GlobalTheory.LamPull.exists_isSquare hpb'.1.w
  have hν₂ := GlobalTheory.LamPull.exists_isSquare hν.1.w
  have hΛ : (abelian₂ t.G t.PP.L).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ t.PP.isLB _ _
  have hΛ' : (abelian₂ t'.G t'.PP.L).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ t'.PP.isLB _ _
  have sA := isSquare_comp hsq₁ hsq
  have sB := isSquare_comp hsq' hν₂
  rw [hel] at sB
  have key := GlobalTheory.LamPull.isSquare_unique sA sB
  refine ⟨o', e.hom.left, _, hpb', hsq', ?_, ?_, ?_, ?_⟩
  · have h2 := GlobalTheory.SiegelPullComp.iso_pull φ₁₂ hiso
    have h3 := GlobalTheory.SiegelPullComp.iso_pull_pull hΛ φ₂ φ₁₂
    rw [key] at h3
    have h4 := (GlobalTheory.SiegelPullComp.iso_pull_pull hΛ (lift (pushPt hν.1.w (fst t'.G t'.G))
      (pushPt hν.1.w (snd t'.G t'.G))).left (lift (pushPt hpb'.1.w (fst o'.A o'.A))
      (pushPt hpb'.1.w (snd o'.A o'.A))).left).symm
    have h5 := GlobalTheory.SiegelPullComp.iso_pull (lift (pushPt hpb'.1.w (fst o'.A o'.A))
      (pushPt hpb'.1.w (snd o'.A o'.A))).left ((GlobalTheory.LamPull.lam_pull E H T T' t t' f).2 ν _ hν₂).symm
    have l0 := o'.isLB
    have l1 := pull_isLB o.isLB φ₁₂
    have l2 := pull_isLB (pull_isLB hΛ φ₂) φ₁₂
    refine LBIso.trans l0 l1 (pull_isLB hΛ' _) hiso₁ ?_
    refine LBIso.trans l1 l2 (pull_isLB hΛ' _) h2 ?_
    refine LBIso.trans l2 (pull_isLB hΛ _) (pull_isLB hΛ' _) h3 ?_
    refine LBIso.trans (pull_isLB hΛ _) (pull_isLB (pull_isLB hΛ _) _) (pull_isLB hΛ' _) h4 h5
  · intro u
    apply hν.1.hom_ext
    · rw [Category.assoc, hel, ← Category.assoc, hlv₁ u, Category.assoc, hlv u, hlev]
    · rw [Category.assoc, Over.w e.hom, Over.w (o'.lev u), Over.w (lev' (bas u))]
  · rw [Category.assoc, hsnd]
  · rw [Category.assoc f w (pullback.fst Ag.s (spMap z))]
    exact GlobalTheory.SiegelPullComp.pb_comp hSPB ho'

end GlobalTheory.SiegelDataPull

end
end

