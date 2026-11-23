module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0548
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCapFBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0549
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseChangeCompatibleGlobalOneFormsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBaseChange_compatibleGlobalOneForms : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (T : C) (e : Glob1 F →ₗ[R] Ω[F.obj T⁄R]), (∀ w, e w = w.1 T) → IsBaseChange (F.obj T) e := by
  first | exact @GlobalTheory.AbCoh.isBaseChange_glob1 | exact GlobalTheory.AbCoh.isBaseChange_glob1 | (intros; apply GlobalTheory.AbCoh.isBaseChange_glob1 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechOneCoboundaryOfRefinement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.KS

namespace GlobalTheory.KS.Refine

theorem isCob_of_refine : ∀ {Y : Scheme.{0}} {I J : Type} (Uc : I → Y.Opens) (c : GlobalTheory.KS.C1 Uc),
    GlobalTheory.KS.IsCoc Uc c → ∀ (V : J → Y.Opens) (σ : J → I), (∀ p, V p ≤ Uc (σ p)) → (⨆ p, V p = ⊤) →
    ∀ (B : ∀ p, Γ(Y, V p)), (∀ p p', GlobalTheory.KS.rsT (c (σ p) (σ p')) (V p ⊓ V p') =
      GlobalTheory.KS.rsT (B p') (V p ⊓ V p') - GlobalTheory.KS.rsT (B p) (V p ⊓ V p')) → GlobalTheory.KS.IsCob Uc c := by
  intro Y I J Uc c hc V σ hV hVt B hB
  have hV' : ∀ p y, y ∈ V p → y ∈ Uc (σ p) := fun p y h => hV p h
  have cov : ∀ O : Y.Opens, O ≤ ⨆ p, O ⊓ V p := by
    intro O x hx
    have : x ∈ ⨆ p, V p := by rw [hVt]; trivial
    obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, hx, hp⟩
  have glue : ∀ i, ∃ t : Γ(Y, Uc i), ∀ p, rsT t (Uc i ⊓ V p) =
      rsT (B p) (Uc i ⊓ V p) + rsT (c (σ p) i) (Uc i ⊓ V p) := by
    intro i
    refine exists_rsT_eq (fun p => Uc i ⊓ V p) (fun p => inf_le_left) (cov _) _ fun p p' => ?_
    have h1 := congrArg (fun s => rsT s ((Uc i ⊓ V p) ⊓ (Uc i ⊓ V p'))) (hB p p')
    have h2 := congrArg (fun s => rsT s ((Uc i ⊓ V p) ⊓ (Uc i ⊓ V p'))) (hc (σ p) (σ p') i)
    simp only [rsT_add, rsT_sub] at h1 h2 ⊢
    repeat
      first | rw [rsT_rsT] at h1 | rw [rsT_rsT] at h2 | rw [rsT_rsT]
      all_goals try (intro x hx; try simp only [TopologicalSpace.Opens.mem_inf] at hx ⊢; aesop)
    linear_combination h1 - h2
  choose t ht using glue
  refine ⟨t, fun i j => ?_⟩
  refine eq_of_rsT_eq (fun p => Uc i ⊓ Uc j ⊓ V p) (fun p => inf_le_left) (cov _) _ _ fun p => ?_
  have h1 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (ht i p)
  have h2 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (ht j p)
  have h3 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (hc (σ p) i j)
  simp only [rsT_add, rsT_sub] at h1 h2 h3 ⊢
  repeat
    first | rw [rsT_rsT] at h1 | rw [rsT_rsT] at h2 | rw [rsT_rsT] at h3 | rw [rsT_rsT]
    all_goals try (intro x hx; try simp only [TopologicalSpace.Opens.mem_inf] at hx ⊢; aesop)
  linear_combination h1 - h2 + h3

end GlobalTheory.KS.Refine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechOneCocyclePosetOneCochainToCechCochain
section
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechCmp

variable {I : Type} [Finite I] {X : Scheme.{0}} {R : Type} [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W))

theorem toCech_cocycle_read (f : GlobalTheory.CatCoh.C1 (capF s U hU hinf)) (hf : f ∈ Z1 (capF s U hU hinf))
    (x : I) (P K : NE I) (hxP : P ≤ NE.single x) (hPK : K ≤ P) (hxK : K ≤ NE.single x)
    (W : X.Opens) (hW : W ≤ cap U K) :
    rsT (cv s U hU hinf (op P) (f (op (NE.single x)) (op P) (homOfLE hxP).op)) W =
      rsT (cv s U hU hinf (op K) (f (op (NE.single x)) (op K) (homOfLE hxK).op)) W -
        rsT (cv s U hU hinf (op K) (f (op P) (op K) (homOfLE hPK).op)) W := by
  have e := Z1.comp ⟨f, hf⟩ (homOfLE hxP).op (homOfLE hPK).op
  have hc : (homOfLE hxP).op ≫ (homOfLE hPK).op = (homOfLE hxK).op := Subsingleton.elim _ _
  rw [hc] at e
  have e' := congrArg (fun b => rsT (cv s U hU hinf (op K) b) W) e
  simp only [map_add (f := _), GlobalTheory.KS.rsT_add] at e'
  rw [cv_mp s U hU hinf (homOfLE hPK).op] at e'
  rw [GlobalTheory.KS.rsT_rsT (O₁ := cap U (op K).unop) (cap_mono U hPK) hW] at e'
  rw [e']
  abel

theorem toCech_isCoc (f : GlobalTheory.CatCoh.C1 (capF s U hU hinf)) (hf : f ∈ Z1 (capF s U hU hinf)) :
    IsCoc U (toCech s U hU hinf f) := by
  intro i j k
  let K : NE I := OrderDual.toDual ⟨{i, j, k}, Set.insert_nonempty i {j, k}⟩
  have hi : i ∈ K.set := Set.mem_insert i _
  have hj : j ∈ K.set := Set.mem_insert_of_mem i (Set.mem_insert j _)
  have hk : k ∈ K.set := Set.mem_insert_of_mem i (Set.mem_insert_of_mem j rfl)
  have sgl : ∀ {a : I}, a ∈ K.set → K ≤ NE.single a := fun ha => NE.le_iff.2 (Set.singleton_subset_iff.2 ha)
  have pr : ∀ {a b : I}, a ∈ K.set → b ∈ K.set → K ≤ NE.pair a b :=
    fun ha hb => NE.le_iff.2 (Set.insert_subset ha (Set.singleton_subset_iff.2 hb))
  have hW : U i ⊓ U j ⊓ U k ≤ cap U K := le_iInf₂ fun x hx => by
    rcases hx with rfl | rfl | rfl
    · exact inf_le_left.trans inf_le_left
    · exact inf_le_left.trans inf_le_right
    · exact inf_le_right
  have hij : U i ⊓ U j ⊓ U k ≤ U i ⊓ U j := inf_le_left
  have hjk : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hik : U i ⊓ U j ⊓ U k ≤ U i ⊓ U k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  simp only [toCech_apply, GlobalTheory.KS.rsT_sub]
  rw [GlobalTheory.KS.rsT_rsT (cap_pair U i j).ge hij, GlobalTheory.KS.rsT_rsT (cap_pair U i j).ge hij,
    GlobalTheory.KS.rsT_rsT (cap_pair U j k).ge hjk, GlobalTheory.KS.rsT_rsT (cap_pair U j k).ge hjk,
    GlobalTheory.KS.rsT_rsT (cap_pair U i k).ge hik, GlobalTheory.KS.rsT_rsT (cap_pair U i k).ge hik]
  rw [toCech_cocycle_read s U hU hinf f hf i _ K _ (pr hi hj) (sgl hi) _ hW,
    toCech_cocycle_read s U hU hinf f hf j _ K _ (pr hi hj) (sgl hj) _ hW,
    toCech_cocycle_read s U hU hinf f hf j _ K _ (pr hj hk) (sgl hj) _ hW,
    toCech_cocycle_read s U hU hinf f hf k _ K _ (pr hj hk) (sgl hk) _ hW,
    toCech_cocycle_read s U hU hinf f hf i _ K _ (pr hi hk) (sgl hi) _ hW,
    toCech_cocycle_read s U hU hinf f hf k _ K _ (pr hi hk) (sgl hk) _ hW]
  abel

theorem isCoc_toCech : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ f : GlobalTheory.CatCoh.C1 (capF s U hU hinf), f ∈ Z1 (capF s U hU hinf) → IsCoc U (toCech s U hU hinf f) :=
  fun _ _ _ _ _ s U hU hinf f hf => toCech_isCoc s U hU hinf f hf

end GlobalTheory.CechCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawMap
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

variable {R S : Type} [CommRing R] [CommRing S] (σ : R →+* S) {d : ℕ} {τ : Type}

theorem map_powerSeriesEvalTwoGroups (c : MvPowerSeries (Fin d ⊕ Fin d) R) {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    MvPowerSeries.map σ (at2 c u v) =
      at2 (MvPowerSeries.map σ c) (fun i => MvPowerSeries.map σ (u i))
        (fun i => MvPowerSeries.map σ (v i)) := by
  have hs : HasSubst (Sum.elim u v) :=
    hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp [hu, hv])
  unfold at2
  rw [map_subst hs]
  congr 1
  funext s
  cases s <;> rfl

theorem constantCoeff_powerSeriesEvalTwoGroups_zero_of {c : MvPowerSeries (Fin d ⊕ Fin d) R}
    (hc : constantCoeff c = 0) {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    constantCoeff (at2 c u v) = 0 := by
  have h0 : ∀ s, constantCoeff (Sum.elim u v s) = 0 := fun s => by cases s <;> simp [hu, hv]
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 hc

theorem map_op_of_const (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    (fun i => MvPowerSeries.map σ (op μ u v i)) =
      op (fun i => MvPowerSeries.map σ (μ i)) (fun i => MvPowerSeries.map σ (u i))
        (fun i => MvPowerSeries.map σ (v i)) := by
  funext i
  exact map_powerSeriesEvalTwoGroups σ (μ i) hu hv

theorem isLaw_map (R S : Type) [CommRing R] [CommRing S] (σ : R →+* S) (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (h : IsLaw μ) :
    IsLaw (fun i => MvPowerSeries.map σ (μ i)) := by
  have hX : ∀ {κ : Type} (f : Fin d → κ), (fun i => MvPowerSeries.map σ
      (X (f i) : MvPowerSeries κ R)) = fun i => (X (f i) : MvPowerSeries κ S) := by
    intro κ f; funext i; exact map_X σ (f i)
  have hcX : ∀ {κ : Type} (f : Fin d → κ) (i : Fin d),
      constantCoeff (X (f i) : MvPowerSeries κ R) = 0 := fun f i => constantCoeff_X _
  refine ⟨fun i => ?_, ?_, fun i => ?_, ?_⟩
  · rw [constantCoeff_map, h.const i, map_zero]
  · have h1 := congrArg (fun w : Fin d → MvPowerSeries (Fin d) R =>
      fun i => MvPowerSeries.map σ (w i)) h.unit
    rw [map_op_of_const σ μ (u := fun i => (X i : MvPowerSeries (Fin d) R)) (fun i => constantCoeff_X i)
      (fun _ => map_zero _)] at h1
    simpa only [map_X, map_zero] using h1
  · have h1 := congrArg (MvPowerSeries.map σ) (h.comm i)
    unfold swap at h1 ⊢
    rw [map_powerSeriesEvalTwoGroups σ (μ i) (hcX Sum.inr) (hcX Sum.inl)] at h1
    simpa only [map_X] using h1
  · have hx1 : ∀ i, constantCoeff (x1 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have hx2 : ∀ i, constantCoeff (x2 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have hx3 : ∀ i, constantCoeff (x3 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have c12 : ∀ i, constantCoeff (op μ x1 x2 i) = 0 := fun i =>
      constantCoeff_powerSeriesEvalTwoGroups_zero_of (h.const i) hx1 hx2
    have c23 : ∀ i, constantCoeff (op μ x2 x3 i) = 0 := fun i =>
      constantCoeff_powerSeriesEvalTwoGroups_zero_of (h.const i) hx2 hx3
    have h1 := congrArg (fun w : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R =>
      fun i => MvPowerSeries.map σ (w i)) h.assoc
    rw [map_op_of_const σ μ c12 hx3, map_op_of_const σ μ hx1 c23,
      map_op_of_const σ μ hx1 hx2, map_op_of_const σ μ hx2 hx3] at h1
    have e1 : (fun i => MvPowerSeries.map σ (x1 (R := R) (d := d) i)) = x1 := hX _
    have e2 : (fun i => MvPowerSeries.map σ (x2 (R := R) (d := d) i)) = x2 := hX _
    have e3 : (fun i => MvPowerSeries.map σ (x3 (R := R) (d := d) i)) = x3 := hX _
    rwa [e1, e2, e3] at h1

end GlobalTheory.Katz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommMonObjOfGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem isCommMonObj_of_grpPullback : ∀ (S S' : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → IsCommMonObj G' := by
  intro S S' G _ _ G' _ f φ h
  rw [isCommMonObj_iff_isMulCommutative]
  intro T
  refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
  rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
    ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspProdCharTransport
section
noncomputable section

namespace GlobalTheory.FinGL.Transport

open Formalism.L2.DIV

theorem isIrreducible_comp {G G' V : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ G V) (f : G' →* G) (hf : Function.Surjective f) (h : σ.IsIrreducible) :
    Representation.IsIrreducible (σ.comp f : Representation ℂ G' V) := by
  let Φ : Subrepresentation (σ.comp f : Representation ℂ G' V) ≃o Subrepresentation σ :=
    { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
        obtain ⟨g', rfl⟩ := hf g
        exact U.apply_mem_toSubmodule g' hv⟩
      invFun := fun U => ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (f g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact Φ.isSimpleOrder

theorem character_coind {G G' P P' V : Type} [Group G] [Group G'] [Group P] [Group P'] [AddCommGroup V] [Module ℂ V]
    (i : P →* G) (i' : P' →* G') (σ : Representation ℂ P V) (F : G' ≃* G) (f : P' →* P) (hf : Function.Surjective f)
    (hc : ∀ p, F (i' p) = i (f p)) (x : G') :
    (Representation.coind i' (σ.comp f : Representation ℂ P' V)).character x =
      (Representation.coind i σ).character (F x) := by
  let L : Representation.coindV i σ ≃ₗ[ℂ] Representation.coindV i' (σ.comp f : Representation ℂ P' V) :=
    { toFun := fun φ => ⟨fun y => φ.1 (F y), fun p y => by
        show φ.1 (F (i' p * y)) = σ (f p) (φ.1 (F y))
        rw [map_mul, hc]
        exact φ.2 _ _⟩
      invFun := fun φ => ⟨fun y => φ.1 (F.symm y), fun p y => by
        obtain ⟨p', rfl⟩ := hf p
        show φ.1 (F.symm (i (f p') * y)) = σ (f p') (φ.1 (F.symm y))
        rw [map_mul, ← hc, MulEquiv.symm_apply_apply]
        exact φ.2 _ _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun φ => Subtype.ext (funext fun y => congrArg φ.1 (F.apply_symm_apply y))
      right_inv := fun φ => Subtype.ext (funext fun y => congrArg φ.1 (F.symm_apply_apply y)) }
  unfold Representation.character
  rw [← LinearMap.trace_conj' _ L]
  congr 1
  refine LinearMap.ext fun φ => Subtype.ext (funext fun y => ?_)
  show φ.1 (y * x) = φ.1 (F.symm (F y * F x))
  rw [← map_mul, MulEquiv.symm_apply_apply]

variable {κ κ' : Type} [Field κ] [Field κ'] {r : ℕ}

def glEquiv (e : κ' ≃+* κ) (r : ℕ) : GL (Fin r) κ' ≃* GL (Fin r) κ :=
  { Matrix.GeneralLinearGroup.map (e : κ' →+* κ) with
    invFun := Matrix.GeneralLinearGroup.map (e.symm : κ →+* κ')
    left_inv := fun g => by
      ext i j
      simp [Matrix.GeneralLinearGroup.map_apply]
    right_inv := fun g => by
      ext i j
      simp [Matrix.GeneralLinearGroup.map_apply] }

def triMap (e : κ' →+* κ) (b : Fin r → ℕ) : blockTri (κ := κ') b →* blockTri (κ := κ) b :=
  ((Matrix.GeneralLinearGroup.map e).comp (blockTri (κ := κ') b).subtype).codRestrict _ fun p i j hij => by
    have h : (p.1 : Matrix (Fin r) (Fin r) κ') i j = 0 := p.2 hij
    show e ((p.1 : Matrix (Fin r) (Fin r) κ') i j) = 0
    rw [h, map_zero]

theorem triMap_apply (e : κ' →+* κ) (b : Fin r → ℕ) (p : blockTri (κ := κ') b) (i j : Fin r) :
    ((triMap e b p : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j =
      e (((p : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') i j) := rfl

theorem triMap_surjective (e : κ' ≃+* κ) (b : Fin r → ℕ) : Function.Surjective (triMap (e : κ' →+* κ) b) := fun p =>
  ⟨triMap (e.symm : κ →+* κ') b p, by
    ext i j
    simp [triMap_apply]⟩

theorem triMap_eq_one_iff (e : κ' →+* κ) (b : Fin r → ℕ) (p : blockTri (κ := κ') b) (i j : Fin r) :
    ((triMap e b p : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j = (1 : Matrix (Fin r) (Fin r) κ) i j ↔
      ((p : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') i j = (1 : Matrix (Fin r) (Fin r) κ') i j := by
  have h1 : (1 : Matrix (Fin r) (Fin r) κ) i j = e ((1 : Matrix (Fin r) (Fin r) κ') i j) := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [triMap_apply, h1, e.injective.eq_iff]

theorem isCuspDatum_comp {V : Type} [AddCommGroup V] [Module ℂ V] (e : κ' ≃+* κ) (b : Fin r → ℕ)
    (σ : Representation ℂ (blockTri (κ := κ) b) V) (h : IsCuspDatum b σ) :
    IsCuspDatum b (σ.comp (triMap (e : κ' →+* κ) b) : Representation ℂ (blockTri (κ := κ') b) V) := by
  refine ⟨h.mono, isIrreducible_comp σ _ (triMap_surjective e b) h.irr, ?_, ?_⟩
  · intro p hp
    exact h.infl _ fun i j hij => (triMap_eq_one_iff _ b p i j).2 (hp i j hij)
  · intro S hS y hy
    refine h.cusp S hS y fun u hu => ?_
    obtain ⟨u', rfl⟩ := triMap_surjective e b u
    exact hy u' fun i j hij => hu i j fun h' => hij ((triMap_eq_one_iff _ b u' i j).1 h')

theorem isCuspProdChar_transport : ∀ (κ κ' : Type) [Field κ] [Field κ'] (e : κ ≃+* κ') (r : ℕ) (θ : GL (Fin r) κ → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar θ → GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar
      (fun x : GL (Fin r) κ' => θ (Matrix.GeneralLinearGroup.map (e.symm : κ' →+* κ) x)) := by
  rintro κ κ' _ _ e r θ ⟨d, b, σ, hσ, hθ⟩
  refine ⟨d, b, σ.comp (triMap (e.symm : κ' →+* κ) b), isCuspDatum_comp e.symm b σ hσ, fun x => ?_⟩
  show θ _ = _
  rw [hθ]
  exact (character_coind _ _ σ (glEquiv e.symm r) _ (triMap_surjective e.symm b) (fun _ => rfl) x).symm

end GlobalTheory.FinGL.Transport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteOfIsProperOfFormallyUnramified
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.PropFin

theorem isFinite_of_isProper_of_formallyUnramified :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S) [IsLocallyNoetherian S],
      IsProper f → FormallyUnramified f → IsFinite f := by
  intro X S f _ hp hu
  have hlqf : LocallyQuasiFinite f := by
    refine ⟨fun {U} hU {V} hV e => ?_⟩
    have h₁ := f.formallyUnramified_appLE hU hV e
    have h₂ := f.finiteType_appLE hU hV e
    algebraize [(f.appLE U V e).hom]
    exact inferInstanceAs (Algebra.QuasiFinite _ _)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end GlobalTheory.PropFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHopfIdealKerIdealOfBialgHom
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDiv

theorem isHopfIdeal_kerIdeal_of_bialgHom (k A B : Type) [CommRing k] [CommRing A] [CommRing B]
    [HopfAlgebra k A] [HopfAlgebra k B] (f : B →ₐc[k] A) : (kerIdeal f).IsHopfIdeal k := by
  refine Ideal.IsHopfIdeal.mk (toIsCoideal := ⟨?_, ?_⟩) ?_
  · intro x hx
    exact (kerIdeal_le_ker_iff f (counitAlgHom k A)).2 (fun c => by simp) hx
  · intro x hx
    have h0 := (kerIdeal_le_ker_iff f (Ideal.Quotient.mkₐ k (kerIdeal f))).1
      fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
    have h : kerIdeal f ≤ RingHom.ker
        ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal f))
          (Ideal.Quotient.mkₐ k (kerIdeal f))).comp (comulAlgHom k A)) := by
      refine (kerIdeal_le_ker_iff f _).2 fun c => ?_
      have key : ∀ t : B ⊗[k] B, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal f))
          (Ideal.Quotient.mkₐ k (kerIdeal f)) (pullbackTwo f t) =
          algebraMap k _ (counit (R := k)
            (TensorProduct.lid k B (LinearMap.rTensor B (counit (R := k) (A := B)) t))) := by
        intro t
        induction t with
        | add x y hx hy => simp only [map_add (f := _), hx, hy]
        | tmul x y =>
          rw [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul,
            TensorProduct.lid_tmul, map_smul]
          erw [h0, h0]
          simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, smul_tmul',
            smul_smul, mul_comm]
      rw [AlgHom.comp_apply, comulAlgHom_apply, ← pullTwo_comul, key, rTensor_counit_comul,
        TensorProduct.lid_tmul, one_smul]
    exact h hx
  · intro x hx
    have h : kerIdeal f ≤ (kerIdeal f).comap (HopfAlgebra.antipodeAlgHom k A) := by
      refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
      have ha' : counit (R := k) a = 0 := ha
      change HopfAlgebra.antipode k (f a) ∈ kerIdeal f
      rw [← bialgHom_map_antipode]
      exact Ideal.mem_map_of_mem (f : B →ₐ[k] A) (by simp [RingHom.mem_ker, ha'])
    exact h hx

end GlobalTheory.PDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationAwayFibStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocalization_away_ferrandPush_fib : ∀ {Y₀ Y₁ Y₂ : Scheme.{0}} (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) [IsClosedImmersion i₁] [Surjective i₁] [IsClosedImmersion i₂] [Surjective i₂], ∀ U ∈ GlobalTheory.FerrandPush.good i₁ i₂, ∀ a : (GlobalTheory.FerrandPush.fib i₁ i₂).obj (op U), letI := ((GlobalTheory.FerrandPush.fib i₁ i₂).map (homOfLE (Y₀.basicOpen_le (((GlobalTheory.FerrandPush.fibπ i₁ i₂).app (op U)).hom a))).op).hom.toAlgebra; IsLocalization.Away a ((GlobalTheory.FerrandPush.fib i₁ i₂).obj (op (Y₀.basicOpen (((GlobalTheory.FerrandPush.fibπ i₁ i₂).app (op U)).hom a)))) := by
  first | exact @GlobalTheory.FerrandPush.isLocalization_away_fib | exact GlobalTheory.FerrandPush.isLocalization_away_fib | (intros; apply GlobalTheory.FerrandPush.isLocalization_away_fib; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionSpecMapOfThickeningStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpenImmersion_of_nilpotent_thickening_cover : ∀ (B₀ : Scheme.{0}) (𝒰 : Set B₀.Opens), (∀ U ∈ 𝒰, IsAffineOpen U) → ∀ (𝒜 : B₀.Opensᵒᵖ ⥤ CommRingCat.{0}) (π : 𝒜 ⟶ B₀.presheaf), (∀ U ∈ 𝒰, Function.Surjective (π.app (op U)).hom ∧ IsNilpotent (RingHom.ker (π.app (op U)).hom)) → (∀ U ∈ 𝒰, ∀ a : 𝒜.obj (op U), letI := (𝒜.map (homOfLE (B₀.basicOpen_le ((π.app (op U)).hom a))).op).hom.toAlgebra; IsLocalization.Away a (𝒜.obj (op (B₀.basicOpen ((π.app (op U)).hom a))))) → ∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ h : U ≤ V, IsOpenImmersion (Spec.map (𝒜.map (homOfLE h).op)) := by
  first | exact @GlobalTheory.ThickGlue.isOpenImmersion_specMap_of_thickening | exact GlobalTheory.ThickGlue.isOpenImmersion_specMap_of_thickening | (intros; apply GlobalTheory.ThickGlue.isOpenImmersion_specMap_of_thickening <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotypicPartExteriorProductInflatedSurjectionStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotypicPart_exteriorProduct_inflated_surjection : ∀ (P G₁ G₂ : Type) [Group P] [Finite P] [Group G₁] [Group G₂] (π : P →* G₁ × G₂), Function.Surjective π → ∀ (φ₁ Y₁ : G₁ → ℂ) (φ₂ Y₂ : G₂ → ℂ), IsChar ℂ ℂ Y₁ → IsChar ℂ ℂ Y₂ → Kills φ₁ Y₁ → Kills φ₂ Y₂ → Kills (fun p => φ₁ (π p).1 * φ₂ (π p).2) (fun p => Y₁ (π p).1 * Y₂ (π p).2) := by
  first | (exact @GlobalTheory.Shin.kills_prod_comp_surj) | (exact GlobalTheory.Shin.kills_prod_comp_surj) | (intros; apply GlobalTheory.Shin.kills_prod_comp_surj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNervePullbackBijectiveDegreeZeroStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentCechNerve_pullback_bijective_degree_zero : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (A' : Type) [CommRing A'] [Algebra A A'],
  Module.Finite A A' → ∀ (k : ℕ) (i : ℤ), Function.Bijective (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q i) 0) := by
  first | (exact @GlobalTheory.EtC.GmStep.LevelZero.cechC_pull_bijective) | (exact GlobalTheory.EtC.GmStep.LevelZero.cechC_pull_bijective) | (intros; apply GlobalTheory.EtC.GmStep.LevelZero.cechC_pull_bijective  <;> assumption)
end

