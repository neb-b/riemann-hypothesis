module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3100
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3106
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3114
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2369
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3084
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1336
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2277
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1423
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRealiseKodairaSpencerDirection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTRealise


set_option maxHeartbeats 4000000 in
theorem realise_core (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (hN : N.Coprime p) (k : Type) [Field k] (β : R →+* k)
    (s : Sp k ⟶ Sp R) (hs : s = spMap β) (o₀ : GlobalTheory.UPel.HT.Obj b N s)
    (φ : LinearMap.BilinForm k (HdR o₀.A)) (hφ : GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ)
    (f : HdR o₀.A →ₗ[k] HdR o₀.A)
    (hf : IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) f)
    (tR : R →+* DualNumber k) (htR : tR = (algebraMap k (DualNumber k)).comp β)
    (hs' : s = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap tR) :
    ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap tR))
      (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)),
      ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f x) := by
  have hZ := GlobalTheory.T.lieConditionHodgeSubspace_le_hodgeFiltration p D R b N k β s hs o₀
  subst hs'
  haveI : Module.Finite k (DualNumber k) := inferInstanceAs (Module.Finite k (k × k))
  haveI : IsArtinianRing (DualNumber k) := IsArtinianRing.of_finite k (DualNumber k)
  have hπ : Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom :=
    fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
  have hsq : RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom ^ 2 = 0 := (SqExt.dual k).sq
  have hA₀ := o₀.ab
  obtain ⟨M, hM⟩ := _root_.GlobalTheory.HTRealise.graphFil_exists_isCompl k o₀.A hA₀ f
  obtain ⟨A, _, i, h, act, hA, hE, hact⟩ := GlobalTheory.HTDeform.exists_lift_oAct p D R b N (DualNumber k) k
    (TrivSqZeroExt.fstHom k k k).toRingHom hπ hsq tR o₀ (graphFil o₀.A f) ⟨M, hM⟩
    (fun y => GlobalTheory.T.mem_hodgeFiltration_iff_dualNumberGraph_reduction k o₀.A hA₀ f y)
    (fun c d hd => by
      haveI := o₀.act.hom c
      exact _root_.GlobalTheory.HTRealise.push_mem_graphFil k o₀.A (o₀.act.act c) f (fun x hx => hf.1 c x hx) d hd)
  haveI : IsCommMonObj A := hA.comm
  obtain ⟨P, φ₂, hP, r1, r2, hsym, hamp, hker, hros, hsq2, hpol⟩ :=
    _root_.GlobalTheory.UPel.HT.PolLift.exists_pol_lift p D R b N (DualNumber k) k (TrivSqZeroExt.fstHom k k k).toRingHom hπ hsq tR o₀ A i h hA act hact
      (fun φ' hφ' x hx y hy => by
        rw [hE] at hx hy
        exact GlobalTheory.T.dualNumberGraphFiltration_isotropic_of_skew k o₀.A hA₀ o₀.P o₀.isLB φ hφ f hf.2.2 φ' hφ' x hx y hy)
  obtain ⟨eta, e1, e2, e3, e4, e5⟩ := _root_.GlobalTheory.HTLevelLift.level_lift p D R b N (DualNumber k) k
    (TrivSqZeroExt.fstHom k k k).toRingHom hπ hsq tR o₀ A i h hA act hact hN P φ₂ hP hsq2 hpol
  have hEl : ∀ d : Crys (divided₂ hsq) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A,
      (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω);
        push (divided₂ hsq) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) d)
        - tR b.ρ • d ∈ liftFil (divided₂ hsq) h →
      ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A,
        (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c);
          push (divided₂ hsq) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i))
            - tR (b.t i c) • w i ∈ liftFil (divided₂ hsq) h) ∧ d - ∑ i, w i ∈ liftFil (divided₂ hsq) h := by
    intro d hd
    rw [hE] at hd ⊢
    subst htR
    exact GlobalTheory.T.dualNumberGraphFiltration_lie_of_map_into_hodge p D R b N k β _ o₀ f hZ hf.2.1 d hd
  refine ⟨{ A := A
            ab := hA
            act := act
            P := P
            isLB := hP
            rig₁ := r1
            rig₂ := r2
            symm := hsym
            ample := hamp
            kerP := hker
            rosati := hros
            lie := fun R' _ β' x hx v hv => GlobalTheory.T.harrisTaylor_lift_lie_of_hodge_summand_lie p D R b N (DualNumber k) k
              (TrivSqZeroExt.fstHom k k k).toRingHom hπ hsq tR o₀ A i h hA act hact hEl R' β' x hx v hv
            lieRank := fun k' _ _ x β' hx j => GlobalTheory.HTLiftLie.lieMult_of_sqZeroLift p D R b N (DualNumber k) k
              (TrivSqZeroExt.fstHom k k k).toRingHom hπ hsq tR o₀ A i h act hact k' x β' hx j
            eta := eta
            eta_add := e1
            eta_lin := e2
            eta_ker := e3
            geom := e4 },
    { φ := i
      φ₂ := φ₂
      cart := h
      sq := hsq2
      act := hact
      pol := hpol
      eta := e5 }, fun x hx => ?_⟩
  obtain ⟨d, hd⟩ := exists_crys hA₀ x (f x)
  refine ⟨d, ?_, hd⟩
  change d ∈ liftFil (divided₂ hsq) h
  rw [hE]
  exact ⟨x, hx, 0, zero_mem _, fun c => by rw [hd c, LinearMap.zero_apply, add_zero]⟩

end GlobalTheory.HTRealise

theorem GlobalTheory.UPel.HT.realise_isKS : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ f : HdR o₀.A →ₗ[k] HdR o₀.A, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) f → ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f x) := by
  intro p _ D R _ b N _ hN k _ _ t o₀ β ht φ hφ f hf
  have e1 : spMap (algebraMap k (DualNumber k)) ≫ t = spMap ((algebraMap k (DualNumber k)).comp β) := by
    rw [ht, ← GlobalTheory.Cris.spMap_comp]
  have e2 : t = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap ((algebraMap k (DualNumber k)).comp β) := by
    rw [ht, ← GlobalTheory.Cris.spMap_comp]
    exact congrArg spMap (RingHom.ext fun r => rfl)
  rw [e1]
  exact GlobalTheory.HTRealise.realise_core p D R b N hN k β t ht o₀ φ hφ f hf _ rfl e2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRhoPartDeformationDim
section
noncomputable section

namespace GlobalTheory.HTRho
open Module

def trAct {k O X X' : Type*} [Field k] [Ring O] [AddCommGroup X] [Module k X] [AddCommGroup X'] [Module k X']
    (e : X ≃ₗ[k] X') (σ : O →+* Module.End k X) : O →+* Module.End k X' where
  toFun a := e.toLinearMap ∘ₗ σ a ∘ₗ e.symm.toLinearMap
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

theorem trAct_apply {k O X X' : Type*} [Field k] [Ring O] [AddCommGroup X] [Module k X] [AddCommGroup X']
    [Module k X'] (e : X ≃ₗ[k] X') (σ : O →+* Module.End k X) (a : O) (x : X') :
    trAct e σ a x = e (σ a (e.symm x)) := rfl

theorem finrank_homO_trAct {k O X Y X' Y' : Type*} [Field k] [Ring O] [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y] [AddCommGroup X'] [Module k X'] [AddCommGroup Y'] [Module k Y']
    (eX : X ≃ₗ[k] X') (eY : Y ≃ₗ[k] Y') (σX : O →+* Module.End k X) (σY : O →+* Module.End k Y) :
    finrank k (homO σX σY) = finrank k (homO (trAct eX σX) (trAct eY σY)) := by
  have h : (homO σX σY).map (LinearEquiv.arrowCongr eX eY).toLinearMap = homO (trAct eX σX) (trAct eY σY) := by
    ext T'
    rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, mem_homO, mem_homO]
    simp only [LinearEquiv.coe_coe, LinearEquiv.arrowCongr_symm_apply, LinearMap.comp_apply, trAct_apply]
    constructor
    · intro hT a x
      have := congrArg eY (hT a (eX.symm x))
      simpa using this
    · intro hT a x
      have := hT a (eX x)
      rw [LinearEquiv.symm_apply_apply] at this
      rw [this, LinearEquiv.symm_apply_apply]
  rw [← h, LinearEquiv.finrank_map_eq]

end GlobalTheory.HTRho

namespace GlobalTheory.HTRho
open Module GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

universe v
variable {k O C : Type*} {H : Type v} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C] [Algebra C O]

theorem finrank_ks_map_cls [FiniteDimensional k H] (σ : O →+* Module.End k H) (G Z : Submodule k H)
    (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G) (hZ : ∀ a, ∀ x ∈ Z, σ a x ∈ Z) (hZG : Z ≤ G) :
    finrank k ((ksSub σ 0 G Z).map (cls G)) =
      finrank k (homO (qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx)) (qAct σ G hG)) := GlobalTheory.T.finrank_ksSub_map_cls_eq_finrank_homO σ G Z hG hZ hZG

theorem finrank_homO_crt {ι W V : Type*} [Fintype ι] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (σW : O →+* Module.End k W) (τ : O →+* Module.End k V)
    (χ : ι → C →+* k) (hχ : Function.Injective χ) (hJ : jSub τ χ ⊤ = ⊥) :
    finrank k (homO σW τ) =
      ∑ i, finrank k (homO σW (qAct τ (mSub τ (χ i) ⊤) (mSub_stable τ (χ i) ⊤ (fun _ _ _ => trivial)))) := GlobalTheory.T.characterAugmentationSubspace_quotientAction_top σW τ χ hχ hJ

theorem finrank_homO_quot {W V : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (σW : O →+* Module.End k W) (τ : O →+* Module.End k V)
    (χ : C →+* k) (hτ : ∀ c, τ (algebraMap C O c) = χ c • 1) :
    finrank k (homO σW τ) =
      finrank k (homO (qAct σW (mSub σW χ ⊤) (mSub_stable σW χ ⊤ (fun _ _ _ => trivial))) τ) := _root_.GlobalTheory.HTRho.finrank_homO_eq_quot_mSub σW τ χ hτ

theorem quot_facts {ι : Type*} (σ : O →+* Module.End k H) (G : Submodule k H) (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G)
    (χ : ι → C →+* k) :
    (jSub σ χ ⊤ ≤ G → jSub (qAct σ G hG) χ ⊤ = ⊥) ∧
    ∀ i, finrank k ((H ⧸ G) ⧸ mSub (qAct σ G hG) (χ i) ⊤) = finrank k (H ⧸ (G ⊔ mSub σ (χ i) ⊤)) := _root_.GlobalTheory.HTRho.quotFacts σ G hG χ

theorem finrank_sub_quot {ι : Type*} [Fintype ι] [FiniteDimensional k H] (σ : O →+* Module.End k H)
    (χ : ι → C →+* k) (hχ : Function.Injective χ) (Fil : Submodule k H) (hFil : ∀ a, ∀ x ∈ Fil, σ a x ∈ Fil)
    (ω : C) (r₀ r₁ : k) (hr : r₀ ≠ r₁)
    (hω : (σ (algebraMap C O ω) - r₀ • 1) * (σ (algebraMap C O ω) - r₁ • 1) = 0) (hχω : ∀ i, χ i ω = r₀)
    (hG : ∀ a, ∀ x ∈ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1),
      σ a x ∈ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1))
    (hZ : ∀ a, ∀ x ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)),
      σ a x ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)))
    (hJ : jSub σ χ ⊤ ≤ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1)) (i : ι) :
    let G := Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1)
    let Z := jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1))
    let σW := qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx)
    finrank k ((G ⧸ Z.comap G.subtype) ⧸ mSub σW (χ i) ⊤) + finrank k (H ⧸ (G ⊔ mSub σ (χ i) ⊤)) =
      finrank k (H ⧸ mSub σ (χ i) ⊤) := GlobalTheory.T.finrank_ksSub_quotient_augmentation_of_two_roots σ χ hχ Fil hFil ω r₀ r₁ hr hω hχω hG hZ hJ i

theorem count {ι : Type*} [Fintype ι] [FiniteDimensional k H] (σ : O →+* Module.End k H)
    (χ : ι → C →+* k) (hχ : Function.Injective χ) (Fil : Submodule k H) (hFil : ∀ a, ∀ x ∈ Fil, σ a x ∈ Fil)
    (ω : C) (r₀ r₁ : k) (hr : r₀ ≠ r₁)
    (hω : (σ (algebraMap C O ω) - r₀ • 1) * (σ (algebraMap C O ω) - r₁ • 1) = 0) (hχω : ∀ i, χ i ω = r₀)
    (m n : ℕ) (hm : 0 < m)
    (hrank : ∀ i, finrank k (H ⧸ mSub σ (χ i) ⊤) = m * n)
    (hJ : jSub σ χ ⊤ ≤ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1))
    (hlie : ∀ i, finrank k (H ⧸ ((Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1)) ⊔ mSub σ (χ i) ⊤)) = m)
    (hmor : ∀ i (X Y : Type v) [AddCommGroup X] [Module k X] [FiniteDimensional k X] [AddCommGroup Y] [Module k Y]
      [FiniteDimensional k Y] (σX : O →+* Module.End k X) (σY : O →+* Module.End k Y),
      (∀ c, σX (algebraMap C O c) = χ i c • 1) → (∀ c, σY (algebraMap C O c) = χ i c • 1) →
      m ^ 2 * finrank k (homO σX σY) = finrank k X * finrank k Y) :
    KSDim σ 0 (Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1))
      (jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1))) (Fintype.card ι * (n - 1)) := by
  set G := Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1) with hGdef
  set Z := jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)) with hZdef
  have hωc : ∀ a, σ a * σ (algebraMap C O ω) = σ (algebraMap C O ω) * σ a := fun a => by
    rw [← map_mul, ← map_mul, Algebra.commutes]
  have hRst : ∀ r : k, ∀ a, ∀ x ∈ LinearMap.range (σ (algebraMap C O ω) - r • 1),
      σ a x ∈ LinearMap.range (σ (algebraMap C O ω) - r • 1) := by
    rintro r a _ ⟨y, rfl⟩
    refine ⟨σ a y, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, hωc]
  have hG : ∀ a, ∀ x ∈ G, σ a x ∈ G := by
    intro a x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _)]
    exact add_mem (Submodule.mem_sup_left (hFil a y hy)) (Submodule.mem_sup_right (hRst r₀ a z hz))
  have hZ : ∀ a, ∀ x ∈ Z, σ a x ∈ Z := jSub_stable σ χ _ (hRst r₁)
  have hZG : Z ≤ G := le_trans (Submodule.span_mono (by
    rintro z ⟨r, lam, c, x, -, hc, rfl⟩; exact ⟨r, lam, c, x, trivial, hc, rfl⟩)) hJ
  have key := GlobalTheory.UPel.Sm.KSCount.ksDim_finrank σ 0 G Z
  rw [finrank_ks_map_cls σ G Z hG hZ hZG] at key
  convert key using 1
  obtain ⟨hF1, hF2⟩ := quot_facts σ G hG χ
  rw [finrank_homO_crt _ _ χ hχ (hF1 hJ)]
  rw [← Finset.card_univ, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finrank_homO_quot _ _ (χ i) (qAct_mSub_algebraMap _ (χ i))]
  have hD := finrank_sub_quot σ χ hχ Fil hFil ω r₀ r₁ hr hω hχω hG hZ hJ i
  have hM := hmor i ((G ⧸ Z.comap G.subtype) ⧸ mSub (qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx)) (χ i) ⊤)
    ((H ⧸ G) ⧸ mSub (qAct σ G hG) (χ i) ⊤) _ _ (qAct_mSub_algebraMap _ (χ i)) (qAct_mSub_algebraMap _ (χ i))
  rw [hF2 i, hlie i] at hM
  simp only at hD
  rw [hlie i, hrank i] at hD
  have h1 := Nat.eq_sub_of_add_eq hD
  rw [h1, ← Nat.mul_sub_one] at hM
  rw [show m * (n - 1) * m = m ^ 2 * (n - 1) by ring] at hM
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) hM).symm

end GlobalTheory.HTRho

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.HTRho

theorem rhoCount : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → KSDim (GlobalTheory.HTCount.crysAct o₀) 0 (Fil o₀.A ⊔ LinearMap.range (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1)) (GlobalTheory.HTCount.lieZ o₀ β) (D.a * (D.n - 1)) := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β hβ
  obtain ⟨hFree, hHodge, -, -, -⟩ := _root_.GlobalTheory.abelianDeRham
  have hA := o₀.ab
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k o₀.A hA
  obtain ⟨hfd, -, -⟩ := GlobalTheory.T.finrank_firstDeRhamHomology_hodgeFiltration_of_field hFree hHodge k o₀.A g hA hg
  have hunit : ∀ n : ℕ, n.Coprime p → IsUnit (n : k) := fun n hn => by
    simpa using (b.unit n hn).map β
  set σ := GlobalTheory.HTCount.crysAct o₀ with hσ
  set χ : Fin D.a → (𝓞 D.F →+* k) := fun i => β.comp (b.t i) with hχdef
  have hχ : Function.Injective χ := by
    intro i j hij
    by_contra hne
    have h1 := b.comax i j hne
    have hle : Ideal.span (Set.range fun x => b.t i x - b.t j x) ≤ RingHom.ker β := by
      rw [Ideal.span_le]
      rintro _ ⟨x, rfl⟩
      have := congrArg (fun f : 𝓞 D.F →+* k => f x) hij
      simp only [χ, RingHom.comp_apply] at this
      simp [RingHom.mem_ker, this]
    have h1' : (1 : R) ∈ RingHom.ker β := hle (by rw [h1]; trivial)
    simp at h1'
  have hFil : ∀ a, ∀ x ∈ Fil o₀.A, σ a x ∈ Fil o₀.A := fun a x hx => by
    haveI := o₀.act.hom a
    rw [hσ, GlobalTheory.HTCount.crysAct_apply]
    exact push_mem_Fil _ hx
  have hχω : ∀ i, χ i D.ω = β b.ρ := fun i => by simp [χ, b.t_ω]
  have hchar : ∀ n : ℕ, n.Coprime p → (n : k) ≠ 0 := fun n hn => (hunit n hn).ne_zero
  have hρk : β b.ρ ^ 2 - (D.tr : k) * β b.ρ + (D.nm : k) = 0 := by
    have := congrArg β b.ρ_root
    simpa using this
  have hr : β b.ρ ≠ (D.tr : k) - β b.ρ := by
    intro h
    have hd : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) = 0 := by
      push_cast
      linear_combination (-(D.tr : k) + 2 * β b.ρ) * h - 4 * hρk
    have hp : (p : ℕ).Prime := Fact.out
    have hcop : (D.tr ^ 2 - 4 * D.nm).natAbs.Coprime p := by
      refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hdv => D.disc_p ?_)
      exact Int.natCast_dvd.2 hdv
    apply hchar _ hcop
    have hm := congrArg (Int.cast : ℤ → k) (Int.natAbs_mul_self' (D.tr ^ 2 - 4 * D.nm))
    rw [Int.cast_mul, Int.cast_mul, hd, mul_zero, Int.cast_natCast] at hm
    exact mul_self_eq_zero.1 hm
  have hω : (σ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1) * (σ (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : k) - β b.ρ) • 1) = 0 := by
    have e1 : D.ω * D.ω - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
      rw [← D.tr_eq, ← D.nm_eq]; ring
    have e2 : σ (algebraMap (𝓞 D.F) D.O (D.ω * D.ω - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F))) = 0 := by
      rw [e1]; simp
    simp only [map_add (f := _), map_sub, map_mul, map_intCast] at e2
    refine LinearMap.ext fun x => ?_
    have e3 := congrArg (fun T => T x) e2
    simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at e3
    simp only [Module.End.intCast_apply, ← Int.cast_smul_eq_zsmul k] at e3
    simp only [LinearMap.smul_apply, Module.End.one_apply, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.zero_apply, map_sub, map_smul]
    set w := σ (algebraMap (𝓞 D.F) D.O D.ω)
    have : β b.ρ * ((D.tr : k) - β b.ρ) = D.nm := by linear_combination -hρk
    linear_combination (norm := module) e3 - hρk • x
  have hS2 := GlobalTheory.T.harrisTaylor_rho_part_lie_deRham_quotient p D R b N ‹_› ‹_› k t o₀ β hβ
  have key := count σ χ hχ (Fil o₀.A) hFil D.ω (β b.ρ) ((D.tr : k) - β b.ρ) hr hω hχω D.m D.n D.m_pos
    (GlobalTheory.T.harrisTaylor_finrank_deRham_quotient_character p D R b N ‹_› ‹_› k t o₀ β hβ) hS2.1 hS2.2
    (fun i X Y _ _ _ _ _ _ σX σY hX hY => by
      let eX := (Module.finBasis k X).equivFun
      let eY := (Module.finBasis k Y).equivFun
      rw [finrank_homO_trAct eX eY σX σY]
      have := GlobalTheory.T.finrank_hom_harrisTaylorOrder_morita p D k hchar (χ i) _ _ (trAct eX σX) (trAct eY σY)
        (fun c => LinearMap.ext fun x => by rw [trAct_apply, hX]; simp) (fun c => LinearMap.ext fun x => by rw [trAct_apply, hY]; simp)
      rwa [← eX.finrank_eq, ← eY.finrank_eq] at this)
  rw [Fintype.card_fin] at key
  exact key

end GlobalTheory.HTRho
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyOfDegreeIntActionHarrisTaylor
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTTors

theorem isIsogDeg_of_geomFibres (S : Scheme.{0}) (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) (φ : A ⟶ A)
    (d : ℕ) (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S),
      GlobalTheory.IwLevel.IsIsogDeg ((Over.pullback t).map φ) d) : GlobalTheory.IwLevel.IsIsogDeg φ d := by
  have := hA.smooth
  have hfin : IsFinite φ.left := GlobalTheory.T.abelianScheme_endomorphism_finite_of_geometric_fibres S A hA φ fun k _ _ t => (h k t).fin
  have hflat : Flat φ.left :=
    GlobalTheory.T.flat_of_finite_flat_geometric_fibres_over_base S A A φ inferInstance inferInstance inferInstance hfin fun k _ _ t => (h k t).flat
  refine ⟨hfin, hflat, GlobalTheory.AbLaw.MulN.surjective_of_geomFibres φ fun k _ _ t => (h k t).surj, fun y => ?_⟩
  let K := AlgebraicClosure (A.left.residueField y)
  let u : Sp K ⟶ A.left := spMap (algebraMap (A.left.residueField y) K) ≫ A.left.fromSpecResidueField y
  let t := u ≫ A.hom
  let q : Sp K := (⊥ : PrimeSpectrum K)
  let v : Sp K ⟶ pullback A.hom t := pullback.lift u (𝟙 _) (by simp [t])
  have hP := GlobalTheory.AbLaw.MulN.isPullback_baseChange t φ
  have e := Scheme.Hom.finrank_of_isPullback _ _ _ _ hP (v q)
  have hv : pullback.fst A.hom t (v q) = y := by
    rw [← Scheme.Hom.comp_apply]
    have : v ≫ pullback.fst A.hom t = u := pullback.lift_fst _ _ _
    rw [this]
    exact (Scheme.Hom.comp_apply _ _ q).trans (Scheme.fromSpecResidueField_apply y _)
  rw [hv] at e
  rw [← e]
  exact (h K t).rank _

theorem isIsogDeg_fibre (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A] (hA : IsAbelianScheme A)
    (F : Type) [Field F] [NumberField F] (ρ : OAct (𝓞 F) A) (l d : ℕ) (hl : l.Prime) (hl0 : (l : k) ≠ 0)
    (hcard : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ l = 1} = l ^ (d * Module.finrank ℚ F))
    (c : 𝓞 F) (hc : c ≠ 0) : GlobalTheory.IwLevel.IsIsogDeg (ρ.act c) ((Algebra.norm ℤ c).natAbs ^ d) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.isFinite_and_finrank_act_eq_norm_pow k A hA F ρ l d hl hl0 hcard c hc
  exact GlobalTheory.T.isogeny_degree_of_fibre_rank k A hA _ (ρ.hom c) h1 _ h2

def pullAct {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {S : Scheme.{0}} {A : Over S} [GrpObj A]
    [IsCommMonObj A] (act : GlobalTheory.UPel.HT.OActN D.O A) {T : Scheme.{0}} (t : T ⟶ S) :
    OAct (𝓞 D.F) ((Over.pullback t).obj A) where
  act c := (Over.pullback t).map (act.act (algebraMap (𝓞 D.F) D.O c))
  hom c := by have := act.hom (algebraMap (𝓞 D.F) D.O c); infer_instance
  one := by rw [map_one, act.one, CategoryTheory.Functor.map_id]
  mul a b := by rw [mul_comm a b, map_mul, act.mul, Functor.map_comp]
  add a b := by
    rw [map_add (f := _), act.add]
    exact map_mul (Over.pullback t).homMonoidHom _ _

theorem isIsogDeg_intAct : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (c : 𝓞 D.F),
    c ≠ 0 → GlobalTheory.IwLevel.IsIsogDeg (o.act.act (algebraMap (𝓞 D.F) D.O c)) ((Algebra.norm ℤ c).natAbs ^ (D.m * D.n)) := by
  intro p _ D R _ b N S s o c hc
  refine isIsogDeg_of_geomFibres S o.A o.ab _ _ fun k _ _ t => ?_
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (t ≫ s)
  have hβ : t ≫ s = spMap φ.hom := by rw [← hφ]; rfl
  obtain ⟨I, -⟩ := o.geom k t φ.hom hβ
  obtain ⟨l, hlp, hl⟩ := Nat.exists_infinite_primes (p + 1)
  have hlp' : l ≠ p := by omega
  have hcop : l.Coprime p := (Nat.coprime_primes hl (Fact.out)).2 hlp'
  have hl0 : (l : k) ≠ 0 := by
    have := (b.unit l hcop).map φ.hom
    rw [map_natCast] at this
    exact this.ne_zero
  have hcount := GlobalTheory.T.card_lTorsion_eq_pow_of_tateSimilitude p D k _ _ _ I l hl hlp'
  let e := GlobalTheory.TorsionLift.ptsEquiv t o.A (𝟙_ (Over (Sp k))) t (Category.id_comp t)
  have hc2 : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ (Over.pullback t).obj o.A // x ^ l = 1} =
      l ^ ((D.m * D.n) * Module.finrank ℚ D.F) := by
    rw [← hcount]
    refine Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)
    show x ^ l = 1 ↔ e x ^ l = 1
    rw [← map_pow, map_eq_one_iff e e.injective]
  exact isIsogDeg_fibre k _ (GlobalTheory.isAbelianScheme_pullback_obj t o.A o.ab) D.F (pullAct o.act t) l _ hl hl0 hc2 c hc

end GlobalTheory.HTTors
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogenyOfSimilitudePullbackObjectsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPIsogenyOfSimilitude_pullback_objects : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N c : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (f : S' ⟶ S) (o o' : Obj b N s) (o₁ o₁' : Obj b N s') (m : ObjMap o₁ o f) (m' : ObjMap o₁' o' f) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ → ∃ ψ₁ : o₁.A ⟶ o₁'.A, IsPIsog c o₁ o₁' ψ₁ ∧ m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ := by
  first | (exact @GlobalTheory.UPel.HT.ESPull.isPIsog_pull) | (exact GlobalTheory.UPel.HT.ESPull.isPIsog_pull) | (intros; apply GlobalTheory.UPel.HT.ESPull.isPIsog_pull  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentPolynomialTateTwistCohomologyVanishingIndStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentPolynomial_tateTwistCohomology_vanishing_inductive : ∀ (q : ℕ) [NeZero q] (n : ℤ), 2 ≤ n → (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) → ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Subsingleton (Ht q (sp (LaurentPolynomial A)) n i) := by
  first | (exact @GlobalTheory.EtC.GmStep.gm_vanishing_step) | (exact GlobalTheory.EtC.GmStep.gm_vanishing_step) | (intros; apply GlobalTheory.EtC.GmStep.gm_vanishing_step  <;> assumption)
end

