module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3084
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniqueIsConnOfLift
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0046
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentCompatibility
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0404
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2768
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2241
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemPowOfMemMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3086
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2886
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickBundleUniqueOfOrderLinearIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBCTrivSqZeroExt
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroCrys

theorem isBC_trivSqZeroExt : ∀ (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V]
    [IsCentralScalar k V] (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ →
    ∀ (h2 : RingHom.ker (TrivSqZeroExt.fstHom k k V).toRingHom ^ 2 = 0)
      (m : GrpMor (dp0 k) (𝟙 _) A₀ (divided₂ h2) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀
        (algebraMap k (TrivSqZeroExt k V)) (𝟙 _) (Over.Hom.left (𝟙 A₀))), m.IsBC := by
  intro k _ V _ _ _ _ A₀ _ hA h2 m
  have := hA.smooth
  obtain ⟨g, hg⟩ := GlobalTheory.SerreDim.exists_dim_of_grpObj A₀
  have e : (𝟙 _ : Sp k ⟶ Sp k) = spMap (RingHom.id k) := (Cris.spMap_id k).symm
  have h := (GlobalTheory.CrysConn.isGrpPullback_refl A₀).congr e rfl
  have key : ∀ (t : Sp k ⟶ Sp k), t = spMap (RingHom.id k) →
      ∀ m : GrpMor (dp0 k) t A₀ (divided₂ h2) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀
        (algebraMap k (TrivSqZeroExt k V)) (𝟙 _) (Over.Hom.left (𝟙 A₀)), m.IsBC := by
    rintro _ rfl m
    exact GlobalTheory.CrysConn.isBC_of_lift _root_.GlobalTheory.abelianDeRham hA hg (isDPNilpotent_bot k) Function.surjective_id
      ((RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id) h (isDPNilpotent_squareZero _)
      (fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩) rfl m (GlobalTheory.CrysConn.isGrpPullback_refl A₀)
  exact key _ e m

end GlobalTheory.SqZeroCrys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPolFormIsNabla
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.LogKS GlobalTheory.LogDR
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PolFormNabla

theorem cupSquare_eps {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) : GlobalTheory.AbDual.CupSquare (epsDP R) (GlobalTheory.DeRham.epsRed R) A := by
  obtain ⟨C, _, φ, j, hφ, hic, -⟩ := exists_const A
  have hC := PolPull.isAbelianScheme_of_isGrpPullback hA hφ
  have gC := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hφ.1 hg
  have su : Function.Surjective (TrivSqZeroExt.fstHom R R R).toRingHom := fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
  exact GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys GlobalTheory.abelianDeRham.1 GlobalTheory.abelianDualCrystal.2
    (isDPNilpotent_squareZero _) su rfl hC gC hic.1 (liftMor (epsDP R) hic)

end GlobalTheory.PolFormNabla
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentKummerCupProductMapBijectiveFiniteStrictH
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

noncomputable section
namespace GlobalTheory.EtC.LaurentMapPullbackBijective

theorem laurentMap_coeff {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (p : LaurentPolynomial A) (n : ℤ) :
    (laurentMap f p).coeff n = f (p.coeff n) := by
  unfold laurentMap
  simp

theorem laurentMap_id (A : Type) [CommRing A] : laurentMap (RingHom.id A) = RingHom.id _ :=
  AddMonoidAlgebra.mapRingHom_id

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (sp A) := by
  simp [spMap]

theorem pull_bijective_of_inverse (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : B →+* A)
    (hgf : g.comp f = RingHom.id A) (hfg : f.comp g = RingHom.id B) (n i : ℤ) :
    Function.Bijective (pull _ (spMap f) (tw q i) n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨pull _ (spMap g) (tw q i) n, fun x => ?_, fun y => ?_⟩
  · rw [← GmPhiNat.pull_spMap_comp, hgf, spMap_id, pull_id]
  · rw [← GmPhiNat.pull_spMap_comp, hfg, spMap_id, pull_id]

theorem ht_subsingleton (q : ℕ) (T : Type) [CommRing T] [Subsingleton T] (n i : ℤ) :
    Subsingleton (Ht q (sp T) n i) := by
  have hb := GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q T T n i
  have hfs : RingHom.fst T T = RingHom.snd T T := RingHom.ext fun _ => Subsingleton.elim _ _
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, hx⟩ := hb.2 (a, b)
  have h1 := congrArg Prod.fst hx
  have h2 := congrArg Prod.snd hx
  simp only at h1 h2
  rw [hfs] at h1
  exact h1.symm.trans h2

theorem laurent_subsingleton (T : Type) [CommRing T] [Subsingleton T] : Subsingleton (LaurentPolynomial T) := by
  refine subsingleton_of_zero_eq_one ?_
  rw [← map_zero (LaurentPolynomial.C : T →+* LaurentPolynomial T), ← map_one (LaurentPolynomial.C : T →+* LaurentPolynomial T),
    Subsingleton.elim (0 : T) 1]

theorem gmPhi_bijective_of_subsingleton (q : ℕ) (T : Type) [CommRing T] [Subsingleton T] (i : ℤ) :
    Function.Bijective (gmPhi q T i) := by
  haveI := ht_subsingleton q T 0 (i - 1)
  haveI := laurent_subsingleton T
  haveI := ht_subsingleton q (LaurentPolynomial T) 1 i
  exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

theorem gmPhi_bijective_of_equiv (h6 : DivisorNaturality) (q : ℕ) [NeZero q] {T T' : Type} [CommRing T] [CommRing T']
    (e : T ≃+* T') (hq : IsUnit (q : T)) (i : ℤ) (h : Function.Bijective (gmPhi q T i)) :
    Function.Bijective (gmPhi q T' i) := by
  have hcomm : (gmPhi q T' i) ∘ (pull _ (spMap (e : T →+* T')) _ 0) =
      (pull _ (spMap (laurentMap (e : T →+* T'))) _ 1) ∘ (gmPhi q T i) :=
    funext fun a => (gmPhi_nat h6 q (e : T →+* T') hq i a).symm
  have hgf : (e.symm : T' →+* T).comp (e : T →+* T') = RingHom.id T := by ext; simp
  have hfg : (e : T →+* T').comp (e.symm : T' →+* T) = RingHom.id T' := by ext; simp
  have hpull := pull_bijective_of_inverse q (e : T →+* T') (e.symm : T' →+* T) hgf hfg 0 (i - 1)
  have hpullL := pull_bijective_of_inverse q (laurentMap (e : T →+* T')) (laurentMap (e.symm : T' →+* T))
    (by rw [← GmPhiNat.laurentMap_comp, hgf, laurentMap_id])
    (by rw [← GmPhiNat.laurentMap_comp, hfg, laurentMap_id]) 1 i
  rw [← Function.Bijective.of_comp_iff _ hpull, hcomm]
  exact hpullL.comp h

theorem laurentProd_bijective (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂] :
    Function.Bijective ((laurentMap (RingHom.fst T₁ T₂)).prod (laurentMap (RingHom.snd T₁ T₂))) := by
  constructor
  · intro p p' h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [RingHom.prod_apply] at h1 h2
    apply AddMonoidAlgebra.ext
    refine Finsupp.ext fun n => ?_
    have e1 := congrArg (fun r => r.coeff n) h1
    have e2 := congrArg (fun r => r.coeff n) h2
    simp only [laurentMap_coeff, RingHom.coe_fst, RingHom.coe_snd] at e1 e2
    exact Prod.ext e1 e2
  · rintro ⟨p₁, p₂⟩
    refine ⟨AddMonoidAlgebra.ofCoeff (Finsupp.zipWith Prod.mk (by simp) p₁.coeff p₂.coeff), ?_⟩
    simp only [RingHom.prod_apply]
    refine Prod.ext (AddMonoidAlgebra.ext ?_) (AddMonoidAlgebra.ext ?_)
    · ext n; simp [laurentMap_coeff]
    · ext n; simp [laurentMap_coeff]

theorem gmPhi_bijective_prod (h6 : DivisorNaturality) (q : ℕ) [NeZero q] (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂]
    (hq : IsUnit (q : T₁ × T₂)) (i : ℤ) (h₁ : Function.Bijective (gmPhi q T₁ i))
    (h₂ : Function.Bijective (gmPhi q T₂ i)) : Function.Bijective (gmPhi q (T₁ × T₂) i) := by
  set f₁ := RingHom.fst T₁ T₂
  set f₂ := RingHom.snd T₁ T₂
  set ψ := (laurentMap f₁).prod (laurentMap f₂)
  have hα := GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q T₁ T₂ 0 (i - 1)
  have hγ := GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q (LaurentPolynomial T₁) (LaurentPolynomial T₂) 1 i
  have hψ : Function.Bijective ψ := laurentProd_bijective T₁ T₂
  let e := RingEquiv.ofBijective ψ hψ
  have hgf : e.symm.toRingHom.comp e.toRingHom = RingHom.id _ := RingHom.ext fun x => e.symm_apply_apply x
  have hfg : e.toRingHom.comp e.symm.toRingHom = RingHom.id _ := RingHom.ext fun x => e.apply_symm_apply x
  have hψpull := pull_bijective_of_inverse q e.toRingHom e.symm.toRingHom hgf hfg 1 i
  have he : e.toRingHom = ψ := rfl
  have hl₁ : laurentMap f₁ = (RingHom.fst _ _).comp ψ := rfl
  have hl₂ : laurentMap f₂ = (RingHom.snd _ _).comp ψ := rfl
  let β := fun y : Ht q (sp (LaurentPolynomial (T₁ × T₂))) 1 i =>
    (pull _ (spMap (laurentMap f₁)) _ 1 y, pull _ (spMap (laurentMap f₂)) _ 1 y)
  have hβ : Function.Bijective β := by
    have : β = (fun x : Ht q (sp (LaurentPolynomial T₁ × LaurentPolynomial T₂)) 1 i =>
        (pull _ (spMap (RingHom.fst (LaurentPolynomial T₁) (LaurentPolynomial T₂))) _ 1 x,
          pull _ (spMap (RingHom.snd (LaurentPolynomial T₁) (LaurentPolynomial T₂))) _ 1 x)) ∘
        (pull _ (spMap ψ) _ 1) := by
      funext y
      simp only [β, Function.comp_apply, hl₁, hl₂, GmPhiNat.pull_spMap_comp]
    rw [this]
    rw [he] at hψpull
    exact hγ.comp hψpull
  have hu₁ : IsUnit (q : T₁) := by simpa using hq.map f₁
  have hu₂ : IsUnit (q : T₂) := by simpa using hq.map f₂
  have hcomm : β ∘ (gmPhi q (T₁ × T₂) i) =
      (Prod.map (gmPhi q T₁ i) (gmPhi q T₂ i)) ∘
        (fun x : Ht q (sp (T₁ × T₂)) 0 (i - 1) => (pull _ (spMap f₁) _ 0 x, pull _ (spMap f₂) _ 0 x)) := by
    funext a
    simp only [β, Function.comp_apply, Prod.map_apply]
    rw [gmPhi_nat h6 q f₁ hq i a, gmPhi_nat h6 q f₂ hq i a]
  rw [← Function.Bijective.of_comp_iff' hβ, hcomm]
  exact (h₁.prodMap h₂).comp hα

end GlobalTheory.EtC.LaurentMapPullbackBijective


open GlobalTheory.EtC.LaurentMapPullbackBijective in
theorem GlobalTheory.EtC.GmStep.gmPhi_bijective_finite : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ (T : Type) [CommRing T] [Algebra A T], Module.Finite A T → ∀ i : ℤ, Function.Bijective (gmPhi q T i) := by
  intro q _ A _ hA hq T _ _ hT
  have h6 : DivisorNaturality := GlobalTheory.T.cup_chern_kummer_pullback_naturality
  have hunit : ∀ (S : Type) [CommRing S] [Algebra A S], IsUnit (q : S) := fun S _ _ => by
    simpa using hq.map (algebraMap A S)
  exact GlobalTheory.T.finiteAlgebra_strictlyHenselian_induction A hA (fun S _ _ => ∀ i : ℤ, Function.Bijective (gmPhi q S i))
    (fun S S' _ _ _ _ e h i => gmPhi_bijective_of_equiv h6 q e.toRingEquiv (hunit S) i (h i))
    (fun S _ _ _ i => gmPhi_bijective_of_subsingleton q S i)
    (fun S₁ S₂ _ _ _ _ _ _ h₁ h₂ i => gmPhi_bijective_prod h6 q S₁ S₂ (hunit (S₁ × S₂)) i (h₁ i) (h₂ i))
    (fun S _ _ _ hS i => GlobalTheory.T.laurentKummerCupProduct_bijective_strictlyHenselian q S hS (hunit S) i)
    T hT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LcCutTwoClosedPointsOneCentre
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

theorem logCanonicalCut_two_points : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (D : X → ℚ) (d h : ℚ) (x x' z : X) (j : ℕ), IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → QNum p N d D → 0 ≤ d → IsClosed ({x} : Set X) → IsClosed ({x'} : Set X) → LcAt p n (Δ + D) x → LcAt p n (Δ + D) x' → z ⤳ x → z ⤳ x' → (z = genericPoint X ∨ IsNkltCentre p n (Δ + D) z) → topologicalKrullDim (closure ({z} : Set X)) = (j + 1 : ℕ) → 0 < h → 2 * ((j + 1 : ℕ) : ℚ) ^ (j + 1) < h ^ (j + 1) * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin (j + 1) => N : ℤ) → ∃ (D' : X → ℚ) (d' : ℚ), 0 ≤ d' ∧ d' ≤ d + h ∧ QNum p N d' D' ∧ ((LcCut p n (Δ + D') x j ∧ ¬ KltAt p n (Δ + D') x') ∨ (LcCut p n (Δ + D') x' j ∧ ¬ KltAt p n (Δ + D') x)) := by
  intro hPr hNa hNe X _ _ _ p n hp hn
  letI := algebraΓOfHom p
  intro Δ m G N D d h x x' z j hΔ hklt hm hG hN hD hd hx hx' hlx hlx' hzx hzx' hz hdim hh hpos
  classical
  have hDq : IsQCart D := hD.isQCart
  obtain ⟨B, δ₀, hδ0, hδ1, hB, hoff, hnk, hpres⟩ :=
    GlobalTheory.T.exists_divisor_nonKlt_at_points_not_containing_centre hPr hNa hNe X p n hp hn Δ m G N D {x, x'} z (j + 1) h hΔ hklt hm hG hN hDq
      (by
        intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact ⟨hx, hzx⟩
        · rw [Finset.mem_singleton.1 hy]; exact ⟨hx', hzx'⟩)
      (by omega) hdim hz hh
      (by
        have hc : (({x, x'} : Finset X).card : ℚ) ≤ 2 := by
          exact_mod_cast Finset.card_le_two
        have hk : (0 : ℚ) ≤ ((j + 1 : ℕ) : ℚ) ^ (j + 1) := by positivity
        calc (({x, x'} : Finset X).card : ℚ) * ((j + 1 : ℕ) : ℚ) ^ (j + 1)
            ≤ 2 * ((j + 1 : ℕ) : ℚ) ^ (j + 1) := mul_le_mul_of_nonneg_right hc hk
          _ < _ := hpos)
  have hBq : IsQCart B := hB.isQCart
  have hδ1' : (0 : ℚ) ≤ 1 - δ₀ := by linarith
  have hDδ : IsQCart ((1 - δ₀) • D) := (_root_.GlobalTheory.QCartCone.isQCart_cone X D D (1 - δ₀) hDq hDq hδ1').2.1
  have hkx : KltAt p n (Δ + (1 - δ₀) • D) x :=
    _root_.GlobalTheory.PairStep.kltAt_add_smul_of_lcAt X p n hp hn Δ D δ₀ x hDq (hklt x) hlx hδ0 hδ1
  have hkx' : KltAt p n (Δ + (1 - δ₀) • D) x' :=
    _root_.GlobalTheory.PairStep.kltAt_add_smul_of_lcAt X p n hp hn Δ D δ₀ x' hDq (hklt x') hlx' hδ0 hδ1
  obtain ⟨c, hc0, hc1, hcl, hcn⟩ := _root_.GlobalTheory.PairStep.exists_threshold_lcAt_not_kltAt hPr X p n hp hn Δ m G ((1 - δ₀) • D) B x hm hG hDδ
    hBq hkx (hnk δ₀ hδ0.le le_rfl x (by simp))
  obtain ⟨c', hc0', hc1', hcl', hcn'⟩ := _root_.GlobalTheory.PairStep.exists_threshold_lcAt_not_kltAt hPr X p n hp hn Δ m G ((1 - δ₀) • D) B x' hm hG
    hDδ hBq hkx' (hnk δ₀ hδ0.le le_rfl x' (by simp))
  have hq1 : QNum p N ((1 - δ₀) * d) ((1 - δ₀) • D) := _root_.GlobalTheory.PairStep.qNum_smul X p hp N d (1 - δ₀) D hδ1' hD
  have key : ∀ e : ℚ, 0 < e → e ≤ 1 → ∃ d' : ℚ, 0 ≤ d' ∧ d' ≤ d + h ∧
      QNum p N d' ((1 - δ₀) • D + e • B) := by
    intro e he0 he1
    refine ⟨(1 - δ₀) * d + e * h, by positivity, by nlinarith, ?_⟩
    exact qNum_add X p hp N _ _ _ _ hq1 (_root_.GlobalTheory.PairStep.qNum_smul X p hp N h e B he0.le hB)
  rcases le_total c' c with hcc | hcc
  · obtain ⟨d', h1, h2, h3⟩ := key c hc0 hc1
    refine ⟨(1 - δ₀) • D + c • B, d', h1, h2, h3, Or.inl ⟨?_, ?_⟩⟩
    · rw [← add_assoc]
      exact _root_.GlobalTheory.PairStep.logCanonicalCut_of_step X p n hp hn Δ D B δ₀ c x z j (hklt x) hDq hBq hlx hδ0 hδ1 hc1 hoff hpres
        hdim hcl hcn
    · rw [← add_assoc]
      intro hk
      exact hcn' ((_root_.GlobalTheory.PairStep.kltAt_lcAt_of_le_coeff X p n hp hn (Δ + (1 - δ₀) • D) B c' c x' hBq hcc).1 hk)
  · obtain ⟨d', h1, h2, h3⟩ := key c' hc0' hc1'
    refine ⟨(1 - δ₀) • D + c' • B, d', h1, h2, h3, Or.inr ⟨?_, ?_⟩⟩
    · rw [← add_assoc]
      exact _root_.GlobalTheory.PairStep.logCanonicalCut_of_step X p n hp hn Δ D B δ₀ c' x' z j (hklt x') hDq hBq hlx' hδ0 hδ1 hc1' hoff
        hpres hdim hcl' hcn'
    · rw [← add_assoc]
      intro hk
      exact hcn ((_root_.GlobalTheory.PairStep.kltAt_lcAt_of_le_coeff X p n hp hn (Δ + (1 - δ₀) • D) B c c' x hBq hcc).1 hk)

end GlobalTheory.PairStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartGaloisRigidStalk
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart.Inj

theorem spMap_comp_eq {S : Scheme.{0}} {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] (ξ : Sp R ⟶ S)
    (ρ₁ ρ₂ : R →+* R') (h : ρ₁.comp (Scheme.stalkClosedPointTo ξ).hom = ρ₂.comp (Scheme.stalkClosedPointTo ξ).hom) :
    spMap ρ₁ ≫ ξ = spMap ρ₂ ≫ ξ := by
  rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
    ← Spec.map_comp]
  congr 2
  ext a
  exact congrArg (fun f => f a) h

theorem genPt_eq {X S : Scheme.{0}} (j : X ⟶ S) [Mono j] {R R' : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    [CommRing R'] [IsDomain R'] (ξ : Sp R ⟶ S) (y : Sp (FractionRing R) ⟶ X) (hy : y ≫ j = jK R ≫ ξ)
    (ρ₁ ρ₂ : R →+* R') (h : ρ₁.comp (Scheme.stalkClosedPointTo ξ).hom = ρ₂.comp (Scheme.stalkClosedPointTo ξ).hom)
    (κ₁ κ₂ : Sp (FractionRing R') ⟶ Sp (FractionRing R)) (h₁ : κ₁ ≫ jK R = jK R' ≫ spMap ρ₁)
    (h₂ : κ₂ ≫ jK R = jK R' ≫ spMap ρ₂) : κ₁ ≫ y = κ₂ ≫ y := by
  rw [← cancel_mono j, Category.assoc, Category.assoc, hy, ← Category.assoc, ← Category.assoc, h₁, h₂,
    Category.assoc, Category.assoc, spMap_comp_eq ξ ρ₁ ρ₂ h]

theorem stalk_comp_eq {X : Scheme.{0}} {W V : Type} [CommRing W] [IsLocalRing W] [CommRing V] [IsLocalRing V]
    (u : Sp W ⟶ X) (g₁ g₂ : W →+* V) [IsLocalHom g₁] [IsLocalHom g₂] (hu : spMap g₁ ≫ u = spMap g₂ ≫ u) :
    g₁.comp (Scheme.stalkClosedPointTo u).hom = g₂.comp (Scheme.stalkClosedPointTo u).hom := by
  have l : ∀ (g : W →+* V) [IsLocalHom g], IsLocalHom (Scheme.stalkClosedPointTo u ≫ CommRingCat.ofHom g).hom := by
    intro g _
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom]; infer_instance
  have e : ∀ (g : W →+* V) [IsLocalHom g], spMap g ≫ u = (SpecToEquivOfLocalRing X (.of V)).symm
      ⟨u (closedPoint W), Scheme.stalkClosedPointTo u ≫ CommRingCat.ofHom g, l g⟩ := by
    intro g _
    rw [SpecToEquivOfLocalRing_symm_apply, Spec.map_comp_assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have hinj := (SpecToEquivOfLocalRing X (.of V)).symm.injective ((e g₁).symm.trans (hu.trans (e g₂)))
  obtain ⟨h₁, h₂⟩ := SpecToEquivOfLocalRing_eq_iff.mp hinj
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] at h₂
  ext a
  have := congrArg (fun q => q.hom a) h₂
  simpa using this

theorem base_eq {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {φ : InvFun ℤ} (C : Taut ζ g n φ) {V : Type}
    [CommRing V] [IsLocalRing V] [IsNoetherianRing V] (θ₁ θ₂ : C.R →+* V) [IsLocalHom θ₁] [IsLocalHom θ₂]
    (hu : spMap (θ₁.comp C.iw) ≫ C.u = spMap (θ₂.comp C.iw) ≫ C.u) (hm : ∀ r, θ₁ r - θ₂ r ∈ maximalIdeal V) :
    θ₁.comp C.iw = θ₂.comp C.iw := by
  haveI : IsLocalHom C.iw := C.ψ_loc
  haveI : IsNoetherianRing C.W := C.noeth
  have hO := stalk_comp_eq C.u (θ₁.comp C.iw) (θ₂.comp C.iw) hu
  exact GlobalTheory.EtUniq.localHom_ext _ _ _ _ C.complete C.u_et C.u_sep _ _ inferInstance inferInstance hO (fun w => hm _)

theorem eq_of_base_coord {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {φ : InvFun ℤ} (C : Taut ζ g n φ) {V : Type}
    [CommRing V] [IsLocalRing V] [IsNoetherianRing V] (θ₁ θ₂ : C.R →+* V) [IsLocalHom θ₁] [IsLocalHom θ₂]
    (hW : θ₁.comp C.iw = θ₂.comp C.iw) (hs : ∀ k, θ₁ (C.s k) = θ₂ (C.s k)) : θ₁ = θ₂ := by
  refine GlobalTheory.TChart.cuniq _ _ _ C.ψ C.compl θ₁ θ₂ inferInstance inferInstance ?_
  apply MvPolynomial.ringHom_ext
  · intro w
    exact congrArg (fun f => f w) hW
  · intro k
    exact hs k

end GlobalTheory.TChart.Inj


open GlobalTheory.TChart.Inj in
theorem GlobalTheory.TChart.galRigid_stalk_of_isFam : ∀ {g n : ℕ} {φ : InvFun ℤ}, 3 ≤ n → ∀ (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (j : F.X ⟶ S) [IsOpenImmersion j], ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → GalRigid (Scheme.stalkClosedPointTo ξ).hom := by
  intro g n φ hn F S j _ C G₁ _ _ y α₁ ξ hF hy R' _ _ _ θ σ hR' hθ hfin hσ hfix hres
  haveI : IsNoetherianRing R' := hR'.1
  haveI : IsLocalHom θ := RingHom.IsIntegral.isLocalHom hfin.to_isIntegral hθ
  haveI : IsLocalHom ((σ : R' →+* R').comp θ) := by
    haveI : IsLocalHom (σ : R' →+* R') := inferInstance
    infer_instance
  obtain ⟨κ₁, hκ₁⟩ := GlobalTheory.PolDeg.exists_genericMap hθ
  obtain ⟨κ₂, hκ₂⟩ := GlobalTheory.PolDeg.exists_genericMap (ρ := (σ : R' →+* R').comp θ) (σ.injective.comp hθ)
  have hf : θ.comp (Scheme.stalkClosedPointTo ξ).hom =
      ((σ : R' →+* R').comp θ).comp (Scheme.stalkClosedPointTo ξ).hom :=
    RingHom.ext fun a => (hfix a).symm
  have hyy := genPt_eq j ξ y hy _ _ hf κ₁ κ₂ hκ₁ hκ₂
  have hm : ∀ r, θ r - ((σ : R' →+* R').comp θ) r ∈ maximalIdeal R' := fun r => by
    rw [← neg_sub]; exact neg_mem (hres r)
  obtain ⟨hu, hs'⟩ := _root_.GlobalTheory.TInj.tautChart_eq_of_genPt hn F C G₁ y α₁ hF R' θ ((σ : R' →+* R').comp θ) hR' hθ (σ.injective.comp hθ)
    inferInstance inferInstance κ₁ κ₂ hκ₁ hκ₂ hyy
  have hW := base_eq C θ ((σ : R' →+* R').comp θ) hu hm
  have e := eq_of_base_coord C θ ((σ : R' →+* R').comp θ) hW (hs' hW)
  intro r
  exact (congrArg (fun f => f r) e).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTorusTranslatesTwistedSums
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

theorem GlobalTheory.Poinc.Sep.twistSum_translate : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ (sg : ℤˣ) (eps : X₁.S.Gam → X₁.S.Gam → ℕ), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → X) → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ zt h : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ zt = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) → X₁.M.stalkHom z₁ h = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps (lab c) τ) * X₁.S.th (lab c + τ) / X₁.S.th x₀ → ∀ wt : (Fin 8 → X) → ZMod (X₁.S.r * X₁.S.N), (∀ a mu, 𝔪.YY a mu → wt mu = (sg : ℤ) • eStd X₁.S.g _ τ a) → SumI (maximalIdeal V) (fun mu => ev zt ^ (wt mu).val * T mu c) (ev h) := by
  intro g n F W Z i X₁ z₁ act x₀ hdiv
  obtain ⟨sg, hsg, hweil⟩ := GlobalTheory.T.exists_thetaTwistedSum_sign_everyMember g n F W Z i X₁ z₁ act x₀ hdiv
  classical
  let Wit : X₁.S.Gam → X₁.S.Gam → ℕ → Prop := fun a τ e =>
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V)
      (X : Type) (_ : AddCommGroup X) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X)
      (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (_ : ∀ c, lab c ∈ X₁.S.HH X₁.M z₁)
      (T : (Fin 8 → X) → C → V) (_ : 𝔪.Terms x₀ lab T) (c : C), lab c = a ∧
      TwistSum X₁ z₁ act x₀ 𝔪 lab T sg c τ e ∧
      ∃ r : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ r = X₁.S.th (lab c + τ) / X₁.S.th x₀ ∧ ev r ≠ 0
  refine ⟨sg, fun a τ => if h : ∃ e, Wit a τ e then h.choose else 0, ?_⟩
  intro V _ _ _ ev X _ m t δ 𝔪 C lab hlab T hT c τ hτ zt h hzt hh wt hwt
  obtain ⟨e₂, he₂⟩ := hsg V ev X m t δ 𝔪 C lab hlab T hT c τ hτ
  by_cases hW : ∃ e, Wit (lab c) τ e
  · beta_reduce at hh
    rw [dite_eq_left hW] at hh
    obtain ⟨V₁, _, _, _, ev₁, Y₁, _, m₁, t₁, δ₁, 𝔪₁, C₁, lab₁, hlab₁, T₁, hT₁, c₁, hc₁, hts, r, hr, hr0⟩ := hW.choose_spec
    have key := GlobalTheory.T.twistedThetaSum_zeta_exponent_independent_member g n F W Z i X₁ z₁ act x₀ hdiv sg hsg hweil V₁ ev₁ Y₁ m₁ t₁ δ₁ 𝔪₁ C₁ lab₁ hlab₁ T₁ hT₁ c₁
      V ev X m t δ 𝔪 C lab hlab T hT c hc₁ τ hτ _ e₂ hts he₂ ⟨r, hr, hr0⟩
    exact key zt h hzt hh wt hwt
  · beta_reduce at hh
    rw [dite_eq_right hW] at hh
    have hh' : X₁.M.stalkHom z₁ h = X₁.S.th (lab c + τ) / X₁.S.th x₀ := by rw [hh]; simp
    have hev : ev h = 0 := by
      by_contra hne
      exact hW ⟨e₂, V, inferInstance, inferInstance, inferInstance, ev, X, inferInstance, m, t, δ, 𝔪, C, lab, hlab, T, hT, c,
        rfl, he₂, h, hh', hne⟩
    obtain ⟨s, hs⟩ := exists_stalk_zeta X₁ z₁ (X₁.S.ζ ^ e₂)
    have := he₂ zt (s * h) hzt (by rw [map_mul, hs, hh', mul_div_assoc]) wt hwt
    rw [map_mul, hev, mul_zero] at this
    rwa [hev]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickBundleUniqueOfOrderLinearIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinTrick_bundle_unique_of_order_linear_iso : ∀ (h M d : ℕ), 0 < d → ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z₁ z₂ : SiegPre (8 * h) M (zetaAway M) t) (act₁ : GlobalTheory.ZarhinFam.ord d → (z₁.A ⟶ z₁.A)) (act₂ : GlobalTheory.ZarhinFam.ord d → (z₂.A ⟶ z₂.A)) (inc₁ : c.A ⟶ z₁.A) (pr₁ : z₁.A ⟶ c.A) (inc₂ : c.A ⟶ z₂.A) (e : z₁.A ≅ z₂.A), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z₁.Principal → z₂.Principal → IsRAct z₁.A act₁ → IsRAct z₂.A act₂ → Adj z₁.A z₁.P (GlobalTheory.ZarhinFam.bar d) act₁ → Adj z₂.A z₂.P (GlobalTheory.ZarhinFam.bar d) act₂ → IsMonHom inc₁ → IsMonHom pr₁ → inc₁ ≫ pr₁ = 𝟙 c.A → pr₁ ≫ inc₁ = act₁ (GlobalTheory.ZarhinFam.idem d) → LBIso c.P (z₁.P.pull (inc₁ ⊗ₘ inc₁).left) → LBIso c.P (z₂.P.pull (inc₂ ⊗ₘ inc₂).left) → IsMonHom e.hom → inc₁ ≫ e.hom = inc₂ → (∀ o, act₁ o ≫ e.hom = e.hom ≫ act₂ o) → LBIso z₁.P (z₂.P.pull (e.hom ⊗ₘ e.hom).left) := by
  first | (exact @GlobalTheory.ZarhinUniqBundle.lbIso_of_ordLinear) | (exact GlobalTheory.ZarhinUniqBundle.lbIso_of_ordLinear) | (intros; apply GlobalTheory.ZarhinUniqBundle.lbIso_of_ordLinear  <;> assumption)
end

