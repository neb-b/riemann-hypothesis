module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2024
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1944
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0508
public import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0323
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0315
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1428
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1166
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRuleExistsOfAlgebraicInvariants
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2021
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2040
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0475
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1520
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1706
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoPreservesRigidificationAtOriginStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iso_preserves_rigidification_at_origin : ∀ (V : Type) [CommRing V] [IsDomain V] (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G]
    (A : Over (Sp (FractionRing V))) [GrpObj A] [IsCommMonObj A] (θ : (Over.pullback (jK V)).obj G ⟶ A) [IsMonHom θ]
    (φ : A.left ⟶ G.left), θ.left ≫ φ = pullback.fst G.hom (jK V) →
    ∀ (he : eSec A ≫ φ = spMap (algebraMap V (FractionRing V)) ≫ eSec G)
    (LP : LB A.left) (LL LM : LB G.left), LP.IsLB → LL.IsLB → LM.IsLB →
    ∀ (rA : LB.Gen (LP.pull (eSec A))) (rL : LB.Gen (LL.pull (eSec G))) (rM : LB.Gen (LM.pull (eSec G)))
      (ψ : LB.Iso LP (LL.pull φ)) (e : LB.Iso LM LL) (w₀ : LB.Iso (LP.pull θ.left) (LM.pull (pullback.fst G.hom (jK V)))),
      (∀ (Z : Scheme.{0}) (r : Z ⟶ ((Over.pullback (jK V)).obj G).left) (z : Z) (i : LL.ι) (j : LM.ι) (k : LP.ι),
        pullback.fst G.hom (jK V) (r z) ∈ LL.U i → pullback.fst G.hom (jK V) (r z) ∈ LM.U j → θ.left (r z) ∈ LP.U k →
        gw w₀ r z j (fun _ => k) =
          (gm (r ≫ pullback.fst G.hom (jK V)) z (LL.U i ⊓ LM.U j) (e.s (i, j)))⁻¹ * gw ψ (r ≫ θ.left) z i k) →
      LB.Gen.Maps (LB.linCombIso ψ (K := PUnit) (fun _ => eSec A) (fun _ => 1)) rA
        (rigPullOf φ (spMap (algebraMap V (FractionRing V))) he LL rL) →
      LB.Gen.Maps (LB.linCombIso e (K := PUnit) (fun _ => eSec G) (fun _ => 1)) rM rL →
      ∀ (z : Sp (FractionRing V)) (JA : (Sp (FractionRing V) ⟶ A.left) → LP.ι) (JG : (Sp (FractionRing V) ⟶ G.left) → LM.ι),
        Good LP z JA → Good LM z JG →
        gw w₀ (eSec ((Over.pullback (jK V)).obj G)) z (JG (jK V ≫ eSec G)) (fun _ => JA (eSec A)) *
            val (L := LP) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rA (𝟙 _) z JA =
          val (L := LM) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) rM (jK V) z JG := by
  first | exact @GlobalTheory.normW_origin | exact GlobalTheory.normW_origin | (intros; apply GlobalTheory.normW_origin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricOfSameNorms
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

namespace GlobalTheory.CoverNorm.Isom

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem asIdeal_p_j (V : Cover Y) (y : V.G) : (V.p (V.j y)).asIdeal = ⊥ := by
  rw [← Scheme.Hom.comp_apply, V.pb.w, Scheme.Hom.comp_apply]
  change Ideal.comap (algebraMap (𝓞 F) F) ((V.π ≫ Y.str) y).asIdeal = ⊥
  have := ((V.π ≫ Y.str) y).isPrime
  rw [Ideal.eq_bot_of_prime ((V.π ≫ Y.str) y).asIdeal]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)

theorem mem_range_j (V : Cover Y) {x : V.X} (hx : (V.p x).asIdeal = ⊥) : x ∈ Set.range V.j := by
  rw [← V.pb.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, V.pb.isoPullback.hom.surjective.range_eq, Set.image_univ,
    Scheme.Pullback.range_fst]
  refine ⟨IsLocalRing.closedPoint F, PrimeSpectrum.ext (Eq.trans ?_ hx.symm)⟩
  change Ideal.comap (algebraMap (𝓞 F) F) (IsLocalRing.maximalIdeal F) = ⊥
  rw [IsLocalRing.maximalIdeal_eq_bot]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)

theorem j_gen_specializes (V : Cover Y) : V.j (genericPoint V.G) ⤳ genericPoint V.X := by
  have h0 : (V.p (genericPoint V.X)).asIdeal = ⊥ :=
    eq_bot_iff.2 (((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 ((PrimeSpectrum.le_iff_specializes _ _).2
      ((genericPoint_specializes (V.j (genericPoint V.G))).map V.p.continuous))).trans
        (asIdeal_p_j V _).le)
  obtain ⟨y, hy⟩ := mem_range_j V h0
  exact hy ▸ (genericPoint_specializes y).map V.j.continuous

theorem cxPts_from_generic_fibre (V : Cover Y) (τ : 𝓞 F →+* ℂ) (y' : CxPts V.p τ) :
    ∃ σ : F →+* ℂ, σ.comp (algebraMap (𝓞 F) F) = τ ∧ ∃ z : CxPts (V.π ≫ Y.str) σ, y'.1 = z.1 ≫ V.j := by
  have hτ := ringOfIntegers_hom_complex_injective F τ
  obtain ⟨σ, hσ⟩ : ∃ σ : F →+* ℂ, σ.comp (algebraMap (𝓞 F) F) = τ :=
    ⟨IsFractionRing.lift (K := F) hτ, RingHom.ext fun x => IsFractionRing.lift_algebraMap (K := F) hτ x⟩
  refine ⟨σ, hσ, ?_⟩
  have hw : y'.1 ≫ V.p = spMap σ ≫ spMap (algebraMap (𝓞 F) F) :=
    y'.2.trans ((congrArg spMap hσ.symm).trans (spMap_comp _ _))
  exact ⟨⟨V.pb.lift y'.1 _ hw, V.pb.lift_snd _ _ _⟩, (V.pb.lift_fst _ _ _).symm⟩

end GlobalTheory.CoverNorm.Isom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegOfNadelVanishingPair
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.KVFromPair

theorem subsingleton_coh_twist (hN : GlobalTheory.Published.NefNumerics) (hV : GlobalTheory.Published.NadelVanishingPair)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ) [hs : SmoothOfRelativeDimension D p] (hp : IsProjOver p)
    (K : CanonLB p D) (N : LB X) (h₁ : letI := algebraΓOfHom p; IsNef k N)
    (h₂ : letI := algebraΓOfHom p; IsBig k N) (q : ℕ) (hq : 0 < q) :
    Subsingleton (coh (twist (GlobalTheory.structureModule X) (tens K.bundle N)) q) := by
  have hNl : N.IsLB := by
    letI := algebraΓOfHom p
    exact h₁.isLB
  obtain ⟨K₁, X₁, p₁, ψ, L₁, hc, hp₁, H, hL₁, e⟩ := _root_.GlobalTheory.ProjCountableDescent.projLB_descends_to_countable_subfield k X p hp N hNl
  have hsm : Smooth p := SmoothOfRelativeDimension.smooth D p
  have hg : GeometricallyConnected p := GlobalTheory.geometricallyConnected_of_isAlgClosed p
  obtain ⟨hs₁, hg₁⟩ := _root_.GlobalTheory.FieldDescentSm.smoothOfRelativeDimension_and_geometricallyConnected_descend K₁ k X₁ X p₁ p ψ H D inferInstance hs hg
  have hne : Nonempty X₁ := ⟨ψ (Classical.arbitrary X)⟩
  have hP := LB.isLB_pull hL₁ ψ
  have ec : cls N hNl = cls (L₁.pull ψ) hP := (cls_eq_iff _ _).2 e
  have n₁ := GlobalTheory.T.isNefLineBundle_of_baseChange_field K₁ k X₁ X p₁ p ψ H hp₁ L₁ hL₁ (by
    letI := algebraΓOfHom p
    exact h₁.of_cls_eq hP ec.symm)
  have b₁ := (GlobalTheory.T.isBigLineBundle_pullback_fieldExtension_iff K₁ k X₁ X p₁ p ψ H hp₁ hp
    ((GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth p D hs).trans
      (GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth p₁ D hs₁).symm) L₁ hL₁).1 (by
    letI := algebraΓOfHom p
    exact h₂.of_cls_eq hP ec.symm)
  let C : CanonLB p₁ D := CanonLB.all p₁ D
  have v₁ := GlobalTheory.T.kawamataViehweg_vanishing_complexEmbeddedField hN hV K₁ (GlobalTheory.KeyHouse.nonempty_ringHom_complex K₁) X₁ p₁ D hp₁ hg₁
    C L₁ n₁ b₁ q hq
  have hT := isLB_tens C.isLB hL₁
  have v := (_root_.GlobalTheory.CohFieldChange.subsingleton_coh_pull_iff_of_isProjOver K₁ k X₁ X p₁ p ψ H hp₁ hp _ hT q).2 v₁
  have eK : cls K.bundle K.isLB = cls (C.bundle.pull ψ) (LB.isLB_pull C.isLB ψ) := by
    obtain ⟨w, hw, -⟩ := canonLB_baseChange K₁ k _ X₁ X p₁ p ψ D H C K
    exact (cls_eq_iff _ _).2 ⟨w, hw⟩
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq (GlobalTheory.structureModule X) (isLB_tens K.isLB hNl)
    (LB.isLB_pull hT ψ) (by
      rw [cls_tens K.isLB hNl, cls_pull hT, cls_tens C.isLB hL₁, map_add (f := _), eK, ec,
        cls_pull C.isLB, cls_pull hL₁])
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ q i).toEquiv.subsingleton_congr.2 v

theorem kawamataViehweg_of_nadelVanishingPair :
    GlobalTheory.Published.NefNumerics → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.KawamataViehweg := by
  intro hN hV k _ _ _ X a _ D hs hp K N h₁ h₂ q hq
  have ha : a = algebraΓOfHom (strHom k X) := Algebra.algebra_ext _ _ (algebraMap_eq_strHom k X)
  have v := subsingleton_coh_twist hN hV k X (strHom k X) D hp K N (ha ▸ h₁) (ha ▸ h₂) q hq
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ q (Twist.unitTwistIso _)).toEquiv.subsingleton_congr.1 v

end GlobalTheory.KVFromPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelActionIsPullbackProdMapTorsor
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

namespace GlobalTheory.CharKer

variable {S : Scheme.{0}}

theorem comp_one_hom {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (u ≫ toUnit X) (toUnit Y)]

theorem pmap_isPullback_actMap : ∀ (S : Scheme.{0}) (A A' N T : Over S) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A'), IsMonHom i → IsMonHom q → IsPullback i (toUnit N) q η[A'] → IsPullback (prMap A N T) (actMap i T) (pmap q T) (pmap q T) := by
  intro S A A' N T _ _ _ i q hi hq hker
  have hiq : i ≫ q = 1 := by rw [hker.w, Hom.one_def]
  have hpf : pmap q T ≫ fst A' T = fst A T ≫ q := by simp [pmap]
  have hps : pmap q T ≫ snd A' T = snd A T := by simp [pmap]
  have hc : prMap A N T ≫ pmap q T = actMap i T ≫ pmap q T := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, Category.assoc, hpf]
      simp only [prMap, actMap, lift_fst_assoc, mul_comp, Category.assoc, hiq]
      simp only [comp_one_hom, _root_.mul_one]
    · rw [Category.assoc, Category.assoc, hps]
      simp [prMap, actMap]
  have hfs : ∀ s : PullbackCone (pmap q T) (pmap q T), (s.fst ≫ fst A T) ≫ q = (s.snd ≫ fst A T) ≫ q := by
    intro s
    have h := congrArg (· ≫ fst A' T) s.condition
    simp only [Category.assoc, hpf] at h
    simpa only [Category.assoc] using h
  have hss : ∀ s : PullbackCone (pmap q T) (pmap q T), s.fst ≫ snd A T = s.snd ≫ snd A T := by
    intro s
    have h := congrArg (· ≫ snd A' T) s.condition
    simpa only [Category.assoc, hps] using h
  have hk : ∀ s : PullbackCone (pmap q T) (pmap q T),
      ((s.fst ≫ fst A T)⁻¹ * (s.snd ≫ fst A T)) ≫ q = toUnit s.pt ≫ η[A'] := by
    intro s
    rw [mul_comp, GrpObj.inv_comp, hfs s, _root_.inv_mul_cancel, Hom.one_def]
  refine ⟨⟨hc⟩, ⟨PullbackCone.IsLimit.mk hc
    (fun s => lift (s.fst ≫ fst A T)
      (lift (hker.lift ((s.fst ≫ fst A T)⁻¹ * (s.snd ≫ fst A T)) (toUnit _) (hk s)) (s.fst ≫ snd A T)))
    ?_ ?_ ?_⟩⟩
  · intro s
    apply CartesianMonoidalCategory.hom_ext <;> simp [prMap]
  · intro s
    apply CartesianMonoidalCategory.hom_ext
    · simp only [actMap, Category.assoc, lift_fst, comp_mul, lift_fst_assoc, lift_snd_assoc, hker.lift_fst]
      exact _root_.mul_inv_cancel_left _ _
    · simp [actMap, hss]
  · intro s m h1 h2
    have ha : m ≫ fst A (N ⊗ T) = s.fst ≫ fst A T := by rw [← h1]; simp [prMap]
    have ht : m ≫ snd A (N ⊗ T) ≫ snd N T = s.fst ≫ snd A T := by rw [← h1]; simp [prMap]
    have hb : m ≫ fst A (N ⊗ T) * m ≫ snd A (N ⊗ T) ≫ fst N T ≫ i = s.snd ≫ fst A T := by
      rw [← h2]; simp [actMap, comp_mul]
    apply CartesianMonoidalCategory.hom_ext
    · simpa using ha
    · apply CartesianMonoidalCategory.hom_ext
      · apply hker.hom_ext
        · simp only [Category.assoc, lift_snd_assoc, lift_fst_assoc, hker.lift_fst]
          rw [← ha]
          exact eq_inv_mul_of_mul_eq hb
        · exact toUnit_unique _ _
      · simpa using ht

end GlobalTheory.CharKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumFalseOfModelSectionZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEven

theorem not_keyOn_of_sec_zero : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : RigLB G)
    (σ : L.L.Sec) (x : KeyIn K) (y : Fin x.P.g → (epsR K ⟶ G)), KeyOn (RingHom.id K) x G L σ y →
    (∀ i, σ.f i = 0) → False := by
  intro K _ G _ _ L σ x y hK hσ
  obtain ⟨φ, -, ψ, -, -, -, -, hsec, -⟩ := hK
  obtain ⟨z, -, hz⟩ := x.th_ne (IsLocalRing.closedPoint K)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  have hzi : z ∈ x.P.L.U i := x.P.A.left.basicOpen_le _ hi
  have hc : φ z ∈ (⨆ a, L.L.U a) := by rw [L.isLB.cover]; trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
  let j : (L.L.pull φ).ι := fun _ => a
  have hzj : z ∈ (L.L.pull φ).U j := Set.mem_iInter.2 fun _ => ha
  have h : (L.L.pull φ).U j ⊓ x.P.L.U i ≤ φ ⁻¹ᵁ L.L.U (j PUnit.unit) :=
    inf_le_left.trans (LB.wchart_le L.L (fun _ => φ) j PUnit.unit)
  have e := hsec j i h
  rw [hσ, map_zero] at e
  have e0 : resG x.P.A.left (inf_le_right : (L.L.pull φ).U j ⊓ x.P.L.U i ≤ x.P.L.U i) (x.th.f i) = 0 := by
    have u := (ψ.s (j, i)).isUnit
    exact (u.mul_right_eq_zero).1 e.symm
  have hb : z ∈ x.P.A.left.basicOpen
      (resG x.P.A.left (inf_le_right : (L.L.pull φ).U j ⊓ x.P.L.U i ≤ x.P.L.U i) (x.th.f i)) := by
    rw [Scheme.basicOpen_res]
    exact ⟨⟨hzj, hzi⟩, hi⟩
  rw [e0, Scheme.basicOpen_zero] at hb
  exact hb

end GlobalTheory.KeyEven
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumScaleSectionsByConstant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyEven

theorem appLE_constFn {K : Type} [CommRing K] {X Y : Scheme.{0}} (p : X ⟶ Sp K) (q : Y ⟶ Sp K) (φ : X ⟶ Y)
    (hw : φ ≫ q = p) (V : Y.Opens) (W : X.Opens) (h : W ≤ φ ⁻¹ᵁ V) (a : K) :
    (φ.appLE V W h).hom (constFn q V a) = constFn p W a := by
  subst hw
  unfold constFn
  rw [← CommRingCat.comp_apply]
  congr 2
  exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _

theorem resG_constFn {K : Type} [CommRing K] {X : Scheme.{0}} (p : X ⟶ Sp K) {U V : X.Opens} (h : V ≤ U) (a : K) :
    resG X h (constFn p U a) = constFn p V a := by
  unfold constFn resG
  rw [← CommRingCat.comp_apply]
  congr 2
  exact Scheme.Hom.appLE_map _ _ _

theorem keyOn_scale (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ σ' : L.L.Sec)
    (x : KeyIn K) (y : Fin x.P.g → (epsR K ⟶ G)) (a : K) (th : x.P.L.Sec)
    (hth : ∀ s : Sp K, ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ nonzeroLocus th)
    (hth' : ∀ i, th.f i = constFn x.P.A.hom _ a * x.th.f i) (hσ : ∀ i, σ'.f i = constFn G.hom _ a * σ.f i)
    (hK : KeyOn (RingHom.id K) x G L σ y) :
    KeyOn (RingHom.id K) ⟨x.P, x.g_pos, x.rig, x.rig_gen, th, hth, x.v, x.basis⟩ G L σ' y := by
  obtain ⟨φ, he, ψ, F, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hK
  have hw : φ ≫ G.hom = x.P.A.hom := by
    rw [h₁.1.w, show spMap (RingHom.id K) = 𝟙 (Sp K) from Spec.map_id _, Category.comp_id]
  refine ⟨φ, he, ψ, F, h₁, h₂, h₃, fun j i h => ?_, h₅, h₆, h₇⟩
  show (φ.appLE _ _ h).hom (σ'.f (j PUnit.unit)) = _ * resG _ inf_le_right (th.f i)
  rw [hσ, hth', map_mul, map_mul, h₄ j i h, appLE_constFn x.P.A.hom G.hom φ hw, resG_constFn, mul_left_comm]

end GlobalTheory.KeyEven

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerChangeOfTangentFrame
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.KSFrameChange

theorem sum_four_comm {R : Type} [AddCommMonoid R] {ι₁ ι₂ ι₃ ι₄ : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    [Fintype ι₄] (F : ι₁ → ι₂ → ι₃ → ι₄ → R) :
    ∑ a, ∑ b, ∑ x, ∑ y, F a b x y = ∑ y, ∑ x, ∑ b, ∑ a, F a b x y :=
  calc ∑ a, ∑ b, ∑ x, ∑ y, F a b x y = ∑ a, ∑ b, ∑ y, ∑ x, F a b x y :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ y, ∑ b, ∑ x, F a b x y := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ y, ∑ a, ∑ b, ∑ x, F a b x y := Finset.sum_comm
    _ = ∑ y, ∑ a, ∑ x, ∑ b, F a b x y :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ y, ∑ x, ∑ a, ∑ b, F a b x y := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ y, ∑ x, ∑ b, ∑ a, F a b x y :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem sum_four_comm' {R : Type} [AddCommMonoid R] {ι₁ ι₂ ι₃ ι₄ : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    [Fintype ι₄] (F : ι₁ → ι₂ → ι₃ → ι₄ → R) :
    ∑ a, ∑ b, ∑ x, ∑ y, F a b x y = ∑ x, ∑ y, ∑ b, ∑ a, F a b x y :=
  (sum_four_comm F).trans Finset.sum_comm

theorem isKS_frame_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X)
    (V : X.Opens) (U : X.affineOpens) (n n' : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left))
    (v' : Fin n' → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (B : Matrix (Fin n) (Fin n') Γ(X, U.1))
    (D : Γ(X, U.1) → Γ(X, U.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)),
    (∀ a, IsTanAtG t (GlobalTheory.LogKS.chart U) (v a)) → (∀ c, IsTanAtG t (GlobalTheory.LogKS.chart U) (v' c)) →
    (∀ a, IsCombAtG t (GlobalTheory.LogKS.chart U) v' (B a) (v a)) → GlobalTheory.LogKS.IsKS t V U v D Θ →
    GlobalTheory.LogKS.IsKS t V U v' D (_root_.Matrix.transpose B * Θ * B) := by
  intro E _ _ _ H X t V U n n' v v' B D Θ hv hv' hB hKS
  obtain ⟨J, W, j, d, hcov, hWL, hF, hD, hc⟩ := hKS
  refine ⟨J, W, j, d, hcov, hWL, hF, hD, ?_⟩
  intro i i' O hO f S _ φ g₀ w' hg hgO htr'
  choose w hw using fun a => (GlobalTheory.LogKS.existsUnique_isTranslate t φ hg (hv a)).exists
  rw [hc i i' O hO f S φ g₀ w hg hgO hw]
  let g' : overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ t.G :=
    Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ g₀) (Category.assoc _ _ _)
  choose gc yc hgc hyc hwc using htr'
  have hgc' : ∀ c, gc c = g' := fun c => Over.OverMorphism.ext (hgc c)
  have key : ∀ a (O' : t.G.left.Opens) (f' : Γ(t.G.left, O')), ⊤ ≤ g₀ ⁻¹ᵁ O' →
      (valR (w a) O' f').snd = ∑ c, φ (B a c) * (valR (w' c) O' f').snd := by
    intro a O' f' hO'
    obtain ⟨h0, hw'⟩ := _root_.GlobalTheory.LogKSDiv.translate_comb t U v' (B a) (v a) φ g₀ hg g' yc hv' (hB a) rfl hyc
    rw [hw' (w a) (hw a), _root_.GlobalTheory.KSLin.snd_valR_translate_prod (g₀ ≫ t.G.hom) t.G g₀ g' rfl yc (fun c => φ (B a c)) h0 O' f' hO']
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hwc c, hgc' c]
  simp_rw [key _ O f hgO]
  have hO2 : ⊤ ≤ g₀ ⁻¹ᵁ (t.PP.L.U (j i) ⊓ t.PP.L.U (j i')) :=
    hgO.trans (fun x hx => (hO.trans (inf_le_inf (hWL i) (hWL i'))) hx)
  simp_rw [key _ _ _ hO2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [sum_four_comm']
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.KSFrameChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSheafSemiAbelianSemiNegOfIsAlgClosed
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

namespace GlobalTheory.Nef

theorem exists_isGenOver (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (h : IsCurve k C) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra k K) (x : Sp K ⟶ C), IsGenOver k x := by
  have := LieSemineg.isIntegral_curve h.1 h.2.2
  let x : Sp C.functionField ⟶ C := C.fromSpecStalk (genericPoint C)
  let φ : CommRingCat.of k ⟶ CommRingCat.of C.functionField := Spec.preimage (x ≫ strHom k C)
  refine ⟨C.functionField, inferInstance, φ.hom.toAlgebra, x, h, isGen_fromSpecStalk C, ?_⟩
  exact (Spec.map_preimage (x ≫ strHom k C)).symm

theorem semiNeg_lie_of_isAlgClosed : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → SemiNeg k (Lie G) := by
  intro k _ _ _ C _ h G _ hG W r hW i hi
  obtain ⟨K, _, _, x, hx⟩ := exists_isGenOver k C h
  obtain ⟨V₀, s, g, hV, hs, hg, hl⟩ := _root_.GlobalTheory.Nef.exists_frame_locFrames k K C x hx W r hW
  have hL := _root_.GlobalTheory.Nef.linesLE_zero_of_sub_lie k K C x hx G hG W r i hi V₀ s g hV hs hg hl
  have hd := _root_.GlobalTheory.Nef.deg_le_rank_mul_of_linesLE r k K (_root_.GlobalTheory.Nef.CurveFF.isFF_of_isGenOver k K C x hx) g hg 0 hL
  rw [mul_zero] at hd
  exact _root_.GlobalTheory.Nef.interNum_det_nonpos_of_deg_nonpos k K C x hx W r hW V₀ s g hV hs hg hl (by exact_mod_cast hd)

end GlobalTheory.Nef
end

