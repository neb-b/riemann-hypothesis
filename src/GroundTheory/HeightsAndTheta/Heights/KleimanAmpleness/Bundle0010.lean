module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CechH0SectionsHypothesesLine
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u v w

def CechZerothCohomologySections.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubSystem S x E), x ≠ 0 → Nonempty (F.H 0 ≃ₗ[S] F.secs)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GeneratedTwistSysZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def GraphClosed.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (G H : LineBundle k x), G.toSubSystem.Generated → IsVeryAmple H.toSubSystem →
    IsVeryAmple (G.toSubSystem.twist H.toSubSystem)

def PointGenerated.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Q : LineBundle k x), IsSubvar x (primeOf (S := k) x) 0 → Q.toSubSystem.Generated

section Hypotheses

variable (k : Type u) [Field k]

theorem generated_twistSys_zero' {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} : (twistSys S x 0).Generated := by
  have h1 : (1 : Ω) ∈ (twistSys S x 0).secs := by
    rw [SubSystem.secs, Submodule.mem_iInf]
    intro I
    exact one_mem_twistMod_zero I
  intro I
  obtain ⟨i, hi⟩ := I.2.1
  apply le_antisymm
  · refine Submodule.span_le.mpr fun z hz => ?_
    rw [SubSystem.secs, SetLike.mem_coe, Submodule.mem_iInf] at hz
    exact hz I
  · change twistMod S x 0 I ≤ _
    rw [twistMod_eq_span 0 I hi, zpow_zero]
    exact Submodule.span_mono (Set.singleton_subset_iff.mpr h1)

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisAltMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

open MvPolynomial

theorem SerreVanish.equiv (hC : GradedCech.Statement) :
    Kleiman.SerreVanish.Statement.{0, 0} ↔ IndefiniteRowSideFullHecke.Kleiman.SerreVanish.Statement := by
  constructor
  · intro hA S _ _ N M _ _ _ _ G hfin
    obtain ⟨c₀, hc₀⟩ := hA S N M (gradedEquiv S N M G) hfin
    obtain ⟨e, -, -⟩ := hC S N
    refine ⟨c₀, fun i hi c hc => ?_⟩
    have := hc₀ i hi c hc
    exact (e M G i c).injective.subsingleton
  · intro hB S _ _ N M _ _ _ _ 𝓜 hfin
    obtain ⟨G, rfl⟩ := (gradedEquiv S N M).surjective 𝓜
    obtain ⟨c₀, hc₀⟩ := hB S N M G hfin
    obtain ⟨e, -, -⟩ := hC S N
    refine ⟨c₀, fun i hi c hc => ?_⟩
    have := hc₀ i hi c hc
    exact (e M G i c).symm.injective.subsingleton

end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.InterNumPointSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u v w

def InterNumPoint.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (y : Fin (N + 1) → Ω),
    IsSubvar y (primeOf (S := k) y) 0 → ∀ L : Fin 0 → SubSystem k y Ω,
      interNum (primeOf (S := k) y) L = (Module.finrank k (funField (k := k) y) : ℤ)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.InterNumRestrictSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u v w

def InterNumRestrict.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (K' : Type w) [Field K'] [Algebra k K'] (y : Fin (N + 1) → K') (hxy : ∀ i, y i ≠ 0 → x i ≠ 0),
    primeOf (S := k) x ≤ primeOf (S := k) y →
    ∀ (pp : Ideal (Poly k N)) (n : ℕ), IsSubvar y pp n →
    ∀ (L : Fin n → LineBundle k x) (L' : Fin n → LineBundle k y) (r : Fin n → Ω → K'),
      (∀ i, RestrictData (L i).toSubSystem hxy (L' i).toSubSystem (r i)) →
      interNum pp (fun i => (L' i).toSubSystem) = interNum pp (fun i => (L i).toSubSystem)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.NefGenericDVRSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

noncomputable section

def NefGenericDVR.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (F : Type) [Field F] [Algebra O F]
    [IsFractionRing O F] (Ω : Type) [Field Ω] [Algebra O Ω] [Algebra F Ω] [IsScalarTower O F Ω]
    (N : ℕ) (x : Fin (N + 1) → Ω) (M : Kleiman.LineBundle O x),
    Kleiman.NefAbove M.toSubSystem ((IsLocalRing.maximalIdeal O).map (C : O →+* Kleiman.Poly O N)) →
    Kleiman.Nef (M.toSubSystem.extend F)

abbrev exO : Type := PowerSeries ℚ

abbrev exF : Type := FractionRing exO

abbrev exΩ : Type := RatFunc exF

theorem NefGenericDVR.hyps :
    Kleiman.NefAbove (Kleiman.twistBundle exO (Kleiman.lineX exF) 0).toSubSystem
      ((IsLocalRing.maximalIdeal exO).map (C : exO →+* Kleiman.Poly exO 1)) :=
  by
    unfold Kleiman.NefAbove
    intro pp _ _
    rw [show (Kleiman.twistBundle exO (Kleiman.lineX exF) 0).toSubSystem =
      Kleiman.twistSys exO (Kleiman.lineX exF) 0 from rfl, Kleiman.interNum_twistSys_zero]

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PClaimVanishCech
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace Cech

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}

theorem subsingleton_H_one_iff :
    Subsingleton (H G ρ 1) ↔ ∀ z : Cochain G 1, d G ρ 1 z = 0 → ∃ w : Cochain G 0, d G ρ 0 w = z := by
  unfold H
  rw [Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_eq_top]
  constructor
  · intro h z hz
    exact h (LinearMap.mem_ker.mpr hz)
  · intro h z hz
    exact h z (LinearMap.mem_ker.mp hz)

theorem sgn_mul_sgn_erase {J : Finset (Fin n)} {j k : Fin n} (hj : j ∈ J) (hk : k ∈ J) (hjk : j ≠ k) :
    sgn J j * sgn (J.erase j) k = -(sgn J k * sgn (J.erase k) j) := by
  wlog h : j < k generalizing j k
  · have h' : k < j := lt_of_le_of_ne (not_lt.mp h) hjk.symm
    rw [this hk hj hjk.symm h', neg_neg]
  have hmem : j ∈ J.filter (· < k) := Finset.mem_filter.mpr ⟨hj, h⟩
  have e1 : (J.erase j).filter (· < k) = (J.filter (· < k)).erase j := by rw [Finset.filter_erase]
  have e2 : (J.erase k).filter (· < j) = J.filter (· < j) := by
    rw [Finset.filter_erase]
    apply Finset.erase_eq_of_notMem
    simp only [Finset.mem_filter, not_and, not_lt]
    intro _; exact h.le
  have hb : 1 ≤ (J.filter (· < k)).card := Finset.card_pos.mpr ⟨j, hmem⟩
  unfold sgn
  rw [e1, e2, Finset.card_erase_of_mem hmem]
  obtain ⟨b', hb'⟩ : ∃ b', (J.filter (· < k)).card = b' + 1 := ⟨_, (Nat.sub_add_cancel hb).symm⟩
  rw [hb', Nat.add_sub_cancel, pow_succ]
  ring

theorem d_one_d_zero
    (hρ : ∀ (I J K : Cell U) (h : I.1 ⊆ J.1) (h' : J.1 ⊆ K.1) (m : G I),
      ρ J K h' (ρ I J h m) = ρ I K (h.trans h') m)
    (w : Cochain G 0) : d G ρ 1 (d G ρ 0 w) = 0 := by
  funext J
  have key : ∀ (K K' : Idx U 0) (h : K.1.1 ⊆ J.1.1) (h' : K'.1.1 ⊆ J.1.1), K = K' →
      ρ K.1 J.1 h (w K) = ρ K'.1 J.1 h' (w K') := by
    rintro K _ h h' rfl; rfl
  rw [d_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [d_apply, map_sum, map_zsmul, hρ, Finset.smul_sum, smul_smul]
  rw [Pi.zero_apply, Finset.sum_sigma']
  refine Finset.sum_involution
    (fun p _ => ⟨⟨p.2.1, Finset.mem_of_mem_erase p.2.2⟩,
      ⟨p.1.1, Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp p.2.2).1.symm, p.1.2⟩⟩⟩) ?_ ?_
    (fun _ _ => Finset.mem_univ _) (fun p _ => rfl)
  · rintro ⟨⟨j, hj⟩, ⟨k, hk⟩⟩ -
    have hk' := Finset.mem_erase.mp hk
    have hidx : face (face J ⟨j, hj⟩) ⟨k, hk⟩ =
        face (face J ⟨k, hk'.2⟩) ⟨j, Finset.mem_erase.mpr ⟨hk'.1.symm, hj⟩⟩ :=
      Subtype.ext (Subtype.ext (Finset.erase_right_comm))
    dsimp only
    rw [key _ _ _ (((face_subset _ _).trans (face_subset _ _))) hidx, ← add_smul]
    have hs : sgn J.1.1 j * sgn (face J ⟨j, hj⟩).1.1 k =
        -(sgn J.1.1 k * sgn (face J ⟨k, hk'.2⟩).1.1 j) :=
      sgn_mul_sgn_erase hj hk'.2 hk'.1.symm
    rw [hs, neg_add_cancel, zero_smul]
  · rintro ⟨⟨j, hj⟩, ⟨k, hk⟩⟩ - - heq
    exact (Finset.mem_erase.mp hk).1 (congrArg (fun p => p.1.1) heq)

end Cech

namespace SubSystem

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

section General

variable {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem d_one_d_zero (F : SubSystem S x E) (w : Cech.Cochain (fun I => F.sub I) 0) :
    Cech.d (fun I => F.sub I) F.res 1 (Cech.d (fun I => F.sub I) F.res 0 w) = 0 :=
  Cech.d_one_d_zero (fun _ _ _ _ _ _ => rfl) w


set_option maxHeartbeats 1000000 in
theorem subsingleton_H_one_of_quot (F G : SubSystem S x E)
    (hGF : ∀ I, ∀ y ∈ G.sub I, y ∈ F.sub I) (hG : Subsingleton (G.H 1))
    (hQ : Subsingleton (quotH F G 1)) : Subsingleton (F.H 1) := by
  unfold SubSystem.H at hG ⊢
  unfold quotH at hQ
  rw [Cech.subsingleton_H_one_iff] at hG hQ ⊢
  intro z hz
  let q : ∀ I, F.sub I →ₗ[S] (F.sub I ⧸ quotSub F G I) := fun I => (quotSub F G I).mkQ
  have hq : ∀ I J h m, q J (F.res I J h m) = quotRes F G I J h (q I m) := fun _ _ _ _ => rfl
  have hqd := Cech.mapC_d (R := S) (G := fun I => ↥(F.sub I))
    (G' := fun I => ↥(F.sub I) ⧸ quotSub F G I) q hq
  obtain ⟨wb, hwb⟩ := hQ (Cech.mapC (R := S) (G := fun I => ↥(F.sub I)) (G' := fun I => ↥(F.sub I) ⧸ quotSub F G I) q 1 z) (by rw [← hqd, hz, map_zero])
  choose w hw using fun I : Cech.Idx (support x) 0 => Submodule.Quotient.mk_surjective _ (wb I)
  have hmw : (Cech.mapC (R := S) (G := fun I => ↥(F.sub I)) (G' := fun I => ↥(F.sub I) ⧸ quotSub F G I) q 0 w) = wb := funext hw
  have hr : (Cech.mapC (R := S) (G := fun I => ↥(F.sub I)) (G' := fun I => ↥(F.sub I) ⧸ quotSub F G I) q 1 (z - Cech.d (fun I => F.sub I) F.res 0 w)) = 0 := by
    rw [map_sub, hqd 0, hmw, hwb]
    exact @sub_eq_zero_of_eq (Cech.Cochain (fun I => ↥(F.sub I) ⧸ quotSub F G I) 1) _ _ _ rfl
  have hrG : ∀ J, (((z - Cech.d (fun I => F.sub I) F.res 0 w) J : F.sub J.1) : E) ∈ G.sub J.1 :=
    fun J => (Submodule.Quotient.mk_eq_zero (quotSub F G J.1)).mp (congrFun hr J)
  let ι : ∀ I, G.sub I →ₗ[S] F.sub I := fun I =>
    { toFun := fun y => ⟨y, hGF I y y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hι : ∀ I J h m, ι J (G.res I J h m) = F.res I J h (ι I m) := fun _ _ _ _ => rfl
  have hιd := Cech.mapC_d (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F.sub I)) ι hι
  have hιinj : ∀ i, Function.Injective (Cech.mapC (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F.sub I)) ι i) := fun i a b hab =>
    funext fun I => Subtype.ext (congrArg (fun c => ((c I : F.sub I.1) : E)) hab)
  obtain ⟨g, hg⟩ : ∃ g : Cech.Cochain (fun I => ↥(G.sub I)) 1,
      (Cech.mapC (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F.sub I)) ι 1 g) =
        z - Cech.d (fun I => F.sub I) F.res 0 w := ⟨fun J => ⟨_, hrG J⟩, rfl⟩
  have hdg : Cech.d (fun I => ↥(G.sub I)) G.res 1 g = 0 := by
    have h2 : (Cech.mapC (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F.sub I)) ι (1 + 1)
        (Cech.d (fun I => ↥(G.sub I)) G.res 1 g)) = 0 := by
      rw [hιd 1 g, hg, map_sub, hz, d_one_d_zero, sub_zero]
    exact hιinj (1 + 1) (h2.trans (LinearMap.map_zero _).symm)
  obtain ⟨v, hv⟩ := hG g hdg
  refine ⟨w + (Cech.mapC (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F.sub I)) ι 0 v), ?_⟩
  rw [map_add (f := _), ← hιd, hv, hg, add_sub_cancel]

end General

theorem subsingleton_H_one_of_smul (F' G : SubSystem S x Ω) (σ : Ω) (hσ : σ ≠ 0)
    (hG : ∀ I z, z ∈ G.sub I ↔ ∃ y ∈ F'.sub I, z = σ * y) (hF : Subsingleton (F'.H 1)) :
    Subsingleton (G.H 1) := by
  unfold SubSystem.H at hF ⊢
  rw [Cech.subsingleton_H_one_iff] at hF ⊢
  have hdiv : ∀ I (z : G.sub I), σ⁻¹ * (z : Ω) ∈ F'.sub I := fun I z => by
    obtain ⟨y, hy, hzy⟩ := (hG I z).mp z.2
    rw [hzy, ← mul_assoc, inv_mul_cancel₀ hσ, one_mul]
    exact hy
  let φ : ∀ I, G.sub I →ₗ[S] F'.sub I := fun I =>
    { toFun := fun z => ⟨σ⁻¹ * z, hdiv I z⟩
      map_add' := fun a b => Subtype.ext (mul_add _ _ _)
      map_smul' := fun s a => Subtype.ext (by
        show σ⁻¹ * (s • (a : Ω)) = s • (σ⁻¹ * (a : Ω))
        rw [Algebra.smul_def, Algebra.smul_def]; ring) }
  let ψ : ∀ I, F'.sub I →ₗ[S] G.sub I := fun I =>
    { toFun := fun y => ⟨σ * y, (hG I _).mpr ⟨y, y.2, rfl⟩⟩
      map_add' := fun a b => Subtype.ext (mul_add _ _ _)
      map_smul' := fun s a => Subtype.ext (by
        show σ * (s • (a : Ω)) = s • (σ * (a : Ω))
        rw [Algebra.smul_def, Algebra.smul_def]; ring) }
  have hφ : ∀ I J h m, φ J (G.res I J h m) = F'.res I J h (φ I m) := fun _ _ _ _ => rfl
  have hψ : ∀ I J h m, ψ J (F'.res I J h m) = G.res I J h (ψ I m) := fun _ _ _ _ => rfl
  have hφd := Cech.mapC_d (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F'.sub I)) φ hφ
  have hψd := Cech.mapC_d (R := S) (G := fun I => ↥(F'.sub I)) (G' := fun I => ↥(G.sub I)) ψ hψ
  intro z hz
  obtain ⟨w, hw⟩ := hF (Cech.mapC (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F'.sub I)) φ 1 z) (by rw [← hφd, hz, map_zero])
  refine ⟨(Cech.mapC (R := S) (G := fun I => ↥(F'.sub I)) (G' := fun I => ↥(G.sub I)) ψ 0 w), ?_⟩
  rw [← hψd, hw]
  funext J
  apply Subtype.ext
  show σ * (σ⁻¹ * ((z J : G.sub J.1) : Ω)) = ((z J : G.sub J.1) : Ω)
  rw [← mul_assoc, mul_inv_cancel₀ hσ, one_mul]

end SubSystem

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutMultPos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

open IsLocalRing

def locQuotEquiv {R : Type*} [CommRing R] (q : Ideal R) [q.IsPrime] (J : Ideal R) :
    (Localization.AtPrime q ⧸ J.localized' (Localization.AtPrime q) q.primeCompl
      (Algebra.linearMap R (Localization.AtPrime q))) ≃ₗ[Localization.AtPrime q]
      LocalizedModule q.primeCompl (R ⧸ J) :=
  have := IsLocalization.linearMap_compatibleSMul q.primeCompl
  (IsLocalizedModule.linearEquiv q.primeCompl
    (J.toLocalizedQuotient' (Localization.AtPrime q) q.primeCompl
      (Algebra.linearMap R (Localization.AtPrime q)))
    (LocalizedModule.mkLinearMap _ _)).restrictScalars _

theorem CutMultPos.proof : CutMultPos.Statement := by
  intro S _ _ N J qq h
  have : qq.IsPrime := h.1.1
  let J' : Ideal (Localization.AtPrime qq) :=
    J.localized' (Localization.AtPrime qq) qq.primeCompl
      (Algebra.linearMap (Poly S N) (Localization.AtPrime qq))
  have hJ' : J' = J.map (algebraMap (Poly S N) (Localization.AtPrime qq)) := by
    simp only [J', Submodule.localized'_eq_span, Ideal.map]
    rfl
  have hmin : maximalIdeal (Localization.AtPrime qq) ∈ J'.minimalPrimes := by
    rw [hJ', IsLocalization.minimalPrimes_map qq.primeCompl, Set.mem_preimage,
      Localization.AtPrime.under_maximalIdeal]
    exact h
  have hne : J' ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hmin.1.2
  have : Nontrivial (Localization.AtPrime qq ⧸ J') := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsArtinianRing (Localization.AtPrime qq ⧸ J') :=
    quotient_artinian_of_mem_minimalPrimes_of_isLocalRing J' hmin
  have : IsArtinian (Localization.AtPrime qq) (Localization.AtPrime qq ⧸ J') :=
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := J'))
  have : IsNoetherianRing (Localization.AtPrime qq) :=
    IsLocalization.isNoetherianRing qq.primeCompl _ inferInstance
  unfold cutMult
  rw [← (locQuotEquiv qq J).length_eq]
  exact ⟨Module.length_pos, Module.length_ne_top.lt_top⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefPlusAmple
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Lemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem SubSystem.twist_sub_eq_mul (F Q : SubSystem k x Ω) (I : Chart x) :
    (F.twist Q).sub I = F.sub I * Q.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  change Submodule.span _ _ = _
  congr 1
  ext z
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩
    exact ⟨y, hy, q, hq, by rw [smul_eq_mul, mul_comm]⟩
  · rintro ⟨y, hy, q, hq, rfl⟩
    exact ⟨q, hq, y, hy, by rw [smul_eq_mul, mul_comm]⟩

theorem twistMod_zero_eq_one (I : Chart x) : twistMod k x 0 I = 1 := by
  obtain ⟨i, hi⟩ := I.2.1
  rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]

theorem SubSystem.pow_sub_eq_pow (Q : SubSystem k x Ω) (n : ℕ) (I : Chart x) :
    (Q.pow n).sub I = Q.sub I ^ n := by
  induction n with
  | zero => rw [pow_zero]; exact twistMod_zero_eq_one I
  | succ n ih => rw [pow_succ, ← ih]; exact SubSystem.twist_sub_eq_mul _ _ I

end Lemmas

end

end GroundTheory.Heights₂.Heights.Kleiman
end

