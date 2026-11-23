module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0010
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IntegOfMem

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PMemDeck
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

theorem UpperTheory.Gal.W2.Seed.pMemDeck :
    MemSum → TfCen → MemDeck := by
  intro hSum hCen X M _ _ T K hT k hk hnorm
  have hconj : ∀ a ∈ T.K₀, ∀ u ∈ T.K₀, a * u * a⁻¹ ∈ T.K₀ := fun a ha u hu =>
    T.K₀.mul_mem (T.K₀.mul_mem ha hu) (T.K₀.inv_mem ha)
  have hmem := hSum X T.K₀ T.K₀ T.K₀ k le_rfl (by simp) hconj (fun a ha u hu => by
    have h1 := hnorm (a * u * a⁻¹) (hconj a ha u hu)
    simpa [mul_assoc, _root_.mul_inv_rev] using h1)
  refine ⟨hmem.1, map_one _, ?_⟩
  intro V _ _ Φ hΦ
  funext g
  have hc : T.Cen 1 := ⟨fun g => by simp, map_one _⟩
  rw [one_smul, hCen X M T 1 hc V Φ hΦ g, mul_one]
  have hinv0 : ∀ k' ∈ T.K₀, ∀ g, Φ (g * k') = Φ g := fun k' hk' g => by
    rw [hΦ k' (T.le hk') g, T.ker k' hk' _]
    simp
  rw [hmem.2.2 V Φ hinv0 g]
  have hall : ∀ a b : ↥T.K₀ ⧸ T.K₀.subgroupOf T.K₀, a = b := by
    intro a b
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact SetLike.coe_mem _
  letI : Unique (↥T.K₀ ⧸ T.K₀.subgroupOf T.K₀) :=
    ⟨⟨QuotientGroup.mk (1 : ↥T.K₀)⟩, fun a => hall a _⟩
  rw [finsum_unique]
  have hx : (↑(Quotient.out (default : ↥T.K₀ ⧸ T.K₀.subgroupOf T.K₀)) : X) ∈ T.K₀ :=
    SetLike.coe_mem _
  rw [_root_.mul_inv_rev, ← mul_assoc, hΦ k⁻¹ (hT.1 (K.inv_mem hk)) _,
    hT.2 k⁻¹ (K.inv_mem hk) _]
  simp only [Units.val_one, one_smul]
  exact hinv0 _ (T.K₀.inv_mem hx) g
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PMemSum
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

private lemma memSum_cls {X : Type} [Group X] {K KM K₀ : Subgroup X} {h : X}
    (hc : ∀ k ∈ K, ∀ u ∈ KM, h * k * u * (h * k)⁻¹ ∈ K₀) (k₁ k₂ : K)
    (e : (QuotientGroup.mk k₁ : K ⧸ KM.subgroupOf K) = QuotientGroup.mk k₂) (y : X) :
    h * (k₁ : X) * y ∈ K₀ ↔ h * (k₂ : X) * y ∈ K₀ := by
  have hu : k₁⁻¹ * k₂ ∈ KM.subgroupOf K := QuotientGroup.eq.1 e
  have hu' : (k₁ : X)⁻¹ * k₂ ∈ KM := by simpa [Subgroup.mem_subgroupOf] using hu
  have hm := hc k₁ k₁.2 _ hu'
  have e2 : h * (k₂ : X) * y = (h * k₁ * ((k₁ : X)⁻¹ * k₂) * (h * k₁)⁻¹) * (h * k₁ * y) := by group
  rw [e2]
  exact (K₀.mul_mem_cancel_left hm).symm

private lemma memSum_eq {X : Type} [Group X] (K KM K₀ : Subgroup X) (h y : X)
    [Fintype (K ⧸ KM.subgroupOf K)] :
    memFn K KM K₀ h y =
      ∑ q : K ⧸ KM.subgroupOf K, if h * (q.out : X) * y ∈ K₀ then (1 : ℂ) else 0 := by
  unfold memFn
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [Finset.sum_boole]

theorem UpperTheory.Gal.W2.Seed.pMemSum :
    MemSum := by
  intro X _ K KM K₀ h hK0 hidx hnorm hc
  haveI : (KM.subgroupOf K).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm g g.2 n hn⟩
  haveI : (KM.subgroupOf K).FiniteIndex := ⟨hidx⟩
  letI : Fintype (K ⧸ KM.subgroupOf K) := Fintype.ofFinite _
  have hex : ∀ y, memFn K KM K₀ h y ≠ 0 →
      ∃ q : K ⧸ KM.subgroupOf K, h * (q.out : X) * y ∈ K₀ := by
    intro y hy
    by_contra hne
    apply hy
    have : IsEmpty {q : K ⧸ KM.subgroupOf K // h * (q.out : X) * y ∈ K₀} :=
      ⟨fun ⟨q, hq⟩ => hne ⟨q, hq⟩⟩
    unfold memFn
    rw [Nat.card_of_isEmpty, Nat.cast_zero]
  have hP : ∀ (a : K) (q : K ⧸ KM.subgroupOf K) (y : X),
      h * (q.out : X) * ((a : X) * y) ∈ K₀ ↔
        h * ((q * (QuotientGroup.mk a : K ⧸ KM.subgroupOf K)).out : X) * y ∈ K₀ := by
    intro a q y
    have e : (QuotientGroup.mk (q.out * a) : K ⧸ KM.subgroupOf K) =
        QuotientGroup.mk (q * (QuotientGroup.mk a : K ⧸ KM.subgroupOf K)).out := by
      rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
    have hcls := memSum_cls hc (q.out * a) (q * (QuotientGroup.mk a : K ⧸ KM.subgroupOf K)).out e y
    have e2 : h * (q.out : X) * ((a : X) * y) = h * ((q.out * a : K) : X) * y := by
      simp only [Subgroup.coe_mul, mul_assoc]
    rw [e2]
    exact hcls
  refine ⟨?_, ?_, ?_⟩
  · show IsBiInv K₀ (memFn K KM K₀ h) ∧ FinDosetSupp K₀ (memFn K KM K₀ h)
    refine ⟨?_, ?_⟩
    · intro a b g
      unfold memFn
      congr 1
      apply Nat.card_congr
      refine (Equiv.mulRight (QuotientGroup.mk (⟨a, hK0 a.2⟩ : K) : K ⧸ KM.subgroupOf K)).subtypeEquiv ?_
      intro q
      have e1 : h * (q.out : X) * ((a : X) * g * (b : X)) =
          h * (q.out : X) * (((⟨a, hK0 a.2⟩ : K) : X) * g) * (b : X) := by
        rw [← mul_assoc (h * (q.out : X))] <;> rfl
      rw [e1, Subgroup.mul_mem_cancel_right _ b.2]
      exact hP ⟨a, hK0 a.2⟩ q g
    · refine ⟨Finset.univ.image (fun q : K ⧸ KM.subgroupOf K => (h * (q.out : X))⁻¹), fun y hy => ?_⟩
      obtain ⟨q, hq⟩ := hex y hy
      refine ⟨(h * (q.out : X))⁻¹, Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩, 1, ⟨_, hq⟩, ?_⟩
      simp only [OneMemClass.coe_one, one_mul]
      group
  · intro y hy
    obtain ⟨q, hq⟩ := hex y hy
    exact ⟨_, (q.out).2, hq⟩
  · intro V _ _ Φ hΦ g
    unfold hAct
    have hpt : ∀ x : X ⧸ K₀, memFn K KM K₀ h x.out • Φ (g * x.out) =
        ∑ q : K ⧸ KM.subgroupOf K,
          (if (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K₀) = x then Φ (g * (h * (q.out : X))⁻¹) else 0) := by
      intro x
      rw [memSum_eq, Finset.sum_smul]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hiff : (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K₀) = x ↔ h * (q.out : X) * x.out ∈ K₀ := by
        conv_lhs => rw [← QuotientGroup.out_eq' x]
        rw [QuotientGroup.eq, inv_inv]
      by_cases hm : h * (q.out : X) * x.out ∈ K₀
      · rw [if_pos hm, if_pos (hiff.mpr hm), one_smul]
        have hg : g * x.out = g * (h * (q.out : X))⁻¹ * (h * (q.out : X) * x.out) := by group
        rw [hg]
        exact hΦ _ hm _
      · rw [if_neg hm, if_neg (fun e => hm (hiff.mp e)), zero_smul]
    rw [finsum_eq_sum_of_fintype (fun k : K ⧸ KM.subgroupOf K => Φ (g * (h * (k.out : X))⁻¹)),
      finsum_congr hpt, finsum_sum_comm]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [finsum_eq_single _ (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K₀)]
      · simp
      · intro x hx
        rw [if_neg (Ne.symm hx)]
    · intro q _
      apply Set.Finite.subset (Set.finite_singleton (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K₀))
      intro x hx
      by_contra hne
      exact hx (if_neg (Ne.symm hne))
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPPart
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

theorem UpperTheory.Gal.W2.Seed.pPPart :
    JEq → PPart := by
  intro hJ E _ _ _ A n p _ S T g
  have hext := (hJ E A n p S T.toAdT T.μ T.mu T.a T.j T.j_mx).1
  have hoff : ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w (T.sec (T.j g)) = comp w g :=
    fun w hw => (T.j_eq (T.sec (T.j g)) g).1 (T.j_sec _) w hw
  have hk1 : ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w ((T.sec (T.j g))⁻¹ * g) = 1 := by
    intro w hw
    rw [map_mul, map_inv, hoff w hw, inv_mul_cancel]
  have hk2 : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w ((T.sec (T.j g))⁻¹ * g) = comp w g := by
    intro w hw
    rw [map_mul, map_inv, T.sec_p _ w hw, inv_one, one_mul]
  refine ⟨(T.sec (T.j g))⁻¹ * g, by group, hk1, hk2, fun h => hext _ _ fun w => ?_⟩
  rw [map_mul (comp w) (T.sec h), map_mul (comp w) _ (T.sec h)]
  by_cases hw : (p : 𝓞 E) ∈ w.asIdeal
  · rw [T.sec_p h w hw, one_mul, mul_one]
  · rw [hk1 w hw, one_mul, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSphComm
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

theorem UpperTheory.Gal.W2.Seed.pSphComm :
    SphComm := by
  intro E _ _ n w t t'
  have hb : ∀ s : GL (Fin n) (w.adicCompletion E), IsBiInv (GlobalTheory.LFun.KGL w (n := n)) (dosetInd ℂ (GlobalTheory.LFun.KGL w (n := n)) s) := fun s => (Formalism.UG.Final.DosetIndMem _ _ ℂ s).1
  exact Formalism.UG.P.heckecomm_gelfand (GlobalTheory.LFun.KGL w (n := n)) Formalism.UG.P.heckecomm_tr Formalism.UG.P.heckecomm_tr_mul
    Formalism.UG.P.heckecomm_tr_tr (fun x hx => Formalism.UG.P.heckecomm_tr_mem _ x hx)
    (Formalism.UG.P.heckecomm_tr_dc Formalism.UG.P.cartan_decomposition_holds E w n) _ _ (hb t) (hb t')
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSumDoset
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

private theorem card_fibre {G : Type} [Group G] (N P : Subgroup G) [N.Normal] (hNP : N ≤ P) (w : G) :
    Nat.card {q : G ⧸ N // (q.out : G) * w⁻¹ ∈ P} = N.relIndex P := by
  have hk := Subgroup.relIndex_ker P (QuotientGroup.mk' N)
  rw [QuotientGroup.ker_mk'] at hk
  rw [hk]
  apply Nat.card_congr
  refine (Equiv.mulRight (QuotientGroup.mk w⁻¹ : G ⧸ N)).subtypeEquiv ?_
  intro q
  rw [Equiv.coe_mulRight, Subgroup.mem_map]
  beta_reduce
  have hq : q * (QuotientGroup.mk w⁻¹ : G ⧸ N) = QuotientGroup.mk ((q.out : G) * w⁻¹) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
  rw [hq]
  constructor
  · intro hp
    exact ⟨_, hp, rfl⟩
  · rintro ⟨p, hp, e⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at e
    have hm := P.mul_mem hp (hNP e)
    simpa using hm

theorem UpperTheory.Gal.W2.Seed.pSumDoset :
    SumDoset := by
  intro X _ K KM h hKM hidx hhK V _ _ Φ hΦ hnorm g
  obtain ⟨L, hL⟩ : ∃ L : Subgroup X, L = K ⊓ Subgroup.comap (MulEquiv.toMonoidHom (MulAut.conj h)) K :=
    ⟨_, rfl⟩
  rw [← hL]
  haveI : (KM.subgroupOf K).Normal := ⟨fun n hn k => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm k k.2 n hn⟩
  haveI : (KM.subgroupOf K).FiniteIndex := ⟨hidx⟩
  letI : Fintype (K ⧸ KM.subgroupOf K) := Fintype.ofFinite _
  have hLK : L ≤ K := by
    rw [hL]
    exact inf_le_left
  have hKML : KM ≤ L := by
    intro u hu
    rw [hL, Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact ⟨hKM hu, hhK u hu⟩
  have hmemL : ∀ k : K, k ∈ L.subgroupOf K ↔ h * (k : X) * h⁻¹ ∈ K := by
    intro k
    rw [Subgroup.mem_subgroupOf, hL, Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    exact ⟨fun hh => hh.2, fun hh => ⟨k.2, hh⟩⟩
  have hNP : KM.subgroupOf K ≤ L.subgroupOf K := by
    intro k hk
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact hKML hk
  have hcard : ∀ y : X, y ∈ DoubleCoset.doubleCoset h⁻¹ (K : Set X) K →
      Nat.card {q : K ⧸ KM.subgroupOf K // h * (q.out : X) * y ∈ K} = KM.relIndex L := by
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hy
    rw [← Subgroup.relIndex_subgroupOf hLK,
      ← card_fibre (KM.subgroupOf K) (L.subgroupOf K) hNP (⟨a, ha⟩ : K)⁻¹]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro q
    rw [inv_inv, hmemL]
    have e : h * (q.out : X) * (a * h⁻¹ * b) = h * ((q.out * ⟨a, ha⟩ : K) : X) * h⁻¹ * b := by
      simp only [Subgroup.coe_mul, mul_assoc]
    rw [e, Subgroup.mul_mem_cancel_right _ hb]
  have hnot : ∀ y : X, y ∉ DoubleCoset.doubleCoset h⁻¹ (K : Set X) K →
      ∀ q : K ⧸ KM.subgroupOf K, h * (q.out : X) * y ∉ K := by
    intro y hy q hq
    apply hy
    rw [DoubleCoset.mem_doubleCoset]
    exact ⟨((q.out : K) : X)⁻¹, K.inv_mem q.out.2, h * (q.out : X) * y, hq, by group⟩
  have hpt : ∀ x : X ⧸ K, ((KM.relIndex L : ℕ) : ℂ) •
      ((DoubleCoset.doubleCoset h⁻¹ (K : Set X) K).indicator (1 : X → ℂ) x.out • Φ (g * x.out)) =
      ∑ q : K ⧸ KM.subgroupOf K,
        (if (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K) = x then Φ (g * (h * (q.out : X))⁻¹) else 0) := by
    intro x
    have hterm : ∀ q : K ⧸ KM.subgroupOf K,
        (if (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K) = x then Φ (g * (h * (q.out : X))⁻¹) else 0) =
          if h * (q.out : X) * x.out ∈ K then Φ (g * x.out) else 0 := by
      intro q
      have hiff : (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K) = x ↔ h * (q.out : X) * x.out ∈ K := by
        conv_lhs => rw [← QuotientGroup.out_eq' x]
        rw [QuotientGroup.eq, inv_inv]
      by_cases hm : h * (q.out : X) * x.out ∈ K
      · rw [if_pos hm, if_pos (hiff.mpr hm)]
        have hg : g * x.out = g * (h * (q.out : X))⁻¹ * (h * (q.out : X) * x.out) := by group
        rw [hg, hΦ _ hm]
      · rw [if_neg hm, if_neg (fun e => hm (hiff.mp e))]
    rw [Finset.sum_congr rfl (fun q _ => hterm q), ← Finset.sum_filter, Finset.sum_const,
      ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    by_cases hy : x.out ∈ DoubleCoset.doubleCoset h⁻¹ (K : Set X) K
    · rw [Set.indicator_of_mem hy, Pi.one_apply, one_smul, hcard _ hy, Nat.cast_smul_eq_nsmul ℂ]
    · have : IsEmpty {q : K ⧸ KM.subgroupOf K // h * (q.out : X) * x.out ∈ K} :=
        ⟨fun ⟨q, hq⟩ => hnot _ hy q hq⟩
      rw [Set.indicator_of_notMem hy, zero_smul, smul_zero, Nat.card_of_isEmpty, zero_smul]
  unfold hAct dosetInd
  rw [smul_finsum, finsum_eq_sum_of_fintype (fun k : K ⧸ KM.subgroupOf K => Φ (g * (h * (k.out : X))⁻¹)),
    finsum_congr hpt, finsum_sum_comm]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [finsum_eq_single _ (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K)]
    · simp
    · intro x hx
      rw [if_neg (Ne.symm hx)]
  · intro q _
    apply Set.Finite.subset (Set.finite_singleton (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K))
    intro x hx
    by_contra hne
    exact hx (if_neg (Ne.symm hne))
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.VecCoord
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.W2.Seed

def EvEx : Prop := ∀ (p : ℕ) (E : Type) [Field E] [NumberField E] [IsCMField E] (T : AdT p E) (w : Plc E), (p : 𝓞 E) ∉ w.asIdeal →
  ∃ ev : AfP p ⊗[ℚ] E →+* w.adicCompletion E, ∀ x, ev (T.Φ x) = pLoc E w x

def VecCoord : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S), ∃ vec : ∀ w : Plc E, AfP p ⊗[ℚ] VQ S.D →+ (Fin n → w.adicCompletion E),
  (∀ v, (∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → vec w v = 0) → v = 0) ∧
  (∀ v, v ∈ LaHat S.D ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → ∀ i, vec w v i ∈ w.adicCompletionIntegers E) ∧
  (∀ y : ∀ w : Plc E, Fin n → w.adicCompletion E, (∀ w i, y w i ∈ w.adicCompletionIntegers E) →
    ∃ v, ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → vec w v = y w) ∧
  (∀ (w : Plc E), (p : 𝓞 E) ∉ w.asIdeal → ∀ (y : Fin n → 𝓞 E) i, vec w (inAf S.D y) i = algebraMap (𝓞 E) _ (y i)) ∧
  (∀ (w : Plc E), (p : 𝓞 E) ∉ w.asIdeal → ∀ g v, vec w (S.L.actG (T.j g) v) =
    (GeneralLinearGroup.map (pLoc E w) T.a * comp w g * (GeneralLinearGroup.map (pLoc E w) T.a)⁻¹).val *ᵥ vec w v) ∧
  ∀ (w : Plc E), (p : 𝓞 E) ∉ w.asIdeal → ∀ (c : 𝓞 E) v,
    vec w (UpperTheory.Gal.Int.Geo.mulF S.D c v) = algebraMap (𝓞 E) (w.adicCompletion E) c • vec w v

def StdForm2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S), ∃ (B : DForm S.G) (x : (AfP p ⊗[ℚ] S.G.C)ˣ) (hx : Triv S.G (AfP p) B.β x 1),
    (∀ y : GL (Fin n) E × ℚˣ, y ∈ GlobalTheory.LKCx.grp S.G B.β ↔ y ∈ Gam0 E n) ∧
    ∀ (y : GL (Fin n) E × ℚˣ) (h : y ∈ GlobalTheory.LKCx.grp S.G B.β) (h' : y ∈ Gam0 E n), (B.embAt x 1 hx ⟨y, h⟩).1 = T.j (rat ⟨y, h'⟩)

def PIntRev : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (y : Gam0 E n), (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w (rat y) ∈ KGL w (n := n)) →
    inclG S.G 1 (locC S.G (y : GL (Fin n) E × ℚˣ)) ∈ LocalSmoothExtension.Kp S.G

def IntCof : Prop := ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (a : GL (Fin n) (Af E)),
  ∀ᶠ w in Filter.cofinite, GeneralLinearGroup.map (pLoc E w) a ∈ KGL w (n := n)

end UpperTheory.Gal.W2.Seed
end
end

