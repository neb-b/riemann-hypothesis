module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistBundleToSubSystem
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0014

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutComponentSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def CutComponent.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : LineBundle k x) (s : Ω), IsSubvar (x := x) pp (n + 1) →
    IsVeryAmple L.toSubSystem → s ∈ L.secs → (∃ I, s ∉ (L.twist (idealSys (x := x) pp)).sub I) →
    ∃ qq ∈ (pp ⊔ zeroIdeal L.toSubSystem s).minimalPrimes, IsSubvar (x := x) qq n

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsMemSupport
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

namespace CechZerothCohomologySections

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]

def pt {i : Fin (N + 1)} (hi : i ∈ support x) : Cech.Idx (support x) 0 :=
  ⟨⟨{i}, Finset.singleton_nonempty i, Finset.singleton_subset_iff.mpr hi⟩, Finset.card_singleton i⟩

theorem idx_ext {U : Finset (Fin (N + 1))} {i : ℕ} {K K' : Cech.Idx U i} (h : K.1.1 = K'.1.1) :
    K = K' :=
  Subtype.ext (Subtype.ext h)

theorem mem_sub_of_mem_secs (F : SubSystem S x E) {z : E} (hz : z ∈ F.secs) (I : Chart x) :
    z ∈ F.sub I :=
  (Submodule.mem_iInf _).mp hz I

theorem cocycle_coe_eq (F : SubSystem S x E) {s : Cech.Cochain (fun I => F.sub I) 0}
    (hs : Cech.d (fun I => F.sub I) F.res 0 s = 0) (K K' : Cech.Idx (support x) 0) :
    (s K : E) = (s K' : E) := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp K.2
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp K'.2
  by_cases hab : a = b
  · subst hab; rw [idx_ext (ha.trans hb.symm)]
  have hsub : ({a, b} : Finset (Fin (N + 1))) ⊆ support x := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact K.1.2.2 (by rw [ha]; exact Finset.mem_singleton_self _)
    · rw [Finset.mem_singleton.mp hz]
      exact K'.1.2.2 (by rw [hb]; exact Finset.mem_singleton_self _)
  let J : Cech.Idx (support x) 1 :=
    ⟨⟨{a, b}, Finset.insert_nonempty _ _, hsub⟩, Finset.card_pair hab⟩
  have ha' : a ∈ J.1.1 := Finset.mem_insert_self _ _
  have hb' : b ∈ J.1.1 := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have fa : Cech.face J ⟨a, ha'⟩ = K' := idx_ext (by
    change ({a, b} : Finset _).erase a = _
    rw [hb]; ext z
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact absurd h2 h1
      · exact h2
    · rintro rfl; exact ⟨Ne.symm hab, Or.inr rfl⟩)
  have fb : Cech.face J ⟨b, hb'⟩ = K := idx_ext (by
    change ({a, b} : Finset _).erase b = _
    rw [ha]; ext z
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact h2
      · exact absurd h2 h1
    · rintro rfl; exact ⟨hab, Or.inl rfl⟩)
  have hval : ∀ L L' : Cech.Idx (support x) 0, L = L' → (s L : E) = (s L' : E) := by
    rintro L L' rfl; rfl
  have h0 := congrArg (F.sub J.1).subtype (congrFun hs J)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Cech.d_apply, map_sum, Pi.zero_apply, map_zero] at h0
  have huniv : (Finset.univ : Finset J.1.1) = {⟨a, ha'⟩, ⟨b, hb'⟩} := by
    ext ⟨z, hz⟩
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, true_iff]
    exact (Finset.mem_insert.mp hz).imp id Finset.mem_singleton.mp
  have hne : (⟨a, ha'⟩ : J.1.1) ≠ ⟨b, hb'⟩ := fun h => hab (congrArg Subtype.val h)
  rw [huniv, Finset.sum_pair hne, map_zsmul, map_zsmul] at h0
  have h1 : Cech.sgn ({a, b} : Finset (Fin (N + 1))) a • (s K' : E) +
      Cech.sgn ({a, b} : Finset (Fin (N + 1))) b • (s K : E) = 0 := by
    rw [← hval _ _ fa, ← hval _ _ fb]; exact h0
  have hsum := Cech.sum_sgn_of_card_two (Finset.card_pair hab)
  rw [Finset.sum_pair hab] at hsum
  have hb2 : Cech.sgn ({a, b} : Finset (Fin (N + 1))) b =
      - Cech.sgn ({a, b} : Finset (Fin (N + 1))) a := by linarith
  rw [hb2, neg_smul, ← sub_eq_add_neg, ← smul_sub] at h1
  have hsq : Cech.sgn ({a, b} : Finset (Fin (N + 1))) a *
      Cech.sgn ({a, b} : Finset (Fin (N + 1))) a = 1 := by
    unfold Cech.sgn; rw [← mul_pow]; norm_num
  have h2 : (s K' : E) - (s K : E) = 0 := by
    rw [← one_smul ℤ ((s K' : E) - (s K : E)), ← hsq, mul_smul, h1, smul_zero]
  exact (sub_eq_zero.mp h2).symm

def constC (F : SubSystem S x E) : F.secs →ₗ[S] Cech.Cochain (fun I => F.sub I) 0 where
  toFun z K := ⟨z, mem_sub_of_mem_secs F z.2 K.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem constC_cocycle (F : SubSystem S x E) (z : F.secs) :
    Cech.d (fun I => F.sub I) F.res 0 (constC F z) = 0 :=
  Cech.d_zero_of_compat (v := fun I => (⟨z, mem_sub_of_mem_secs F z.2 I⟩ : F.sub I))
    (fun _ _ _ => rfl)

def toKer (F : SubSystem S x E) :
    F.secs →ₗ[S] LinearMap.ker (Cech.d (fun I => F.sub I) F.res 0) :=
  (constC F).codRestrict _ fun z => LinearMap.mem_ker.mpr (constC_cocycle F z)

theorem exists_mem_support (hx : x ≠ 0) : ∃ i, i ∈ support x := by
  by_contra h
  simp only [not_exists] at h
  exact hx (funext fun i => by_contra fun hi => h i ((mem_support x).mpr hi))

theorem toKer_bijective (F : SubSystem S x E) (hx : x ≠ 0) : Function.Bijective (toKer F) := by
  obtain ⟨i₀, hi₀⟩ := exists_mem_support hx
  refine ⟨fun z₁ z₂ h => ?_, fun s => ?_⟩
  · have := congrArg (fun t => ((t.1 (pt hi₀) : F.sub (pt hi₀).1) : E)) h
    exact Subtype.ext this
  · have hs := LinearMap.mem_ker.mp s.2
    have hz : (s.1 (pt hi₀) : E) ∈ F.secs := by
      refine Submodule.mem_iInf _ |>.mpr fun I => ?_
      obtain ⟨i, hi⟩ := I.2.1
      have hsup : i ∈ support x := I.2.2 hi
      rw [Submodule.restrictScalars_mem, cocycle_coe_eq F hs (pt hi₀) (pt hsup)]
      exact F.mono _ I (Finset.singleton_subset_iff.mpr hi) _ (s.1 (pt hsup)).2
    refine ⟨⟨_, hz⟩, Subtype.ext (funext fun K => Subtype.ext ?_)⟩
    exact cocycle_coe_eq F hs (pt hi₀) K

theorem proof : CechZerothCohomologySections.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F hx
  have hp : (Cech.bdry (fun I => F.sub I) F.res 0).comap
      (LinearMap.ker (Cech.d (fun I => F.sub I) F.res 0)).subtype = ⊥ := by
    rw [show Cech.bdry (fun I => F.sub I) F.res 0 = ⊥ from rfl, Submodule.comap_bot,
      Submodule.ker_subtype]
  set_option synthInstance.maxHeartbeats 200000 in
    exact ⟨(Submodule.quotEquivOfEqBot _ hp).trans
    (LinearEquiv.ofBijective (toKer F) (toKer_bijective F hx)).symm⟩

end CechZerothCohomologySections

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.FiniteHZeroOfExact
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w v₁ v₂ v₃

namespace Cech

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R]
  {A : Cell U → Type v₁} [∀ I, AddCommGroup (A I)] [∀ I, Module R (A I)]
  {B : Cell U → Type v₂} [∀ I, AddCommGroup (B I)] [∀ I, Module R (B I)]
  {C : Cell U → Type v₃} [∀ I, AddCommGroup (C I)] [∀ I, Module R (C I)]


set_option maxHeartbeats 1000000 in
theorem finite_H_zero_of_exact [IsNoetherianRing R]
    (ρA : ∀ I J : Cell U, I.1 ⊆ J.1 → A I →ₗ[R] A J) (ρB : ∀ I J : Cell U, I.1 ⊆ J.1 → B I →ₗ[R] B J)
    (ρC : ∀ I J : Cell U, I.1 ⊆ J.1 → C I →ₗ[R] C J)
    (hρB : ∀ (I J K : Cell U) (h : I.1 ⊆ J.1) (h' : J.1 ⊆ K.1) (m : B I),
      ρB J K h' (ρB I J h m) = ρB I K (h.trans h') m)
    (ι : ∀ I, A I →ₗ[R] B I) (q : ∀ I, B I →ₗ[R] C I)
    (hι : ∀ I J h m, ι J (ρA I J h m) = ρB I J h (ι I m))
    (hq : ∀ I J h m, q J (ρB I J h m) = ρC I J h (q I m))
    (hinj : ∀ I, Function.Injective (ι I)) (hsurj : ∀ I, Function.Surjective (q I))
    (hex : ∀ I b, q I b = 0 ↔ ∃ a, ι I a = b)
    (hB : Module.Finite R (H B ρB 0)) (hA : Module.Finite R (H A ρA 1)) :
    Module.Finite R (H C ρC 0) := by
  have := hA
  have hιd := mapC_d (R := R) (G := A) (G' := B) ι hι
  have hqd := mapC_d (R := R) (G := B) (G' := C) q hq
  have hιinj : ∀ i, Function.Injective (mapC (R := R) (G := A) (G' := B) ι i) := fun i a b hab =>
    _root_.funext fun I => hinj I.1 (congrFun hab I)
  have hq0 : ∀ i (c : Cochain B i), mapC (R := R) (G := B) (G' := C) q i c = 0 ↔
      ∃ a, mapC (R := R) (G := A) (G' := B) ι i a = c := fun i c => by
    constructor
    · intro h
      choose a ha using fun I => (hex I.1 (c I)).mp (congrFun h I)
      exact ⟨a, _root_.funext ha⟩
    · rintro ⟨a, rfl⟩
      exact _root_.funext fun I => (hex I.1 _).mpr ⟨a I, rfl⟩

  obtain ⟨P, hP⟩ : ∃ P : Submodule R (Cochain B 0), ∀ w, w ∈ P ↔
      mapC (R := R) (G := B) (G' := C) q 1 (d B ρB 0 w) = 0 :=
    ⟨LinearMap.ker ((mapC (R := R) (G := B) (G' := C) q 1).comp (d B ρB 0)), fun _ => LinearMap.mem_ker⟩

  obtain ⟨θ, hθ0, hθs⟩ : ∃ θ : P →ₗ[R] H C ρC 0,
      (∀ p, θ p = 0 ↔ mapC (R := R) (G := B) (G' := C) q 0 p.1 = 0) ∧ Function.Surjective θ := by
    have hk : ∀ p : P, mapC (R := R) (G := B) (G' := C) q 0 p.1 ∈ LinearMap.ker (d C ρC 0) := fun p => by
      rw [LinearMap.mem_ker, ← hqd 0]; exact (hP p.1).mp p.2
    refine ⟨(Submodule.mkQ _).comp (LinearMap.codRestrict _
      ((mapC (R := R) (G := B) (G' := C) q 0).comp P.subtype) hk), fun p => ?_, fun h => ?_⟩
    · change Submodule.Quotient.mk _ = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact Submodule.mem_bot R
    · obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ h
      choose w hw using fun I : Idx U 0 => hsurj I.1 (c.1 I)
      have hmw : mapC (R := R) (G := B) (G' := C) q 0 w = c.1 := _root_.funext hw
      refine ⟨⟨w, (hP w).mpr (by rw [hqd 0, hmw]; exact c.2)⟩, ?_⟩
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk c
      congr 1
      exact Subtype.ext hmw

  have hdP : ∀ p : P, d B ρB 0 p.1 ∈ LinearMap.range (mapC (R := R) (G := A) (G' := B) ι 1) := fun p =>
    LinearMap.mem_range.mpr ((hq0 1 _).mp ((hP p.1).mp p.2))
  obtain ⟨g, hg⟩ : ∃ g : P →ₗ[R] Cochain A 1,
      ∀ p, mapC (R := R) (G := A) (G' := B) ι 1 (g p) = d B ρB 0 p.1 :=
    ⟨(LinearEquiv.ofInjective _ (hιinj 1)).symm.toLinearMap.comp
        (LinearMap.codRestrict _ ((d B ρB 0).comp P.subtype) hdP),
      fun p => congrArg Subtype.val ((LinearEquiv.ofInjective _ (hιinj 1)).apply_symm_apply _)⟩
  have hgk : ∀ p : P, g p ∈ LinearMap.ker (d A ρA 1) := fun p =>
    LinearMap.mem_ker.mpr (hιinj (1 + 1) ((hιd 1 (g p)).trans (by
      rw [hg, d_one_d_zero hρB, map_zero])))
  obtain ⟨ψ, hψ0⟩ : ∃ ψ : P →ₗ[R] H A ρA 1, ∀ p, ψ p = 0 ↔ ∃ g', d A ρA 0 g' = g p :=
    ⟨(Submodule.mkQ _).comp (LinearMap.codRestrict _ g hgk), fun p => by
      change Submodule.Quotient.mk _ = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact LinearMap.mem_range⟩
  have hle : LinearMap.ker θ ≤ LinearMap.ker ψ := fun p hp => by
    obtain ⟨a, ha⟩ := (hq0 0 _).mp ((hθ0 p).mp hp)
    refine (hψ0 p).mpr ⟨a, hιinj 1 ?_⟩
    rw [hg, hιd 0, ha]

  let f := (LinearMap.ker θ).liftQ ψ hle
  have hZP : LinearMap.ker (d B ρB 0) ≤ P := fun z hz =>
    (hP z).mpr (by rw [LinearMap.mem_ker.mp hz, map_zero])
  let j := (LinearMap.ker θ).mkQ.comp (Submodule.inclusion hZP)
  have hker : LinearMap.ker f = LinearMap.range j := by
    apply le_antisymm
    · intro m hm
      obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      have hm' : ψ p = 0 := hm
      obtain ⟨g', hg'⟩ := (hψ0 p).mp hm'
      have hz : p.1 - mapC (R := R) (G := A) (G' := B) ι 0 g' ∈ LinearMap.ker (d B ρB 0) := by
        rw [LinearMap.mem_ker, map_sub, ← hιd 0, hg', hg, sub_self]
      have hqι : mapC (R := R) (G := B) (G' := C) q 0 (mapC (R := R) (G := A) (G' := B) ι 0 g') = 0 :=
        (hq0 0 _).mpr ⟨g', rfl⟩
      refine ⟨⟨_, hz⟩, (Submodule.Quotient.eq _).mpr ((hθ0 _).mpr ?_)⟩
      change mapC (R := R) (G := B) (G' := C) q 0
        (p.1 - mapC (R := R) (G := A) (G' := B) ι 0 g' - p.1) = 0
      rw [sub_sub_cancel_left, map_neg, hqι, neg_zero]
    · rintro _ ⟨z, rfl⟩
      show ψ (Submodule.inclusion hZP z) = 0
      refine (hψ0 _).mpr ⟨0, hιinj 1 ?_⟩
      rw [map_zero, map_zero, hg]
      exact (LinearMap.mem_ker.mp z.2).symm

  have hZfin : Module.Finite R (LinearMap.ker (d B ρB 0)) := by
    have : Module.Finite R (LinearMap.ker (d B ρB 0) ⧸
        (bdry B ρB 0).comap (LinearMap.ker (d B ρB 0)).subtype) := hB
    exact Module.Finite.equiv (Submodule.quotEquivOfEqBot
      ((bdry B ρB 0).comap (LinearMap.ker (d B ρB 0)).subtype) (eq_bot_iff.mpr fun z hz =>
      (Submodule.mem_bot R).mpr (Subtype.ext ((Submodule.mem_bot R).mp
        (show (z : Cochain B 0) ∈ (⊥ : Submodule R (Cochain B 0)) from hz)))))
  have hM : Module.Finite R (P ⧸ LinearMap.ker θ) := by
    refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker f (IsNoetherian.noetherian _) ?_⟩
    rw [top_inf_eq, hker, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map j
  exact Module.Finite.equiv (θ.quotKerEquivOfSurjective hθs)

end Cech

theorem QuotientH0Finite.proof : QuotientH0Finite.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ F G hGF hF hG
  have key := Cech.finite_H_zero_of_exact (A := fun I => ↥(G.sub I)) (B := fun I => ↥(F.sub I))
    (C := fun I => ↥(F.sub I) ⧸ SubSystem.quotSub F G I) G.res F.res (SubSystem.quotRes F G)
    (fun _ _ _ _ _ _ => rfl)
    (fun I => { toFun := fun y => ⟨y, hGF I y.2⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl })
    (fun I => (SubSystem.quotSub F G I).mkQ) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun I a b hab => Subtype.ext (congrArg (fun y : F.sub I => (y : E)) hab))
    (fun I => Submodule.mkQ_surjective _)
    (fun I b => ⟨fun h => ⟨⟨b, (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F G I)).mp h⟩, rfl⟩,
      fun ⟨a, ha⟩ => (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F G I)).mpr (ha ▸ a.2)⟩)
    hF hG
  exact key

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart mIdealOver)

def CellLocEval.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (n : ℕ),
    Nonempty (cellH S y γ n ≃ₗ[S] cechHc ι (quotPart S (mIdealOver S y)) γ n)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHFreeObj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace KHFree

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def negSet (a : (Σ k, ι k) → ℤ) : ∀ k, Finset (ι k) :=
  fun k => Finset.univ.filter fun i => a ⟨k, i⟩ < 0

def blockSum (a : (Σ k, ι k) → ℤ) : K → ℤ :=
  fun k => ∑ i, a ⟨k, i⟩

def posExp (a : (Σ k, ι k) → ℤ) : (Σ k, ι k) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => (a p).toNat

def negExp (a : (Σ k, ι k) → ℤ) : (Σ k, ι k) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => (-a p).toNat

theorem monomial_negExp_mem (S : Type) [CommRing S] (I : ∀ k, Finset (ι k)) (a : (Σ k, ι k) → ℤ)
    (h : ∀ k, negSet a k ⊆ I k) : (monomial (negExp a) (1 : S) : MRingOver S ι) ∈ KH.cellMon S I := by
  classical
  rw [monomial_eq, C_1, one_mul, Finsupp.prod]
  refine Submonoid.prod_mem _ fun p hp => Submonoid.pow_mem _ (Submonoid.subset_closure ?_) _
  refine ⟨p.1, p.2, h p.1 ?_, rfl⟩
  have hp' : (negExp a) p ≠ 0 := Finsupp.mem_support_iff.mp hp
  simp only [negExp, Finsupp.coe_equivFunOnFinite_symm] at hp'
  simp only [negSet, Finset.mem_filter, Finset.mem_univ, true_and]
  show a p < 0
  omega


open Classical in
def monoFrac (S : Type) [CommRing S] (I : ∀ k, Finset (ι k)) (a : (Σ k, ι k) → ℤ) :
    LocalizedModule (KH.cellMon S I) (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) :=
  if h : ∀ k, negSet a k ⊆ I k then
    LocalizedModule.mk (Ideal.Quotient.mk ⊥ (monomial (posExp a) 1))
      ⟨monomial (negExp a) 1, monomial_negExp_mem S I a h⟩
  else 0

def CombCell (ι : K → Type) (J : ∀ k, Finset (ι k)) (n : ℕ) : Type :=
  {I : KH.Cell K ι n // ∀ k, J k ⊆ I.1 k}

abbrev CombC (S : Type) (J : ∀ k, Finset (ι k)) (n : ℕ) : Type :=
  CombCell ι J n → S

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]


open Classical in
def combD (S : Type) [CommRing S] (J : ∀ k, Finset (ι k)) (n : ℕ) :
    CombC S J n →ₗ[S] CombC S J (n + 1) :=
  LinearMap.pi fun I => ∑ k, ∑ i ∈ I.1.1 k,
    if h : ((∀ l, (Function.update I.1.1 k ((I.1.1 k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I.1.1 k ((I.1.1 k).erase i) l).card - 1) = n) ∧
        ∀ l, J l ⊆ Function.update I.1.1 k ((I.1.1 k).erase i) l then
      KH.faceSign I.1.1 k i • LinearMap.proj (R := S) (φ := fun _ : CombCell ι J n => S)
        ⟨⟨Function.update I.1.1 k ((I.1.1 k).erase i), h.1⟩, h.2⟩
    else 0

def combB (S : Type) [CommRing S] (J : ∀ k, Finset (ι k)) : (n : ℕ) → Submodule S (CombC S J n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (combD S J n)

end KHFree

namespace KHFree

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


open Classical in
def singOne (S : Type) [CommRing S] (J : ∀ k, Finset (ι k)) (n : ℕ) : CombC S J n :=
  fun I => if ∀ k, J k = ∅ → (I.1.1 k).card = 1 then 1 else 0


open Classical in
def embed (S : Type) [CommRing S] (a : (Σ k, ι k) → ℤ) (n : ℕ) :
    CombC S (negSet a) n →ₗ[S] KH.CechC S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n :=
  LinearMap.pi fun I => if h : ∀ k, negSet a k ⊆ I.1 k then
    (LinearMap.toSpanSingleton S _ (monoFrac S I.1 a)).comp
      (LinearMap.proj (R := S) (φ := fun _ : CombCell ι (negSet a) n => S) ⟨I, h⟩)
  else 0

end KHFree

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MulQuotEqSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def MulQuotEq.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (F₁ F₂ G₁ G₂ : SubSystem k x Ω) (s : Ω),
    (∀ I, ∀ y ∈ F₁.sub I, s * y ∈ G₁.sub I) →
    (∀ I, ∀ z ∈ G₁.sub I, ∃ y ∈ F₁.sub I, z - s * y ∈ G₂.sub I) →
    (∀ I, ∀ y ∈ F₁.sub I, (s * y ∈ G₂.sub I ↔ y ∈ F₂.sub I)) →
    eulerCharQuot k G₁ G₂ = eulerCharQuot k F₁ F₂

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionNonvanishSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SectionNonvanish.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
    primeOf (S := k) x ≤ pp → (∃ i, (X i : Poly k N) ∉ pp) →
    ∀ D : LineBundle k x, D.toSubSystem.Generated →
    ∃ s ∈ D.toSubSystem.secs, ∃ I, s ∉ (D.toSubSystem.twist (idealSys x pp)).sub I

end

end GroundTheory.Heights₂.Heights.Kleiman
end

