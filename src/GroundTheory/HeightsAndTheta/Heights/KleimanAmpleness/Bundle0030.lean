module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeTailCone
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistFiniteness.CoeffPsiMulSingle
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrictTwist
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleNefPlusAmple

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeTailLoc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Loc

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem aeval_ne_zero_of_mem_monos_support {I : Finset (Fin (N + 1))} (hI : I ⊆ support x)
    {s : Poly S N} (hs : s ∈ monos I) : aeval x s ≠ 0 := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    rw [aeval_X]
    exact (mem_support x).mp (hI hi)
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_ne_zero ha hb

theorem isUnit_coneLaurent_of_mem_monos {I : Finset (Fin (N + 1))} (hI : I ⊆ support x)
    {s : Poly S N} (hs : s ∈ monos I) : IsUnit (coneLaurent S x s) := by
  obtain ⟨e, he⟩ := monos_isHomogeneous hs
  rw [coneLaurent_of_isHomogeneous he]
  exact isUnit_coneSingle (S := S) (x := x) e (aeval_ne_zero_of_mem_monos_support hI hs)

variable (M : FinGradedSub (S := S) (x := x) Ω)

def locCone (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) :
    LocMod S N M.coneSub I →ₗ[Poly S N] ConeLaurent S x :=
  LocalizedModule.lift (monos I) M.coneSub.subtype fun s => by
    rw [Module.End.isUnit_iff]
    exact IsUnit.isUnit_iff_mulLeft_bijective.mp (isUnit_coneLaurent_of_mem_monos hI s.2)

theorem locCone_mk (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) (m : M.coneSub)
    (s : monos (S := S) I) :
    coneLaurent S x s * locCone M I hI (LocalizedModule.mk m s) = m := by
  have h1 : (s : Poly S N) • (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I) M.coneSub) =
      LocalizedModule.mk m 1 := by
    rw [LocalizedModule.smul'_mk]
    exact LocalizedModule.mk_cancel s m
  have h2 : locCone M I hI ((s : Poly S N) • LocalizedModule.mk m s) = m := by
    change LocalizedModule.lift (monos I) M.coneSub.subtype _
      ((s : Poly S N) • (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I) M.coneSub)) = m
    rw [h1]
    simp
  have h3 := (locCone M I hI).map_smul (s : Poly S N) (LocalizedModule.mk m s : LocMod S N M.coneSub I)
  exact h3.symm.trans h2

theorem locCone_mk_eq {I : Finset (Fin (N + 1))} (hI : I ⊆ support x) {m : M.coneSub}
    {s : monos (S := S) I} {w : ConeLaurent S x} (h : coneLaurent S x s * w = m) :
    locCone M I hI (LocalizedModule.mk m s) = w :=
  (isUnit_coneLaurent_of_mem_monos hI s.2).mul_left_cancel ((locCone_mk M I hI m s).trans h.symm)

theorem locCone_injective (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) :
    Function.Injective (locCone M I hI) := by
  refine (injective_iff_map_eq_zero _).mpr fun z => ?_
  refine LocalizedModule.induction_on
    (β := fun z : LocalizedModule (monos (S := S) I) M.coneSub => locCone M I hI z = 0 → z = 0)
    (fun m s hz => ?_) z
  have h := locCone_mk M I hI m s
  rw [hz, mul_zero] at h
  have hm : m = 0 := Subtype.ext h.symm
  rw [hm, LocalizedModule.zero_mk]

theorem locCone_locRes {I J : Finset (Fin (N + 1))} (h : I ⊆ J) (hJ : J ⊆ support x)
    (z : LocMod S N M.coneSub I) :
    locCone M J hJ (locRes h z) = locCone M I (h.trans hJ) z := by
  refine LocalizedModule.induction_on
    (β := fun z : LocalizedModule (monos (S := S) I) M.coneSub =>
      locCone M J hJ (locRes h z) = locCone M I (h.trans hJ) z) (fun m s => ?_) z
  rw [locRes_mk]
  exact locCone_mk_eq M hJ (locCone_mk M I _ m s)

theorem locMod_subsingleton {I : Finset (Fin (N + 1))} {i : Fin (N + 1)} (hi : i ∈ I) (hx : x i = 0) :
    Subsingleton (LocMod S N M.coneSub I) := by
  have hX : ∀ m : M.coneSub, (X i : Poly S N) • m = 0 := fun m => by
    apply Subtype.ext
    change coneLaurent S x (X i) * (m : ConeLaurent S x) = 0
    rw [coneLaurent_of_isHomogeneous (isHomogeneous_X S i), aeval_X, hx, AddMonoidAlgebra.single_zero,
      map_zero, zero_mul]
  refine subsingleton_of_forall_eq 0 fun z => ?_
  refine LocalizedModule.induction_on
    (β := fun z : LocalizedModule (monos (S := S) I) M.coneSub => z = 0) (fun m s => ?_) z
  rw [← LocalizedModule.mk_cancel_common_left ⟨X i, X_mem_monos hi⟩ s m]
  have h0 : (⟨X i, X_mem_monos hi⟩ : monos (S := S) I) • m = 0 := hX m
  rw [h0, LocalizedModule.zero_mk]

theorem locCone_degLoc (c : ℤ) (I : StdCell N) (hI : I.1 ⊆ support x) {z : LocMod S N M.coneSub I.1}
    (hz : z ∈ degLoc M.coneGraded c I) :
    ∃ v ∈ M.tilde c ⟨I.1, I.2.1, hI⟩, locCone M I.1 hI z = coneSingle S x c v := by
  refine Submodule.span_induction (p := fun z _ => ∃ v ∈ M.tilde c ⟨I.1, I.2.1, hI⟩,
    locCone M I.1 hI z = coneSingle S x c v) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨m, s, a, e, hm, hse, hae, rfl⟩
    have hs0 := aeval_ne_zero_of_mem_monos_support hI s.2
    refine ⟨(aeval x (s : Poly S N))⁻¹ • coeffAt S x a (m : ConeLaurent S x),
      Submodule.subset_span ⟨coeffAt S x a m, s, a, e, s.2, hse, m.2 a, hae, rfl⟩, locCone_mk_eq M hI ?_⟩
    rw [← coneLaurent_smul, smul_coneSingle hse, smul_eq_mul, mul_inv_cancel_left₀ hs0,
      show c + (e : ℤ) = a by omega]
    exact (M.eq_coneSingle_of_mem_conePiece hm).symm
  · exact ⟨0, zero_mem _, by rw [map_zero, map_zero]⟩
  · rintro _ _ _ _ ⟨v, hv, hzv⟩ ⟨v', hv', hzv'⟩
    exact ⟨v + v', add_mem hv hv', by rw [map_add (f := _), map_add (f := _), hzv, hzv']⟩
  · rintro s _ _ ⟨v, hv, hzv⟩
    exact ⟨s • v, (M.tilde c _).smul_of_tower_mem s hv, by rw [LinearMap.map_smul_of_tower, hzv, map_smul]⟩

def tildeGens (c : ℤ) (I : Chart x) : Set Ω :=
  {y | ∃ (m : Ω) (s : Poly S N) (a : ℤ) (e : ℕ), s ∈ monos I.1 ∧ s.IsHomogeneous e ∧ m ∈ M.piece a ∧
    a - e = c ∧ y = (aeval x s)⁻¹ • m}

theorem tilde_le_span (c : ℤ) (I : Chart x) :
    (M.tilde c I : Set Ω) ⊆ Submodule.span S (tildeGens M c I) := by
  have hclosed : ∀ a : chartRing S x I, ∀ y ∈ Submodule.span S (tildeGens M c I),
      a • y ∈ Submodule.span S (tildeGens M c I) := by
    intro a y hy
    refine Submodule.span_induction (p := fun y _ => a • y ∈ Submodule.span S (tildeGens M c I))
      ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨m, s, b, e, hs, hse, hm, hbe, rfl⟩
      obtain ⟨f, s', e', hs', hf, hse', ha⟩ := a.2
      refine Submodule.subset_span ⟨aeval x f • m, s' * s, b + e', e' + e, mul_mem hs' hs, hse'.mul hse,
        M.smul_mem e' b f m hf hm, by push_cast; omega, ?_⟩
      simp only [chartRing_smul_def, smul_eq_mul, ha, map_mul, mul_inv, div_eq_mul_inv]
      ring
    · rw [smul_zero]; exact zero_mem _
    · intro y y' _ _ hy hy'; rw [smul_add]; exact add_mem hy hy'
    · intro t y _ hy
      have : a • (t • y) = t • (a • y) := by
        rw [chartRing_smul_def, chartRing_smul_def, Algebra.smul_def, Algebra.smul_def]; ring
      rw [this]; exact Submodule.smul_mem _ t hy
  intro y hy
  exact Submodule.span_induction (p := fun y _ => y ∈ Submodule.span S (tildeGens M c I))
    (fun y hy => Submodule.subset_span hy) (zero_mem _) (fun _ _ _ _ => add_mem)
    (fun a y _ hy => hclosed a y hy) hy

theorem exists_locCone_eq (c : ℤ) (I : StdCell N) (hI : I.1 ⊆ support x) {y : Ω}
    (hy : y ∈ M.tilde c ⟨I.1, I.2.1, hI⟩) :
    ∃ z ∈ degLoc M.coneGraded c I, locCone M I.1 hI z = coneSingle S x c y := by
  refine Submodule.span_induction (p := fun y _ => ∃ z ∈ degLoc M.coneGraded c I,
    locCone M I.1 hI z = coneSingle S x c y) ?_ ?_ ?_ ?_ (tilde_le_span M c _ hy)
  · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    refine ⟨LocalizedModule.mk ⟨coneSingle S x a m, M.coneSingle_mem_coneSub hm⟩ ⟨s, hs⟩,
      Submodule.subset_span ⟨_, ⟨s, hs⟩, a, e, M.coneSingle_mem_conePiece hm, hse, hae, rfl⟩,
      locCone_mk_eq M hI ?_⟩
    have hs0 := aeval_ne_zero_of_mem_monos_support hI hs
    change s • coneSingle S x c ((aeval x s)⁻¹ • m) = coneSingle S x a m
    rw [smul_coneSingle hse, smul_eq_mul, mul_inv_cancel_left₀ hs0, show c + (e : ℤ) = a by omega]
  · exact ⟨0, zero_mem _, by rw [map_zero, map_zero]⟩
  · rintro _ _ _ _ ⟨z, hz, hzy⟩ ⟨z', hz', hzy'⟩
    exact ⟨z + z', add_mem hz hz', by rw [map_add (f := _), map_add (f := _), hzy, hzy']⟩
  · rintro t _ _ ⟨z, hz, hzy⟩
    exact ⟨t • z, Submodule.smul_mem _ t hz, by rw [LinearMap.map_smul_of_tower, hzy, map_smul]⟩

end Loc

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial AddMonoidAlgebra TwistFin

universe u w

theorem TwistFinite.proof (hE : Extension.Statement.{u, w, w}) (hSF : SerreFinite.Statement.{u, w}) :
    TwistFinite.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x G B r η hx _ hgen
  classical
  obtain ⟨M0, -, hG⟩ := hE S Ω N x Ω G.toSubFamily G.fg
  obtain ⟨n0, d0, g0, -, hspan⟩ := M0.fg
  obtain ⟨i0, hi0⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have hfin : Module.Finite (Sy S r) (cohom (tgraded x η S n0 d0 g0) 0 0) :=
    hSF (Sy S r) N _ (tgraded x η S n0 d0 g0) inferInstance 0 0
  let Γ : Set (Amb x η) := {γ | ∃ (b : ℕ) (s : Ω), s ∈ (G.twist (B.pow b)).secs ∧
    γ = (toA x η).symm (single ((0 : ℤ), (b : ℤ)) s)}
  have hΓ : Γ ⊆ LinearMap.range (readChartH0 x η S n0 d0 g0 i0 hi0) := by
    rintro _ ⟨b, s, hs, rfl⟩
    refine mem_range_readChartH0 x η S n0 d0 g0 i0 hi0 _ fun I hI => ?_
    refine chart_pre x η S (n0 := n0) (d0 := d0) (g0 := g0) M0 G B hgen hG hspan I hI b ?_
    rw [SubSystem.secs, Submodule.mem_iInf] at hs
    exact hs (toChart x I hI)
  have hfg : (Submodule.span (Sy S r) Γ).FG := by
    have : IsNoetherian (Sy S r) (LinearMap.range (readChartH0 x η S n0 d0 g0 i0 hi0)) :=
      isNoetherian_of_fg_of_noetherian _ (Module.Finite.iff_fg.mp inferInstance)
    exact isNoetherian_submodule.mp this _ (Submodule.span_le.mpr hΓ)
  obtain ⟨t, ht⟩ := hfg
  obtain ⟨T, hTΓ, htT⟩ := Submodule.subset_span_finite_of_subset_span
    (R := Sy S r) (s := Γ) (t := t) (by rw [← ht]; exact Submodule.subset_span)
  have hle : Submodule.span (Sy S r) Γ ≤ Submodule.span (Sy S r) (T : Set (Amb x η)) := by
    rw [← ht, Submodule.span_le]
    exact htT
  have hT : ∀ γ : T, ∃ (b : ℕ) (s : Ω), s ∈ (G.twist (B.pow b)).secs ∧
      (γ : Amb x η) = (toA x η).symm (single ((0 : ℤ), (b : ℤ)) s) := fun γ => hTΓ γ.2
  choose bT sT hsT hγT using hT
  let e := T.equivFin
  refine ⟨T.card, fun k => bT (e.symm k), fun k => sT (e.symm k), fun k => hsT _, ?_⟩
  intro b s hs
  have hmem : (toA x η).symm (single ((0 : ℤ), (b : ℤ)) s) ∈
      Submodule.span (Sy S r) (T : Set (Amb x η)) :=
    hle (Submodule.subset_span ⟨b, s, hs, rfl⟩)
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp hmem
  have hcoef := congrArg (fun a => (toA x η a).coeff ((0 : ℤ), (b : ℤ))) hc
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [AddEquiv.apply_symm_apply, map_sum, toA_smulSy, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, coeff_single, Finsupp.single_eq_same] at hcoef
  rw [← hcoef]
  refine Submodule.sum_mem _ fun γ hγ => ?_
  have h1 : toA x η γ = single ((0 : ℤ), ((bT ⟨γ, hγ⟩ : ℕ) : ℤ)) (sT ⟨γ, hγ⟩) := by
    have := congrArg (toA x η) (hγT ⟨γ, hγ⟩)
    rwa [AddEquiv.apply_symm_apply] at this
  rw [h1, coeff_psi_mul_single]
  refine Submodule.sum_mem _ fun d _ => ?_
  split_ifs with hdb
  · refine Submodule.subset_span ⟨e ⟨γ, hγ⟩, homogeneousComponent d (c γ), d,
      homogeneousComponent_isHomogeneous _ _, ?_, ?_⟩
    · simp only [Equiv.symm_apply_apply]
      exact hdb
    · simp only [Equiv.symm_apply_apply]
  · exact zero_mem _

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleEmbedSections
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section VeryAmpleEmbedSectionsProof

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {y : Fin (N + 1) → Ω}

theorem vaes_ampleBase_le_chartRing {r : ℕ} {h : Fin (r + 1) → Ω} {j : Fin (r + 1)} (hj : h j ≠ 0) :
    ampleBase (S := k) h j ≤ chartRing k h (singleChart hj) :=
  Algebra.adjoin_le (by rintro _ ⟨l, rfl⟩; exact (ratio (S := k) hj l).2)

theorem vaes_mem_pow_of_forall (Q : LineBundle k y) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hv : IsVeryAmpleBy Q.toSubSystem h) (I : Chart y) {m : ℕ} {s : Ω}
    (hs : ∀ j, h j ≠ 0 → ∃ e : ℕ, s * h j ^ e ∈ (Q.toSubSystem.pow (m + e)).sub I) :
    s ∈ (Q.toSubSystem.pow m).sub I := by
  have hs' : ∀ j, h j ≠ 0 → ∃ e : ℕ, s * h j ^ e ∈ Q.toSubSystem.sub I ^ (m + e) := fun j hj => by
    obtain ⟨e, he⟩ := hs j hj
    exact ⟨e, by rw [← SubSystem.pow_sub_eq_pow Q.toSubSystem]; exact he⟩
  rw [SubSystem.pow_sub_eq_pow Q.toSubSystem]
  clear hs
  obtain ⟨P', hPP'⟩ := Q.invertible I
  set P := Q.toSubSystem.sub I with hP
  let c : Ideal (chartRing k y I) := (P ^ m).comap (LinearMap.toSpanSingleton _ Ω s)
  have hc : ∀ a, a ∈ c ↔ (a : Ω) * s ∈ P ^ m := fun a => by
    change a • s ∈ P ^ m ↔ _; rw [chartRing_smul_def]
  have key : ∀ j, ∀ q ∈ P', ∀ a : chartRing k y I, (a : Ω) = h j * q → a ∈ c.radical := by
    intro j q hq a ha
    by_cases hj : h j = 0
    · have : a = 0 := Subtype.ext (by rw [ha, hj, zero_mul]; rfl)
      rw [this]; exact Ideal.zero_mem _
    obtain ⟨e, he⟩ := hs' j hj
    refine ⟨e, (hc _).mpr ?_⟩
    have hmem := Submodule.mul_mem_mul he (Submodule.pow_mem_pow P' hq e)
    rw [pow_add, mul_assoc, ← mul_pow, hPP', one_pow, mul_one] at hmem
    rw [Subalgebra.coe_pow, ha]
    convert hmem using 1
    ring
  let M : Submodule (chartRing k y I) Ω := Submodule.map (Algebra.linearMap (chartRing k y I) Ω) c.radical
  have hle : P * P' ≤ M := by
    refine Submodule.mul_le.mpr fun p hp q hq => ?_
    rw [hP, ← hv.generates I] at hp
    induction hp using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      have h1 : h j * q ∈ P * P' := Submodule.mul_mem_mul
        (by rw [hP, ← hv.generates I]; exact Submodule.subset_span ⟨j, rfl⟩) hq
      rw [hPP'] at h1
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp h1
      exact ⟨a, key j q hq a ha, ha⟩
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add u v _ _ hu hv => rw [add_mul]; exact Submodule.add_mem _ hu hv
    | smul a u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a hu
  have h1 : (1 : Ω) ∈ M := hle (by rw [hPP']; exact Submodule.one_le.mp le_rfl)
  obtain ⟨a, ha, ha1⟩ := h1
  have : a = 1 := Subtype.ext ha1
  have ha' : (1 : chartRing k y I) ∈ c.radical := this ▸ ha
  rw [← Ideal.eq_top_iff_one, Ideal.radical_eq_top, Ideal.eq_top_iff_one, hc] at ha'
  simpa using ha'

end VeryAmpleEmbedSectionsProof

theorem VeryAmpleEmbed.Sections.proof : VeryAmpleEmbed.Sections.Statement.{u, w} := by
  intro k _ Ω _ _ N y Q r h _ hv m
  apply le_antisymm
  · intro s hs
    refine (Submodule.mem_iInf _).mpr fun J => ?_
    obtain ⟨j, hjJ⟩ := J.2.1
    have hj : h j ≠ 0 := (mem_support h).mp (J.2.2 hjJ)
    have hsI : ∀ I, s ∈ (Q.toSubSystem.pow m).sub I := fun I =>
      (Submodule.restrictScalars_mem k _ _).mp ((Submodule.mem_iInf _).mp hs I)
    have hb : s / h j ^ m ∈ ampleRing Q.toSubSystem 1 (h j) := Set.mem_iInter.mpr fun I =>
      ⟨m, by rw [one_mul, div_mul_cancel₀ _ (pow_ne_zero _ hj)]; exact hsI I⟩
    have hbc := vaes_ampleBase_le_chartRing hj (hv.closed j hj hb)
    have hmem : s ∈ twistMod k h (m : ℤ) (singleChart hj) := by
      rw [twistMod_eq_span _ _ (Finset.mem_singleton_self j), Submodule.mem_span_singleton]
      exact ⟨⟨_, hbc⟩, by rw [chartRing_smul_def, zpow_natCast, div_mul_cancel₀ _ (pow_ne_zero _ hj)]⟩
    exact (Submodule.restrictScalars_mem k _ _).mpr ((twistSys k h (m : ℤ)).mono (singleChart hj) J
      (Finset.singleton_subset_iff.mpr hjJ) s hmem)
  · intro s hs
    refine (Submodule.mem_iInf _).mpr fun I => (Submodule.restrictScalars_mem k _ _).mpr ?_
    refine vaes_mem_pow_of_forall Q hv I fun j hj => ?_
    have hsj : s ∈ twistMod k h (m : ℤ) (singleChart hj) :=
      (Submodule.restrictScalars_mem k _ _).mp ((Submodule.mem_iInf _).mp hs _)
    obtain ⟨g, t, e, ht, hte, hg, hgt⟩ := exists_rep_of_mem_twistMod h m hj hsj
    have ht' : t ∈ Submonoid.closure {(X j : MvPolynomial (Fin (r + 1)) k)} := by
      have : ((fun i => (X i : MvPolynomial (Fin (r + 1)) k)) ''
          ((({j} : Finset (Fin (r + 1))) : Set (Fin (r + 1))))) = {X j} := by simp
      rw [← this]; exact ht
    obtain ⟨d, rfl⟩ := Submonoid.mem_closure_singleton.mp ht'
    have hde : e = d := hte.inj_right (isHomogeneous_X_pow j d) (by
      rw [X_pow_eq_monomial, Ne, monomial_eq_zero]; exact one_ne_zero)
    subst hde
    refine ⟨e, ?_⟩
    have := aeval_mem_pow Q.toSubSystem hv.mem_secs I hg
    rwa [hgt, map_pow, aeval_X, add_comm] at this

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleProductPos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem VeryAmpleProductPos.proof (hR : GenericPointSectionInput.Statement.{u, w}) (hP : PointDegreePos.Statement.{u, w})
    (hC : CutComponent.Statement.{u, w}) (hM : CutMultPos.Statement.{u}) :
    VeryAmpleProductPos.Statement.{u, w} := by
  intro k _ Ω _ _ N x e
  induction e with
  | zero =>
    intro pp L hW _
    have h0 : (fun i => (L i).toSubSystem) = (![] : Fin 0 → SubSystem k x Ω) :=
      funext fun i => i.elim0
    rw [h0, (hR k Ω N x).2.2.2.2 pp hW]
    exact_mod_cast hP k Ω N x pp hW
  | succ n ih =>
    intro pp L hW hL
    obtain ⟨s, hs, hsI⟩ := exists_sec_not_mem (L (Fin.last n)) (hL _) hW
    have hsplit : (fun i => (L i).toSubSystem) = Fin.snoc (α := fun _ => SubSystem k x Ω)
        (fun i : Fin n => (L (Fin.castSucc i)).toSubSystem) (L (Fin.last n)).toSubSystem :=
      (Fin.snoc_init_self _).symm
    rw [hsplit, (hR k Ω N x).2.2.2.1 n pp (fun i => L (Fin.castSucc i)) (L (Fin.last n)) s hW hs hsI]
    obtain ⟨q₀, hq₀, hq₀W⟩ := hC k Ω N x n pp (L (Fin.last n)) s hW (hL _) hs hsI

    have hterm : ∀ qq (h : qq ∈ (pp ⊔ zeroIdeal (L (Fin.last n)).toSubSystem s).minimalPrimes),
        IsSubvar x qq n → haveI : qq.IsPrime := h.1.1
        0 < (((cutMult (pp ⊔ zeroIdeal (L (Fin.last n)).toSubSystem s) qq).toNat : ℤ) *
          interNum qq (fun i => (L (Fin.castSucc i)).toSubSystem)) := by
      intro qq h hqW
      have hm := hM k N _ qq h
      exact mul_pos (by exact_mod_cast ENat.toNat_pos hm.1.ne' hm.2.ne) (ih qq _ hqW fun i => hL _)
    refine lt_of_lt_of_le ?_ (single_le_finsum q₀ ?_ ?_)
    · rw [dite_eq_left ⟨hq₀, hq₀W⟩]
      exact hterm q₀ hq₀ hq₀W
    · refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _
        (pp ⊔ zeroIdeal (L (Fin.last n)).toSubSystem s)).subset fun qq hqq => ?_
      by_contra hn
      exact hqq (dif_neg fun h => hn h.1)
    · intro qq
      split_ifs with h
      · exact (hterm qq h.1 h.2).le
      · exact le_rfl

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperQuotFiltSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperQuotFilt.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F₁ F₂ : SubFamily k x E), (∀ I, (F₁.sub I).FG) → (∀ I, F₂.sub I ≤ F₁.sub I) →
    ∀ J : Ideal (Poly k N), (∀ f ∈ J, ∀ d : ℕ, homogeneousComponent d f ∈ J) → primeOf (S := k) x ≤ J →
    (∀ I, (F₁.toSubSystem.twist (idealSys x J)).sub I ≤ F₂.sub I) →
    ∃ (r : ℕ) (G : ℕ → SubFamily k x E) (pp : Fin r → Ideal (Poly k N)) (a : Fin r → ℤ),
      (∀ m I, ((G m).sub I).FG) ∧ (G 0).toSubSystem = F₂.toSubSystem ∧
      (G r).toSubSystem = F₁.toSubSystem ∧ (∀ m < r, ∀ I, (G m).sub I ≤ (G (m + 1)).sub I) ∧
      (∀ m, (pp m).IsPrime ∧ (∀ f ∈ pp m, ∀ d : ℕ, homogeneousComponent d f ∈ pp m) ∧ J ≤ pp m) ∧
      ∀ (m : Fin r) (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ),
        Nonempty (QuotIso
          (((G (m + 1)).toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
          (((G m).toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
          (((twistSys k x (a m)).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
          ((((twistSys k x (a m)).twist (idealSys x (pp m))).twistPows t (fun j => (L j).toSubSystem) n).twist
            (twistSys k x c)))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsRestrictGenerated
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def RestrictGenerated.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (K' : Type w) [Field K'] [Algebra S K'] (y : Fin (N + 1) → K') (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (pp : Ideal (Poly S N)), primeOf (S := S) x ≤ pp → primeOf (S := S) y = pp →
    ∀ (Q : LineBundle S x) (Q' : LineBundle S y) (r : Ω → K'),
      RestrictData Q.toSubSystem hxy Q'.toSubSystem r → Q'.toSubSystem.Generated →
      ∀ I : Chart x, Q.toSubSystem.sub I ≤
        Submodule.span (chartRing S x I) {z | ∃ s : Chart x → Ω, (∀ I', s I' ∈ Q.toSubSystem.sub I') ∧
          (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ (Q.toSubSystem.twist (idealSys x pp)).sub I₂) ∧
          z = s I} ⊔ (Q.toSubSystem.twist (idealSys x pp)).sub I

end

end GroundTheory.Heights₂.Heights.Kleiman
end

