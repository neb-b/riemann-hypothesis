module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0288
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowRepresentativesUpToFrameAdaptedIsometry
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardAdditiveCharacterLocalNeOneSplitPrime
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemAdelicLatticeClosureIffSwapMemSpan
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.AdelicLatticeSwap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))

private lemma mem_intAf_of_mem_intAd {a : Af F} (ha : a ∈ Formalism.UG.intAd F) : a ∈ Formalism.MainNotions.StandardLattice.intAf F := by
  intro v
  exact ha v

private lemma mem_intAd_of_mem_intAf {a : Af F} (ha : a ∈ Formalism.MainNotions.StandardLattice.intAf F) : a ∈ Formalism.UG.intAd F := by
  intro v
  exact ha v

private lemma intAf_mul_mem {a b : Af F} (ha : a ∈ Formalism.MainNotions.StandardLattice.intAf F) (hb : b ∈ Formalism.MainNotions.StandardLattice.intAf F) :
    a * b ∈ Formalism.MainNotions.StandardLattice.intAf F := by
  intro v
  rw [map_mul]
  exact mul_mem (ha v) (hb v)

private lemma one_mem_intAf_flag_measures : (1 : Af F) ∈ Formalism.MainNotions.StandardLattice.intAf F := by
  intro v
  rw [map_one]
  exact one_mem _


omit [NumberField E] in
theorem gen_smul_mem (a : Af F) (ha : a ∈ Formalism.UG.intAd F) (c : 𝓞 E)
    (y : Fin n → Af F ⊗[F] E) (hy : y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))) :
    (a ⊗ₜ[F] (c : E) : Af F ⊗[F] E) • y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) := by
  unfold Formalism.MainNotions.StandardLattice.latHat at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hw
    apply AddSubgroup.subset_closure
    refine ⟨a * b, intAf_mul_mem (mem_intAf_of_mem_intAd ha) hb, c • x, L.smul_mem c hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add u w _ _ hu hw => rw [smul_add]; exact add_mem hu hw
  | neg u _ hu => rw [smul_neg]; exact neg_mem hu

theorem int_smul_mem (t : E ⊗[F] Af F) (ht : t ∈ Formalism.MainNotions.S.IntAf F E) :
    ∀ y : Fin n → Af F ⊗[F] E, y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) →
      (Algebra.TensorProduct.comm F (Af F) E).symm t • y ∈
        Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) := by
  unfold Formalism.MainNotions.S.IntAf Formalism.UG.tensInt at ht
  induction ht using Subring.closure_induction with
  | mem s hs =>
    intro y hy
    rcases hs with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩
    · obtain ⟨c, rfl⟩ := he
      rw [Algebra.TensorProduct.comm_symm_tmul]
      exact gen_smul_mem L 1 (one_mem _) c y hy
    · rw [Algebra.TensorProduct.comm_symm_tmul]
      simpa using gen_smul_mem L b hb 1 y hy
  | zero => intro y _; rw [map_zero, zero_smul]; exact zero_mem _
  | one => intro y hy; rw [map_one, one_smul]; exact hy
  | add s u _ _ hs hu => intro y hy; rw [map_add (f := _), add_smul]; exact add_mem (hs y hy) (hu y hy)
  | neg s _ hs => intro y hy; rw [map_neg, neg_smul]; exact neg_mem (hs y hy)
  | mul s u _ _ hs hu => intro y hy; rw [map_mul, mul_smul]; exact hs _ (hu y hy)

theorem symm_mem_of_mem (z : Fin n → E ⊗[F] Af F) (hz : z ∈ Formalism.MainNotions.S.lamAf (F := F) L) :
    (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm (z i)) ∈
      Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) := by
  unfold Formalism.MainNotions.S.lamAf at hz
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨x, hx⟩, rfl⟩ := hw
    unfold Formalism.MainNotions.StandardLattice.latHat
    apply AddSubgroup.subset_closure
    refine ⟨1, one_mem_intAf_flag_measures, x, hx, ?_⟩
    funext i
    show (Algebra.TensorProduct.comm F (Af F) E).symm ((x i) ⊗ₜ[F] (1 : Af F)) = (1 : Af F) ⊗ₜ[F] x i
    simp
  | zero =>
    have h0 : (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm ((0 : Fin n → E ⊗[F] Af F) i)) = 0 := by
      funext i
      simp
    rw [h0]
    exact zero_mem _
  | add u w _ _ hu hw =>
    have h1 : (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm ((u + w) i)) =
        (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm (u i)) +
          fun i => (Algebra.TensorProduct.comm F (Af F) E).symm (w i) := by
      funext i
      simp
    rw [h1]
    exact add_mem hu hw
  | smul s u _ hu =>
    have h2 : (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm ((s • u) i)) =
        (Algebra.TensorProduct.comm F (Af F) E).symm (s : E ⊗[F] Af F) •
          fun i => (Algebra.TensorProduct.comm F (Af F) E).symm (u i) := by
      funext i
      simp [Subring.smul_def]
    rw [h2]
    exact int_smul_mem L s s.2 _ hu

theorem mem_latHat_iff_comm_mem_lamAf (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E))
    (y : Fin n → Af F ⊗[F] E) :
    y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) ↔
      (fun i => Algebra.TensorProduct.comm F (Af F) E (y i)) ∈ Formalism.MainNotions.S.lamAf (F := F) L := by
  constructor
  · intro hy
    unfold Formalism.MainNotions.StandardLattice.latHat at hy
    induction hy using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hw
      have hg : (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) ∈ Formalism.MainNotions.S.lamAf (F := F) L :=
        Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
      have hs : ((1 : E) ⊗ₜ[F] a : E ⊗[F] Af F) ∈ Formalism.MainNotions.S.IntAf F E :=
        Subring.subset_closure (Or.inr ⟨⟨a, mem_intAd_of_mem_intAf ha⟩, rfl⟩)
      convert Submodule.smul_mem _ (⟨_, hs⟩ : Formalism.MainNotions.S.IntAf F E) hg using 1
      funext i
      simp [Subring.smul_def, Formalism.UG.inclE, Algebra.TensorProduct.tmul_mul_tmul]
    | zero =>
      convert zero_mem (Formalism.MainNotions.S.lamAf (F := F) L) using 1
      funext i
      simp
    | add u w _ _ hu hw =>
      convert add_mem hu hw using 1
      funext i
      simp
    | neg u _ hu =>
      convert neg_mem hu using 1
      funext i
      simp
  · intro hz
    simpa using symm_mem_of_mem L _ hz

end GlobalTheory.AdelicLatticeSwap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MiddleLatticeSelfDualAnisotropicPairing
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.MidLat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem hconj (x y : S.V) : star (S.hT x y) = S.hT y x := by
  have h := S.herm.eq x y
  simpa [starRingEnd_apply] using h

def prj (e f : Fin r → S.V) : S.V →ₗ[E] S.V :=
  LinearMap.id - ∑ a, (S.hT (f a)).smulRight (e a) - ∑ a, (S.hT (e a)).smulRight (f a)

theorem prj_apply (e f : Fin r → S.V) (y : S.V) :
    prj e f y = y - ∑ a, S.hT (f a) y • e a - ∑ a, S.hT (e a) y • f a := by
  simp [prj, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smulRight_apply]

variable {e f : Fin r → S.V} (hee : ∀ a b, S.hT (e a) (e b) = 0) (hff : ∀ a b, S.hT (f a) (f b) = 0)
  (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0)

include hef in
theorem hfe (a b : Fin r) : S.hT (f a) (e b) = if b = a then 1 else 0 := by
  rw [← hconj, hef]; split_ifs <;> simp

include hee hef in
theorem prj_e (b : Fin r) : prj e f (e b) = 0 := by
  rw [prj_apply]; simp [hfe hef, hee]

include hff hef in
theorem prj_f (b : Fin r) : prj e f (f b) = 0 := by
  rw [prj_apply]; simp [hff, hef]

theorem prj_perp {y : S.V} (hy : ∀ a, S.hT (e a) y = 0 ∧ S.hT (f a) y = 0) : prj e f y = y := by
  rw [prj_apply]; simp [(hy _).1, (hy _).2]

theorem pair_prj {y : S.V} (hy : ∀ a, S.hT (e a) y = 0 ∧ S.hT (f a) y = 0) (x : S.V) :
    S.hT (prj e f x) y = S.hT x y := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [prj_apply]; simp [map_sub, map_sum, (hy _).1, (hy _).2]

include hee hef in
theorem prj_spanE {s : S.V} (hs : s ∈ Submodule.span E (Set.range e)) : prj e f s = 0 := by
  have h : Submodule.span E (Set.range e) ≤ LinearMap.ker (prj e f) :=
    Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact prj_e hee hef b)
  exact h hs

include hff hef in
theorem prj_spanF {s : S.V} (hs : s ∈ Submodule.span E (Set.range f)) : prj e f s = 0 := by
  have h : Submodule.span E (Set.range f) ≤ LinearMap.ker (prj e f) :=
    Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact prj_f hff hef b)
  exact h hs

theorem latSpanS_le_span (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (v : Fin r → S.V) :
    latSpanS aa v ≤ (Submodule.span E (Set.range v)).restrictScalars (𝓞 E) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, x, -, rfl⟩
  exact Submodule.smul_mem _ x (Submodule.subset_span ⟨a, rfl⟩)

end GlobalTheory.St.G.MidLat


open GlobalTheory.St.G.MidLat in
theorem GlobalTheory.St.G.midLat_selfDual_pairing : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), (∀ y : (VS D).V, (∀ a, (VS D).hT (X.eX a) y = 0 ∧ (VS D).hT (X.fY a) y = 0) → ((y ∈ (VS D).L0 ↔ y ∈ X.Lb) ∧ ((∀ x ∈ X.Lb, (VS D).hT x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) → y ∈ X.Lb))) ∧ (∃ x ∈ X.Lb, (VS D).hT (X.zu u) x = 1) ∧ ∀ y ∈ (VS D).L0, y - ∑ a, (VS D).hT (X.fY a) y • X.eX a - ∑ a, (VS D).hT (X.eX a) y • X.fY a ∈ X.Lb := by
  intro D X u
  have hprjL : ∀ y ∈ (VS D).L0, prj X.eX X.fY y ∈ X.Lb := by
    intro y hy
    rw [X.Lam_split] at hy
    obtain ⟨y1, hy1, t, ht, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨s, hs, l, hl, rfl⟩ := Submodule.mem_sup.1 hy1
    have hs' := latSpanS_le_span _ _ hs
    have ht' := latSpanS_le_span _ _ ht
    rw [map_add (f := _), map_add (f := _), prj_spanE X.ee X.ef hs', prj_spanF X.ff X.ef ht', zero_add, add_zero,
      prj_perp (fun a => X.Lb_perp l hl a)]
    exact hl
  have hLbL : X.Lb ≤ (VS D).L0 := by
    rw [X.Lam_split]; exact le_sup_right.trans le_sup_left
  have h1 : ∀ y : (VS D).V, (∀ a, (VS D).hT (X.eX a) y = 0 ∧ (VS D).hT (X.fY a) y = 0) →
      ((y ∈ (VS D).L0 ↔ y ∈ X.Lb) ∧
        ((∀ x ∈ X.Lb, (VS D).hT x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) → y ∈ X.Lb)) := by
    intro y hy
    refine ⟨⟨fun h => ?_, fun h => hLbL h⟩, fun hint => ?_⟩
    · have := hprjL y h; rwa [prj_perp hy] at this
    · have hU : Formalism.HermitianLatticesTheory.dual (VS D).hT (VS D).L0 = (VS D).L0 := (VS D).baseLattice_isUnimodular
      have hyL : y ∈ (VS D).L0 := by
        rw [← hU]
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
          LinearMap.restrictScalars_apply, Submodule.mem_one]
        intro x hx
        obtain ⟨o, ho⟩ := hint _ (hprjL x hx)
        exact ⟨o, by rw [ho, pair_prj hy]⟩
      have := hprjL y hyL; rwa [prj_perp hy] at this
  refine ⟨h1, ?_, fun y hy => ?_⟩

  · let σ : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (starRingEnd D.host.E)
    have hσ : ∀ o : 𝓞 D.host.E, ((σ o : 𝓞 D.host.E) : D.host.E) = star (o : D.host.E) := fun o => rfl
    let J : Ideal (𝓞 D.host.E) :=
      (LinearMap.range (((VS D).hT (X.zu u)).restrictScalars (𝓞 D.host.E) ∘ₗ X.Lb.subtype)).comap
        (Algebra.linearMap (𝓞 D.host.E) D.host.E)
    have hJ : ∀ o, o ∈ J ↔ ∃ x ∈ X.Lb, (VS D).hT (X.zu u) x = (o : D.host.E) := by
      intro o
      simp only [J, Submodule.mem_comap, LinearMap.mem_range, LinearMap.coe_comp, Function.comp_apply,
        Submodule.coe_subtype, LinearMap.restrictScalars_apply, Algebra.linearMap_apply, Subtype.exists,
        exists_prop]
    by_cases hJt : J = ⊤
    · obtain ⟨x, hx, hx1⟩ := (hJ 1).1 (hJt ▸ Submodule.mem_top)
      exact ⟨x, hx, by rw [hx1]; simp⟩
    exfalso
    obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJt
    have hM0 : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)
    obtain ⟨c, hc, hc1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := D.host.E) hM0 hM.ne_top
    have hc' := (FractionalIdeal.mem_inv_iff (by rwa [ne_eq, FractionalIdeal.coeIdeal_eq_zero])).1 hc
    have hU : Formalism.HermitianLatticesTheory.dual (VS D).hT (VS D).L0 = (VS D).L0 := (VS D).baseLattice_isUnimodular
    have hzL : X.zu u ∈ X.Lb := X.zu_Lb u
    have hwperp : ∀ a, (VS D).hT (X.eX a) (star c • X.zu u) = 0 ∧ (VS D).hT (X.fY a) (star c • X.zu u) = 0 := by
      intro a
      exact ⟨by rw [map_smul, smul_eq_mul, (X.zu_orth u a).1, mul_zero],
        by rw [map_smul, smul_eq_mul, (X.zu_orth u a).2, mul_zero]⟩
    have hwLb : star c • X.zu u ∈ X.Lb := by
      refine (h1 _ hwperp).2 ?_
      intro x hx
      have hxd : x ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT (VS D).L0 := by rw [hU]; exact hLbL hx
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
        LinearMap.restrictScalars_apply, Submodule.mem_one] at hxd
      obtain ⟨o, ho⟩ := hxd (X.zu u) (hLbL hzL)
      have hoM : o ∈ M := hJM ((hJ o).2 ⟨x, hx, ho.symm⟩)
      obtain ⟨o', ho'⟩ := (FractionalIdeal.mem_one_iff _).1
        (hc' _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨o, hoM, rfl⟩))
      refine ⟨σ o', ?_⟩
      change ((σ o' : 𝓞 D.host.E) : D.host.E) = _
      rw [hσ]
      change star (algebraMap (𝓞 D.host.E) D.host.E o') = _
      rw [ho', map_smul, smul_eq_mul, ← hconj (X.zu u) x, ← ho, star_mul, mul_comm]
    have hprim := (X.Fu_fixed u).2.2.2.2 (star c)
    dsimp only at hprim
    rw [X.flagZVector u] at hprim
    have horth : star c • X.zu u ∈ Formalism.MainNotions.S.Lat.orth (Formalism.MainNotions.S.Lat.hS D)
        (Formalism.MainNotions.S.Lat.Xsp (⟨X.Fu u, X.zu u⟩ : Formalism.MainNotions.S.Lat.LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E))) := by
      simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
      intro x hx
      have hX : Formalism.MainNotions.S.Lat.Xsp (⟨X.Fu u, X.zu u⟩ : Formalism.MainNotions.S.Lat.LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E))
          = Submodule.span D.host.E (Set.range X.eX) := by
        show Submodule.span D.host.E (Set.range (X.Fu u).e) = _
        rw [X.Fu_e u]
      rw [hX] at hx
      have hle : Submodule.span D.host.E (Set.range X.eX) ≤ LinearMap.ker ((VS D).hT (star c • X.zu u)) :=
        Submodule.span_le.2 (by
          rintro _ ⟨a, rfl⟩
          show (VS D).hT (star c • X.zu u) (X.eX a) = 0
          rw [← hconj, (hwperp a).1, star_zero])
      have := hle hx
      rw [LinearMap.mem_ker] at this
      rw [← hconj, this, star_zero]
    obtain ⟨o, ho⟩ := hprim ⟨Submodule.mem_sup_left ⟨hLbL hwLb, horth⟩, horth⟩
    apply hc1
    refine (FractionalIdeal.mem_one_iff _).2 ⟨σ o, ?_⟩
    change ((σ o : 𝓞 D.host.E) : D.host.E) = c
    rw [hσ, ho, star_star]
  · have := hprjL y hy; rwa [prj_apply] at this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedReferenceFrameCongruentUnitriangularStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedReferenceFrame_congruent_unitriangular : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ n m, n ∈ NRat (lf D (X.Fu u)) → m ∈ NRat (lf D (X.Fu u')) → Formalism.HermitianLatticesTheory.gmap (n⁻¹ * t₀.lin * m) t₀.lam' = t₀.lam → (∃ d, G.IsTerm d (c.lat (ρ * n) t₀.lam)) → ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∃ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b - frameAct (frame (lf D (X.Fu u))) ξ b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • t₀.lam)) := by
  first | exact @GlobalTheory.HL.LocCong.loc_cong | exact GlobalTheory.HL.LocCong.loc_cong | (intros; apply GlobalTheory.HL.LocCong.loc_cong <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlaceFlagUnipotentRadicalIsUnipotent
section
open Matrix

noncomputable section

namespace GlobalTheory.UnipRadNilp

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n r : ℕ}

theorem hJ_sub_right (ε : Fin n → Bool) (x y w : Fin n → ℂ) : hJ ε x (y - w) = hJ ε x y - hJ ε x w := by
  unfold hJ; rw [mulVec_sub, dotProduct_sub]

theorem hJ_sub_left (ε : Fin n → Bool) (x y w : Fin n → ℂ) : hJ ε (x - y) w = hJ ε x w - hJ ε y w := by
  unfold hJ; rw [star_sub, sub_dotProduct]

theorem hJ_add_left (ε : Fin n → Bool) (x y w : Fin n → ℂ) : hJ ε (x + y) w = hJ ε x w + hJ ε y w := by
  unfold hJ; rw [star_add, add_dotProduct]

theorem hJ_smul_left (ε : Fin n → Bool) (c : ℂ) (x w : Fin n → ℂ) : hJ ε (c • x) w = star c * hJ ε x w := by
  unfold hJ; rw [star_smul, smul_dotProduct, smul_eq_mul]

theorem hJ_zero_left' (ε : Fin n → Bool) (w : Fin n → ℂ) : hJ ε 0 w = 0 := by
  unfold hJ; simp

theorem orth_span (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (b : ℕ) (w : Fin n → ℂ)
    (hw : ∀ c : Fin r, c.1 < b → hJ ε (e c) w = 0) : ∀ v ∈ spanLt e b, hJ ε v w = 0 := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    exact hw c hc
  | zero => exact hJ_zero_left' ε w
  | add x y _ _ hx hy => rw [hJ_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [hJ_smul_left, hx, mul_zero]

theorem spanLt_zero (e : Fin r → Fin n → ℂ) : spanLt e 0 = ⊥ := by
  unfold spanLt
  have : (e '' {b : Fin r | b.1 < 0}) = ∅ := by
    ext x; simp
  rw [this, Submodule.span_empty]

theorem pow_lower (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) {G : Matrix (Fin n) (Fin n) ℂ}
    (hG : InS e z G) (k : ℕ) : ∀ m, ∀ v ∈ spanLt e (m + k), (G - 1) ^ k *ᵥ v ∈ spanLt e m := by
  induction k with
  | zero => intro m v hv; simpa using hv
  | succ k ih =>
    intro m v hv
    have h1 : (G - 1) *ᵥ v ∈ spanLt e (m + k) := by
      have hle : spanLt e (m + (k + 1)) ≤ (spanLt e (m + k)).comap (Matrix.mulVecLin (G - 1)) := by
        unfold spanLt
        rw [Submodule.span_le]
        rintro _ ⟨b, hb, rfl⟩
        have hb' : (b : ℕ) < m + (k + 1) := hb
        simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
        refine Submodule.span_mono ?_ (hG.1 b)
        rintro _ ⟨c, hc, rfl⟩
        have hc' : (c : ℕ) < b := hc
        exact ⟨c, show (c : ℕ) < m + k by omega, rfl⟩
      exact hle hv
    rw [pow_succ, ← mulVec_mulVec]
    exact ih m _ h1

theorem nilp (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Formalism.REAL.UJ ε)
    (hg : g ∈ NLoc ε e z) : (Formalism.MainNotions.S.uMat g - 1) ^ (2 * r + 1) = 0 := by
  set G := Formalism.MainNotions.S.uMat g with hGdef
  have hN : InN ε e z G := hg
  have hS' : InS e z (Formalism.MainNotions.S.uMat g⁻¹) :=
    (Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI.SG ε e z).inv_mem hg.1
  have hGG' : G * Formalism.MainNotions.S.uMat g⁻¹ = 1 := Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.uMat_mul_inv ε g
  have hiso := Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.isIsom_uMat ε g

  have adj : ∀ b : Fin r, ∀ w, hJ ε (e b) ((G - 1) *ᵥ w) = hJ ε ((Formalism.MainNotions.S.uMat g⁻¹ - 1) *ᵥ e b) w := by
    intro b w
    have h1 : hJ ε (e b) (G *ᵥ w) = hJ ε (Formalism.MainNotions.S.uMat g⁻¹ *ᵥ e b) w := by
      have := hiso (Formalism.MainNotions.S.uMat g⁻¹ *ᵥ e b) w
      rw [mulVec_mulVec, hGG', one_mulVec] at this
      exact this
    rw [sub_mulVec, one_mulVec, hJ_sub_right, h1, sub_mulVec, one_mulVec, hJ_sub_left]

  have step1 : ∀ k, ∀ x, ∀ b : Fin r, b.1 < k → hJ ε (e b) ((G - 1) ^ k *ᵥ x) = 0 := by
    intro k
    induction k with
    | zero => intro x b hb; omega
    | succ k ih =>
      intro x b hb
      rw [pow_succ', ← mulVec_mulVec, adj]
      refine orth_span ε e b.1 _ (fun c hc => ih x c (by omega)) _ (hS'.1 b)
  have step2 : ∀ x, (G - 1) ^ (r + 1) *ᵥ x ∈ spanLt e r := by
    intro x
    rw [pow_succ', ← mulVec_mulVec]
    exact hN.2 _ (fun a => step1 r x a a.2)
  have step3 : ∀ x, (G - 1) ^ (2 * r + 1) *ᵥ x = 0 := by
    intro x
    have : (G - 1) ^ (2 * r + 1) = (G - 1) ^ r * (G - 1) ^ (r + 1) := by
      rw [← pow_add]; ring_nf
    rw [this, ← mulVec_mulVec]
    have hm := pow_lower e z hN.1 r 0 _ (by rw [zero_add]; exact step2 x)
    rw [spanLt_zero] at hm
    exact (Submodule.mem_bot ℂ).1 hm
  ext i j
  have := congrFun (step3 (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

end GlobalTheory.UnipRadNilp

theorem GlobalTheory.unipRad_pow_eq_zero : ∀ {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Formalism.REAL.UJ ε), g ∈ Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc ε e z → (Formalism.MainNotions.S.uMat g - 1) ^ (2 * r + 1) = 0 :=
  fun ε e z g hg => GlobalTheory.UnipRadNilp.nilp ε e z g hg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowRepresentativesUpToFrameAdaptedIsometryStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_representatives_up_to_frame_adapted_isometry : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (∀ Λ, IsRowLat D (X.Fu u) Λ → ∃ Λ' ∈ Y.what₂ u, ∃ σ, Adapt σ (lf D (X.Fu u)) (lf D (X.Fu u)) ∧ Formalism.HermitianLatticesTheory.gmap σ Λ' = Λ) ∧ ∀ Λ ∈ Y.what₂ u, ∀ Λ' ∈ Y.what₂ u, ∀ σ, Adapt σ (lf D (X.Fu u)) (lf D (X.Fu u)) → Formalism.HermitianLatticesTheory.gmap σ Λ' = Λ → Λ' = Λ := by
  intro D X Y u u'
  exact GlobalTheory.RowRep.rowReps D X Y u u'
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardAdditiveCharacterLocalNeOneSplitPrimeStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardAdditiveCharacter_local_ne_one_splitPrime : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (psi : E ⊗[F] Ad F → ℂ), (∀ x y, psi (x + y) = psi x * psi y) → (∀ x ∈ OAd F E, psi x = 1) → (∀ x : E, psi (inclE (F := F) (Ad F) x) * Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ E x : ℚ) : ℂ)) = 1) → ∀ (p : ℕ), p.Prime → SplitsIn E p → ∀ (v : HeightOneSpectrum (𝓞 F)), (p : 𝓞 F) ∈ v.asIdeal → ∀ e ∈ intV E v, e * e = e → e ≠ 0 → ∃ a ∈ intV E v, psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((p : F)⁻¹) * (e * a))) ≠ 1 := by
  first | exact @GlobalTheory.St.G.psi_local_ne_one | exact GlobalTheory.St.G.psi_local_ne_one | (intros; apply GlobalTheory.St.G.psi_local_ne_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VagueLimitRescaledMeasuresProdStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vague_limit_rescaled_measures_prod : ∀ (α β V W : Type) [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (c : α → V) (c' : β → W) (lam : Measure V) (lam' : Measure W) [IsLocallyFiniteMeasure lam] [IsLocallyFiniteMeasure lam'] (d d' : ℕ), Measurable c → Measurable c' → Vag μ c lam d → Vag ν c' lam' d' → Vag (μ.prod ν) (Prod.map c c') (lam.prod lam') (d + d') := by
  first | exact @GlobalTheory.IwConst.vag_prod | exact GlobalTheory.IwConst.vag_prod | (intros; apply GlobalTheory.IwConst.vag_prod <;> assumption)
end

