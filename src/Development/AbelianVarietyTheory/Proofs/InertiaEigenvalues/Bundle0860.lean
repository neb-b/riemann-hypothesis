module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0684
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0102
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0838
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinPullbackIsGoodTwistOfAnticyclotomicTame
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0812
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOpenSubgroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0835
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0846
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0849
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitSetInertiaPowerTrivial
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwistPullTame

theorem coprime_absNorm {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {m : ℕ}
    (hm : ((m : ℕ) : 𝓞 E) ∉ P.asIdeal) : Nat.Coprime m (Ideal.absNorm P.asIdeal) := by
  first
  | exact @_root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem
  | exact _root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem
  | (apply _root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem ..)


open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin) in
theorem tameAt_of_ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {art : Neutral.B1.Ideles E →* Gab E Ω}
    (ha : IsGlobalArtin art) {r : G E Ω →* ℂˣ} {χ : Formalism.L2.Host.HChar E} (h : GlobalTheory.ToricDistribution.Corr art r χ)
    {P : HeightOneSpectrum (𝓞 E)} {B : ValuationSubring Ω} (hB : IsPlaceOver B P) {m : ℕ}
    (hm : ((m : ℕ) : 𝓞 E) ∉ P.asIdeal) (hi : ∀ σ ∈ Ine (F := E) B, r σ ^ m = 1) : χ.TameAt P := by
  intro x hx hx1
  obtain ⟨a, ha'⟩ := GlobalTheory.Mem.UnrAe.exists_levelLe χ P
  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem P.asIdeal
  have hlt : Valued.v ((Ideal.absNorm P.asIdeal : ℕ) : P.adicCompletion E) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 E) (P.adicCompletion E)), GlobalTheory.Mem.WildChar.valued_algebraMap_lt_one]
    exact hmem
  have h3 := ha' _ (GlobalTheory.Mem.UnrAe.isUnitAt_pow hx (Ideal.absNorm P.asIdeal ^ a)) (by
    rw [Units.val_pow_eq_pow_val]
    refine GlobalTheory.Mem.WildChar.val_pow_pow_sub_one_le _ (le_of_eq hx) (hx1.trans_lt ?_) hlt a
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num)
  rw [map_pow] at h3
  have h4 : χ.loc P x ^ m = 1 := by
    obtain ⟨σ, hσ, e⟩ := (ha.ine P B hB _).mp ⟨x, hx, rfl⟩
    have e2 : χ.loc P x = r σ := h _ σ e.symm
    rw [e2, hi σ hσ]
  have hc : Nat.Coprime m (Ideal.absNorm P.asIdeal ^ a) := (coprime_absNorm hm).pow_right a
  rw [← pow_one (χ.loc P x), ← hc.gcd_eq_one]
  exact pow_gcd_eq_one.2 ⟨h4, h3⟩

theorem ine_pow_of_conj {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) {A : Type} [CommGroup A]
    {φ : G D.host.E N.Om →* A} (hanti : AntiHom X.cc φ) {P P' : Pl D.host.E} (hc : Formalism.BasicNotions.IsConjPl D.host P P') {m : ℕ}
    (h : ∀ B : ValuationSubring N.Om, IsPlaceOver B P → ∀ σ ∈ Ine (F := D.host.E) B, φ σ ^ m = 1)
    (B' : ValuationSubring N.Om) (hB' : IsPlaceOver B' P') (σ : G D.host.E N.Om) (hσ : σ ∈ Ine (F := D.host.E) B') :
    φ σ ^ m = 1 := by
  have h1 := GlobalTheory.TwistDet.cConj_mem_ine X hσ
  have h2 := GlobalTheory.TwistDet.isPlaceOver_moveVal_cc X (GlobalTheory.TwistDet.isConjPl_symm hc) hB'
  have h3 := h _ h2 _ h1
  rw [GlobalTheory.TwistDet.antiHom_cConj X hanti, inv_pow, inv_eq_one] at h3
  exact h3

theorem natCast_mem_conj {D : D7} {P P' : Pl D.host.E} (hc : Formalism.BasicNotions.IsConjPl D.host P P') (m : ℕ) :
    ((m : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal ↔ ((m : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  rw [GlobalTheory.TwistDet.isConjPl_iff.1 hc, map_natCast]

end GlobalTheory.TwistPullTame

namespace GlobalTheory.TwistPullTame

open GlobalTheory.TwistPull

theorem good_pull_tame : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (a : Recip D N.Om), a.Good → ∀ (A : Type) [CommGroup A] (φ : G D.host.E N.Om →* A), IsOpen (φ.ker : Set (G D.host.E N.Om)) → AntiHom X.cc φ → ∀ Q : Finset (Pl D.host.E), SplitSet Q → (∀ P ∈ Q, ∃ m : ℕ, ((m : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ∀ B : ValuationSubring N.Om, IsPlaceOver B P → ∀ σ ∈ Ine (F := D.host.E) B, φ σ ^ m = 1) → (∀ v : Pl D.host.E, v ∉ Q → (∀ P ∈ Q, ¬ Formalism.BasicNotions.IsConjPl D.host P v) → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, φ σ = 1) → (⟨Q, a.pull φ, resOf (a.pull φ)⟩ : Twist D A).Good := by
  intro D N X a ha A _ φ hφ hanti Q hQ hQm hunr
  haveI := finite_range (D := D) hφ
  set M := Nat.card φ.range with hMdef
  have hM : M ≠ 0 := Nat.card_pos.ne'
  have hr : ∀ f : φ.range →* ℂˣ, IsOpen ((f.comp φ.rangeRestrict).ker : Set (G D.host.E N.Om)) ∧
      ∀ σ, (f.comp φ.rangeRestrict) σ ^ M = 1 := fun f => by
    refine ⟨Subgroup.isOpen_mono (H₁ := φ.ker) (fun g hg => ?_) hφ, fun σ => ?_⟩
    · have : φ.rangeRestrict g = 1 := Subtype.ext (MonoidHom.mem_ker.1 hg)
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, this, map_one]
    · rw [MonoidHom.comp_apply, ← map_pow, pow_card_eq_one', map_one]
  have hanti' : ∀ f : φ.range →* ℂˣ, AntiHom X.cc (f.comp φ.rangeRestrict) := fun f g g' hg => by
    have e : φ.rangeRestrict g' = (φ.rangeRestrict g)⁻¹ := Subtype.ext (hanti g g' hg)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, e, map_inv]

  have hin : ∀ P ∈ Q, ∀ P' : Pl D.host.E, (P' = P ∨ Formalism.BasicNotions.IsConjPl D.host P P') → ∃ m : ℕ,
      ((m : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal ∧
        ∀ B : ValuationSubring N.Om, IsPlaceOver B P' → ∀ σ ∈ Ine (F := D.host.E) B, φ σ ^ m = 1 := by
    intro P hP P' hP'
    obtain ⟨m, hm, hB⟩ := hQm P hP
    rcases hP' with rfl | hc
    · exact ⟨m, hm, hB⟩
    · exact ⟨m, fun h => hm ((natCast_mem_conj hc m).1 h), ine_pow_of_conj X hanti hc hB⟩
  have htame : ∀ (f : φ.range →* ℂˣ) (χ : Formalism.L2.Host.HChar D.host.E),
      GlobalTheory.ToricDistribution.Corr a.art (f.comp φ.rangeRestrict) χ →
      ∀ P ∈ Q, ∀ P' : Pl D.host.E, (P' = P ∨ Formalism.BasicNotions.IsConjPl D.host P P') → χ.TameAt P' := by
    intro f χ hχ P hP P' hP'
    obtain ⟨m, hm, hB⟩ := hin P hP P' hP'
    obtain ⟨B, hB'⟩ := ReciprocityTheory.Gal.exists_isPlaceOver N.Om P'
    refine tameAt_of_ine ha.artin hχ hB' hm fun σ hσ => ?_
    have e : φ.rangeRestrict σ ^ m = 1 := Subtype.ext (by
      rw [SubmonoidClass.coe_pow, MonoidHom.coe_rangeRestrict, hB B hB' σ hσ]; rfl)
    rw [MonoidHom.comp_apply, ← map_pow, e, map_one]
  refine ⟨isOpen_ker_pull ha hφ, fun x => pull_rat ha φ x, fun y => ?_, hQ, ?_, fun PP hPP => isResAt_resOf ?_⟩
  ·
    refine (pull_eq_of_chars a hφ (y := 1) fun f => ?_).trans (map_one _)
    obtain ⟨h1, h2⟩ := hr f
    obtain ⟨c, χ, hc, hχ, hcr⟩ := exists_chrEq_pull ha h1 hM h2
    rw [map_one]
    refine Units.ext ((hcr _).symm.trans ?_)
    rw [real_C D N X a.art ha.artin _ _ hM h2 (hanti' f) c χ hc hχ y]
    simp
  ·
    intro x h1 h2 h3 h4
    refine (pull_eq_of_chars a hφ (y := 1) fun f => ?_).trans (map_one _)
    obtain ⟨o1, o2⟩ := hr f
    obtain ⟨c, χ, hc, hχ, hcr⟩ := exists_chrEq_pull ha o1 hM o2
    rw [map_one]
    refine Units.ext ((hcr _).symm.trans ?_)
    rw [GlobalTheory.T.heckeChar_unramified_outside_split_set_of_tame D N a.art ha.artin _ M hM o2 c χ hc hχ Q hQ (htame f χ hχ) (fun v hv hc' B hB σ hσ => by
      rw [MonoidHom.comp_apply, show φ.rangeRestrict σ = 1 from Subtype.ext (hunr v hv hc' B hB σ hσ), map_one]) x h1 h2 h3 h4]
    simp
  ·
    have hPP := hQ.isIdemAt hPP
    have same : ∀ (x x' : (AE D)ˣ) (u : (kP PP)ˣ), (1 - idemAt PP) * (x : AE D) = 1 - idemAt PP →
        (1 - idemAt PP) * (x' : AE D) = 1 - idemAt PP →
        ∀ (hi : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
          (hi' : toEAf D (x' : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
        resS D.host.F PP ⟨_, hi⟩ = u → resS D.host.F PP ⟨_, hi'⟩ = u → a.pull φ x = a.pull φ x' := by
      intro x x' u hx hx' hi hi' hu hu'
      refine pull_eq_of_chars a hφ fun f => ?_
      obtain ⟨o1, o2⟩ := hr f
      obtain ⟨c, χ, hc, hχ, hcr⟩ := exists_chrEq_pull ha o1 hM o2
      have ht : χ.TameAt PP := htame f χ hχ PP ‹_› PP (Or.inl rfl)
      obtain ⟨ρ, hρ⟩ := GlobalTheory.exists_isRes_of_tameAt D χ PP ht
      have e : ∀ z : (AE D)ˣ, (1 - idemAt PP) * (z : AE D) = 1 - idemAt PP →
          ∀ (hz : toEAf D (z : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
          resS D.host.F PP ⟨_, hz⟩ = u → a.pull (f.comp φ.rangeRestrict) z = ρ u := fun z hz hzi hzu =>
        Units.ext ((hcr z).symm.trans (GlobalTheory.ConjTwist.eq_res_of_chrEq hc hPP ht hρ z hz hzi u hzu))
      rw [e x hx hi hu, e x' hx' hi' hu']
    have hlift := fun u => GlobalTheory.ConjTwist.exists_isLocUnit hPP u
    choose xs hxs using hlift
    have hmul : ∀ u v, a.pull φ (xs (u * v)) = a.pull φ (xs u * xs v) := fun u v => by
      obtain ⟨hi, hu⟩ := (hxs (u * v)).res
      obtain ⟨hi1, hu1⟩ := (hxs u).res
      obtain ⟨hi2, hu2⟩ := (hxs v).res
      have hi3 : toEAf D ((xs u * xs v : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
        rw [Units.val_mul, map_mul]
        exact mul_mem hi1 hi2
      refine same _ _ (u * v) (hxs (u * v)).off ?_ hi hi3 hu ?_
      · rw [Units.val_mul, ← mul_assoc, (hxs u).off, (hxs v).off]
      · have : (⟨_, hi3⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, hi1⟩ * ⟨_, hi2⟩ :=
          Subtype.ext (by
            change toEAf D ((xs u * xs v : (AE D)ˣ) : AE D) = toEAf D (xs u : AE D) * toEAf D (xs v : AE D)
            rw [Units.val_mul, map_mul])
        rw [this, map_mul, hu1, hu2, Units.val_mul]
    refine ⟨MonoidHom.mk' (fun u => a.pull φ (xs u)) (fun u v => ?_), ?_⟩
    · show a.pull φ (xs (u * v)) = a.pull φ (xs u) * a.pull φ (xs v)
      rw [hmul, map_mul]
    · intro x hx hi u hu
      show a.pull φ x = a.pull φ (xs u)
      obtain ⟨hi', hu'⟩ := (hxs u).res
      exact same x (xs u) u hx (hxs u).off hi hi' hu hu'

end GlobalTheory.TwistPullTame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StdParabolicTwistedTraceSumNeZeroOfVector
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LevelType

theorem StdBlock.mul {p r : ℕ} {a : ℕ} {x y : GL (Fin r) (ZMod p)} (hx : StdBlock a x) (hy : StdBlock a y) :
    StdBlock a (x * y) := by
  intro i j hij
  rw [Units.val_mul, Matrix.mul_apply]
  by_cases hi : i.val ≤ a
  · have hj : ¬ a ≤ j.val := fun h => hij ⟨hi, h⟩
    have : ∀ k, y.val k j = if k = j then 1 else 0 := fun k => hy k j (fun h => hj h.2)
    simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact hx i j hij
  · have : ∀ k, x.val i k = if i = k then 1 else 0 := fun k => hx i k (fun h => hi h.1)
    simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact hy i j hij

theorem stdBlock_one {p r : ℕ} (a : ℕ) : StdBlock a (1 : GL (Fin r) (ZMod p)) := by
  intro i j _
  simp [Matrix.one_apply]

theorem stdTrace_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (r a : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (v : ρ), v ≠ 0 → StdVec ρ.ρ a θ v → stdTrace a θ ρ.character ≠ 0 := by
  intro p _ r a θ ρ v hv0 hv
  classical
  set S : Finset (GL (Fin r) (ZMod p)) := Finset.univ.filter (StdBlock a) with hS
  set c : GL (Fin r) (ZMod p) → ℂ := fun x => (((θ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) with hc
  have hcm : ∀ x y, c (x * y) = c x * c y := fun x y => by
    simp [hc, map_mul, mul_inv, Units.val_mul, mul_comm]
  set E : Module.End ℂ ρ := ∑ x ∈ S, c x • ρ.ρ x with hE
  have htr : stdTrace a θ ρ.character = LinearMap.trace ℂ ρ E := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hE, map_sum, stdTrace, hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp [FDRep.character, hc]
  have himg : ∀ x ∈ S, S.image (x * ·) = S := fun x hx => by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy ⊢
      exact hx.mul hy
    · rw [Finset.card_image_of_injective _ (mul_right_injective x)]
  have hEE : E * E = (S.card : ℂ) • E := by
    have : ∀ x ∈ S, (c x • ρ.ρ x) * E = E := fun x hx => by
      rw [hE, Finset.mul_sum]
      conv_rhs => rw [← himg x hx]
      rw [Finset.sum_image (fun y _ z _ h => mul_left_cancel h)]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [smul_mul_smul_comm, ← map_mul, hcm x y]
    calc E * E = ∑ x ∈ S, (c x • ρ.ρ x) * E := by rw [hE, Finset.sum_mul]
      _ = ∑ x ∈ S, E := Finset.sum_congr rfl this
      _ = (S.card : ℂ) • E := by rw [Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have hEv : E v = (S.card : ℂ) • v := by
    rw [hE, LinearMap.sum_apply, Finset.sum_congr rfl (g := fun _ => v), Finset.sum_const, Nat.cast_smul_eq_nsmul]
    intro x hx
    rw [LinearMap.smul_apply, hv x (by simpa [hS] using hx), smul_smul]
    simp [hc]
  have hcard : (S.card : ℂ) ≠ 0 := by
    have : (1 : GL (Fin r) (ZMod p)) ∈ S := by simpa [hS] using stdBlock_one (p := p) (r := r) a
    exact Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem this)
  set P : Module.End ℂ ρ := (S.card : ℂ)⁻¹ • E with hP
  have hPP : IsIdempotentElem P := by
    rw [IsIdempotentElem, hP, smul_mul_smul_comm, hEE, smul_smul]
    congr 1
    field_simp
  have hPv : P v = v := by
    rw [hP, LinearMap.smul_apply, hEv, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  have hP0 : P ≠ 0 := fun h => hv0 (by rw [← hPv, h, LinearMap.zero_apply])
  have htP : LinearMap.trace ℂ ρ P ≠ 0 := fun h => hP0 ((LinearMap.IsIdempotentElem.trace_eq_zero_iff hPP).1 h)
  rw [htr]
  have : E = (S.card : ℂ) • P := by rw [hP, smul_smul, mul_inv_cancel₀ hcard, one_smul]
  rw [this, map_smul, smul_eq_mul]
  exact mul_ne_zero hcard htP

end GlobalTheory.LevelType

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameGenAtTransport
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LabTies

section Galois

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

def conjHom (c : Ω ≃+* Ω) (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y) :
    G E Ω →* G E Ω where
  toFun := GlobalTheory.AntiRamConj.conjAut c hc
  map_one' := by
    ext x
    exact c.apply_symm_apply x
  map_mul' g h := by
    ext x
    change c (g (h (c.symm x))) = c (g (c.symm (c (h (c.symm x)))))
    rw [RingEquiv.symm_apply_apply]

theorem conjHom_apply (c : Ω ≃+* Ω) (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y)
    (g : G E Ω) (x : Ω) : conjHom c hc g x = c (g (c.symm x)) := rfl

theorem continuous_conjHom (c : Ω ≃+* Ω)
    (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y) : Continuous (conjHom c hc) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff E Ω U).1 hU
  obtain ⟨S, hS⟩ := IntermediateField.fg_of_fg_toSubalgebra L (Subalgebra.fg_of_fg_toSubmodule
    ((Submodule.fg_iff_finiteDimensional L.toSubalgebra.toSubmodule).2 hL))
  classical
  let L' := IntermediateField.adjoin E ((S.image c.symm : Finset Ω) : Set Ω)
  have hL' : FiniteDimensional E L' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine Filter.mem_map.2 (Filter.mem_of_superset
    ((IntermediateField.fixingSubgroup_isOpen L').mem_nhds (Subgroup.one_mem _)) fun g hg => hLU ?_)
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hg
  have key : L ≤ IntermediateField.fixedField (Subgroup.zpowers (conjHom c hc g)) := by
    rw [← hS, IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    have h1 : conjHom c hc g x = x := by
      rw [conjHom_apply, hg _ (IntermediateField.subset_adjoin _ _ (by simpa using hx)), RingEquiv.apply_symm_apply]
    exact (Subgroup.zpowers_le (H := MulAction.stabilizer (G E Ω) x)).2 h1 hf
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact (IntermediateField.mem_fixedField_iff _ _).1 (key hx) _ (Subgroup.mem_zpowers _)

theorem tameGenAt_transport (c : Ω ≃+* Ω)
    (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y)
    (hc' : ∀ x : E, ∃ y : E, c (algebraMap E Ω x) = algebraMap E Ω y)
    {B B' : ValuationSubring Ω} (hB : ∀ y, y ∈ B ↔ c y ∈ B') {γ γ' : G E Ω} (hγ : ∀ y, γ' (c y) = c (γ y))
    (h : TameGenAt B γ) : TameGenAt B' γ' := by
  have hc'' : ∀ x : E, ∃ y : E, c.symm.symm (algebraMap E Ω x) = algebraMap E Ω y := hc'
  have eB : B' = GlobalTheory.AntiRamConj.moveVal c B := by
    ext y
    rw [GlobalTheory.AntiRamConj.mem_moveVal, hB, RingEquiv.apply_symm_apply]
  have eγ : γ' = conjHom c hc γ := by
    ext y
    rw [conjHom_apply, ← hγ, RingEquiv.apply_symm_apply]
  subst eB eγ
  set f := conjHom c hc
  refine ⟨GlobalTheory.AntiRamConj.conjAut_mem_ine c hc h.1, fun σ hσ => ?_⟩
  have h1 := GlobalTheory.AntiRamConj.conjAut_mem_ine c.symm hc'' hσ
  have e2 : GlobalTheory.AntiRamConj.moveVal c.symm (GlobalTheory.AntiRamConj.moveVal c B) = B := by
    ext x
    simp [GlobalTheory.AntiRamConj.mem_moveVal]
  rw [e2] at h1
  have e3 : σ = f (GlobalTheory.AntiRamConj.conjAut c.symm hc'' σ) := by
    ext x
    rw [conjHom_apply, GlobalTheory.AntiRamConj.conjAut_apply]
    simp
  rw [e3]
  refine map_mem_closure (continuous_conjHom c hc) (h.2 h1) fun τ hτ => ?_
  have h2 := Subgroup.mem_map_of_mem f hτ
  rw [MonoidHom.map_closure] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨a, ha | ha, rfl⟩
  · exact Or.inl (congrArg f ha)
  · refine Or.inr fun y hy => ?_
    rw [GlobalTheory.AntiRamConj.moveVal_lt_one, map_sub, map_div₀, map_one, conjHom_apply, RingEquiv.symm_apply_apply]
    exact ha _ ((map_ne_zero_iff _ c.symm.injective).2 hy)

end Galois

theorem main : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut),
    GlobalTheory.PendOf.LabAll D T → IneRep D ∧ LabDepth D ∧ LabGen D := by
  intro D T ⟨γ, h1, h2, h3⟩
  have hG : GenFam D γ := by
    refine ⟨h1, fun k w hw => ?_⟩
    obtain ⟨v, rfl | hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
    · rw [h1]
      exact D.ntypes.tg_gen k v
    · obtain ⟨c, hc1, hc2, hc3⟩ := h2 k v w hv
      refine tameGenAt_transport c (fun x => ⟨D.host.conj x, ?_⟩) (fun x => ⟨_, hc1 x⟩) hc2 hc3
        (D.ntypes.tg_gen k v)
      rw [RingEquiv.symm_apply_eq, hc1, GlobalTheory.AntiRamConj.host_conj_conj]
  have h3' : GlobalTheory.PendOf.Model.LabAll T γ := h3
  exact ⟨GlobalTheory.PendOf.Model.ineRep_of_tie T, GlobalTheory.PendOf.Model.labDepth_of_tie T hG h3',
    GlobalTheory.PendOf.Model.labGen_of_tie T hG h3'⟩

end GlobalTheory.LabTies

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TieMove
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs.Move.TieUp

theorem rds_eq {D : D7} {r : Rest D} {ι : D.what₂.LL →+* (overD D r).what₂.LL} {e : ↥(overD D r).LL0 ≃+* ↥D.LL0}
    (h : CopyTw D (overD D r) ι e) {ρ : Setup D.ntw} {rd : Rds D.nexp ρ} {rd' : Rds (overD D r).nexp (setupUp r ρ)}
    (hr : RdRel h rd rd') : rd' = (rd) := by
  funext i j b
  refine LinearMap.ext fun f => ?_
  have h1 := hr ((i)) i ((HEq.refl i)) ((j)) b ((f))
  refine eq_of_heq ?_
  exact (h1)

theorem tie_move : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {ρ : Setup D.ntw} {ρ' : Setup D'.ntw}, SameSetup ρ ρ' → ∀ (hρ : ρ.Good) (hρ' : ρ'.Good)
    (rd : Rds D.nexp ρ) (rd' : Rds D'.nexp ρ'), RdRel h rd rd' → ∀ T : Comparison₂ hρ rd,
    ∃ T' : Comparison₂ hρ' rd', ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : Fin D.R.m) b,
      HEq (T i j b).rdV (T' i' (h.cm j) b).rdV := by
  intro D D' ι e h ρ ρ' hs hρ hρ' rd rd' hr T
  obtain ⟨r, rfl⟩ := h.exists_rest
  cases SameData.eq_up r hs
  have hrd := rds_eq h hr
  subst hrd
  refine ⟨fun i j b => (cellUp r h hρ' (T i j b)), fun i i' hi j b => ?_⟩
  cases hi
  exact (cellUp_rdV r h hρ' (T i j b))

end GlobalTheory.TwInputs.Move.TieUp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedIntegrandMeasurableInvariantBoundedStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedIntegrand_measurable_invariant_bounded : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (φ φ' : GA E (m + 1) → ℂ)
    (Φ : (Fin (m + 1) → Cinf E) → ℂ) (N : ℕ) (x : ℝ),
    Continuous (GlobalTheory.JSW.whit φ) → Continuous (GlobalTheory.JSW.whit φ') →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g) →
    Continuous Φ → (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    Measurable (GlobalTheory.ZEul.uInt φ φ' Φ N x) ∧
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, GlobalTheory.ZEul.uInt φ φ' Φ N x (u * g) = GlobalTheory.ZEul.uInt φ φ' Φ N x g) ∧
    ∀ g, ‖GlobalTheory.ZEul.uInt φ φ' Φ N x g‖ ≤ (‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ + ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖) / 2 := by
  first | exact @GlobalTheory.ZEulProps.uInt_props | exact GlobalTheory.ZEulProps.uInt_props | (intros; apply GlobalTheory.ZEulProps.uInt_props <;> assumption)
end

