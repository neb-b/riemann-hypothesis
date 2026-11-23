module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0037
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0833
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryGroupCharacterOfHeckeChar
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDetCharacter

def cut {R : Type} [CommRing R] (ε : R) (h : ε * ε = ε) : R →* R where
  toFun u := (1 - ε) + ε * u
  map_one' := by ring
  map_mul' u v := by linear_combination (-(1 - u - v + u * v)) * h

theorem mul_det_sub_one {R : Type} [CommRing R] {n : ℕ} (a : R) (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, a * (M - 1) i j = 0) : a * (M.det - 1) = 0 := by
  let I : Ideal R := LinearMap.ker (LinearMap.mul R R a)
  have h1 : (Ideal.Quotient.mk I).mapMatrix M = (Ideal.Quotient.mk I).mapMatrix 1 := by
    ext i j
    exact Ideal.Quotient.eq.2 (h i j)
  have h2 := congrArg Matrix.det h1
  rw [← RingHom.map_det, ← RingHom.map_det, Matrix.det_one] at h2
  exact Ideal.Quotient.eq.1 h2

theorem cut_eq {R : Type} [CommRing R] {ε e f d : R} (a1 : ε * e = e)
    (a2 : ε * f = 0) (hd : (1 - (e + f)) * (d - 1) = 0) : (1 - ε) + ε * d = e * d + (1 - e) := by
  linear_combination ε * hd + (d - 1) * (a1 + a2)

theorem cut_mul {R : Type} [CommRing R] {ε e f d d' : R} (e2 : f * f = f) (a1 : ε * e = 0)
    (a2 : ε * f = f) (hd : (1 - (e + f)) * (d - 1) = 0) (e3 : d * d' = 1) :
    ((1 - ε) + ε * d) * (f * d' + (1 - f)) = 1 := by
  have e4 : ε * (d - 1) = f * (d - 1) := by
    linear_combination ε * hd + (d - 1) * (a1 + a2)
  linear_combination (1 + f * (d' - 1)) * e4 + (d - 1) * (d' - 1) * e2 + f * e3

variable {D : D7}

theorem det_mul_conj (V : HSp D) (g : GA D V) :
    (Formalism.L2.Theta.mt V g).det * cA D (Formalism.L2.Theta.mt V g).det = 1 := by
  have h : ((Formalism.L2.Theta.mt V g).map (cA D))ᵀ * V.gram.map (incA D) * Formalism.L2.Theta.mt V g = V.gram.map (incA D) := g.2
  have hu := (GlobalTheory.LatVac.gram_det_isUnit V).map (incA D)
  rw [RingHom.map_det, RingHom.mapMatrix_apply] at hu
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply (cA D), ← RingHom.map_det] at h2
  refine hu.mul_left_cancel ?_
  linear_combination h2

theorem algebraMap_norm (z : AE D) :
    algebraMap (AF D.host.F) (AE D) (Algebra.norm (AF D.host.F) z) = z * cA D z := by
  have hx : ∃ x, D.sp.cm.sig x ≠ x := by
    by_contra h
    push Not at h
    have hs : Function.Surjective (algebraMap D.host.F D.host.E) := fun x => (D.sp.cm.fixed x).1 (h x)
    have h1 : Module.finrank D.host.F D.host.E = 1 := by
      rw [← (LinearEquiv.ofBijective (Algebra.linearMap D.host.F D.host.E)
        ⟨(algebraMap D.host.F D.host.E).injective, hs⟩).finrank_eq, Module.finrank_self]
    have h2 := D.sp.cm.deg2
    omega
  obtain ⟨δ, -, h⟩ := GlobalTheory.QuadNormBase.norm_form D.host.F D.host.E D.sp.cm.sig D.sp.cm.deg2 (fun x => star_star x) hx
  obtain ⟨x, y, e1, e2⟩ := (h (AF D.host.F)).1 z
  rw [e1, e2]

theorem char_norm {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (x x' : (AE D)ˣ)
    (hx : (x' : AE D) = cA D x) : χ x * χ x' = 1 := by
  obtain ⟨⟨η, hη⟩, h1⟩ := h
  have e : x * x' = idF D (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) x) := by
    refine Units.ext ?_
    rw [Units.val_mul, hx]
    exact (algebraMap_norm (x : AE D)).symm
  rw [← map_mul, e, h1 η hη, hη.2.2.1 x, one_pow]

theorem char_eq_of_mul_conj {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (y x : (AE D)ˣ)
    (hy : (y : AE D) * cA D x = 1) : χ y = χ x := by
  obtain ⟨x', hx'⟩ : IsUnit (cA D x) := x.isUnit.map (cA D)
  have hc := char_norm h x x' hx'
  have h1 : y * x' = 1 := Units.ext (by rw [Units.val_mul, hx', hy, Units.val_one])
  have h2 := congrArg χ h1
  rw [map_mul, map_one, ← hc] at h2
  exact mul_right_cancel h2

def cutDet (ε : AE D) (h : ε * ε = ε) (V : HSp D) : GA D V →* (AE D)ˣ :=
  (Units.map (cut ε h)).comp ((Matrix.GeneralLinearGroup.det (n := Fin V.rank) (R := AE D)).comp (matHom V))

theorem cutDet_val (ε : AE D) (h : ε * ε = ε) (V : HSp D) (g : GA D V) :
    (cutDet ε h V g : AE D) = (1 - ε) + ε * (Formalism.L2.Theta.mt V g).det := rfl

theorem cutDet_eq_one (ε : AE D) (h : ε * ε = ε) (V : HSp D) (g : GA D V)
    (hg : ∀ i j, ε * (Formalism.L2.Theta.mt V g - 1) i j = 0) : cutDet ε h V g = 1 := by
  refine Units.ext ?_
  rw [cutDet_val, Units.val_one]
  linear_combination mul_det_sub_one ε _ hg

theorem continuous_cutDet (ε : AE D) (h : ε * ε = ε) (V : HSp D) : Continuous (cutDet ε h V) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have h0 : Continuous fun g : GA D V => matHom V g := continuous_subtype_val
  have h1 : Continuous (Formalism.L2.Theta.mt V) := Units.continuous_val.comp h0
  have h2 : Continuous fun g : GA D V => Formalism.L2.Theta.mt V g⁻¹ := by
    have e : (fun g : GA D V => Formalism.L2.Theta.mt V g⁻¹) = fun g => ((matHom V g)⁻¹).1 := by
      funext g
      unfold Formalism.L2.Theta.mt
      rw [map_inv]
    rw [e]
    exact Units.continuous_coe_inv.comp h0
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_const.add (continuous_const.mul h1.matrix_det)
  · simp only [← map_inv, cutDet_val]
    exact continuous_const.add (continuous_const.mul h2.matrix_det)

theorem cutDet_real (ε : AE D) (h1 : ε * ε = ε) (h3 : infPart D ε = 0) (V : HSp D) (g : GA D V) (hg : g ∈ GinfC V) :
    cutDet ε h1 V g = 1 := by
  refine cutDet_eq_one ε h1 V g fun i j => ?_
  have hm : (Formalism.L2.Theta.mt V g).map (finPart D) = 1 := congrArg Units.val (show finHom V g = 1 from hg)
  have hf : finPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
    have e1 : finPart D (Formalism.L2.Theta.mt V g i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j :=
      congrFun (congrFun hm i) j
    rw [Matrix.sub_apply, RingHom.map_sub, e1, sub_eq_zero]
    by_cases e : i = j
    · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]
  exact GlobalTheory.SplitScalar.adele_ext (by rw [RingHom.map_mul, h3, zero_mul, RingHom.map_zero])
    (by rw [RingHom.map_mul, hf, mul_zero, RingHom.map_zero])

theorem det_supp {e : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt e V g) :
    (1 - (e + cA D e)) * ((Formalism.L2.Theta.mt V g).det - 1) = 0 :=
  mul_det_sub_one _ _ fun i j => by rw [sub_mul, one_mul, hg i j, sub_self]

set_option maxHeartbeats 1000000 in
theorem cutDet_same (ε : AE D) (h1 : ε * ε = ε) {e : AE D} (a1 : ε * e = e) (a2 : ε * cA D e = 0) {V : HSp D} {g : GA D V}
    {x : (AE D)ˣ} (hg : SuppAt e V g) (hx : IsDetAt e V g x) : cutDet ε h1 V g = x := by
  have hx' : (x : AE D) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) := hx
  refine Units.ext ?_
  rw [cutDet_val, hx']
  exact cut_eq a1 a2 (det_supp hg)

set_option maxHeartbeats 1000000 in
theorem cutDet_conj (ε : AE D) (h1 : ε * ε = ε) {e : AE D} (he : e * e = e) (a1 : ε * e = 0) (a2 : ε * cA D e = cA D e)
    {V : HSp D} {g : GA D V} {x : (AE D)ˣ} (hg : SuppAt e V g) (hx : IsDetAt e V g x) :
    (cutDet ε h1 V g : AE D) * cA D x = 1 := by
  have hx' : (x : AE D) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) := hx
  have e2 : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have e5 : cA D x = cA D e * cA D (Formalism.L2.Theta.mt V g).det + (1 - cA D e) := by
    rw [hx', RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub, RingHom.map_one]
  rw [cutDet_val, e5]
  exact cut_mul e2 a1 a2 (det_supp hg) (det_mul_conj V g)


set_option maxHeartbeats 1000000 in
theorem exists_character : ∀ (D : D7) (ε : AE D), (ε * ε = ε ∧ ε * cA D ε = 0 ∧ infPart D ε = 0 ∧ (∀ e, IsSplitIdem D e → (ε * e = e ∧ ε * cA D e = 0) ∨ (ε * e = 0 ∧ ε * cA D e = cA D e)) ∧ ∀ v η, NonSplitAt D v η → algebraMap (AF D.host.F) (AE D) η * ε = 0) → ∀ (V : HSp D) (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∃ c : GA D V →* Circle, Continuous c ∧ (∀ g ∈ GinfC V, c g = 1) ∧ (∀ v η, NonSplitAt D v η → ∀ g, SuppPl η V g → c g = 1) ∧ ∀ e, IsSplitIdem D e → ∀ g x, SuppAt e V g → IsDetAt e V g x → c g = χ x := by
  rintro D ε ⟨h1, -, h3, h4, h5⟩ V χ n hχ hres
  refine ⟨χ.comp (cutDet ε h1 V), hχ.1.comp (continuous_cutDet ε h1 V), fun g hg => ?_, fun v η hv g hg => ?_,
    fun e he g x hg hx => ?_⟩
  · rw [MonoidHom.comp_apply, cutDet_real ε h1 h3 V g hg, map_one]
  · rw [MonoidHom.comp_apply, cutDet_eq_one ε h1 V g fun i j => ?_, map_one]
    rw [← hg i j, ← mul_assoc, mul_comm ε, h5 v η hv, zero_mul]
  · rw [MonoidHom.comp_apply]
    rcases h4 e he with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · rw [cutDet_same ε h1 a1 a2 hg hx]
    · exact char_eq_of_mul_conj hres _ x (cutDet_conj ε h1 he.1 a1 a2 hg hx)

end GlobalTheory.SplitDetCharacter
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimContinuousNormLeOnIccOfDetermined
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory

theorem finiteDim_norm_le_on_Icc_of_determined :
    ∀ (V : Submodule ℂ (ℝ → ℂ)), FiniteDimensional ℂ V → (∀ f ∈ V, Continuous f) → ∀ ℓ : ℝ, 0 < ℓ →
    (∀ f ∈ V, (∀ x ∈ Set.Icc 0 ℓ, f x = 0) → f = 0) → ∀ R : ℝ, ∃ C : ℝ, ∀ f ∈ V, ∀ M : ℝ,
      (∀ x ∈ Set.Icc 0 ℓ, ‖f x‖ ≤ M) → ∀ t ∈ Set.Icc (-R) R, ‖f t‖ ≤ C * M := by
  intro V hV hcont ℓ hℓ hdet R
  let ev : Set.Icc (0:ℝ) ℓ → Module.Dual ℂ V := fun x =>
    (LinearMap.proj (R := ℂ) (φ := fun _ : ℝ => ℂ) (x:ℝ)).comp V.subtype
  obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' ℂ ev
  haveI : Finite κ := hli.finite
  letI : Fintype κ := Fintype.ofFinite κ
  classical
  let T : V →ₗ[ℂ] (κ → ℂ) := LinearMap.pi (fun k => ev (a k))
  have hT : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro g hg
    have h1 : Submodule.span ℂ (Set.range (ev ∘ a)) ≤ LinearMap.ker (Module.Dual.eval ℂ V g) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have := congrFun hg k
      simpa [T] using this
    rw [hspan] at h1
    have h2 : ∀ x ∈ Set.Icc (0:ℝ) ℓ, (g : ℝ → ℂ) x = 0 := by
      intro x hx
      have := h1 (Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩)
      simpa [ev] using this
    exact Subtype.ext (hdet g g.2 h2)
  obtain ⟨S, hS⟩ := LinearMap.exists_leftInverse_of_injective T hT
  let g : κ → ℝ → ℂ := fun k => (S (Pi.single k 1) : ℝ → ℂ)
  have hB : ∀ k, ∃ B, ∀ t ∈ Set.Icc (-R) R, ‖g k t‖ ≤ B := fun k =>
    (isCompact_Icc).exists_bound_of_continuousOn (hcont _ (S (Pi.single k 1)).2).continuousOn
  choose B hB using hB
  refine ⟨∑ k, max (B k) 0, ?_⟩
  intro f hf M hM t ht
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_rfl, hℓ.le⟩)
  have e : (⟨f, hf⟩ : V) = S (T ⟨f, hf⟩) := (LinearMap.congr_fun hS _).symm
  have e2 : T ⟨f, hf⟩ = ∑ k, (f (a k)) • (Pi.single k 1 : κ → ℂ) := by
    ext j; simp [T, ev, Finset.sum_apply, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e2, map_sum] at e
  have e3 := congrFun (congrArg Subtype.val e) t
  have hft : f t = ∑ k, f (a k) * g k t := by
    simpa [g, Finset.sum_apply] using e3
  rw [hft, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, mul_comm]
  exact mul_le_mul ((hB k t ht).trans (le_max_left _ _)) (hM _ (a k).2) (norm_nonneg _)
    (le_max_right _ _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKilledEqOfEqualMultiplicities
section
noncomputable section

open GlobalTheory.CuspMult

namespace GlobalTheory.RepCount

variable {H W X : Type} [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]

def modMap {σ : Representation ℂ H W} {ρ : Representation ℂ H X} (f : W →ₗ[ℂ] X)
    (hf : ∀ g s, f (σ g s) = ρ g (f s)) : σ.asModule →ₗ[MonoidAlgebra ℂ H] ρ.asModule :=
  Representation.IntertwiningMap.equivLinearMapAsModule σ ρ
    (f.intertwiningMap_of_isIntertwiningMap σ ρ hf)

theorem modMap_apply {σ : Representation ℂ H W} {ρ : Representation ℂ H X} (f : W →ₗ[ℂ] X)
    (hf : ∀ g s, f (σ g s) = ρ g (f s)) (x : σ.asModule) :
    ρ.asModuleEquiv (modMap f hf x) = f (σ.asModuleEquiv x) := rfl

def subEquiv {ρ : Representation ℂ H X} (U : Subrepresentation ρ) :
    U.toRepresentation.asModule ≃ₗ[MonoidAlgebra ℂ H] U.asSubmodule :=
  LinearEquiv.ofBijective
    ((modMap (σ := U.toRepresentation) (ρ := ρ) U.toSubmodule.subtype (fun _ _ => rfl)).codRestrict
      U.asSubmodule (fun x => (U.toRepresentation.asModuleEquiv x).2))
    ⟨fun a b h => U.toRepresentation.asModuleEquiv.injective (Subtype.ext (congrArg Subtype.val h)),
     fun y => ⟨U.toRepresentation.asModuleEquiv.symm ⟨ρ.asModuleEquiv y.1, y.2⟩, rfl⟩⟩

variable [TopologicalSpace H]

theorem isAdmissible_of_injective {σ : Representation ℂ H W} {ρ : Representation ℂ H X}
    (f : W →ₗ[ℂ] X) (hf : ∀ g s, f (σ g s) = ρ g (f s)) (hi : Function.Injective f)
    (h : GlobalTheory.PRep.IsAdmissible ρ) : GlobalTheory.PRep.IsAdmissible σ := by
  refine ⟨fun v => ?_, fun K hK hK' => ?_⟩
  · have : {g : H | σ g v = v} = {g : H | ρ g (f v) = f v} := by
      ext g
      simp only [Set.mem_setOf_eq, ← hf, hi.eq_iff]
    rw [this]
    exact h.1 _
  · haveI := h.2 K hK hK'
    refine FiniteDimensional.of_injective
      (f.restrict (p := GlobalTheory.PRep.fixed σ K) (q := GlobalTheory.PRep.fixed ρ K) (fun v hv k => ?_)) ?_
    · rw [← hf, hv k, map_smul]
    · intro a b hab
      exact Subtype.ext (hi (congrArg Subtype.val hab))

def pieces (ρ : Representation ℂ H X) (C : Submodule ℂ X) :
    Set (Submodule (MonoidAlgebra ℂ H) ρ.asModule) :=
  {m | ∃ U : Subrepresentation ρ, (U.toSubmodule ≤ C ∧ U.toRepresentation.IsIrreducible ∧
    GlobalTheory.PRep.IsAdmissible U.toRepresentation) ∧ U.asSubmodule = m}

theorem simple_of_mem_pieces {ρ : Representation ℂ H X} {C : Submodule ℂ X}
    {m : Submodule (MonoidAlgebra ℂ H) ρ.asModule} (hm : m ∈ pieces ρ C) :
    IsSimpleModule (MonoidAlgebra ℂ H) m := by
  obtain ⟨U, ⟨-, hU, -⟩, rfl⟩ := hm
  exact IsSimpleModule.congr (subEquiv U).symm

theorem mem_sSup_pieces_of_mem {ρ : Representation ℂ H X} {C : Submodule ℂ X} {x : X}
    (hx : x ∈ irrSum ρ C) : ρ.asModuleEquiv.symm x ∈ sSup (pieces ρ C) := by
  have : irrSum ρ C ≤ ((sSup (pieces ρ C)).restrictScalars ℂ).comap
      ρ.asModuleEquiv.symm.toLinearMap := by
    refine iSup₂_le fun U hU y hy => ?_
    exact (le_sSup (s := pieces ρ C) ⟨U, hU, rfl⟩ : U.asSubmodule ≤ _) hy
  exact this hx

theorem mem_of_mem_sSup_pieces {ρ : Representation ℂ H X} {C : Submodule ℂ X} {x : ρ.asModule}
    (hx : x ∈ sSup (pieces ρ C)) : ρ.asModuleEquiv x ∈ C := by
  rw [sSup_eq_iSup'] at hx
  refine Submodule.iSup_induction _ (motive := fun x => ρ.asModuleEquiv x ∈ C) hx ?_ ?_ ?_
  · rintro ⟨_, U, hU, rfl⟩ y hy
    exact hU.1 hy
  · simp
  · intro a b ha hb
    rw [map_add (f := _)]
    exact C.add_mem ha hb

theorem semisimple_sSup_pieces (ρ : Representation ℂ H X) (C : Submodule ℂ X) :
    IsSemisimpleModule (MonoidAlgebra ℂ H) ↥(sSup (pieces ρ C)) := by
  rw [sSup_eq_iSup]
  refine isSemisimpleModule_biSup_of_isSemisimpleModule_submodule fun m hm => ?_
  haveI := simple_of_mem_pieces hm
  infer_instance

theorem apply_mem_irrSum {σ : Representation ℂ H W} {ρ : Representation ℂ H X} {C : Submodule ℂ X}
    (h1 : σ.IsIrreducible) (h2 : GlobalTheory.PRep.IsAdmissible σ) {f : W →ₗ[ℂ] X}
    (hf : f ∈ homInto σ ρ C) (s : W) : f s ∈ irrSum ρ C := by
  let F := f.intertwiningMap_of_isIntertwiningMap σ ρ hf.2
  rcases Representation.IsIrreducible.injective_or_eq_zero F with hi | h0
  · have hi' : Function.Injective f := hi
    let e : W ≃ₗ[ℂ] F.range.toSubmodule := LinearEquiv.ofInjective f hi'
    have he : ∀ g s, e (σ g s) = F.range.toRepresentation g (e s) :=
      fun g s => Subtype.ext (hf.2 g s)
    have he' : ∀ g s, e.symm (F.range.toRepresentation g s) = σ g (e.symm s) := by
      intro g s
      rw [LinearEquiv.symm_apply_eq, he, e.apply_symm_apply]
    have hirr : F.range.toRepresentation.IsIrreducible := by
      rw [Representation.irreducible_iff_isSimpleModule_asModule]
      exact IsSimpleModule.congr
        (LinearEquiv.ofBijective (modMap e.symm.toLinearMap he') e.symm.bijective)
    have hle : F.range.toSubmodule ≤ irrSum ρ C :=
      le_iSup₂_of_le (f := fun (U : Subrepresentation ρ) (_ : U.toSubmodule ≤ C ∧
        U.toRepresentation.IsIrreducible ∧ GlobalTheory.PRep.IsAdmissible U.toRepresentation) =>
          U.toSubmodule) F.range ⟨by rintro _ ⟨t, rfl⟩; exact hf.1 t, hirr,
            isAdmissible_of_injective e.symm.toLinearMap he' e.symm.injective h2⟩ le_rfl
    exact hle ⟨s, rfl⟩
  · have : f s = 0 := DFunLike.congr_fun h0 s
    rw [this]
    exact Submodule.zero_mem _

theorem rank_homInto {σ : Representation ℂ H W} (ρ : Representation ℂ H X) (C : Submodule ℂ X)
    (h1 : σ.IsIrreducible) (h2 : GlobalTheory.PRep.IsAdmissible σ) :
    Module.rank ℂ (homInto σ ρ C) =
      Module.rank ℂ (σ.asModule →ₗ[MonoidAlgebra ℂ H] ↥(sSup (pieces ρ C))) := by
  refine LinearEquiv.rank_eq (LinearEquiv.ofBijective
    { toFun := fun f => (modMap f.1 f.2.2).codRestrict _
        (fun s => mem_sSup_pieces_of_mem (apply_mem_irrSum h1 h2 f.2 (σ.asModuleEquiv s)))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } ⟨fun a b hab => ?_, fun g => ?_⟩)
  · ext s
    exact congrArg Subtype.val (LinearMap.congr_fun hab (σ.asModuleEquiv.symm s))
  · refine ⟨⟨ρ.asModuleEquiv.toLinearMap ∘ₗ
      (((sSup (pieces ρ C)).subtype ∘ₗ g).restrictScalars ℂ) ∘ₗ σ.asModuleEquiv.symm.toLinearMap,
      fun s => mem_of_mem_sSup_pieces (g _).2, fun x s => ?_⟩, rfl⟩
    change ρ.asModuleEquiv (g (σ.asModuleEquiv.symm (σ x s))).1 =
      ρ x (ρ.asModuleEquiv (g (σ.asModuleEquiv.symm s)).1)
    rw [Representation.asModuleEquiv_symm_map_rho, map_smul, Submodule.coe_smul,
      Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]

theorem exists_rep {ρ : Representation ℂ H X} {C : Submodule ℂ X}
    (U : Submodule (MonoidAlgebra ℂ H) ↥(sSup (pieces ρ C)))
    (hU : IsSimpleModule (MonoidAlgebra ℂ H) U) :
    ∃ V : Subrepresentation ρ, V.toRepresentation.IsIrreducible ∧
      GlobalTheory.PRep.IsAdmissible V.toRepresentation ∧
      Nonempty (U ≃ₗ[MonoidAlgebra ℂ H] V.toRepresentation.asModule) := by
  let e := Submodule.equivMapOfInjective _ (sSup (pieces ρ C)).injective_subtype U
  haveI : IsSimpleModule (MonoidAlgebra ℂ H) (U.map (sSup (pieces ρ C)).subtype) :=
    IsSimpleModule.congr e.symm
  haveI : ∀ m : pieces ρ C, IsSimpleModule (MonoidAlgebra ℂ H) m :=
    fun m => simple_of_mem_pieces m.2
  obtain ⟨_, ⟨V, hV, rfl⟩, ⟨e'⟩⟩ := (U.map (sSup (pieces ρ C)).subtype).linearEquiv_of_le_sSup
    (pieces ρ C) (Submodule.map_subtype_le _ _)
  exact ⟨V, hV.2.1, hV.2.2, ⟨(e.trans e').trans (subEquiv V).symm⟩⟩

def killedEquiv {ρ : Representation ℂ H X} {C : Submodule ℂ X} (I : Set (MonoidAlgebra ℂ H))
    (hC : IsDecomp ρ C) (ho : ∀ x ∈ killed ρ I, IsOpen {g : H | ρ g x = x}) :
    (C ⊓ killed ρ I : Submodule ℂ X) ≃ₗ[ℂ]
      GlobalTheory.SemisimpleCount.killed I ↥(sSup (pieces ρ C)) where
  toFun x := ⟨⟨ρ.asModuleEquiv.symm x.1, mem_sSup_pieces_of_mem (hC _ x.2.1 (ho _ x.2.2))⟩,
    fun r hr => Subtype.ext (mem_killed.1 x.2.2 r hr)⟩
  invFun y := ⟨ρ.asModuleEquiv y.1.1, mem_of_mem_sSup_pieces y.1.2,
    mem_killed.2 fun r hr => congrArg Subtype.val (y.2 r hr)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [TopologicalSpace H] in
theorem killed_ne_bot {σ : Representation ℂ H W} {I : Set (MonoidAlgebra ℂ H)} {S : Type}
    [AddCommGroup S] [Module (MonoidAlgebra ℂ H) S]
    (e : S ≃ₗ[MonoidAlgebra ℂ H] σ.asModule) {s : S} (hs : s ≠ 0) (hI : ∀ x ∈ I, x • s = 0) :
    killed σ I ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  refine ⟨σ.asModuleEquiv (e s), mem_killed.2 fun r hr => ?_, by simpa using hs⟩
  rw [← Representation.asModuleEquiv_map_smul, ← map_smul, hI r hr, map_zero, map_zero]

theorem finrank_inf_killed_eq : ∀ (H : Type) [Group H] [TopologicalSpace H] (X Y : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (ρ : Representation ℂ H X) (ρ' : Representation ℂ H Y) (C : Submodule ℂ X) (C' : Submodule ℂ Y) (I : Set (MonoidAlgebra ℂ H)), IsDecomp ρ C → IsDecomp ρ' C' → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H W), σ.IsIrreducible → GlobalTheory.PRep.IsAdmissible σ → killed σ I ≠ ⊥ → Module.rank ℂ (homInto σ ρ C) = Module.rank ℂ (homInto σ ρ' C')) → (∀ x ∈ killed ρ I, IsOpen {g : H | ρ g x = x}) → (∀ y ∈ killed ρ' I, IsOpen {g : H | ρ' g y = y}) → FiniteDimensional ℂ (C ⊓ killed ρ I : Submodule ℂ X) → FiniteDimensional ℂ (C' ⊓ killed ρ' I : Submodule ℂ Y) → Module.finrank ℂ (C ⊓ killed ρ I : Submodule ℂ X) = Module.finrank ℂ (C' ⊓ killed ρ' I : Submodule ℂ Y) := by
  intro H _ _ X Y _ _ _ _ ρ ρ' C C' I hC hC' hm ho ho' f f'
  have e := killedEquiv I hC ho
  have e' := killedEquiv I hC' ho'
  rw [e.finrank_eq, e'.finrank_eq]
  refine GlobalTheory.SemisimpleCount.finrank_killed_eq (MonoidAlgebra ℂ H) _ _ I _ _
    (semisimple_sSup_pieces ρ C) (semisimple_sSup_pieces ρ' C') (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    e.finiteDimensional e'.finiteDimensional ?_ ?_
  · rintro U hU ⟨u, hu, h0, hI⟩
    obtain ⟨V, h1, h2, ⟨φ⟩⟩ := exists_rep U hU
    rw [GlobalTheory.SemisimpleCount.rank_hom_congr_left φ, GlobalTheory.SemisimpleCount.rank_hom_congr_left φ,
      ← rank_homInto ρ C h1 h2, ← rank_homInto ρ' C' h1 h2]
    exact hm _ _ h1 h2 (killed_ne_bot φ (s := ⟨u, hu⟩) (fun h => h0 (congrArg Subtype.val h))
      fun r hr => Subtype.ext (hI r hr))
  · rintro U hU ⟨u, hu, h0, hI⟩
    obtain ⟨V, h1, h2, ⟨φ⟩⟩ := exists_rep U hU
    rw [GlobalTheory.SemisimpleCount.rank_hom_congr_left φ, GlobalTheory.SemisimpleCount.rank_hom_congr_left φ,
      ← rank_homInto ρ C h1 h2, ← rank_homInto ρ' C' h1 h2]
    exact hm _ _ h1 h2 (killed_ne_bot φ (s := ⟨u, hu⟩) (fun h => h0 (congrArg Subtype.val h))
      fun r hr => Subtype.ext (hI r hr))

end GlobalTheory.RepCount

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSourceGlActionSymmetrisedSameSigns
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColLie

theorem fockS_eq_colDer_of_same_signs : ∀ {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (Y : Matrix (Fin a) (Fin a) ℂ),
    (∀ i j, ε' i = ε j) →
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ε ε' Y = (GlobalTheory.ColLie.colDer τ Y : Module.End ℂ (PolF D b a)) + (((b : ℂ) / 2) * Y.trace) • 1 := by
  intro D a b τ ε ε' Y h
  have hs : ∀ (i : Fin b) (j k : Fin a), GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO τ ε ε' i j * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO τ ε ε' i k =
      (LinearMap.mulLeft ℂ (MvPolynomial.X (τ, i, j) : PolF D b a) ∘ₗ
        (MvPolynomial.pderiv (τ, i, k)).toLinearMap : Module.End ℂ (PolF D b a)) := by
    intro i j k
    have hjk : ε j = ε k := (h i j).symm.trans (h i k)
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε j) * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε k) = 1 := by
      rw [hjk]; unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn; split_ifs <;> simp
    unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO
    rw [if_pos (h i j), if_pos (h i k), smul_mul_smul_comm, h1, one_smul]
    rfl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS GlobalTheory.ColLie.colDer
  simp only [hs, Finset.sum_add_distrib, smul_add, Finset.smul_sum]
  congr 1
  · rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin b)))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
  · simp only [smul_ite, smul_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Matrix.trace, Matrix.diag, Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
    congr 1
    ring

end GlobalTheory.ColLie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFineModuliAtComplexEmbeddingComplexBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFineModuliAtComplexEmbedding_complexBaseChange : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (F' : Fam ℂ O Λ g), IsBC F' F σ → FineAt F σ ρ N C → FineAt F' (RingHom.id ℂ) ρ N C := by
  first | exact @GlobalTheory.PELU.fineAt_of_isBC | exact GlobalTheory.PELU.fineAt_of_isBC | (intros; apply GlobalTheory.PELU.fineAt_of_isBC <;> assumption)
end

