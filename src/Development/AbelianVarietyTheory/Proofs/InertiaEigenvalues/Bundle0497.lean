module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftBlochKatoCocycleIffOrthogonalLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0344
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0458
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicValNatFactorialBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0464
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0462
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualBlochKatoLatticeDualOrthogonal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual

namespace GlobalTheory.ResOrth

theorem mem_of_mk_mem_span {k Z : Type} [CommRing k] [AddCommGroup Z] [Module k Z] {A B : Submodule k Z} (hB : B ≤ A)
    {S : Set (Z ⧸ B)} (hS : ∀ ξ ∈ S, ∃ z ∈ A, ξ = Submodule.Quotient.mk z) {x : Z}
    (hx : Submodule.Quotient.mk x ∈ Submodule.span k S) : x ∈ A := by
  have h1 : Submodule.span k S ≤ A.map B.mkQ := Submodule.span_le.2 fun ξ hξ => by
    obtain ⟨z, hz, rfl⟩ := hS ξ hξ
    exact ⟨z, hz, rfl⟩
  obtain ⟨z, hz, e⟩ := h1 hx
  have h2 : z - x ∈ B := (Submodule.Quotient.eq B).1 e
  simpa using A.sub_mem hz (hB h2)

section General

variable {Γ k M M' : Type} [Group Γ] [TopologicalSpace Γ] [CommRing k] [AddCommGroup M] [Module k M] [AddCommGroup M']
  [Module k M'] (χ : Γ → k) (ρ : Representation k Γ M) (ρ' : Representation k Γ M') (P : M →ₗ[k] M' →ₗ[k] k)

def leftPerp (y : Γ → M') : Submodule k (Γ → M) where
  carrier := {x | CupCob χ ρ' P x y}
  zero_mem' := ⟨0, IsLocallyConstant.const 0, fun g h => by simp⟩
  add_mem' := by
    rintro x x' ⟨f, hf, e⟩ ⟨f', hf', e'⟩
    refine ⟨f + f', hf.add hf', fun g h => ?_⟩
    simp only [Pi.add_apply, map_add (f := _), LinearMap.add_apply, e, e']
    ring
  smul_mem' := by
    rintro c x ⟨f, hf, e⟩
    refine ⟨fun g => c * f g, hf.comp _, fun g h => ?_⟩
    simp only [Pi.smul_apply, map_smul, LinearMap.smul_apply, e, smul_eq_mul]
    ring

def rightPerp (x : Γ → M) : Submodule k (Γ → M') where
  carrier := {y | CupCob χ ρ' P x y}
  zero_mem' := ⟨0, IsLocallyConstant.const 0, fun g h => by simp⟩
  add_mem' := by
    rintro y y' ⟨f, hf, e⟩ ⟨f', hf', e'⟩
    refine ⟨f + f', hf.add hf', fun g h => ?_⟩
    simp only [Pi.add_apply, map_add (f := _), e, e']
    ring
  smul_mem' := by
    rintro c y ⟨f, hf, e⟩
    refine ⟨fun g => c * f g, hf.comp _, fun g h => ?_⟩
    simp only [Pi.smul_apply, map_smul, e, smul_eq_mul]
    ring

variable [TopologicalSpace M] [DiscreteTopology M] [TopologicalSpace M'] [DiscreteTopology M']
  [ContinuousConstSMul k M] [ContinuousConstSMul k M']

variable {χ ρ ρ' P}

theorem cupCob_of_left_coboundary (hP : ∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y) {x : Γ → M} (hx : x ∈ B1 ρ)
    {y : Γ → M'} (hy : y ∈ Z1 ρ') : CupCob χ ρ' P x y := by
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hx
  refine ⟨fun g => P m (y g), ((IsLocallyConstant.iff_continuous _).2 hy.1).comp _, fun g h => ?_⟩
  simp only [hm, hy.2, map_sub, map_add (f := _), LinearMap.sub_apply, hP]
  ring

theorem cupCob_of_right_coboundary (hP : ∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y) (hρ' : ContAction ρ')
    {x : Γ → M} (hx : x ∈ Z1 ρ) {y : Γ → M'} (hy : y ∈ B1 ρ') : CupCob χ ρ' P x y := by
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hy
  have h1 : Continuous fun g => ρ' g m := hρ'.comp (f := fun g : Γ => (g, m)) (by fun_prop)
  refine ⟨fun g => -P (x g) (ρ' g m), (((IsLocallyConstant.iff_continuous _).2 hx.1).prodMk
    ((IsLocallyConstant.iff_continuous _).2 h1)).comp fun p => -P p.1 p.2, fun g h => ?_⟩
  simp only [hm, hx.2, map_sub, map_add (f := _), map_mul, LinearMap.add_apply, Module.End.mul_apply, hP]
  ring

theorem cupCob_of_span (hP : ∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y) (hρ' : ContAction ρ')
    {S : Set (H1 ρ)} {S' : Set (H1 ρ')} (p : Z1 ρ → Prop) (p' : Z1 ρ' → Prop)
    (hS : ∀ ξ ∈ S, ∃ z, p z ∧ ξ = Submodule.Quotient.mk z) (hS' : ∀ ξ ∈ S', ∃ z, p' z ∧ ξ = Submodule.Quotient.mk z)
    (h : ∀ z z', p z → p' z' → CupCob χ ρ' P z.1 z'.1) (x : Z1 ρ) (y : Z1 ρ')
    (hx : Submodule.Quotient.mk x ∈ Submodule.span k S) (hy : Submodule.Quotient.mk y ∈ Submodule.span k S') :
    CupCob χ ρ' P x.1 y.1 := by
  refine mem_of_mk_mem_span (A := (leftPerp χ ρ' P y.1).comap (Z1 ρ).subtype)
    (fun z hz => cupCob_of_left_coboundary hP hz y.2) (fun ξ hξ => ?_) hx
  obtain ⟨z, hz, rfl⟩ := hS ξ hξ
  refine ⟨z, ?_, rfl⟩
  refine mem_of_mk_mem_span (A := (rightPerp χ ρ' P z.1).comap (Z1 ρ').subtype)
    (fun z' hz' => cupCob_of_right_coboundary hP hρ' z.2 hz') (fun ξ' hξ' => ?_) hy
  obtain ⟨z', hz', rfl⟩ := hS' ξ' hξ'
  exact ⟨z', h z z' hz hz', rfl⟩

end General

section DVR

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem exists_residue_embedding {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ f : IsLocalRing.ResidueField O →ₗ[O] KmodO O, Function.Injective f ∧ ∀ a : O,
      f (IsLocalRing.residue O a) =
        Submodule.Quotient.mk ((algebraMap O (FractionRing O) ϖ)⁻¹ * algebraMap O (FractionRing O) a) := by
  have h0 : algebraMap O (FractionRing O) ϖ ≠ 0 := by simpa using hϖ.ne_zero
  let φ : O →ₗ[O] KmodO O := (Submodule.mkQ _).comp
    ((LinearMap.mulLeft O (algebraMap O (FractionRing O) ϖ)⁻¹).comp (Algebra.linearMap O (FractionRing O)))
  have hk : LinearMap.ker φ = IsLocalRing.maximalIdeal O := by
    ext a
    rw [LinearMap.mem_ker, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
    refine (Submodule.Quotient.mk_eq_zero _).trans ⟨?_, ?_⟩
    · rintro ⟨b, hb⟩
      refine ⟨b, IsFractionRing.injective O (FractionRing O) ?_⟩
      have hb' : algebraMap O (FractionRing O) b =
        (algebraMap O (FractionRing O) ϖ)⁻¹ * algebraMap O (FractionRing O) a := hb
      rw [map_mul, hb', mul_inv_cancel_left₀ h0]
    · rintro ⟨b, rfl⟩
      refine ⟨b, ?_⟩
      change algebraMap O (FractionRing O) b =
        (algebraMap O (FractionRing O) ϖ)⁻¹ * algebraMap O (FractionRing O) (ϖ * b)
      rw [map_mul, inv_mul_cancel_left₀ h0]
  exact ⟨(IsLocalRing.maximalIdeal O).liftQ φ hk.ge,
    LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ hk.le), fun a => rfl⟩

theorem kmod_torsion {l : ℕ} (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (b : KmodO O) :
    ∃ n : ℕ, l ^ n • b = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := O) a
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hy0 hϖ
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hl
  obtain ⟨c, hc⟩ := hn.dvd.trans (pow_dvd_pow_of_dvd hl n)
  refine ⟨n, ?_⟩
  rw [← Submodule.mkQ_apply, ← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨c * x, ?_⟩
  have h1 : algebraMap O (FractionRing O) y ≠ 0 := by simpa using hy0
  rw [Algebra.linearMap_apply, nsmul_eq_mul, Nat.cast_pow, ← map_natCast (algebraMap O (FractionRing O)), ← map_pow,
    hc, map_mul, map_mul]
  field_simp

end DVR

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {i : X.Tw}
  {K : Type} [Field K] [Algebra (X.O0 i) K]

theorem red_apply (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (g : GE N) (m : Fin D.R.r → K) :
    red i K ρ g m = ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (algebraMap (X.O0 i) K)).mulVec m := by
  funext a
  simp [repOn, matAct, Matrix.mulVec, dotProduct]

theorem red_dot (s : X.Sig i) {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)} (hρ : IsDual i s ρ) (g : GE N)
    (x y : Fin D.R.r → K) :
    red i K (Tgl i s) g x ⬝ᵥ red i K ρ g y = algebraMap (X.O0 i) K ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) * (x ⬝ᵥ y) := by
  have h3 : IsUnit (Tmat i s g).det := by
    rw [← Tgl_coe]; exact Matrix.isUnits_det_units _
  have e : (Tmat i s g).transpose * Tdual i s g = ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) • 1 := by
    rw [Tdual, Matrix.mul_smul, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ h3, Matrix.transpose_one]
  rw [red_apply, red_apply, hρ, Tgl_coe, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.transpose_map, ← Matrix.map_mul, e, Matrix.smul_one_eq_diagonal, Matrix.diagonal_map (map_zero _),
    ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]

theorem bkOn_orthogonal : LocalTateDuality → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ ρ, IsDual i s ρ → ∀ v ∈ placesOver D.host.E (X.l i), ∀ (x : Z1 ((red i K (Tgl i s)).comp (DecV N v).subtype)) (y : Z1 ((red i K ρ).comp (DecV N v).subtype)), Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K v → Submodule.Quotient.mk y ∈ bkOn bkP i ρ (1 : GE N →* Kˣ) K v → CupCob (fun g : DecV N v => algebraMap (X.O0 i) K ((eps0 X i g.1 : (X.O0 i)ˣ) : X.O0 i)) ((red i K ρ).comp (DecV N v).subtype) (dotProductBilin K K) x.1 y.1 := by
  intro hT D N X bkP i s hG K _ _ _ _ hK ρ hρ v hv x y hx hy
  have hloc : IsLocalHom (algebraMap (X.O0 i) K) := ⟨fun a ha => by
    by_contra hn
    exact ha.ne_zero (hK a hn)⟩
  have hc : ContAction (red i K ρ) := by
    refine GlobalTheory.PrimeToInertia.contAction_repOn (X.twistBaseCoefficientRing_isAdic i) ρ ?_ 1 (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ) fun b => ⟨1, fun x hx => ?_⟩
    · simp_rw [hρ _]; exact GlobalTheory.PrimeToInertia.continuous_Tdual i s
    · rw [pow_one, IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at hx
      rw [hx, zero_smul]
  rw [bkOn, dite_eq_left hv] at hx hy
  refine cupCob_of_span (ρ := (red i K (Tgl i s)).comp (DecV N v).subtype)
    (ρ' := (red i K ρ).comp (DecV N v).subtype) (P := dotProductBilin K K) (fun g a b => red_dot s hρ g.1 a b)
    (hc.comp (f := fun p : DecV N v × (Fin D.R.r → K) => ((p.1 : GE N), p.2)) (by fun_prop))
    (fun z => ∃ d b, IsFCoc bkP i v hv (Tgl i s) d ∧ ∀ g a, z.1 g a = algebraMap (X.O0 i) K (d g a) • b)
    (fun z => ∃ d b, IsFCoc bkP i v hv ρ d ∧ ∀ g a, z.1 g a = algebraMap (X.O0 i) K (d g a) • b) ?_ ?_ ?_ x y hx hy
  · rintro ξ ⟨z, c, d, b, h1, h2, h3, rfl⟩
    exact ⟨z, ⟨d, b, isFCoc_iff.2 ⟨c, h1, h2⟩, h3⟩, rfl⟩
  · rintro ξ ⟨z, c, d, b, h1, h2, h3, rfl⟩
    exact ⟨z, ⟨d, b, isFCoc_iff.2 ⟨c, h1, h2⟩, h3⟩, rfl⟩
  rintro z z' ⟨d, b, hd, e⟩ ⟨d', b', hd', e'⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.O0 i)
  have hopen : IsOpen ((IsLocalRing.maximalIdeal (X.O0 i) : Ideal (X.O0 i)) : Set (X.O0 i)) := by
    simpa using (isAdic_iff.1 (X.twistBaseCoefficientRing_isAdic i)).1 1
  have hlc : ∀ a, IsLocallyConstant fun g => IsLocalRing.residue (X.O0 i) (d' g a) := fun a => by
    have hca : Continuous fun g => d' g a := (continuous_apply a).comp hd'.continuous
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
    filter_upwards [(hopen.preimage (hca.sub (continuous_const (y := d' g a)))).mem_nhds (x := g) (by simp)] with h hh
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hh
  obtain ⟨f, hf, ef⟩ := (_root_.GlobalTheory.BKLatticeCochain.lift_iff_orthogonal D N X bkP i s hG ρ hρ v hv ϖ hϖ d' hlc (fun g h a => by
    rw [hd'.cocycle, hρ]; simp)).1 ⟨d', hd', fun g a => by simp⟩ d hd
  obtain ⟨ι, hι, eι⟩ := exists_residue_embedding hϖ
  have := X.twistBaseCoefficientRing_residueField_finite i
  obtain ⟨c, hc, ec⟩ := GlobalTheory.LocalH2Injective.h2_inj hT D.host.E N.Om (X.l i) _ v (N.plOm.2 v) (X.O0 i) _ _ ι hι
    (kmod_torsion (GlobalTheory.PrimeToInertia.l_mem i))
    (fun g h => IsLocalRing.residue (X.O0 i) (d g ⬝ᵥ (Tdual i s g.1).mulVec (d' h))) f hf
    (fun g h => (eι _).trans (ef g h))
  let π : IsLocalRing.ResidueField (X.O0 i) →+* K := IsLocalRing.ResidueField.lift (algebraMap (X.O0 i) K)
  have hπ : ∀ a, π (IsLocalRing.residue (X.O0 i) a) = algebraMap (X.O0 i) K a := fun a => rfl
  refine ⟨fun g => b * b' * π (c g), hc.comp fun t => b * b' * π t, fun g h => ?_⟩
  have e1 := congrArg π (ec g h)
  rw [hπ, map_add (f := _), map_sub, Algebra.smul_def, map_mul] at e1
  have e2 : π (algebraMap (X.O0 i) _ (algebraMap ℤ_[X.l i] (X.O0 i)
      ((cycZ D.host.E N.Om (X.l i) g.1 : ℤ_[X.l i]ˣ) : ℤ_[X.l i]))) =
      algebraMap (X.O0 i) K ((eps0 X i g.1 : (X.O0 i)ˣ) : X.O0 i) := rfl
  rw [e2] at e1
  have e3 : z.1 g ⬝ᵥ red i K ρ g.1 (z'.1 h) =
      b * b' * algebraMap (X.O0 i) K (d g ⬝ᵥ (Tdual i s g.1).mulVec (d' h)) := by
    rw [red_apply, hρ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, Matrix.mulVec, e, e', map_sum, map_mul, Matrix.map_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  refine e3.trans ?_
  rw [e1]
  ring

end GlobalTheory.ResOrth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomExtDense
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysEval

section Abstract

variable {B P R : Type} [CommRing B] [CommRing P] [CommRing R] (l : ℕ) (ι : B →+* P) (f : B →+* R)

def Approx (F : P) (r : ℕ) (y : R) : Prop :=
  ∃ (n : ℕ) (b : B) (p h : P), n ≠ 0 ∧ (n : P) * p = ι b ∧ F = p + (l : P) ^ r * h ∧ (n : R) * y = f b

variable {l ι f}

theorem approx_add {F G : P} {r : ℕ} {y z : R} (hF : Approx l ι f F r y) (hG : Approx l ι f G r z) :
    Approx l ι f (F + G) r (y + z) := by
  obtain ⟨n, b, p, h, hn, hp, hF, hy⟩ := hF
  obtain ⟨m, c, q, k, hm, hq, hG, hz⟩ := hG
  refine ⟨n * m, (m : B) * b + (n : B) * c, p + q, h + k, mul_ne_zero hn hm, ?_, ?_, ?_⟩
  · rw [map_add (f := _), map_mul, map_mul, map_natCast, map_natCast, ← hp, ← hq]; push_cast; ring
  · rw [hF, hG]; ring
  · rw [map_add (f := _), map_mul, map_mul, map_natCast, map_natCast, ← hy, ← hz]; push_cast; ring

theorem approx_mul {F G : P} {r : ℕ} {y z : R} (hF : Approx l ι f F r y) (hG : Approx l ι f G r z) :
    Approx l ι f (F * G) r (y * z) := by
  obtain ⟨n, b, p, h, hn, hp, hF, hy⟩ := hF
  obtain ⟨m, c, q, k, hm, hq, hG, hz⟩ := hG
  refine ⟨n * m, b * c, p * q, p * k + h * q + (l : P) ^ r * h * k, mul_ne_zero hn hm, ?_, ?_, ?_⟩
  · rw [map_mul, ← hp, ← hq]; push_cast; ring
  · rw [hF, hG]; ring
  · rw [map_mul, ← hy, ← hz]; push_cast; ring

theorem approx_ι (b : B) (r : ℕ) : Approx l ι f (ι b) r (f b) :=
  ⟨1, b, ι b, 0, one_ne_zero, by simp, by simp, by simp⟩

theorem approx_one (r : ℕ) : Approx l ι f 1 r 1 := by
  simpa using approx_ι (l := l) (ι := ι) (f := f) 1 r

theorem approx_zero (r : ℕ) : Approx l ι f 0 r 0 := by
  simpa using approx_ι (l := l) (ι := ι) (f := f) 0 r

variable (htf : ∀ (n : ℕ) (x : R), n ≠ 0 → (n : R) * x = 0 → x = 0)
  (hK : ∀ (n : ℕ) (b : B) (p : P), n ≠ 0 → (n : P) * p = ι b → ∃ y : R, (n : R) * y = f b) (hl0 : l ≠ 0)
include htf hK hl0

theorem approx_dvd {F : P} {r s : ℕ} (hrs : r ≤ s) {y z : R} (hy : Approx l ι f F r y)
    (hz : Approx l ι f F s z) : (l : R) ^ r ∣ y - z := by
  obtain ⟨n, b, p, h, hn, hp, hF, hy⟩ := hy
  obtain ⟨m, c, q, k, hm, hq, hF', hz⟩ := hz
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrs
  have h0 : p - q = (l : P) ^ r * ((l : P) ^ d * k - h) := by linear_combination hF' - hF
  have h1 : ((n * m * l ^ r : ℕ) : P) * ((l : P) ^ d * k - h) = ι ((m : B) * b - (n : B) * c) := by
    rw [map_sub, map_mul, map_mul, map_natCast, map_natCast, ← hp, ← hq]
    push_cast
    linear_combination ((n : P) * m) * h0.symm
  obtain ⟨w, hw⟩ := hK _ _ _ (mul_ne_zero (mul_ne_zero hn hm) (pow_ne_zero _ hl0)) h1
  refine ⟨w, (sub_eq_zero.1 (htf (n * m) _ (mul_ne_zero hn hm) ?_)).symm⟩
  rw [map_sub, map_mul, map_mul, map_natCast, map_natCast, ← hy, ← hz] at hw
  push_cast at hw ⊢
  linear_combination hw

variable [IsAdicComplete (Ideal.span {(l : R)}) R]
  (hD : ∀ (F : P) (r : ℕ), ∃ (n : ℕ) (b : B) (p h : P), n ≠ 0 ∧ (n : P) * p = ι b ∧ F = p + (l : P) ^ r * h)

omit htf hl0 in
include hD in
theorem exists_approx (F : P) (r : ℕ) : ∃ y, Approx l ι f F r y := by
  obtain ⟨n, b, p, h, hn, hp, hF⟩ := hD F r
  obtain ⟨y, hy⟩ := hK n b p hn hp
  exact ⟨y, n, b, p, h, hn, hp, hF, hy⟩


omit htf hK hl0 in
variable (l) in
theorem sep_l (x : R) (h : ∀ r : ℕ, (l : R) ^ r ∣ x) : x = 0 :=
  IsHausdorff.haus' (I := Ideal.span {(l : R)}) x fun n => by
    simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact h n

include hD in
theorem exists_lim (F : P) : ∃ L : R, ∀ r y, Approx l ι f F r y → (l : R) ^ r ∣ L - y := by
  choose y hy using exists_approx hK hD F
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(l : R)}) y (fun {m n} hmn => by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact approx_dvd htf hK hl0 hmn (hy m) (hy n))
  refine ⟨L, fun r z hz => ?_⟩
  have h1 := hL r
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
  have h2 := approx_dvd htf hK hl0 le_rfl (hy r) hz
  have e : L - z = (y r - z) - (y r - L) := by ring
  rw [e]
  exact dvd_sub h2 h1


include hD in
theorem exists_ringHom : ∃ E : P →+* R, ∀ F r y, Approx l ι f F r y → (l : R) ^ r ∣ E F - y := by
  choose L hL using exists_lim htf hK hl0 hD
  have key : ∀ F z, (∀ r, ∃ y, Approx l ι f F r y ∧ (l : R) ^ r ∣ z - y) → L F = z := fun F z hz =>
    sub_eq_zero.1 (sep_l l _ fun r => by
      obtain ⟨y, hy, hzy⟩ := hz r
      have e : L F - z = (L F - y) - (z - y) := by ring
      rw [e]
      exact dvd_sub (hL F r y hy) hzy)
  have h1 : L 1 = 1 := key 1 1 fun r => ⟨1, approx_one r, by simp⟩
  have h0 : L 0 = 0 := key 0 0 fun r => ⟨0, approx_zero r, by simp⟩
  have hm : ∀ F G, L (F * G) = L F * L G := by
    intro F G
    refine key _ _ fun r => ?_
    obtain ⟨y, hy⟩ := exists_approx hK hD F r
    obtain ⟨z, hz⟩ := exists_approx hK hD G r
    obtain ⟨c, hc⟩ := hL F r y hy
    obtain ⟨d, hd⟩ := hL G r z hz
    exact ⟨y * z, approx_mul hy hz, c * z + y * d + (l : R) ^ r * c * d, by
      linear_combination (L G) * hc + (y + (l : R) ^ r * c) * hd⟩
  have ha : ∀ F G, L (F + G) = L F + L G := by
    intro F G
    refine key _ _ fun r => ?_
    obtain ⟨y, hy⟩ := exists_approx hK hD F r
    obtain ⟨z, hz⟩ := exists_approx hK hD G r
    obtain ⟨c, hc⟩ := hL F r y hy
    obtain ⟨d, hd⟩ := hL G r z hz
    exact ⟨y + z, approx_add hy hz, c + d, by linear_combination hc + hd⟩
  exact ⟨{ toFun := L, map_one' := h1, map_zero' := h0, map_mul' := hm, map_add' := ha }, hL⟩


omit hK in
include hD in
theorem ringHom_ext_dense (G₁ G₂ : P →+* R) (h : ∀ b, G₁ (ι b) = G₂ (ι b)) : G₁ = G₂ := by
  ext F
  refine sub_eq_zero.1 (sep_l l _ fun r => ?_)
  obtain ⟨n, b, p, k, hn, hp, hF⟩ := hD F r
  have e1 : (n : R) * (G₁ p - G₂ p) = G₁ ((n : P) * p) - G₂ ((n : P) * p) := by
    rw [map_mul, map_mul, map_natCast, map_natCast]; ring
  have h1 : G₁ p = G₂ p := sub_eq_zero.1 (htf n _ hn (by rw [e1, hp, h, sub_self]))
  exact ⟨G₁ k - G₂ k, by rw [hF, map_add (f := _), map_add (f := _), map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, h1]; ring⟩

end Abstract

section Concrete

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [Algebra O K] (t : Wq l a →ₐ[ℤ_[l]] O)


variable (K) in
def embK (τ : ZMod a) : Wq l a →+* K := (algebraMap O K).comp (emb t τ).toRingHom


variable (l a) in
abbrev Bp : Type := Polynomial (Polynomial (Wq l a))


variable (K) in
def rhoK (τ : ZMod a) : Polynomial (Wq l a) →+* K⟦X⟧ :=
  (PowerSeries.map (embK K t τ)).comp Polynomial.coeToPowerSeries.ringHom


variable (K) in
def iotaP : Bp l a →+* (ZMod a → K⟦X⟧⟦X⟧) :=
  Pi.ringHom fun τ => (PowerSeries.map (rhoK K t τ)).comp Polynomial.coeToPowerSeries.ringHom

theorem coeff_iotaP (b : Bp l a) (τ : ZMod a) (i n : ℕ) :
    coeff n (coeff i (iotaP K t b τ)) = embK K t τ ((b.coeff i).coeff n) := by
  rw [show iotaP K t b τ = PowerSeries.map (rhoK K t τ) (b : (Polynomial (Wq l a))⟦X⟧) from rfl, coeff_map,
    Polynomial.coeff_coe, rhoK, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, coeff_map,
    Polynomial.coeff_coe]

theorem rhoK_eq_toAc [IsUltrametricDist K] [IsUnitBall O K] (q : Polynomial (Wq l a)) (τ : ZMod a) :
    rhoK K t τ q = (toAc t K (q : (Wq l a)⟦X⟧) τ : K⟦X⟧) := by
  ext n
  rw [coeff_toAc]
  simp [rhoK, embK, coeff_map, Polynomial.coeff_coe]

theorem charZero_K [NormedAlgebra ℚ_[l] K] : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective

theorem embK_injective [NormedAlgebra ℚ_[l] K] (τ : ZMod a) : Function.Injective (embK K t τ) := by
  have := charZero_K (l := l) (K := K)
  refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
  by_contra h0
  obtain ⟨m, v, hv, rfl⟩ := WittVector.exists_eq_pow_p_mul w h0
  have hu : IsUnit v := WittVector.isUnit_of_coeff_zero_ne_zero v hv
  rw [map_mul, map_pow, map_natCast] at hw
  exact mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero)) (hu.map _).ne_zero hw


include t in
theorem wq_nat_cancel [NormedAlgebra ℚ_[l] K] {n : ℕ} (hn : n ≠ 0) {x : Wq l a}
    (h : (n : Wq l a) * x = 0) : x = 0 := by
  have := charZero_K (l := l) (K := K)
  refine embK_injective (K := K) t 0 ?_
  have h1 := congrArg (embK K t 0) h
  rw [map_mul, map_natCast, map_zero] at h1
  rw [map_zero]
  exact (mul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 hn)

variable {e : ℕ} (ϖ : PiSys l e)

theorem ev_coe (q : Polynomial (Wq l a)) :
    ϖ.ev a (q : (Wq l a)⟦X⟧) = q.eval₂ (wA l a).toRingHom ϖ.teich := by
  have h := Polynomial.ringHom_ext (f := (ϖ.ev a).comp Polynomial.coeToPowerSeries.ringHom)
    (g := Polynomial.eval₂RingHom (wA l a).toRingHom ϖ.teich) (fun w => by simp) (by simp)
  exact RingHom.congr_fun h q


variable (a) in
def evC : Polynomial (Wq l a) →+* Per.Acris l :=
  ((ainfToAcris l).toRingHom.comp (ϖ.ev a)).comp Polynomial.coeToPowerSeries.ringHom


variable (a) in
def fP (g : GQ l) : Bp l a →+* Per.Acris l :=
  Polynomial.eval₂RingHom (evC a ϖ) (ainfToAcris l (ϖ.mu g * ϖ.teich))

end Concrete

end GlobalTheory.CrysEval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepresentationDensityOfIsInternalConstituentStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_representation_density_of_isInternal_constituents : ∀ {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K Γ V) (ι : Type) [Fintype ι] [DecidableEq ι] (Vs : ι → Submodule K V) (hs : ∀ j, Stable ρ (Vs j)), DirectSum.IsInternal Vs → (∀ j, Submodule.span K (Set.range fun g => (ρ g).restrict (hs j g)) = ⊤) → (∀ j j', j ≠ j' → ∀ e : Vs j ≃ₗ[K] Vs j', ¬ ∀ g v, e ((ρ g).restrict (hs j g) v) = (ρ g).restrict (hs j' g) (e v)) → ∀ f : V →ₗ[K] V, (∀ j, ∀ v ∈ Vs j, f v ∈ Vs j) → f ∈ Submodule.span K (Set.range ρ) := by
  first | exact @GlobalTheory.BlockDensity.density | exact GlobalTheory.BlockDensity.density | (intros; apply GlobalTheory.BlockDensity.density <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimePlaceCmTypeConjugateStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPrime_place_cmType_conjugate : ∀ (D : D7) (i : D.nd.Loc), SplitRowPrime D.host (D.nd.l i) → ∀ (w w' : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (hw' : w' ∈ placesOver D.host.E (D.nd.l i)), IsConjPl D.host w w' → (PlIn (N := D.nd) D.nbr i true w hw ∧ PlIn (N := D.nd) D.nbr i false w' hw') ∨ (PlIn (N := D.nd) D.nbr i false w hw ∧ PlIn (N := D.nd) D.nbr i true w' hw') := by
  first | exact @GlobalTheory.SplitType.place_type_conj | exact GlobalTheory.SplitType.place_type_conj | (intros; apply GlobalTheory.SplitType.place_type_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameSettingGroupActionCompatStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_setting_group_action_compat : ∀ {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {G : Type} [Group G] [TopologicalSpace G] {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] {P₀ : PhiMod O K l e a ι} {P₁ : PhiMod O K l e a κ} {P₂ : PhiMod O K l e a μ} {T₀ T₁ T₂ : LocLat G ℚ_[l] K O} {I₀ : Ident t ϖ P₀ T₀} {I₁ : Ident t ϖ P₁ T₁} {I₂ : Ident t ϖ P₂ T₂} {f : LatHom T₀.L T₁.L} {g : LatHom T₁.L T₂.L} {F : GlobalTheory.BK.Hom P₀ P₁} {H : GlobalTheory.BK.Hom P₁ P₂} (hS : IsSESLat (Qp := ℚ_[l]) f g) (hF : IsMapOf I₀ I₁ f F) (hH : IsMapOf I₁ I₂ g H), ∀ v : κ → OW l O, homW t ϖ H v = 0 → ∃ w, homW t ϖ F w = v := by
  first | exact @GlobalTheory.BKReal.SESExact.homW_exact_middle | exact GlobalTheory.BKReal.SESExact.homW_exact_middle | (intros; apply GlobalTheory.BKReal.SESExact.homW_exact_middle <;> assumption)
end

