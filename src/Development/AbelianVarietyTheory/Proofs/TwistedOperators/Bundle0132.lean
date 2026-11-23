module

public import Mathlib
public import ReciprocityTheory.Automorphisms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0115
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0091

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DegreeOnePrimeReductionSplitPlaceDictionary
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaceRed

section Gen

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

theorem mem_max_iff (a : v.adicCompletionIntegers F) :
    IsLocalRing.residue (v.adicCompletionIntegers F) a = 0 ↔ Valued.v (a : v.adicCompletion F) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff]
  exact Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) _))

theorem exists_red {A : Type} [CommRing A] (I : Ideal A) (ψ : A →+* v.adicCompletionIntegers F)
    (hI : ∀ x, x ∈ I ↔ Valued.v (ψ x : v.adicCompletion F) < 1)
    (hs : ∀ a : v.adicCompletionIntegers F, ∃ x, Valued.v ((a : v.adicCompletion F) - ψ x) < 1) :
    ∃ r : v.adicCompletionIntegers F →+* A ⧸ I, (∀ x, r (ψ x) = Ideal.Quotient.mk I x) ∧
      ∀ a, r a = 0 ↔ Valued.v (a : v.adicCompletion F) < 1 := by
  let q := Ideal.Quotient.lift I ((IsLocalRing.residue _).comp ψ)
    (fun x hx => (mem_max_iff _).2 ((hI x).1 hx))
  have hq : Function.Bijective q := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact Ideal.Quotient.eq_zero_iff_mem.2 ((hI x).2 ((mem_max_iff _).1 hy))
    · intro y
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨x, hx⟩ := hs a
      refine ⟨Ideal.Quotient.mk I x, ?_⟩
      show IsLocalRing.residue _ (ψ x) = _
      rw [eq_comm, ← sub_eq_zero, ← map_sub, mem_max_iff]
      exact hx
  let e := RingEquiv.ofBijective q hq
  refine ⟨(e.symm : _ →+* A ⧸ I).comp (IsLocalRing.residue _), fun x => ?_, fun a => ?_⟩
  · show e.symm _ = _
    rw [RingEquiv.symm_apply_eq]
    rfl
  · show e.symm _ = 0 ↔ _
    rw [map_eq_zero_iff _ e.symm.injective, mem_max_iff]

theorem exists_unitPart : ∃ t : (v.adicCompletion F)ˣ →* v.adicCompletionIntegers F,
    ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → (t u : v.adicCompletion F) = u := by
  obtain ⟨p, hp⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-1))
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  have hne : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) ≠ 0 := fun u =>
    (Valuation.ne_zero_iff _).2 u.ne_zero
  have hv : ∀ u : (v.adicCompletion F)ˣ,
      Valued.v ((u : v.adicCompletion F) * p ^ (WithZero.log (Valued.v (u : v.adicCompletion F)))) = 1 := by
    intro u
    rw [map_mul, map_zpow₀, hp, ← WithZero.exp_zsmul]
    conv_lhs => lhs; rw [← WithZero.exp_log (hne u)]
    rw [← WithZero.exp_add]
    simp
  refine ⟨⟨⟨fun u => ⟨(u : v.adicCompletion F) * p ^ (WithZero.log (Valued.v (u : v.adicCompletion F))),
    (hv u).le⟩, ?_⟩, ?_⟩, ?_⟩
  · apply Subtype.ext
    simp
  · intro a b
    apply Subtype.ext
    show ((a * b : (v.adicCompletion F)ˣ) : v.adicCompletion F) * p ^ _ = (_ * p ^ _) * (_ * p ^ _)
    rw [Units.val_mul, map_mul, WithZero.log_mul (hne a) (hne b), zpow_add₀ hp0]
    ring
  · intro u hu
    show (u : v.adicCompletion F) * p ^ _ = _
    rw [hu]
    simp

end Gen

variable {D : D7} {v : FinPl D} (φ : SplitProj D v)

def rdQh : D.host.E →+* Fv D.host.F v :=
  φ.toRingHom.comp (Algebra.TensorProduct.includeRight (R := D.host.F) (A := Fv D.host.F v) (B := D.host.E)).toRingHom

theorem rdQh_apply (x : D.host.E) : rdQh φ x = rdQ φ x := rfl

theorem rdQ_int (x : 𝓞 D.host.E) : rdQ φ (x : D.host.E) ∈ v.adicCompletionIntegers D.host.F := by
  obtain ⟨p, hm, hp⟩ : IsIntegral ℤ (x : D.host.E) := x.2
  refine ReciprocityTheory.Aut.adic_le_one_of_poly v p hm ?_
  have := congrArg (rdQh φ) hp
  rw [Polynomial.hom_eval₂, map_zero, RingHom.ext_int ((rdQh φ).comp _) (Int.castRingHom _)] at this
  exact this

theorem rdQ_alg (y : D.host.F) :
    rdQ φ (algebraMap D.host.F D.host.E y) = algebraMap D.host.F (Fv D.host.F v) y := by
  show φ ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Fv D.host.F v) (B := D.host.E))
    (algebraMap D.host.F D.host.E y)) = _
  rw [AlgHom.commutes]
  exact φ.commutes (algebraMap D.host.F (Fv D.host.F v) y)

def rdO : 𝓞 D.host.E →+* v.adicCompletionIntegers D.host.F :=
  ((rdQh φ).comp (algebraMap (𝓞 D.host.E) D.host.E)).codRestrict (v.adicCompletionIntegers D.host.F) (rdQ_int φ)

theorem rdO_coe (x : 𝓞 D.host.E) : (rdO φ x : Fv D.host.F v) = rdQ φ (x : D.host.E) := rfl

theorem rdO_dense (a : v.adicCompletionIntegers D.host.F) :
    ∃ x, Valued.v ((a : Fv D.host.F v) - rdO φ x) < 1 := by
  obtain ⟨y, hy⟩ := ReciprocityTheory.Aut.adic_exists_approx v (a : Fv D.host.F v) a.2
  refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y, ?_⟩
  have h1 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F D.host.E (algebraMap (𝓞 D.host.F) D.host.F y) := by
    show algebraMap (𝓞 D.host.E) D.host.E _ = _
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [rdO_coe, h1, rdQ_alg]
  exact hy

theorem rdE_tmul (x : D.host.E) (y : Af D.host.F) :
    rdE φ (x ⊗ₜ[D.host.F] y) = φ (y v ⊗ₜ[D.host.F] x) := rfl

theorem rdE_int (N : EAf D) (hN : N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    rdE φ N ∈ v.adicCompletionIntegers D.host.F := by
  have hle : Formalism.L2.Herm.intAf D.host.F D.host.E ≤
      (v.adicCompletionIntegers D.host.F).toSubring.comap (rdE φ) := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨b, rfl⟩ | ⟨y, rfl⟩)
    · obtain ⟨b0, hb0⟩ := b.2
      show rdE φ ((b : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) ∈ v.adicCompletionIntegers D.host.F
      rw [← hb0]
      exact rdQ_int φ b0
    · show rdE φ ((1 : D.host.E) ⊗ₜ[D.host.F] (y : Af D.host.F)) ∈ v.adicCompletionIntegers D.host.F
      rw [rdE_tmul]
      have : φ ((y : Af D.host.F) v ⊗ₜ[D.host.F] (1 : D.host.E)) = (y : Af D.host.F) v := φ.commutes _
      rw [this]
      exact y.2 v
  exact hle hN

def rdS : Formalism.L2.Herm.intAf D.host.F D.host.E →+* v.adicCompletionIntegers D.host.F :=
  ((rdE φ).comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).codRestrict (v.adicCompletionIntegers D.host.F)
    (fun N => rdE_int φ N.1 N.2)

theorem rdS_oToS (x : 𝓞 D.host.E) : rdS φ (Formalism.L2.DIV.oToS D.host.F D.host.E x) = rdO φ x := rfl

theorem eq_resS {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (PP : Formalism.L2.DIV.Pl E) (g : Formalism.L2.Herm.intAf F E →+* Formalism.L2.DIV.kP PP)
    (hg : ∀ x, g (Formalism.L2.DIV.oToS F E x) = Ideal.Quotient.mk PP.asIdeal x) (N : Formalism.L2.Herm.intAf F E) :
    g N = Formalism.L2.DIV.resS F PP N := by
  have key : ∀ g' : Formalism.L2.Herm.intAf F E →+* Formalism.L2.DIV.kP PP,
      (∀ x, g' (Formalism.L2.DIV.oToS F E x) = Ideal.Quotient.mk PP.asIdeal x) →
      Formalism.L2.DIV.idS F PP.asIdeal ≤ RingHom.ker g' := by
    intro g' hg'
    refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, hg']
    exact Ideal.Quotient.eq_zero_iff_mem.2 hx
  obtain ⟨q, hq⟩ := Formalism.L2.DIV.cmpS_surj (F := F) PP.asIdeal PP.ne_bot (Ideal.Quotient.mk _ N)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hm : Formalism.L2.DIV.oToS F E b - N ∈ Formalism.L2.DIV.idS F PP.asIdeal := Ideal.Quotient.eq.1 hq
  have h1 := key g hg hm
  have h2 := key _ (Formalism.L2.DIV.resS_oToS (F := F) PP) hm
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h1 h2
  rw [← h1, ← h2, hg, Formalism.L2.DIV.resS_oToS]

theorem red_dict : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E), IsProjAt φ PP → (∃ r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP, Function.Surjective r ∧ (∀ a : v.adicCompletionIntegers D.host.F, r a = 0 ↔ Valued.v (a : Fv D.host.F v) < 1) ∧ (∀ (a : Fv D.host.F v) (b : Formalism.L2.DIV.kP PP), RedRel φ PP a b ↔ ∃ h : a ∈ v.adicCompletionIntegers D.host.F, r ⟨a, h⟩ = b) ∧ ∀ (N : EAf D) (hN : N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), ∃ h : rdE φ N ∈ v.adicCompletionIntegers D.host.F, r ⟨rdE φ N, h⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨N, hN⟩) ∧ ∀ ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ, ∃ mu : (Fv D.host.F v)ˣ →* ℂˣ, LiftsChar φ PP mu ξ := by
  intro D v φ PP hP
  obtain ⟨r, hr, hr0⟩ := exists_red PP.asIdeal (rdO φ) hP (rdO_dense φ)
  have hrel : ∀ (a : Fv D.host.F v) (b : Formalism.L2.DIV.kP PP),
      RedRel φ PP a b ↔ ∃ h : a ∈ v.adicCompletionIntegers D.host.F, r ⟨a, h⟩ = b := by
    intro a b
    constructor
    · rintro ⟨x, rfl, hx⟩
      have ha : a ∈ v.adicCompletionIntegers D.host.F := by
        have e : a = (a - rdQ φ (x : D.host.E)) + rdQ φ (x : D.host.E) := by ring
        rw [e]
        exact add_mem ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx.le) (rdQ_int φ x)
      refine ⟨ha, ?_⟩
      rw [← hr, ← sub_eq_zero, ← map_sub, hr0]
      exact hx
    · rintro ⟨h, rfl⟩
      obtain ⟨x, hx⟩ := rdO_dense φ ⟨a, h⟩
      refine ⟨x, ?_, hx⟩
      rw [← hr, eq_comm, ← sub_eq_zero, ← map_sub, hr0]
      exact hx
  refine ⟨⟨r, fun b => ?_, hr0, hrel, fun N hN => ⟨rdE_int φ N hN, ?_⟩⟩, fun ξ => ?_⟩
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨_, hr x⟩
  · exact eq_resS PP (r.comp (rdS φ)) (fun x => hr x) ⟨N, hN⟩
  · obtain ⟨t, ht⟩ := exists_unitPart (F := D.host.F) (v := v)
    refine ⟨ξ.comp (r.toMonoidHom.comp t).toHomUnits, fun u k huk => ?_⟩
    obtain ⟨h, hk⟩ := (hrel _ _).1 huk
    have hu : Valued.v (u : Fv D.host.F v) = 1 := by
      refine le_antisymm h (not_lt.1 fun hlt => ?_)
      have h0 : (k : Formalism.L2.DIV.kP PP) = 0 := hk ▸ (hr0 ⟨_, h⟩).2 hlt
      have : Nontrivial (Formalism.L2.DIV.kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
      exact k.ne_zero h0
    show ξ _ = ξ k
    congr 1
    apply Units.ext
    show r (t u) = k
    rw [← hk]
    congr 1
    exact Subtype.ext (ht u hu)

end GlobalTheory.PlaceRed

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqSumWeilComponentsAddTwoSmulLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor.CompDecomp

open Filter Topology

theorem tendsto_one_sub_sum (F : Type) [Field F] [NumberField F] :
    Tendsto (fun Q : Finset (HeightOneSpectrum (𝓞 F)) => (1 : Af F) - ∑ v ∈ Q, singleV F v 1) atTop (𝓝 0) := by
  classical
  let A : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F) :=
    fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  let y : Finset (HeightOneSpectrum (𝓞 F)) → (∀ v, A v) := fun Q v =>
    ⟨if v ∈ Q then 0 else 1, by
      by_cases h : v ∈ Q
      · rw [if_pos h]; exact (v.adicCompletionIntegers F).zero_mem
      · rw [if_neg h]; exact (v.adicCompletionIntegers F).one_mem⟩
  let z : ∀ v, A v := fun v => ⟨0, (v.adicCompletionIntegers F).zero_mem⟩
  have hy : Tendsto y atTop (𝓝 z) := by
    rw [tendsto_pi_nhds]
    intro v
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [Filter.eventually_ge_atTop {v}] with Q hQ
    have hv : v ∈ Q := Finset.singleton_subset_iff.mp hQ
    apply Subtype.ext
    show (if v ∈ Q then (0 : v.adicCompletion F) else 1) = 0
    rw [if_pos hv]
  have hc : Continuous (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      A Filter.cofinite) := RestrictedProduct.isEmbedding_structureMap.continuous
  have key : ∀ Q, (1 : Af F) - ∑ v ∈ Q, singleV F v 1 =
      RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) A Filter.cofinite (y Q) := by
    intro Q
    apply FiniteAdeleRing.ext
    intro w
    have hw : ((1 : Af F) - ∑ v ∈ Q, singleV F v 1) w = evalV F w ((1 : Af F) - ∑ v ∈ Q, singleV F v 1) := rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hw, map_sub, map_one, map_sum]
    show _ = (if w ∈ Q then (0 : w.adicCompletion F) else 1)
    by_cases h : w ∈ Q
    · rw [Finset.sum_eq_single_of_mem w h (fun b _ hb => GlobalTheory.LatVac.evalV_singleV_ne F b w (Ne.symm hb)),
        GlobalTheory.LatVac.evalV_singleV_same, if_pos h, sub_self]
    · rw [Finset.sum_eq_zero (fun b hb => GlobalTheory.LatVac.evalV_singleV_ne F b w (by rintro rfl; exact h hb)),
        if_neg h, sub_zero]
  have h0 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) A
      Filter.cofinite z = (0 : Af F) :=
    by
      apply FiniteAdeleRing.ext
      intro w
      rfl
  have h1 : Tendsto (fun Q => (1 : Af F) - ∑ v ∈ Q, singleV F v 1) atTop
      (𝓝 (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) A
        Filter.cofinite z)) :=
    ((hc.tendsto z).comp hy).congr (fun Q => (key Q).symm)
  rw [h0] at h1
  exact h1

variable {D : D7}

private theorem infComponent_algebraMap_pairA {D : D7} (a : Ainf D.host.F) (b : Af D.host.F) :
    infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F a b)) = a ⊗ₜ[D.host.F] (1 : D.host.E) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rfl

private theorem sum_sgW_plTau_eq_one (D : D7) :
    ∑ τ : D.what₂.Tau, GlobalTheory.AutFunCompare.sgW (plTau D τ) 1 = (1 : Ainf D.host.F) := by
  classical
  have hb := (GlobalTheory.CMTypePlaces.places_bijective D).sum_comp
    (fun w : InfinitePlace D.host.F => GlobalTheory.AutFunCompare.sgW w (1 : w.Completion))
  have h : ∑ w : InfinitePlace D.host.F, GlobalTheory.AutFunCompare.sgW w (1 : w.Completion) = (1 : Ainf D.host.F) := by
    have h' := Finset.univ_sum_single (1 : ∀ w : InfinitePlace D.host.F, w.Completion)
    simp only [Pi.one_apply] at h'
    simp only [GlobalTheory.AutFunCompare.sgW]
    exact h'
  exact hb.trans h

private theorem af_ext_of_fstA_sndA {F : Type} [Field F] [NumberField F] {x y : AF F}
    (h1 : fstA F x = fstA F y) (h2 : sndA F x = sndA F y) : x = y :=
  Prod.ext h1 h2

private theorem fstA_pairA_twisted_operators {F : Type} [Field F] [NumberField F] (a : Ainf F) (b : Af F) :
    fstA F (pairA F a b) = a := rfl

private theorem sndA_pairA_twisted_operators {F : Type} [Field F] [NumberField F] (a : Ainf F) (b : Af F) :
    sndA F (pairA F a b) = b := rfl

theorem one_sub_sum_idem (P : Finset (Place D)) (hP : P.toRight = Finset.univ) :
    1 - ∑ p ∈ P, idem D p = algebraMap (AF D.host.F) (AE D)
      (pairA D.host.F 0 (1 - ∑ v ∈ P.toLeft, singleV D.host.F v 1)) := by
  rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight, hP]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show (1 : AE D) - (∑ v ∈ P.toLeft, idem D (.inl v) + ∑ τ : D.what₂.Tau, idem D (.inr τ)) =
      algebraMap (AF D.host.F) (AE D) (1 - (∑ v ∈ P.toLeft, pairA D.host.F 0 (singleV D.host.F v 1) +
        ∑ τ : D.what₂.Tau, pairA D.host.F (GlobalTheory.AutFunCompare.sgW (plTau D τ) 1) 0)) by
    rw [map_sub, map_add (f := _), map_one, map_sum, map_sum]
    rfl]
  congr 1
  apply af_ext_of_fstA_sndA
  set_option synthInstance.maxHeartbeats 100000 in
    · simp [fstA_pairA_twisted_operators, map_sum, sum_sgW_plTau_eq_one D]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp [sndA_pairA_twisted_operators, map_sum]

theorem exists_eq_sum_wAt_add_two_smul : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ w : WO S T, ∃ P₀ : Finset (Place D), ∀ P : Finset (Place D), P₀ ⊆ P → ∃ u ∈ (latO S T ΛS ΛT fun _ => True), w = ∑ p ∈ P, wAt p w + 2 • u := by
  intro D S T ΛS ΛT hS hT w
  classical
  have hU := GlobalTheory.LatOpen.isOpen_nsmul_latO D S T ΛS ΛT hS hT 2 two_pos
  let g : Af D.host.F → WO S T := fun e => algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 e) • w
  have hg : Continuous g := by
    have h1 : Continuous fun e : Af D.host.F => pairA D.host.F 0 e :=
      (continuous_const.prodMk continuous_id : Continuous fun e : Af D.host.F => ((0 : Ainf D.host.F), e))
    have h2 : Continuous (algebraMap (AF D.host.F) (AE D)) := by
      have hs : (algebraMap (AF D.host.F) (AE D) : AF D.host.F → AE D) = fun r => r • (1 : AE D) := by
        funext r
        exact Algebra.algebraMap_eq_smul_one r
      rw [hs]
      exact Continuous.smul (f := fun r : AF D.host.F => r) (g := fun _ : AF D.host.F => (1 : AE D))
        continuous_id continuous_const
    exact (h2.comp h1).smul continuous_const
  have hg0 : g 0 = 0 := by
    show algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 0) • w = 0
    rw [show pairA D.host.F 0 0 = 0 from rfl, map_zero, zero_smul]
  have hlim : Tendsto (fun Q => g (1 - ∑ v ∈ Q, singleV D.host.F v 1)) atTop (𝓝 0) := by
    have h := (hg.tendsto 0).comp (tendsto_one_sub_sum D.host.F)
    rw [hg0] at h
    exact h
  have hmem : (0 : WO S T) ∈ {x : WO S T | ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E))
      (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), (x - (2 : ℕ) • l).map (finPart D) = 0} := by
    simp only [Set.mem_ofPred_eq]
    refine ⟨0, zero_mem _, ?_⟩
    simp
  obtain ⟨Q₀, hQ₀⟩ := Filter.eventually_atTop.1 (hlim.eventually_mem (hU.mem_nhds hmem))
  refine ⟨Q₀.disjSum Finset.univ, fun P hP => ?_⟩
  have hR : P.toRight = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro τ
    rw [Finset.mem_toRight]
    exact hP (Finset.inr_mem_disjSum.2 (Finset.mem_univ τ))
  have hL : Q₀ ⊆ P.toLeft := by
    intro v hv
    rw [Finset.mem_toLeft]
    exact hP (Finset.inl_mem_disjSum.2 hv)
  obtain ⟨l, hl, hfin⟩ := hQ₀ _ hL
  refine ⟨l, hl, ?_⟩
  have hrest : w - ∑ p ∈ P, wAt p w = g (1 - ∑ v ∈ P.toLeft, singleV D.host.F v 1) := by
    show w - ∑ p ∈ P, wAt p w =
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (1 - ∑ v ∈ P.toLeft, singleV D.host.F v 1)) • w
    rw [← one_sub_sum_idem P hR, sub_smul, one_smul, Finset.sum_smul]
    congr 1
  have hl0 := GlobalTheory.SplitScalar.latO_fin hl
  have h2l : g (1 - ∑ v ∈ P.toLeft, singleV D.host.F v 1) = (2 : ℕ) • l := by
    ext i j
    apply GlobalTheory.SplitScalar.adele_ext
    · have hij := congrFun (congrFun hl0 i) j
      simp only [Matrix.map_apply, Matrix.zero_apply] at hij
      show infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (1 - ∑ v ∈ P.toLeft, singleV D.host.F v 1))
        * w i j) = infPart D ((2 : ℕ) • l i j)
      rw [map_mul, infComponent_algebraMap_pairA, TensorProduct.zero_tmul, zero_mul, map_nsmul, hij, smul_zero]
    · have hij := congrFun (congrFun hfin i) j
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.sub_apply, map_sub] at hij
      exact sub_eq_zero.1 hij
  rw [← h2l, ← hrest]
  exact (add_sub_cancel _ _).symm

end GlobalTheory.PlaceTensor.CompDecomp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetMatrixPairIntegralOutside
section
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory

theorem matrixPair_integral_cofinite (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (M N : Matrix κ κ (Af F)) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, ∀ i j,
      evalV F v (M i j) ∈ v.adicCompletionIntegers F ∧
      evalV F v (N i j) ∈ v.adicCompletionIntegers F := by
  have hM : ∀ᶠ v in Filter.cofinite, ∀ p : κ × κ,
      (M p.1 p.2).1 v ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F :=
    Filter.eventually_all.2 fun p => (M p.1 p.2).2
  have hN : ∀ᶠ v in Filter.cofinite, ∀ p : κ × κ,
      (N p.1 p.2).1 v ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F :=
    Filter.eventually_all.2 fun p => (N p.1 p.2).2
  have h := hM.and hN
  rw [Filter.eventually_cofinite] at h
  refine ⟨h.toFinset, fun v hv i j => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv
  exact ⟨hv.1 (i, j), hv.2 (i, j)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitPrimeAvoiding
section
open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

namespace GlobalTheory.SplitChoice

theorem exists_place_over (K : Type) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal := by
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) (Ideal.span {(p : ℤ)})
    (by rw [(RingHom.injective_iff_ker_eq_bot (algebraMap ℤ (𝓞 K))).1 (FaithfulSMul.algebraMap_injective _ _)]; exact bot_le)
  have hm : ((p : ℕ) : 𝓞 K) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      change (p : ℤ) ∈ Ideal.under ℤ Q
      rw [hQc]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, fun h0 => ?_⟩, hm⟩
  rw [h0, Ideal.mem_bot] at hm
  exact hp.ne_zero (by exact_mod_cast hm)

theorem natCast_notMem_of_absNorm_lt {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {p : ℕ}
    (hp : p.Prime) (h : Ideal.absNorm v.asIdeal < p) : (p : 𝓞 K) ∉ v.asIdeal := by
  intro hmem
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hcop : Nat.Coprime p (Ideal.absNorm v.asIdeal) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd) (by omega)
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (𝓞 K))
  simp only [eq_intCast, Int.cast_natCast] at hab
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ (Ideal.absNorm_mem _))))

theorem splitsCompletely_of_modEq_one (D : D7) {p : ℕ} (hp : p.Prime)
    (hc : p ≡ 1 [MOD D.host.QS * D.host.q * D.host.d]) : SplitsCompletely D p := by
  obtain ⟨h1, -, h3⟩ := GlobalTheory.HostSplit.split_completely_of_modEq_one D.R D.host p hp hc
  have hs : GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentStabilizers.SplitsCompletely D.host.E p := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentStabilizers.SplitsCompletely
    rw [GlobalTheory.SplitResidue.card_eq_ncard_primesOver D.host.E hp, ← GlobalTheory.HostSplit.ncard_placesOver D.host.E hp, h1]
  refine ⟨hp, fun w hw => ⟨h3 w hw, ?_⟩⟩
  haveI := w.isPrime
  have hs' := (GlobalTheory.SplitResidue.card_eq_ncard_primesOver D.host.E hp).symm.trans hs
  exact (GlobalTheory.LocSplit.split_prime hp hs' w.asIdeal hw).1

theorem exists_split_prime : ∀ (D : D7) (S : Set (HeightOneSpectrum (𝓞 D.host.F))) (N : ℕ), S.Finite → N ≠ 0 →
    ∃ p : ℕ, SplitsCompletely D p ∧ p.Coprime N ∧ (∀ v ∈ S, (p : 𝓞 D.host.F) ∉ v.asIdeal) ∧
      ∃ v : HeightOneSpectrum (𝓞 D.host.F), (p : 𝓞 D.host.F) ∈ v.asIdeal := by
  intro D S N hS hN
  have hn : D.host.QS ≠ 0 := D.host.QS_pos.ne'
  have hq : D.host.q ≠ 0 := D.host.hyp.1.ne_zero
  have hd : D.host.d ≠ 0 := D.host.hyp.2.1.ne_zero
  have hm : D.host.QS * D.host.q * D.host.d ≠ 0 := by positivity
  obtain ⟨p, hp, hlt, hc⟩ := Nat.exists_prime_gt_modEq_one
    (N + ∑ v ∈ hS.toFinset, Ideal.absNorm v.asIdeal) hm
  refine ⟨p, splitsCompletely_of_modEq_one D hp hc, ?_, fun v hv => ?_, exists_place_over _ hp⟩
  · refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun hdv => ?_
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hdv
    omega
  · refine natCast_notMem_of_absNorm_lt v hp ?_
    have := Finset.single_le_sum (f := fun v : HeightOneSpectrum (𝓞 D.host.F) => Ideal.absNorm v.asIdeal)
      (fun _ _ => Nat.zero_le _) (hS.mem_toFinset.2 hv)
    omega

end GlobalTheory.SplitChoice
end

