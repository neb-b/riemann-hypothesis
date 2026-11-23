module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0435
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0354
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0070
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
public import GroundTheory.GlobalFields.Adele.Discrete
public import GroundTheory.GlobalFields.Adele.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0454
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicKernelTiltInvariantsFaithful
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0486
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinLiftCompatibleBdRPrisms
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.RingHomLiftCongruence

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem exists_poly (bk : BK K) (y : bk.S ⧸ Ideal.span {bk.E}) :
    ∃ P : Polynomial (Wq l bk.a), Ideal.Quotient.mk _ (P : bk.S) = y := by
  have : IsAdicComplete (Ideal.span {(l : Wq l bk.a)}) (Wq l bk.a) := WittVector.isAdicCompleteIdealSpanP
  have H : bk.Ep.IsDistinguishedAt (Ideal.span {(l : Wq l bk.a)}) :=
    { mem := fun {i} hi => Ideal.mem_span_singleton.2 (bk.dvd_coeff i hi)
      monic := bk.monic }
  exact ⟨_, H.isWeierstrassDivisorAt'.mk_mod'_eq_self⟩

theorem exists_dvd_pow_mul_ringHom_sub_mul {S A : Type} [CommRing S] [CommRing A] (f g : S →+* A) (e p : A) (s t : S)
    (hs : ∃ k : ℕ, e ∣ p ^ k * (f s - g s)) (ht : ∃ k : ℕ, e ∣ p ^ k * (f t - g t)) :
    ∃ k : ℕ, e ∣ p ^ k * (f (s * t) - g (s * t)) := by
  obtain ⟨a, x, hx⟩ := hs
  obtain ⟨b, y, hy⟩ := ht
  refine ⟨a + b, p ^ b * f t * x + p ^ a * g s * y, ?_⟩
  rw [map_mul, map_mul]
  linear_combination (p ^ b * f t) * hx + (p ^ a * g s) * hy

theorem exists_dvd_pow_mul_ringHom_sub_natPowComb {S A : Type} [CommRing S] [CommRing A] (f g : S →+* A) (e p : A) (m i j : ℕ) (s t : S)
    (hs : ∃ k : ℕ, e ∣ p ^ k * (f s - g s)) (ht : ∃ k : ℕ, e ∣ p ^ k * (f t - g t)) :
    ∃ k : ℕ, e ∣ p ^ k * (f ((m : S) ^ i * s + (m : S) ^ j * t) - g ((m : S) ^ i * s + (m : S) ^ j * t)) := by
  obtain ⟨a, x, hx⟩ := hs
  obtain ⟨b, y, hy⟩ := ht
  refine ⟨a + b, p ^ b * (m : A) ^ i * x + p ^ a * (m : A) ^ j * y, ?_⟩
  simp only [map_add (f := _), map_mul, map_pow, map_natCast]
  linear_combination (p ^ b * (m : A) ^ i) * hx + (p ^ a * (m : A) ^ j) * hy

theorem ringHom_lift_sub_mem_mul {S R A : Type} [CommRing S] [CommRing R] [CommRing A] (ψ : S →+* A) (φ : R →+* A) (I : Ideal A)
    (p : A) (i j : ℕ) (s t : S) (x y : R) (hs : ψ s - p ^ i * φ x ∈ I) (ht : ψ t - p ^ j * φ y ∈ I) :
    ψ (s * t) - p ^ (i + j) * φ (x * y) ∈ I := by
  have h := I.add_mem (I.mul_mem_left (ψ t) hs) (I.mul_mem_left (p ^ i * φ x) ht)
  convert h using 1
  rw [map_mul, map_mul]
  ring

theorem ringHom_lift_sub_mem_natPowComb {S R A : Type} [CommRing S] [CommRing R] [CommRing A] (ψ : S →+* A) (φ : R →+* A) (I : Ideal A)
    (m i j : ℕ) (s t : S) (x y : R) (hs : ψ s - (m : A) ^ i * φ x ∈ I) (ht : ψ t - (m : A) ^ j * φ y ∈ I) :
    ψ ((m : S) ^ j * s + (m : S) ^ i * t) - (m : A) ^ (i + j) * φ (x + y) ∈ I := by
  have h := I.add_mem (I.mul_mem_left ((m : A) ^ j) hs) (I.mul_mem_left ((m : A) ^ i) ht)
  convert h using 1
  simp only [map_add (f := _), map_mul, map_pow, map_natCast]
  ring

noncomputable def oK (K : FinExt l) (C : Core l) : ↥(OL K) →+* Per.BdRp l :=
  C.o.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)

def Good (bk : BK K) (C : Core l) (n : ℕ) (x : ↥(OL K)) : Prop :=
  ∃ (k : ℕ) (s : bk.S), ((aDp l).comp bk.ev) s - (l : Per.BdRp l) ^ k * oK K C x ∈ Per.FilP l n ∧
    ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ,
      BK.hf (bk := bk) f bk.E ^ n ∣ (l : B.A) ^ k * (BK.hf (bk := bk) f s - BK.hf (bk := bk) g s)

variable {bk : BK K} {C : Core l} {n : ℕ}

theorem Good.mul {x y : ↥(OL K)} (hx : Good bk C n x) (hy : Good bk C n y) : Good bk C n (x * y) := by
  obtain ⟨i, s, hs, hs'⟩ := hx
  obtain ⟨j, t, ht, ht'⟩ := hy
  exact ⟨i + j, s * t, ringHom_lift_sub_mem_mul _ _ _ _ i j s t x y hs ht,
    fun B f g => exists_dvd_pow_mul_ringHom_sub_mul _ _ _ _ s t (hs' B f g) (ht' B f g)⟩

theorem Good.add {x y : ↥(OL K)} (hx : Good bk C n x) (hy : Good bk C n y) : Good bk C n (x + y) := by
  obtain ⟨i, s, hs, hs'⟩ := hx
  obtain ⟨j, t, ht, ht'⟩ := hy
  exact ⟨i + j, (l : bk.S) ^ j * s + (l : bk.S) ^ i * t, ringHom_lift_sub_mem_natPowComb _ _ _ l i j s t x y hs ht,
    fun B f g => exists_dvd_pow_mul_ringHom_sub_natPowComb _ _ _ _ l j i s t (hs' B f g) (ht' B f g)⟩

theorem good_C (w : Wq l bk.a) :
    Good bk C n (bk.str.symm (Ideal.Quotient.mk _ (PowerSeries.C w))) := by
  refine ⟨0, PowerSeries.C w, ?_, fun B f g => ⟨0, ?_⟩⟩
  · have h := bk.θ_ev (bk.str.symm (Ideal.Quotient.mk _ (PowerSeries.C w))) (PowerSeries.C w)
      (bk.str.apply_symm_apply _).symm
    rw [bk.ev_C] at h
    have h2 := _root_.GlobalTheory.SeedSec.o_eq_aDp_wA l bk.a C w
      (((bk.str.symm (Ideal.Quotient.mk _ (PowerSeries.C w)) : ↥(OL K)) : ↥K.1) : Om l)
      (by rw [h]; exact coe_intToOC K _)
    have h3 : oK K C (bk.str.symm (Ideal.Quotient.mk _ (PowerSeries.C w))) = aDp l (wA l bk.a w) := h2
    rw [h3, RingHom.comp_apply, bk.ev_C, pow_zero, one_mul, sub_self]
    exact Ideal.zero_mem _
  · rw [(_root_.GlobalTheory.BSP.IdealSubMembership.main l K bk B f g).1 w, sub_self, mul_zero]
    exact dvd_zero _

theorem good_X : Good bk C n (bk.str.symm (Ideal.Quotient.mk _ X)) := by
  obtain ⟨m, q, h1, h2⟩ := _root_.GlobalTheory.BSP.BK.exists_approx_root l K bk n
  have hIndep (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) :
      ∃ k : ℕ, BK.hf (bk := bk) f bk.E ^ n ∣
        (l : B.A) ^ k * (BK.hf (bk := bk) f q - BK.hf (bk := bk) g q) := by
    obtain ⟨hC, hX, hI⟩ := _root_.GlobalTheory.BSP.IdealSubMembership.main l K bk B f g
    obtain ⟨-, -, hI'⟩ := _root_.GlobalTheory.BSP.IdealSubMembership.main l K bk B g f
    obtain ⟨c, a, b, hab⟩ := _root_.GlobalTheory.BSP.bezout_Ep_derivative l K bk
    exact approxRoot_image_indep_general_rings l n m c bk.Ep a b hab q h1 h2 B.I
      (BK.hf (bk := bk) f) (BK.hf (bk := bk) g) hC hX hI hI'
  exact ⟨m, q, _root_.GlobalTheory.BSP.approxRoot_sub_mem_fil l K bk C n m q h1 h2, hIndep⟩

theorem good_poly (P : Polynomial (Wq l bk.a)) :
    Good bk C n (bk.str.symm (Ideal.Quotient.mk _ (P : bk.S))) := by
  induction P using Polynomial.induction_on with
  | C a => rw [Polynomial.coe_C]; exact good_C a
  | add p q hp hq => rw [Polynomial.coe_add, map_add (f := _), map_add (f := _)]; exact hp.add hq
  | monomial k a h =>
    rw [pow_succ, ← mul_assoc, Polynomial.coe_mul, Polynomial.coe_X, map_mul, map_mul]
    exact h.mul good_X

theorem exists_lift : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l)
    (n : ℕ) (x : ↥(OL K)), ∃ (k : ℕ) (s : bk.S),
    aDp l (bk.ev s) - (l : Per.BdRp l) ^ k * C.o ((x : ↥K.1) : Om l) ∈ Per.FilP l n ∧
    (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ,
      BK.hf (bk := bk) f bk.E ^ n ∣ (l : B.A) ^ k * (BK.hf (bk := bk) f s - BK.hf (bk := bk) g s)) := by
  intro l _ K bk C n x
  obtain ⟨P, hP⟩ := exists_poly bk (bk.str x)
  have h := good_poly (bk := bk) (C := C) (n := n) P
  rw [hP, bk.str.symm_apply_apply] at h
  exact h

end GlobalTheory.BSP.RingHomLiftCongruence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteCoefficientSetFrobeniusCharpolys
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.FrobSysCoef

theorem main : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (U : Set (Formalism.ConjugateSelfDual.G E Ω)) (p : Formalism.ConjugateSelfDual.G E Ω → ℂ[X]), Dense U → ∃ S : Finset ℂ, ∀ K : IntermediateField ℚ_[l] (Qbar l), (∀ z ∈ S, ι.symm z ∈ K) → ∀ ρ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l), Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l))) → IsSSRep ρ → (∀ σ ∈ U, ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = p σ) → ∃ Pm : GL (Fin a) (Qbar l), ∀ g s t, ((Pm⁻¹ * ρ g * Pm : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) s t ∈ K := by
  intro l _ ι E Ω _ _ _ _ _ a U p hU
  classical
  by_cases hex : ∃ ρ₀ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l),
      Continuous (fun g => ((ρ₀ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l))) ∧ IsSSRep ρ₀ ∧
      (∀ σ ∈ U, ((ρ₀ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = p σ)
  · obtain ⟨ρ₀, hc₀, hs₀, hp₀⟩ := hex
    obtain ⟨S₀, hS₀⟩ := _root_.GlobalTheory.CoefField.entries_mem_of_finset l E Ω a ρ₀ hc₀
    refine ⟨S₀.image ι, fun K hK ρ hc hs hp => ?_⟩
    have hK' : ∀ z ∈ S₀, z ∈ K := fun z hz => by
      simpa using hK (ι z) (Finset.mem_image_of_mem _ hz)
    have hU' : ∀ σ ∈ U, ((ρ₀ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly =
        ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly := fun σ hσ =>
      Polynomial.map_injective ι.toRingHom ι.injective ((hp₀ σ hσ).trans (hp σ hσ).symm)
    have hall := GlobalTheory.charpoly_eq_of_eqOn_dense _ _ hc₀ hc U hU hU'
    obtain ⟨Pm, hPm⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ₀ ρ hs₀ hs hall
    refine ⟨Pm⁻¹, fun g s t => ?_⟩
    have : Pm⁻¹⁻¹ * ρ g * Pm⁻¹ = ρ₀ g := by
      rw [hPm g, inv_inv]; group
    rw [this]
    exact hS₀ K hK' g s t
  · refine ⟨∅, fun K _ ρ hc hs hp => ?_⟩
    exact absurd ⟨ρ, hc, hs, hp⟩ hex

end GlobalTheory.FrobSysCoef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainRationalUpperUnitriangula
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CellDec

def unipFund (E : Type) [Field E] [NumberField E] (n : ℕ) : Set (NA E n) :=
  {u | ∀ i j : Fin n, i < j → ((u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ GroundTheory.Global.fundamentalSet E}

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem ratGL_mem_NA {γ : GL (Fin n) E} (hγ : γ ∈ GlobalTheory.SmGL.unipB E (Fin n)) : ratGL E n γ ∈ NA E n := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB E).1 hγ
  refine (GlobalTheory.SmGL.mem_unipB (Ad E)).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · simp [ratGL, h1 i j hij]
  · simp [ratGL, h2 i]

theorem exists_fundamentalDomain_NE (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)]
    [BorelSpace (GA E n)] (ν : Measure (NA E n)) [ν.IsHaarMeasure] : ∃ D : Set (NA E n),
    IsFundamentalDomain ((NE E n).subgroupOf (NA E n)) D ν ∧ 0 < ν D ∧ ν D < ⊤ := by
  classical
  have hfd : IsFundamentalDomain ((NE E n).subgroupOf (NA E n)) (unipFund E n) ν := by
    refine IsFundamentalDomain.mk' ?_ ?_
    · refine MeasurableSet.nullMeasurableSet ?_
      have : unipFund E n = ⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : i < j),
          (fun u : NA E n => ((u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j) ⁻¹'
            GroundTheory.Global.fundamentalSet E := by
        ext u; simp [unipFund]
      rw [this]
      refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
      refine (Continuous.measurable ?_) (GroundTheory.Global.measurableSet_fundamentalSet E)
      exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem i j
    · intro x
      obtain ⟨γ, ⟨hγ, hγD⟩, huniq⟩ := GlobalTheory.T.existsUnique_ratUnitriangular_mul_entries_mem_fundamentalSet E n (x : GA E n) x.2
      refine ⟨⟨⟨ratGL E n γ, ratGL_mem_NA hγ⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γ, hγ, rfl⟩)⟩,
        fun i j hij => hγD i j hij, ?_⟩
      intro g hg
      obtain ⟨γ', hγ', hγ'g⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 g.2)
      have he : γ' = γ := huniq γ' ⟨hγ', fun i j hij => by
        have := hg i j hij
        rw [hγ'g]; exact this⟩
      apply Subtype.ext; apply Subtype.ext
      change ((g : NA E n) : GA E n) = ratGL E n γ
      rw [← hγ'g, he]
  have hE : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have hG : Countable ((NE E n).subgroupOf (NA E n)) := by
    have h : ∀ g : (NE E n).subgroupOf (NA E n), ∃ γ : GL (Fin n) E, ratGL E n γ = ((g : NA E n) : GA E n) :=
      fun g => by
        obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 g.2)
        exact ⟨γ, hγ⟩
    choose f hf using h
    have : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
    have : Countable (GL (Fin n) E) :=
      Function.Injective.countable (f := fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E))
        fun a b h => Units.ext h
    exact Function.Injective.countable (f := f) fun a b hab =>
      Subtype.ext (Subtype.ext (by rw [← hf a, ← hf b, hab]))
  have hinv : SMulInvariantMeasure ((NE E n).subgroupOf (NA E n)) (NA E n) ν :=
    ⟨fun g s _ => by
      have : (fun x : NA E n => g • x) = fun x => (g : NA E n) * x := rfl
      show ν ((fun x => g • x) ⁻¹' s) = ν s
      rw [this]; exact measure_preimage_mul ν (g : NA E n) s⟩
  refine ⟨unipFund E n, hfd, pos_iff_ne_zero.2 (hfd.measure_ne_zero (NeZero.ne ν)), ?_⟩
  set C : Set (Ad E) := closure (GroundTheory.Global.fundamentalSetInfinite E) ×ˢ
    (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (FiniteAdeleRing (𝓞 E) E)) with hCdef
  have hC : IsCompact C := (GroundTheory.Global.isCompact_closure_fundamentalSetInfinite E).prod
    (GroundTheory.Global.isCompact_integralFiniteAdeles E)
  set K : Set (GA E n) := {g : GA E n | g ∈ NA E n ∧ ∀ i j : Fin n, i < j →
    (g : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ C} with hKdef
  have hK : IsCompact ((Subtype.val : NA E n → GA E n) ⁻¹' K) := by
    rw [Subtype.isCompact_iff, Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype]
    change IsCompact (K ∩ (NA E n : Set (GA E n)))
    rw [Set.inter_eq_left.2 (fun g (hg : g ∈ K) => hg.1)]
    exact _root_.GlobalTheory.CellDec.isCompact_unip_entries_mem E n C hC
  refine (measure_mono fun u hu => ?_).trans_lt hK.measure_lt_top
  refine ⟨u.2, fun i j hij => ?_⟩
  have h := hu i j hij
  exact ⟨subset_closure h.1, h.2⟩

end GlobalTheory.CellDec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHwOfFonOfCmpOf
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL

theorem exists_hwOf_fonOf_cmpOf : ∀ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)), (∀ (l : ℕ) [Fact l.Prime], LocTied l (L l) (A l)) → (∀ (l : ℕ) [Fact l.Prime], WachEx (A l)) → ∃ (H : HWOf L) (F : FonOf L A H), Nonempty (CmpOf L A H F) := by
  intro L A hT hW
  have key : ∀ (l : ℕ) [Fact l.Prime], ∃ H : LocHW l (L l), ∃ F : LocFon l (L l) (A l) H,
      Nonempty (LocCmpT l (L l) (A l) H F) := fun l _ =>
    GlobalTheory.T.exists_local_wach_functor l (L l) (A l) (hT l) (_root_.GlobalTheory.TiltFaithful.faithH l (L l) (A l)) (hW l)
  choose H F hC using key
  exact ⟨fun l _ => H l, fun l _ => F l, ⟨fun l _ => (hC l).some⟩⟩

end GlobalTheory.HWL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralWittLatticeBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.SatLattice

section abstract

variable {R : Type} [CommRing R] [IsDomain R] {π : R} (O : Subring R)

theorem pid_of_fact (hπ : Irreducible π) (hO : π ∈ O)
    (h4 : ∀ w ∈ O, w ≠ 0 → ∃ (k : ℕ) (v v' : R), v ∈ O ∧ v' ∈ O ∧ v * v' = 1 ∧ w = π ^ k * v) :
    IsPrincipalIdealRing O := by
  have hu : ∀ a : O, IsUnit (a : R) → IsUnit a := by
    intro a ha
    obtain ⟨k, v, v', hv, hv', h1, h2⟩ := h4 a a.2 ha.ne_zero
    rcases k with _ | k
    · refine IsUnit.of_mul_eq_one (⟨v', hv'⟩ : O) (Subtype.ext ?_)
      simp [h2, h1]
    · exfalso
      rw [h2, pow_succ', mul_assoc] at ha
      exact hπ.not_isUnit (isUnit_of_mul_isUnit_left ha)
  have hirr : Irreducible (⟨π, hO⟩ : O) := by
    refine ⟨fun h => hπ.not_isUnit (h.map O.subtype), fun a b hab => ?_⟩
    exact (hπ.isUnit_or_isUnit (congrArg Subtype.val hab)).imp (hu a) (hu b)
  have : IsDiscreteValuationRing O := by
    refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨_, hirr, ?_⟩
    intro x hx
    obtain ⟨k, v, v', hv, hv', h1, h2⟩ := h4 x x.2 (fun h => hx (Subtype.ext h))
    refine ⟨k, ⟨⟨v, hv⟩, ⟨v', hv'⟩, Subtype.ext h1, Subtype.ext (by simp [mul_comm v' v, h1])⟩, Subtype.ext ?_⟩
    simp [h2]
  infer_instance

theorem sat_pow (hπ : π ≠ 0) (h1 : ∀ w ∈ O, π ∣ w → ∃ v ∈ O, w = π * v) (n : ℕ) (x : R)
    (hx : π ^ n * x ∈ O) : x ∈ O := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    obtain ⟨v, hv, h⟩ := h1 _ hx ⟨π ^ n * x, by ring⟩
    refine ih ?_
    have : π ^ n * x = v := mul_left_cancel₀ hπ (by rw [← h]; ring)
    rwa [this]

def divSub {d : ℕ} (Y : Matrix (Fin d) (Fin d) R) (a : R) : Submodule O (Fin d → O) where
  carrier := {x | ∀ i, a ∣ (Y *ᵥ fun j => (x j : R)) i}
  zero_mem' i := by
    simp [Matrix.mulVec, dotProduct]
  add_mem' {x y} hx hy i := by
    have : (fun j => ((x + y) j : R)) = (fun j => (x j : R)) + fun j => (y j : R) := rfl
    rw [this, Matrix.mulVec_add]
    exact dvd_add (hx i) (hy i)
  smul_mem' c x hx i := by
    have : (fun j => ((c • x) j : R)) = (c : R) • fun j => (x j : R) := rfl
    rw [this, Matrix.mulVec_smul]
    exact Dvd.dvd.mul_left (hx i) _

theorem exists_basis_matrix [IsPrincipalIdealRing O] {d : ℕ} (Y : Matrix (Fin d) (Fin d) R) (a : R) (ha : a ≠ 0)
    (haO : a ∈ O) :
    ∃ P : Matrix (Fin d) (Fin d) R, (∀ i j, P i j ∈ O) ∧ P.det ≠ 0 ∧ (∀ i j, a ∣ (Y * P) i j) ∧
      ∀ x : Fin d → R, (∀ i, x i ∈ O) → (∀ i, a ∣ (Y *ᵥ x) i) →
        ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ x = P *ᵥ w := by
  set N := divSub O Y a with hN
  have hmem : ∀ v : Fin d → O, (⟨a, haO⟩ : O) • v ∈ N := by
    intro v i
    have : (fun j => (((⟨a, haO⟩ : O) • v) j : R)) = a • fun j => (v j : R) := rfl
    rw [this, Matrix.mulVec_smul]
    exact Dvd.intro _ rfl
  let f : (Fin d → O) →ₗ[O] N := LinearMap.codRestrict N ((⟨a, haO⟩ : O) • LinearMap.id) hmem
  have hf : Function.Injective f := by
    intro v w h
    funext i
    have := congrArg (fun z : N => ((z.1 i : O) : R)) h
    exact Subtype.ext (mul_left_cancel₀ ha this)
  have hr : Module.finrank O N = d := by
    apply le_antisymm
    · simpa using N.finrank_le
    · simpa using LinearMap.finrank_le_finrank_of_injective hf
  let b := Module.finBasisOfFinrankEq O N hr
  let P : Matrix (Fin d) (Fin d) R := Matrix.of fun i j => ((b j).1 i : R)
  have hspan : ∀ x : Fin d → R, (∀ i, x i ∈ O) → (∀ i, a ∣ (Y *ᵥ x) i) →
        ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ x = P *ᵥ w := by
    intro x hx hd
    let z : N := ⟨fun i => ⟨x i, hx i⟩, hd⟩
    refine ⟨fun j => (b.repr z j : R), fun j => (b.repr z j).2, funext fun i => ?_⟩
    have := congrArg (fun z : N => ((z.1 i : O) : R)) (b.sum_repr z)
    refine Eq.trans this.symm ?_
    rw [Submodule.coe_sum, Finset.sum_apply, AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine ⟨P, fun i j => ((b j).1 i).2, ?_, fun i j => (b j).2 i, hspan⟩
  have hcol : ∀ j : Fin d, ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ a • (Pi.single j 1 : Fin d → R) = P *ᵥ w := by
    intro j
    refine hspan _ (fun i => ?_) (fun i => ?_)
    · by_cases h : i = j
      · simp [h, haO]
      · simp [h]
    · rw [Matrix.mulVec_smul]
      exact Dvd.intro _ rfl
  choose w _ hw using hcol
  have hPQ : P * Matrix.of (fun i j => w j i) = a • (1 : Matrix (Fin d) (Fin d) R) := by
    ext i j
    have := congrFun (hw j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Pi.single_apply] at this
    simp [Matrix.mul_apply, ← this, Matrix.one_apply]
  intro h0
  have := congrArg Matrix.det hPQ
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ ha this.symm

theorem lattice_abstract [IsPrincipalIdealRing O] (hπ : π ≠ 0) (hO : π ∈ O)
    (h1 : ∀ w ∈ O, π ∣ w → ∃ v ∈ O, w = π * v) {d : ℕ} (Y : Matrix (Fin d) (Fin d) R) (c : ℕ) (u : Rˣ)
    (hdet : Y.det = π ^ c * u) :
    ∃ (m : ℕ) (P Y' : Matrix (Fin d) (Fin d) R), (∀ i j, P i j ∈ O) ∧ P.det ≠ 0 ∧ π ^ m • Y' = Y * P ∧
      (∀ v : Fin d → R, (∀ i, v i ∈ O) → ∀ n : ℕ, (∀ i, π ^ n ∣ (Y *ᵥ v) i) →
        ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ π ^ m • v = π ^ n • (P *ᵥ w)) ∧
      ∀ w : Fin d → R, (∀ i, w i ∈ O) → (∀ i, π ∣ (Y' *ᵥ w) i) → ∀ i, π ∣ w i := by
  obtain ⟨P, hPO, hP, hdv, hspan⟩ := exists_basis_matrix O Y (π ^ c) (pow_ne_zero _ hπ) (O.pow_mem hO c)
  choose y hy using hdv
  have hY' : π ^ c • Matrix.of y = Y * P := by
    ext i j
    simp [hy]
  have key : ∀ v : Fin d → R, (∀ i, v i ∈ O) → ∀ n : ℕ, (∀ i, π ^ n ∣ (Y *ᵥ v) i) →
        ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ π ^ c • v = π ^ n • (P *ᵥ w) := by
    intro v hv n hn
    choose z hz using hn
    have hz' : Y *ᵥ v = π ^ n • z := funext hz
    let x : Fin d → R := ((u⁻¹ : Rˣ) : R) • (Y.adjugate *ᵥ z)
    have hx : π ^ c • v = π ^ n • x := by
      have h := congrArg (fun t => ((u⁻¹ : Rˣ) : R) • (Y.adjugate *ᵥ t)) hz'
      simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.mulVec_smul, Matrix.smul_mulVec,
        Matrix.one_mulVec, hdet] at h
      rw [smul_smul, mul_left_comm, Units.inv_mul, mul_one, smul_comm] at h
      exact h
    have hYx : Y *ᵥ x = π ^ c • z := by
      simp only [x, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.mulVec_smul, Matrix.smul_mulVec,
        Matrix.one_mulVec, hdet]
      rw [smul_smul, mul_left_comm, Units.inv_mul, mul_one]
    obtain ⟨w, hw, hxw⟩ := hspan x (fun i => sat_pow O hπ h1 n _ (by
      have := congrFun hx i
      simp only [Pi.smul_apply, smul_eq_mul] at this
      rw [← this]
      exact O.mul_mem (O.pow_mem hO c) (hv i))) (fun i => by rw [hYx]; exact Dvd.intro _ rfl)
    exact ⟨w, hw, by rw [hx, hxw]⟩
  refine ⟨c, P, Matrix.of y, hPO, hP, hY', key, fun w hw hd => ?_⟩
  obtain ⟨w', -, h⟩ := key (P *ᵥ w) (fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact O.sum_mem fun j _ => O.mul_mem (hPO i j) (hw j)) (c + 1) (fun i => by
    rw [Matrix.mulVec_mulVec, ← hY', Matrix.smul_mulVec, pow_succ]
    exact mul_dvd_mul_left _ (hd i))
  have h2 : P *ᵥ (w - π • w') = 0 := by
    funext i
    have := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    refine mul_left_cancel₀ (pow_ne_zero c hπ) ?_
    linear_combination this
  have h3 := Matrix.eq_zero_of_mulVec_eq_zero hP h2
  intro i
  exact ⟨w' i, sub_eq_zero.1 (congrFun h3 i)⟩

end abstract

theorem exists_lattice_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (Y1 : Matrix (Fin d) (Fin d) (WCb l)), Y1.det ≠ 0 → ∃ (m : ℕ) (P Y' : Matrix (Fin d) (Fin d) (WCb l)), (∀ i j, P i j ∈ bk.OE) ∧ P.det ≠ 0 ∧ (l : WCb l) ^ m • Y' = Y1 * P ∧ (∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → ∀ n : ℕ, (∀ i, (l : WCb l) ^ n ∣ (Y1 *ᵥ v) i) → ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (l : WCb l) ^ m • v = (l : WCb l) ^ n • (P *ᵥ w)) ∧ ∀ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) → (∀ i, (l : WCb l) ∣ (Y' *ᵥ w) i) → ∀ i, (l : WCb l) ∣ w i := by
  intro l _ K bk d Y1 hY
  obtain ⟨h1, -, -, h4, -⟩ := _root_.GlobalTheory.OEDvr.main l K bk
  have hirr : Irreducible (l : WCb l) := WittVector.irreducible l
  have : PerfectRing (Cb l) l := by
    refine PerfectRing.ofSurjective _ l fun x => ?_
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
    obtain ⟨a', rfl⟩ := surjective_frobenius (OCb l) l a
    obtain ⟨b', rfl⟩ := surjective_frobenius (OCb l) l b
    exact ⟨algebraMap (OCb l) (Cb l) a' / algebraMap (OCb l) (Cb l) b', by
      simp [frobenius_def, div_pow, map_pow]⟩
  obtain ⟨c, u, hu⟩ := WittVector.exists_eq_pow_p_mul' Y1.det hY
  have := pid_of_fact bk.OE hirr (natCast_mem _ l) h4
  exact lattice_abstract bk.OE hirr.ne_zero (natCast_mem _ l) h1 Y1 c u hu

end GlobalTheory.SatLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentBlockRootFactorsRankOneDomainStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentBlock_rootFactors_rank_one_domain : ∀ {O : Type} [CommRing O] [IsDomain O] (n t : ℕ) (e X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O), 2 ≤ t → e * e = e → e * X₀ = X₀ → X₀ * e = X₀ → Set.InjOn ρ (Finset.Icc 1 t : Set ℕ) → ∏ c ∈ Finset.Icc 1 t, (Polynomial.X - Polynomial.C (ρ c)) = blockPol e X₀ → ((((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod).map (toFr O)).rank = 1 ∧ ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod * ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod = (∏ c ∈ Finset.Ioc 1 t, (ρ 1 - ρ c)) • ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod := by
  first | exact @GlobalTheory.RootFactor.rank_one_and_sq | exact GlobalTheory.RootFactor.rank_one_and_sq | (intros; apply GlobalTheory.RootFactor.rank_one_and_sq <;> assumption)
end

