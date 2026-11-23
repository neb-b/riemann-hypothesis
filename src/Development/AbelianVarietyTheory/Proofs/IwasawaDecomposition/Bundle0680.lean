module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoTame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0826
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0634
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1698
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0671
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0678
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompAtBaseCharacterMulUnramifiedEqTypeCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.TypeCharRead

variable {K : Type} [Field K] [NumberField K]

theorem isUnit_of_val_eq_one (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletionIntegers K)
    (h : Valued.v (x : v.adicCompletion K) = 1) : IsUnit x :=
  (Valuation.integer.integers (Valued.v (R := v.adicCompletion K))).isUnit_iff_valuation_eq_one.2 h

theorem red_eq_zero_of_val_lt_one (v : HeightOneSpectrum (𝓞 K)) {p : ℕ} [Fact p.Prime]
    (red : v.adicCompletionIntegers K →+* ZMod p) (x : v.adicCompletionIntegers K)
    (hx : Valued.v (x : v.adicCompletion K) < 1) : red x = 0 := by
  by_contra h
  have ht : (red x)⁻¹ * red x = 1 := inv_mul_cancel₀ h
  set n : ℕ := ((red x)⁻¹ : ZMod p).val with hn
  set z : v.adicCompletionIntegers K := 1 - (n : v.adicCompletionIntegers K) * x with hz
  have hrz : red z = 0 := by
    rw [hz, map_sub, map_mul, map_one, map_natCast, hn, ZMod.natCast_zmod_val, ht, sub_self]
  have hnv : Valued.v (((n : v.adicCompletionIntegers K) : v.adicCompletion K)) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (n : v.adicCompletionIntegers K).2
  have hlt : Valued.v (((n : v.adicCompletionIntegers K) : v.adicCompletion K) * (x : v.adicCompletion K)) < 1 := by
    rw [map_mul]
    calc Valued.v (((n : v.adicCompletionIntegers K) : v.adicCompletion K)) * Valued.v (x : v.adicCompletion K)
        ≤ 1 * Valued.v (x : v.adicCompletion K) := by gcongr
      _ < 1 := by rw [one_mul]; exact hx
  have hvz : Valued.v (z : v.adicCompletion K) = 1 := by
    have e : (z : v.adicCompletion K) = 1 - ((n : v.adicCompletionIntegers K) : v.adicCompletion K) * (x : v.adicCompletion K) := by
      rw [hz]; push_cast; rfl
    rw [e]
    exact Valuation.map_one_sub_of_lt _ hlt
  have hu := (isUnit_of_val_eq_one v z hvz).map red
  rw [hrz] at hu
  exact not_isUnit_zero hu

end GlobalTheory.TypeCharRead

open Formalism.L2.DIV (kP)
open Formalism.IndefR.Links (IsRes)

namespace GlobalTheory.TypeCharRead

theorem compAt_baseCharacter_mul_unramified_eq_typeCharacter_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ValLL0 D cf →
    ∀ τ : ℕ → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))ˣ →* (↥D.LL0)ˣ,
    (∀ i j b kv x, 1 ≤ j → j ≤ D.R.m → ((Bs.exp.tauG i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
      GlobalTheory.SeriesTie.sideEmb D.ntw i b ((τ j kv x : (↥D.LL0)ˣ) : ↥D.LL0)) →
    ∀ (j : Fin D.R.m) (kv : Σ k : Fin 2, D.nd.PlG k) (s : SplitPlace D.host.E), s.w = NX.pG D kv →
    ∀ χ : HChar D.host.E, χ.UnrAt s.w →
    ∀ red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1),
    ∃ ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ, NG.IsCompAt (cf.mu0 j * χ) s ξ ∧
      ∀ (y : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) (hy : IsUnit (red y))
        (uu : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ), (uu : s.v.adicCompletion (maximalRealSubfield D.host.E)) = y →
          ((ξ uu : ℂˣ) : ℂ) = embLL0 D ((τ (j.1 + 1) kv hy.unit : (↥D.LL0)ˣ) : ↥D.LL0) := by
  intro hGAR D cf Rw low Pq S hL eig θ Bs hV τ hτ j kv s hsw χ hχ red
  haveI : Fact (D.host.g kv.1).Prime := ⟨D.host.g_prime kv.1⟩
  obtain ⟨-, -, -, h4⟩ := _root_.GlobalTheory.MtRed.km_reduction D 0
  obtain ⟨φ, hφs, hφ0, hφa, -⟩ := h4 s
  have hker : RingHom.ker φ ≤ RingHom.ker red := fun x hx =>
    (RingHom.mem_ker).2 (red_eq_zero_of_val_lt_one s.v red x ((hφ0 x).1 ((RingHom.mem_ker).1 hx)))
  set ι := φ.liftOfSurjective hφs ⟨red, hker⟩ with hι
  have hιφ : ∀ x, ι (φ x) = red x := fun x => RingHom.liftOfSurjective_comp_apply φ hφs ⟨red, hker⟩ x
  have hred0 : ∀ x, red x = 0 → Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1 := by
    intro x hx
    refine lt_of_le_of_ne ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 x.2) (fun h1 => ?_)
    have hu := (isUnit_of_val_eq_one s.v x h1).map red
    rw [hx] at hu
    exact not_isUnit_zero hu
  let c : (kP s.w)ˣ →* ℂˣ :=
    (Units.map (embLL0 D).toMonoidHom).comp ((τ (j.1 + 1) kv).comp (Units.map ι.toMonoidHom))
  have hres : IsRes (cf.mu0 j * χ) s.w c := by
    intro a k u hk hu
    have ha : a ∉ s.w.asIdeal := by
      intro hm
      have : (u : kP s.w) = 0 := by rw [hu]; exact Ideal.Quotient.eq_zero_iff_mem.2 hm
      exact u.ne_zero this
    have ha0 : ((a : 𝓞 D.host.E) : D.host.E) ≠ 0 := hk ▸ k.ne_zero
    obtain ⟨hia, hφia⟩ := hφa a
    set x : (ZMod (D.host.g kv.1))ˣ := Units.map ι.toMonoidHom u with hx
    have hxv : (x : ZMod (D.host.g kv.1)) = red ⟨_, hia⟩ := by
      show ι (u : kP s.w) = _
      rw [hu, ← hφia, hιφ]
    have hmem : (((x : ZMod (D.host.g kv.1)).val : 𝓞 D.host.E) - a) ∈ (NX.pG D kv).asIdeal := by
      rw [← hsw]
      obtain ⟨hib, hφib⟩ := hφa (((x : ZMod (D.host.g kv.1)).val : 𝓞 D.host.E) - a)
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hφib]
      apply (hφ0 _).2
      apply hred0
      have e : (⟨_, hib⟩ : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) =
          (((x : ZMod (D.host.g kv.1)).val : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E))) - ⟨_, hia⟩ := by
        apply Subtype.ext
        show s.i (((((x : ZMod (D.host.g kv.1)).val : 𝓞 D.host.E) - a : 𝓞 D.host.E)) : D.host.E) = _
        push_cast
        rw [map_sub, map_natCast]
      rw [e, map_sub, map_natCast, ZMod.natCast_zmod_val, hxv, sub_self]
    have h61 := _root_.GlobalTheory.TwInputs.tau_eq_locK hGAR D cf Rw low Pq S hL eig θ Bs hV τ hτ j kv x a ha0 hmem
    have hunit : IsUnitAt s.w (atFin s.w k) := by
      have e := GlobalTheory.ChainOnto.TameRes.val_alg s.w (k : D.host.E)
      show Valued.v (algebraMap D.host.E (s.w.adicCompletion D.host.E) (k : D.host.E)) = 1
      rw [e, hk]
      exact GlobalTheory.ChainOnto.TameRes.valuation_eq_one_of_not_mem s.w a ha
    have h2 : χ.locK s.w k = 1 := hχ _ hunit
    have hk' : Units.mk0 ((a : 𝓞 D.host.E) : D.host.E) ha0 = k := Units.ext hk.symm
    rw [hk', ← hsw] at h61
    apply Units.ext
    have e : (cf.mu0 j * χ).locK s.w k = (cf.mu0 j).locK s.w k * χ.locK s.w k := rfl
    rw [e, h2, mul_one, ← h61]
    rfl
  obtain ⟨ξ, hξc, hξr⟩ := _root_.GlobalTheory.XiRes.exists_isCompAt_res D s φ hφs hφ0 hφa _ c hres
  refine ⟨ξ, hξc, fun y hy uu huu => ?_⟩
  have hyv : Valued.v (y : s.v.adicCompletion (maximalRealSubfield D.host.E)) = 1 := by
    refine le_antisymm ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 y.2) (not_lt.1 fun hlt => ?_)
    have h0 := red_eq_zero_of_val_lt_one s.v red y hlt
    rw [h0] at hy
    exact not_isUnit_zero hy
  have hyu : IsUnit (φ y) := (isUnit_of_val_eq_one s.v y hyv).map φ
  rw [hξr uu y hyu.unit huu.symm hyu.unit_spec.symm]
  have hw : Units.map ι.toMonoidHom hyu.unit = hy.unit := by
    apply Units.ext
    show ι ((hyu.unit : kP s.w)) = red y
    rw [hyu.unit_spec, hιφ]
  show (embLL0 D) ((τ (j.1 + 1) kv (Units.map ι.toMonoidHom hyu.unit) : (↥D.LL0)ˣ) : ↥D.LL0) = _
  rw [hw]

end GlobalTheory.TypeCharRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexTypePlaceCharacterEqSuperdiagAddCharMulLo
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.XUniRead

section Loc
variable {L : Type} [Field L] [NumberField L] [IsCMField L]

private theorem red_zero (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {q : ℕ} (hq : q.Prime)
    (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* ZMod q)
    (y : v.adicCompletionIntegers (maximalRealSubfield L))
    (hy : Valued.v (y : v.adicCompletion (maximalRealSubfield L)) < 1) : red y = 0 := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharZero (v.adicCompletion (maximalRealSubfield L)) :=
    charZero_of_injective_algebraMap (algebraMap (maximalRealSubfield L) _).injective
  have hp : (RingHom.ker red).IsPrime := RingHom.ker_isPrime red
  have hne : RingHom.ker red ≠ ⊥ := by
    intro h
    have h1 : ((q : ℕ) : v.adicCompletionIntegers (maximalRealSubfield L)) ∈ RingHom.ker red := by
      rw [RingHom.mem_ker, map_natCast, ZMod.natCast_self]
    rw [h, Ideal.mem_bot] at h1
    have h2 := congrArg (fun z : v.adicCompletionIntegers (maximalRealSubfield L) =>
      (z : v.adicCompletion (maximalRealSubfield L))) h1
    simp only [SubringClass.coe_natCast, ZeroMemClass.coe_zero, Nat.cast_eq_zero] at h2
    exact hq.ne_zero h2
  have hm : RingHom.ker red = IsLocalRing.maximalIdeal _ :=
    IsLocalRing.eq_maximalIdeal (hp.isMaximal hne)
  rw [← RingHom.mem_ker, hm, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨z, hz⟩ := hu.exists_right_inv
  have h2 := congrArg (fun z : v.adicCompletionIntegers (maximalRealSubfield L) =>
      Valued.v (z : v.adicCompletion (maximalRealSubfield L))) hz
  simp only [MulMemClass.coe_mul, map_mul, OneMemClass.coe_one, map_one] at h2
  have hz1 : Valued.v (z : v.adicCompletion (maximalRealSubfield L)) ≤ 1 := z.2
  have h3 := mul_le_mul_right hz1 (Valued.v (y : v.adicCompletion (maximalRealSubfield L)))
  rw [h2, mul_one] at h3
  exact absurd hy (not_lt.2 h3)

private theorem intLift_coe (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (y : v.adicCompletionIntegers (maximalRealSubfield L)) :
    NX.intLift v (y : v.adicCompletion (maximalRealSubfield L)) = y := by
  unfold NX.intLift
  rw [dite_eq_left y.2]

private theorem sum_top {R : Type} [CommRing R] {n r : ℕ} (h : r ≤ n) (X : Matrix (Fin n) (Fin n) R) :
    (∑ a : Fin n, ∑ b : Fin n, if a.val + 1 = b.val ∧ b.val < r then X a b else 0) = NX.supSum r (NX.topR h X) := by
  unfold NX.supSum NX.topR
  symm
  refine Finset.sum_of_injOn (Fin.castLE h) (Fin.castLE_injective h).injOn (fun _ _ => Finset.mem_univ _)
    (fun a _ ha => Finset.sum_eq_zero fun b _ => if_neg fun hh => ha ⟨⟨a.val, by omega⟩, by simp, Fin.ext rfl⟩) fun a _ => ?_
  refine Finset.sum_of_injOn (Fin.castLE h) (Fin.castLE_injective h).injOn (fun _ _ => Finset.mem_univ _)
    (fun b _ hb => if_neg fun hh => hb ⟨⟨b.val, hh.2⟩, by simp, Fin.ext rfl⟩) fun b _ => ?_
  refine if_congr ?_ rfl rfl
  simp only [Fin.val_castLE, b.2, and_true]
  exact eq_comm

private theorem supSum_small {R : Type} [CommRing R] {r : ℕ} (h : ¬ 2 ≤ r) (M : Matrix (Fin r) (Fin r) R) :
    NX.supSum r M = 0 := by
  unfold NX.supSum
  exact Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => if_neg (by have := b.2; omega)

private theorem loc_read (s : SplitPlace L) {n r : ℕ} (h : r ≤ n) {q : ℕ} (hq : q.Prime)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield L) →+* ZMod q)
    (x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) (hx : NG.UniRT s r x) :
    NX.IsUniTri r (NX.redMat s.v red (NX.topR h x.val)) ∧ IsUnit (red (NX.intLift s.v (NX.detT r x.val))) ∧
    ((NX.intLift s.v (NX.detT r x.val) : s.v.adicCompletionIntegers (maximalRealSubfield L)) :
      s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r x ∧
    ∃ y : s.v.adicCompletionIntegers (maximalRealSubfield L),
      (y : s.v.adicCompletion (maximalRealSubfield L)) = NG.supDiag s r x ∧
      red y = NX.supSum r (NX.redMat s.v red (NX.topR h x.val)) := by
  obtain ⟨⟨⟨X0, hX0⟩, hll⟩, huni⟩ := hx
  obtain ⟨X, hXu, hX⟩ : ∃ X : Matrix (Fin n) (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)),
      IsUnit X.det ∧ ∀ a b, x.val a b = (X a b : s.v.adicCompletion (maximalRealSubfield L)) :=
    ⟨X0.val, Matrix.isUnits_det_units X0, fun a b => by rw [← hX0]; rfl⟩
  have hr : ∀ a b, NX.redMat s.v red (NX.topR h x.val) a b = red (X (Fin.castLE h a) (Fin.castLE h b)) := fun a b => by
    simp only [NX.redMat, NX.topR, Matrix.submatrix_apply]
    rw [hX, intLift_coe]
  have hd : NX.detT r x.val = ((NX.detT r X : s.v.adicCompletionIntegers (maximalRealSubfield L)) :
      s.v.adicCompletion (maximalRealSubfield L)) := by
    unfold NX.detT
    refine Eq.trans ?_ (RingHom.map_det (s.v.adicCompletionIntegers (maximalRealSubfield L)).subtype _).symm
    congr 1
    exact Matrix.ext fun a b => hX _ _
  refine ⟨⟨fun a b hab => ?_, fun a => ?_⟩, ?_, ?_, NX.supSum r (NX.topR h X), ?_, ?_⟩
  · rw [hr]
    refine red_zero _ hq red _ ?_
    rw [← hX]
    exact (huni _ _ a.2 b.2).1 hab
  · rw [hr, ← sub_eq_zero, ← map_one red, ← map_sub]
    refine red_zero _ hq red _ ?_
    have := (huni (Fin.castLE h a) (Fin.castLE h a) a.2 a.2).2 rfl
    rw [hX] at this
    exact this
  · rw [hd, intLift_coe]
    have h1 := hXu.map red
    rw [RingHom.map_det, Matrix.twoBlockTriangular_det' (red.mapMatrix X) (fun a : Fin n => r ≤ a.val)
      (fun a ha b hb => red_zero _ hq red _ (by rw [← hX]; exact hll a b ha (not_le.1 hb)))] at h1
    have h2 := isUnit_of_mul_isUnit_left h1
    unfold NX.detT
    rw [RingHom.map_det]
    exact h2
  · rw [hd, intLift_coe, ← hd]
    rfl
  · unfold NG.supDiag
    rw [sum_top h]
    unfold NX.supSum
    push_cast
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · exact (hX _ _).symm
    · rfl
  · unfold NX.supSum
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · exact (hr _ _).symm
    · exact map_zero _

end Loc

end GlobalTheory.XUniRead

theorem _root_.GlobalTheory.T.complex_typePlaceCharacter_eq_superdiag_addChar_mul_lowerDet : ∀ (D : D7) (X : NExpTied D) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (kv0 : Σ kk : Fin 2, D.nd.PlG kk)
    (s : SplitPlace D.host.E) (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv0.1))
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ),
    (∀ (u : G0g D.nd) (hu : u ∈ D.nexp.U) (hu' : u ∈ Formalism.IndefR.NX.U D.nd),
      ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
        GlobalTheory.SeriesTie.sideEmb D.ntw i b ((psiUOf D.nd (NX.xiRed D) θ ⟨u, hu'⟩ : (↥D.LL0)ˣ) : ↥D.LL0)) →
    ∀ (τ : (ZMod (D.host.g kv0.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (τ' : (ZMod (D.host.g kv0.1))ˣ →* (↥D.LL0)ˣ),
    (∀ x, ((τ x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) = GlobalTheory.SeriesTie.sideEmb D.ntw i b ((τ' x : (↥D.LL0)ˣ) : ↥D.LL0)) →
    ∀ (e : NX.Kk D i k →+* ℂ), SideRead i b k e →
    ∀ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ),
    (2 ≤ D.R.r → ∀ y : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E),
      ψ₀ (y : s.v.adicCompletion (maximalRealSubfield D.host.E)) =
        embLL0 D ((θ kv0.1 (Multiplicative.ofAdd (NX.xiRed D kv0 * red y)) : (↥D.LL0)ˣ) : ↥D.LL0)) →
    ∀ (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ),
    (∀ (y : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) (hy : IsUnit (red y))
      (uu : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ), (uu : s.v.adicCompletion (maximalRealSubfield D.host.E)) = y →
        ((ξ uu : ℂˣ) : ℂ) = embLL0 D ((τ' hy.unit : (↥D.LL0)ˣ) : ↥D.LL0)) →
    ∀ (x : GL (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))), NG.UniRT s D.R.r x →
    ∀ uu : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ,
      (uu : s.v.adicCompletion (maximalRealSubfield D.host.E)) = NG.detDD s D.R.r x →
      e (NX.gVal D i k b kv0 s red τ (x : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E)))) =
        ψ₀ (NG.supDiag s D.R.r x) * ((ξ uu : ℂˣ) : ℂ) := by
  intro D X i k b kv0 s red θ hpsi τ τ' hτ e he ψ₀ hψ₀ ξ hξ x hx uu huu
  classical
  obtain ⟨h1, h2, h3, y, hy, hry⟩ := GlobalTheory.XUniRead.loc_read s (n := D.R.nV) (Nat.le_add_right D.R.r D.R.t : D.R.r ≤ D.R.nV)
    (D.host.g_prime kv0.1) red x hx
  unfold NX.gVal
  erw [dite_eq_left h2]
  rw [map_mul, hτ, he, hξ _ h2 uu (huu.trans h3.symm)]
  congr 1
  generalize hM : NX.redMat s.v red (NX.topR (Nat.le_add_right D.R.r D.R.t : D.R.r ≤ D.R.nV) x.val) = M
  erw [hM] at h1 hry
  have hdet : IsUnit M.det := by
    rw [Matrix.det_of_upperTriangular h1.1, Finset.prod_eq_one fun a _ => h1.2 a]
    exact isUnit_one
  have hval := NX.glOf_val M hdet
  generalize hu : (Pi.mulSingle kv0 (NX.glOf M) : G0g D.nd) = u
  have hu0 : (u kv0).val = M := by rw [← hu, Pi.mulSingle_eq_same, hval]
  have hu1 : ∀ kv, kv ≠ kv0 → (u kv).val = 1 := fun kv hkv => by rw [← hu, Pi.mulSingle_eq_of_ne hkv]; rfl
  have hm' : u ∈ Formalism.IndefR.NX.U D.nd := fun kv => by
    by_cases hkv : kv = kv0
    · subst hkv; rw [hu0]; exact h1
    · rw [hu1 kv hkv]; exact ⟨Matrix.blockTriangular_one, fun a => Matrix.one_apply_eq a⟩
  have hm : u ∈ D.nexp.U := by rw [X.U_eq]; exact hm'
  unfold NX.psiUTot
  rw [dite_eq_left hm, hpsi u hm hm', he, psiUOf_apply, Fintype.prod_eq_single kv0 (fun kv hkv => by
    rw [hu1 kv hkv, NX.supSum_one, mul_zero, ofAdd_zero, map_one]), hu0, ← hy]
  by_cases hr : 2 ≤ D.R.r
  · rw [hψ₀ hr y, hry]
  · have h0 : NG.supDiag s D.R.r x = 0 := by
      unfold NG.supDiag
      exact Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => if_neg (by omega)
    rw [hy, h0, GlobalTheory.XUniRead.supSum_small hr, mul_zero, ofAdd_zero, map_one, Units.val_one, map_one, AddChar.map_zero_eq_one]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.E0ReadOfEigenLabeling
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading

noncomputable section

namespace GlobalTheory.HeightCounting.Up.IdempotentAdelicReading


set_option maxHeartbeats 4000000 in
theorem gaL_jV {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hr : R.grp_red_L)
    (hj : R.models_jV) (j : Fin D.R.m) (hc : (R.cV j).Is) (t : T) (y : (A.fam.L j t).S.Forms)
    (l : (R.cV j).W →ₗ[ℂ] ℂ) :
    gaL (Vc D j) (R.βV j) (R.datVt j t) R.eG (RealDat.eC (A := A) (sg0 D A)) (fun g => l (R.extV j t (R.jV j t y) g)) =
      fun g => l (R.extV j t (R.jV j t (∑ a, (idemOf A.X).coeff a • (A.fam.L j t).r a y)) g) := by
  let Φ : (R.HV j t).H →ₗ[ℂ] (GA D (Vc D j) → ℂ) := l.compLeft (GA D (Vc D j)) ∘ₗ R.extV j t
  have hs : ∀ a, RealDat.eC (A := A) (sg0 D A) a = D.what₂.embLL ((idemOf A.X).coeff a) := fun a => by
    show sg0 D A _ = _
    rw [sg0, sgAt_mk D.what₂.embLL R.hv0]
  have key : ∀ a, Φ (R.jV j t ((A.fam.L j t).r a y)) =
      Formalism.IndefR.Links.actL (Vc D j) (R.βV j) (R.datVt j t) (R.eG a) (Φ (R.jV j t y)) := fun a =>
    (GlobalTheory.GoodModelVec.actL_coord R hr hj j hc t a y l).symm
  show gaL (Vc D j) (R.βV j) (R.datVt j t) R.eG (RealDat.eC (A := A) (sg0 D A)) (Φ (R.jV j t y)) =
    Φ (R.jV j t (∑ a, (idemOf A.X).coeff a • (A.fam.L j t).r a y))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  simp only [LinearMap.map_smulₛₗ, key, gaL, LinearMap.sum_apply, LinearMap.smul_apply, hs, RingHom.id_apply]
  rfl


set_option maxHeartbeats 4000000 in
theorem act_of_read {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A3.A Ks) (F : Face D A3.A) {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R F X0)
    (hg : GlobalTheory.LiftRows.Given R F) {s : ℕ} (hok : A3.A.fam.Ok s) (j : Fin D.R.m) :
    ∀ (μ : D.what₂.Tup) (t : T), Y.tup t = μ → ∀ (h : Used0 D μ) (f : D.what₂.Mt μ (j.1 + 1)) (l : (R.cV j).W →ₗ[ℂ] ℂ),
      gaL (Vc D j) (R.βV j) (R.datVt j t) R.eG (RealDat.eC (A := A3.A) (sg0 D A3.A)) (fun g => l ((Y.IL.jMt μ h j f).1 g)) =
        fun g => l ((Y.IL.jMt μ h j (D.what₂.eMt μ (j.1 + 1) f)).1 g) := by
  intro μ t ht h f l
  subst ht
  let Ψ : D.what₂.Mt (Y.tup t) (j.1 + 1) →ₗ[ℂ] (GA D (Vc D j) → ℂ) :=
    l.compLeft (GA D (Vc D j)) ∘ₗ
      ((((toLiftReal R F Y.tupT Y.hm Y.hTop Y.hinj).Amt (Y.tup t) j).subtype :
        _ →ₗ[ℂ] (GA D (Vc D j) → (R.cV j).W)) ∘ₗ (Y.IL.jMt (Y.tup t) h j).toLinearMap)
  have hΨ : ∀ f, Ψ f = fun g => l ((Y.IL.jMt (Y.tup t) h j f).1 g) := fun _ => rfl
  have hF := Y.formsL j t
  have main : gaL (Vc D j) (R.βV j) (R.datVt j t) R.eG (RealDat.eC (A := A3.A) (sg0 D A3.A)) ∘ₗ Ψ =
      Ψ ∘ₗ D.what₂.eMt (Y.tup t) (j.1 + 1) := by
    refine LinearMap.ext_on_range hF.span fun k => ?_
    have hop := hF.op_eq (Pi.single k 1)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hop ⊢
    rw [hop, hΨ, hΨ, Y.mtRead j t h, Y.mtRead j t h]
    generalize (Pi.single k 1 : Fin _ → D.what₂.LL) = x
    have hl : liftForm A3.A F.P0 F.ψ0 j t ((lE D A3.A F.P0 F.ψ0 j t).mulVec x) =
        ∑ g, (idemOf A3.A.X).coeff g • (A3.A.fam.L j t).r g (liftForm A3.A F.P0 F.ψ0 j t x) :=
      GlobalTheory.ClassSumIdentity.lvlE_lvlOp hok.conj _ ((hok.lifts j t).hpos _) _ (hok.lifts j t).act _ _ _
        (fun b => (idempotent_central _ _ A3.A.X hok.irr).2 b) x
    rw [hl]
    exact gaL_jV R hg.core.grp.red_L hg.core.models.jV j (hg.core.models.cV j) t _ l
  exact LinearMap.congr_fun main f

theorem goodIdempotent_eq_goodProjector_adelicReading {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A3.A Ks) (F : Face D A3.A) {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R F X0)
    {cf : CharFrame D} {nch : NChoice D} (tp : TupTied D cf nch) (hC : R.C = cf) (Xd : DivX D) (E : EigIdx D Xd)
    (labPi : E.Pi → A3.A.fam.base.Ix) (hbase : R.BaseW F)
    (htup : ∀ μ, Used0 D μ → R.toLevCh.xiH (Y.tupT μ) = tp.xi μ) (hg : GlobalTheory.LiftRows.Given R F) (hf : R.FullP)
    {s : ℕ} (hok : A3.A.fam.Ok s) :
    GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector (realOfRead R F Y tp hC Xd E labPi hbase htup hg hf) := by
  apply GlobalTheory.NRows.Model.unitaryRealisationReading_of_idempotent_acts_via_levelGroup
  intro μ hμ j f l
  rw [← D.nStage_trivialCharacter_compat.2]
  exact act_of_read R F Y hg hok j μ (Y.tupT μ) (Y.tupTie μ hμ) hμ f l

end GlobalTheory.HeightCounting.Up.IdempotentAdelicReading
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EnlargedBaseLb2Descent
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up.HkCopy

theorem exists_units_copy {T T' Q Q' : Type} {O : T → Type} {O' : T' → Type} [c : ∀ i, CommRing (O i)]
    [c' : ∀ i, CommRing (O' i)] (hT : T = T') (hO : HEq O O') (hc : HEq c c') (hQ : Q = Q')
    (f : ∀ (i : T) (_b : Bool) (_P : Q), (O i)ˣ) :
    ∃ f' : ∀ (i : T') (_b : Bool) (_P : Q'), (O' i)ˣ,
      ∀ (i : T) (i' : T') (b : Bool) (P : Q) (P' : Q'), HEq i i' → HEq P P' → HEq (f' i' b P') (f i b P) := by
  subst hT; cases hO; cases hc; subst hQ
  exact ⟨f, fun i i' b P P' hi hP => by cases hi; cases hP; rfl⟩

theorem plE_eq {R R' : Ranks} (hR : R = R') {H : Host R} {H' : Host R'} (hH : HEq H H') : PlE H = PlE H' := by
  subst hR; cases hH; rfl

theorem exists_cHk_copy {D D' : D7} (h : GlobalTheory.TwistChoice.SameExport D D')
    (f : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ) :
    ∃ f' : ∀ (i : D'.ntw.Tw) (_b : Bool) (_P : PlE D'.host), (D'.ntw.O i)ˣ,
      ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw) (b : Bool) (P : PlE D.host) (P' : PlE D'.host), HEq i i' → HEq P P' →
        HEq (f' i' b P') (f i b P) :=
  exists_units_copy (eq_of_heq h.set.Tw) h.set.O h.set.crO (plE_eq h.gal.R h.gal.host) f

end GlobalTheory.HeightCounting.Up.HkCopy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedReadingsRelatedLocalizedAdelicDataStatement
section
theorem GlobalTheory.T.normalisedReadings_related_localizedAdelicData :
    type_of% @GlobalTheory.HeightCounting.Fin3.yRel_of_pin :=
  @GlobalTheory.HeightCounting.Fin3.yRel_of_pin
end

