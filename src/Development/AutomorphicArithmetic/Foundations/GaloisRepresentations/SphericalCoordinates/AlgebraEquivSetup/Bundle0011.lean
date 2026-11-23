module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1113
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0055

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAdQEx
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

open Rat.HeightOneSpectrum GlobalTheory.NormLevelCompare in
private theorem away_iff (p : ℕ) [hp : Fact p.Prime] (w : HeightOneSpectrum ℤ) :
    w.asIdeal ≠ Ideal.span {(p : ℤ)} ↔ (p : 𝓞 ℚ) ∉ (primeCorr w).asIdeal := by
  have mem : ∀ {R : Type} [CommRing R] [Algebra R ℚ] [IsIntegralClosure R ℤ ℚ]
      (v : HeightOneSpectrum R) (n : ℕ), (n : R) ∈ v.asIdeal ↔ natGenerator v ∣ n := by
    intro R _ _ _ v n
    rw [natGenerator_dvd_iff, ← map_natCast (Rat.IsIntegralClosure.intEquiv R) n,
      Ideal.apply_mem_of_equiv_iff]
  have key : primesEquiv (primeCorr w) = primesEquiv w := by
    change primesEquiv (primesEquiv.symm (primesEquiv w)) = _
    exact Equiv.apply_symm_apply _ _
  have hg : natGenerator (primeCorr w) = natGenerator w := congrArg Subtype.val key
  rw [mem, hg, ← mem (R := ℤ)]
  refine not_congr ⟨fun h ↦ h ▸ Ideal.mem_span_singleton_self _, fun h ↦ ?_⟩
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp.out).irreducible
  exact (hmax.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 h)).symm

private theorem ringEquiv_of_algEquiv {K A B : Type*} [CommSemiring K] [Semiring A] [Semiring B]
    {_ : Algebra K A} {_ : Algebra K B} (e : A ≃ₐ[K] B) : ∃ f : A ≃+* B, ∀ x, f x = e x := ⟨e.toRingEquiv, fun _ ↦ rfl⟩

open GlobalTheory.NormLevelCompare in
private theorem exists_local_ring (w : HeightOneSpectrum ℤ) :
    ∃ e : (primeCorr w).adicCompletion ℚ ≃+* w.adicCompletion ℚ,
      ∀ x, e x ∈ w.adicCompletionIntegers ℚ ↔ x ∈ (primeCorr w).adicCompletionIntegers ℚ := by
  obtain ⟨e, he⟩ := exists_local w
  obtain ⟨f, hf⟩ := ringEquiv_of_algEquiv e
  exact ⟨f, fun x ↦ by rw [hf]; exact he x⟩

open GlobalTheory.NormLevelCompare in
private noncomputable def eL (w : HeightOneSpectrum ℤ) :
    (primeCorr w).adicCompletion ℚ ≃+* w.adicCompletion ℚ :=
  Classical.choose (exists_local_ring w)

open GlobalTheory.NormLevelCompare in
private theorem eL_mem (w : HeightOneSpectrum ℤ) (x : (primeCorr w).adicCompletion ℚ) :
    eL w x ∈ w.adicCompletionIntegers ℚ ↔ x ∈ (primeCorr w).adicCompletionIntegers ℚ := Classical.choose_spec (exists_local_ring w) x

open GlobalTheory.NormLevelCompare in
private theorem eL_mapsTo (w : HeightOneSpectrum ℤ) :
    Set.MapsTo (eL w).toRingHom ((primeCorr w).adicCompletionIntegers ℚ) (w.adicCompletionIntegers ℚ) := fun x hx ↦ (eL_mem w x).2 hx

private theorem finiteAdeleRingAway_ext {p : ℕ} {x y : AfP p} (h : ∀ v, AfP.eval v x = AfP.eval v y) : x = y := RestrictedProduct.ext _ _ h

open GlobalTheory.NormLevelCompare in
private noncomputable def rho (p : ℕ) : AfQ →+* AfP p :=
  RestrictedProduct.mapAlongRingHom (fun u : HeightOneSpectrum (𝓞 ℚ) ↦ u.adicCompletion ℚ)
    (fun v : AwayP p ↦ v.1.adicCompletion ℚ)
    (B₁ := fun u ↦ u.adicCompletionIntegers ℚ) (B₂ := fun v ↦ v.1.adicCompletionIntegers ℚ)
    (fun v ↦ primeCorr v.1) (primeCorr.injective.comp Subtype.val_injective).tendsto_cofinite
    (fun v ↦ (eL v.1).toRingHom) (hφ := .of_forall fun v ↦ eL_mapsTo v.1)

open GlobalTheory.NormLevelCompare in
private theorem eval_rho {p : ℕ} (a : AfQ) (v : AwayP p) :
    AfP.eval v (rho p a) = eL v.1 (a (primeCorr v.1)) := rfl

section
open GlobalTheory.NormLevelCompare
open scoped Classical in
private noncomputable def gL {p : ℕ} (b : AfP p) (w : HeightOneSpectrum ℤ) :
    (primeCorr w).adicCompletion ℚ :=
  if h : w.asIdeal ≠ Ideal.span {(p : ℤ)} then (eL w).symm (AfP.eval (⟨w, h⟩ : AwayP p) b) else 0

private theorem gL_pos {p : ℕ} (b : AfP p) (v : AwayP p) : gL b v.1 = (eL v.1).symm (AfP.eval v b) := by
  unfold gL
  rw [dite_eq_left v.2]
  rfl

private theorem gL_neg {p : ℕ} (b : AfP p) (w : HeightOneSpectrum ℤ)
    (h : ¬ w.asIdeal ≠ Ideal.span {(p : ℤ)}) : gL b w = 0 := by
  unfold gL
  rw [dite_eq_right h]

private theorem afP_ev {p : ℕ} (b : AfP p) :
    ∀ᶠ v : AwayP p in Filter.cofinite, AfP.eval v b ∈ v.1.adicCompletionIntegers ℚ := b.2

private theorem gL_ev {p : ℕ} (b : AfP p) : ∀ᶠ w : HeightOneSpectrum ℤ in Filter.cofinite,
    gL b w ∈ (primeCorr w).adicCompletionIntegers ℚ := by
  have hb := afP_ev b
  rw [Filter.eventually_cofinite] at hb ⊢
  refine (hb.image Subtype.val).subset ?_
  intro w hw
  by_cases h : w.asIdeal ≠ Ideal.span {(p : ℤ)}
  · refine ⟨⟨w, h⟩, ?_, rfl⟩
    intro hv
    apply hw
    rw [show gL b w = _ from gL_pos b ⟨w, h⟩]
    exact (eL_mem w _).1 (by simpa using hv)
  · exact absurd (by rw [gL_neg b w h]; exact zero_mem _) hw

private theorem exists_pi_extend {α β : Type*} (P : β → Type*) (σ : α ≃ β) (g : ∀ a, P (σ a)) :
    ∃ f : ∀ b, P b, ∀ a, f (σ a) = g a := ⟨Equiv.piCongrLeft P σ g, fun a ↦ Equiv.piCongrLeft_apply_apply P σ g a⟩

private noncomputable def fL {p : ℕ} (b : AfP p) : ∀ u : HeightOneSpectrum (𝓞 ℚ), u.adicCompletion ℚ :=
  Classical.choose (exists_pi_extend (fun u : HeightOneSpectrum (𝓞 ℚ) => u.adicCompletion ℚ) primeCorr (gL b))

private theorem fL_corr {p : ℕ} (b : AfP p) (w : HeightOneSpectrum ℤ) : fL b (primeCorr w) = gL b w := Classical.choose_spec
  (exists_pi_extend (fun u : HeightOneSpectrum (𝓞 ℚ) => u.adicCompletion ℚ) primeCorr (gL b)) w

private theorem fL_ev {p : ℕ} (b : AfP p) : ∀ᶠ u : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
    fL b u ∈ u.adicCompletionIntegers ℚ := by
  have hg := gL_ev b
  rw [Filter.eventually_cofinite] at hg ⊢
  refine (hg.image primeCorr).subset ?_
  intro u hu
  obtain ⟨w, rfl⟩ := primeCorr.surjective u
  refine ⟨w, ?_, rfl⟩
  intro hw
  apply hu
  rw [fL_corr]
  exact hw

private noncomputable def liftA {p : ℕ} (b : AfP p) : AfQ := ⟨fL b, fL_ev b⟩

private theorem liftA_apply {p : ℕ} (b : AfP p) (u : HeightOneSpectrum (𝓞 ℚ)) : liftA b u = fL b u := rfl

private theorem rho_surj (p : ℕ) : Function.Surjective (rho p) := by
  intro b
  refine ⟨liftA b, finiteAdeleRingAway_ext fun v ↦ ?_⟩
  rw [eval_rho, liftA_apply, fL_corr, gL_pos, RingEquiv.apply_symm_apply]
end

open GlobalTheory.NormLevelCompare in
private theorem rho_ker (p : ℕ) [Fact p.Prime] (a : AfQ) :
    rho p a = 0 ↔ ∀ v : Plc ℚ, (p : 𝓞 ℚ) ∉ v.asIdeal → a v = 0 := by
  constructor
  · intro h v hv
    obtain ⟨w, rfl⟩ := primeCorr.surjective v
    have h2 : eL w (a (primeCorr w)) = 0 :=
      (congrArg (AfP.eval (⟨w, (away_iff p w).2 hv⟩ : AwayP p)) h).trans (map_zero _)
    exact (map_eq_zero_iff _ (eL w).injective).1 h2
  · intro h
    refine finiteAdeleRingAway_ext fun v ↦ ?_
    rw [eval_rho, map_zero, h _ ((away_iff p v.1).1 v.2), map_zero]

open GlobalTheory.NormLevelCompare in
private theorem rho_int (p : ℕ) [Fact p.Prime] (a : AfQ) :
    IsIntAf (rho p a) ↔ ∀ v : Plc ℚ, (p : 𝓞 ℚ) ∉ v.asIdeal → Valued.v (a v) ≤ 1 := by
  constructor
  · intro h v hv
    obtain ⟨w, rfl⟩ := primeCorr.surjective v
    have h2 : eL w (a (primeCorr w)) ∈ w.adicCompletionIntegers ℚ := h ⟨w, (away_iff p w).2 hv⟩
    rw [eL_mem] at h2
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h2
  · intro h v
    show AfP.eval v (rho p a) ∈ _
    rw [eval_rho, eL_mem]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h _ ((away_iff p v.1).1 v.2))

theorem UpperTheory.Gal.W2.Seed.pAdQEx :
    AdQEx := fun p _ ↦ ⟨⟨rho p, rho_surj p, rho_ker p, rho_int p⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAdTEx
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pAdTEx :
    AdQEx → AdTensor → IdemP → AdTEx := by
  intro hQ hT hI p _ E _ _ _
  obtain ⟨Q⟩ := hQ p
  obtain ⟨ι, h1, h2, h3⟩ := hT E
  obtain ⟨e, he, he'⟩ := hI p E
  let M : AfQ ⊗[ℚ] E →ₐ[ℚ] AfP p ⊗[ℚ] E :=
    Algebra.TensorProduct.map Q.ρ.toRatAlgHom (AlgHom.id ℚ E)
  have hM : ∀ (a : AfQ) (x : E), M (a ⊗ₜ x) = Q.ρ a ⊗ₜ x := fun a x => rfl
  have hρe : Q.ρ e = 0 := (Q.ker e).2 fun v hv => (he v).2 hv
  have hιa : ∀ a : AfQ, ι (a ⊗ₜ 1) = finiteAdeleMap ℚ E a := fun a => by
    rw [h1, map_one, mul_one]
  have hιE : ∀ x : E, ι (1 ⊗ₜ x) = algebraMap E (Af E) x := fun x => by
    rw [h1, map_one, one_mul]

  have hMker : ∀ y, M y = 0 → (e ⊗ₜ[ℚ] (1 : E)) * y = y := by
    intro y hy
    let b := Module.finBasis ℚ E
    obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_right b y
    have hc0 : (c.mapRange Q.ρ (map_zero _)).sum (fun i m => m ⊗ₜ[ℚ] b i) = 0 := by
      rw [Finsupp.sum_mapRange_index (by simp)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hy, Finsupp.sum, Finsupp.sum, map_sum]
      rfl
    have hc := TensorProduct.sum_tmul_basis_right_eq_zero b _ hc0
    have hci : ∀ i, e * c i = c i := by
      intro i
      have hi : Q.ρ (c i) = 0 := by
        have := DFunLike.congr_fun hc i
        simpa using this
      have hv := (Q.ker (c i)).1 hi
      refine Subtype.ext (funext fun v => ?_)
      by_cases hp : (p : 𝓞 ℚ) ∈ v.asIdeal
      · show e v * c i v = c i v
        rw [(he v).1 hp, one_mul]
      · show e v * c i v = c i v
        rw [hv v hp, mul_zero]
    rw [Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hci]

  have hιe : ι (e ⊗ₜ 1) = finiteAdeleMap ℚ E e := hιa e
  have hMe : M (e ⊗ₜ 1) = 0 := by rw [hM, hρe, TensorProduct.zero_tmul]
  have hMker' : ∀ x : Af E, M (ι.symm x) = 0 ↔
      ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → pLoc E w x = 0 := by
    intro x
    constructor
    · intro h w hw
      have h' := congrArg ι (hMker _ h)
      rw [map_mul, hιe, ι.apply_symm_apply] at h'
      rw [← h', map_mul, (he' w).2 hw, zero_mul]
    · intro h
      have hx : finiteAdeleMap ℚ E e * x = x := by
        refine GlobalTheory.EulerTw.pLoc_ext E fun w => ?_
        by_cases hp : (p : 𝓞 E) ∈ w.asIdeal
        · rw [map_mul, (he' w).1 hp, one_mul]
        · rw [map_mul, (he' w).2 hp, zero_mul, h w hp]
      rw [← hx, ← hιe, map_mul ι.symm, ι.symm_apply_apply, map_mul, hMe, zero_mul]
  have hgen : ∀ (a : AfP p) (c : 𝓞 E), IsIntAf a →
      ∃ y ∈ AddSubgroup.closure {y : AfQ ⊗[ℚ] E | ∃ (a : AfQ) (x : 𝓞 E),
        (∀ v : Plc ℚ, Valued.v (a v) ≤ 1) ∧ y = a ⊗ₜ (x : E)}, M y = a ⊗ₜ (c : E) := by
    intro a c ha
    obtain ⟨b, rfl⟩ := Q.surj a
    have hb := (Q.int b).1 ha
    refine ⟨((1 - e) * b) ⊗ₜ (c : E), AddSubgroup.subset_closure ⟨_, c, ?_, rfl⟩, ?_⟩
    · intro v
      by_cases hp : (p : 𝓞 ℚ) ∈ v.asIdeal
      · have : ((1 - e) * b) v = (1 - e v) * b v := rfl
        rw [this, (he v).1 hp, sub_self, zero_mul, map_zero]
        exact zero_le
      · have : ((1 - e) * b) v = (1 - e v) * b v := rfl
        rw [this, (he v).2 hp, sub_zero, one_mul]
        exact hb v hp
    · rw [hM, map_mul, map_sub, map_one, hρe, sub_zero, one_mul]
  have hMs : Function.Surjective M := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a x =>
      obtain ⟨b, rfl⟩ := Q.surj a
      exact ⟨b ⊗ₜ x, rfl⟩
    | add u v hu hv =>
      obtain ⟨u', rfl⟩ := hu
      obtain ⟨v', rfl⟩ := hv
      exact ⟨u' + v', map_add _ _ _⟩
  have hO : ∀ z ∈ OHat p E, ∃ y ∈ AddSubgroup.closure {y : AfQ ⊗[ℚ] E | ∃ (a : AfQ) (x : 𝓞 E),
      (∀ v : Plc ℚ, Valued.v (a v) ≤ 1) ∧ y = a ⊗ₜ (x : E)}, M y = z := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, c, ha, rfl⟩ := hz
      exact hgen a c ha
    | zero => exact ⟨0, zero_mem _, map_zero _⟩
    | add u v _ _ hu hv =>
      obtain ⟨u', hu', rfl⟩ := hu
      obtain ⟨v', hv', rfl⟩ := hv
      exact ⟨u' + v', add_mem hu' hv', map_add _ _ _⟩
    | neg u _ hu =>
      obtain ⟨u', hu', rfl⟩ := hu
      exact ⟨-u', neg_mem hu', map_neg _ _⟩
  have hC : ∀ y ∈ AddSubgroup.closure {y : AfQ ⊗[ℚ] E | ∃ (a : AfQ) (x : 𝓞 E),
      (∀ v : Plc ℚ, Valued.v (a v) ≤ 1) ∧ y = a ⊗ₜ (x : E)}, M y ∈ OHat p E := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, c, ha, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨Q.ρ a, c, (Q.int a).2 fun v _ => ha v, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
    | neg u _ hu => rw [map_neg]; exact neg_mem hu
  exact ⟨{ toAdQ := Q
           Φ := (M : AfQ ⊗[ℚ] E →+* AfP p ⊗[ℚ] E).comp (ι.symm : Af E →+* AfQ ⊗[ℚ] E)
           Φ_E := fun x => by
            show M (ι.symm _) = _
            rw [← hιE, ι.symm_apply_apply, hM, map_one]
           Φ_Q := fun a => by
            show M (ι.symm _) = _
            rw [← hιa, ι.symm_apply_apply, hM]
           Φ_surj := fun z => by
            obtain ⟨y, rfl⟩ := hMs z
            refine ⟨ι y, ?_⟩
            show M (ι.symm (ι y)) = _
            rw [ι.symm_apply_apply]
           Φ_ker := hMker'
           Φ_int := fun x => by
            show M (ι.symm x) ∈ OHat p E ↔ _
            constructor
            · intro hx w hw
              obtain ⟨y, hy, hyz⟩ := hO _ hx
              have hd : M (ι.symm (x - ι y)) = 0 := by
                rw [map_sub, map_sub, ι.symm_apply_apply, hyz, sub_self]
              have h0 := (hMker' _).1 hd w hw
              rw [map_sub, sub_eq_zero] at h0
              rw [h0]
              exact (h2 y).1 hy w
            · intro hx
              have hz : M (ι.symm (finiteAdeleMap ℚ E e * x)) = 0 := by
                rw [← hιe, map_mul ι.symm, ι.symm_apply_apply, map_mul, hMe, zero_mul]
              have hi : ι.symm (x - finiteAdeleMap ℚ E e * x) ∈ AddSubgroup.closure
                  {y : AfQ ⊗[ℚ] E | ∃ (a : AfQ) (x : 𝓞 E),
                    (∀ v : Plc ℚ, Valued.v (a v) ≤ 1) ∧ y = a ⊗ₜ (x : E)} := by
                refine (h2 _).2 fun w => ?_
                rw [ι.apply_symm_apply, map_sub, map_mul]
                by_cases hp : (p : 𝓞 E) ∈ w.asIdeal
                · rw [(he' w).1 hp, one_mul, sub_self, map_zero]
                  exact zero_le
                · rw [(he' w).2 hp, zero_mul, sub_zero]
                  exact hx w hp
              have := hC _ hi
              rwa [map_sub, map_sub, hz, sub_zero] at this
           Φ_conj := fun x => by
            show M (ι.symm (conjFin (conjE E) x)) = conjT E (AfP p) (M (ι.symm x))
            obtain ⟨y, rfl⟩ := ι.surjective x
            rw [ι.symm_apply_apply]
            induction y using TensorProduct.inductionOn with
            | tmul a z =>
              rw [h1, map_mul, h3, conjFin_algebraMap, ← h1, ι.symm_apply_apply, hM, hM, conjT_tmul]
              rfl
            | add u v hu hv =>
              simp only [map_add (f := _), hu, hv] }⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAdTensor
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

noncomputable section

namespace UpperTheory.Gal.W2.Seed

open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap below)
open GroundTheory.Global.SemiLocal (completionMap)

private theorem eq_zero_of_small {E : Type} [Field E] [NumberField E] {w : Plc E}
    (z : w.adicCompletion E) (h : ∀ n : ℕ, Valued.v z ≤ WithZero.exp (-(n : ℤ))) : z = 0 := by
  by_contra hz
  have h0 : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).2 hz
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v z = WithZero.exp m :=
    ⟨WithZero.log _, (WithZero.exp_log h0).symm⟩
  have := h (1 - m).toNat
  rw [hm, WithZero.exp_le_exp] at this
  omega

private theorem valued_completionMap_le {E : Type} [Field E] [NumberField E] (P : Plc E)
    (t : (below ℚ P).adicCompletion ℚ) (n : ℕ) (ht : Valued.v t ≤ WithZero.exp (-(n : ℤ))) :
    Valued.v (completionMap (below ℚ P) P t) ≤ WithZero.exp (-(n : ℤ)) := by
  have he : P.asIdeal.ramificationIdx (𝓞 ℚ) ≠ 0 := by
    intro h0
    have h := GroundTheory.Global.SemiLocal.valued_completionMap (below ℚ P) P
      (0 : (below ℚ P).adicCompletion ℚ)
    rw [map_zero, map_zero, map_zero, h0, pow_zero] at h
    exact zero_ne_one h
  rw [GroundTheory.Global.SemiLocal.valued_completionMap]
  refine le_trans ?_ ht
  refine pow_le_of_le_one zero_le (ht.trans ?_) he
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

private theorem ringHom_eq {E : Type} [Field E] [NumberField E] (P : Plc E) (v : Plc ℚ)
    (φ ψ : v.adicCompletion ℚ →+* P.adicCompletion E)
    (hφ : ∀ (n : ℕ) (a : v.adicCompletion ℚ), Valued.v a ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (φ a) ≤ WithZero.exp (-(n : ℤ)))
    (hψ : ∀ (n : ℕ) (a : v.adicCompletion ℚ), Valued.v a ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (ψ a) ≤ WithZero.exp (-(n : ℤ))) (x : v.adicCompletion ℚ) : φ x = ψ x := by
  have aux : ∀ q : ℚ →+* v.adicCompletion ℚ, DenseRange q → φ x = ψ x := by
    intro q hd
    rw [← sub_eq_zero]
    refine eq_zero_of_small _ fun n => ?_
    have hopen : IsOpen {y : v.adicCompletion ℚ | Valued.v (y - x) ≤ WithZero.exp (-(n : ℤ))} :=
      (GlobalTheory.Idele.isOpen_valued_le (K := ℚ) v (-(n : ℤ))).preimage
        (continuous_id.sub continuous_const)
    obtain ⟨k, hk⟩ := hd.exists_mem_open hopen ⟨x, by simp⟩
    have hk' : Valued.v (q k - x) ≤ WithZero.exp (-(n : ℤ)) := by
      simpa only [Set.mem_ofPred_eq] using hk
    have h : φ (q k) = ψ (q k) := RingHom.congr_fun (Subsingleton.elim (φ.comp q) (ψ.comp q)) k
    have e : φ x - ψ x = ψ (q k - x) - φ (q k - x) := by
      rw [map_sub φ, map_sub ψ, h]
      abel
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le (hψ n _ hk') (hφ n _ hk'))
  exact aux _ (HeightOneSpectrum.denseRange_algebraMap (K := ℚ) v)

private theorem locMap_eq {E : Type} [Field E] [NumberField E] (P : Plc E)
    (x : (below ℚ P).adicCompletion ℚ) :
    GlobalTheory.AdeleBaseChange.locMap ℚ P x = completionMap (below ℚ P) P x :=
  ringHom_eq P (below ℚ P) (GlobalTheory.AdeleBaseChange.locMap ℚ P) (completionMap (below ℚ P) P)
    (fun n a ha => GlobalTheory.AdeleBaseChange.locMap_valued P n a ha)
    (fun n a ha => valued_completionMap_le P a n ha) x

private theorem ringHom_eq_of_continuous {R : Type} [Ring R] [TopologicalSpace R] [T2Space R]
    (v : Plc ℚ) (φ ψ : v.adicCompletion ℚ →+* R) (hφ : Continuous φ) (hψ : Continuous ψ)
    (x : v.adicCompletion ℚ) : φ x = ψ x := by
  have aux : ∀ q : ℚ →+* v.adicCompletion ℚ, DenseRange q → φ x = ψ x := fun q hd =>
    congrFun (hd.equalizer hφ hψ (funext fun k =>
      RingHom.congr_fun (Subsingleton.elim (φ.comp q) (ψ.comp q)) k)) x
  exact aux _ (HeightOneSpectrum.denseRange_algebraMap (K := ℚ) v)

private theorem adMap_eq {E : Type} [Field E] [NumberField E] (a : AfQ) :
    GlobalTheory.AdeleBaseChange.adMap ℚ E a = finiteAdeleMap ℚ E a :=
  FiniteAdeleRing.ext _ fun P => locMap_eq P _

private theorem below_conjSrc {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Plc E) :
    below ℚ (conjSrc (conjE E) w) = below ℚ w := by
  have h := conjPl_conjSrc (conjE E) w
  refine HeightOneSpectrum.ext (Ideal.ext fun y => ?_)
  change algebraMap (𝓞 ℚ) (𝓞 E) y ∈ (conjSrc (conjE E) w).asIdeal ↔ algebraMap (𝓞 ℚ) (𝓞 E) y ∈ w.asIdeal
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← h]
  have : conjE E ((algebraMap (𝓞 ℚ) (𝓞 E) y : 𝓞 E) : E) = ((algebraMap (𝓞 ℚ) (𝓞 E) y : 𝓞 E) : E) := by
    change conjE E (algebraMap ℚ E (y : ℚ)) = algebraMap ℚ E (y : ℚ)
    simp [eq_ratCast]
  rw [this]

private theorem conj_finiteAdeleMap {E : Type} [Field E] [NumberField E] [IsCMField E] (a : AfQ) :
    conjFin (conjE E) (finiteAdeleMap ℚ E a) = finiteAdeleMap ℚ E a := by
  refine GlobalTheory.EulerTw.pLoc_ext E fun w => ?_
  rw [pLoc_conjFin]
  have hb := below_conjSrc w
  have key : ∀ (u : Plc E) (_ : below ℚ u = below ℚ w) (f : u.adicCompletion E →+* w.adicCompletion E),
      Continuous f → f (pLoc E u (finiteAdeleMap ℚ E a)) = pLoc E w (finiteAdeleMap ℚ E a) := by
    intro u hu f hf
    haveI : w.asIdeal.LiesOver (below ℚ u).asIdeal := (GroundTheory.Global.AdeleBaseChange.below_eq_iff w _).1 hu.symm
    change f (completionMap (below ℚ u) u (a (below ℚ u))) = completionMap (below ℚ w) w (a (below ℚ w))
    rw [← GroundTheory.Global.AdeleBaseChange.completionMap_congr hu w a]
    exact ringHom_eq_of_continuous (below ℚ u) (f.comp (completionMap (below ℚ u) u)) (completionMap (below ℚ u) w)
      (hf.comp (GroundTheory.Global.SemiLocal.continuous_completionMap _ _))
      (GroundTheory.Global.SemiLocal.continuous_completionMap _ _) _
  exact key _ hb _ (conjLoc_spec (conjE E) w).1

end UpperTheory.Gal.W2.Seed

open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)

theorem UpperTheory.Gal.W2.Seed.pAdTensor :
    AdTensor := by
  intro E _ _ _
  obtain ⟨ι, hι⟩ := GlobalTheory.AdeleBaseChange.exists_toAd ℚ E
  let c : AfQ ⊗[ℚ] E ≃+* Formalism.L2.DIV.AfE ℚ E :=
    (Algebra.TensorProduct.comm ℚ AfQ E).toRingEquiv
  have hc : ∀ a x, c (a ⊗ₜ[ℚ] x) = x ⊗ₜ[ℚ] a := fun a x => rfl
  have hc' : ∀ a x, c.symm (x ⊗ₜ[ℚ] a) = a ⊗ₜ[ℚ] x := fun a x => rfl
  let j := c.trans (RingEquiv.ofBijective ι
    ⟨GlobalTheory.AdeleBaseChange.map_injective hι, GlobalTheory.AdeleBaseChange.map_surjective hι⟩)
  have hj : ∀ y, j y = ι (c y) := fun y => rfl
  refine ⟨j, fun a x => ?_, fun y => ⟨fun hy => ?_, fun hy => ?_⟩, conj_finiteAdeleMap⟩
  · rw [hj, hc, hι, adMap_eq, mul_comm]
  · have : j y ∈ Formalism.UG.intAd E := by
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, x, ha, rfl⟩ := hy
        rw [hj, hc]
        exact GlobalTheory.AdeleBaseChange.map_mem_int hι (Formalism.UG.P.levelaf_tmul_mem x ha)
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | neg x _ hx => rw [map_neg]; exact neg_mem hx
    exact this
  · have h : c y ∈ Formalism.L2.DIV.RInt ℚ E := GlobalTheory.AdeleBaseChange.mem_int_of_map hι hy
    obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
    obtain ⟨r, hr, e⟩ := Formalism.UG.P.levelaf_decomp g hg h
    have e' : y = c.symm (c y) := (c.symm_apply_apply y).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e', e, map_sum]
    refine sum_mem fun i _ => AddSubgroup.subset_closure ⟨r i, g i, hr i, ?_⟩
    rw [hc']
end
end

