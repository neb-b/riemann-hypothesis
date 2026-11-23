module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorsKilledHeisenbergAverageIsotropic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1136
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0766
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1220
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsElemStdLatticeSandwichSplitSupport
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.SuppLatStd

theorem exists_mem_only {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E)) :
    ∃ b : 𝓞 E, b ≠ 0 ∧ b ∈ Q.asIdeal ∧ ∀ P : Ideal (𝓞 E), P.IsPrime → b ∈ P → P = Q.asIdeal := by
  have hQ0 : Q.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero Q.ne_bot
  have hH : Fintype.card (ClassGroup (𝓞 E)) ≠ 0 := Fintype.card_ne_zero
  have hp : (Q.asIdeal ^ Fintype.card (ClassGroup (𝓞 E))).IsPrincipal := by
    refine (ClassGroup.mk0_eq_one_iff (pow_mem hQ0 _)).1 ?_
    have : (⟨Q.asIdeal ^ Fintype.card (ClassGroup (𝓞 E)), pow_mem hQ0 _⟩ : nonZeroDivisors (Ideal (𝓞 E))) =
        ⟨Q.asIdeal, hQ0⟩ ^ Fintype.card (ClassGroup (𝓞 E)) := rfl
    rw [this, map_pow, pow_card_eq_one]
  obtain ⟨b, hb⟩ := hp.principal
  have hbm : b ∈ Q.asIdeal ^ Fintype.card (ClassGroup (𝓞 E)) := hb ▸ Submodule.mem_span_singleton_self b
  refine ⟨b, fun h0 => ?_, Ideal.pow_le_self hH hbm, fun P hP hbP => ?_⟩
  · rw [h0, Submodule.span_singleton_eq_bot.2 rfl] at hb
    exact pow_ne_zero _ Q.ne_bot hb
  · have hle : Q.asIdeal ^ Fintype.card (ClassGroup (𝓞 E)) ≤ P := by
      rw [hb]; exact (Ideal.span_singleton_le_iff_mem P).2 hbP
    exact (Q.isMaximal.eq_of_le hP.ne_top (hP.le_of_pow_le hle)).symm

theorem val_mul_mulVec_le {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (z : Fin n → K)
    (c : K) (hz : ∀ j, Valued.v (z j) ≤ 1) (hM : ∀ i j, Valued.v c * Valued.v (M i j) ≤ 1) (i : Fin n) :
    Valued.v (c * M.mulVec z i) ≤ 1 := by
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [← mul_assoc, map_mul, map_mul]
  exact mul_le_one' (hM i j) (hz j)

end GlobalTheory.SuppLatStd

namespace GlobalTheory.SuppLatStd


set_option maxHeartbeats 2000000 in
theorem lat_std_of_suppAt : ∀ (D : D7) (V : HSp D), V.gram = 1 → Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ (h : GA D V) (e : AE D) (Ps : Finset (Formalism.L2.DIV.Pl D.host.E)) (bad : ℕ), IsIdemSum e Ps → (∀ PP ∈ Ps, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e V h → ∃ m : 𝓞 D.host.E, m ≠ 0 ∧ Ideal.span {m} • Bridge.hLat V (finPt V h) ≤ Formalism.L2.Pj.stdLat D.host.E V.rank ∧ Ideal.span {m} • Formalism.L2.Pj.stdLat D.host.E V.rank ≤ Bridge.hLat V (finPt V h) ∧ ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → m ∈ P → P.map (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) ≠ P ∧ ((bad : ℕ) : 𝓞 D.host.E) ∉ P := by
  intro D V hg hL h e Ps bad he hbad hs
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h4 := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨hid, hcj⟩ := GlobalTheory.ConjVal.components_and_conj_valuation D ι h1 h2 h4
  obtain ⟨ev, hev⟩ : ∃ ev : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), AE D →+* Q.adicCompletion D.host.E,
      ∀ Q z, ev Q z = ι (finPart D z) Q :=
    ⟨fun Q => ((GlobalTheory.CharLocProd.evalAt Q).comp ι.toRingHom).comp (finPart D), fun _ _ => rfl⟩
  simp only [← hev] at hid hcj
  obtain ⟨⟨es, hes, hsum⟩, horth⟩ := he
  have e1 : ∀ Q ∈ Ps, ev Q e = 1 := fun Q hQ => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum, Finset.sum_eq_single Q (fun Q' h' hne => (hid _ _ (hes Q' h')).2.2 Q hne.symm)
      (fun h' => absurd hQ h'), (hid _ _ (hes Q hQ)).2.1]
  have e2 : ∀ Q, Q ∉ Ps → ev Q e = 0 := fun Q hQ => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum]
    exact Finset.sum_eq_zero fun Q' h' => (hid _ _ (hes Q' h')).2.2 Q fun hh => hQ (hh ▸ h')
  have hP : ∀ Q ∈ Ps, GlobalTheory.IdemSupport.cP Q ∉ Ps := fun Q hQ hQ' => by
    have a := congrArg (ev (GlobalTheory.IdemSupport.cP Q)) horth
    rw [map_mul, e1 _ hQ', one_mul, map_zero] at a
    have a' := hcj e Q
    rw [a, e1 Q hQ, map_zero, map_one] at a'
    exact zero_ne_one a'

  have hA1 : ∀ Q, Q ∉ Ps → GlobalTheory.IdemSupport.cP Q ∉ Ps → (ev Q).mapMatrix (mt V h) = 1 := fun Q hQ hQ' => by
    have a := hcj e (GlobalTheory.IdemSupport.cP Q)
    rw [e2 _ hQ', map_zero, GlobalTheory.ClassScalarValue.cP_cP, map_eq_zero] at a
    have hu : ev Q (e + cA D e) = 0 := by rw [map_add (f := _), e2 Q hQ, a, add_zero]
    have : (ev Q).mapMatrix (mt V h - 1) = 0 := by
      refine Matrix.ext fun i j => ?_
      change ev Q ((mt V h - 1) i j) = 0
      rw [← hs i j, map_mul, hu, zero_mul]
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this
  have hinv : ∀ Q, (ev Q).mapMatrix (mt V h) * (ev Q).mapMatrix (mt V h⁻¹) = 1 := fun Q => by
    rw [← map_mul, show mt V h * mt V h⁻¹ = 1 by unfold Formalism.L2.Theta.mt; rw [map_inv]; exact Units.mul_inv _, map_one]
  have hB1 : ∀ Q, Q ∉ Ps → GlobalTheory.IdemSupport.cP Q ∉ Ps → (ev Q).mapMatrix (mt V h⁻¹) = 1 := fun Q hQ hQ' => by
    have := hinv Q
    rwa [hA1 Q hQ hQ', one_mul] at this

  have hlog : ∀ x : WithZero (Multiplicative ℤ), ∃ n : ℕ, x ≤ WithZero.exp (n : ℤ) := fun x => by
    by_cases hx : x = 0
    · exact ⟨0, hx ▸ zero_le'⟩
    · exact ⟨(WithZero.log x).toNat, by
        rw [← WithZero.exp_log hx]; exact WithZero.exp_le_exp.2 (by rw [WithZero.log_exp]; exact Int.self_le_toNat _)⟩
  choose fn hfn using hlog
  set S := Ps ∪ Ps.image GlobalTheory.IdemSupport.cP with hS
  set f : HeightOneSpectrum (𝓞 D.host.E) × Fin V.rank × Fin V.rank → ℕ := fun p =>
    fn (Valued.v (ev p.1 (mt V h p.2.1 p.2.2))) ⊔ fn (Valued.v (ev p.1 (mt V h⁻¹ p.2.1 p.2.2))) with hf
  set N : ℕ := (S ×ˢ (Finset.univ ×ˢ Finset.univ : Finset (Fin V.rank × Fin V.rank))).sup f with hN'
  have hN : ∀ Q ∈ S, ∀ i j, Valued.v (ev Q (mt V h i j)) ≤ WithZero.exp (N : ℤ) ∧
      Valued.v (ev Q (mt V h⁻¹ i j)) ≤ WithZero.exp (N : ℤ) := by
    intro Q hQ i j
    have hle : f (Q, i, j) ≤ N := Finset.le_sup (Finset.mem_product.2 ⟨hQ, Finset.mem_product.2 ⟨Finset.mem_univ i, Finset.mem_univ j⟩⟩)
    constructor
    · exact (hfn _).trans (WithZero.exp_le_exp.2 (by exact_mod_cast le_sup_left.trans hle))
    · exact (hfn _).trans (WithZero.exp_le_exp.2 (by exact_mod_cast le_sup_right.trans hle))
  have hout : ∀ Q, Q ∉ S → Q ∉ Ps ∧ GlobalTheory.IdemSupport.cP Q ∉ Ps := fun Q hQ =>
    ⟨fun h' => hQ (Finset.mem_union_left _ h'), fun h' => hQ (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨_, h', GlobalTheory.ClassScalarValue.cP_cP Q⟩))⟩

  choose b hb0 hbQ hbP using fun Q : HeightOneSpectrum (𝓞 D.host.E) => exists_mem_only Q
  set m : 𝓞 D.host.E := (∏ Q ∈ S, b Q) ^ N with hm
  have hm1 : ∀ Q : HeightOneSpectrum (𝓞 D.host.E),
      Valued.v (algebraMap D.host.E (Q.adicCompletion D.host.E) (algebraMap (𝓞 D.host.E) D.host.E m)) ≤ 1 :=
    fun Q => (GlobalTheory.CharLocProd.val_algebraMap Q _).trans_le (Q.valuation_le_one m)
  have hmN : ∀ Q ∈ S, Valued.v (algebraMap D.host.E (Q.adicCompletion D.host.E)
      (algebraMap (𝓞 D.host.E) D.host.E m)) ≤ WithZero.exp (-(N : ℤ)) := fun Q hQ => by
    rw [GlobalTheory.CharLocProd.val_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    refine (HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).2 (Ideal.pow_mem_pow ?_ N)
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem b hQ
    rw [hc]; exact Ideal.mul_mem_right _ _ (hbQ Q)
  have hone : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (i j : Fin V.rank),
      Valued.v ((1 : Matrix (Fin V.rank) (Fin V.rank) K) i j) ≤ 1 := fun i j => by
    rw [Matrix.one_apply]; split_ifs <;> simp
  have hcond : ∀ Q i j, Valued.v (algebraMap D.host.E (Q.adicCompletion D.host.E) (algebraMap (𝓞 D.host.E) D.host.E m)) *
      Valued.v (ev Q (mt V h i j)) ≤ 1 ∧
      Valued.v (algebraMap D.host.E (Q.adicCompletion D.host.E) (algebraMap (𝓞 D.host.E) D.host.E m)) *
      Valued.v (ev Q (mt V h⁻¹ i j)) ≤ 1 := fun Q i j => by
    by_cases hQ : Q ∈ S
    · have k : WithZero.exp (-(N : ℤ)) * WithZero.exp (N : ℤ) = 1 := by
        rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
      exact ⟨(mul_le_mul' (hmN Q hQ) (hN Q hQ i j).1).trans k.le, (mul_le_mul' (hmN Q hQ) (hN Q hQ i j).2).trans k.le⟩
    · obtain ⟨o1, o2⟩ := hout Q hQ
      have a1 : ev Q (mt V h i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) (Q.adicCompletion D.host.E)) i j :=
        congrFun (congrFun (hA1 Q o1 o2) i) j
      have a2 : ev Q (mt V h⁻¹ i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) (Q.adicCompletion D.host.E)) i j :=
        congrFun (congrFun (hB1 Q o1 o2) i) j
      rw [a1, a2]
      exact ⟨mul_le_one' (hm1 Q) (hone i j), mul_le_one' (hm1 Q) (hone i j)⟩

  have hmat : ∀ Q, ((Matrix.GeneralLinearGroup.map ι.toRingHom (finPt V h).1)⁻¹).1.map (GlobalTheory.CharLocProd.evalAt Q) =
      (ev Q).mapMatrix (mt V h⁻¹) := fun Q => by
    rw [← map_inv, ← Subgroup.coe_inv, ← map_inv]
    refine Matrix.ext fun i j => ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply, hev]
    rfl
  have memG : ∀ x, x ∈ Bridge.hLat V (finPt V h) ↔ ∀ i (Q : HeightOneSpectrum (𝓞 D.host.E)), Valued.v ((((ev Q).mapMatrix (mt V h⁻¹)).mulVec
      (fun j => algebraMap D.host.E (Q.adicCompletion D.host.E) (x j))) i) ≤ 1 := fun x => by
    rw [GlobalTheory.ClassScalarValue.mem_hLat ι h1 h2 V hL (finPt V h) x]
    refine forall_congr' fun i => forall_congr' fun Q => ?_
    rw [← hmat Q]
    have := RingHom.map_mulVec (GlobalTheory.CharLocProd.evalAt Q) ((Matrix.GeneralLinearGroup.map ι.toRingHom (finPt V h).1)⁻¹).1
      (fun j => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (x j)) i
    exact iff_of_eq (congrArg (fun w => Valued.v w ≤ 1) this)
  have memS : ∀ x, x ∈ Formalism.L2.Pj.stdLat D.host.E V.rank ↔
      ∀ i (Q : HeightOneSpectrum (𝓞 D.host.E)), Valued.v (algebraMap D.host.E (Q.adicCompletion D.host.E) (x i)) ≤ 1 := fun x => by
    rw [← hL, GlobalTheory.ClassScalarValue.mem_hLat ι h1 h2 V hL 1 x]
    simp only [OneMemClass.coe_one, map_one, inv_one, Units.val_one, Matrix.one_mulVec]
    rfl
  have hsm : ∀ (x : Fin V.rank → D.host.E) i, (m • x) i = algebraMap (𝓞 D.host.E) D.host.E m * x i := fun x i => by
    rw [Pi.smul_apply, Algebra.smul_def]
  refine ⟨m, pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun Q _ => hb0 Q), ?_, ?_, ?_⟩
  · refine Submodule.smul_le.2 fun r hr x hx => ?_
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [mul_smul]
    refine Submodule.smul_mem _ a ((memS _).2 fun i Q => ?_)
    have hx' := (memG x).1 hx
    have e3 : algebraMap D.host.E (Q.adicCompletion D.host.E) ((m • x) i) =
        algebraMap D.host.E (Q.adicCompletion D.host.E) (algebraMap (𝓞 D.host.E) D.host.E m) *
          ((ev Q).mapMatrix (mt V h)).mulVec (((ev Q).mapMatrix (mt V h⁻¹)).mulVec
            (fun j => algebraMap D.host.E (Q.adicCompletion D.host.E) (x j))) i := by
      rw [Matrix.mulVec_mulVec, hinv Q, Matrix.one_mulVec, hsm, map_mul]
    rw [e3]
    exact GlobalTheory.SuppLatStd.val_mul_mulVec_le _ _ _ (fun j => hx' j Q) (fun i j => (hcond Q i j).1) i
  · refine Submodule.smul_le.2 fun r hr x hx => ?_
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [mul_smul]
    refine Submodule.smul_mem _ a ((memG _).2 fun i Q => ?_)
    have hx' := (memS x).1 hx
    have e3 : (fun j => algebraMap D.host.E (Q.adicCompletion D.host.E) ((m • x) j)) =
        algebraMap D.host.E (Q.adicCompletion D.host.E) (algebraMap (𝓞 D.host.E) D.host.E m) •
          (fun j => algebraMap D.host.E (Q.adicCompletion D.host.E) (x j)) := funext fun j => by
      rw [hsm, map_mul]; rfl
    rw [e3, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    exact GlobalTheory.SuppLatStd.val_mul_mulVec_le _ _ _ (fun j => hx' j Q) (fun i j => (hcond Q i j).2) i
  · have hmap : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q →
        Q.asIdeal.map (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) ≠ Q.asIdeal := fun Q hne heq => by
      refine hne (HeightOneSpectrum.ext ?_)
      rw [← heq]
      ext x
      rw [GlobalTheory.IdemSupport.mem_cP]
      have hle : Q.asIdeal.map (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤
          Q.asIdeal.comap (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
        Ideal.map_le_iff_le_comap.2 fun y hy => by
          rw [Ideal.mem_comap, Ideal.mem_comap]; simpa [GlobalTheory.IdemSupport.cO_cO] using hy
      constructor
      · intro hx
        simpa [GlobalTheory.IdemSupport.cO_cO] using
          Ideal.mem_map_of_mem (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) hx
      · intro hx
        simpa using hle hx
    intro P hPp hmP
    obtain ⟨Q, hQS, hbQP⟩ := (hPp.prod_mem_iff).1 (hPp.mem_of_pow_mem _ hmP)
    obtain rfl := hbP Q P hPp hbQP
    rcases Finset.mem_union.1 hQS with hQ | hQ
    · exact ⟨hmap Q fun hc => hP Q hQ (by rw [hc]; exact hQ), hbad Q hQ⟩
    · obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.1 hQ
      refine ⟨hmap _ fun hc => hP Q' hQ' ?_, fun hm' => hbad Q' hQ' ?_⟩
      · rw [GlobalTheory.ClassScalarValue.cP_cP] at hc
        rw [← hc]; exact hQ'
      · rwa [GlobalTheory.IdemSupport.mem_cP, map_natCast] at hm'

end GlobalTheory.SuppLatStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentPlaceChartFiniteAdeles
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

namespace GlobalTheory.DownLift.SplitCoef

variable {D : D7}

theorem toEAf_idem_mul_eq_zero {e : AE D} (he : IsSplitIdem D e) (a : AE D) :
    toEAf D (e * a) = 0 ↔ e * a = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  apply GlobalTheory.SplitScalar.adele_ext
  · rw [map_mul, GlobalTheory.SplitScalar.infPart_splitIdem he, zero_mul, map_zero]
  · rw [map_zero]
    change (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E) (finPart D (e * a)) = 0 at h
    exact (map_eq_zero_iff _ (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective).1 h

theorem residue_eq_zero_iff_val_lt {v : HeightOneSpectrum (𝓞 D.host.F)} (o : GlobalTheory.SplitHecke.Ov D v) :
    IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v) o = 0 ↔ Valued.v (o : Fv D.host.F v) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  exact ⟨fun h => lt_of_le_of_ne o.2 h, fun h => h.ne⟩


set_option maxHeartbeats 1000000 in
theorem exists_levChart : ∀ (D : D7) (e : AE D) (PP : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e PP →
    ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v)
      (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)), LevChart e PP v φ ι := by
  intro D e PP he
  obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart e he.1
  obtain ⟨φ, hφ, hres⟩ := GlobalTheory.ThetaSupport.exists_chart_levels he hπ
  obtain ⟨hi, hi1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D e PP he
  have hπe : π e = 1 := by
    have h0 : π (1 - e) = 0 := (hπ.2.1 _).2 (by rw [mul_sub, mul_one, he.1.1, sub_self])
    rw [map_sub, map_one, sub_eq_zero] at h0
    exact h0.symm
  have hint_iff : ∀ a : AE D, toEAf D (e * a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      π a ∈ v.adicCompletionIntegers D.host.F := by
    intro a
    rw [← GlobalTheory.SplitHecke.isInt_Ov, ← hπ.2.2.2 a]
    exact ⟨GlobalTheory.PlaceDatum.finPart_mem_of_toEAf, GlobalTheory.IdemRes.toEAf_mem_of_finPart⟩
  have hsurj : Function.Surjective φ := fun y => by
    obtain ⟨a, ha⟩ := hπ.1 y
    exact ⟨toEAf D a, by rw [hφ, ha]⟩
  have hint : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, φ s ∈ v.adicCompletionIntegers D.host.F := by
    intro s
    obtain ⟨a, ha⟩ := GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) (s : Formalism.IndefR.Datum.EAf D)
    rw [← ha, hφ, ← hint_iff, map_mul, ha]
    exact mul_mem hi s.2
  let g : Formalism.L2.Herm.intAf D.host.F D.host.E →+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) :=
    (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)).comp
      ((φ.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).codRestrict (v.adicCompletionIntegers D.host.F) hint)
  have hg : ∀ s, g s = IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v) ⟨φ s, hint s⟩ := fun s => rfl
  have hrsurj : Function.Surjective (resS D.host.F PP) := fun q => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨_, resS_oToS PP x⟩
  have hker : RingHom.ker (resS D.host.F PP) ≤ RingHom.ker g := fun s hs => by
    rw [RingHom.mem_ker] at hs ⊢
    rw [hg, residue_eq_zero_iff_val_lt]
    exact hres s hs
  let ι₀ : kP PP →+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) :=
    RingHom.liftOfRightInverse (resS D.host.F PP) (Function.surjInv hrsurj) (Function.rightInverse_surjInv hrsurj) ⟨g, hker⟩
  have hι₀ : ∀ s, ι₀ (resS D.host.F PP s) = g s := fun s =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ s
  haveI := PP.isMaximal
  letI : Field (kP PP) := Ideal.Quotient.field PP.asIdeal
  have hbij : Function.Bijective ι₀ := by
    refine ⟨RingHom.injective ι₀, fun r => ?_⟩
    obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨z, hz⟩ := hsurj (o : Fv D.host.F v)
    obtain ⟨a, rfl⟩ := GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) z
    have hm : toEAf D e * toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [← map_mul, hint_iff, ← hφ, hz]
      exact o.2
    refine ⟨resS D.host.F PP ⟨_, hm⟩, ?_⟩
    rw [hι₀, hg]
    congr 1
    apply Subtype.ext
    show φ (toEAf D e * toEAf D a) = (o : Fv D.host.F v)
    rw [map_mul, hz, hφ e, hπe, one_mul]
  refine ⟨v, φ, RingEquiv.ofBijective ι₀ hbij, hsurj, fun z => ?_, fun z => ?_, fun s o ho => ?_⟩
  · obtain ⟨a, rfl⟩ := GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) z
    rw [hφ, hπ.2.1, ← map_mul, toEAf_idem_mul_eq_zero he.1]
  · obtain ⟨a, rfl⟩ := GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) z
    rw [← map_mul, hint_iff, hφ]
  · change ι₀ (resS D.host.F PP s) = _
    rw [hι₀, hg]
    congr 1
    exact Subtype.ext ho.symm

end GlobalTheory.DownLift.SplitCoef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsHalfIdem
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.SingleDatum

theorem exists_isHalfIdem : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (l : Geo.Tor.Level H), ∃ e : AE D, IsHalfIdem l e := by
  intro D H l
  classical
  have hbar : ∀ x : 𝓞 D.host.E, H.bar x = GlobalTheory.IdemSupport.cO D x := fun x =>
    RingOfIntegers.ext (by rw [H.bar_eq, GlobalTheory.IdemSupport.cO_coe]; rfl)
  have key : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), l.Mb ≤ Q.asIdeal → ¬ l.Mb ≤ (GlobalTheory.IdemSupport.cP Q).asIdeal := by
    intro Q h1 h2
    apply Q.isPrime.ne_top
    rw [eq_top_iff, ← l.coprime]
    refine sup_le h1 (Ideal.map_le_iff_le_comap.2 fun x hx => ?_)
    have h3 := h2 hx
    rw [GlobalTheory.IdemSupport.mem_cP] at h3
    rw [Ideal.mem_comap, RingHom.coe_coe, hbar]
    exact h3
  have hne : l.Mb ≠ ⊥ := by
    intro h
    have h1 := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h1
    have h2 : (l.M : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by have := l.three_le; omega)
    exact h2 h1
  have hfin : {Q : HeightOneSpectrum (𝓞 D.host.E) | l.Mb ≤ Q.asIdeal}.Finite :=
    (Ideal.finite_factors (I := l.Mb) (by rwa [Ideal.zero_eq_bot])).subset fun Q hQ => Ideal.dvd_iff_le.2 hQ
  refine (GlobalTheory.GridIdem.exists_isIdemSum hfin.toFinset ?_ ?_).imp fun e he => ⟨hfin.toFinset, he, fun PP => hfin.mem_toFinset⟩
  · intro Q hQ
    rw [Set.Finite.mem_toFinset] at hQ
    refine GlobalTheory.Hk3.SplitMatch.exists_isIdemAt fun h => key Q hQ fun x hx => ?_
    rw [GlobalTheory.IdemSupport.mem_cP]
    have h4 : Formalism.DivisionValues.cO D.host.E x ∈ (Formalism.DivisionValues.conjPl Q).asIdeal := Ideal.mem_map_of_mem _ (hQ hx)
    rw [h] at h4
    exact h4
  · intro Q hQ Q' hQ' hu
    rw [Set.Finite.mem_toFinset] at hQ hQ'
    rcases GlobalTheory.IdemSupport.eq_or_eq_cP hu with h | h
    · exact h
    · exact absurd (by rw [← h]; exact hQ) (key Q' hQ')

end GlobalTheory.SingleDatum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdeleCMMemIntegralOfIdempotent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.IdemFin

theorem toEAf_mem_intAf_of_idem : ∀ {D : D7} {e : AE D}, e * e = e → toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D e he
  have h1 : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he]
  exact GlobalTheory.LevSplit.swapAE_int (GlobalTheory.AdIdem.idempotent_mem_intAE D _ h1)

end GlobalTheory.IdemFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentAddConjSupportFinitePrimeToP
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.StdAtPrime

namespace GlobalTheory

theorem idemSum_add_conj_support_finite : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ (e : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt e P → infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) → (∀ (z : AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)), Valued.v (ι (finPart D (cA D z)) (GlobalTheory.IdemSupport.cP Q)) = Valued.v (ι (finPart D z) Q)) → ∀ (p : ℕ) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → (∀ PP ∈ P, (p : 𝓞 D.host.E) ∉ PP.asIdeal) → ∃ S : Set (HeightOneSpectrum (𝓞 D.host.E)), S.Finite ∧ (∀ Q ∈ S, (p : 𝓞 D.host.E) ∉ Q.asIdeal) ∧ ∀ Q ∉ S, ι (finPart D (e + cA D e)) Q = 0 := by
  intro D ι hid hcj p e P he hp
  classical
  obtain ⟨ev, hev⟩ : ∃ ev : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), AE D →+* Q.adicCompletion D.host.E,
      ∀ Q z, ev Q z = ι (finPart D z) Q :=
    ⟨fun Q => ((GlobalTheory.CharLocProd.evalAt Q).comp ι.toRingHom).comp (finPart D), fun _ _ => rfl⟩
  simp only [← hev] at hid hcj ⊢
  obtain ⟨⟨es, hes, hsum⟩, horth⟩ := he
  have e2 : ∀ Q, Q ∉ P → ev Q e = 0 := fun Q hQ => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum]
    exact Finset.sum_eq_zero fun Q' h' => (hid _ _ (hes Q' h')).2.2 Q fun hh => hQ (hh ▸ h')
  refine ⟨↑P ∪ GlobalTheory.IdemSupport.cP '' ↑P, P.finite_toSet.union (P.finite_toSet.image _), ?_, ?_⟩
  · rintro Q (hQ | ⟨Q', hQ', rfl⟩)
    · exact hp Q hQ
    · rw [GlobalTheory.IdemSupport.mem_cP, map_natCast]
      exact hp Q' hQ'
  · intro Q hQ
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_image, not_or, not_exists, not_and] at hQ
    have h1 : Q ∉ P := hQ.1
    have h2 : GlobalTheory.IdemSupport.cP Q ∉ P := fun h => hQ.2 _ h (GlobalTheory.ClassScalarValue.cP_cP Q)
    have a := hcj e (GlobalTheory.IdemSupport.cP Q)
    rw [e2 _ h2, map_zero, GlobalTheory.ClassScalarValue.cP_cP, map_eq_zero] at a
    rw [map_add (f := _), e2 Q h1, a, add_zero]

end GlobalTheory
end

