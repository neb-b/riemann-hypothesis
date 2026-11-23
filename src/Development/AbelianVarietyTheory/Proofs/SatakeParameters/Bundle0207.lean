module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsParahoricTypeVectorAtConjugatePlace
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntegralIffSpectralNormLeOne
section
open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ClosureIso

open Polynomial

section localPart

variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F]
  {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 F)}

theorem exists_ne_zero_valued_lt_one (v : HeightOneSpectrum (𝓞 K)) :
    ∃ c : v.adicCompletion K, c ≠ 0 ∧ Valued.v c < 1 := by
  obtain ⟨x, hx⟩ := v.valuation_surjective K (WithZero.exp (-1))
  have hxv : Valued.v (algebraMap K (v.adicCompletion K) x) = WithZero.exp (-1) :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x).trans hx
  refine ⟨algebraMap K _ x, ?_, ?_⟩
  · intro h0
    rw [h0, map_zero] at hxv
    exact WithZero.exp_ne_zero hxv.symm
  · rw [hxv, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num

theorem valued_map_le_one (f : v.adicCompletion K →+* v'.adicCompletion F) (hf : Continuous f)
    {x : v.adicCompletion K} (hx : Valued.v x ≤ 1) : Valued.v (f x) ≤ 1 := by
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_valued_lt_one v
  have hN : ∀ N : ℕ, ‖f c‖ * ‖f x‖ ^ N < 1 := by
    intro N
    have h1 : Valued.v (c * x ^ N) < 1 := by
      rw [Valuation.map_mul, Valuation.map_pow]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one₀ zero_le hx)) hc1
    have h2 := GlobalTheory.ConjParahoric.val_lt_one_map f hf h1
    rw [← Valued.toNormedField.norm_lt_one_iff] at h2
    simpa [map_mul, map_pow, norm_mul, norm_pow] using h2
  by_contra hgt
  rw [← Valued.toNormedField.norm_le_one_iff, not_le] at hgt
  have hfc : 0 < ‖f c‖ := norm_pos_iff.2 ((map_ne_zero f).2 hc0)
  obtain ⟨N, hN'⟩ := pow_unbounded_of_one_lt (‖f c‖⁻¹) hgt
  have := hN N
  have h3 : 1 < ‖f c‖ * ‖f x‖ ^ N := by
    calc (1 : ℝ) = ‖f c‖ * ‖f c‖⁻¹ := (mul_inv_cancel₀ hfc.ne').symm
      _ < ‖f c‖ * ‖f x‖ ^ N := mul_lt_mul_of_pos_left hN' hfc
  linarith

def intMap (f : v.adicCompletion K →+* v'.adicCompletion F) (hf : Continuous f) :
    v.adicCompletionIntegers K →+* v'.adicCompletionIntegers F :=
  (f.comp (v.adicCompletionIntegers K).subtype).codRestrict (v'.adicCompletionIntegers F).toSubring
    (fun x => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
      (valued_map_le_one f hf ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 x.2)))

theorem isIntegral_map (f : v.adicCompletion K →+* v'.adicCompletion F) (hf : Continuous f)
    (b : Kbar v ≃+* Kbar v') (hb : ∀ x, b (algebraMap _ _ x) = algebraMap _ _ (f x)) {y : Kbar v}
    (hy : IsIntegral (v.adicCompletionIntegers K) y) :
    IsIntegral (v'.adicCompletionIntegers F) (b y) := by
  refine IsIntegral.map_of_comp_eq (intMap f hf) b.toRingHom ?_ hy
  ext x
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K) (v.adicCompletion K) (Kbar v),
    IsScalarTower.algebraMap_apply (v'.adicCompletionIntegers F) (v'.adicCompletion F) (Kbar v'), hb]
  rfl

theorem valued_le_one_of_isIntegral {x : v'.adicCompletion F}
    (hx : IsIntegral (v'.adicCompletionIntegers F) (algebraMap (v'.adicCompletion F) (Kbar v') x)) :
    Valued.v x ≤ 1 := by
  rw [isIntegral_algebraMap_iff ] at hx
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 y.2

end localPart

section spectral

variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F]
  {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 F)}

theorem isIntegral_iff_spectralNorm_le_one (y : Kbar v) :
    IsIntegral (v.adicCompletionIntegers K) y ↔ spectralNorm (v.adicCompletion K) (Kbar v) y ≤ 1 := by
  have hyK : IsIntegral (v.adicCompletion K) y := Algebra.IsIntegral.isIntegral y
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hyK)]
  constructor
  · intro hy n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' (v.adicCompletion K) hy, coeff_map]
    exact Valued.toNormedField.norm_le_one_iff.2
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((minpoly (v.adicCompletionIntegers K) y).coeff n).2)
  · intro h
    have hl : minpoly (v.adicCompletion K) y ∈
        lifts (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
        (Valued.toNormedField.norm_le_one_iff.1 (h n))⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hyK)
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap (v.adicCompletion K), hq, minpoly.aeval]

theorem exists_isIntegral_mul_inv_pow {y : Kbar v} (hy : ¬ IsIntegral (v.adicCompletionIntegers K) y)
    {c : v.adicCompletion K} (hc : c ≠ 0) :
    ∃ N : ℕ, IsIntegral (v.adicCompletionIntegers K) (algebraMap _ (Kbar v) c⁻¹ * y⁻¹ ^ N) := by
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := exists_ne_zero_valued_lt_one v
  letI : NontriviallyNormedField (v.adicCompletion K) :=
    NontriviallyNormedField.ofNormNeOne ⟨ϖ, hϖ0, (Valued.toNormedField.norm_lt_one_iff.2 hϖ1).ne⟩
  have hmul : ∀ a b : Kbar v, spectralNorm (v.adicCompletion K) (Kbar v) (a * b) =
      spectralNorm (v.adicCompletion K) (Kbar v) a * spectralNorm (v.adicCompletion K) (Kbar v) b :=
    fun a b => spectralAlgNorm_mul a b
  have hy1 : 1 < spectralNorm (v.adicCompletion K) (Kbar v) y := by
    rw [isIntegral_iff_spectralNorm_le_one, not_le] at hy
    exact hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy isIntegral_zero
  have hinv : spectralNorm (v.adicCompletion K) (Kbar v) y⁻¹ *
      spectralNorm (v.adicCompletion K) (Kbar v) y = 1 := by
    rw [← hmul, inv_mul_cancel₀ hy0, spectralNorm_one]
  have hlt : spectralNorm (v.adicCompletion K) (Kbar v) y⁻¹ < 1 := by
    rw [eq_inv_of_mul_eq_one_left hinv]
    exact inv_lt_one_of_one_lt₀ hy1
  have hc' : 0 < ‖c‖ := norm_pos_iff.2 hc
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hc' hlt
  refine ⟨n + 1, ?_⟩
  have hs0 : 0 ≤ spectralNorm (v.adicCompletion K) (Kbar v) y⁻¹ := spectralNorm_nonneg _
  rw [isIntegral_iff_spectralNorm_le_one, hmul, spectralNorm_extends,
    isPowMul_spectralNorm _ (by omega : 1 ≤ n + 1)]
  calc ‖c⁻¹‖ * spectralNorm (v.adicCompletion K) (Kbar v) y⁻¹ ^ (n + 1)
      ≤ ‖c⁻¹‖ * spectralNorm (v.adicCompletion K) (Kbar v) y⁻¹ ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hs0 hlt.le (by omega)) (norm_nonneg _)
    _ ≤ ‖c⁻¹‖ * ‖c‖ := mul_le_mul_of_nonneg_left hn.le (norm_nonneg _)
    _ = 1 := by rw [norm_inv, inv_mul_cancel₀ hc'.ne']

theorem isIntegral_map_iff (f : v.adicCompletion K →+* v'.adicCompletion F) (hf : Continuous f)
    (b : Kbar v ≃+* Kbar v') (hb : ∀ x, b (algebraMap _ _ x) = algebraMap _ _ (f x)) (y : Kbar v) :
    IsIntegral (v'.adicCompletionIntegers F) (b y) ↔ IsIntegral (v.adicCompletionIntegers K) y := by
  refine ⟨fun h => ?_, isIntegral_map f hf b hb⟩
  by_contra hy
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_valued_lt_one v
  obtain ⟨N, hN⟩ := exists_isIntegral_mul_inv_pow hy hc0
  have h1 := isIntegral_map f hf b hb hN
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy isIntegral_zero
  have hby0 : b y ≠ 0 := (map_ne_zero b).2 hy0
  have h2 : IsIntegral (v'.adicCompletionIntegers F)
      (algebraMap (v'.adicCompletion F) (Kbar v') (f c)⁻¹) := by
    have e : algebraMap (v'.adicCompletion F) (Kbar v') (f c)⁻¹ =
        b y ^ N * b (algebraMap (v.adicCompletion K) (Kbar v) c⁻¹ * y⁻¹ ^ N) := by
      rw [map_mul, map_pow, map_inv₀ b y, hb, map_inv₀ f, inv_pow, mul_left_comm,
        mul_inv_cancel₀ (pow_ne_zero _ hby0), mul_one]
    rw [e]
    exact (h.pow N).mul h1
  have h3 := valued_le_one_of_isIntegral h2
  have h4 := GlobalTheory.ConjParahoric.val_lt_one_map f hf hc1
  have hfc : f c ≠ 0 := (map_ne_zero f).2 hc0
  have h5 : Valued.v (f c * (f c)⁻¹) < 1 := by
    rw [Valuation.map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' h3) h4
  rw [mul_inv_cancel₀ hfc, Valuation.map_one] at h5
  exact lt_irrefl _ h5

end spectral

end GlobalTheory.ClosureIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsParahoricTypeVectorOfBlockTypeVectorPadicIso
section
open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys

noncomputable section

namespace GlobalTheory.ParRead

open ValuativeRel Matrix

variable {g : ℕ} [Fact g.Prime] {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

theorem lt_one_mem_nhds : {x : F | valuation F x < 1} ∈ nhds (0 : F) :=
  (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, by simp⟩

theorem val_lt_one {e : ℚ_[g] ≃+* F} (he : Continuous e) {z : ℚ_[g]} (hz : ‖z‖ < 1) :
    valuation F (e z) < 1 := by
  have h1 : Filter.Tendsto (fun n : ℕ => (e z) ^ n) Filter.atTop (nhds 0) := by
    have := (he.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz)
    rw [map_zero] at this
    simpa [Function.comp_def, map_pow] using this
  obtain ⟨n, hn⟩ := (h1.eventually lt_one_mem_nhds).exists
  rw [map_pow] at hn
  by_contra hc
  exact absurd hn (not_lt.2 (one_le_pow₀ (not_lt.1 hc)))

theorem val_lt_one_of_red {e : ℚ_[g] ≃+* F} (he : Continuous e) {z : ℤ_[g]}
    (hz : PadicInt.toZMod z = 0) : valuation F (e z) < 1 := by
  have : z ∈ RingHom.ker (PadicInt.toZMod (p := g)) := hz
  rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at this
  exact val_lt_one he this

theorem val_le_one {e : ℚ_[g] ≃+* F} (he : Continuous e) (z : ℤ_[g]) : valuation F (e z) ≤ 1 := by
  set m : ℕ := (PadicInt.toZMod z).val
  have hm : PadicInt.toZMod (z - (m : ℤ_[g])) = 0 := by
    rw [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  have e1 : e (z : ℚ_[g]) = (m : F) + e ((z - (m : ℤ_[g]) : ℤ_[g]) : ℚ_[g]) := by
    rw [PadicInt.coe_sub, map_sub, PadicInt.coe_natCast, map_natCast]; ring
  rw [e1]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ (val_lt_one_of_red he hm).le)
  clear e1 hm
  induction m with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ]; exact (Valuation.map_add _ _ _).trans (max_le ih (by simp))

def intHom {e : ℚ_[g] ≃+* F} (he : Continuous e) : ℤ_[g] →+* 𝒪[F] :=
  (e.toRingHom.comp (algebraMap ℤ_[g] ℚ_[g])).codRestrict 𝒪[F] fun z => by
    rw [Valuation.mem_integer_iff]; exact val_le_one he z

theorem map_inc_mem_KO {e : ℚ_[g] ≃+* F} (he : Continuous e) {n : ℕ} (k : GL (Fin n) ℤ_[g]) :
    Matrix.GeneralLinearGroup.map e.toRingHom (inc g n k) ∈ GlobalTheory.SplitWeil.KO F (Fin n) := by
  refine ⟨Matrix.GeneralLinearGroup.map (intHom he) k, ?_⟩
  ext i j
  simp [inc, intHom]
  rfl

theorem act_inc {e : ℚ_[g] ≃+* F} (he : Continuous e) {ξ : Fˣ →* ℂˣ} {χ : (ZMod g)ˣ →* ℂˣ}
    (hT : TamePart (ξ.comp (Units.map e.toMonoidHom)) χ) {r t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin (r + t)) F) V} {u : V} (hu : GlobalTheory.SplitRead.IsBlockVec ξ ρ u)
    (k : GL (Fin (r + t)) ℤ_[g]) (h0 : InPar r (red g (r + t) k : Mt g (r + t)))
    (h1 : tl r (red g (r + t) k : Mt g (r + t)) = 1) (c : (ZMod g)ˣ)
    (hc : (c : ZMod g) = (br r t (red g (r + t) k : Mt g (r + t))).det) :
    ρ (Matrix.GeneralLinearGroup.map e.toRingHom (inc g (r + t) k)) u = ((χ c : ℂˣ) : ℂ) • u := by
  have hred : ∀ i j, (red g (r + t) k : Mt g (r + t)) i j = PadicInt.toZMod ((k : Matrix (Fin (r + t)) (Fin (r + t)) ℤ_[g]) i j) :=
    fun i j => by simp [red]
  have hent : ∀ i j, (Matrix.GeneralLinearGroup.map e.toRingHom (inc g (r + t) k)).val i j =
      e ((k : Matrix (Fin (r + t)) (Fin (r + t)) ℤ_[g]) i j : ℚ_[g]) := fun i j => by simp [inc]
  set d : ℤ_[g] := ((k : Matrix (Fin (r + t)) (Fin (r + t)) ℤ_[g]).submatrix (Fin.natAdd r) (Fin.natAdd r)).det with hd
  have hbr : br r t (red g (r + t) k : Mt g (r + t)) =
      (PadicInt.toZMod (p := g)).mapMatrix ((k : Matrix (Fin (r + t)) (Fin (r + t)) ℤ_[g]).submatrix (Fin.natAdd r) (Fin.natAdd r)) := by
    ext i j
    have hi : r + (i : ℕ) < r + t := by omega
    have hj : r + (j : ℕ) < r + t := by omega
    simp only [br, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (And.intro hi hj), hred]
    rfl
  have hdc : PadicInt.toZMod d = c := by rw [hc, hbr, hd, RingHom.map_det]
  have hdu : IsUnit d := by
    by_contra h
    have : d ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by rw [PadicInt.ker_toZMod]; exact h
    rw [RingHom.mem_ker, hdc] at this
    exact c.ne_zero this
  refine (hu _ (map_inc_mem_KO he k) ?_ ?_
    (Units.map e.toMonoidHom (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom hdu.unit)) ?_).trans ?_
  · intro i j
    rw [hent]
    apply val_lt_one_of_red he
    rw [← hred]
    exact h0 _ _ (by simp) (by simp)
  · intro i j
    rw [hent]
    have hij : (red g (r + t) k : Mt g (r + t)) (Fin.castAdd t i) (Fin.castAdd t j) = (1 : Mt g r) i j := by
      rw [← h1]
      have hi : (i : ℕ) < r + t := by omega
      have hj : (j : ℕ) < r + t := by omega
      simp only [tl, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (And.intro hi hj)]
      rfl
    have h2 : PadicInt.toZMod ((k : Matrix (Fin (r + t)) (Fin (r + t)) ℤ_[g]) (Fin.castAdd t i) (Fin.castAdd t j) -
        if i = j then 1 else 0) = 0 := by
      rw [map_sub, ← hred, hij, Matrix.one_apply]
      split_ifs <;> simp
    have := val_lt_one_of_red he h2
    convert this using 2
    split_ifs <;> simp
  · simp [hd, RingHom.map_det]
    congr 1
  · have h2 := hT hdu.unit
    have h3 : Units.map (PadicInt.toZMod (p := g)).toMonoidHom hdu.unit = c := Units.ext (by simpa using hdc)
    rw [h3, MonoidHom.comp_apply] at h2
    rw [h2]

theorem inPar_one {r n : ℕ} : InPar r (1 : Mt g n) := fun i j hj hi => by
  rw [Matrix.one_apply_ne]
  intro h; rw [h] at hi; omega

theorem tl_one {r t : ℕ} : tl r (1 : Mt g (r + t)) = 1 := by
  ext i j
  have hi : (i : ℕ) < r + t := by omega
  have hj : (j : ℕ) < r + t := by omega
  simp only [tl, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (And.intro hi hj), Matrix.one_apply, Fin.ext_iff]

theorem br_one {r t : ℕ} : br r t (1 : Mt g (r + t)) = 1 := by
  ext i j
  have hi : r + (i : ℕ) < r + t := by omega
  have hj : r + (j : ℕ) < r + t := by omega
  simp only [br, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (And.intro hi hj), Matrix.one_apply, Fin.ext_iff]
  by_cases h : (i : ℕ) = j
  · simp [h]
  · rw [if_neg (by omega), if_neg h]

theorem blk_parts {r t : ℕ} (y : Gn g t) :
    InPar r (blk r t (r + t) 1 y : Mt g (r + t)) ∧ tl r (blk r t (r + t) 1 y : Mt g (r + t)) = 1 ∧
      br r t (blk r t (r + t) 1 y : Mt g (r + t)) = (y : Mt g t) := by
  set M : Mt g (r + t) := fun i j : Fin (r + t) =>
    if (i : ℕ) < r ∧ (j : ℕ) < r then Formalism.MainNotions.ArithmeticCylinders.entN ((1 : Gn g r) : Mt g r) i j
    else if r ≤ (i : ℕ) ∧ r ≤ (j : ℕ) then Formalism.MainNotions.ArithmeticCylinders.entN (y : Mt g t) (i - r) (j - r) else 0 with hM
  have h0 : InPar r M := fun i j hj hi => by rw [hM]; dsimp only; rw [if_neg (by omega), if_neg (by omega)]
  have h1 : tl r M = 1 := by
    ext i j
    have hi : (i : ℕ) < r + t := by omega
    have hj : (j : ℕ) < r + t := by omega
    simp [tl, Formalism.MainNotions.ArithmeticCylinders.entN, hM, hi, hj]
  have h2 : br r t M = y := by
    ext i j
    simp [br, Formalism.MainNotions.ArithmeticCylinders.entN, hM]
  have hu : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, LabelDet.det_inPar r t M h0, h1, h2, Matrix.det_one, one_mul]
    exact (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  have hb : (blk r t (r + t) 1 y : Mt g (r + t)) = M := by
    show ((toG M : Gn g (r + t)) : Mt g (r + t)) = M
    rw [toG, dif_pos hu]; rfl
  rw [hb]; exact ⟨h0, h1, h2⟩

theorem isParVec_of_isBlockVec : ∀ (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F), Continuous e → ∀ (ξ : Fˣ →* ℂˣ) (χ : (ZMod g)ˣ →* ℂˣ),
    TamePart (ξ.comp (Units.map e.toMonoidHom)) χ → ∀ (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin (r + t)) F) V) (u : V), GlobalTheory.SplitRead.IsBlockVec ξ ρ u →
    IsParVec (ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) r t χ u := by
  intro g _ F _ _ _ _ e he ξ χ hT r t V _ _ ρ u hu
  have hsurj : ∀ x : Gn g (r + t), red g (r + t) (Function.invFun (red g (r + t)) x) = x :=
    fun x => Function.invFun_eq (Model.red_surjective _ x)
  refine ⟨?_, ?_, ?_⟩
  · rw [Model.mem_principalCongruenceFixedVectors_iff]
    intro k hk
    have := act_inc he hT hu k (by rw [hk, Units.val_one]; exact inPar_one) (by rw [hk, Units.val_one]; exact tl_one) 1
      (by rw [hk, Units.val_one, Units.val_one, br_one, Matrix.det_one])
    rw [map_one, Units.val_one, one_smul] at this
    exact this
  · intro x h0 h1 h2
    have := act_inc he hT hu (Function.invFun (red g (r + t)) x) (by rw [hsurj]; exact h0) (by rw [hsurj]; exact h1) 1
      (by rw [hsurj, h2, Matrix.det_one, Units.val_one])
    rw [map_one, Units.val_one, one_smul] at this
    exact this
  · intro y
    obtain ⟨h0, h1, h2⟩ := blk_parts (r := r) y
    have := act_inc he hT hu (Function.invFun (red g (r + t)) (blk r t (r + t) 1 y)) (by rw [hsurj]; exact h0)
      (by rw [hsurj]; exact h1) (Matrix.GeneralLinearGroup.det y)
      (by rw [hsurj, h2, Matrix.GeneralLinearGroup.val_det_apply])
    exact this

end GlobalTheory.ParRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsParahoricTypeVectorOfUpperParahoricEigen
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SameParahoric

open Filter Topology

theorem denseRange_i {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) :
    DenseRange (s.i : L → s.v.adicCompletion (maximalRealSubfield L)) := by
  refine (s.v.denseRange_algebraMap (maximalRealSubfield L)).mono ?_
  rintro _ ⟨y, rfl⟩
  exact ⟨algebraMap (maximalRealSubfield L) L y, s.i.commutes y⟩

theorem eq_comp {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L)
    (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ) (μ : (s.w.adicCompletion L)ˣ →* ℂˣ)
    (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (hc : Continuous c)
    (hci : ∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) (hμ : GlobalTheory.SmGL.IsSmoothChar μ) (N : ℕ)
    (hN : ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ,
      Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1)
    (hglob : ∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k) =
      μ (Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom k))
    (d : (s.v.adicCompletion (maximalRealSubfield L))ˣ) :
    ξ d = μ (Units.map c.toRingHom.toMonoidHom d) := by
  obtain ⟨z, hz⟩ := s.v.valuedAdicCompletion_surjective (maximalRealSubfield L) (WithZero.exp (-(N : ℤ)))
  have hξo : GlobalTheory.SmGL.IsSmoothChar ξ := by
    have hU : IsOpen {x : (s.v.adicCompletion (maximalRealSubfield L))ˣ |
        Valued.v ((x : s.v.adicCompletion (maximalRealSubfield L)) - 1) < Valued.v z} := by
      have h1 := (Valued.isOpen_ball (s.v.adicCompletion (maximalRealSubfield L)) (Valued.v.restrict z)).preimage
        (Units.continuous_val.sub (continuous_const (y := (1 : s.v.adicCompletion (maximalRealSubfield L)))))
      simpa only [Set.preimage_setOf_eq, Valuation.restrict_lt_iff, Pi.sub_apply] using h1
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hU.mem_nhds ?_) fun x hx => ?_)
    · simp only [Set.mem_setOf_eq, Units.val_one, sub_self, map_zero, hz]
      exact WithZero.exp_pos
    · have hx' : Valued.v ((x : s.v.adicCompletion (maximalRealSubfield L)) - 1) < Valued.v z := hx
      exact hN x (by rw [← hz]; exact hx'.le)
  have hcu : Continuous (Units.map c.toRingHom.toMonoidHom :
      (s.v.adicCompletion (maximalRealSubfield L))ˣ → (s.w.adicCompletion L)ˣ) := by
    rw [Units.continuous_iff]
    exact ⟨hc.comp Units.continuous_val, hc.comp Units.continuous_coe_inv⟩
  have hs := hξo.mul (hμ.comp _ hcu).inv
  have hcl := Subgroup.isClosed_of_isOpen _ hs
  refine mul_inv_eq_one.1 ?_
  by_contra hy
  obtain ⟨U, hU, hU'⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hcl.isOpen_compl
  have hyU : (d : s.v.adicCompletion (maximalRealSubfield L)) ∈ U := by
    have : d ∈ Units.val ⁻¹' U := by rw [hU']; exact hy
    exact this
  obtain ⟨k, hk1, hk2⟩ := (denseRange_i s).exists_mem_open
    (hU.inter isOpen_ne (t := {z | z ≠ 0})) ⟨d, hyU, d.ne_zero⟩
  have hk0 : k ≠ 0 := fun e => hk2 (by rw [e, map_zero])
  have h3 : Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) (Units.mk0 k hk0) ∈ Units.val ⁻¹' U := hk1
  rw [hU'] at h3
  refine h3 ?_
  have hm : Units.map c.toRingHom.toMonoidHom
      (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) (Units.mk0 k hk0)) =
      Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom (Units.mk0 k hk0) := Units.ext (hci k)
  show ξ _ * (μ (Units.map c.toRingHom.toMonoidHom _))⁻¹ = 1
  rw [hm, ← hglob]
  exact mul_inv_cancel _

theorem isParahoricVec_of_eigen : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (r t : ℕ) {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) (s.w.adicCompletion L)) W) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ) (μ : (s.w.adicCompletion L)ˣ →* ℂˣ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → GlobalTheory.SmGL.IsSmoothChar μ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → (∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k) = μ (Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom k)) → ∀ u : W, (∀ g : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)), NG.ParaRT s r g → ∀ d : (s.v.adicCompletion (maximalRealSubfield L))ˣ, (d : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r g → π (Matrix.GeneralLinearGroup.map c.toRingHom g) u = ((ξ d : ℂˣ) : ℂ) • u) → GlobalTheory.ThetaGL.IsParahoricVec μ π u := by
  intro L _ _ _ s r t W _ _ π ξ μ c hc hci hμ ⟨N, hN⟩ hglob u hvec
  have hE := GlobalTheory.ConjParahoric.isEquiv_of_continuous c hc
  have hlt : ∀ x, ValuativeRel.valuation _ x < 1 → Valued.v (c.symm x) < 1 := fun x hx =>
    (Valuation.isEquiv_iff_val_lt_one.1 hE).2 hx
  have hle : ∀ x, ValuativeRel.valuation _ x ≤ 1 →
      c.symm x ∈ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := fun x hx =>
    (Valuation.isEquiv_iff_val_le_one.1 hE).2 hx
  intro h hK hlow x hx
  obtain ⟨hi1, hi2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff h).1 hK
  let g := Matrix.GeneralLinearGroup.map c.symm.toRingHom h
  have hg : ∀ a b, g.val a b = c.symm (h.val a b) := fun a b => rfl
  have hg' : ∀ a b, (g⁻¹).val a b = c.symm ((h⁻¹).val a b) := fun a b => rfl
  have hpara : NG.ParaRT s r g := by
    refine ⟨GlobalTheory.ConjParahoric.mem_GLint_of_entries _ g (fun a b => hg a b ▸ hle _ (hi1 a b))
      (fun a b => hg' a b ▸ hle _ (hi2 a b)), fun a b ha hb => ?_⟩
    rw [hg]
    have ea : Fin.natAdd r (⟨a.val - r, by omega⟩ : Fin t) = a := by ext; simp; omega
    have eb : Fin.castAdd t (⟨b.val, hb⟩ : Fin r) = b := by ext; simp
    have := hlow ⟨a.val - r, by omega⟩ ⟨b.val, hb⟩
    rw [ea, eb] at this
    exact hlt _ this
  have hDD : c.symm (x : s.w.adicCompletion L) = NG.detDD s r g := by
    rw [NG.detDD, ← Matrix.det_submatrix_equiv_self (GlobalTheory.ConjParahoric.lowerEquiv r t), hx]
    refine (RingHom.map_det c.symm.toRingHom _).trans ?_
    congr 1
  have key := hvec g hpara (Units.map c.symm.toRingHom.toMonoidHom x) hDD
  have hpp : Matrix.GeneralLinearGroup.map c.toRingHom g = h :=
    Units.ext (Matrix.ext fun a b => c.apply_symm_apply _)
  have hcc : Units.map c.toRingHom.toMonoidHom (Units.map c.symm.toRingHom.toMonoidHom x) = x :=
    Units.ext (c.apply_symm_apply _)
  rw [hpp, GlobalTheory.SameParahoric.eq_comp s ξ μ c hc hci hμ N hN hglob, hcc] at key
  exact key

end GlobalTheory.SameParahoric
end

