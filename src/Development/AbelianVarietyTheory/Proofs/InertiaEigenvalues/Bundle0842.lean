module

public import Mathlib
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0834
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0753
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0835
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ZeroDegreeOfPinFor

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelNatBumpRankinSelbergCell
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.RSParams

variable {E : Type} [Field E] [NumberField E]

theorem valued_natCast (v : HeightOneSpectrum (𝓞 E)) (N : ℕ) :
    Valued.v (N : v.adicCompletion E) = v.intValuation (N : 𝓞 E) := by
  have h := v.valuedAdicCompletion_eq_valuation (K := E) (N : 𝓞 E)
  rw [v.valuation_of_algebraMap] at h
  simpa using h

theorem exists_nat (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ w ∈ S, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ S) (k : ℕ) :
    ∃ N : ℕ, 0 < N ∧ (∀ v ∈ S, (N : 𝓞 E) ∈ v.asIdeal ^ k) ∧ ∀ v ∉ S, (N : 𝓞 E) ∉ v.asIdeal := by
  classical
  set q : HeightOneSpectrum (𝓞 E) → Ideal ℤ := fun w => Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal with hq
  have hq0 : ∀ w, q w ≠ ⊥ := fun w h => by
    have hm : ((Ideal.absNorm w.asIdeal : ℕ) : ℤ) ∈ q w := by
      rw [hq, Ideal.mem_comap, map_natCast]
      exact Ideal.absNorm_mem _
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff] at hm
    exact w.ne_bot hm
  set 𝔞 : Ideal ℤ := ∏ w ∈ S, q w with h𝔞
  set n : ℤ := Submodule.IsPrincipal.generator 𝔞 with hn
  have hspan : Ideal.span {n} = 𝔞 := Ideal.span_singleton_generator 𝔞
  have h𝔞0 : 𝔞 ≠ ⊥ := by
    rw [h𝔞, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    exact fun w _ => hq0 w
  have hn0 : n ≠ 0 := fun h => h𝔞0 (by rw [← hspan, h, Ideal.span_singleton_eq_bot])
  set N₀ : ℕ := n.natAbs with hN₀
  have hN₀q : ∀ w ∈ S, (N₀ : ℤ) ∈ q w := fun w hw => by
    have h1 : (N₀ : ℤ) ∈ 𝔞 := by
      rw [← hspan, Ideal.mem_span_singleton]
      exact Int.dvd_natAbs.2 dvd_rfl
    exact Ideal.prod_le_inf.trans (Finset.inf_le hw) h1
  refine ⟨N₀ ^ k, pow_pos (Int.natAbs_pos.2 hn0) k, fun v hv => ?_, fun v hv h => ?_⟩
  · have h1 : (N₀ : 𝓞 E) ∈ v.asIdeal := by
      have := hN₀q v hv
      rwa [hq, Ideal.mem_comap, map_natCast] at this
    rw [Nat.cast_pow]
    exact Ideal.pow_mem_pow h1 k
  · rw [Nat.cast_pow] at h
    have h1 : (N₀ : 𝓞 E) ∈ v.asIdeal := v.isPrime.mem_of_pow_mem k h
    have h2 : (N₀ : ℤ) ∈ q v := by rwa [hq, Ideal.mem_comap, map_natCast]
    have h3 : n ∈ q v := by
      obtain ⟨c, hc⟩ := (Int.natAbs_dvd.2 (dvd_refl n) : (N₀ : ℤ) ∣ n)
      rw [hc]
      exact Ideal.mul_mem_right _ _ h2
    haveI hp : (q v).IsPrime := Ideal.comap_isPrime _ _
    have h4 : 𝔞 ≤ q v := by rw [← hspan, Ideal.span_singleton_le_iff_mem]; exact h3
    obtain ⟨w, hw, hle⟩ := (Ideal.IsPrime.prod_le hp).1 h4
    have hmax : (q w).IsMaximal := (Ideal.comap_isPrime _ w.asIdeal).isMaximal (hq0 w)
    have heq : q w = q v := hmax.eq_of_le hp.ne_top hle
    exact hv (hS w hw v heq.symm)

variable [_root_.NumberField.IsTotallyComplex E]

theorem mem_natLat_iff {N : ℕ} (hN : 0 < N) (z : Af E) :
    z ∈ GlobalTheory.RSJ.natLat E N ↔ ∀ v : HeightOneSpectrum (𝓞 E), Valued.v (z v) ≤ Valued.v (N : v.adicCompletion E) := by
  constructor
  · rintro ⟨y, hy, rfl⟩ v
    change Valued.v ((N : v.adicCompletion E) * y v) ≤ _
    rw [map_mul]
    exact mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hy v))
  · intro h
    set c : Af E := algebraMap E (Af E) ((N : E)⁻¹) with hc
    have hcN : c * (N : Af E) = 1 := by
      rw [hc, ← map_natCast (algebraMap E (Af E)), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), map_one]
    refine ⟨z * c, fun v => ?_, ?_⟩
    · have e : c v * (N : v.adicCompletion E) = 1 := congrArg (fun x : Af E => x v) hcN
      have e' : Valued.v (c v) * Valued.v (N : v.adicCompletion E) = 1 := by rw [← map_mul, e, map_one]
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v (z v * c v) ≤ 1
      rw [map_mul, ← e', mul_comm (Valued.v (c v))]
      exact mul_le_mul_of_nonneg_right (h v) zero_le'
    · calc z = z * (c * (N : Af E)) := by rw [hcN, mul_one]
        _ = (N : Af E) * (z * c) := by ring

end GlobalTheory.RSParams


open GlobalTheory.RSParams in
theorem GlobalTheory.RSParams.exists_level_nat_bump : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∈ S, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ S) →
    ∀ V : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (V : Set (GL (Fin (m + 1)) (Af E))) →
    (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), locGL E (m + 1) w k ∈ V) →
    ∃ (N : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), 0 < N ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ Φ (Pi.single (Fin.last m) 1) ≠ 0 ∧
      (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) ∧
      GlobalTheory.RSLocalPart.levelAt (m + 1) S J ⊆ V ∧
      (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v : HeightOneSpectrum (𝓞 E), z v ∈ v.adicCompletionIntegers E) ∧
      (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) ∧
      (∀ z z' : Af E, (∀ v ∈ S, z v = z' v) → (∀ v ∉ S, z v ∈ v.adicCompletionIntegers E) →
        (∀ v ∉ S, z' v ∈ v.adicCompletionIntegers E) → (z ∈ GlobalTheory.RSJ.natLat E N ↔ z' ∈ GlobalTheory.RSJ.natLat E N)) := by
  intro E _ _ _ m S hS V hV hw
  classical
  obtain ⟨J, hJS, -, hJV⟩ := GlobalTheory.RSLocalPart.exists_levelAt_subset S V hV hw
  set k : ℕ := ∑ v ∈ S, (FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat with hk
  obtain ⟨N, hN, hNS, hNc⟩ := exists_nat S hS k
  have hv1 : ∀ v : HeightOneSpectrum (𝓞 E), Valued.v (N : v.adicCompletion E) ≤ 1 := fun v => by
    rw [valued_natCast]; exact v.intValuation_le_one _
  have hvS : ∀ v ∈ S, Valued.v (N : v.adicCompletion E) ≤
      WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) := fun v hv => by
    rw [valued_natCast]
    refine ((v.intValuation_le_pow_iff_mem _ k).2 (hNS v hv)).trans (WithZero.exp_le_exp.2 ?_)
    have h1 : FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E) ≤
        ((FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat : ℤ) := Int.self_le_toNat _
    have h2 : (FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat ≤ k :=
      Finset.single_le_sum (f := fun v => (FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat)
        (fun _ _ => Nat.zero_le _) hv
    omega
  have hvn : ∀ v ∉ S, Valued.v (N : v.adicCompletion E) = 1 := fun v hv => by
    rw [valued_natCast]
    exact le_antisymm (v.intValuation_le_one _) (not_lt.1 fun h => hNc v hv ((v.intValuation_lt_one_iff_mem _).1 h))
  have he : (Pi.single (Fin.last m) 1 : Fin (m + 1) → Cinf E) ∈ GlobalTheory.RSTheta.rowSet E (Fin.last m) := fun w => by
    simp
  obtain ⟨ρ, hts, hcs, hcd, hr, h1⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    ((GlobalTheory.RSTheta.isOpen_rowSet (E := E) (Fin.last m)).mem_nhds he)
  have hr' : ∀ u, ρ u ∈ Set.Icc (0 : ℝ) 1 := fun u => hr ⟨u, rfl⟩
  refine ⟨N, J, fun u => (ρ u : ℂ), hN, Complex.ofRealCLM.contDiff.comp hcd, hcs.comp_left Complex.ofReal_zero,
    (tsupport_comp_subset Complex.ofReal_zero ρ).trans hts, fun u => ⟨by simpa using (hr' u).1, by simp⟩,
    by simp [h1], hJS, hJV, fun z hz v => ?_, fun z hz v hv => ?_, fun z z' hzz hz hz' => ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact ((mem_natLat_iff hN z).1 hz v).trans (hv1 v)
  · exact ((mem_natLat_iff hN z).1 hz v).trans (hvS v hv)
  · rw [mem_natLat_iff hN, mem_natLat_iff hN]
    refine forall_congr' fun v => ?_
    by_cases hv : v ∈ S
    · rw [hzz v hv]
    · rw [hvn v hv]
      exact ⟨fun _ => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hz' v hv),
        fun _ => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hz v hv)⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMirabolicWhittakerReductionCell
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.WhitRed

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem compV_eq (w : HeightOneSpectrum (𝓞 E)) (x : GA E n) :
    GlobalTheory.CellDec.compV E n w x = GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) x) :=
  Units.ext (Matrix.ext fun _ _ => rfl)

theorem map_pLoc_prod_of_notMem (f : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin n) (w.adicCompletion E))
    (v : HeightOneSpectrum (𝓞 E)) : ∀ L : List (HeightOneSpectrum (𝓞 E)), v ∉ L →
    GeneralLinearGroup.map (pLoc E v) (L.map fun w => locGL E n w (f w)).prod = 1
  | [], _ => by simp
  | w :: L, h => by
    rw [List.mem_cons, not_or] at h
    rw [List.map_cons, List.prod_cons, map_mul, map_pLoc_prod_of_notMem f v L h.2, pLoc_locGL_of_ne h.1, one_mul]

theorem map_pLoc_prod_of_mem (f : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin n) (w.adicCompletion E))
    (v : HeightOneSpectrum (𝓞 E)) : ∀ L : List (HeightOneSpectrum (𝓞 E)), L.Nodup → v ∈ L →
    GeneralLinearGroup.map (pLoc E v) (L.map fun w => locGL E n w (f w)).prod = f v
  | [], _, h => absurd h List.not_mem_nil
  | w :: L, hL, h => by
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, map_mul]
    by_cases hv : v = w
    · subst hv
      rw [pLoc_locGL, map_pLoc_prod_of_notMem f v L hL.1, mul_one]
    · rw [pLoc_locGL_of_ne hv, one_mul]
      exact map_pLoc_prod_of_mem f v L hL.2 ((List.mem_cons.1 h).resolve_left hv)

theorem row_mul_inv {R : Type} [CommRing R] {a : ℕ} (A B : GL (Fin a) R) (i : Fin a)
    (h : ∀ j, A.val i j = B.val i j) (j : Fin a) : (A * B⁻¹).val i j = (1 : Matrix (Fin a) (Fin a) R) i j := by
  have e : (A * B⁻¹).val i j = (B * B⁻¹).val i j := by
    simp only [Units.val_mul, Matrix.mul_apply, h]
  rw [e, mul_inv_cancel, Units.val_one]

variable [_root_.NumberField.IsTotallyComplex E]

theorem compV_infGL (w : HeightOneSpectrum (𝓞 E)) (y : GL (Fin n) (Cinf E)) :
    GlobalTheory.CellDec.compV E n w (infGL E n y) = 1 := by
  rw [compV_eq, pFin_infGL, map_one]

theorem comm_of_supp {x y : GA E n} (hinf : GeneralLinearGroup.map (pInf E) x = 1)
    (hw : ∀ w, GlobalTheory.CellDec.compV E n w x = 1 ∨ GlobalTheory.CellDec.compV E n w y = 1) : x * y = y * x := by
  refine ga_ext (by rw [map_mul, map_mul, hinf, one_mul, mul_one]) (GlobalTheory.CellDec.GL_ext_pLoc fun w => ?_)
  rw [map_mul, map_mul, map_mul, map_mul, ← compV_eq, ← compV_eq]
  rcases hw w with h | h <;> rw [h] <;> simp

end GlobalTheory.WhitRed


open GlobalTheory.WhitRed in
theorem GlobalTheory.WhitRed.exists_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (F : GA E (m + 1) → ℂ)
    (U : Subgroup (GL (Fin (m + 1)) (Af E))) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
    (∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g) →
    (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g) →
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    (∀ y : Fin (m + 1) → Af E, y - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ κ ∈ U, (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
        ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j =
          pLoc E w (y j)) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, IsUnit (pInf E (g.val (Fin.last m) (Fin.last m))) →
      (fun i => pFin E (g.val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) T ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T,
        ‖GlobalTheory.JSW.whit F (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g *
          (infGL E (m + 1) (GlobalTheory.RSTheta.rowGL (Fin.last m) (fun i => pInf E (g.val (Fin.last m) i))))⁻¹)‖ =
        ‖GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l.1)‖ := by
  intro E _ _ _ m T ϖ F U J hU hK hN hκ g hg hu hy
  obtain ⟨u₁, hu₁, k, hk, he⟩ := hg
  have hrow : ∀ j, g.val (Fin.last m) j = k.val (Fin.last m) j := by
    intro j
    obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu₁
    rw [he, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)]
    · rw [h2, one_mul]
    · intro i _ hi
      rw [h1 _ _ (lt_of_le_of_ne (Fin.le_last i) hi), zero_mul]
    · simp
  have hσrow : ∀ j, (GlobalTheory.RSTheta.rowGL (Fin.last m) (fun i => pInf E (g.val (Fin.last m) i))).val (Fin.last m) j =
      pInf E (g.val (Fin.last m) j) := by
    intro j
    have := congrFun (GlobalTheory.RSTheta.single_vecMul_rowGL (ℓ := Fin.last m) (y := fun i => pInf E (g.val (Fin.last m) i)) hu) j
    rwa [Matrix.single_one_vecMul] at this
  generalize GlobalTheory.RSTheta.rowGL (Fin.last m) (fun i => pInf E (g.val (Fin.last m) i)) = σ at hσrow ⊢
  obtain ⟨κ, hκU, hκoff, hκT⟩ := hκ _ hy
  obtain ⟨hf, hhf⟩ : ∃ hf : GL (Fin (m + 1)) (Af E),
      hf = (T.toList.map fun w => locGL E (m + 1) w (GlobalTheory.CellDec.compV E (m + 1) w k)).prod := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : GA E (m + 1), h = infGL E (m + 1) (GeneralLinearGroup.map (pInf E) k) * finGL E (m + 1) hf :=
    ⟨_, rfl⟩
  have hhinf : GeneralLinearGroup.map (pInf E) h = GeneralLinearGroup.map (pInf E) k := by
    rw [hh, map_mul, pInf_infGL, pInf_finGL, mul_one]
  have hhon : ∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w h = GlobalTheory.CellDec.compV E (m + 1) w k := by
    intro w hw
    rw [hh, map_mul, compV_infGL, one_mul, GlobalTheory.CellDec.compV_finGL, hhf,
      map_pLoc_prod_of_mem _ w _ T.nodup_toList (Finset.mem_toList.2 hw)]
  have hhoff : ∀ w ∉ T, GlobalTheory.CellDec.compV E (m + 1) w h = 1 := by
    intro w hw
    rw [hh, map_mul, compV_infGL, one_mul, GlobalTheory.CellDec.compV_finGL, hhf,
      map_pLoc_prod_of_notMem _ w _ (fun h' => hw (Finset.mem_toList.1 h'))]
  have hkT : h⁻¹ * k ∈ GlobalTheory.CellDec.US E (m + 1) T := by
    rw [GlobalTheory.CellDec.mem_US] at hk ⊢
    intro v hv
    rw [map_mul, map_inv, hhoff v hv, inv_one, one_mul]
    exact hk v hv
  have hkTinf : GeneralLinearGroup.map (pInf E) (h⁻¹ * k) = 1 := by
    rw [map_mul, map_inv, hhinf, inv_mul_cancel]
  have hkTT : ∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w (h⁻¹ * k) = 1 := by
    intro w hw
    rw [map_mul, map_inv, hhon w hw, inv_mul_cancel]
  obtain ⟨p, hp⟩ : ∃ p : GA E (m + 1), p = h * (infGL E (m + 1) σ)⁻¹ * (finGL E (m + 1) κ)⁻¹ := ⟨_, rfl⟩
  have hpoff : ∀ w ∉ T, GlobalTheory.CellDec.compV E (m + 1) w p = 1 := by
    intro w hw
    rw [hp, map_mul, map_mul, map_inv, map_inv, hhoff w hw, compV_infGL, GlobalTheory.CellDec.compV_finGL, hκoff w hw]
    simp
  refine ⟨p, ⟨fun w hw => hpoff w hw, fun j => ?_⟩, fun l => ?_⟩
  · apply ad_ext
    · have e1 : pInf E (p.val (Fin.last m) j) = (GeneralLinearGroup.map (pInf E) p).val (Fin.last m) j := rfl
      have e2 : GeneralLinearGroup.map (pInf E) p = GeneralLinearGroup.map (pInf E) k * σ⁻¹ := by
        rw [hp, map_mul, map_mul, map_inv, map_inv, hhinf, pInf_infGL, pInf_finGL, inv_one, mul_one]
      have hkr : ∀ j, (GeneralLinearGroup.map (pInf E) k).val (Fin.last m) j = σ.val (Fin.last m) j := by
        intro j
        rw [hσrow, hrow]
        rfl
      rw [e1, e2, row_mul_inv _ _ _ hkr]
      by_cases hj : j = Fin.last m
      · subst hj; simp
      · rw [if_neg hj, map_zero, Matrix.one_apply_ne (Ne.symm hj)]
    · refine IsDedekindDomain.FiniteAdeleRing.ext _ fun w => ?_
      change (GlobalTheory.CellDec.compV E (m + 1) w p).val (Fin.last m) j =
        pLoc E w (pFin E (if j = Fin.last m then (1 : Ad E) else 0))
      have eR : pLoc E w (pFin E (if j = Fin.last m then (1 : Ad E) else 0)) =
          (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j := by
        by_cases hj : j = Fin.last m
        · subst hj; simp
        · rw [if_neg hj, map_zero, map_zero, Matrix.one_apply_ne (Ne.symm hj)]
      rw [eR]
      by_cases hw : w ∈ T
      · have e2 : GlobalTheory.CellDec.compV E (m + 1) w p =
            GlobalTheory.CellDec.compV E (m + 1) w k * (GeneralLinearGroup.map (pLoc E w) κ)⁻¹ := by
          rw [hp, map_mul, map_mul, map_inv, map_inv, hhon w hw, compV_infGL, GlobalTheory.CellDec.compV_finGL, inv_one, mul_one]
        rw [e2]
        refine row_mul_inv _ _ _ (fun j => ?_) j
        rw [hκT w hw j]
        show pLoc E w (pFin E (k.val _ _)) = _
        rw [← hrow]
      · rw [hpoff w hw]
        rfl
  · obtain ⟨t, ht⟩ : ∃ t : GA E (m + 1), t = GlobalTheory.CellDec.tl (m + 1) ϖ l.1 := ⟨_, rfl⟩
    rw [← ht]
    have htinf : GeneralLinearGroup.map (pInf E) t = 1 := by
      rw [ht, GlobalTheory.CellDec.tl]
      exact pInf_finGL _
    have htT : ∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w t = 1 := by
      intro w hw
      rw [ht, GlobalTheory.CellDec.compV_tl, l.2 w hw, GlobalTheory.IwaCell.tD_zero]
    have hc1 : (h⁻¹ * k) * (infGL E (m + 1) σ)⁻¹ = (infGL E (m + 1) σ)⁻¹ * (h⁻¹ * k) :=
      comm_of_supp hkTinf fun w => Or.inr (by rw [map_inv, compV_infGL, inv_one])
    have hc2 : t * p = p * t := comm_of_supp htinf fun w => by
      by_cases hw : w ∈ T
      · exact Or.inl (htT w hw)
      · exact Or.inr (hpoff w hw)
    have hp' : h * (infGL E (m + 1) σ)⁻¹ = p * finGL E (m + 1) κ := by
      rw [hp, inv_mul_cancel_right]
    have key : t * g * (infGL E (m + 1) σ)⁻¹ =
        (t * u₁ * t⁻¹) * ((p * t * finGL E (m + 1) κ) * (h⁻¹ * k)) := by
      calc t * g * (infGL E (m + 1) σ)⁻¹ = t * u₁ * (h * ((h⁻¹ * k) * (infGL E (m + 1) σ)⁻¹)) := by
            rw [he]; group
        _ = t * u₁ * ((h * (infGL E (m + 1) σ)⁻¹) * (h⁻¹ * k)) := by rw [hc1]; group
        _ = t * u₁ * t⁻¹ * ((t * p) * finGL E (m + 1) κ * (h⁻¹ * k)) := by rw [hp']; group
        _ = _ := by rw [hc2]
    have hu₁' : t * u₁ * t⁻¹ ∈ GlobalTheory.CellDec.NA E (m + 1) := by
      rw [ht]; exact GlobalTheory.CellDec.tl_conj_mem ϖ l.1 hu₁
    rw [key, hN _ hu₁', hK _ hkT hkTinf hkTT, hU κ hκU]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtOfIsKsForm
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
namespace GlobalTheory.TwInputs.Move.Forms


set_option maxHeartbeats 4000000 in
theorem hecke_geo {D D' : D7} (hR : D.R = D'.R) (hH : HEq D.host D'.host) (hsp : HEq D.sp D'.sp)
    (j : Fin D.R.m) (j' : Fin D'.R.m) (hj : (j : ℕ) = j') :
    GA D (Wc D j) = GA D' (Wc D' j') ∧ HEq (Wc D j) (Wc D' j') ∧
    ∀ (β : GL (Fin (Wc D j).rank) (Lev.EAf D)) (β' : GL (Fin (Wc D' j').rank) (Lev.EAf D')), HEq β β' →
    ∀ (Pg : Finset (Pl D.host.E)) (Pg' : Finset (Pl D'.host.E)), HEq Pg Pg' →
    ∀ (P : PlE D.host) (P' : PlE D'.host), HEq P P' → ∀ (k : ℕ) (α' : GA D' (Wc D' j')) (R' : Finset (GA D' (Wc D' j'))),
      IsHeckeAt (Wc D' j') P' k α' →
      Bridge.IsDC (Lev.levG (Wc D' j') β' (Lev.datY _ D'.R.r D'.R.t 0 (r_le_rank_Wc j') Pg' ∅ (LevelP.triv _ _ _)
        (fun _ _ => 1) (fun _ => 1) Lev.Frm.B)) α' R' →
      ∃ (α : GA D (Wc D j)) (R : Finset (GA D (Wc D j))), IsHeckeAt (Wc D j) P k α ∧
        Bridge.IsDC (Lev.levG (Wc D j) β (Lev.datY _ D.R.r D.R.t 0 (r_le_rank_Wc j) Pg ∅ (LevelP.triv _ _ _)
          (fun _ _ => 1) (fun _ => 1) Lev.Frm.B)) α R ∧
        ∀ F F', HEq F F' → HEq (Mult.heckeLin (Wc D j) R F) (Mult.heckeLin (Wc D' j') R' F') := by
  cases D; cases D'
  dsimp only at hR hH hsp
  subst hR; subst hH; subst hsp
  cases Fin.ext hj
  refine ⟨rfl, HEq.rfl, fun β β' hβ Pg Pg' hPg P P' hP k α R h1 h2 => ?_⟩
  subst hβ; subst hPg; subst hP
  exact ⟨α, R, h1, h2, fun F F' hF => by subst hF; rfl⟩


set_option maxHeartbeats 4000000 in
theorem exists_sameVec {D D' : D7} (hR : D.R = D'.R) (hH : HEq D.host D'.host) (hT : D.what₂.Tau = D'.what₂.Tau)
    (he : HEq D.eTau D'.eTau) {V : HSp D} {V' : HSp D'} (hV : HEq V V') {P : D.what₂.Tau → SPar} {P' : D'.what₂.Tau → SPar}
    {M : Mult.DSModel V P} {M' : Mult.DSModel V' P'} (hM : SameModel M M') (v' : M'.Vec) : ∃ v : M.Vec, SameVec v v' := by
  obtain ⟨h1, h2, h3, h4, -, -, h5⟩ := hM
  obtain ⟨R, H, sp, vol, vp, what₂, eT⟩ := D
  obtain ⟨R', H', sp', vol', vp', rows', eT'⟩ := D'
  dsimp only at hR hH hT he
  subst hR; subst hH
  cases what₂; cases rows'
  dsimp only at hT he
  subst hT; subst he; subst hV
  cases M; cases M'
  dsimp only at h1 h2 h3 h4 h5
  subst h1; subst h2; subst h3; subst h4; subst h5
  exact ⟨v', fun τ τ' h => by subst h; rfl⟩


set_option maxHeartbeats 4000000 in
theorem place_geo {R R' : Ranks} {H : Host R} {H' : Host R'} (hR : R = R') (hH : HEq H H') :
    PlE H = PlE H' ∧ ∀ (P : PlE H) (P' : PlE H'), HEq P P' → (IsSplitPl H P ↔ IsSplitPl H' P') ∧
      Nat.card (kP P) = Nat.card (kP P') ∧
      (∀ (χ : Formalism.L2.Host.HChar H.E) (χ' : Formalism.L2.Host.HChar H'.E), HEq χ χ' → χ.val P = χ'.val P') := by
  subst hR; subst hH
  refine ⟨rfl, fun P P' hP => ?_⟩
  subst hP
  exact ⟨Iff.rfl, rfl, fun _ _ h => by subst h; rfl⟩


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem record_heq {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    {Y : NExp D.R D.host D.what₂ D.LL0 N X} {Y' : NExp D'.R D'.host D'.what₂ D'.LL0 N' X'}
    (h1 : GlobalTheory.TwistChoice.SameGalois N N') (h2 : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients X X') (h3 : GlobalTheory.TwistChoice.SameForms Y Y')
    (hB : HEq Y.Bsup Y'.Bsup) (hd : HEq X.delta X'.delta) {i : X.Tw} {i' : X'.Tw} (hi : HEq i i') :
    (∀ j b (x : Y.Fm i j b) (x' : Y'.Fm i' j b), HEq x x' → (x ∈ Y.Bsup i j b ↔ x' ∈ Y'.Bsup i' j b) ∧
      (∀ g g', HEq g g' → HEq (Y.actG i j b g x) (Y'.actG i' j b g' x')) ∧
      ∀ k P P', HEq P P' → HEq (Y.hkF i j b k P x) (Y'.hkF i' j b k P' x')) ∧
    (∀ (ε : ∀ i, Bool → (FractionRing (X.O i) →+* ℂ)) (ε' : ∀ i, Bool → (FractionRing (X'.O i) →+* ℂ)), HEq ε ε' →
      ∀ b a a', HEq a a' → ε i b a = ε' i' b a') ∧
    ∀ (P : PlE D.host) (P' : PlE D'.host), HEq P P' → (P ∈ X.S0 i ↔ P' ∈ X'.S0 i') ∧
      ∀ σ' : Formalism.ConjugateSelfDual.G D'.host.E N'.Om, IsFrob (F := D'.host.E) (N'.plOm.1 P') (normV P') σ' →
        ∃ σ : Formalism.ConjugateSelfDual.G D.host.E N.Om, IsFrob (F := D.host.E) (N.plOm.1 P) (normV P) σ ∧ ∀ b : Bool,
          HEq (algebraMap (X.O i) (FractionRing (X.O i)) (algebraMap (X.O0 i) (X.O i)
              ((if b then X.delta i σ else (X.delta i σ)⁻¹ : (X.O0 i)ˣ) : X.O0 i)))
            (algebraMap (X'.O i') (FractionRing (X'.O i')) (algebraMap (X'.O0 i') (X'.O i')
              ((if b then X'.delta i' σ' else (X'.delta i' σ')⁻¹ : (X'.O0 i')ˣ) : X'.O0 i'))) := by
  obtain ⟨a1, a2, -, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  have xTw := h2.Tw
  have fixedFieldTransport_baseIntegerRing_heq := h2.O0
  have fixedFieldTransport_baseIntegerCommRing_heq := h2.crO0
  have xO := h2.O
  have xcrO := h2.crO
  have xalgO := h2.algO
  have fixedFieldTransport_initialPlaceSet_heq := h2.S0
  have yFm := h3.Fm
  have yacgFm := h3.acgFm
  have ymodFmK := h3.modFmK
  have ymodFmO := h3.modFmO
  have yactG := h3.actG
  have yhkF := h3.hkF
  clear h2 h3
  cases D; cases D'
  dsimp only at a1 a2
  subst a1; subst a2
  cases N; cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases X; cases X'
  dsimp only at xTw fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq xO xcrO xalgO fixedFieldTransport_initialPlaceSet_heq hd
  subst xTw; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst xO; subst xcrO; subst xalgO; subst fixedFieldTransport_initialPlaceSet_heq; subst hd
  cases Y; cases Y'
  dsimp only at yFm yacgFm ymodFmK ymodFmO yactG yhkF hB
  subst yFm; subst yacgFm; subst ymodFmK; subst ymodFmO; subst yactG; subst yhkF; subst hB
  subst hi
  refine ⟨fun j b x x' hx => ?_, fun ε ε' hε b a a' ha => ?_, fun P P' hP => ?_⟩
  · subst hx
    exact ⟨Iff.rfl, fun g g' h => by subst h; rfl, fun k P P' h => by subst h; rfl⟩
  · subst hε; subst ha; rfl
  · subst hP
    exact ⟨Iff.rfl, fun σ hσ => ⟨σ, hσ, fun _ => HEq.rfl⟩⟩

section Ext

variable {LL LL' Ks Ks' WL WL' G G' : Type} [Field LL] [Field LL'] [NumberField LL']
  [Field Ks] [NumberField Ks] [Algebra Ks LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' LL']
  [AddCommGroup WL] [Module LL WL] [Module Ks WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] [IsScalarTower Ks LL WL]
  [AddCommGroup WL'] [Module LL' WL'] [Module Ks' WL'] [Module (𝓞 Ks') WL'] [IsScalarTower (𝓞 Ks') Ks' WL']
  [IsScalarTower Ks' LL' WL']
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {W' : (LL' →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)]
  [Group G] [Group G']
  {ι : LL →+* LL'} {eK : Ks ≃+* Ks'} {γ : G ≃* G'} {A : Arith.FormsL LL Ks WL W G} {A' : Arith.FormsL LL' Ks' WL' W' G'}

end Ext

end GlobalTheory.TwInputs.Move.Forms

end
end

