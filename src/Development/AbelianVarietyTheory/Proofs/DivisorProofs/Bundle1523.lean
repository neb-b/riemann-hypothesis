module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorRationalTranslateMemThetaFunctions
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCoordinatesModPrimeSelfDualStabilizer
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalGroupJetsChart
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0044

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitInertFactorizationUnitaryLatticeStabi
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.UnitaryFactor

section Glue

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def glue (e : A) (X Y : Matrix n n A) : Matrix n n A := e • X + (1 - e) • Y

theorem glue_apply (e : A) (X Y : Matrix n n A) (i j : n) :
    glue e X Y i j = e * X i j + (1 - e) * Y i j := by
  simp [glue, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem glue_self (e : A) (X : Matrix n n A) : glue e X X = X := by
  rw [glue, ← add_smul]; simp

theorem glue_mul {e : A} (he : e * e = e) (X Y X' Y' : Matrix n n A) :
    glue e X Y * glue e X' Y' = glue e (X * X') (Y * Y') := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := by linear_combination he
  simp only [glue, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he, h1, h2, h3,
    zero_smul, add_zero, zero_add, smul_add]

theorem glue_map (f : A →+* A) (e : A) (X Y : Matrix n n A) :
    (glue e X Y).map f = glue (f e) (X.map f) (Y.map f) := by
  ext i j; simp [glue_apply, Matrix.map_apply]

theorem glue_transpose (e : A) (X Y : Matrix n n A) : (glue e X Y).transpose = glue e X.transpose Y.transpose := by
  ext i j; simp [glue_apply]

theorem prod_glue {e : A} (he : e * e = e) (s : Finset n) (f g : n → A) :
    ∏ i ∈ s, (e * f i + (1 - e) * g i) = e * ∏ i ∈ s, f i + (1 - e) * ∏ i ∈ s, g i := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro j s hj ih
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.prod_insert hj, ih]
    linear_combination (f j * ∏ i ∈ s, f i - g j * ∏ i ∈ s, f i - f j * ∏ i ∈ s, g i + g j * ∏ i ∈ s, g i) * he

theorem det_glue {e : A} (he : e * e = e) (X Y : Matrix n n A) :
    (glue e X Y).det = e * X.det + (1 - e) * Y.det := by
  rw [Matrix.det_apply', Matrix.det_apply', Matrix.det_apply', Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [glue_apply]
  rw [prod_glue he]
  ring

theorem exists_glue_left {e : A} (he : e * e = e) (g : GL n A) :
    ∃ U : GL n A, (U : Matrix n n A) = glue e (g : Matrix n n A) 1 ∧
      ((U⁻¹ : GL n A) : Matrix n n A) = glue e ((g⁻¹ : GL n A) : Matrix n n A) 1 :=
  ⟨⟨glue e (g : Matrix n n A) 1, glue e ((g⁻¹ : GL n A) : Matrix n n A) 1,
    by rw [glue_mul he, Units.mul_inv, Matrix.one_mul, glue_self],
    by rw [glue_mul he, Units.inv_mul, Matrix.one_mul, glue_self]⟩, rfl, rfl⟩

theorem exists_glue_right {e : A} (he : e * e = e) (g : GL n A) :
    ∃ U : GL n A, (U : Matrix n n A) = glue e 1 (g : Matrix n n A) ∧
      ((U⁻¹ : GL n A) : Matrix n n A) = glue e 1 ((g⁻¹ : GL n A) : Matrix n n A) :=
  ⟨⟨glue e 1 (g : Matrix n n A), glue e 1 ((g⁻¹ : GL n A) : Matrix n n A),
    by rw [glue_mul he, Units.mul_inv, Matrix.one_mul, glue_self],
    by rw [glue_mul he, Units.inv_mul, Matrix.one_mul, glue_self]⟩, rfl, rfl⟩

theorem glue_left_sub (e : A) (X : Matrix n n A) (i j : n) :
    glue e X 1 i j - (1 : Matrix n n A) i j = e * (X i j - (1 : Matrix n n A) i j) := by
  rw [glue_apply]; ring

theorem glue_right_sub (e : A) (X : Matrix n n A) (i j : n) :
    glue e 1 X i j - (1 : Matrix n n A) i j = (1 - e) * (X i j - (1 : Matrix n n A) i j) := by
  rw [glue_apply]; ring

theorem alg_sub_one {ε η u : A} (h2 : ε * η = 0) (h1' : η * η = η) :
    (1 - η) + η * u - 1 = (ε + η) * (η * (u - 1)) := by
  linear_combination (1 - u) * (h2 + h1')

theorem alg_norm {ε η u v : A} (h1 : ε * ε = ε) (h2 : ε * η = 0) (hu : u * v = 1) :
    (1 - η) + η * u = ((1 - (ε + η)) + (ε + η) * u) * ((1 - ε) + ε * v) := by
  linear_combination (-(1 - u - v + u * v)) * (h1 + h2) - ε * hu

theorem alg_inv {η u v : A} (h1' : η * η = η) (hu : u * v = 1) :
    ((1 - η) + η * u) * ((1 - η) + η * v) = 1 := by
  linear_combination (1 - u - v + u * v) * h1' + η * hu

end Glue

end GlobalTheory.UnitaryFactor

namespace GlobalTheory.UnitaryFactor

theorem one_mem_ohE (D : D7) {a : ℕ} (i j : Fin a) : (1 : Matrix (Fin a) (Fin a) (AE D)) i j ∈ OhE D := by
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _


set_option maxHeartbeats 2000000 in
theorem exists_split_inert_factor : ∀ (D : D7) {a : ℕ} (k : GA D a), k ∈ intG D a → ∃ (ks ki : GA D a) (x : (AE D)ˣ), k = ks * ki ∧ ks ∈ intG D a ∧ ki ∈ intG D a ∧ SuppSplit D (ks : GL (Fin a) (AE D)) ∧ SuppInert D (ki : GL (Fin a) (AE D)) ∧ (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x : AE D) - 1)) ∧ x = Matrix.GeneralLinearGroup.det (ks : GL (Fin a) (AE D)) * sgU D x ∧ IntU D x ∧ ∃ η ∈ OhE D, (x : AE D) - 1 = η * (((Matrix.GeneralLinearGroup.det (k : GL (Fin a) (AE D)) : (AE D)ˣ) : AE D) - 1) := by
  intro D a k hk
  have hkI : IntG D (k : GL (Fin a) (AE D)) := (GlobalTheory.NormSum.mem_intG k).1 hk
  have hgu : (((k : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)).map (sgA D)).transpose *
      ((k : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) = 1 :=
    (GlobalTheory.NormSum.PtsMem.mem_GA D _).1 k.2
  have hu : ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) (AE D)) : (AE D)ˣ) : AE D) *
      sgA D ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) (AE D)) : (AE D)ˣ) : AE D) = 1 :=
    GlobalTheory.NormSum.VacMove.det_norm D k
  have hum := GlobalTheory.NormSum.VacMove.det_int D _ hkI
  generalize hg : (k : GL (Fin a) (AE D)) = g at hkI hgu hu hum ⊢
  have hdg : ((Matrix.GeneralLinearGroup.det g : (AE D)ˣ) : AE D) = (g : Matrix (Fin a) (Fin a) (AE D)).det :=
    Matrix.GeneralLinearGroup.val_det_apply g
  generalize ((Matrix.GeneralLinearGroup.det g : (AE D)ˣ) : AE D) = u at hu hum hdg ⊢
  obtain ⟨ε, hε, h1, h2, h3⟩ := GlobalTheory.NormSum.VacMove.exists_half_idem D
  have hηε : sgA D (sgA D ε) = ε := GlobalTheory.NormSum.VacMove.sgA_sgA D ε
  have hηm : sgA D ε ∈ OhE D := GlobalTheory.NormSum.VacMove.sgA_mem D hε
  have h1' : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, h1]
  generalize hη : sgA D ε = η at hηε hηm h1' h2 h3 ⊢
  have hPP : (ε + η) * (ε + η) = ε + η := by linear_combination h1 + h1' + 2 * h2
  have hPs : sgA D (ε + η) = ε + η := by rw [map_add (f := _), hη, hηε, add_comm]
  have hPm : ε + η ∈ OhE D := add_mem hε hηm
  have h1m : (1 : Matrix (Fin a) (Fin a) (AE D)).map (sgA D) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  obtain ⟨ks, hks1, hks2⟩ := exists_glue_left hPP g
  obtain ⟨ki, hki1, hki2⟩ := exists_glue_right hPP g
  have hksG : ks ∈ GA D a := by
    rw [GlobalTheory.NormSum.PtsMem.mem_GA, hks1, glue_map, hPs, h1m, glue_transpose, Matrix.transpose_one, glue_mul hPP, hgu,
      Matrix.one_mul, glue_self]
  have hkiG : ki ∈ GA D a := by
    rw [GlobalTheory.NormSum.PtsMem.mem_GA, hki1, glue_map, hPs, h1m, glue_transpose, Matrix.transpose_one, glue_mul hPP, hgu,
      Matrix.one_mul, glue_self]
  have hdet : ((Matrix.GeneralLinearGroup.det ks : (AE D)ˣ) : AE D) = (1 - (ε + η)) + (ε + η) * u := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hks1, det_glue hPP, Matrix.det_one, hdg]
    ring
  have hx : ((1 - η) + η * u) * ((1 - η) + η * sgA D u) = 1 := by
    exact alg_inv h1' hu
  obtain ⟨x, hx1, hx2⟩ : ∃ x : (AE D)ˣ, (x : AE D) = (1 - η) + η * u ∧
      ((x⁻¹ : (AE D)ˣ) : AE D) = (1 - η) + η * sgA D u :=
    ⟨⟨_, _, hx, by rw [mul_comm, hx]⟩, rfl, rfl⟩
  refine ⟨⟨ks, hksG⟩, ⟨ki, hkiG⟩, x, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext; apply Units.ext
    show ((k : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) = (ks : Matrix (Fin a) (Fin a) (AE D)) * ki
    rw [hg, hks1, hki1, glue_mul hPP, Matrix.mul_one, Matrix.one_mul, glue_self]
  · exact (GlobalTheory.NormSum.mem_intG _).2 fun i j =>
      ⟨by rw [hks1, glue_apply]
          exact add_mem (mul_mem hPm (hkI i j).1) (mul_mem (sub_mem (one_mem _) hPm) (one_mem_ohE D i j)),
       by rw [hks2, glue_apply]
          exact add_mem (mul_mem hPm (hkI i j).2) (mul_mem (sub_mem (one_mem _) hPm) (one_mem_ohE D i j))⟩
  · exact (GlobalTheory.NormSum.mem_intG _).2 fun i j =>
      ⟨by rw [hki1, glue_apply]
          exact add_mem (mul_mem hPm (one_mem_ohE D i j)) (mul_mem (sub_mem (one_mem _) hPm) (hkI i j).1),
       by rw [hki2, glue_apply]
          exact add_mem (mul_mem hPm (one_mem_ohE D i j)) (mul_mem (sub_mem (one_mem _) hPm) (hkI i j).2)⟩
  · intro q hq hi i j
    show ZeroAt D q ((ks : Matrix (Fin a) (Fin a) (AE D)) i j - (1 : Matrix (Fin a) (Fin a) (AE D)) i j)
    rw [hks1, glue_left_sub]
    exact GlobalTheory.NormSum.VacMove.zeroAt_mul D hq ((h3 q hq).1 hi) _
  · intro q hq hi i j
    show ZeroAt D q ((ki : Matrix (Fin a) (Fin a) (AE D)) i j - (1 : Matrix (Fin a) (Fin a) (AE D)) i j)
    rw [hki1, glue_right_sub]
    exact GlobalTheory.NormSum.VacMove.zeroAt_mul D hq ((h3 q hq).2 hi) _
  · intro q hq hi
    have e : ((x : (AE D)ˣ) : AE D) - 1 = (ε + η) * (η * (u - 1)) := by
      rw [hx1]; exact alg_sub_one h2 h1'
    rw [e]
    exact GlobalTheory.NormSum.VacMove.zeroAt_mul D hq ((h3 q hq).1 hi) _
  · apply Units.ext
    show (x : AE D) = ((Matrix.GeneralLinearGroup.det ks : (AE D)ˣ) : AE D) * sgA D (x : AE D)
    have hs : sgA D ((1 - η) + η * u) = (1 - ε) + ε * sgA D u := by
      rw [map_add (sgA D), map_sub (sgA D), map_one (sgA D), map_mul (sgA D), hηε]
    rw [hdet, hx1, hs]
    exact alg_norm h1 h2 hu
  · refine ⟨?_, ?_⟩
    · rw [hx1]; exact add_mem (sub_mem (one_mem _) hηm) (mul_mem hηm hum)
    · rw [hx2]; exact add_mem (sub_mem (one_mem _) hηm) (mul_mem hηm (GlobalTheory.NormSum.VacMove.sgA_mem D hum))
  · refine ⟨η, hηm, ?_⟩
    rw [hx1]
    ring

end GlobalTheory.UnitaryFactor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTypeFrameCoverLevelMapsReductions
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU)
open GlobalTheory.LevPull (CongMod)
open scoped TensorProduct Matrix

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.TypeFrameCover

open GlobalTheory.LevDesc

section Primes

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}

theorem typePrime_isPrime {l : Level H} (hM : l.M = D.host.g 0 * D.host.g 1) (v : Sq D.host) :
    (typePrime l v).IsPrime := by
  refine halfPrime_isPrime l v.2.1.isMaximal ?_
  obtain ⟨k, hk⟩ := g_dvd (D := D) v.1
  rw [hM, hk, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ v.2.2

theorem typePrime_eq {l l₂ : Level H} (hM : l.M = D.host.g 0 * D.host.g 1) (hl₂ : IsTypeLevel l₂)
    (hle : l₂.Mb ≤ l.Mb) (v : Sq D.host) : typePrime l₂ v = typePrime l v := by
  obtain ⟨hP, hN⟩ := hl₂.typePrime_spec v
  have hne : typePrime l₂ v ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hN
    exact (D.host.g_prime v.1).ne_zero hN.symm
  exact (hP.isMaximal hne).eq_of_le (typePrime_isPrime hM v).ne_top (sup_le_sup_right hle _)

theorem exists_mem_eq {l : Level H} (hM : l.M = D.host.g 0 * D.host.g 1) {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (hMb : l.Mb = ∏ PP ∈ Pg, PP.asIdeal) (v : Sq D.host) : ∃ PP ∈ Pg, PP.asIdeal = typePrime l v := by
  have hP := typePrime_isPrime hM v
  have h1 : ∏ PP ∈ Pg, PP.asIdeal ≤ typePrime l v := hMb ▸ le_sup_left
  obtain ⟨PP, hPP, h2⟩ := (hP.prod_le).1 h1
  exact ⟨PP, hPP, PP.isMaximal.eq_of_le hP.ne_top h2⟩

theorem exists_equiv {l : Level H} (hM : l.M = D.host.g 0 * D.host.g 1) {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (hMb : l.Mb = ∏ PP ∈ Pg, PP.asIdeal) : ∃ e : Sq D.host ≃ Pg, ∀ v, (e v).1.asIdeal = typePrime l v := by
  choose f hf hfe using exists_mem_eq hM hMb
  have hinj : Function.Injective (fun v ↦ (⟨f v, hf v⟩ : Pg)) := by
    intro v w h
    have h' : typePrime l v = typePrime l w := by
      rw [← hfe v, ← hfe w]; exact congrArg (fun x : Pg ↦ x.1.asIdeal) h
    by_contra hvw
    have hc := typePrime_coprime (l := l) hvw
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq, h', sup_idem] at hc
    exact (typePrime_isPrime hM w).ne_top hc
  have hsurj : Function.Surjective (fun v ↦ (⟨f v, hf v⟩ : Pg)) := by
    rintro ⟨PP, hPP⟩
    have hle : l.Mb ≤ PP.asIdeal := hMb ▸ Ideal.prod_le_inf.trans (Finset.inf_le hPP)
    have hm : ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      rw [← Nat.cast_mul, ← hM]; exact hle (natCast_M_mem l)
    have hk : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      rcases PP.isPrime.mem_or_mem hm with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    obtain ⟨k, hk⟩ := hk
    have hg : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) PP.asIdeal := by
      rw [Ideal.mem_comap, map_natCast]; exact hk
    let w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F) :=
      ⟨Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) PP.asIdeal, inferInstance, fun e ↦ by
        rw [e, Ideal.mem_bot] at hg
        exact (D.host.g_prime k).ne_zero (by exact_mod_cast hg)⟩
    have he : typePrime l ⟨k, ⟨w, hg⟩⟩ = PP.asIdeal :=
      halfPrime_eq l w.isMaximal PP.isPrime (sup_le hle Ideal.map_comap_le)
    refine ⟨⟨k, ⟨w, hg⟩⟩, Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext ?_)⟩
    exact (hfe _).trans he
  exact ⟨Equiv.ofBijective _ ⟨hinj, hsurj⟩, fun v ↦ hfe v⟩

theorem nonempty_iso {l₂ : Level H} (hl₂ : IsTypeLevel l₂) (v : Sq D.host) (PP : Formalism.L2.DIV.Pl D.host.E)
    (hPP : PP.asIdeal = typePrime l₂ v) : Nonempty (ZMod (D.host.g v.1) ≃+* kP PP) := by
  have hc : Nat.card (kP PP) = D.host.g v.1 := by
    rw [← (hl₂.typePrime_spec v).2, ← hPP, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (kP PP) := Nat.finite_of_card_ne_zero (hc ▸ (D.host.g_prime _).ne_zero)
  haveI := Fintype.ofFinite (kP PP)
  exact ⟨ZMod.ringEquivOfPrime (kP PP) (D.host.g_prime v.1) (by rw [← Nat.card_eq_fintype_card, hc])⟩

end Primes

section Frame

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

theorem exists_frame {l₂ : Level H} (hl₂ : IsTypeLevel l₂) (hr : Dw.p + Dw.q = D.R.r) (v : Sq D.host)
    (PP : Formalism.L2.DIV.Pl D.host.E) (hPP : PP.asIdeal = typePrime l₂ v) (iso : ZMod (D.host.g v.1) ≃+* kP PP)
    {n : ℕ} (hn : n = D.R.r) (φ : Dw.La →ₗ[𝓞 D.host.E] (Fin n → kP PP)) (hφ : Function.Surjective φ) :
    ∃ f : QMod Dw.La (typePrime l₂ v) ≃+ (Fin D.R.r → ZMod (D.host.g v.1)),
      ∀ x : Dw.La, f (Submodule.Quotient.mk x) = fun j ↦ iso.symm (φ x (Fin.cast hn.symm j)) := by
  subst hn
  have hker : typePrime l₂ v • (⊤ : Submodule (𝓞 D.host.E) Dw.La) ≤ LinearMap.ker φ := by
    rw [← hPP, Submodule.smul_le]
    intro a ha x _
    rw [LinearMap.mem_ker, map_smul]
    funext j
    rw [Pi.smul_apply, Pi.zero_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_mul]
  let ψ := (typePrime l₂ v • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).liftQ φ hker
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  have hc : Nat.card (𝓞 D.host.E ⧸ typePrime l₂ v) = D.host.g v.1 := by
    rw [← (hl₂.typePrime_spec v).2, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.host.E ⧸ typePrime l₂ v) := Nat.finite_of_card_ne_zero (hc ▸ (D.host.g_prime _).ne_zero)
  haveI := Dw.fin
  haveI := Dw.proj
  have hN : Nat.card (QMod Dw.La (typePrime l₂ v)) = D.host.g v.1 ^ D.R.r := by
    rw [GlobalTheory.natCard_quot_smul_top_of_projective, hc, Dw.rank, hr]
  have hc' : Nat.card (kP PP) = D.host.g v.1 := by
    rw [← (hl₂.typePrime_spec v).2, ← hPP, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hN' : Nat.card (Fin D.R.r → kP PP) = D.host.g v.1 ^ D.R.r := by
    rw [Nat.card_fun, hc', Nat.card_eq_fintype_card, Fintype.card_fin]
  haveI : Finite (QMod Dw.La (typePrime l₂ v)) :=
    Nat.finite_of_card_ne_zero (by rw [hN]; exact pow_ne_zero _ (D.host.g_prime _).ne_zero)
  have hψb : Function.Bijective ψ := hψs.bijective_of_nat_card_le (by rw [hN, hN'])
  let e1 : QMod Dw.La (typePrime l₂ v) ≃+ (Fin D.R.r → kP PP) := AddEquiv.ofBijective ψ.toAddMonoidHom hψb
  let e2 : (Fin D.R.r → kP PP) ≃+ (Fin D.R.r → ZMod (D.host.g v.1)) :=
    AddEquiv.piCongrRight (fun _ ↦ iso.symm.toAddEquiv)
  exact ⟨e1.trans e2, fun x ↦ rfl⟩

end Frame

section Main

theorem mulVec_reindex {K : Type} [CommRing K] {n r : ℕ} (h : n = r) (hr : r ≤ n) (Mn : Matrix (Fin n) (Fin n) K)
    (y z : Fin n → K)
    (hyz : (fun j ↦ y (Fin.cast h.symm j)) = Mn.submatrix (Fin.castLE hr) (Fin.castLE hr) *ᵥ fun j ↦ z (Fin.cast h.symm j)) :
    y = Mn *ᵥ z := by
  subst h
  exact hyz

theorem typeFrame_cover : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m), IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1 → ∀ (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l l₂ : Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → Dw.p + Dw.q = D.R.r → l.A = 1 → l.M = D.host.g 0 * D.host.g 1 → IsTypeLevel l₂ → l₂.Mb ≤ l.Mb → l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → ∀ lev : G → Dw.La →ₗ[𝓞 D.host.E] Dw.La, LevIs R i ι l.M (Mfr l) lev → ∃ (fr : TypeFrame Dw l₂) (e : Sq D.host ≃ R.Pg) (iso : ∀ v : Sq D.host, ZMod (D.host.g v.1) ≃+* kP (e v).1), (∀ (γ : LevelAut Dw l₂) (g : G), (∀ v, R.eG g (e v) = Formalism.UG.bc (iso v : ZMod (D.host.g v.1) →+* kP (e v).1) (typeRed fr γ v)) → CongMod l.Mb (liftLa γ) (lev g)) ∧ ∀ γ : LevelAut Dw l₂, CongMod l.Mb (liftLa γ) LinearMap.id → typeRed fr γ = 1 := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i hβ H Dw l l₂ ι hι hr hA hM hl₂ hle hMb lev hlev
  obtain ⟨e, he⟩ := exists_equiv hM hMb
  have htp : ∀ v, typePrime l₂ v = typePrime l v := typePrime_eq hM hl₂ hle
  have he₂ : ∀ v, (e v).1.asIdeal = typePrime l₂ v := fun v ↦ (he v).trans (htp v).symm
  let iso : ∀ v : Sq D.host, ZMod (D.host.g v.1) ≃+* kP (e v).1 := fun v ↦ (nonempty_iso hl₂ v _ (he₂ v)).some
  have hφ := fun v : Sq D.host ↦ _root_.GlobalTheory.LatCoordRed.coord_red D (Wc D i) (R.βW i) (R.ΛW i) hβ Dw.La ι hι (e v).1
  choose φ hφs hφk using hφ
  have hfr0 := fun v ↦ exists_frame hl₂ hr v (e v).1 (he₂ v) (iso v) (rank_Wc i) (φ v) (hφs v)
  choose fr hfr using hfr0
  refine ⟨fr, e, iso, ?_, ?_⟩
  · intro γ g hg a
    obtain ⟨κ, hκ, hκa⟩ := hlev g
    have hSt : Lev.finE (Wc D i) κ ∈ St (R.βW i) := parLev_St hκ.2.1
    have hin : ∀ v, l.Mb ≤ (e v).1.asIdeal := fun v ↦ by rw [he v]; exact le_sup_left
    have hkill : ∀ v, ∀ u ∈ l.Mb, ∀ x : Dw.La, φ v (u • x) = 0 := by
      intro v u hu x
      rw [map_smul]
      funext j
      rw [Pi.smul_apply, Pi.zero_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem.2 (hin v hu), zero_mul]
    have hcop : l.Mb ⊔ Mfr l = ⊤ := l.coprime
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 (hcop ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ l.Mb ⊔ Mfr l)
    have ha : a = u • a + w • a := by rw [← add_smul, huw, one_smul]
    have hlevφ : ∀ v, φ v (lev g a) = (redFn (R.βW i) (e v).1 (Lev.finE (Wc D i) κ)).1 *ᵥ φ v a := by
      intro v
      have h1 := hφk v κ hSt l.M (hin v (natCast_M_mem l)) (w • a) (lev g (w • a))
        (hκa (w • a) (Submodule.smul_mem_smul hw Submodule.mem_top))
      have h2 : φ v (w • a) = φ v a := by
        conv_rhs => rw [ha]
        rw [map_add (f := _), hkill v u hu, zero_add]
      have h3 : φ v (lev g a) = φ v (lev g (w • a)) := by
        conv_lhs => rw [ha]
        rw [map_add (f := _), map_add (f := _), map_smul, hkill v u hu, zero_add]
      rw [h3, h1, h2]
    have hliftφ : ∀ v, φ v (liftLa γ a) = φ v (lev g a) := by
      intro v
      have hγa : γ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (liftLa γ a) := (liftLa_spec γ a).symm
      have h0 : (typeRed fr γ v : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1))) *ᵥ
          fr v (Submodule.Quotient.mk a) = fr v (Submodule.Quotient.mk (liftLa γ a)) := by
        have h00 := GlobalTheory.LevDesc.typeRed_mulVec fr γ v (Submodule.Quotient.mk a)
        rw [hγa] at h00
        exact h00
      rw [hfr, hfr] at h0
      have h1 := GlobalTheory.LevelActionPinned.equiv_mulVec (iso v)
        (typeRed fr γ v : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1)))
        (fun j ↦ (iso v).symm (φ v a (Fin.cast (rank_Wc i).symm j)))
      rw [h0] at h1
      simp only [RingEquiv.apply_symm_apply] at h1
      have hT : (typeRed fr γ v : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1))).map (iso v) =
          (redFn (R.βW i) (e v).1 (Lev.finE (Wc D i) κ) : Matrix _ _ _).submatrix
            (Fin.castLE (R.datWp i R.triv).hr) (Fin.castLE (R.datWp i R.triv).hr) := by
        have h5 : R.eG g (e v) = upperLeftBlock (R.datWp i R.triv).hr (redFn (R.βW i) (e v).1 (Lev.finE (Wc D i) κ)) :=
          (congrFun hκ.2.2 (e v)).symm
        have h6 := upper_block_val_submatrix (R.datWp i R.triv).hr (blockTri_blkOf_le _ _ (parLev_g hκ.2.1 (e v).2))
        rw [← h5, hg v] at h6
        exact h6
      rw [hT] at h1
      rw [hlevφ v]
      exact mulVec_reindex (rank_Wc i) _ _ _ _ h1
    have hall : ∀ v, liftLa γ a - lev g a ∈ typePrime l v • (⊤ : Submodule (𝓞 D.host.E) Dw.La) := by
      intro v
      have hx : φ v (liftLa γ a - lev g a) = 0 := by rw [map_sub, sub_eq_zero, hliftφ v]
      have h4 : fr v (Submodule.Quotient.mk (liftLa γ a - lev g a)) = 0 := by
        rw [hfr, hx]
        funext j
        simp
      have h5 := (AddEquiv.map_eq_zero_iff (fr v)).1 h4
      rw [Submodule.Quotient.mk_eq_zero, htp] at h5
      exact h5
    have h3 := mem_iInf_smul_top (typePrime_coprime (l := l)) hall
    have hle' : ⨅ v, typePrime l v ≤ l.Mb := iInf_typePrime_le.trans
      (sup_le le_rfl ((Ideal.span_singleton_le_iff_mem _).2 (by rw [← hM]; exact natCast_M_mem l)))
    exact Submodule.smul_mono_left hle' h3
  · intro γ hγ
    rw [typeRed_eq_one, mem_grpR_iff]
    intro v q
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have h1 : γ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (liftLa γ a) := (liftLa_spec γ a).symm
    rw [h1, ← Submodule.Quotient.mk_sub]
    have h2 : liftLa γ a - a ∈ typePrime l₂ v • (⊤ : Submodule (𝓞 D.host.E) Dw.La) :=
      Submodule.smul_mono_left ((le_sup_left : l.Mb ≤ typePrime l v).trans (htp v).ge) (hγ a)
    exact map_mem_smul_top (l₂.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ h2

end Main

end GlobalTheory.TypeFrameCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
section
noncomputable section

namespace GlobalTheory.PtDeg

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def FrameCoord {K : Type} [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K)
    {B : GlobalTheory.CM.PAT H (Sp (𝓞 K))} {t₀ : SAB H (Sp K)} (m1 : SABMap t₀ Xo.univ.t y.x)
    (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ)
    (v : Fin (Dw.mult ρ) → Fin F.P₀.g → K) : Prop :=
  ∀ i, ∃ (u : Sp (DualNumber K) ⟶ t₀.G.left) (w : epsR K ⟶ F.P₀.A),
    u ≫ m1.φ = y.u ρ i ∧ u ≫ m2.φ = w.left ≫ F.φ ∧ IsLieComb (v i) F.v w

def LocBasis {K : Type} [Field K] [NumberField K] {n : ℕ} (𝔓 : HeightOneSpectrum (𝓞 K))
    (L : Submodule (𝓞 K) (Fin n → K)) {m : ℕ} (b : Fin m → Fin n → K) : Prop :=
  (∀ i, b i ∈ L) ∧ LinearIndependent K b ∧
    ∀ x ∈ L, ∃ d : 𝓞 K, d ∉ 𝔓.asIdeal ∧ d • x ∈ Submodule.span (𝓞 K) (Set.range b)

end GlobalTheory.PtDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestBis
section
open NumberField IsLocalRing Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

namespace GlobalTheory.IntegralChartCover

theorem cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y), ∃ (T' : CDVR) (φ : T.V →+* T'.V) (t' : SAB H (Sp T'.V)), Function.Injective φ ∧ φ.Finite ∧ UpFBr.GeoJ T'.V t'.G (𝓞 E) (fun a => t'.act.act a) (chD C3.ch) (fun i => MvPowerSeries.map φ (C3.FT i)) (fun a i => MvPowerSeries.map φ (C3.actT a i)) := by
  intro E _ _ _ H Dw lv Xo c inst hstar T io y C3
  obtain rfl : inst = H.starRing := GlobalTheory.PowGerm.starRing_ext_of_star inst H.starRing hstar
  letI := H.starRing
  letI := io.toAlgebra
  obtain ⟨T', φ, t', m, hi, hf, ⟨P⟩⟩ := GlobalTheory.ChartCharacters.exists_finite_ext_pelUnif Xo T C3.I.G C3.I.t' C3.I.m2 _ C3.I.m1
  obtain ⟨F', x', act', hF, hA, hx, ha⟩ := GlobalTheory.integralChart_baseChange E H Dw lv Xo c T io y C3 T' φ t' m
  exact ⟨T', φ, t', hi, hf, P.D, P.A, P.U.toUnifPre, F', x', _, t'.act.toRingAct, P.oD, P.oA, act', hF, funext hA, fun _ => rfl, hx, P.lin, ha⟩

end GlobalTheory.IntegralChartCover
end

