module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UBoundOffTop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0756
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0737
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLevelTypePrimeDatumLocallySmall
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0744
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
public import GroundTheory.AutomorphicForms.ReductionSiegel

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleOffTypeFamilyBound
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory.LevelBudget

variable {D : D7} {L : SizeData₂ D}

theorem ETpi_le (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (u : D.what₂.Word) :
    Formalism.MainNotions.product_first_zeroth_parts.ETpi D u ≤ 12 * D.R.f * L.sc.b := by
  have hb := GlobalTheory.HCEntries.one_le_b L
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  unfold Formalism.MainNotions.product_first_zeroth_parts.ETpi
  have hN := GlobalTheory.LevelLoss.N_le_b h P
  have hNe : (D.R.N D.R.m : ℝ) = D.R.k + D.R.m * (D.R.t + 1) := by unfold Ranks.N; push_cast; ring
  have r2 := (GlobalTheory.FockDegreeGap.ranks_le D).2
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have h1 : ∑ τ : D.what₂.Tau, (Formalism.MainNotions.product_first_zeroth_parts.Wt D u τ : ℝ) ≤ D.R.f * (5 * L.sc.b) := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun τ : D.what₂.Tau => (Formalism.MainNotions.product_first_zeroth_parts.Wt D u τ : ℝ)) _
      (fun τ _ => GlobalTheory.LevelLoss.Wtau_le h P hx u τ)
    rwa [Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul] at this
  have h2 : ((Formalism.MainNotions.product_first_zeroth_parts.tops D).card : ℝ) ≤ D.R.f := by
    have := Finset.card_le_univ (Formalism.MainNotions.product_first_zeroth_parts.tops D)
    rw [D.what₂.card_Tau] at this
    exact_mod_cast this
  have h3 : ((D.R.t : ℝ) + 1) * ((D.R.m : ℝ) + 1) ≤ L.sc.b := by nlinarith
  have h4 : ((Formalism.MainNotions.product_first_zeroth_parts.tops D).card : ℝ) * (((D.R.t : ℝ) + 1) * ((D.R.m : ℝ) + 1)) ≤ D.R.f * L.sc.b :=
    mul_le_mul h2 h3 (by positivity) hf0
  have h5 : (D.R.f : ℝ) * D.R.N D.R.m ≤ D.R.f * L.sc.b :=
    mul_le_mul_of_nonneg_left (by linarith [Nat.cast_nonneg (α := ℝ) (D.R.N D.R.m)]) hf0
  have h6 : 0 ≤ (D.R.f : ℝ) * L.sc.b := by positivity
  nlinarith

theorem admissible_off_type_level_budget : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → TuSize Fm → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.LevelPrimeBudget (Fm.D x i) (Fm.L x i) C := by
  intro eps Fm _ _ ⟨x₁, h1⟩
  refine ⟨max (12 * Fm.CTu) 0, max 2 x₁, le_max_right _ _, fun x hx0 hx i u => ⟨fun S hS => GlobalTheory.SeenHalf.seen_half Fm x hx i u S hS, ?_⟩⟩
  have a := ETpi_le (Fm.sizes x hx i) (Fm.params x hx i)
    (by rw [Fm.L_x x i hx]; exact (le_max_left _ _).trans hx0) u
  have b := (h1 x ((le_max_right _ _).trans hx0) i).2 u
  have hb := GlobalTheory.HCEntries.one_le_b (Fm.L x i)
  have hT : (1 : ℝ) ≤ (((Fm.D x i).mem u).A.T : ℝ) := by exact_mod_cast ((Fm.D x i).mem u).A.T_prime.one_le
  have hl : 0 ≤ Real.log (((Fm.D x i).mem u).A.T : ℝ) := Real.log_nonneg hT
  have e : (Fm.L x i).B0 = (Fm.D x i).R.f * (Fm.D x i).R.m * (Fm.L x i).sc.b * (Fm.L x i).sc.L := rfl
  have hB : 0 ≤ (Fm.L x i).B0 := Formalism.MainNotions.WeightDegreeSizes.loss_bound_nonneg _
  calc Formalism.MainNotions.product_first_zeroth_parts.ETpi (Fm.D x i) u * Real.log (((Fm.D x i).mem u).A.T : ℝ)
      ≤ 12 * (Fm.D x i).R.f * (Fm.L x i).sc.b * Real.log (((Fm.D x i).mem u).A.T : ℝ) :=
        mul_le_mul_of_nonneg_right a hl
    _ ≤ 12 * (Fm.D x i).R.f * (Fm.L x i).sc.b * (Fm.CTu * (Fm.D x i).R.m * (Fm.L x i).sc.L) :=
        mul_le_mul_of_nonneg_left b (by positivity)
    _ = 12 * Fm.CTu * (Fm.L x i).B0 := by rw [e]; ring
    _ ≤ max (12 * Fm.CTu) 0 * (Fm.L x i).B0 := mul_le_mul_of_nonneg_right (le_max_left _ _) hB

end GlobalTheory.LevelBudget
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantEleventh
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.IndexCount

open Formalism.L2.Col.Loc Formalism.L2.Col.LocE GlobalTheory.RowTypeInv GlobalTheory.SymLevelDatum

section

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ)

theorem sclLat_anti (hq : q ≠ 0) {N : ℕ} {e e' : ℕ → ℤ} (h : ∀ l, e l ≤ e' l) : sclLat P q N e' ≤ sclLat P q N e := by
  have hq' : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  intro x hx
  rw [mem_sclLat] at hx ⊢
  intro l
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 (h l.1))
  have h1 : IntAt P ((q : E) ^ k) := (intRing P).pow_mem (intAt_natCast P q) k
  convert h1.mul (hx l) using 1
  rw [show e' l.1 = e l.1 + k by omega, zpow_add₀ hq', zpow_natCast]
  field_simp

theorem mem_sclLat_succ (hq : q ≠ 0) {N : ℕ} (e : ℕ → ℤ) (x : Sp E N) :
    x ∈ sclLat P q N (fun l => e l + 1) ↔ (q : E)⁻¹ • x ∈ sclLat P q N e := by
  have hq' : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  rw [mem_sclLat, mem_sclLat]
  refine forall_congr' fun l => ?_
  rw [zpow_add₀ hq', zpow_one, Pi.smul_apply, smul_eq_mul, mul_inv, mul_assoc]

theorem mem_stabL_of_cong {N : ℕ} {M₀ M M₁ : Submodule (𝓞 E) (Sp E N)} (h₀ : M₀ ≤ M) (h₁ : M ≤ M₁)
    {κ : Sp E N ≃ₗ[E] Sp E N} (hκ : κ ∈ stabL E N M₁) (hc : ∀ y ∈ M₁, κ y - y ∈ M₀) : κ ∈ stabL E N M := by
  intro x
  constructor
  · intro hx
    simpa using M.sub_mem hx (h₀ (hc x ((hκ x).1 (h₁ hx))))
  · intro hx
    simpa using M.add_mem (h₀ (hc x (h₁ hx))) hx

noncomputable def resMat {N : ℕ} (e : ℕ → ℤ) (h : Sp E N ≃ₗ[E] Sp E N) : Fin N × Fin N → 𝓞 E ⧸ P.asIdeal :=
  fun p => redP P (h (eN E N p.2.1) p.1 * (q : E) ^ (e p.2.1 - e p.1.1))

theorem cong_of_resMat_eq (hq : q ≠ 0) (hdiv : ∀ a : E, IntAt P a → redP P a = 0 → IntAt P (a / (q : E)))
    {N : ℕ} {e : ℕ → ℤ} {h h' : Sp E N ≃ₗ[E] Sp E N} (hh : h ∈ stabL E N (sclLat P q N e))
    (hh' : h' ∈ stabL E N (sclLat P q N e)) (hres : resMat P q e h = resMat P q e h') :
    ∀ y ∈ sclLat P q N e, (h⁻¹ * h') y - y ∈ sclLat P q N (fun l => e l + 1) := by
  have hq' : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  have a1 := (maps_iff P q hq e e h.toLinearMap).1 fun y hy => (hh y).2 hy
  have a2 := (maps_iff P q hq e e h'.toLinearMap).1 fun y hy => (hh' y).2 hy
  have a3 := (maps_iff P q hq e (fun l => e l + 1) (h'.toLinearMap - h.toLinearMap)).2 fun l l' => by
    have b1 : IntAt P (h' (eN E N l'.1) l * (q : E) ^ (e l'.1 - e l.1) - h (eN E N l'.1) l * (q : E) ^ (e l'.1 - e l.1)) :=
      (intRing P).sub_mem (a2 l l') (a1 l l')
    have b2 := reduction_add b1 (a1 l l')
    have b3 : redP P (h (eN E N l'.1) l * (q : E) ^ (e l'.1 - e l.1)) =
      redP P (h' (eN E N l'.1) l * (q : E) ^ (e l'.1 - e l.1)) := congrFun hres (l, l')
    erw [sub_add_cancel, b3, right_eq_add] at b2
    convert hdiv _ b1 b2 using 1
    rw [show e l'.1 - (e l.1 + 1) = e l'.1 - e l.1 - 1 by ring, zpow_sub_one₀ hq']
    simp only [LinearMap.sub_apply, Pi.sub_apply, LinearEquiv.coe_coe]
    field_simp
  intro y hy
  have a4 := a3 y hy
  rw [mem_sclLat_succ P q hq] at a4 ⊢
  rw [← hh, map_smul, map_sub]
  simpa using a4

theorem mem_JGsym_of_cong (hq : q ≠ 0) (k rS r t n c : ℕ) {κ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hκ : κ ∈ stabL E (n + c) (lamY P q n c fun i => i + 1))
    (hc : ∀ y ∈ lamY P q n c fun i => i + 1, κ y - y ∈ sclLat P q (n + c) (fun l => scE n (fun i => i + 1) l + 1)) :
    κ ∈ JGsym P q k rS r t n c := by
  have h₀ : ∀ s, sclLat P q (n + c) (fun l => scE n (fun i => i + 1) l + 1) ≤ flagS P q k rS n c s := fun s =>
    sclLat_anti P q hq fun l => by split_ifs <;> omega
  have h₁ : ∀ s, flagS P q k rS n c s ≤ lamY P q n c fun i => i + 1 := fun s =>
    sclLat_anti P q hq fun l => by split_ifs <;> omega
  refine ⟨hκ, fun s _ => mem_stabL_of_cong (h₀ s) (h₁ s) hκ hc, fun s _ => ⟨mem_stabL_of_cong (h₀ s) (h₁ s) hκ hc, h₀ s (hc _ ?_)⟩⟩
  have hq' : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  unfold lamY bvecS bvecG
  rw [mem_sclLat]
  intro i
  by_cases hi : i.1 = fIdx k c n (symIdxInv k rS s)
  · simp only [Pi.smul_apply, eN, hi, if_true, smul_eq_mul, mul_one]
    rw [inv_mul_cancel₀ (zpow_ne_zero _ hq')]
    exact intAt_one P
  · simp only [Pi.smul_apply, eN, hi, if_false, smul_eq_mul, mul_zero]
    exact intAt_zero P

end

end GlobalTheory.IndexCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantThird
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNormsUnit

theorem mem_of_divs {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {P : HeightOneSpectrum A} (h : P ∈ divs a) :
    a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hf
  · exact hf.mem_toFinset.1 h
  · simp at h

theorem qe_one {X : Fields} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} :
    QE sel ((1 : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) = ∅ := by
  have h : Qprime ((1 : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) = ∅ := by
    change Qprime (1 : Chr X.F X.E X.K) = ∅
    ext v
    simp [Qprime, MonoidHom.ker_one]
  unfold QE
  split_ifs with hf
  · rw [(Set.Finite.toFinset_eq_empty (h := hf)).2 h]
    rfl
  · rfl

theorem exists_prime {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {Sg : Set ℕ} (u : Pr.Word) (P : HeightOneSpectrum (𝓞 X.E)) (hP : P ∈ Sall sel (1 : Tup X.F X.E X.K Sg) u) :
    ∃ l : ℕ, l.Prime ∧ (l : 𝓞 X.E) ∈ P.asIdeal ∧ ¬ l ∣ Pr.cond := by
  classical
  have hg : ∀ i, P ∈ Pr.vG i → ∃ l : ℕ, l.Prime ∧ (l : 𝓞 X.E) ∈ P.asIdeal ∧ ¬ l ∣ Pr.cond := by
    intro i hi
    refine ⟨Pr.g i, hPr.g_prime i, hPr.piG_norm i ▸ P.asIdeal.mul_mem_left _ (mem_of_divs hi), fun hd => ?_⟩
    have h1 : Pr.g i ≡ 1 [MOD Pr.g i] := (hPr.g_cong i).of_dvd hd
    have h2 : Pr.g i ∣ 1 := (Nat.modEq_zero_iff_dvd).1 (h1.symm.trans ((Nat.modEq_zero_iff_dvd).2 dvd_rfl))
    exact (hPr.g_prime i).one_lt.ne' (Nat.dvd_one.1 h2)
  unfold Sall at hP
  simp only [rowSG, uSG, qe_one, Primes.vGs, Finset.mem_union, Finset.notMem_empty, or_false] at hP
  rcases hP with h | h | h
  · have h0 : Pr.piT u ∈ P.asIdeal := mem_of_divs h
    have hT : (Pr.T u : 𝓞 X.E) ∈ P.asIdeal := hPr.piT_norm u ▸ P.asIdeal.mul_mem_right _ h0
    refine ⟨Pr.T u, hPr.T_prime u, hT, fun hd => ?_⟩
    have h1 : (Pr.T u : 𝓞 X.E) ∣ Pr.piT u - 1 :=
      (Nat.cast_dvd_cast (hd.mul_right _)).trans (hPr.piT_cong u)
    have h2 : Pr.piT u - 1 ∈ P.asIdeal := Ideal.mem_of_dvd _ h1 hT
    have h3 := P.asIdeal.sub_mem h0 h2
    rw [sub_sub_cancel] at h3
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h3)
  · exact hg 0 h
  · exact hg 1 h

end GlobalTheory.ColNormsUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantTwelfth
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.CouplingCosets

theorem finite_ncard_cosets {E : Type} [Field E] [NumberField E] {n : ℕ} (A₁ A₀ : Submodule (𝓞 E) (Sp E n)) (c : ℕ) (hc : 0 < c)
    (h : ∀ y ∈ A₁, c • y ∈ A₀) :
    {Y : Set (Sp E n) | ∃ y ∈ A₁, Y = {z | z - y ∈ A₀}}.Finite ∧
      {Y : Set (Sp E n) | ∃ y ∈ A₁, Y = {z | z - y ∈ A₀}}.ncard ≤ c ^ (Module.finrank ℚ E * n) := by
  haveI : Module.Finite ℚ (Sp E n) := Module.Finite.trans E (Sp E n)
  have hd : Module.finrank ℚ (Sp E n) = Module.finrank ℚ E * n := by
    rw [← Module.finrank_mul_finrank ℚ E (Sp E n)]
    simp
  obtain ⟨hf, hle⟩ := GlobalTheory.SemilocalClasses.finite_card_le A₁.subtype.toAddMonoidHom (Submodule.subtype_injective _)
    (A₀.comap A₁.subtype).mkQ.toAddMonoidHom (Submodule.mkQ_surjective _) c hc fun x =>
      (Submodule.Quotient.mk_eq_zero _).2 (h x x.2)
  rw [hd] at hle
  let φ : (A₁ ⧸ A₀.comap A₁.subtype) → Set (Sp E n) := fun q => {z | z - ((Quotient.out q : A₁) : Sp E n) ∈ A₀}
  have hsub : {Y : Set (Sp E n) | ∃ y ∈ A₁, Y = {z | z - y ∈ A₀}} ⊆ Set.range φ := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨Submodule.Quotient.mk ⟨y, hy⟩, ?_⟩
    have h1 : (Submodule.Quotient.mk (Quotient.out (Submodule.Quotient.mk (p := A₀.comap A₁.subtype) ⟨y, hy⟩)) :
        A₁ ⧸ A₀.comap A₁.subtype) = Submodule.Quotient.mk ⟨y, hy⟩ := Quotient.out_eq _
    have h2 := (Submodule.Quotient.eq _).1 h1
    set w : A₁ := Quotient.out (Submodule.Quotient.mk (p := A₀.comap A₁.subtype) ⟨y, hy⟩) with hw
    have h3 : (w : Sp E n) - y ∈ A₀ := h2
    ext z
    show z - (w : Sp E n) ∈ A₀ ↔ z - y ∈ A₀
    constructor
    · intro hz
      simpa using A₀.add_mem hz h3
    · intro hz
      simpa using A₀.sub_mem hz h3
  refine ⟨(Set.finite_range φ).subset hsub, ((Set.ncard_le_ncard hsub (Set.finite_range φ)).trans ?_).trans hle⟩
  exact Finite.card_range_le φ

theorem finite_ncard_ybSet {X : Fields} {Pr : Primes X} (hPr : Pr.Ok)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} (mu : Tup X.F X.E X.K Sg) (hmu : mu = 1)
    (cst : LocCst X (rowSG Pr sel mu)) {n : ℕ} (L : Submodule (𝓞 X.E) (Sp X.E n)) :
    (ybSet sel mu cst L).Finite ∧ (ybSet sel mu cst L).ncard ≤ (Pr.g 0 * Pr.g 1) ^ (Module.finrank ℚ X.E * n) := by
  classical
  have hvG : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs := by
    intro P
    rcases Finset.mem_union.mp P.2 with h | h
    · exact h
    · have h0 : QE sel (mu : Chr X.F X.E X.K) = ∅ := by
        rw [hmu]
        exact twistPrimes_trivialTuple_empty sel Sg
      rw [h0] at h
      simp at h
  refine finite_ncard_cosets _ _ _ (Nat.mul_pos (hPr.g_prime 0).pos (hPr.g_prime 1).pos) ?_
  intro y hy
  unfold locLat at hy ⊢
  rw [Submodule.mem_iInf] at hy ⊢
  intro P
  have h1 := hy P
  rw [Submodule.mem_comap] at h1 ⊢
  simp only [hvG P, if_true, zpow_neg, zpow_one, inv_inv, zpow_zero, inv_one, one_smul, LinearMap.restrictScalars_apply,
    LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul] at h1 ⊢
  rcases Finset.mem_union.mp (hvG P) with h | h
  · have hq : Formalism.L2.Col.qOf P.1 = Pr.g 0 := hPr.vG_norm 0 _ h
    rw [hq] at h1
    rw [mul_nsmul]
    exact nsmul_mem h1 _
  · have hq : Formalism.L2.Col.qOf P.1 = Pr.g 1 := hPr.vG_norm 1 _ h
    rw [hq] at h1
    rw [mul_nsmul']
    exact nsmul_mem h1 _

end GlobalTheory.CouplingCosets
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingAdjointEqOfPullbackIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutatorPairing_adjoint_eq_of_pullback_iso : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → ∀ α β : A ⟶ A, IsMonHom α → IsMonHom β → LBIso (P.pull (lift (fst A A ≫ α) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ β)).left) → ∀ (n : ℤ) (T : Over S) (a b : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ), Out.WeilIs (G2 A) P n (lift (a ≫ α) 1) (lift 1 b) c → Out.WeilIs (G2 A) P n (lift a 1) (lift 1 (b ≫ β)) c' → c = c' := by
  first | (exact @GlobalTheory.AdjPairing.weilIs_adj_eq) | (exact GlobalTheory.AdjPairing.weilIs_adj_eq) | (intros; apply GlobalTheory.AdjPairing.weilIs_adj_eq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingSwapEqOfSwapInvariantStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutatorPairing_swap_eq_of_swap_invariant : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∀ (n : ℤ) (T : Over S) (u v : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ), Out.WeilIs (G2 A) P n (lift 1 u) (lift v 1) c → Out.WeilIs (G2 A) P n (lift u 1) (lift 1 v) c' → c = c' := by
  first | (exact @GlobalTheory.SwapPairing.weilIs_swap_eq) | (exact GlobalTheory.SwapPairing.weilIs_swap_eq) | (intros; apply GlobalTheory.SwapPairing.weilIs_swap_eq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjArchUnipotentMemNhdsOne
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology Filter
open scoped NumberField.AdeleRing

namespace GlobalTheory.InfConj

theorem continuous_mixedSpace_symm (E : Type) [Field E] [NumberField E] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace E).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace E).apply_symm_apply y)) ⟨v, hv⟩).symm

def liftMat (E : Type) [Field E] [NumberField E] (a : ℕ)
    (Y : GroundTheory.Automorphic.AutomorphicForm.ArchMatrix E a) : Matrix (Fin a) (Fin a) (Ad E) :=
  Matrix.of fun i j => (((InfiniteAdeleRing.ringEquiv_mixedSpace E).symm (Y i j), 0) : Ad E)

theorem continuous_liftMat (E : Type) [Field E] [NumberField E] (a : ℕ) : Continuous (liftMat E a) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine Continuous.prodMk ((continuous_mixedSpace_symm E).comp ?_) continuous_const
  exact (continuous_apply j).comp (continuous_apply i)

theorem liftMat_zero (E : Type) [Field E] [NumberField E] (a : ℕ) : liftMat E a 0 = 0 := by
  ext i j : 2
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm 0 = 0
    exact map_zero _
  · rfl

theorem liftMat_archMat (E : Type) [Field E] [NumberField E] (a : ℕ) (Z : Matrix (Fin a) (Fin a) (Ad E))
    (hZ : ∀ i j, (Z i j).2 = 0) : liftMat E a (GroundTheory.Automorphic.CuspidalSpectrum.archMat E a Z) = Z := by
  ext i j : 2
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm (InfiniteAdeleRing.ringEquiv_mixedSpace E (Z i j).1) = (Z i j).1
    exact RingEquiv.symm_apply_apply _ _
  · exact (hZ i j).symm

end GlobalTheory.InfConj

namespace GlobalTheory.InfConj

theorem conj_blockEntry_snd (E : Type) [Field E] [NumberField E] (a r : ℕ) (x : GA E a)
    (P : BlockIx a r → Ad E) (hP : ∀ p, (P p).2 = 0) (i j : Fin a) :
    ((((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
        GroundTheory.Automorphic.AutomorphicForm.blockEntry P * (x : Matrix (Fin a) (Fin a) (Ad E))) i j).2 = 0 := by
  let f : Matrix (Fin a) (Fin a) (Ad E) →+* Matrix (Fin a) (Fin a) (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) :=
    (RingHom.snd (InfiniteAdeleRing E) (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E)).mapMatrix
  have hB : f (GroundTheory.Automorphic.AutomorphicForm.blockEntry P) = 0 := by
    refine Matrix.ext fun k l => ?_
    change (GroundTheory.Automorphic.AutomorphicForm.blockEntry P k l).2 = 0
    unfold GroundTheory.Automorphic.AutomorphicForm.blockEntry
    rw [Matrix.of_apply]
    split_ifs with h
    · exact hP _
    · rfl
  change f (((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
        GroundTheory.Automorphic.AutomorphicForm.blockEntry P * (x : Matrix (Fin a) (Fin a) (Ad E))) i j = 0
  rw [map_mul, map_mul, hB, mul_zero, zero_mul]
  rfl

theorem conj_unip_mem_nhds : ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (U : Set (GA E a)), U ∈ 𝓝 (1 : GA E a) →
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x : GA E a) (P : BlockIx a r → Ad E), (∀ p, (P p).2 = 0) →
      ‖GroundTheory.Automorphic.CuspidalSpectrum.archMat E a (((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
        GroundTheory.Automorphic.AutomorphicForm.blockEntry P * (x : Matrix (Fin a) (Fin a) (Ad E)))‖ ≤ δ →
      x⁻¹ * unip P * x ∈ U := by
  intro E _ _ a r U hU
  rw [(Units.isInducing_embedProduct (M := Matrix (Fin a) (Fin a) (Ad E))).nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨t, ht, htU⟩ := hU
  let φ : Matrix (Fin a) (Fin a) (Ad E) → Matrix (Fin a) (Fin a) (Ad E) × (Matrix (Fin a) (Fin a) (Ad E))ᵐᵒᵖ :=
    fun Z => (1 + Z, MulOpposite.op (1 - Z))
  have hφ : Continuous φ :=
    (continuous_const.add continuous_id).prodMk (MulOpposite.continuous_op.comp (continuous_const.sub continuous_id))
  have hφ0 : φ (liftMat E a 0) = Units.embedProduct _ (1 : GA E a) := by
    rw [liftMat_zero]
    simp only [φ, add_zero, sub_zero, Units.embedProduct_apply, inv_one, Units.val_one]
  have hnb : (φ ∘ liftMat E a) ⁻¹' t ∈ 𝓝 (0 : GroundTheory.Automorphic.AutomorphicForm.ArchMatrix E a) :=
    (hφ.comp (continuous_liftMat E a)).continuousAt.preimage_mem_nhds (by
      rw [Function.comp_apply, hφ0]; exact ht)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hnb
  refine ⟨ε / 2, by positivity, fun x P hP hnorm => htU ?_⟩
  set Z := ((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
    GroundTheory.Automorphic.AutomorphicForm.blockEntry P * (x : Matrix (Fin a) (Fin a) (Ad E)) with hZdef
  have hmem : GroundTheory.Automorphic.CuspidalSpectrum.archMat E a Z ∈ Metric.ball 0 ε := by
    rw [mem_ball_zero_iff]; linarith
  have h1 := hball hmem
  rw [Set.mem_preimage, Function.comp_apply, liftMat_archMat E a Z (conj_blockEntry_snd E a r x P hP)] at h1
  rw [Set.mem_preimage]
  convert h1 using 1
  have hv : ((x⁻¹ * unip P * x : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) = 1 + Z := by
    rw [Units.val_mul, Units.val_mul]
    change ((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) * (1 + nilM P) * (x : Matrix (Fin a) (Fin a) (Ad E)) = _
    rw [mul_add, add_mul, mul_one, Units.inv_mul, hZdef]
    rfl
  have hi : ((x⁻¹ * unip P * x : GA E a)⁻¹ : GA E a).val = 1 - Z := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc, Units.val_mul, Units.val_mul]
    change ((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) * (1 - nilM P) * (x : Matrix (Fin a) (Fin a) (Ad E)) = _
    rw [mul_sub, sub_mul, mul_one, Units.inv_mul, hZdef]
    rfl
  simp only [Units.embedProduct_apply, φ]
  rw [hv, hi]

end GlobalTheory.InfConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalNormLeOfOscillationScaledUnipFD
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing

namespace GlobalTheory.CuspTail

theorem norm_le_of_osc_scaledUnipFD : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ), 0 < r → r < a →
    ∀ φ : GA E a → ℂ, (∀ γ g, φ (ratGL E a γ * g) = φ g) → IsCuspidal φ → Continuous φ →
    ∀ M : ℕ, 0 < M → ∀ (x : GA E a) (B : ℝ),
      (∀ X ∈ GroundTheory.Automorphic.scaledUnipFD E a r M, ‖φ (unip X * x) - φ x‖ ≤ B) → ‖φ x‖ ≤ B := by
  intro E _ _ _ a r hr hra φ _ hcusp hφ M hM x B hB
  set D := GroundTheory.Automorphic.scaledUnipFD E a r M with hDdef
  set ν := GroundTheory.Automorphic.AutomorphicForm.unipMeasure E a r
  have hD : IsAddFundamentalDomain (ratN E a r) D ν :=
    GroundTheory.Automorphic.isAddFundamentalDomain_scaledUnipFD hM
  have hD1 : ν D = 1 := GroundTheory.Automorphic.unipMeasure_scaledUnipFD hM
  have hunip : (unip : (BlockIx a r → Ad E) → GA E a) =
      (GroundTheory.Automorphic.AutomorphicForm.unipGL (n := a) (r := r) (R := Ad E)) :=
    funext fun X => Units.ext rfl
  have hcont : Continuous fun X : BlockIx a r → Ad E => φ (unip X * x) := by
    refine hφ.comp (Continuous.mul ?_ continuous_const)
    rw [hunip]
    exact GroundTheory.Automorphic.AutomorphicForm.continuous_unipGL
  obtain ⟨C, hC, hDC⟩ :=
    GroundTheory.Automorphic.CuspidalSpectrum.exists_isCompact_superset_scaledUnipFD (K := E) (n := a) r hM
  have hint : IntegrableOn (fun X => φ (unip X * x)) D ν :=
    (hcont.continuousOn.integrableOn_compact hC).mono_set hDC
  have hmean : ∫ X in D, φ (unip X * x) ∂ν = 0 :=
    hcusp r hr hra ν D inferInstance hD x
  have hfin : ν D < ⊤ := by rw [hD1]; exact ENNReal.one_lt_top
  have hkey : ∫ X in D, (φ (unip X * x) - φ x) ∂ν = -φ x := by
    rw [integral_sub hint (integrableOn_const hfin.ne)]
    simp only [hmean, setIntegral_const, measureReal_def, hD1, ENNReal.toReal_one, one_smul, zero_sub]
  calc ‖φ x‖ = ‖∫ X in D, (φ (unip X * x) - φ x) ∂ν‖ := by rw [hkey, norm_neg]
    _ ≤ B * ν.real D := norm_setIntegral_le_of_norm_le_const hfin hB
    _ = B := by simp [measureReal_def, hD1]

end GlobalTheory.CuspTail
end

