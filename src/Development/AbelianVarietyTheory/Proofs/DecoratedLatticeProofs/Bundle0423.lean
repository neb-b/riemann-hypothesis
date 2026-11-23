module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0378
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0381

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitDegreeOnePlaceEqExp
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDegOnePow

section Arith
variable {K : Type} [Field K] [NumberField K]

theorem pow_dvd_of_mem (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 K)) (I : Ideal (𝓞 K))
    (hvI : IsCoprime v.asIdeal I) (hpI : Ideal.span {(p : 𝓞 K)} = v.asIdeal * I) (n : ℕ) (r : ℤ)
    (hr : (r : 𝓞 K) ∈ v.asIdeal ^ n) : (p : ℤ) ^ n ∣ r := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨s, rfl⟩ := ih (Ideal.pow_le_pow_right (Nat.le_succ n) hr)
    have h1 : v.asIdeal ^ n * v.asIdeal ∣ v.asIdeal ^ n * (I ^ n * Ideal.span {(s : 𝓞 K)}) := by
      rw [← pow_succ, ← mul_assoc, ← mul_pow, ← hpI, Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton,
        Ideal.dvd_span_singleton]
      simpa using hr
    rw [mul_dvd_mul_iff_left (pow_ne_zero n v.ne_bot)] at h1
    have h2 : (s : 𝓞 K) ∈ v.asIdeal := Ideal.dvd_span_singleton.1 (hvI.pow_right.dvd_of_dvd_mul_left h1)
    have hpv : (p : 𝓞 K) ∈ v.asIdeal :=
      (Ideal.span_singleton_le_iff_mem _).1 (hpI ▸ Ideal.mul_le_left)
    have h3 : (p : ℤ) ∣ s := by
      by_contra hc
      obtain ⟨x, y, e⟩ := ((Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd).2 hc
      have e' : (x : 𝓞 K) * p + y * s = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 K) e
      exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (e' ▸ add_mem (Ideal.mul_mem_left _ _ hpv) (Ideal.mul_mem_left _ _ h2)))
    rw [pow_succ]
    exact mul_dvd_mul_left _ h3

theorem exists_int_sub_mem (N : ℕ) (hN : N ≠ 0) (J : Ideal (𝓞 K)) (hJ : Ideal.absNorm J = N)
    (hinj : ∀ r : ℤ, (r : 𝓞 K) ∈ J → (N : ℤ) ∣ r) (m : 𝓞 K) : ∃ r : ℤ, m - r ∈ J := by
  have hle : Ideal.span {(N : ℤ)} ≤ J.comap (Int.castRingHom (𝓞 K)) := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast, ← hJ]
    exact Ideal.absNorm_mem J
  have hi : Function.Injective (Ideal.quotientMap J (Int.castRingHom (𝓞 K)) hle) :=
    Ideal.quotientMap_injective' fun r hr => Ideal.mem_span_singleton.2 (hinj r hr)
  have hc : Nat.card (𝓞 K ⧸ J) = N := by rw [← hJ, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 K ⧸ J) := Nat.finite_of_card_ne_zero (hc ▸ hN)
  have hb := hi.bijective_of_nat_card_le (by
    rw [hc, Nat.card_congr (Int.quotientSpanNatEquivZMod N).toEquiv, Nat.card_zmod])
  obtain ⟨r, hr⟩ := hb.2 (Ideal.Quotient.mk J m)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  exact ⟨r, Ideal.Quotient.eq.1 hr.symm⟩

theorem trace_idem (N : ℕ) (J I : Ideal (𝓞 K)) (hN : Ideal.span {(N : 𝓞 K)} = J * I)
    (hinj : ∀ r : ℤ, (r : 𝓞 K) ∈ J → (N : ℤ) ∣ r) (hsurj : ∀ m : 𝓞 K, ∃ r : ℤ, m - r ∈ J)
    (t : 𝓞 K) (ht : t ∈ I) (ht1 : t - 1 ∈ J) : ∃ m : ℤ, Algebra.trace ℤ (𝓞 K) t = 1 + N * m := by
  classical
  let b := Module.Free.chooseBasis ℤ (𝓞 K)
  choose r hr using fun j => hsurj (b j)
  have hy : ∀ j, ∃ y : 𝓞 K, y * N = (b j - r j) * t := fun j =>
    Ideal.mem_span_singleton'.1 (hN ▸ Ideal.mul_mem_mul (hr j) ht)
  choose y hy using hy
  let π : 𝓞 K →ₗ[ℤ] ℤ := b.constr ℤ r
  let g : 𝓞 K →ₗ[ℤ] 𝓞 K := b.constr ℤ y
  have hπ : ∀ m : 𝓞 K, m - (π m : 𝓞 K) ∈ J := by
    have : (J.restrictScalars ℤ).mkQ ∘ₗ (LinearMap.id - (Algebra.linearMap ℤ (𝓞 K)) ∘ₗ π) = 0 :=
      b.ext fun j => (Submodule.Quotient.mk_eq_zero _).2 (by simpa [π] using hr j)
    intro m
    simpa using (Submodule.Quotient.mk_eq_zero _).1 (LinearMap.congr_fun this m)
  have hm : Algebra.lmul ℤ (𝓞 K) t = π.smulRight t + (N : ℤ) • g := b.ext fun j => by
    simp only [π, g, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.smul_apply, Module.Basis.constr_basis,
      Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
    rw [zsmul_eq_mul, zsmul_eq_mul, Int.cast_natCast]
    linear_combination (-1 : 𝓞 K) * hy j
  obtain ⟨c, hc⟩ := hinj (π t - 1) (by
    have := sub_mem ht1 (hπ t)
    push_cast
    convert this using 1
    ring)
  refine ⟨c + LinearMap.trace ℤ _ g, ?_⟩
  rw [Algebra.trace_apply, hm, map_add (f := _), map_smul, LinearMap.trace_smulRight, smul_eq_mul]
  linear_combination hc

theorem fin_part (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 K))
    (hnorm : Ideal.absNorm v.asIdeal = p) (hsq : (p : 𝓞 K) ∉ v.asIdeal ^ 2) (α : Af K)
    (hα1 : evalV K v α = 1) (hα0 : ∀ w, w ≠ v → evalV K w α = 0) (b : ℤ) (n : ℕ) :
    ∃ x : 𝓞 K, (∃ m : ℤ, Algebra.intTrace ℤ (𝓞 K) x = b + (p : ℤ) ^ n * m) ∧
      ∀ w : HeightOneSpectrum (𝓞 K), (α * algebraMap K (Af K) ((b : K) / (p : K) ^ n) -
        algebraMap K (Af K) ((x : K) / (p : K) ^ n)) w ∈ w.adicCompletionIntegers K := by
  obtain ⟨I, hvI, hpI⟩ := GlobalTheory.StdCharDegOne.exists_cofactor p v hnorm hsq
  obtain ⟨u, hu, t, ht, hut⟩ := Ideal.isCoprime_iff_exists.mp (hvI.pow (m := n) (n := n))
  have hN : Ideal.span {((p ^ n : ℕ) : 𝓞 K)} = v.asIdeal ^ n * I ^ n := by
    rw [← mul_pow, ← hpI, Ideal.span_singleton_pow, Nat.cast_pow]
  have hinj : ∀ r : ℤ, (r : 𝓞 K) ∈ v.asIdeal ^ n → ((p ^ n : ℕ) : ℤ) ∣ r := fun r hr => by
    rw [Nat.cast_pow]; exact pow_dvd_of_mem p hp v I hvI hpI n r hr
  obtain ⟨m, hm⟩ := trace_idem (p ^ n) _ _ hN hinj
    (exists_int_sub_mem _ (pow_ne_zero n hp.ne_zero) _ (by rw [map_pow, hnorm]) hinj) t ht (by
      rw [show t - 1 = -u by linear_combination hut]; exact neg_mem hu)
  have hp0 : (p : 𝓞 K) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hmemp : ∀ z ∈ v.asIdeal ^ n * I ^ n, ∃ y, z = (p : 𝓞 K) ^ n * y := fun z hz => by
    rw [← hN, Ideal.mem_span_singleton'] at hz
    obtain ⟨y, hy⟩ := hz
    exact ⟨y, by rw [← hy, mul_comm, Nat.cast_pow]⟩
  refine ⟨b * t, ⟨b * m, ?_⟩, fun w => ?_⟩
  · rw [← zsmul_eq_mul, map_smul, Algebra.intTrace_eq_trace, hm, smul_eq_mul]
    push_cast
    ring
  have hcomp : (α * algebraMap K (Af K) ((b : K) / (p : K) ^ n) - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K) ^ n)) w =
      α w * algebraMap K (Af K) ((b : K) / (p : K) ^ n) w - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K) ^ n) w := rfl
  rw [hcomp]
  by_cases hw : w = v
  · subst hw
    have h1 : α w = 1 := hα1
    have hsub : algebraMap K (Af K) ((b : K) / (p : K) ^ n) w - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K) ^ n) w =
        algebraMap K (Af K) ((((b : 𝓞 K) - (b : 𝓞 K) * t : 𝓞 K) : K) / (((p : 𝓞 K) ^ n : 𝓞 K) : K)) w := by
      rw [show ((((b : 𝓞 K) - (b : 𝓞 K) * t : 𝓞 K) : K) / (((p : 𝓞 K) ^ n : 𝓞 K) : K)) =
        (b : K) / (p : K) ^ n - ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K) ^ n) by rw [← sub_div]; simp, map_sub]
      rfl
    rw [h1, one_mul, hsub]
    obtain ⟨u', hu', s, hs, hus⟩ := Ideal.isCoprime_iff_exists.mp (hvI.pow_right (n := n))
    have hsv : s ∉ w.asIdeal := fun h =>
      w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (hus ▸ add_mem hu' h))
    have hmem : ((b : 𝓞 K) - (b : 𝓞 K) * t) * s ∈ w.asIdeal ^ n * I ^ n := by
      refine Ideal.mul_mem_mul ?_ hs
      rw [show (b : 𝓞 K) - (b : 𝓞 K) * t = b * u by linear_combination (-b : 𝓞 K) * hut]
      exact Ideal.mul_mem_left _ _ hu
    obtain ⟨y, hy⟩ := hmemp _ hmem
    exact GlobalTheory.StdCharDegOne.integral_of_mul w _ _ s y hp0 hsv hy
  · have h0 : α w = 0 := hα0 w hw
    rw [h0, zero_mul, zero_sub]
    refine neg_mem ?_
    obtain ⟨s, hsv, hsw⟩ : ∃ s ∈ v.asIdeal, s ∉ w.asIdeal := by
      by_contra hc
      push Not at hc
      exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hc).symm)
    obtain ⟨y, hy⟩ := hmemp _ (Ideal.mul_mem_mul (Ideal.pow_mem_pow hsv n) (Ideal.mul_mem_left _ (b : 𝓞 K) ht))
    have := GlobalTheory.StdCharDegOne.integral_of_mul w ((p : 𝓞 K) ^ n) ((b : 𝓞 K) * t) (s ^ n) y hp0
      (fun h => hsw (w.isPrime.mem_of_pow_mem n h)) (by rw [mul_comm]; exact hy)
    simpa using this

end Arith

theorem stdChar_placeIdem_div_pow (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (p : ℕ) (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hnorm : Ideal.absNorm v.asIdeal = p) (hsq : (p : 𝓞 D.host.F) ∉ v.asIdeal ^ 2)
    (ε) (hε : IsPlaceIdem D v ε) (b : ℤ) (n : ℕ) :
    ψ (ε * algebraMap D.host.F (AF D.host.F) ((b : D.host.F) / (p : D.host.F) ^ n)) =
      Complex.exp (2 * Real.pi * Complex.I * b / (p : ℂ) ^ n) := by
  obtain ⟨α, rfl, hα1, hα0⟩ := hε
  obtain ⟨x, ⟨m, hm⟩, hint⟩ := fin_part p hp v hnorm hsq α hα1 hα0 b n
  have hsplit : pairA D.host.F 0 α * algebraMap D.host.F (AF D.host.F) ((b : D.host.F) / (p : D.host.F) ^ n) =
      pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F) ^ n)) +
      pairA D.host.F 0 (α * algebraMap D.host.F (Af D.host.F) ((b : D.host.F) / (p : D.host.F) ^ n) -
        algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F) ^ n)) := by
    refine Prod.ext ?_ ?_
    · show (0 : Ainf D.host.F) * _ = 0 + 0
      rw [zero_mul, add_zero]
    · show α * algebraMap D.host.F (Af D.host.F) ((b : D.host.F) / (p : D.host.F) ^ n) =
        algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F) ^ n) +
        (α * algebraMap D.host.F (Af D.host.F) ((b : D.host.F) / (p : D.host.F) ^ n) -
          algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F) ^ n))
      rw [add_sub_cancel]
  have htr : ∀ r : 𝓞 D.host.F, Algebra.trace ℚ D.host.F (r : D.host.F) = ((Algebra.intTrace ℤ (𝓞 D.host.F) r : ℤ) : ℚ) :=
    fun r => (Algebra.algebraMap_intTrace (A := ℤ) (K := ℚ) (L := D.host.F) r).symm
  have h1 : ψ (pairA D.host.F 0 (α * algebraMap D.host.F (Af D.host.F) ((b : D.host.F) / (p : D.host.F) ^ n) -
        algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F) ^ n))) = 1 := by
    refine GlobalTheory.IntDense.mem_of_isClosed D.host.F (C := {y | ψ (pairA D.host.F 0 y) = 1})
      (isClosed_eq (hψ.1.1.comp (Continuous.prodMk continuous_const continuous_id)) continuous_const)
      (fun r => ?_) _ hint
    show ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (r : D.host.F))) = 1
    rw [GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ, htr, mul_comm]
    push_cast
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [hsplit, AddChar.map_add_eq_mul, h1, mul_one, GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ]
  have hq : Algebra.trace ℚ D.host.F ((x : D.host.F) / (p : D.host.F) ^ n) = ((b : ℚ) + p ^ n * m) / p ^ n := by
    have e : (x : D.host.F) / (p : D.host.F) ^ n = (((p : ℚ) ^ n)⁻¹) • (x : D.host.F) := by
      rw [Algebra.smul_def, map_inv₀, map_pow, map_natCast, div_eq_inv_mul]
    rw [e, map_smul, htr, hm, smul_eq_mul]
    push_cast
    ring
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [hq, show 2 * ↑Real.pi * Complex.I * ((((b : ℚ) + p ^ n * m) / p ^ n : ℚ) : ℂ) =
      2 * Real.pi * Complex.I * b / (p : ℂ) ^ n + m * (2 * Real.pi * Complex.I) by
    push_cast; field_simp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem weilChar_pr_eq_exp : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → (Formalism.L2.Col.qOf PP).Prime → ((Formalism.L2.Col.qOf PP : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2 → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt PP x) → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ ψk : AddChar k Circle, (ofSplit q).IsChar ψ ψk → ∀ (a : D.host.E) (b : ℤ) (n : ℕ), Formalism.L2.Col.IntAt PP (D.host.xi0 * a - (b : D.host.E) / (Formalism.L2.Col.qOf PP : D.host.E) ^ n) → (ψk ((ofSplit q).pr a) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * b / (Formalism.L2.Col.qOf PP : ℂ) ^ n) := by
  intro D k _ _ _ _ q PP hid hp hsq hint ψ hψ ψk hch a b n hx
  have hv := GlobalTheory.LocMod.PinInhab.v_eq_under q hid
  have hPP : Ideal.absNorm PP.asIdeal = Formalism.L2.Col.qOf PP := rfl
  generalize Formalism.L2.Col.qOf PP = p at hp hsq hx hPP ⊢
  have hpr : ∀ y : D.host.E, (ofSplit q).pr y = q.pr (incA D y) := fun _ => rfl
  have hms : ∀ (x : AE D) (y : k), x * q.sec y = q.sec (q.pr x * y) := fun x y => by
    have h := q.sec_pr (x * q.sec y)
    have h' := q.sec_pr (q.sec y)
    rw [map_mul, q.pr_sec] at h
    rw [q.pr_sec] at h'
    rw [h, mul_left_comm, ← h']
  have h0 : (ψk ((ofSplit q).pr a) : ℂ) = psiE ψ (q.sec (q.pr (incA D (D.host.xi0 * a)))) := by
    rw [map_mul, map_mul]
    exact (hch _).trans (congrArg _ (hms _ _))
  rw [h0]
  generalize D.host.xi0 * a = x at hx
  set c : D.host.F := (b : D.host.F) / (p : D.host.F) ^ n with hcdef
  have hc : algebraMap D.host.F D.host.E c = (b : D.host.E) / (p : D.host.E) ^ n := by
    rw [hcdef, map_div₀, map_pow, map_intCast, map_natCast]
  have hxs : x = (x - (b : D.host.E) / (p : D.host.E) ^ n) + algebraMap D.host.F D.host.E c := by
    rw [hc]; ring
  have hadd : ∀ u w : AE D, psiE ψ (u + w) = psiE ψ u * psiE ψ w := by
    intro u w; simp only [GlobalTheory.MixPer.psiE, map_add (f := _), AddChar.map_add_eq_mul]
  rw [hxs, map_add (f := _), map_add (f := _), map_add (f := _), hadd]
  have hy : q.pr (incA D (x - (b : D.host.E) / (p : D.host.E) ^ n)) ∈ 𝒪[k] := by
    rw [← hpr]; exact (hint _).2 hx
  have h1 : psiE ψ (q.sec (q.pr (incA D (x - (b : D.host.E) / (p : D.host.E) ^ n)))) = 1 := by
    rw [GlobalTheory.MixPer.psiE, GlobalTheory.SplitCharCond.trace_sec q, GlobalTheory.SplitCharCond.snd_trace,
      GlobalTheory.SplitCharCond.char_int hψ (GlobalTheory.SplitCharCond.trace_int ((q.int_iff _).1 hy))]
  rw [h1, one_mul]
  obtain ⟨ε, hε, he⟩ := q.above
  have htr : Algebra.trace (AF D.host.F) (AE D) q.e = ε := by
    refine Algebra.TensorProduct.includeLeft_injective (S := AF D.host.F) (algebraMap D.host.F D.host.E).injective ?_
    change algebraMap (AF D.host.F) (AE D) _ = algebraMap (AF D.host.F) (AE D) _
    rw [GlobalTheory.FockCompare.SymplVal.trace_AE, he]
  have hinc : incA D (algebraMap D.host.F D.host.E c) =
      algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) c) := GlobalTheory.SplitCharCond.one_tmul_eq c
  rw [q.sec_pr, hinc, mul_comm, ← Algebra.smul_def, GlobalTheory.MixPer.psiE, map_smul, smul_eq_mul, htr, mul_comm]
  have hnorm : Ideal.absNorm q.v.asIdeal = p := by rw [hv]; exact GlobalTheory.SplitDegOneChar.absNorm_under PP p hp hPP
  have hsqv : (p : 𝓞 D.host.F) ∉ q.v.asIdeal ^ 2 := by
    rw [hv]; exact GlobalTheory.SplitDegOneChar.natCast_not_mem_under_sq PP p hsq
  exact stdChar_placeIdem_div_pow D ψ hψ p hp q.v hnorm hsqv ε hε b n

end GlobalTheory.SplitDegOnePow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XiCpl1EqZeroOfFrames
section
open NumberField IsDedekindDomain Matrix ValuativeRel Formalism.L2.Col
open scoped Classical

noncomputable section

namespace GlobalTheory.CplDead

open Formalism.HermitianLatticesTheory GlobalTheory.ThetaMove

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem full_finset_inf {W ι : Type} [AddCommGroup W] [Module (𝓞 E) W] (S : Finset ι) (M : ι → Submodule (𝓞 E) W)
    (hM : ∀ i, Full (M i)) : Full (S.inf M) := by
  induction S using Finset.induction_on with
  | empty => intro x; exact ⟨1, one_pos, by simp⟩
  | insert i S hi ih => rw [Finset.inf_insert]; exact (hM i).inf ih

theorem exists_approx_family {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (M : HeightOneSpectrum (𝓞 E) → Submodule (𝓞 E) W) (hM : ∀ P, Full (M P)) (x : HeightOneSpectrum (𝓞 E) → W) :
    ∃ t : W, ∀ P ∈ S, t - x P ∈ localization₂ P.asIdeal (M P) := by
  have h := fun P => (full_finset_inf S M hM).approx {P} (x P)
  choose t h1 h2 using h
  refine ⟨∑ P ∈ S, t P, fun P hP => localization_mono P (Finset.inf_le hP) ?_⟩
  rw [← Finset.add_sum_erase S t hP, add_sub_right_comm]
  refine Submodule.add_mem _ (h1 P P (Finset.mem_singleton_self P)) (Submodule.sum_mem _ fun Q hQ => h2 Q P ?_)
  rw [Finset.mem_singleton]
  exact (Finset.ne_of_mem_erase hQ).symm

theorem full_of_span {n : ℕ} (N : Submodule (𝓞 E) (Sp E n)) (hN : Submodule.span E (N : Set (Sp E n)) = ⊤) : Full N := by
  first
  | exact @_root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top
  | exact _root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top
  | (apply _root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top <;> assumption)
  | (intros; apply _root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top ..)

theorem full_stdLat (n : ℕ) : Full (stdLat E n) := by
  refine full_of_span _ (top_le_iff.1 fun x _ => ?_)
  rw [pi_eq_sum_univ x]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span fun j _ => ?_)
  by_cases h : i = j
  · simp only [if_pos h]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
  · simp only [if_neg h]; exact Submodule.zero_mem _

theorem intAt_of_mem_stdAt {n : ℕ} {P : HeightOneSpectrum (𝓞 E)} {x : Sp E n} (hx : x ∈ stdAt E n P) (i : Fin n) :
    IntAt P (x i) := by
  obtain ⟨s, hs, hx⟩ := hx
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hx i (Set.mem_univ i))
  exact ⟨r, s, hs, by rw [hr]; rfl⟩

variable {a b : ℕ}

def homInto (S₀ : Set (Sp E a)) (g : Sp E b →ₗ[E] Sp E b) (N : Submodule (𝓞 E) (Sp E b)) : Submodule (𝓞 E) (HomE E a b) where
  carrier := {z | ∀ y ∈ S₀, g (z y) ∈ N}
  zero_mem' := fun y _ => by simp
  add_mem' := fun {z z'} hz hz' y hy => by
    rw [LinearMap.add_apply, map_add (f := _)]; exact N.add_mem (hz y hy) (hz' y hy)
  smul_mem' := fun c z hz y hy => by
    rw [LinearMap.smul_apply, LinearMap.map_smul_of_tower]; exact N.smul_mem _ (hz y hy)

theorem full_homInto (S₀ : Finset (Sp E a)) (g : Sp E b →ₗ[E] Sp E b) {N : Submodule (𝓞 E) (Sp E b)} (hN : Full N) :
    Full (homInto (S₀ : Set (Sp E a)) g N) := by
  intro z
  choose n hn hz using fun y => hN (g (z y))
  refine ⟨∏ y ∈ S₀, n y, Finset.prod_pos fun y _ => hn y, fun y hy => ?_⟩
  rw [LinearMap.smul_apply, LinearMap.map_smul_of_tower, ← Finset.prod_erase_mul S₀ n hy, Nat.cast_mul, mul_smul]
  exact N.smul_mem _ (hz y)

theorem apply_mem_of_mem_locP {S₀ : Set (Sp E a)} {g : Sp E b →ₗ[E] Sp E b} {N : Submodule (𝓞 E) (Sp E b)}
    {P : HeightOneSpectrum (𝓞 E)} {z : HomE E a b} (hz : z ∈ localization₂ P.asIdeal (homInto S₀ g N)) {y : Sp E a}
    (hy : y ∈ localization₂ P.asIdeal (Submodule.span (𝓞 E) S₀)) : g (z y) ∈ localization₂ P.asIdeal N := by
  obtain ⟨s, hs, hz⟩ := hz
  obtain ⟨t, ht, hy⟩ := hy
  have h : ∀ w ∈ Submodule.span (𝓞 E) S₀, g ((s • z) w) ∈ N := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => exact hz w hw
    | zero => simp
    | add u v _ _ hu hv => rw [map_add (f := _), map_add (f := _)]; exact N.add_mem hu hv
    | smul c u _ hu => rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower]; exact N.smul_mem _ hu
  refine ⟨s * t, P.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
  have := h _ hy
  rwa [LinearMap.smul_apply, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower,
    smul_smul] at this

variable [StarRing E]

theorem phiT_add (K : Type) [Field K] {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG)
    {d' : Deco E b ST SG'} (hd' : d'.Ok) (x z : HomE E a b)
    (hz : ∀ P : ST, ∀ y ∈ d.at P.1, ((qOf P.1 : E))⁻¹ • z y ∈ d'.at P.1) : phiT K d d' (x + z) = phiT K d d' x := by
  have key : ∀ x z : HomE E a b, (∀ P : ST, ∀ y ∈ d.at P.1, ((qOf P.1 : E))⁻¹ • z y ∈ d'.at P.1) →
      (∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y) →
      ∀ P : ST, ∀ y ∈ d.at P.1, (x + z) y ∈ d'.at P.1 ∧ d'.f P ((x + z) y) = d.f P y := by
    intro x z hz hx P y hy
    have hq : (qOf P.1 : E) ≠ 0 := by
      have : qOf P.1 ≠ 0 := by rw [qOf, Ne, Ideal.absNorm_eq_zero_iff]; exact P.1.ne_bot
      exact_mod_cast this
    have e : z y = (qOf P.1 : 𝓞 E) • ((qOf P.1 : E))⁻¹ • z y := by
      rw [← algebraMap_smul E (qOf P.1 : 𝓞 E), map_natCast, smul_smul, mul_inv_cancel₀ hq, one_smul]
    have h1 : z y ∈ d'.at P.1 := by rw [e]; exact Submodule.smul_mem _ _ (hz P y hy)
    have h2 : d'.f P (z y) = 0 := by
      rw [e, hd'.f_smul P _ _ (hz P y hy), Ideal.Quotient.eq_zero_iff_mem.2
        (show (qOf P.1 : 𝓞 E) ∈ P.1.asIdeal from Ideal.absNorm_mem _), zero_mul]
    rw [LinearMap.add_apply]
    exact ⟨Submodule.add_mem _ (hx P y hy).1 h1, by rw [hd'.f_add P _ (hx P y hy).1 _ h1, h2, add_zero, (hx P y hy).2]⟩
  unfold phiT
  refine if_congr ⟨fun h => ?_, key x z hz⟩ rfl rfl
  have := key (x + z) (-z) (fun P y hy => by
    rw [LinearMap.neg_apply, smul_neg]; exact Submodule.neg_mem _ (hz P y hy)) h
  rwa [add_neg_cancel_right] at this

theorem exists_transport (K : Type) [Field K] {ST SG SG' SB : Finset (HeightOneSpectrum (𝓞 E))} (hdis : Disjoint ST SB)
    {d : Deco E a ST SG} (hd : d.Ok) {d' : Deco E b ST SG'} (hd' : d'.Ok) (f₀ : Frs E a SB) (f f' : Frs E b SB)
    (c : SB → E) (x : HomE E a b) :
    ∃ x' : HomE E a b, phiT K d d' x' = phiT K d d' x ∧
      ∀ (P : SB) s l, IntAt P.1 (c P * (inFr (f₀ P) (f P) x' - inFr (f₀ P) (f' P) x) (Pi.single s 1) l) := by
  obtain ⟨S₀, hS₀⟩ := hd.lat.fg
  obtain ⟨S₁, hS₁⟩ := hd'.lat.fg
  have hone : Full (1 : Submodule (𝓞 E) E) := by
    intro x
    obtain ⟨n, hn, hnx⟩ := full_stdLat (E := E) 1 (fun _ => x)
    refine ⟨n, hn, ?_⟩
    simpa [stdLat, Submodule.mem_pi] using hnx (0 : Fin 1) (Set.mem_univ _)
  have hfull : Full d'.N := by
    let M : Sp E b → Submodule (𝓞 E) (Sp E b) := fun y =>
      (1 : Submodule (𝓞 E) E).comap ((hStd E b y).restrictScalars (𝓞 E))
    have hM : ∀ y, Full (M y) := by
      intro y x
      obtain ⟨n, hn, hx⟩ := hone (hStd E b y x)
      refine ⟨n, hn, ?_⟩
      simpa [M] using hx
    have hle : S₁.inf M ≤ d'.N := by
      intro x hx
      rw [← hd'.uni]
      simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
        LinearMap.restrictScalars_apply]
      intro y hy
      rw [← hS₁] at hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact (show S₁.inf M ≤ M y from Finset.inf_le hy) hx
      | zero => simp
      | add y z hy hz ihy ihz => simpa using Submodule.add_mem (1 : Submodule (𝓞 E) E) ihy ihz
      | smul r y hy ih =>
        let r' : 𝓞 E := ⟨star (r : E), r.isIntegral_coe.map (starRingEnd E).toIntAlgHom⟩
        rw [← algebraMap_smul E r y, LinearMap.map_smulₛₗ, LinearMap.smul_apply]
        have hr := (1 : Submodule (𝓞 E) E).smul_mem r' ih
        change star (r : E) * hStd E b y x ∈ (1 : Submodule (𝓞 E) E) at hr
        simpa [starRingEnd_apply, smul_eq_mul] using hr
    intro x
    obtain ⟨n, hn, hx⟩ := full_finset_inf S₁ M hM x
    exact ⟨n, hn, hle hx⟩
  obtain ⟨t, ht⟩ := exists_approx_family (W := HomE E a b) (ST ∪ SB)
    (fun P => if h : P ∈ SB then
        homInto ((Finset.univ.image fun s : Fin a => f₀ ⟨P, h⟩ (Pi.single s 1) : Finset (Sp E a)) : Set (Sp E a))
          (c ⟨P, h⟩ • (f ⟨P, h⟩).symm.toLinearMap) (stdLat E b)
      else homInto (S₀ : Set (Sp E a)) (((qOf P : E))⁻¹ • LinearMap.id) d'.N)
    (fun P => by
      by_cases h : P ∈ SB
      · simp only [dif_pos h]; exact full_homInto _ _ (full_stdLat b)
      · simp only [dif_neg h]; exact full_homInto _ _ hfull)
    (fun P => if h : P ∈ SB then (f ⟨P, h⟩).toLinearMap ∘ₗ (f' ⟨P, h⟩).symm.toLinearMap ∘ₗ x else x)
  refine ⟨t, ?_, fun P s l => ?_⟩
  · rw [← add_sub_cancel x t]
    refine phiT_add K d hd' x _ fun P y hy => ?_
    have h : P.1 ∉ SB := Finset.disjoint_left.1 hdis P.2
    have h1 := ht P.1 (Finset.mem_union_left _ P.2)
    simp only [dif_neg h] at h1
    exact apply_mem_of_mem_locP h1 (by rw [hS₀]; exact hy)
  · have h1 := ht P.1 (Finset.mem_union_right _ P.2)
    simp only [dif_pos P.2] at h1
    have h2 := apply_mem_of_mem_locP h1 (y := f₀ P (Pi.single s 1))
      (mem_localization_of_mem _ (Submodule.subset_span (by simp)))
    have h3 := intAt_of_mem_stdAt h2 l
    convert h3 using 1
    simp [inFr]

end Gen

theorem xiCpl1_eq_zero_of_frames : ∀ {X : Fields} {Pr : Primes X} {R : Formalism.BasicNotions.Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Formalism.L2.DIV.Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Formalism.L2.DIV.Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), L.Ok Ch sel mu cst G m2 → ∀ (u : Pr.Word), Disjoint (Pr.vT u) (rowSG Pr sel mu) → ∀ (al : L.β m2) (p₀ : ChPt (R := R) sel mu u m2) (p p' : ChPt (R := R) sel mu u (m2 + 1)) (Y Y' : Set (Sp X.E (R.N (m2 + 1)))), p'.deco = p.deco → (∀ P : rowSG Pr sel mu, ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ • ((frsF sel mu p' P).symm (repY Y') - (frsF sel mu p P).symm (repY Y)) ∈ stdAt X.E (R.N (m2 + 1)) P.1) → (∀ x, XiCpl1 Ch sel mu cst L m2 al p₀ p Y x = 0) → ∀ x, XiCpl1 Ch sel mu cst L m2 al p₀ p' Y' x = 0 := by
  intro X Pr R Ch sel S mu cst L G m2 hL u hdis al p₀ p p' Y Y' hdeco hY h0 x
  obtain ⟨x', h1, h2⟩ := exists_transport X.K hdis p₀.deco.2 p.deco.2 (frsF sel mu p₀) (frsF sel mu p) (frsF sel mu p')
    (fun P => ((qOf P.1 : X.E) ^ cst.B)⁻¹) x
  rw [← h0 x']
  unfold XiCpl1
  rw [hdeco, h1]
  congr 1
  refine Finset.prod_congr rfl fun P _ => ?_
  have e1 := hL.psiInvX al P (inFr (frsF sel mu p₀ P) (frsF sel mu p' P) x) _ ((frsF sel mu p P).symm (repY Y)) (h2 P)
  have e2 := hL.psiInv al P (inFr (frsF sel mu p₀ P) (frsF sel mu p' P) x) ((frsF sel mu p P).symm (repY Y))
    ((frsF sel mu p' P).symm (repY Y') - (frsF sel mu p P).symm (repY Y)) (fun i => intAt_of_mem_stdAt (hY P) i)
  rw [add_sub_cancel] at e1 e2
  rw [e1, e2]

end GlobalTheory.CplDead
end
end

