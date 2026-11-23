module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0058
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0083

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormSpanInvol
section
open NumberField IsDedekindDomain Formalism.L2.Col

namespace GlobalTheory.SplitUnram

variable {E : Type} [Field E] [NumberField E]

theorem absNorm_span_invol (s : 𝓞 E →+* 𝓞 E) (hs : ∀ x, s (s x) = x) (a : 𝓞 E) :
    Ideal.absNorm (Ideal.span {s a}) = Ideal.absNorm (Ideal.span {a}) := by
  let e : 𝓞 E ≃+* 𝓞 E := RingEquiv.ofRingHom s s (RingHom.ext hs) (RingHom.ext hs)
  let e' : 𝓞 E ≃ₐ[ℤ] 𝓞 E := AlgEquiv.ofRingEquiv (f := e) (fun n => by simp)
  rw [Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton]
  exact congrArg Int.natAbs (Algebra.norm_eq_of_algEquiv e' a)

theorem natCast_notMem_sq : ∀ (E : Type) [Field E] [NumberField E] (s : 𝓞 E →+* 𝓞 E) (a : 𝓞 E) (p : ℕ),
    (∀ x, s (s x) = x) → p.Prime → a * s a = (p : 𝓞 E) → IsCoprime a (s a) →
    2 * (divs a).card = Module.finrank ℚ E → (∀ P ∈ divs a, Ideal.absNorm P.asIdeal = p) →
    ∀ P ∈ divs a, ((p : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 := by
  intro E _ _ s a p hs hp ha hcop hcard hN P hP hmem
  classical
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  have ha0 : a ≠ 0 := left_ne_zero_of_mul (ha ▸ hp0)
  have hnorm : Ideal.absNorm (Ideal.span {a}) = p ^ (divs a).card := by
    have h1 : Ideal.absNorm (Ideal.span {a}) ^ 2 = (p ^ (divs a).card) ^ 2 := by
      rw [← pow_mul, mul_comm, hcard, ← RingOfIntegers.rank, ← Ideal.absNorm_span_natCast, ← ha,
        ← Ideal.span_singleton_mul_span_singleton, map_mul, absNorm_span_invol s hs, sq]
    exact Nat.pow_left_injective two_ne_zero h1
  have haP : a ∈ P.asIdeal := (mem_divs ha0 P).1 hP
  have ha2 : a ∈ P.asIdeal ^ 2 := by
    obtain ⟨u, v, huv⟩ := hcop
    have h1 : a = u * a ^ 2 + v * (p : 𝓞 E) := by
      rw [← ha]
      linear_combination (-a) * huv
    rw [h1]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow haP 2)) (Ideal.mul_mem_left _ _ hmem)
  have hd1 : P.asIdeal ^ 2 ∣ Ideal.span {a} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact ha2
  have hd2 : ∏ Q ∈ (divs a).erase P, Q.asIdeal ∣ Ideal.span {a} := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro P _ Q _ hPQ
      exact (HeightOneSpectrum.isCoprime_of_ne P Q hPQ)
    · intro Q hQ
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact (mem_divs ha0 Q).1 (Finset.mem_of_mem_erase hQ)
  have hc : IsCoprime (P.asIdeal ^ 2) (∏ Q ∈ (divs a).erase P, Q.asIdeal) := by
    refine IsCoprime.pow_left (IsCoprime.prod_right fun Q hQ => ?_)
    exact HeightOneSpectrum.isCoprime_of_ne P Q (Finset.ne_of_mem_erase hQ).symm
  have hd := map_dvd Ideal.absNorm (hc.mul_dvd hd1 hd2)
  rw [hnorm, map_mul, map_pow, map_prod, hN P hP,
    Finset.prod_congr rfl (fun Q hQ => hN Q (Finset.mem_of_mem_erase hQ)), Finset.prod_const, ← pow_add,
    Nat.pow_dvd_pow_iff_le_right hp.one_lt] at hd
  have h3 := Finset.card_erase_add_one hP
  omega

end GlobalTheory.SplitUnram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormSplitPlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.Proof.AbsNormSplitPlace

open GlobalTheory.Proof.NarrowJetMoments

theorem absNorm_of_split {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v) (hl : (Ideal.absNorm v.asIdeal).Prime)
    {P : HeightOneSpectrum (𝓞 E)} (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) :
    Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal := by
  obtain ⟨Q, Q', -, hm⟩ := hs
  have hN : Ideal.absNorm Q.asIdeal * Ideal.absNorm Q'.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
    rw [← map_mul, ← hm, Ideal.absNorm_algebraMap]
    congr 1
    rw [← h2]
    exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E).symm
  have h1 : ∀ R : HeightOneSpectrum (𝓞 E), Ideal.absNorm R.asIdeal ≠ 1 := fun R h =>
    R.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have hb := (hl.mul_eq_prime_sq_iff (h1 Q) (h1 Q')).1 hN
  have hle : Q.asIdeal * Q'.asIdeal ≤ P.asIdeal := by
    rw [← hm, ← hP, Ideal.under_def]
    exact Ideal.map_comap_le
  rcases P.isPrime.mul_le.1 hle with h | h
  · rw [← Q.isMaximal.eq_of_le P.isPrime.ne_top h, hb.1]
  · rw [← Q'.isMaximal.eq_of_le P.isPrime.ne_top h, hb.2]

theorem plc_eq_absNorm {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    (hl : (Ideal.absNorm v.asIdeal).Prime) : ringChar (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
  have h6 : ringChar (𝓞 F ⧸ v.asIdeal) ∣ Ideal.absNorm v.asIdeal := by
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.absNorm_mem _
  haveI := v.isPrime
  exact ((Nat.dvd_prime hl).1 h6).resolve_left CharP.ringChar_ne_one

theorem main : ∀ (Z : Dat) (u : Z.Pr.Word) (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ) (mu : Tup Z.X.F Z.X.E Z.X.K S), Z.Ok → IsSel Z.X sel → Z.Pr.T u ∈ S → (∀ i, Z.Pr.g i ∈ S) → (∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u) ∧ ∀ P ∈ rowSG Z.Pr sel mu, (Formalism.L2.Col.qOf P).Prime ∧ Formalism.L2.Col.qOf P ≠ Z.Pr.T u ∧ ((Z.Pr.T u : ℕ) : 𝓞 Z.X.E) ∉ P.asIdeal ∧ ((∃ i, Formalism.L2.Col.qOf P = Z.Pr.g i) ∨ Formalism.L2.Col.qOf P ∉ S) := by
  intro Z u sel S mu hZ hsel hT hg
  have hPr := hZ.primes
  have hTn : ∀ P ∈ rowSG Z.Pr sel mu, ((Z.Pr.T u : ℕ) : 𝓞 Z.X.E) ∉ P.asIdeal := fun P hP =>
    notMem_rowSG hPr hsel (hPr.T_prime u) hT (hPr.T_ne_g u) hP
  refine ⟨fun P hP hP' => ?_, fun P hP => ?_⟩
  · rcases (mem_Sall sel mu u P).1 hP with h | h <;> rcases (mem_Sall sel mu u _).1 hP' with h' | h'
    · refine conj_piT_notMem hPr u ⟨conjPrime₂ P, h'⟩ ?_
      change cO Z.X.E (Z.Pr.piT u) ∈ (conjPrime₂ P).asIdeal
      rw [mem_conjP, cO_cO]
      exact decoFin_mem_of_mem_divs h
    · exact hTn _ h' (natCast_mem_conjP.2 (T_mem hPr u ⟨P, h⟩))
    · exact hTn _ h (natCast_mem_conjP.1 (T_mem hPr u ⟨conjPrime₂ P, h'⟩))
    · exact conjP_notMem_rowSG hZ.fields hPr hsel hg h h'
  · have key : (Formalism.L2.Col.qOf P).Prime ∧ ((∃ i, Formalism.L2.Col.qOf P = Z.Pr.g i) ∨ Formalism.L2.Col.qOf P ∉ S) := by
      classical
      rcases Finset.mem_union.1 hP with h | h
      · obtain ⟨i, hi⟩ := mem_vGs_iff.1 h
        have e : Formalism.L2.Col.qOf P = Z.Pr.g i := hPr.vG_norm i P hi
        exact ⟨e ▸ hPr.g_prime i, Or.inl ⟨i, e⟩⟩
      · obtain ⟨v, hv, e⟩ := good_of_mem_QE h
        have e1 : Formalism.L2.Col.qOf P = Ideal.absNorm v.asIdeal :=
          absNorm_of_split hZ.fields.rankE hv.1 hv.2.1.1 (e ▸ hsel v)
        refine ⟨e1 ▸ hv.2.1.1, Or.inr ?_⟩
        rw [e1, ← plc_eq_absNorm hv.2.1.1]
        exact hv.2.2
    refine ⟨key.1, fun e => hTn P hP ?_, hTn P hP, key.2⟩
    rw [← e]
    exact Ideal.absNorm_mem _

end GlobalTheory.Proof.AbsNormSplitPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AddSubgroupRepsExistenceCardSum
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.RepsMod

variable {H : Type} [AddCommGroup H]

theorem sum_eq_of_family {M ι : Type} [AddCommMonoid M] {Λ B : AddSubgroup H} {R : Finset H}
    (hR : IsReps Λ B R) (s : Finset ι) (f : ι → H) (hf : ∀ i ∈ s, f i ∈ B)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, f i - f j ∈ Λ → i = j) (hsurj : ∀ y ∈ B, ∃ i ∈ s, y - f i ∈ Λ)
    (F : H → M) (hF : ∀ y ∈ B, ∀ l ∈ Λ, l ∈ B → F (y + l) = F y) :
    ∑ y ∈ R, F y = ∑ i ∈ s, F (f i) := by
  obtain ⟨h1, h2, h3⟩ := hR
  symm
  choose r hr hrl using fun i (hi : i ∈ s) => h3 (f i) (hf i hi)
  refine Finset.sum_bij r hr ?_ ?_ ?_
  · intro i hi j hj hij
    apply hinj i hi j hj
    have := Λ.sub_mem (hrl i hi) (hrl j hj)
    rw [hij] at this
    simpa using this
  · intro y hy
    obtain ⟨i, hi, hl⟩ := hsurj y (h1 y hy)
    refine ⟨i, hi, ?_⟩
    symm
    apply h2 y hy _ (hr i hi)
    have := Λ.add_mem hl (hrl i hi)
    simpa using this
  · intro i hi
    have := hF (r i hi) (h1 _ (hr i hi)) _ (hrl i hi) (B.sub_mem (hf i hi) (h1 _ (hr i hi)))
    simpa using this

theorem out_sub_mem_iff (Λ B : AddSubgroup H) (x y : B) :
    ((x : H) - y ∈ Λ) ↔ (QuotientAddGroup.mk x : B ⧸ Λ.addSubgroupOf B) = QuotientAddGroup.mk y := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]
  simp

theorem out_inj (Λ B : AddSubgroup H) (c d : B ⧸ Λ.addSubgroupOf B)
    (h : ((c.out : B) : H) - (d.out : B) ∈ Λ) : c = d := by
  rw [out_sub_mem_iff] at h
  simpa using h

theorem out_surj (Λ B : AddSubgroup H) (y : H) (hy : y ∈ B) :
    ∃ c : B ⧸ Λ.addSubgroupOf B, y - ((c.out : B) : H) ∈ Λ := by
  refine ⟨QuotientAddGroup.mk ⟨y, hy⟩, ?_⟩
  have := (out_sub_mem_iff Λ B ⟨y, hy⟩ (Quotient.out (QuotientAddGroup.mk ⟨y, hy⟩ : B ⧸ Λ.addSubgroupOf B))).2 (by simp)
  exact this

theorem exists_reps (Λ B : AddSubgroup H) (h : Λ.relIndex B ≠ 0) : ∃ R : Finset H, IsReps Λ B R := by
  classical
  have : Finite (B ⧸ Λ.addSubgroupOf B) := Nat.finite_of_card_ne_zero h
  have := Fintype.ofFinite (B ⧸ Λ.addSubgroupOf B)
  refine ⟨Finset.univ.image (fun c : B ⧸ Λ.addSubgroupOf B => ((c.out : B) : H)), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
    exact (c.out).2
  · intro x hx y hy hxy
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 hy
    rw [out_inj Λ B c d hxy]
  · intro y hy
    obtain ⟨c, hc⟩ := out_surj Λ B y hy
    exact ⟨_, Finset.mem_image.2 ⟨c, Finset.mem_univ _, rfl⟩, hc⟩

theorem card_reps (Λ B : AddSubgroup H) (R : Finset H) (hR : IsReps Λ B R) :
    R.card = Λ.relIndex B := by
  classical
  have : Finite (B ⧸ Λ.addSubgroupOf B) := by
    refine Finite.of_surjective (fun x : R => (QuotientAddGroup.mk ⟨x.1, hR.1 _ x.2⟩ : B ⧸ Λ.addSubgroupOf B)) ?_
    intro c
    obtain ⟨x, hx, hl⟩ := hR.2.2 _ (c.out).2
    refine ⟨⟨x, hx⟩, ?_⟩
    have := (out_sub_mem_iff Λ B c.out ⟨x, hR.1 _ hx⟩).1 hl
    simpa using this.symm
  have := Fintype.ofFinite (B ⧸ Λ.addSubgroupOf B)
  have h := sum_eq_of_family hR Finset.univ (fun c : B ⧸ Λ.addSubgroupOf B => ((c.out : B) : H))
    (fun c _ => (c.out).2) (fun c _ d _ h => out_inj Λ B c d h)
    (fun y hy => by
      obtain ⟨c, hc⟩ := out_surj Λ B y hy
      exact ⟨c, Finset.mem_univ _, hc⟩) (fun _ => (1 : ℕ)) (fun _ _ _ _ _ => rfl)
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ] at h
  rw [h, ← Nat.card_eq_fintype_card]
  rfl

theorem sum_prod_reps (M : Type) [AddCommMonoid M] (Λ B B₁ B₂ : AddSubgroup H) (R R₁ R₂ : Finset H)
    (F : H → M) (h1 : B₁ ≤ B) (h2 : B₂ ≤ B) (hs : ∀ y ∈ B, ∃ y₁ ∈ B₁, ∃ y₂ ∈ B₂, y - (y₁ + y₂) ∈ Λ)
    (hi : ∀ y₁ ∈ B₁, ∀ y₂ ∈ B₂, y₁ + y₂ ∈ Λ → y₁ ∈ Λ) (hR : IsReps Λ B R) (hR₁ : IsReps Λ B₁ R₁)
    (hR₂ : IsReps Λ B₂ R₂) (hF : ∀ y ∈ B, ∀ l ∈ Λ, l ∈ B → F (y + l) = F y) :
    ∑ y ∈ R, F y = ∑ y₂ ∈ R₂, ∑ y₁ ∈ R₁, F (y₁ + y₂) := by
  rw [← Finset.sum_product']
  refine sum_eq_of_family hR (R₂ ×ˢ R₁) (fun p => p.2 + p.1) ?_ ?_ ?_ F hF
  · intro p hp
    rw [Finset.mem_product] at hp
    exact B.add_mem (h1 (hR₁.1 _ hp.2)) (h2 (hR₂.1 _ hp.1))
  · intro p hp q hq hpq
    rw [Finset.mem_product] at hp hq
    have e : p.2 + p.1 - (q.2 + q.1) = (p.2 - q.2) + (p.1 - q.1) := by abel
    simp only [e] at hpq
    have a1 := hi _ (B₁.sub_mem (hR₁.1 _ hp.2) (hR₁.1 _ hq.2)) _
      (B₂.sub_mem (hR₂.1 _ hp.1) (hR₂.1 _ hq.1)) hpq
    have a2 : p.1 - q.1 ∈ Λ := by
      have := Λ.sub_mem hpq a1
      simpa using this
    exact Prod.ext (hR₂.2.1 _ hp.1 _ hq.1 a2) (hR₁.2.1 _ hp.2 _ hq.2 a1)
  · intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, hl⟩ := hs y hy
    obtain ⟨r₁, hr₁, hl₁⟩ := hR₁.2.2 _ hy₁
    obtain ⟨r₂, hr₂, hl₂⟩ := hR₂.2.2 _ hy₂
    refine ⟨(r₂, r₁), Finset.mem_product.2 ⟨hr₂, hr₁⟩, ?_⟩
    have e : y - (r₁ + r₂) = (y - (y₁ + y₂)) + (y₁ - r₁) + (y₂ - r₂) := by abel
    simp only [e]
    exact Λ.add_mem (Λ.add_mem hl hl₁) hl₂

theorem sum_char_reps (K : Type) [Field K] (Λ B : AddSubgroup H) (R : Finset H) (φ : H → K)
    (hR : IsReps Λ B R) (hm : ∀ x ∈ B, ∀ y ∈ B, φ (x + y) = φ x * φ y)
    (h1 : ∀ x ∈ B, x ∈ Λ → φ x = 1) :
    ((∀ y ∈ B, φ y = 1) → ∑ y ∈ R, φ y = (R.card : K)) ∧
      ((¬ ∀ y ∈ B, φ y = 1) → ∑ y ∈ R, φ y = 0) := by
  constructor
  · intro h
    rw [Finset.sum_congr rfl (fun y hy => h y (hR.1 y hy))]
    simp
  · intro h
    push Not at h
    obtain ⟨y₀, hy₀, hne⟩ := h
    have key := sum_eq_of_family hR R (fun y => y₀ + y) (fun y hy => B.add_mem hy₀ (hR.1 y hy))
      (fun x hx y hy hxy => hR.2.1 x hx y hy (by simpa using hxy))
      (fun y hy => by
        obtain ⟨x, hx, hl⟩ := hR.2.2 _ (B.sub_mem hy hy₀)
        exact ⟨x, hx, by rwa [← sub_sub]⟩) φ
      (fun y hy l hl hlB => by rw [hm y hy l hlB, h1 l hlB hl, mul_one])
    rw [Finset.sum_congr rfl (fun y hy => hm y₀ hy₀ y (hR.1 y hy)), ← Finset.mul_sum] at key
    have : (φ y₀ - 1) * ∑ y ∈ R, φ y = 0 := by rw [_root_.sub_mul, one_mul, ← key, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)

theorem not_dvd_relIndex (Λ B : AddSubgroup H) (g p : ℕ) (hp : p.Prime) (hc : Nat.Coprime g p)
    (h : Λ.relIndex B ≠ 0) (hg : ∀ x ∈ B, g • x ∈ Λ) : ¬ p ∣ Λ.relIndex B := by
  intro hd
  have : Finite (B ⧸ Λ.addSubgroupOf B) := Nat.finite_of_card_ne_zero h
  have := Fact.mk hp
  obtain ⟨c, hcc⟩ := exists_prime_addOrderOf_dvd_card' (G := B ⧸ Λ.addSubgroupOf B) p hd
  have h0 : g • c = 0 := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective c
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    simpa using hg x x.2
  have hdg : p ∣ g := hcc ▸ addOrderOf_dvd_of_nsmul_eq_zero h0
  exact (hp.coprime_iff_not_dvd.1 hc.symm) hdg

theorem reps_facts : ∀ (H : Type) [AddCommGroup H], (∀ Λ B : AddSubgroup H, Λ.relIndex B ≠ 0 → ∃ R : Finset H, IsReps Λ B R) ∧ (∀ (Λ B : AddSubgroup H) (R : Finset H), IsReps Λ B R → R.card = Λ.relIndex B) ∧ (∀ (M : Type) [AddCommMonoid M] (Λ B B₁ B₂ : AddSubgroup H) (R R₁ R₂ : Finset H) (F : H → M), B₁ ≤ B → B₂ ≤ B → (∀ y ∈ B, ∃ y₁ ∈ B₁, ∃ y₂ ∈ B₂, y - (y₁ + y₂) ∈ Λ) → (∀ y₁ ∈ B₁, ∀ y₂ ∈ B₂, y₁ + y₂ ∈ Λ → y₁ ∈ Λ) → IsReps Λ B R → IsReps Λ B₁ R₁ → IsReps Λ B₂ R₂ → (∀ y ∈ B, ∀ l ∈ Λ, l ∈ B → F (y + l) = F y) → ∑ y ∈ R, F y = ∑ y₂ ∈ R₂, ∑ y₁ ∈ R₁, F (y₁ + y₂)) ∧ (∀ (K : Type) [Field K] (Λ B : AddSubgroup H) (R : Finset H) (φ : H → K), IsReps Λ B R → (∀ x ∈ B, ∀ y ∈ B, φ (x + y) = φ x * φ y) → (∀ x ∈ B, x ∈ Λ → φ x = 1) → ((∀ y ∈ B, φ y = 1) → ∑ y ∈ R, φ y = (R.card : K)) ∧ ((¬ ∀ y ∈ B, φ y = 1) → ∑ y ∈ R, φ y = 0)) ∧ ∀ (Λ B : AddSubgroup H) (g p : ℕ), p.Prime → Nat.Coprime g p → Λ.relIndex B ≠ 0 → (∀ x ∈ B, g • x ∈ Λ) → ¬ p ∣ Λ.relIndex B :=
  fun _ _ => ⟨exists_reps, card_reps, sum_prod_reps, sum_char_reps, not_dvd_relIndex⟩

end GlobalTheory.RepsMod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicLatticeCompletionLocalGlobalStatement
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLatticeCompletion_local_global : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin k → E)), Module.Finite (𝓞 E) Λ → (∀ u : Fin k → E ⊗[F] FiniteAdeleRing (𝓞 F) F, u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ ↔ ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (u i)) ∈ locLat v Λ) ∧ (Submodule.span E (Λ : Set (Fin k → E)) = ⊤ → ∀ x : Fin k → E, (∀ v : HeightOneSpectrum (𝓞 F), (fun i => inclE (F := F) (v.adicCompletion F) (x i)) ∈ locLat v Λ) → x ∈ Λ) ∧ ∀ a : E, (∀ v : HeightOneSpectrum (𝓞 F), inclE (F := F) (v.adicCompletion F) a ∈ intV E v) → a ∈ (algebraMap (𝓞 E) E).range := by
  first | exact @GlobalTheory.LatLocGlob.latS_local_global | exact GlobalTheory.LatLocGlob.latS_local_global | (intros; apply GlobalTheory.LatLocGlob.latS_local_global <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicNumbersPadicPlacesFacts
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomPlace

theorem norm_le_one_of_isIntegral_int {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[p])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem exists_extension (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (σ : K →+* ℂ) (ι : K →+* ℂ_[p]) :
    ∃ lam : TaylorLogMetric.Qbar →+* ℂ_[p], ∀ k, σ k ∈ TaylorLogMetric.Qbar ∧ TaylorLogMetric.lamC lam (σ k) = ι k := by
  have hmem : ∀ k, σ k ∈ TaylorLogMetric.Qbar := fun k =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) k).algHom σ.toRatAlgHom)
  let σ' : K →+* TaylorLogMetric.Qbar := σ.codRestrict TaylorLogMetric.Qbar hmem
  let : Algebra K TaylorLogMetric.Qbar := σ'.toAlgebra
  let : Algebra K ℂ_[p] := ι.toAlgebra
  have : IsScalarTower ℚ K TaylorLogMetric.Qbar := IsScalarTower.of_algebraMap_eq fun q => by
    rw [eq_ratCast, eq_ratCast, map_ratCast]
  have : Algebra.IsAlgebraic ℚ TaylorLogMetric.Qbar := by
    convert algebraicClosure.isAlgebraic ℚ ℂ <;> first | rfl | exact Subsingleton.elim _ _
  have : Algebra.IsAlgebraic K TaylorLogMetric.Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  let f : TaylorLogMetric.Qbar →ₐ[K] ℂ_[p] := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨f.toRingHom, fun k => ⟨hmem k, ?_⟩⟩
  unfold TaylorLogMetric.lamC
  rw [dite_eq_left (hmem k)]
  exact f.commutes k

theorem norm_le_one_of_valuation (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (ι : K →+* ℂ_[p]) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖ι (y : K)‖ < 1) (x : K) (hx : w.valuation K x ≤ 1) :
    ‖ι x‖ ≤ 1 := by
  obtain ⟨n, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
  have hint : ∀ y : 𝓞 K, ‖ι (y : K)‖ ≤ 1 := fun y =>
    norm_le_one_of_isIntegral_int (by
      convert map_isIntegral_int ι (RingOfIntegers.isIntegral_coe y)
      exact Subsingleton.elim _ _)
  have hd : 1 ≤ ‖ι ((d : 𝓞 K) : K)‖ := not_lt.1 fun hlt => d.2 ((hw _).2 hlt)
  have h2 : ‖ι x‖ * ‖ι ((d : 𝓞 K) : K)‖ = ‖ι (n : K)‖ := by
    rw [← norm_mul, ← map_mul]; exact congrArg (fun z => ‖ι z‖) h
  have h3 := hint n
  nlinarith [norm_nonneg (ι x)]

theorem exp_rat_pow_den (r : ℚ) :
    Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ((r : ℝ) : ℂ)) ^ r.den = 1 := by
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  refine ⟨-r.num, ?_⟩
  have h : ((r.den : ℂ)) * (r : ℂ) = (r.num : ℂ) := by
    exact_mod_cast Rat.den_mul_eq_num r
  push_cast
  rw [← h]; ring

theorem root_of_unity_norm {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {z : ℂ} {n : ℕ}
    (hn : n ≠ 0) (hz : z ^ n = 1) : z ∈ TaylorLogMetric.Qbar ∧ ‖TaylorLogMetric.lamC lam z‖ = 1 := by
  have hmem : z ∈ TaylorLogMetric.Qbar := by
    refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (Nat.pos_of_ne_zero hn) ?_)
    rw [hz]; exact isAlgebraic_one
  refine ⟨hmem, ?_⟩
  unfold TaylorLogMetric.lamC
  rw [dite_eq_left hmem]
  have h1 : (⟨z, hmem⟩ : TaylorLogMetric.Qbar) ^ n = 1 := Subtype.ext (by simpa using hz)
  have h2 : ‖lam ⟨z, hmem⟩‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h2

theorem places : ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (σ : K →+* ℂ) (ι : K →+* ℂ_[p]), (∃ lam : TaylorLogMetric.Qbar →+* ℂ_[p], ∀ k, σ k ∈ TaylorLogMetric.Qbar ∧ TaylorLogMetric.lamC lam (σ k) = ι k) ∧ (∀ w : HeightOneSpectrum (𝓞 K), (∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖ι (y : K)‖ < 1) → ∀ x : K, w.valuation K x ≤ 1 → ‖ι x‖ ≤ 1) ∧ ∀ (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (r : ℚ), Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ((r : ℝ) : ℂ)) ∈ TaylorLogMetric.Qbar ∧ ‖TaylorLogMetric.lamC lam (Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ((r : ℝ) : ℂ)))‖ = 1 :=
  fun K _ _ p _ σ ι => ⟨exists_extension K p σ ι, norm_le_one_of_valuation K p ι,
    fun lam r => root_of_unity_norm lam r.den_ne_zero (exp_rat_pow_den r)⟩

end GlobalTheory.MomPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ApplyMemLocP
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable
  GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.AdjMem

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

omit [NumberField E] in
theorem hStd_adj (x : HomE E a b) (v : Sp E a) (y : Sp E b) : hStd E a v (adj x y) = hStd E b (x v) y := by
  have : x v = LinearMap.toMatrix' x *ᵥ v := (LinearMap.toMatrix'_mulVec x v).symm
  rw [this]
  change star v ⬝ᵥ ((LinearMap.toMatrix' x)ᴴ *ᵥ y) = star (LinearMap.toMatrix' x *ᵥ v) ⬝ᵥ y
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec]

theorem apply_mem_locP {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {Q : HeightOneSpectrum (𝓞 E)} (hA : localization₂ Q.asIdeal AA = localization₂ Q.asIdeal (1 : Submodule (𝓞 E) E))
    {x : HomE E a b} (hx : x ∈ perO AA N N') {v : Sp E a} (hv : v ∈ localization₂ Q.asIdeal N) : x v ∈ localization₂ Q.asIdeal N' := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, x', hx', rfl⟩ := hz
    obtain ⟨s, hs, hsv⟩ := (mem_locP _ _ _).1 hv
    obtain ⟨t, ht, htr⟩ := (mem_locP _ _ _).1 (hA ▸ le_locP Q AA hr)
    obtain ⟨c, hc⟩ := Submodule.mem_one.1 htr
    refine (mem_locP _ _ _).2 ⟨t * s, fun hm => (Q.isPrime.mem_or_mem hm).elim ht hs, ?_⟩
    have h1 := N'.smul_mem c (hx' _ hsv)
    have e : (t * s) • (r • x') v = c • x' (s • v) := by
      rw [← algebraMap_smul E c, hc, ← algebraMap_smul E s v, map_smul, LinearMap.smul_apply, ← algebraMap_smul E (t * s),
        smul_smul, smul_smul, map_mul, Algebra.smul_def t r]
      congr 1
      ring
    rw [e]
    exact h1
  | zero => exact zero_mem _
  | add x x' _ _ h h' => exact add_mem h h'
  | smul c x _ h => exact Submodule.smul_mem _ c h

theorem adj_mem_locP {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {P : HeightOneSpectrum (𝓞 E)} (hN : IsSdLat N) (hN' : IsSdLat N')
    (hA : localization₂ (conjPrime₂ P).asIdeal AA = localization₂ (conjPrime₂ P).asIdeal (1 : Submodule (𝓞 E) E))
    {x : HomE E a b} (hx : x ∈ perO AA N N') {y : Sp E b} (hy : y ∈ localization₂ P.asIdeal N') : adj x y ∈ localization₂ P.asIdeal N := by
  obtain ⟨Q, rfl⟩ : ∃ Q, P = conjPrime₂ Q := ⟨conjPrime₂ P, (GlobalTheory.CharValCompare.conjP_conjP P).symm⟩
  rw [GlobalTheory.CharValCompare.conjP_conjP] at hA
  rw [GlobalTheory.Survey.StandardDeterminantUnits.mem_at_conj hN'.1.fg hN'.2] at hy
  rw [GlobalTheory.Survey.StandardDeterminantUnits.mem_at_conj hN.1.fg hN.2]
  intro v hv
  rw [hStd_adj]
  exact hy _ (apply_mem_locP hA hx hv)

theorem adj_per_mem : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a))
    (N'' : Submodule (𝓞 X.E) (Sp X.E b)) (P : HeightOneSpectrum (𝓞 X.E)), IsSdLat N → IsSdLat N'' →
    localization₂ (conjPrime₂ P).asIdeal A.AA = localization₂ (conjPrime₂ P).asIdeal (1 : Submodule (𝓞 X.E) X.E) →
    ∀ x ∈ per A N N'', ∀ y ∈ localization₂ P.asIdeal N'', adj x y ∈ localization₂ P.asIdeal N :=
  fun _ _ _ _ _ _ _ hN hN' hA _ hx _ hy => adj_mem_locP hN hN' hA hx hy

end GlobalTheory.AdjMem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLatticeVectorApproxAllFinitePlacesStatement
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_vector_approx_all_finitePlaces : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin k → E)), Module.Finite (𝓞 E) Λ → ∀ (T : ℕ), T ≠ 0 → ∀ (y : ∀ v : HeightOneSpectrum (𝓞 F), Fin k → E ⊗[F] v.adicCompletion F), (∀ v, y v ∈ locLat v Λ) → ∃ x ∈ Λ, ∀ v : HeightOneSpectrum (𝓞 F), ∃ z ∈ locLat v Λ, y v = (fun i => inclE (F := F) (v.adicCompletion F) (x i)) + T • z := by
  first | exact @GlobalTheory.OverCompare.exists_lattice_approx_all | exact GlobalTheory.OverCompare.exists_lattice_approx_all | (intros; apply GlobalTheory.OverCompare.exists_lattice_approx_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceSizeLstar
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_sizeLstar : SzRow (fun _ _ L => SizeLstar L) := szRow_lStar

end GlobalTheory.EX
end

