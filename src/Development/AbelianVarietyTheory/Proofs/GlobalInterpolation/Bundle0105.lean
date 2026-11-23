module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0087
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Principal
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0002
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0001
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0097

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocPAAAndPrimesNe
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.AAUnitAway

theorem natCast_notMem {A : Type} [CommRing A] {I : Ideal A} (hI : I ≠ ⊤) {l n : ℕ} (hl : (l : A) ∈ I)
    (h : Nat.Coprime n l) : (n : A) ∉ I := by
  intro hn
  obtain ⟨x, y, e⟩ : IsCoprime (n : A) (l : A) := Nat.Coprime.cast h
  exact hI ((Ideal.eq_top_iff_one _).2 (e ▸ I.add_mem (I.mul_mem_left _ hn) (I.mul_mem_left _ hl)))

theorem exists_den (D : D7) (Q : Ideal (𝓞 D.host.E)) [hQ : Q.IsPrime] {l : ℕ} (hl : l.Prime) (h2 : l ∉ D.host.small) (hq : l ≠ D.host.q)
    (hlQ : (l : 𝓞 D.host.E) ∈ Q) :
    ∃ z : 𝓞 D.host.E, z ∉ Q ∧ ∀ t ∈ D.host.AA0, ∃ w : 𝓞 D.host.E, (w : D.host.E) = t * (z : D.host.E) := by
  have hnot : ¬ D.host.𝔟 ≤ Q := by
    intro hle
    have hd : Q ∣ differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) := by
      rw [D.host.𝔟_spec.1]
      exact (Ideal.dvd_iff_le.2 hle).mul_right _
    exact natCast_notMem hQ.ne_top hlQ (Nat.Coprime.mul_left
      ((Nat.Prime.coprime_iff_not_dvd hl).2 (UpperTheory.Small.not_dvd_QS D.host hl h2)).symm
      ((Nat.coprime_primes D.host.hyp.1 hl).2 hq.symm)) (D.host.der.diffSupport Q hQ hd)
  obtain ⟨z, hz, hzP⟩ := Set.not_subset.1 hnot
  have hB : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (Formalism.L2.Pj.b_ne_bot D)
  refine ⟨z, hzP, fun t ha => ?_⟩
  unfold Host.AA0 at ha
  rw [FractionalIdeal.mem_inv_iff hB] at ha
  obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1 (ha _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨z, hz, rfl⟩))
  exact ⟨w, hw⟩

theorem localization_le_of_le_localization₂ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {I J : Submodule (𝓞 E) E}
    (h : I ≤ localization₂ P.asIdeal J) : localization₂ P.asIdeal I ≤ localization₂ P.asIdeal J := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := (mem_locP P I x).1 hx
  obtain ⟨t, ht, hx⟩ := (mem_locP P J _).1 (h hx)
  refine (mem_locP P J x).2 ⟨t * s, fun hm => ?_, by rwa [mul_smul]⟩
  rcases P.isPrime.mem_or_mem hm with h | h
  exacts [ht h, hs h]

theorem locP_AA (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (cD : D.what₂.Tau → ℂ) (P : HeightOneSpectrum (𝓞 X.E)) (l : ℕ) (hl : l.Prime) (h2 : l ∉ D.host.small) (hq : l ≠ D.host.q)
    (hP : (l : 𝓞 X.E) ∈ P.asIdeal) (hc : Nat.Coprime (Ideal.absNorm cc) l) :
    localization₂ P.asIdeal (ambOf s B χ cD).AA = localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E) := by
  let j : 𝓞 D.host.E →+* 𝓞 X.E := RingOfIntegers.mapRingHom (s.iE.symm : D.host.E →+* X.E)
  have hj : ∀ a : 𝓞 D.host.E, ((j a : 𝓞 X.E) : X.E) = s.iE.symm (a : D.host.E) := fun _ => rfl
  haveI := P.isPrime
  refine le_antisymm (localization_le_of_le_localization₂ P ?_) (localization_le_of_le_localization₂ P ?_)
  · obtain ⟨z, hz, hden⟩ := exists_den D (P.asIdeal.comap j) hl h2 hq (by rw [Ideal.mem_comap, map_natCast]; exact hP)
    refine Submodule.span_le.2 ?_
    rintro r ⟨c, -, t, ht, rfl⟩
    obtain ⟨w, hw⟩ := hden t ht
    refine (mem_locP P _ _).2 ⟨j z, hz, Submodule.mem_one.2 ⟨j (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w), ?_⟩⟩
    rw [Algebra.smul_def]
    change ((j _ : 𝓞 X.E) : X.E) = ((j z : 𝓞 X.E) : X.E) * _
    rw [hj, hj, ← map_mul]
    congr 1
    have e : ((algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w : 𝓞 D.host.E) : D.host.E) =
      ((c : D.host.K) : D.host.E) * (w : D.host.E) := rfl
    rw [e, hw]
    ring
  · intro x hx
    obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hx
    refine (mem_locP P _ _).2 ⟨(Ideal.absNorm cc : ℕ), natCast_notMem P.isPrime.ne_top hP hc, ?_⟩
    have h1 : ((Ideal.absNorm cc : ℕ) : X.E) ∈ (ambOf s B χ cD).AA := by
      refine Submodule.subset_span ⟨_, Ideal.absNorm_mem cc, 1, Formalism.L2.Pj.one_mem_inverse_halfDifferent D, ?_⟩
      simp
    convert Submodule.smul_mem _ y h1 using 1
    simp [Algebra.smul_def, mul_comm]

theorem sq_ne_neg {X : Fields} (hX : X.Ok) (π : 𝓞 X.E) (p : ℕ) (hp : p.Prime) (hn : π * X.conjO π = (p : 𝓞 X.E))
    (hcop : IsCoprime π (X.conjO π)) (hcard : (divs π).card = X.f) (hN : ∀ P ∈ divs π, Ideal.absNorm P.asIdeal = p)
    (a : X.E) : a ^ 2 ≠ -(p : X.E) := by
  intro ha
  have hrk : Module.finrank ℚ X.E = 2 * X.f := by
    rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, Fields.f, hX.card_Tau, mul_comm]
  have hcc : ∀ x, X.conjO (X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : X.E))
  obtain ⟨P, hP⟩ := Finset.card_pos.1 (hcard ▸ hX.f_pos)
  have hint : IsIntegral ℤ a := by
    refine IsIntegral.of_pow two_pos ?_
    rw [ha]
    exact (isIntegral_algebraMap (R := ℤ) (x := (p : ℤ)) |>.neg) |> fun h => by simpa using h
  obtain ⟨b, hba⟩ : ∃ b : 𝓞 X.E, algebraMap (𝓞 X.E) X.E b = a := ⟨⟨a, hint⟩, rfl⟩
  have hb : b ^ 2 = -(p : 𝓞 X.E) := by
    apply RingOfIntegers.coe_injective
    rw [map_pow, hba, ha, map_neg, map_natCast]
  have hpP : (p : 𝓞 X.E) ∈ P.asIdeal := hN P hP ▸ Ideal.absNorm_mem _
  have haP : b ∈ P.asIdeal :=
    P.isPrime.mem_of_pow_mem 2 (hb ▸ P.asIdeal.neg_mem hpP)
  refine GlobalTheory.SplitUnram.natCast_notMem_sq X.E X.conjO π p hcc hp hn hcop (by rw [hrk, hcard]) hN P hP ?_
  have := Ideal.pow_mem_pow haP 2
  rwa [hb, neg_mem_iff] at this

theorem notMem_small {X : Fields} (hX : X.Ok) (D : D7) (s : Seam D X) (π : 𝓞 X.E) (p : ℕ) (hp : p.Prime)
    (hn : π * X.conjO π = (p : 𝓞 X.E)) (hcop : IsCoprime π (X.conjO π)) (hcard : (divs π).card = X.f)
    (hN : ∀ P ∈ divs π, Ideal.absNorm P.asIdeal = p) : p ∉ D.host.small := by
  intro hs
  have hrk : Module.finrank ℚ X.E = 2 * X.f := by
    rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, Fields.f, hX.card_Tau, mul_comm]
  have hcc : ∀ x, X.conjO (X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : X.E))
  obtain ⟨P, hP⟩ := Finset.card_pos.1 (hcard ▸ hX.f_pos)
  have hpP : (p : 𝓞 X.E) ∈ P.asIdeal := hN P hP ▸ Ideal.absNorm_mem _
  exact (UpperTheory.Ram.not_dvd_QS_of_notMem_sq D.host.toHostAx D.host.QS_exact X.E s.iE P p hp hpP
    (GlobalTheory.SplitUnram.natCast_notMem_sq X.E X.conjO π p hcc hp hn hcop (by rw [hrk, hcard]) hN P hP)).1
    (Nat.dvd_of_mem_primeFactors hs)

theorem primes_ne (Z : Dat) (D : D7) (s : Seam D Z.X) (hZ : Z.Ok) :
    (∀ u, Z.Pr.T u ∉ D.host.small ∧ Z.Pr.T u ≠ D.host.q) ∧ ∀ i, Z.Pr.g i ∉ D.host.small ∧ Z.Pr.g i ≠ D.host.q := by
  have ha : (s.iE.symm (D.host.sqq)) ^ 2 = -(D.host.q : Z.X.E) := by
    rw [← map_pow, D.host.sqq_sq, map_neg, map_natCast]
  have hcc : ∀ x, Z.X.conjO (Z.X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : Z.X.E))
  have hPr := hZ.primes
  refine ⟨fun u => ⟨fun h => ?_, fun h => ?_⟩, fun i => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact notMem_small hZ.fields D s _ _ (hPr.T_prime u) (hPr.piT_norm u) (hPr.piT_cop u) (hPr.vT_card u) (hPr.vT_norm u) h
  · exact sq_ne_neg hZ.fields _ _ (hPr.T_prime u) (hPr.piT_norm u) (hPr.piT_cop u) (hPr.vT_card u) (hPr.vT_norm u) _ (h ▸ ha)
  · exact notMem_small hZ.fields D s (Z.X.conjO (Z.Pr.piG i)) _ (hPr.g_prime i) (by rw [hcc, mul_comm, hPr.piG_norm i])
      (by rw [hcc]; exact (hPr.piG_cop i).symm) (hPr.vG_card i) (hPr.vG_norm i) h
  · exact sq_ne_neg hZ.fields (Z.X.conjO (Z.Pr.piG i)) _ (hPr.g_prime i) (by rw [hcc, mul_comm, hPr.piG_norm i])
      (by rw [hcc]; exact (hPr.piG_cop i).symm) (hPr.vG_card i) (hPr.vG_norm i) _ (h ▸ ha)

theorem locP_AA_and_primes_ne : (∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (P : HeightOneSpectrum (𝓞 X.E)) (l : ℕ), l.Prime → l ∉ D.host.small → l ≠ D.host.q → (l : 𝓞 X.E) ∈ P.asIdeal → Nat.Coprime (Ideal.absNorm cc) l → localization₂ P.asIdeal (ambOf s B χ cD).AA = localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E)) ∧ ∀ (Z : Dat) (D : D7) (s : Seam D Z.X), Z.Ok → (∀ u, Z.Pr.T u ∉ D.host.small ∧ Z.Pr.T u ≠ D.host.q) ∧ ∀ i, Z.Pr.g i ∉ D.host.small ∧ Z.Pr.g i ≠ D.host.q :=
  ⟨locP_AA, primes_ne⟩

end GlobalTheory.AAUnitAway
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MovedVacuumMemThetaFunctionsAndMoves
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.Moved

theorem sd_stdL (D : D7) (N : ℕ) : StandardLatticesGL3.SD D (StandardLatticesGL3.stdL D N) := by
  letI := D.host.cmStar
  have hr : ∀ x : D.host.E, x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ↔ IsIntegral ℤ x := fun x =>
    ⟨by rintro ⟨a, rfl⟩; exact a.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  have hm : ∀ x : Fin N → D.host.E, x ∈ StandardLatticesGL3.stdL D N ↔ ∀ k, IsIntegral ℤ (x k) := fun x => by
    simp only [StandardLatticesGL3.stdL, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]
    exact forall_congr' fun k => hr (x k)
  have hs : ∀ k : Fin N, (Pi.single k 1 : Fin N → D.host.E) ∈ StandardLatticesGL3.stdL D N := fun k => by
    rw [hm]
    intro j
    rw [Pi.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  refine ⟨Submodule.fg_pi fun _ => ?_, ?_, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  · rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin N)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨k, rfl⟩
    simpa using hs k
  · rw [hr]
    rw [hm] at hx hy
    exact IsIntegral.sum _ fun i _ => ((hx i).map (starRingEnd D.host.E).toIntAlgHom).mul (hy i)
  · rw [hm]
    intro k
    have := h _ (hs k)
    rw [hr] at this
    simpa [Formalism.BasicNotions.stdH, Pi.single_apply, apply_ite] using this

theorem isHerm_formV (A : ℝ) (n : Type) [Fintype n] (N N' : ℕ) : IsHerm (formV A n N N') := by
  intro x y
  set_option synthInstance.maxHeartbeats 100000 in
    simp [formV, map_sum, mul_comm]

theorem inter_mem_Th {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] {H : Sesq V} {α : V → ℂ}
    (hH : IsHerm H) {A₁ A₂ : AddSubgroup V} (hf : relIdx A₁ A₂ ≠ 0)
    (hs₁ : IsSemiChar H A₁ α) (hd₂ : IsSelfDual H A₂) (hs₂ : IsSemiChar H A₂ α)
    {F : V → ℂ} (hF : F ∈ Th H α A₁) : inter H α A₁ A₂ F ∈ Th H α A₂ := by
  have : Finite (A₂ ⧸ A₁.addSubgroupOf A₂) := Nat.finite_of_card_ne_zero hf
  refine ⟨?_, GlobalTheory.ThetaInter.inter_mem_fixedBy hH hs₁ hd₂ hs₂ hF.2⟩
  have := Fintype.ofFinite (A₂ ⧸ A₁.addSubgroupOf A₂)
  have hU : ∀ x z, AnalyticAt ℂ (opU H x F) z := fun x z => by
    have h : AnalyticAt ℂ (fun z => H z x) z := (LinearMap.toContinuousLinearMap (H.flip x)).analyticAt z
    have h2 : AnalyticAt ℂ (fun z => F (z + x)) z :=
      AnalyticAt.comp (f := fun z => z + x) (hF.1 _ (Set.mem_univ _)) (analyticAt_id.add analyticAt_const)
    exact h2.mul ((analyticAt_const.mul h).sub analyticAt_const).cexp
  rw [GlobalTheory.ThetaInter.inter_eq]
  intro z _
  exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun c _ => analyticAt_const.mul (hU _ z))

theorem iop_eq (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a b : ℕ} (A₁ A₂ : AddSubgroup (TaylorLogMetric.VC D a b)) (G : TaylorLogMetric.VC D a b → ℂ) :
    TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc δ) A₁ A₂ G =
      inter (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) A₁ A₂ G := rfl

theorem iop_mul (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (A B : AddSubgroup (TaylorLogMetric.VC D N N')) (c : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ)
    (z : TaylorLogMetric.VC D N N') : TaylorLogMetric.Iop D T A B (fun w => c * G w) z = c * TaylorLogMetric.Iop D T A B G z := by
  unfold TaylorLogMetric.Iop
  rw [mul_left_comm, mul_finsum _ c]
  congr 1
  refine finsum_congr fun q => ?_
  simp only [TaylorLogMetric.U]; ring

variable {D : D7} {χ : TaylorLogMetric.IdE D → ℂ} {n : ℕ} {L L' L'' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}

theorem chi_detId_mul (hχ : TaylorLogMetric.IsChi D χ) (h : StandardLatticesGL3.SD D L) (h' : StandardLatticesGL3.SD D L') (h'' : StandardLatticesGL3.SD D L'') :
    χ (TaylorLogMetric.detId D L L'') = χ (TaylorLogMetric.detId D L L') * χ (TaylorLogMetric.detId D L' L'') := by
  rw [(GlobalTheory.RelDetIdeal.detId_normOne_mul D n L L' L'' h h' h'').2]
  exact hχ.1 _ _ (GlobalTheory.RelDetIdeal.detId_normOne_mul D n L L' L'' h h' h'').1 (GlobalTheory.RelDetIdeal.detId_normOne_mul D n L' L'' L'' h' h'' h'').1

theorem chi_detId_ne_zero (hχ : TaylorLogMetric.IsChi D χ) (h : StandardLatticesGL3.SD D L) (h' : StandardLatticesGL3.SD D L') : χ (TaylorLogMetric.detId D L L') ≠ 0 := by
  obtain ⟨⟨𝔟, -, hb⟩, h2⟩ := GlobalTheory.RelDetIdeal.detId_normOne_mul D n L L L h h h
  have h1 : TaylorLogMetric.detId D L L = 1 := by
    rw [← mul_one (TaylorLogMetric.detId D L L), ← hb, ← mul_assoc, ← h2]
  have h3 := chi_detId_mul hχ h h' h
  have h4 : χ 1 = 1 := by simpa [Submodule.one_eq_span] using hχ.2 1
  rw [h1, h4] at h3
  exact left_ne_zero_of_mul_eq_one h3.symm

theorem thMoved_mem_and_moves : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (a b : ℕ), TaylorLogMetric.IsChi D χ → B.EqP χ → B.LatAll → B.ThZeroMem a b → Even a → Even b → (∀ L L', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → Base.chiFac χ a b L L' ≠ 0 ∧ B.thMoved a b L L' ∈ Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D B.tor) (TaylorLogMetric.La D B.tor L L')) ∧ (∀ L L' L'', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → StandardLatticesGL3.SD D L'' → B.thMoved a b L L'' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L L'') (B.thMoved a b L L')) ∧ ∀ L L₁ L', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L₁ → StandardLatticesGL3.SD D L' → B.thMoved a b L₁ L' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L') (B.thMoved a b L L') := by
  intro D cc δ B χ a b hχ hE hL h0 ha hb
  have sa := sd_stdL D a
  have sb := sd_stdL D b
  have hne : ∀ L L', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → Base.chiFac χ a b L L' ≠ 0 := fun L L' h h' =>
    mul_ne_zero (zpow_ne_zero _ (chi_detId_ne_zero hχ sa h)) (zpow_ne_zero _ (chi_detId_ne_zero hχ sb h'))
  have step : ∀ L₁ L₁' L₂ L₂', StandardLatticesGL3.SD D L₁ → StandardLatticesGL3.SD D L₁' → StandardLatticesGL3.SD D L₂ → StandardLatticesGL3.SD D L₂' → ∀ F,
      F ∈ Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D B.tor) (TaylorLogMetric.La D B.tor L₁ L₁') →
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L₁ L₁') (TaylorLogMetric.La D B.tor L₂ L₂') F ∈
        Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D B.tor) (TaylorLogMetric.La D B.tor L₂ L₂') := by
    intro L₁ L₁' L₂ L₂' h₁ h₁' h₂ h₂' F hF
    have A₁ : TaylorLogMetric.admitted D a b L₁ L₁' := ⟨ha, hb, h₁, h₁'⟩
    have A₂ : TaylorLogMetric.admitted D a b L₂ L₂' := ⟨ha, hb, h₂, h₂'⟩
    rw [iop_eq]
    exact inter_mem_Th (isHerm_formV _ _ _ _) (hL.2 a b _ _ _ _ A₁ A₂).1 (hL.1 a b _ _ A₁).2 (hL.1 a b _ _ A₂).1
      (hL.1 a b _ _ A₂).2 hF
  refine ⟨fun L L' h h' => ⟨hne L L' h h', step _ _ _ _ h sb h h' _ (step _ _ _ _ sa sb h sb _ h0)⟩, ?_, ?_⟩
  · intro L L' L'' h h' h''
    funext z
    have e : Base.chiFac χ a b L L'' * B.thMoved a b L L'' z = χ (TaylorLogMetric.detId D L' L'') ^ (-((a / 2 : ℕ) : ℤ)) *
        TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L L'')
          (fun w => Base.chiFac χ a b L L' * B.thMoved a b L L' w) z :=
      congrFun (hE.2.1 a b ⟨L, h⟩ ⟨L', h'⟩ ⟨L'', h''⟩ ha hb) z
    have f : Base.chiFac χ a b L L'' = χ (TaylorLogMetric.detId D L' L'') ^ (-((a / 2 : ℕ) : ℤ)) * Base.chiFac χ a b L L' := by
      unfold Base.chiFac
      rw [chi_detId_mul hχ sb h' h'', mul_zpow]
      ring
    rw [iop_mul, ← mul_assoc, ← f] at e
    exact mul_left_cancel₀ (hne _ _ h h'') e
  · intro L L₁ L' h h₁ h'
    funext z
    have e : Base.chiFac χ a b L₁ L' * B.thMoved a b L₁ L' z = χ (TaylorLogMetric.detId D L L₁) ^ (((b / 2 : ℕ) : ℤ)) *
        TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L')
          (fun w => Base.chiFac χ a b L L' * B.thMoved a b L L' w) z :=
      congrFun (hE.2.2 a b ⟨L, h⟩ ⟨L₁, h₁⟩ ⟨L', h'⟩ ha hb) z
    have f : Base.chiFac χ a b L₁ L' = χ (TaylorLogMetric.detId D L L₁) ^ (((b / 2 : ℕ) : ℤ)) * Base.chiFac χ a b L L' := by
      unfold Base.chiFac
      rw [chi_detId_mul hχ sa h h₁, mul_zpow]
      ring
    rw [iop_mul, ← mul_assoc, ← f] at e
    exact mul_left_cancel₀ (hne _ _ h₁ h') e

end GlobalTheory.ThetaMove.Moved
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RatIntOfIsIntegral
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.SplitK

theorem rat_int_of_isIntegral {E : Type} [Field E] [CharZero E] (r : ℚ) (h : IsIntegral ℤ (r : E)) :
    ∃ m : ℤ, (m : ℚ) = r := by
  have h1 : IsIntegral ℤ r :=
    (isIntegral_algHom_iff (algebraMap ℚ E).toIntAlgHom (algebraMap ℚ E).injective).1 (by simpa using h)
  simpa using IsIntegrallyClosed.isIntegral_iff.1 h1

theorem int_of_prime_mul_sq {d : ℕ} (hd : d.Prime) (c : ℚ) (k : ℤ) (h : (d : ℚ) * c ^ 2 = k) :
    ∃ n : ℤ, (n : ℚ) = c := by
  have h1 : IsIntegral ℤ (((d : ℚ) * c) ^ 2) := by
    have : ((d : ℚ) * c) ^ 2 = algebraMap ℤ ℚ (d * k) := by
      simp only [eq_intCast]; push_cast; rw [← h]; ring
    rw [this]; exact isIntegral_algebraMap
  obtain ⟨e, he⟩ := rat_int_of_isIntegral (E := ℚ) ((d : ℚ) * c)
    (by simpa using IsIntegral.of_pow two_pos h1)
  have h2 : e ^ 2 = d * k := by
    have : (e : ℚ) ^ 2 = d * k := by rw [he, ← h]; ring
    exact_mod_cast this
  obtain ⟨n, hn⟩ := (Nat.prime_iff_prime_int.1 hd).dvd_of_dvd_pow (n := 2) ⟨k, h2⟩
  refine ⟨n, ?_⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne_zero
  apply mul_left_cancel₀ hd0
  rw [← he, hn]; push_cast; ring

theorem jacobi_of_eq {p : ℕ} (hp : p.Prime) (d m n : ℤ) (h : m ^ 2 + d * n ^ 2 = 4 * p)
    (hm : ¬ (p : ℤ) ∣ m) : jacobiSym (-d) p = 1 := by
  have hg : m.gcd p = 1 := by
    rw [Int.gcd_comm]
    exact Int.isCoprime_iff_gcd_eq_one.1 ((Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd.2 hm)
  have h1 : jacobiSym (-d * n ^ 2) p = 1 := by
    rw [← jacobiSym.sq_one' hg]
    apply jacobiSym.mod_left'
    exact (Int.emod_emod_of_dvd _ (dvd_refl _)).symm.trans
      ((Int.emod_emod_of_dvd _ (dvd_refl _)).trans (Int.modEq_iff_dvd.2 ⟨4, by linear_combination h⟩))
  rw [jacobiSym.mul_left, jacobiSym.pow_left] at h1
  rcases jacobiSym.trichotomy (-d) p with h2 | h2 | h2
  · rw [h2] at h1; simp at h1
  · exact h2
  · rw [h2] at h1; nlinarith [sq_nonneg (jacobiSym n p)]

theorem mem_K {D : D7} {X : Fields} (s : Seam D X) (hs : s.Ok) {x : X.E} (hx : x ∈ X.Kq) :
    s.iE x ∈ D.host.K := by
  have hall : ∀ τ τ' : D.what₂.Tau, TaylorLogMetric.embT D τ (s.iE x) = TaylorLogMetric.embT D τ' (s.iE x) := fun τ τ' => by
    have h1 := hs.1 (s.iT.symm τ) x
    have h2 := hs.1 (s.iT.symm τ') x
    rw [Equiv.apply_symm_apply] at h1 h2
    rw [← h1, ← h2, hx (s.iT.symm τ) (s.iT.symm τ')]
  let τ₀ : D.what₂.Tau := D.eTau.symm 1
  have h := GlobalTheory.InducedType.sum_eq_trace D (s.iE x)
  rw [← GlobalTheory.InducedType.restrict_K D τ₀, Finset.sum_congr rfl (fun τ _ => hall τ τ₀), Finset.sum_const,
    ← map_nsmul] at h
  have h2 := (TaylorLogMetric.embT D τ₀).injective h
  rw [nsmul_eq_mul] at h2
  have hc : (((Finset.univ : Finset D.what₂.Tau).card : ℕ) : D.host.E) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 ⟨τ₀, Finset.mem_univ _⟩).ne'
  rw [eq_div_of_mul_eq hc ((mul_comm _ _).trans h2)]
  exact div_mem (Subtype.property _) (natCast_mem _ _)

theorem splitk : ∀ (D : D7) (X : Fields) (s : Seam D X) (ϖ : 𝓞 X.E) (p : ℕ), s.Ok → (ϖ : X.E) ∈ X.Kq → (∃ κ : 𝓞 D.host.K, ((κ : D.host.K) : D.host.E) = s.iE (ϖ : X.E)) ∧ (p.Prime → p ≠ 2 → ϖ * X.conjO ϖ = (p : 𝓞 X.E) → IsCoprime ϖ (X.conjO ϖ) → jacobiSym (-(D.host.d : ℤ)) p = 1) := by
  intro D X s ϖ p hs hK
  have hmem := mem_K s hs hK
  refine ⟨?_, fun hp _ hN hco => ?_⟩
  · have h1 : IsIntegral ℤ (s.iE (ϖ : X.E)) :=
      IsIntegral.map (s.iE : X.E →+* D.host.E).toIntAlgHom ϖ.isIntegral_coe
    have h2 : IsIntegral ℤ (⟨_, hmem⟩ : D.host.K) :=
      (isIntegral_algHom_iff D.host.K.val.toRingHom.toIntAlgHom D.host.K.val.toRingHom.injective).1 h1
    exact ⟨⟨_, h2⟩, rfl⟩
  · obtain ⟨a, b, hab⟩ := GlobalTheory.QuadSubfield.exists_coords D hmem
    have hc : s.iE ((X.conjO ϖ : 𝓞 X.E) : X.E) = a - b * D.host.sqrtMinusD := by
      rw [← GlobalTheory.QuadSubfield.conj_coords, ← hab, ← hs.2]; rfl
    have hsum : ((ϖ + X.conjO ϖ : 𝓞 X.E) : X.E) = ((2 * a : ℚ) : X.E) := by
      apply s.iE.injective
      rw [map_ratCast]
      push_cast
      rw [map_add (f := _), hc, hab]; ring
    obtain ⟨m, hm⟩ := rat_int_of_isIntegral (E := X.E) (2 * a) (hsum ▸ (ϖ + X.conjO ϖ).isIntegral_coe)
    have hprod : a ^ 2 + D.host.d * b ^ 2 = p := by
      have h1 := congrArg (fun z : 𝓞 X.E => s.iE (z : X.E)) hN
      push_cast at h1
      rw [map_mul, hc, hab, map_natCast] at h1
      have h2 : (a : D.host.E) ^ 2 + D.host.d * (b : D.host.E) ^ 2 = p := by
        linear_combination h1 + (b : D.host.E) ^ 2 * D.host.sqrtMinusD_sq
      exact_mod_cast h2
    obtain ⟨n, hn⟩ := int_of_prime_mul_sq D.host.hyp.2.1 (2 * b) (4 * p - m ^ 2)
      (by push_cast; rw [hm]; linear_combination 4 * hprod)
    refine jacobi_of_eq hp _ m n ?_ ?_
    · have : (m : ℚ) ^ 2 + D.host.d * (n : ℚ) ^ 2 = 4 * p := by
        rw [hm, hn]; linear_combination 4 * hprod
      exact_mod_cast this
    · rintro ⟨t, ht⟩
      have h1 : ϖ + X.conjO ϖ = (p : 𝓞 X.E) * (t : 𝓞 X.E) := by
        apply RingOfIntegers.ext
        rw [hsum, ← hm, ht]
        simp
      rw [← hN] at h1
      have u1 : IsUnit ϖ := hco.isUnit_of_dvd' dvd_rfl ⟨X.conjO ϖ * t - 1, by linear_combination h1⟩
      have u2 : IsUnit (X.conjO ϖ) := u1.map _
      have u3 : IsUnit (algebraMap ℤ (𝓞 X.E) (p : ℤ)) := by
        simpa [hN] using u1.mul u2
      have := Algebra.IsIntegral.isLocalHom ℤ (𝓞 X.E)
      exact (Nat.prime_iff_prime_int.1 hp).not_unit (isUnit_of_map_unit _ _ u3)

end GlobalTheory.MomT.SplitK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexLocPNeZero
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.VolumePos

section Index

variable {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module (𝓞 E) W]

theorem relIndex_ne_zero {M₀ M : Submodule (𝓞 E) W} (h₀ : Full M₀) (hM : M.FG) :
    M₀.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 := by
  haveI : Module.Finite (𝓞 E) M := Module.Finite.iff_fg.2 hM
  haveI : Module.Finite ℤ M := Module.Finite.trans (𝓞 E) M
  haveI : AddGroup.FG M.toAddSubgroup := Module.Finite.iff_addGroup_fg.1 ‹Module.Finite ℤ M›
  have : Finite (M.toAddSubgroup ⧸ M₀.toAddSubgroup.addSubgroupOf M.toAddSubgroup) := by
    apply AddCommGroup.finite_of_fg_torsion
    intro q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨n, hn, hx⟩ := h₀ x
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    rw [Nat.cast_smul_eq_nsmul] at hx
    exact hx
  exact AddSubgroup.index_ne_zero_of_finite

theorem relIndex_localized_ne_zero (P : HeightOneSpectrum (𝓞 E)) {M₀ M : Submodule (𝓞 E) W} (h₀ : Full M₀) (h : Full M) (hM : M.FG) :
    (localization₂ P.asIdeal M₀).toAddSubgroup.relIndex (localization₂ P.asIdeal M).toAddSubgroup ≠ 0 := by
  intro h0
  have hle : (localization₂ P.asIdeal M).toAddSubgroup ≤ M.toAddSubgroup ⊔ (localization₂ P.asIdeal M₀).toAddSubgroup := by
    intro x hx
    obtain ⟨t, h1, h2⟩ := (h.inf h₀).approx {P} x
    have h3 := h1 P (Finset.mem_singleton_self P)
    have ht : t ∈ M := mem_of_locP fun Q => by
      by_cases hQ : Q = P
      · subst hQ
        have := (localization₂ Q.asIdeal M).add_mem (localization_mono Q inf_le_left h3) hx
        rwa [sub_add_cancel] at this
      · exact localization_mono Q inf_le_left (h2 Q (by simpa using hQ))
    have : x = t - (t - x) := by abel
    rw [this]
    exact sub_mem (AddSubgroup.mem_sup_left ht) (AddSubgroup.mem_sup_right (localization_mono P inf_le_right h3))
  have h4 := AddSubgroup.relIndex_eq_zero_of_le_right hle h0
  rw [AddSubgroup.relIndex_sup_right] at h4
  exact relIndex_ne_zero h₀ hM
    (AddSubgroup.relIndex_eq_zero_of_le_left (fun x hx => mem_localization_of_mem P hx) h4)

end Index

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem homO_fg {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} (hN : N.FG) (hN' : N'.FG)
    (hs : Submodule.span E (N : Set (Sp E a)) = ⊤) : (homO N N').FG := by
  obtain ⟨T, rfl⟩ := hN
  let φ : HomE E a b →ₗ[𝓞 E] (T → Sp E b) :=
    { toFun := fun x y => x y.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := by
    intro x y hxy
    rw [Submodule.span_span_of_tower] at hs
    exact LinearMap.ext_on hs fun v hv => congrFun hxy ⟨v, hv⟩
  refine Submodule.fg_of_fg_map_injective φ hφ ?_
  refine Submodule.FG.of_le (Submodule.fg_pi (p := fun _ : T => N') fun _ => hN') ?_
  rintro _ ⟨x, hx, rfl⟩ y _
  exact hx _ (Submodule.subset_span y.2)

theorem perO_fg {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} (hA : AA.FG)
    (hH : (homO N N').FG) : (perO AA N N').FG := by
  let B : E →ₗ[𝓞 E] HomE E a b →ₗ[𝓞 E] HomE E a b :=
    LinearMap.mk₂ (𝓞 E) (fun r x => r • x) (fun _ _ _ => add_smul _ _ _) (fun _ _ _ => smul_assoc _ _ _)
      (fun _ _ _ => smul_add _ _ _) (fun _ _ _ => smul_comm _ _ _)
  refine Submodule.FG.of_le (Submodule.FG.map₂ B hA hH) (Submodule.span_le.2 ?_)
  rintro _ ⟨r, hr, x, hx, rfl⟩
  exact Submodule.apply_mem_map₂ B hr hx

theorem volC_pos : Formalism.L2.Ker.VolCPos := by
  intro E _ _ _ a b AA S N N' hN hN' hs hs' hA hA0
  have la : Submodule.IsLattice E (Formalism.L2.Col.stdLat E a) := Formalism.L2.Col.stdLat_lattice
  have lb : Submodule.IsLattice E (Formalism.L2.Col.stdLat E b) := Formalism.L2.Col.stdLat_lattice
  have hspan (n : ℕ) : Submodule.span E (Formalism.L2.Col.stdLat E n : Set (Sp E n)) = ⊤ := by
    rw [Formalism.L2.Col.stdLat_eq_span, Submodule.span_span_of_tower]
    have hbasis : (fun i : Fin n => (Pi.single i (1 : E) : Sp E n)) =
        ⇑(Pi.basisFun E (Fin n)) :=
      funext fun i => (Pi.basisFun_apply E (Fin n) i).symm
    rw [hbasis, (Pi.basisFun E (Fin n)).span_eq]
  have full₀ : Submodule.IsFullLattice E (Formalism.L2.Col.stdLat E b) :=
    { toIsLattice := lb, span_eq_top := hspan b }
  have full₁ : Submodule.IsFullLattice E N' :=
    { toIsLattice := Submodule.IsLattice.of_fg E hN', span_eq_top := hs' }
  have f₀ := PeriodComp.full AA (Formalism.L2.Col.stdLat E a)
    (Formalism.L2.Col.stdLat E b) la.fg full₀ hA0
  have f₁ := PeriodComp.full AA N N' hN full₁ hA0
  have g₀ := perO_fg hA (homO_fg la.fg lb.fg (hspan a))
  have g₁ := perO_fg hA (homO_fg hN hN' hs)
  refine Finset.prod_pos fun P _ => div_pos ?_ ?_
  · exact Nat.cast_pos.2 (Nat.pos_of_ne_zero (relIndex_localized_ne_zero P f₀ f₁ g₁))
  · exact Nat.cast_pos.2 (Nat.pos_of_ne_zero (relIndex_localized_ne_zero P f₁ f₀ g₀))

end GlobalTheory.ThetaMove.VolumePos
end

