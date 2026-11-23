module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
public import Formalism.GaloisCohomology.GaloisCohomologyProofs.LdataNonempty
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ShaLeV
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PowTotientConductor
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.VsField
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ExistsStrictHenselianAbsolutelyClosedLocalRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostCond

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CountIV
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem sum_le (n N t : ℕ) (hN : 1 ≤ N) (ht : 2 ≤ t) :
    ∑ e ∈ Finset.Ico 1 t, n * (2 * N * e) ≤ (N * t) ^ (n + 3) := by
  have h1 : ∀ m : ℕ, 2 * m ≤ 2 ^ (m + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h2 : 2 ≤ 2 ^ (m + 1) :=
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_succ 2 (m + 1)]
      omega
  have hNt : 2 ≤ N * t := by nlinarith
  have h2 : 2 ^ (n + 1) ≤ (N * t) ^ (n + 1) := Nat.pow_le_pow_left hNt _
  have h3 : N * t ^ 2 ≤ (N * t) ^ 2 := by nlinarith
  calc ∑ e ∈ Finset.Ico 1 t, n * (2 * N * e) ≤ ∑ e ∈ Finset.Ico 1 t, n * (2 * N * t) :=
        Finset.sum_le_sum fun e he => by
          have := (Finset.mem_Ico.1 he).2
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ this.le)
    _ = (t - 1) * (n * (2 * N * t)) := by simp [Finset.sum_const, Nat.card_Ico]
    _ ≤ t * (n * (2 * N * t)) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ = (2 * n) * (N * t ^ 2) := by ring
    _ ≤ (N * t) ^ (n + 1) * (N * t) ^ 2 := Nat.mul_le_mul (le_trans (h1 n) h2) h3
    _ = (N * t) ^ (n + 3) := by rw [← pow_add]

theorem UpperTheory.V.HV.countIV :
    CountIV := by
  intro χ l _ j hlB
  obtain ⟨hlp, hl2⟩ := prime_of_mem_Bchi hlB
  refine ⟨l * χ.N * l ^ j + 3, ?_⟩
  intro h hχ t ht hbig B hLay Ω _ _ _ c ψ hψ hodd
  haveI := c.dvr
  haveI := c.fin
  have hNpos : 0 < h.N := Host.N_pos h
  have hN16 := (hostIndex h).2.2.1
  have hN2 : 2 ≤ h.N := le_trans (by norm_num) (Nat.le_of_dvd hNpos hN16)
  have hbf := bchiFacts h t hbig
  have hlB' : l ∈ Bchi h.chi := by rw [hχ]; exact hlB
  have hlq1 : l ≠ h.q1 := (hbf.1 l hlB').1.ne
  have hld : l ≠ h.d := (hbf.1 l hlB').2.ne
  have hcond : ψ.conductor ∣ χ.N := by
    have := ((hostOdd h c.O ψ hψ).2 l hlp hl2 hlq1 hld hodd).1
    rw [← hχ]
    exact this
  obtain ⟨L₀, _, _, L₁, _, _, _, _, _, _, hAb, hLayer, hdeg, hker⟩ := ivField χ l j hl2 Ω
  have hgal := hker c.O h.N ψ hcond
  obtain ⟨D⟩ := ldata_nonempty (F := L₁) (Ω := Ω) l
  have hVV := hLay L₀ hAb L₁ hLayer Ω D
  have hT : Subgroup.closure ((Finset.univ : Finset (L₁ ≃ₐ[ℚ] L₁)) : Set (L₁ ≃ₐ[ℚ] L₁)) = ⊤ := by simp
  have hcard : (Finset.univ : Finset (L₁ ≃ₐ[ℚ] L₁)).card ≤ l * χ.N * l ^ j := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    exact hdeg
  have hclsker : (Chr.cls ℚ Ω h.N).ker ≤ (Chr.dirG ℚ Ω ψ).ker := by
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ ⊢
    simp [Chr.dirG, hσ]
  have hb : ∑ e ∈ Finset.Ico 1 t, (Finset.univ : Finset (L₁ ≃ₐ[ℚ] L₁)).card * LDataCardLeFinrank.nuBound l h.N e
      ≤ (h.N * t) ^ (l * χ.N * l ^ j + 3) := by
    calc _ ≤ ∑ e ∈ Finset.Ico 1 t, (Finset.univ : Finset (L₁ ≃ₐ[ℚ] L₁)).card * (2 * h.N * e) :=
          Finset.sum_le_sum fun e he => Nat.mul_le_mul_left _
            (lossLe l h.N 0 e hlp hl2 hN2 (Nat.zero_le _) (Finset.mem_Ico.1 he).1).2
      _ ≤ (h.N * t) ^ ((Finset.univ : Finset (L₁ ≃ₐ[ℚ] L₁)).card + 3) := sum_le _ h.N t (by omega) ht
      _ ≤ _ := Nat.pow_le_pow_right (Nat.mul_pos hNpos (by omega)) (by omega)
  refine Chr.nuSum.2 l c.O (fun e => Vlen Ω c e ψ) (fun e => shaLen D (e : ℤ))
    (fun e => (Finset.univ : Finset (L₁ ≃ₐ[ℚ] L₁)).card * LDataCardLeFinrank.nuBound l h.N e) t B _ ?_ hVV.2 ?_
  · intro e he1 he2
    refine ⟨hVV.1 e he1 he2, ?_⟩
    have h1 := Chr.V'_le_V (k := ℚ) (Ω := Ω) l h.N e (Chr.dirG ℚ Ω ψ)
    have h2 := Chr.upV ℚ Ω L₁ l c.O D e (Chr.dirG ℚ Ω ψ) hgal Finset.univ hT
    have h3 := (Chr.H0_local_card_bounded_of_cls_ker_le_ker Ω l c.O h.N e (Chr.dirG ℚ Ω ψ) he1.ne' hclsker).2
    calc Vlen Ω c e ψ ≤ Chr.V l e (Chr.dirG ℚ Ω ψ) := h1
      _ ≤ _ := h2
      _ ≤ shaLen D (e : ℤ) * eO l c.O + ((Finset.univ : Finset (L₁ ≃ₐ[ℚ] L₁)).card : ℕ∞) *
            ((LDataCardLeFinrank.nuBound l h.N e : ℕ∞) * eO l c.O) := by gcongr
      _ = _ := by push_cast; ring
  · exact_mod_cast hb
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CountVs
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem kBound_le (K n n0 D : ℕ) (x : ℝ) (hx : 2 ≤ x) (hn : n ≤ n0) (hD : 0 < D)
    (hl : Real.log (D : ℝ) ≤ (n : ℝ) * Real.log x) :
    kBound (K : ℝ) 1 n D ≤ x ^ ((2 * n0) ^ K * (n0 + 1)) := by
  have hx0 : 0 < x := by linarith
  have hn' : (n : ℝ) ≤ n0 := by exact_mod_cast hn
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have h2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hx1 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have h3 : Real.log (2 * (D : ℝ)) ≤ ((n0 : ℝ) + 1) * Real.log x := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right hn' hx1]
  have h4 : 0 ≤ Real.log (2 * (D : ℝ)) := Real.log_nonneg (by linarith)
  unfold kBound
  rw [← Real.exp_log (pow_pos hx0 _), Real.exp_le_exp, Real.log_pow, Real.rpow_natCast]
  push_cast
  rw [mul_assoc ((2 * (n0 : ℝ)) ^ K)]
  refine mul_le_mul ?_ h3 h4 (by positivity)
  rw [mul_one]
  gcongr

private theorem nrm_le (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (hT : eO l O ≠ ⊤)
    (a : ℕ∞) (m : ℕ) (h : a ≤ (m : ℕ∞) * eO l O) : a ≠ ⊤ ∧ Chr.nrm l O a ≤ m := by
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← hk] at h
  have hmk : (m : ℕ∞) * (k : ℕ∞) = ((m * k : ℕ) : ℕ∞) := by push_cast; rfl
  rw [hmk] at h
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) h
  refine ⟨ha, ?_⟩
  lift a to ℕ using ha
  have h' : a ≤ m * k := by exact_mod_cast h
  unfold Chr.nrm
  rw [← hk]
  simp only [ENat.toNat_coe]
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · simp [hk0]
  · rw [div_le_iff₀ (by exact_mod_cast hk0)]
    exact_mod_cast h'

private theorem final_le (A n0 : ℕ) (x v y l N : ℝ) (hl : 1 ≤ l) (hN : 2 ≤ N) (hx : x = l * N)
    (hy0 : 0 ≤ y) (hy : y ≤ l) (hv : v ≤ 2 * x ^ A + n0 * (2 * N)) :
    v * y ≤ x ^ (A + n0 + 3) := by
  have h2n : ∀ m : ℕ, m + 1 ≤ 2 ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ]; omega
  have hx2 : 2 ≤ x := by rw [hx]; nlinarith
  have hx0 : 0 ≤ x := by linarith
  have hlx : l ≤ x := by rw [hx]; nlinarith
  have hX : x ≤ x ^ (A + 1) := le_self_pow₀ (by linarith) (by omega)
  have hX0 : 0 ≤ x ^ (A + 1) := pow_nonneg hx0 _
  have hn00 : (0 : ℝ) ≤ n0 := Nat.cast_nonneg _
  have hp2 : (1 : ℝ) ≤ 2 ^ n0 := one_le_pow₀ (by norm_num)
  have hn0 : (n0 : ℝ) + 1 ≤ 2 ^ n0 := by exact_mod_cast h2n n0
  have hpow : (2 : ℝ) ^ (n0 + 2) ≤ x ^ (n0 + 2) := pow_le_pow_left₀ (by norm_num) hx2 _
  have hA0 : 0 ≤ x ^ A := pow_nonneg hx0 A
  have hpos : 0 ≤ 2 * x ^ A + n0 * (2 * N) := by nlinarith
  have e1 : x ^ A * l ≤ x ^ (A + 1) := by
    rw [pow_succ]; exact mul_le_mul_of_nonneg_left hlx hA0
  calc v * y ≤ (2 * x ^ A + n0 * (2 * N)) * y := mul_le_mul_of_nonneg_right hv hy0
    _ ≤ (2 * x ^ A + n0 * (2 * N)) * l := mul_le_mul_of_nonneg_left hy hpos
    _ = 2 * (x ^ A * l) + 2 * n0 * x := by rw [hx]; ring
    _ ≤ 2 * x ^ (A + 1) + 2 * n0 * x ^ (A + 1) := by nlinarith
    _ ≤ x ^ (A + 1) * 2 ^ (n0 + 2) := by
      rw [pow_add (2 : ℝ) n0 2]
      nlinarith [mul_le_mul_of_nonneg_left hn0 hX0, mul_le_mul_of_nonneg_left hp2 hX0]
    _ ≤ x ^ (A + 1) * x ^ (n0 + 2) := mul_le_mul_of_nonneg_left hpow hX0
    _ = x ^ (A + n0 + 3) := by rw [← pow_add]; congr 1; omega

theorem UpperTheory.V.HV.countVs :
    GlobalTheory.Published.PoitouTateDuality → LocalFinitenessK → LocalTateDualityK → ∀ CK : ℝ, LemmaK CK → CountVs := by
  intro hPT hLF hLT CK hK χ
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = (Bchi χ).sup id := ⟨_, rfl⟩
  obtain ⟨n0, hn0⟩ : ∃ n0 : ℕ, n0 = 2 * ordC χ * (16 * ordC χ * (M * χ.N) ^ 2 * M ^ (2 * (4 * ordC χ).totient)) * M :=
    ⟨_, rfl⟩
  have hK' : LemmaK (⌈CK⌉₊ : ℝ) := Win.kmono CK _ (Nat.le_ceil CK) hK
  refine ⟨(2 * n0) ^ ⌈CK⌉₊ * (n0 + 1) + n0 + 3, ?_⟩
  intro h hχ t hbig Ω _ _ _ l _ c e hl2 he0 het ψ hψX hP
  obtain ⟨⟨hlB, he1⟩, hR⟩ := hP
  subst he1
  subst hχ
  haveI := c.dvr
  haveI := c.fin
  have hlp : l.Prime := Fact.out
  have hl2' : 2 ≤ l := hlp.two_le
  obtain ⟨hIs, -⟩ := (Host.mem_X h).1 hψX
  have hNpos : 0 < h.N := Host.N_pos h
  have hN2 : 2 ≤ h.N := le_trans (by norm_num) (Nat.le_of_dvd hNpos (hostIndex h).2.2.1)
  have hlM : l ≤ M := by rw [hM]; exact Finset.le_sup (f := id) hlB
  have hord := vsOrd h c.O ψ hIs l hlp hl2 hR
  have hordM : orderOf ψ * l ≤ n0 := by
    rw [hn0]
    refine Nat.mul_le_mul (le_trans hord ?_) hlM
    show 2 * ordC h.chi * (16 * ordC h.chi * (l * h.chi.N) ^ 2 * l ^ (2 * (4 * ordC h.chi).totient)) ≤ _
    gcongr
  obtain ⟨L, _, _, _, _, _, hMu, hdeg, hcyc, hgal⟩ := vsField Ω l hl2 c.O h.N ψ
  obtain ⟨D⟩ := ldata_nonempty (F := L) (Ω := Ω) l
  have hdegn : Module.finrank ℚ L ≤ n0 := le_trans hdeg hordM
  have hT : Subgroup.closure ((Finset.univ : Finset (L ≃ₐ[ℚ] L)) : Set (L ≃ₐ[ℚ] L)) = ⊤ := by simp
  have hcard : (Finset.univ : Finset (L ≃ₐ[ℚ] L)).card ≤ n0 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    exact hdegn
  have hclsker : (Chr.cls ℚ Ω h.N).ker ≤ (Chr.dirG ℚ Ω ψ).ker := by
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ ⊢
    simp [Chr.dirG, hσ]
  have hsha : shaLen D ((1 : ℕ) : ℤ) ≤ VLen D ((1 : ℕ) : ℤ) := PropA.shaLeV hPT hLF hLT L Ω l (Or.inl hl2) D _
  have hkl := Win.klen _ hK' l L Ω D hMu 1 le_rfl
  obtain ⟨m1, hm1⟩ : ∃ m1 : ℕ, VLen D ((1 : ℕ) : ℤ) = m1 := ⟨_, (ENat.coe_toNat hkl.1).symm⟩
  have hup := Chr.upV ℚ Ω L l c.O D 1 (Chr.dirG ℚ Ω ψ) hgal Finset.univ hT
  have hh0 := (Chr.H0_local_card_bounded_of_cls_ker_le_ker Ω l c.O h.N 1 (Chr.dirG ℚ Ω ψ) one_ne_zero hclsker).2
  have heO : eO l c.O ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) (dvrFacts l c.O).2.2.2.2.2.2.1
  have hV : Vlen Ω c 1 ψ ≤ ((m1 + (Finset.univ : Finset (L ≃ₐ[ℚ] L)).card *
      LDataCardLeFinrank.nuBound l h.N 1 : ℕ) : ℕ∞) * eO l c.O := by
    calc Vlen Ω c 1 ψ ≤ Chr.V l 1 (Chr.dirG ℚ Ω ψ) := Chr.V'_le_V (k := ℚ) (Ω := Ω) l h.N 1 (Chr.dirG ℚ Ω ψ)
      _ ≤ _ := hup
      _ ≤ VLen D ((1 : ℕ) : ℤ) * eO l c.O + ((Finset.univ : Finset (L ≃ₐ[ℚ] L)).card : ℕ∞) *
            ((LDataCardLeFinrank.nuBound l h.N 1 : ℕ∞) * eO l c.O) := by gcongr
      _ = _ := by rw [hm1]; push_cast; ring
  obtain ⟨hne, hnrm⟩ := nrm_le l c.O heO _ _ hV
  refine ⟨hne, ?_⟩
  have hD : 0 < (discr L).natAbs := Int.natAbs_pos.2 (discr_ne_zero L)
  have hx2 : (2 : ℝ) ≤ (l : ℝ) * h.N := by
    have : (2 : ℝ) ≤ l := by exact_mod_cast hl2'
    have : (2 : ℝ) ≤ h.N := by exact_mod_cast hN2
    nlinarith
  have hlogD : Real.log ((discr L).natAbs : ℝ) ≤ (Module.finrank ℚ L : ℝ) * Real.log ((l : ℝ) * h.N) := by
    have := Win.disc L (l * h.N) (Nat.mul_pos (by omega) hNpos) hcyc
    push_cast at this
    exact this
  have hkb := kBound_le ⌈CK⌉₊ (Module.finrank ℚ L) n0 (discr L).natAbs ((l : ℝ) * h.N) hx2 hdegn hD hlogD
  have hnu : LDataCardLeFinrank.nuBound l h.N 1 ≤ 2 * h.N * 1 := (lossLe l h.N 0 1 hlp hl2 hN2 (Nat.zero_le _) le_rfl).2
  have hv : Vn Ω c 1 ψ ≤ 2 * ((l : ℝ) * h.N) ^ ((2 * n0) ^ ⌈CK⌉₊ * (n0 + 1)) + n0 * (2 * (h.N : ℝ)) := by
    have hc1 : ((Finset.univ : Finset (L ≃ₐ[ℚ] L)).card : ℝ) ≤ n0 := by exact_mod_cast hcard
    have hc2 : (LDataCardLeFinrank.nuBound l h.N 1 : ℝ) ≤ 2 * h.N := by
      have : (LDataCardLeFinrank.nuBound l h.N 1 : ℝ) ≤ ((2 * h.N * 1 : ℕ) : ℝ) := by exact_mod_cast hnu
      push_cast at this
      linarith
    have hc3 : (m1 : ℝ) ≤ 2 * kBound (⌈CK⌉₊ : ℝ) 1 (Module.finrank ℚ L) (discr L).natAbs := by
      have := hkl.2
      rw [hm1, ENat.toNat_coe] at this
      exact this
    calc Vn Ω c 1 ψ ≤ ((m1 + (Finset.univ : Finset (L ≃ₐ[ℚ] L)).card *
          LDataCardLeFinrank.nuBound l h.N 1 : ℕ) : ℝ) := hnrm
      _ = (m1 : ℝ) + ((Finset.univ : Finset (L ≃ₐ[ℚ] L)).card : ℝ) *
          (LDataCardLeFinrank.nuBound l h.N 1 : ℝ) := by push_cast; ring
      _ ≤ 2 * kBound (⌈CK⌉₊ : ℝ) 1 (Module.finrank ℚ L) (discr L).natAbs + n0 * (2 * (h.N : ℝ)) := by
          gcongr
      _ ≤ _ := by linarith
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hlp.one_lt.le
  have hy0 : 0 ≤ Real.log (l : ℝ) := Real.log_nonneg hl1
  have hyl : Real.log (l : ℝ) ≤ l := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hfin := final_le ((2 * n0) ^ ⌈CK⌉₊ * (n0 + 1)) n0 ((l : ℝ) * h.N) (Vn Ω c 1 ψ) (Real.log l) l h.N
    hl1 (by exact_mod_cast hN2) rfl hy0 hyl hv
  simpa using hfin
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PsiBar
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem cc_iff {Ω : Type} [Field Ω] [CharZero Ω] (σ : G ℚ Ω) : IsCC σ ↔ IsConjOm σ.toRingEquiv := Iff.rfl

private noncomputable def dirHom (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (O : Type) [CommRing O] (N : ℕ) [NeZero N] :
    DirichletCharacter O N →* (G ℚ Ω →* Oˣ) :=
  MonoidHom.mk' (Chr.dirG ℚ Ω) fun χ χ' => by
    ext σ
    simp [Chr.dirG]

private theorem dirHom_inj (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (O : Type) [CommRing O] (N : ℕ) [NeZero N] :
    Function.Injective (dirHom Ω O N) := by
  intro χ χ' h
  rw [← DirichletCharacter.toUnitHom_inj]
  ext u
  obtain ⟨σ, rfl⟩ := (Chr.clsOnto Ω N).1 u
  exact congrArg Units.val (DFunLike.congr_fun h σ)

private theorem ker_le (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O]
    [IsDomain O] {N : ℕ} [NeZero N] (ψ : DirichletCharacter O N) :
    (Chr.cls ℚ Ω l).ker ≤ (Chr.dirG ℚ Ω (comp l (th0 l ψ))).ker := by
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ ⊢
  have hl : l.Prime := Fact.out
  by_cases hlN : l ∣ N
  · have hpos : 0 < orderOf ψ := orderOf_pos ψ
    have hord : ¬ l ∣ orderOf (th0 l ψ) := (partOrd _ l hl ψ hpos).2.2.1
    have hord2 : ¬ l ∣ orderOf (comp l (th0 l ψ)) := fun h =>
      hord (dvd_trans h ((compAlg O N l hl).2.2.2.2.2.1 (th0 l ψ)).2.1)
    have hcond : (comp l (th0 l ψ)).conductor ∣ l := ((compOrd O N (th0 l ψ) l hl).2.2.1 hord2).2
    have hft : (comp l (th0 l ψ)).FactorsThrough l :=
      DirichletCharacter.FactorsThrough.mono _ (DirichletCharacter.factorsThrough_conductor _) hcond hlN
    have hk := (DirichletCharacter.factorsThrough_iff_ker_unitsMap hlN).1 hft
    have hmap : ZMod.unitsMap hlN (Chr.cls ℚ Ω N σ) = 1 := by
      have := DFunLike.congr_fun ((Chr.clsFacts ℚ Ω N).2.1 l hlN) σ
      rw [MonoidHom.comp_apply] at this
      rw [this, hσ]
    exact hk (MonoidHom.mem_ker.2 hmap)
  · have h1 : comp l (th0 l ψ) = 1 := ((compAlg O N l hl).2.2.2.2.2.1 (th0 l ψ)).2.2.1 hlN
    rw [h1]
    apply Units.ext
    show ((MulChar.toUnitHom (1 : DirichletCharacter O N)) (Chr.cls ℚ Ω N σ) : O) = 1
    rw [MulChar.coe_toUnitHom]
    simp

private theorem psi_cc (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] {N : ℕ} [NeZero N] (ψ : DirichletCharacter O N) (e : ℕ) {σ : G ℚ Ω} (h : IsConjOm σ.toRingEquiv) :
    Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1 ↔ PsiEven e ψ := by
  have hcyc : chiO ℚ Ω l O σ = -1 := by
    have h1 : cycZ ℚ Ω l σ = -1 := IsConjOm.cyc (E := ℚ) h
    simp only [chiO, MonoidHom.comp_apply, h1]
    ext
    simp
  have hcls : Chr.cls ℚ Ω N σ = -1 := (Chr.clsFacts ℚ Ω N).2.2.2.1 σ h
  have hinv : ((-1 : Oˣ) ^ e)⁻¹ = (-1) ^ e := by rw [← inv_pow, inv_neg_one]
  have hz : (chiO ℚ Ω l O ^ (e : ℤ)) σ = (-1) ^ e := by
    rw [zpow_natCast, MonoidHom.pow_apply, hcyc]
  simp only [Chr.Psi, MonoidHom.mul_apply, hz, Chr.dirG, MonoidHom.comp_apply, hcls, PsiEven]
  rw [mul_eq_one_iff_eq_inv', hinv, ← Units.val_inj, MulChar.coe_toUnitHom]
  simp

theorem UpperTheory.V.HV.psiBar :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (w : G ℚ Ω →* c.Oˣ), IsOmT c w → ∀ (N : ℕ) [NeZero N] (ψ : DirichletCharacter c.O N),
      (∃ b < l - 1, Chr.dirG ℚ Ω (comp l (th0 l ψ)) = w ^ b ∧
        ∀ e : ℕ, Congr c (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) (w ^ (e + b) * Chr.dirG ℚ Ω (chiP l ψ))) ∧
      (∀ e : ℕ, PsiEven e ψ ↔ ∀ σ : G ℚ Ω, IsCC σ → Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1) ∧
      orderOf (Chr.dirG ℚ Ω ψ) = orderOf ψ ∧
      ∀ ψ' : DirichletCharacter c.O N, Chr.dirG ℚ Ω (ψ * ψ') = Chr.dirG ℚ Ω ψ * Chr.dirG ℚ Ω ψ' ∧ (Chr.dirG ℚ Ω ψ = Chr.dirG ℚ Ω ψ' → ψ = ψ') := by
  intro Ω _ _ _ l _ c w hw N _ ψ
  have hl : l.Prime := Fact.out
  have cf := congrFacts Ω l c
  have hmul : ∀ a a' : DirichletCharacter c.O N,
      Chr.dirG ℚ Ω (a * a') = Chr.dirG ℚ Ω a * Chr.dirG ℚ Ω a' := fun a a' => map_mul (dirHom Ω c.O N) a a'
  have hpw : ∀ (a : DirichletCharacter c.O N) (n : ℕ),
      Chr.dirG ℚ Ω (a ^ n) = Chr.dirG ℚ Ω a ^ n := fun a n => map_pow (dirHom Ω c.O N) a n
  have hone : Chr.dirG ℚ Ω (1 : DirichletCharacter c.O N) = 1 := map_one (dirHom Ω c.O N)
  obtain ⟨_, hwc⟩ := hw
  have hfacts := (omT Ω l c).2 w ⟨‹_›, hwc⟩
  have hker : w.ker ≤ (Chr.dirG ℚ Ω (comp l (th0 l ψ))).ker := by
    rw [hfacts.2.1]; exact ker_le Ω l ψ
  obtain ⟨b, hb, hbeq⟩ := hfacts.2.2.2.2.2.2.2 _ hker
  refine ⟨⟨b, hb, hbeq, fun e => ?_⟩, ?_, orderOf_injective (dirHom Ω c.O N) (dirHom_inj Ω c.O N) ψ,
    fun ψ' => ⟨hmul ψ ψ', fun h => dirHom_inj Ω c.O N h⟩⟩
  · have hdec : ψ = comp l (th0 l ψ) * chiP l ψ * kap l ψ := by
      rw [chiP, mul_comm (th0 l ψ), mul_inv_cancel_left, dirichletPrimeToLPart_mul_lPowerPart]
    have hψ' : Chr.dirG ℚ Ω ψ = w ^ b * Chr.dirG ℚ Ω (chiP l ψ) * Chr.dirG ℚ Ω (kap l ψ) := by
      conv_lhs => rw [hdec]
      rw [hmul, hmul, hbeq]
    have hpos : 0 < orderOf ψ := orderOf_pos ψ
    have hkord := (partOrd _ l hl ψ hpos).1
    have hkap : Congr c (Chr.dirG ℚ Ω (kap l ψ)) 1 := by
      apply cf.2.2.1 _ ((orderOf ψ).factorization l)
      rw [← hpw, show kap l ψ = lPart l ψ from rfl, ← hkord, pow_orderOf_eq_one, hone]
    have hcw : Congr c (chiO ℚ Ω l c.O) w := cf.1.symm hwc
    have hpowc : ∀ n : ℕ, Congr c (chiO ℚ Ω l c.O ^ n) (w ^ n) := by
      intro n
      induction n with
      | zero => simp only [pow_zero]; exact cf.1.refl _
      | succ n ih => rw [pow_succ, pow_succ]; exact (cf.2.1 _ _ _ _ ih hcw).1
    have h2 := (cf.2.1 _ _ _ _ (hpowc e)
      (cf.2.1 _ _ _ _ (cf.1.refl (w ^ b * Chr.dirG ℚ Ω (chiP l ψ))) hkap).1).1
    show Congr c (chiO ℚ Ω l c.O ^ (e : ℤ) * Chr.dirG ℚ Ω ψ) (w ^ (e + b) * Chr.dirG ℚ Ω (chiP l ψ))
    rw [zpow_natCast, hψ', show w ^ (e + b) * Chr.dirG ℚ Ω (chiP l ψ)
      = w ^ e * (w ^ b * Chr.dirG ℚ Ω (chiP l ψ) * 1) by rw [mul_one, pow_add, mul_assoc]]
    exact h2
  · intro e
    constructor
    · intro hE σ hσ
      exact (psi_cc Ω l ψ e ((cc_iff σ).1 hσ)).2 hE
    · intro hall
      obtain ⟨σ0, hσ0⟩ := exists_isConjOm (E := ℚ) (Ω := Ω)
      let σ : G ℚ Ω := AlgEquiv.ofRingEquiv (f := σ0) (fun q => by simp)
      have hσ : IsConjOm σ.toRingEquiv := hσ0
      exact (psi_cc Ω l ψ e hσ).1 (hall σ ((cc_iff σ).2 hσ))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ThmHV
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem UpperTheory.V.HV.thmHV :
    PointHV → ∀ (K : BConst) (Ct : ℝ), 0 < Ct → ThmHV K Ct := by
  intro hP K Ct hCt ψ
  obtain ⟨C, r₁, r₂, hr₁, hr₂, hmain⟩ := hP ψ (fun l => Nat.log l (K.Rl l (Lchi ψ l)) + 3)
  refine ⟨(C : ℝ), r₁, r₂, hr₁, hr₂, ?_⟩
  intro eps A1 heps _
  have hJ : 0 < Jchi K Ct eps ψ := BConst.J_pos K hCt heps _ _ _
  refine ⟨(2 : ℝ) ^ Jchi K Ct eps ψ, ?_⟩
  intro e t hadm X hX q d hpair hq hd hlist _ Y hwin x hYx hxY
  obtain ⟨⟨hXY, hYX⟩, hwin'⟩ := hwin
  have hXY' : X ^ (1 / Jchi K Ct eps ψ) ≤ Y := hXY
  have h1 : ((2 : ℝ) ^ Jchi K Ct eps ψ) ^ (1 / Jchi K Ct eps ψ) ≤ X ^ (1 / Jchi K Ct eps ψ) :=
    Real.rpow_le_rpow (by positivity) hX (by positivity)
  rw [one_div, Real.rpow_rpow_inv (by norm_num) hJ.ne'] at h1
  rw [one_div] at hXY'
  have hx2 : (2 : ℝ) ≤ x := by linarith
  obtain ⟨he2, -, ht2, htx⟩ := hadm x hx2
  have hxX : x ≤ X := le_trans hxY hYX
  have htX : (t x : ℝ) ≤ X ^ Ct := le_trans htx (Real.rpow_le_rpow (by linarith) hxX hCt.le)
  intro E _ _ _ hE
  have hB := hwin' x hYx hxY
  have hq' : 2 * t x + 1 < q := by exact_mod_cast (show (2 * (t x : ℝ) + 1) < q by linarith)
  have hd' : 2 * t x + 1 < d := by exact_mod_cast (show (2 * (t x : ℝ) + 1) < d by linarith)
  have hbig : Host.Big ⟨ψ, e x, q, d, he2, hpair⟩ (t x) := by
    refine ⟨hq', hd', ?_⟩
    intro y hy
    apply hlist y
    simp only [Host.q, Host.o, List.mem_cons, List.not_mem_nil] at hy ⊢
    tauto
  have key := hmain ⟨ψ, e x, q, d, he2, hpair⟩ rfl
    (hlist r₁ (by simp)).1 (hlist r₁ (by simp)).2 (hlist r₂ (by simp)).1 (hlist r₂ (by simp)).2
    (t x) ht2 hbig (Real.exp (x ^ (4 * eps / 5))) (Real.exp_pos _).le
    (fun l hl _ => hB.2 l hl) E hE
  rw [hostCond ⟨ψ, e x, q, d, he2, hpair⟩ E hE]
  simpa [Real.rpow_natCast] using key
end

