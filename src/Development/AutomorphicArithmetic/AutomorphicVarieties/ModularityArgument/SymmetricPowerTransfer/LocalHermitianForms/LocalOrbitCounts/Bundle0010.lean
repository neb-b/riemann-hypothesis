module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.NotEvenIrr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.LeftMulMatrixEmbeddingDetEqNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.HermAdj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.ExistsRho

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.KapMove
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem inv_norm {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K} (L : IsLoc O Δ)
    {c : K} {d m : EL Δ τ} (h : IsDat c d m) : ∀ t ∈ NE τ, ∀ x : Kˣ,
    lcount O c d (((t * x : Kˣ) : K) • m) = lcount O c d ((x : K) • m) := fun t ht x => by
  rw [Units.val_mul, mul_smul]
  exact lcountNorm O K Δ τ L c d _ (datSmul K Δ τ c d m h x) t ht

theorem UpperTheory.V.Z.Sym.Loc.kapMove : UpperTheory.V.Z.Sym.Loc.KapMove := by
  intro O K _ _ _ _ _ Δ τ L hr c hc z hz lam lam' hn hn' htr htr'
  have h2 : (2 + τ : K) ≠ 0 := by
    intro h0
    apply hr
    have : τ = -2 := by linear_combination h0
    rw [this]
    norm_num
  obtain ⟨ul, hul⟩ : IsUnit lam :=
    QuadraticAlgebra.isUnit_iff_norm_isUnit.2 (by rw [hn]; exact h2.isUnit)
  have hβ : QuadraticAlgebra.norm (lam' * ((ul⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ)) = 1 := by
    have e : QuadraticAlgebra.norm (ul : Lsq K Δ) *
        QuadraticAlgebra.norm ((ul⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [hul, hn] at e
    rw [map_mul, hn', e]
  obtain ⟨y, hy⟩ := h90L O K Δ L _ hβ
  have hl' : lam' = lam * star (y : Lsq K Δ) * ((y⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ) := by
    rw [hy, ← hul]
    have e1 : (ul : Lsq K Δ) * ((ul⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ) = 1 := Units.mul_inv ul
    have e2 : (y : Lsq K Δ) * ((y⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ) = 1 := Units.mul_inv y
    linear_combination (-lam' * ((y : Lsq K Δ) * ((y⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ))) * e1 + (-lam') * e2
  set Y : (EL Δ τ)ˣ := Units.map (algebraMap (Lsq K Δ) (EL Δ τ)).toMonoidHom y with hYdef
  have hsig : ∀ a : Lsq K Δ, sigL (algebraMap (Lsq K Δ) (EL Δ τ) a) =
      algebraMap (Lsq K Δ) (EL Δ τ) (star a) := by
    intro a
    ext <;> simp [sigL]
  have hstar : ∀ a : Lsq K Δ, star (algebraMap (Lsq K Δ) (EL Δ τ) a) =
      algebraMap (Lsq K Δ) (EL Δ τ) a := by
    intro a
    ext <;> simp
  have hYc : (Y : EL Δ τ) = algebraMap (Lsq K Δ) (EL Δ τ) y := rfl
  have hYi : ((Y⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) =
      algebraMap (Lsq K Δ) (EL Δ τ) ((y⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ) := rfl
  have hA : dLam lam z * sigL (Y : EL Δ τ) * ((Y⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) = dLam lam' z := by
    rw [hYc, hYi, hsig, hl']
    simp only [dLam, Algebra.smul_def, map_mul]
    ring
  set g : Kˣ := Units.map (QuadraticAlgebra.norm : Lsq K Δ →* K) y with hgdef
  have hB : ∀ x : Kˣ, ((x : K) • (1 : EL Δ τ)) * ↑Y * star (sigL (Y : EL Δ τ)) =
      ((x * g : Kˣ) : K) • (1 : EL Δ τ) := by
    intro x
    rw [hYc, hsig, hstar, mul_assoc, ← map_mul, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    rw [Units.val_mul, mul_smul]
    have hgc : ((g : Kˣ) : K) = QuadraticAlgebra.norm (y : Lsq K Δ) := rfl
    rw [hgc, smul_one_mul]
    congr 1
    rw [Algebra.smul_def, mul_one]
    exact (IsScalarTower.algebraMap_apply K (Lsq K Δ) (EL Δ τ) _).symm
  have hD' := datLam K Δ τ c hr hc lam' hn' z hz
  have hf : ∀ t ∈ NE τ, ∀ x : Kˣ,
      (fun x : Kˣ => lcount O c (dLam lam' z) ((x : K) • (1 : EL Δ τ))) (t * x) =
      (fun x : Kˣ => lcount O c (dLam lam' z) ((x : K) • (1 : EL Δ τ))) x :=
    fun t ht x => inv_norm L hD' t ht x
  have hss := (sumShift O K Δ τ L hr (fun x : Kˣ => lcount O c (dLam lam' z) ((x : K) • (1 : EL Δ τ))) hf g).2.1
  have hk : kapSum O c (dLam lam z) 1 = hs (τ ^ 2 - 4) (QuadraticAlgebra.norm (y : Lsq K Δ)) *
      kapSum O c (dLam lam' z) 1 := by
    unfold kapSum
    rw [← show ((g : Kˣ) : K) = QuadraticAlgebra.norm (y : Lsq K Δ) from rfl, ← hss]
    refine finsum_congr (fun t => ?_)
    congr 1
    rw [(datIso O K Δ τ c (dLam lam z) (((Quotient.out t : Kˣ) : K) • 1) Y).1, hA, hB]
  have hε : eps τ lam' = hs (τ ^ 2 - 4) (QuadraticAlgebra.norm (y : Lsq K Δ)) * eps τ lam := by
    have htr'' := htr'
    rw [hl'] at htr'' ⊢
    exact signLaw O K Δ τ L hr lam y hn htr htr''
  rw [hk, hε]
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.PStable
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.pStable :
    UpperTheory.V.Z.Sym.Loc.PStable := by
  intro O K _ _ _ _ _ Δ τ L hr j χ hj hχ a ha
  haveI := L.frac
  have hnω : QuadraticAlgebra.norm (a : Etau K τ) = 1 := by
    rw [ha, QuadraticAlgebra.norm_def]
    simp
  have hR : gOrb O j χ a = ((PS.Fv O τ).ncard : ℂ) := by
    rw [gLat O K Δ τ L hr j χ hj hχ a 1 1 (by rw [hnω]; simp), ← PS.vcount_eq L hr]
    simp [ha]
  rw [hR]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hp0 : algebraMap O K π ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]
    exact hπ.ne_zero
  set p : Kˣ := Units.mk0 _ hp0 with hpdef
  have hpv : ((p : Kˣ) : K) = algebraMap O K π := rfl
  have hpe : ¬ EvenVal O ((p : Kˣ) : K) := by
    rw [hpv]
    exact PS.not_even_irr L hπ
  have hfv : ∀ t : Kˣ, (PS.Fv O τ).ncard = (PS.Gs O τ (↑t) 1).ncard + (PS.Gs O τ (↑(t * p)) 1).ncard :=
    fun t => PS.fv_card L hr t p hpe
  by_cases hD : IsSquare (τ ^ 2 - 4)
  · have hI := UpperTheory.evenValuation_norm_compactUnits_of_split O K Δ τ L hr hD
    have hall : ∀ x : Kˣ, x ∈ NE τ := fun x =>
      (hsNE O K Δ τ L hr x).2 ((hsLaw O K Δ L).2.2.2 (τ ^ 2 - 4) x hr hD)
    obtain ⟨r, hrr⟩ := hD
    have hr0 : r ≠ 0 := by
      rintro rfl
      apply hr
      rw [hrr, mul_zero]
    have h2 : (2 : K) ≠ 0 := by
      have h := L.two.map (algebraMap O K)
      rw [map_ofNat] at h
      exact h.ne_zero
    set β : K := (τ - r) / 2 with hβdef
    set u : K := (((p : Kˣ) : K) - 1) / r with hudef
    have hb : β ^ 2 - τ * β + 1 = 0 := by
      rw [hβdef]
      field_simp
      linear_combination (-1 : K) * hrr
    have hτβ : τ - 2 * β = r := by
      rw [hβdef]
      field_simp
      ring
    have hru : r * u = ((p : Kˣ) : K) - 1 := by
      rw [hudef]
      field_simp
    set w : Etau K τ := ⟨1 - β * u, u⟩ with hwdef
    have hw : QuadraticAlgebra.norm w = ((p : Kˣ) : K) := by
      rw [QuadraticAlgebra.norm_def, hwdef]
      simp only
      linear_combination u ^ 2 * hb + u * hτβ + hru
    obtain ⟨y0, hy0⟩ : IsUnit w :=
      QuadraticAlgebra.isUnit_iff_norm_isUnit.2 (by rw [hw]; exact p.isUnit)
    have hy0n : QuadraticAlgebra.norm (y0 : Etau K τ) = ((p : Kˣ) : K) := by rw [hy0, hw]
    have hy0u : PS.nU y0 = p := Units.ext (by rw [PS.nU_val, hy0n])
    have hy0C : y0 ∉ Cint O τ := by
      intro h
      have := hI.1 y0 h
      rw [hy0n] at this
      exact hpe this
    have hpc : ∀ t : Kˣ, pcount O τ ↑t = ((PS.Fv O τ).ncard : ℂ) := by
      intro t
      have c1 : ∀ y : (Etau K τ)ˣ, ∃ z, ∃ c ∈ Cint O τ, y = 1 * c * z ^ 2 ∨ y = y0 * c * z ^ 2 := by
        intro y
        have hyne : QuadraticAlgebra.norm (y : Etau K τ) ≠ 0 := by
          rw [← PS.nU_val]
          exact Units.ne_zero _
        rcases PS.even_or L hyne hp0 hpe with he | he
        · obtain ⟨z, c, hc, hyc⟩ := hI.2 y he
          exact ⟨z, c, hc, Or.inl (by rw [one_mul, hyc])⟩
        · have e : QuadraticAlgebra.norm ((y * y0⁻¹ : (Etau K τ)ˣ) : Etau K τ) =
              QuadraticAlgebra.norm (y : Etau K τ) / ((p : Kˣ) : K) := by
            rw [← PS.nU_val, map_mul, map_inv, hy0u, Units.val_mul, Units.val_inv_eq_inv_val,
              PS.nU_val, div_eq_mul_inv]
          obtain ⟨z, c, hc, hyc⟩ := hI.2 (y * y0⁻¹) (e ▸ he)
          refine ⟨z, c, hc, Or.inr ?_⟩
          rw [mul_assoc, ← hyc, mul_comm, inv_mul_cancel_right]
      have c2 : ∀ z : (Etau K τ)ˣ, z ^ 2 * 1 * y0⁻¹ ∈ Cint O τ → z ∈ Cint O τ := by
        intro z hz
        exfalso
        have hE := hI.1 _ hz
        have hzn : ((PS.nU z : Kˣ) : K) ≠ 0 := Units.ne_zero _
        have e : QuadraticAlgebra.norm ((z ^ 2 * 1 * y0⁻¹ : (Etau K τ)ˣ) : Etau K τ) =
            ((PS.nU z : Kˣ) : K) ^ 2 / ((p : Kˣ) : K) := by
          rw [← PS.nU_val, map_mul, map_mul, map_pow, map_one, mul_one, map_inv, hy0u, Units.val_mul,
            Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, div_eq_mul_inv]
        rw [e] at hE
        have hsq : EvenVal O (((PS.nU z : Kˣ) : K) ^ 2) := ⟨1, (PS.nU z : K), hzn, by simp⟩
        apply hpe
        have := PS.even_mul hsq (PS.even_inv hE)
        have hp' : ((PS.nU z : Kˣ) : K) ^ 2 * (((PS.nU z : Kˣ) : K) ^ 2 / ((p : Kˣ) : K))⁻¹ =
            ((p : Kˣ) : K) := by
          field_simp
        rwa [hp'] at this
      rw [PS.pcount_eq L hr t 1 y0 c1 c2]
      have hdisj : Disjoint (PS.Gs O τ (↑t) 1) (PS.Gs O τ (↑t) y0) := by
        rw [Set.disjoint_left]
        rintro S ⟨-, c, hc, hg⟩ ⟨-, c', hc', hg'⟩
        have hu := PS.gen_uniq hg hg'
        apply hy0C
        have e : y0 = (1 * c) * ((1 * c)⁻¹ * (y0 * c')) * c'⁻¹ := by group
        rw [e]
        exact mul_mem (mul_mem (by rw [one_mul]; exact hc) hu) (inv_mem hc')
      rw [Set.ncard_union_eq hdisj (PS.gs_fin L hr t 1) (PS.gs_fin L hr t y0), PS.gs_ncard ((t : Kˣ) : K) y0,
        hy0u, hfv t, Units.val_mul]
    rw [finsum_eq_single _ (QuotientGroup.mk 1 : Kˣ ⧸ NE τ), hpc]
    intro t ht
    exfalso
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective t
    exact ht (QuotientGroup.eq.2 (hall _))
  · have hC := UpperTheory.compactTorusUnits_eq_top_of_nonsplit O K Δ τ L hr hD
    have hpc : ∀ (t : Kˣ) (b : (Etau K τ)ˣ), pcount O τ ↑t = ((PS.Gs O τ (↑t) b).ncard : ℂ) := by
      intro t b
      rw [PS.pcount_eq L hr t b b (fun y => ⟨1, b⁻¹ * y, by rw [hC]; trivial, Or.inl (by group)⟩)
        (fun z _ => by rw [hC]; trivial), Set.union_self]
    have hinv : ∀ t ∈ NE τ, ∀ x : Kˣ, pcount O τ ↑(t * x) = pcount O τ ↑x := by
      rintro t ⟨b, rfl⟩ x
      rw [hpc x b, PS.gs_ncard, hpc _ 1, Units.val_mul, mul_comm]
      rfl
    obtain ⟨⟨g0, hg0⟩, hsum⟩ := UpperTheory.finsum_quotient_norms_of_nonsplit O K Δ τ L hr hD
    have e : ∀ t : Kˣ, ((PS.Fv O τ).ncard : ℂ) = pcount O τ ↑t + pcount O τ ↑(t * p) := by
      intro t
      rw [hfv t, Nat.cast_add, hpc t 1, hpc (t * p) 1]
    by_cases hpN : p ∈ NE τ
    · have hS : ∑ᶠ t : Kˣ ⧸ NE τ, pcount O τ ↑(Quotient.out t) = pcount O τ ↑(1 : Kˣ) + pcount O τ ↑g0 :=
        hsum (fun x : Kˣ => pcount O τ ↑x) hinv g0 hg0
      rw [hS]
      have e1 := e 1
      have e2 := e g0
      rw [mul_comm, hinv p hpN] at e1 e2
      linear_combination (-1 / 2 : ℂ) * e1 + (-1 / 2 : ℂ) * e2
    · have hS : ∑ᶠ t : Kˣ ⧸ NE τ, pcount O τ ↑(Quotient.out t) = pcount O τ ↑(1 : Kˣ) + pcount O τ ↑p :=
        hsum (fun x : Kˣ => pcount O τ ↑x) hinv p hpN
      rw [hS, e 1, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.ThetaMem
section
open QuadraticAlgebra Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem mem_iff_fst_mem_and_snd_mem_of_isFix_of_isUnit_two_sub {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    {Δ τ : K} (hL : IsLoc O Δ) (hτ : τ ∈ (algebraMap O K).range) (h2 : ∃ u : Oˣ, algebraMap O K u = 2 - τ)
    {c : K} {d m : EL Δ τ} (hD : IsDat c d m) {S : Set (Sp Δ τ)} (hS : IsFix O c d m S) (x : Sp Δ τ) :
    x ∈ S ↔ (x.1, (0 : EL Δ τ)) ∈ S ∧ ((0 : Lsq K Δ), x.2) ∈ S := by
  obtain ⟨hadd, -, hfst, hsnd⟩ := UpperTheory.V.Z.Sym.Loc.One.splitS O K Δ τ hL hτ h2 c d m hD S hS
  constructor
  · intro hx
    refine ⟨hfst x hx, ?_⟩
    have h := hsnd x hx 1 ⟨1, by simp⟩ ⟨0, by simp⟩
    rwa [ofE_one, one_mul] at h
  · rintro ⟨h1, h3⟩
    have h := hadd _ h1 _ h3
    simpa using h

private theorem mem_iff_mk_ofE_mul_snd_mem_of_forall_inr_iff {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    {Δ τ : K} (hL : IsLoc O Δ) (hτ : τ ∈ (algebraMap O K).range) (h2 : ∃ u : Oˣ, algebraMap O K u = 2 - τ)
    {c : K} {d m : EL Δ τ} (hD : IsDat c d m) {S₀ S₁ : Set (Sp Δ τ)} (h₀ : IsFix O c d m S₀)
    (h₁ : IsFix O c d m S₁) (s : K) (y₀ : (EL Δ τ)ˣ)
    (hy : ∀ S : Set (Sp Δ τ), IsFix O c d m S → ∀ x : EL Δ τ, ((0 : Lsq K Δ), x) ∈ S ↔
      ∃ a b : Etau K τ, x = ↑y₀ * (ofE Δ a + ({ re := 0, im := s } : Lsq K Δ) • ofE Δ b) ∧
        ((0 : Lsq K Δ), ↑y₀ * ofE Δ a) ∈ S ∧ ((0 : Lsq K Δ), ↑y₀ * ofE Δ b) ∈ S)
    (q : (Etau K τ)ˣ)
    (hq : ∀ a : Etau K τ, ((0 : Lsq K Δ), ↑y₀ * ofE Δ a) ∈ S₀ ↔
      ((0 : Lsq K Δ), ↑y₀ * ofE Δ ((q : Etau K τ) * a)) ∈ S₁)
    (x : Sp Δ τ) : x ∈ S₀ ↔ (x.1, ofE Δ (q : Etau K τ) * x.2) ∈ S₁ := by
  rw [mem_iff_fst_mem_and_snd_mem_of_isFix_of_isUnit_two_sub hL hτ h2 hD h₀ x, mem_iff_fst_mem_and_snd_mem_of_isFix_of_isUnit_two_sub hL hτ h2 hD h₁ (x.1, ofE Δ (q : Etau K τ) * x.2)]
  dsimp only
  have hf : (x.1, (0 : EL Δ τ)) ∈ S₀ ↔ (x.1, (0 : EL Δ τ)) ∈ S₁ :=
    ⟨UpperTheory.V.Z.Sym.Loc.One.fst O K Δ τ hL hτ h2 c d m hD S₀ S₁ h₀ h₁ x.1,
      UpperTheory.V.Z.Sym.Loc.One.fst O K Δ τ hL hτ h2 c d m hD S₁ S₀ h₁ h₀ x.1⟩
  refine and_congr hf ?_
  rw [hy S₀ h₀, hy S₁ h₁]
  constructor
  · rintro ⟨a, b, hx, ha, hb⟩
    refine ⟨(q : Etau K τ) * a, (q : Etau K τ) * b, ?_, (hq a).1 ha, (hq b).1 hb⟩
    rw [hx, ofE_mul, ofE_mul, Algebra.smul_def, Algebra.smul_def]
    ring
  · rintro ⟨a, b, hx, ha, hb⟩
    refine ⟨(↑q⁻¹ : Etau K τ) * a, (↑q⁻¹ : Etau K τ) * b, ?_, (hq _).2 (by rwa [Units.mul_inv_cancel_left]),
      (hq _).2 (by rwa [Units.mul_inv_cancel_left])⟩
    have hq1 : ofE Δ (↑q⁻¹ : Etau K τ) * ofE Δ (q : Etau K τ) = 1 := by
      rw [← ofE_mul, Units.inv_mul, ofE_one]
    calc x.2 = ofE Δ (↑q⁻¹ : Etau K τ) * (ofE Δ (q : Etau K τ) * x.2) := by
          rw [← mul_assoc, hq1, one_mul]
      _ = _ := by
        rw [hx, ofE_mul, ofE_mul, Algebra.smul_def, Algebra.smul_def]
        ring

private theorem mem_iff_tor_mem_of_isFix_of_isIntegral_quo {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    {Δ τ : K} (hL : IsLoc O Δ) (hu : ∃ u : Oˣ, algebraMap O K u = τ ^ 2 - 4)
    {c : K} {d m : EL Δ τ} (hD : IsDat c d m) {S : Set (Sp Δ τ)} (hS : IsFix O c d m S)
    (z : (Etau K τ)ˣ) (hz1 : IsIntegral O (quo z)) (hz2 : IsIntegral O (quo z⁻¹)) (x : Sp Δ τ) :
    x ∈ S ↔ tor Δ z x ∈ S := by
  obtain ⟨hτ, h2, -, -⟩ := UpperTheory.V.Z.Sym.Loc.One.intE O K Δ τ hL hu
  obtain ⟨u, s, hs, hΔ⟩ := hL.even
  obtain ⟨y₀, hy⟩ := UpperTheory.V.Z.Sym.Loc.One.snd O K Δ τ hL hu c d m hD s⁻¹ u
    (by rw [hΔ, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hs), mul_one])
  have hω : ∀ x ∈ {a : Etau K τ | ((0 : Lsq K Δ), ↑y₀ * ofE Δ a) ∈ S},
      ω * x ∈ {a : Etau K τ | ((0 : Lsq K Δ), ↑y₀ * ofE Δ a) ∈ S} := by
    intro x hx
    have h := (UpperTheory.V.Z.Sym.Loc.One.splitS O K Δ τ hL hτ h2 c d m hD S hS).2.2.2 _ hx ω ⟨0, by simp⟩ ⟨1, by simp⟩
    simp only [Set.mem_setOf_eq] at h ⊢
    rw [ofE_mul, mul_left_comm]
    exact h
  obtain ⟨u₀, hu₀⟩ := UpperTheory.V.Z.Sym.Loc.One.princ O K Δ τ hL hu _
    (UpperTheory.V.Z.Sym.Loc.One.lat O K Δ τ hL c d m S hS y₀) hω
  simp only [Set.mem_setOf_eq] at hu₀
  have hqq : quo z * quo z⁻¹ = 1 := by
    simp only [quo, inv_inv]
    have e1 : (z : Etau K τ) * ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) = 1 := Units.mul_inv z
    have e2 : star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * star (z : Etau K τ) = 1 := by
      rw [← star_mul, Units.mul_inv, star_one]
    linear_combination (star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * star (z : Etau K τ)) * e1 + e2
  let q : (Etau K τ)ˣ := ⟨quo z, quo z⁻¹, hqq, by rw [mul_comm]; exact hqq⟩
  have H := mem_iff_mk_ofE_mul_snd_mem_of_forall_inr_iff hL hτ h2 hD hS hS s⁻¹ y₀ hy q (by
    intro a
    rw [hu₀, hu₀]
    show IsIntegral O ((↑u₀⁻¹ : Etau K τ) * a) ↔ IsIntegral O ((↑u₀⁻¹ : Etau K τ) * (quo z * a))
    constructor
    · intro h
      have h' := hz1.mul h
      have e : quo z * ((↑u₀⁻¹ : Etau K τ) * a) = (↑u₀⁻¹ : Etau K τ) * (quo z * a) := by ring
      rwa [e] at h'
    · intro h
      have h' := hz2.mul h
      have e : quo z⁻¹ * ((↑u₀⁻¹ : Etau K τ) * (quo z * a)) = (↑u₀⁻¹ : Etau K τ) * a := by
        linear_combination ((↑u₀⁻¹ : Etau K τ) * a) * hqq
      rwa [e] at h') x
  exact H

theorem UpperTheory.V.Z.Sym.Loc.oneU :
    UpperTheory.V.Z.Sym.Loc.OneU := by
  intro O K _ _ _ _ _ Δ τ hL c d m hD δ ι P hM hδ hu
  obtain ⟨u, s, hs, hΔ⟩ := hL.even
  have hstar : ∀ x : Lsq K Δ, IsInt O x → IsInt O (star x) := fun x =>
    ((UpperTheory.V.Z.Sym.Loc.descent O K Δ hL s⁻¹ u
      (by rw [hΔ, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hs), mul_one])) x).2
  have kuOf : ∀ g : U3 Δ, (∀ v : Fin 3 → Lsq K Δ, (∀ i, IsInt O (v i)) →
      ∀ i, IsInt O (((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ v) i)) → g ∈ KU O Δ := by
    intro g hg
    have hij : ∀ i j, IsInt O ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j) := by
      intro i j
      have h := hg (Pi.single j 1) (by
        intro k
        simp only [Pi.single_apply]
        split_ifs
        · exact isIntegral_one
        · exact isIntegral_zero) i
      simpa [Matrix.mulVec_single] using h
    show ∀ i j, IsInt O ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j) ∧
      IsInt O (star ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j))
    exact fun i j => ⟨hij i j, hstar _ (hij i j)⟩
  have h1fix := UpperTheory.V.Z.Sym.Loc.One.fixg O K Δ τ hL c d m δ ι P hM 1
    (by rw [inv_one, one_mul, map_one, mul_one]; exact hδ)
  have hmem1 : ∀ x : Sp Δ τ, x ∈ {x : Sp Δ τ | ∀ i, IsInt O
      (((((1 : U3 Δ)⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ P x) i)} ↔ ∀ i, IsInt O (P x i) := by
    intro x
    simp
  have hθ : ∀ g : U3 Δ, ((theta Δ g : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) =
      (g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map star := fun g => rfl
  have hstarmv : ∀ (M : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (v : Fin 3 → Lsq K Δ),
      star (M *ᵥ v) = M.map star *ᵥ star v := by
    intro M v
    funext i
    simp [Matrix.mulVec, dotProduct, star_sum, star_mul']
  have hcomm : ∀ z : (Etau K τ)ˣ, (ι z)⁻¹ * δ * theta Δ (ι z) = δ := by
    intro z
    have hv : ∀ x : Sp Δ τ, ((δ * theta Δ (ι z) : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ star (P x) =
        ((ι z * δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ star (P x) := by
      intro x
      have e1 : semi d (tor Δ z x) = tor Δ z (semi d x) := by
        simp only [semi, tor, sigL_mul, sigL_ofE]
        exact Prod.ext rfl (by dsimp only; ring)
      have e2 := congrArg P e1
      rw [hM.semi, hM.tor, hM.tor, hM.semi, hstarmv] at e2
      rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hθ]
      exact e2
    have hM' : ((δ * theta Δ (ι z) : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) =
        ((ι z * δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) := by
      funext i j
      have h := congrFun (hv (P.symm (star (Pi.single j 1)))) i
      simpa [Matrix.mulVec_single] using h
    have hU : δ * theta Δ (ι z) = ι z * δ := Subtype.ext hM'
    rw [mul_assoc, hU, ← mul_assoc, inv_mul_cancel, one_mul]
  refine ⟨fun y => ⟨fun hy => ?_, ?_⟩, le_antisymm ?_ ?_⟩
  · have hyfix := UpperTheory.V.Z.Sym.Loc.One.fixg O K Δ τ hL c d m δ ι P hM y hy
    obtain ⟨z, hz⟩ := UpperTheory.V.Z.Sym.Loc.One.uniq O K Δ τ hL hu c d m hD _ _ h1fix hyfix
    refine ⟨z, (ι z)⁻¹ * y, ?_, by rw [← mul_assoc, mul_inv_cancel, one_mul]⟩
    apply kuOf
    intro v hv i
    have hx := (hz (P.symm ((((ι z)⁻¹ * y : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ v))).2 (by
      show ∀ i, IsInt O ((((y⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ
        P (tor Δ z (P.symm ((((ι z)⁻¹ * y : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ v)))) i)
      rw [hM.tor, LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        ← Submonoid.coe_mul, ← Submonoid.coe_mul]
      have e : y⁻¹ * ι z * ((ι z)⁻¹ * y) = 1 := by group
      rw [e, Submonoid.coe_one, Matrix.one_mulVec]
      exact hv)
    rw [hmem1] at hx
    simpa using hx i
  · rintro ⟨z, k, hk, rfl⟩
    have hθk : theta Δ k ∈ KU O Δ := by
      have hk' : ∀ i j, IsInt O ((k : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j) ∧
          IsInt O (star ((k : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j)) := hk
      show ∀ i j, IsInt O (((theta Δ k : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j) ∧
        IsInt O (star (((theta Δ k : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j))
      intro i j
      rw [hθ]
      simp only [Matrix.map_apply, star_star]
      exact ⟨(hk' i j).2, (hk' i j).1⟩
    have e : (ι z * k)⁻¹ * δ * theta Δ (ι z * k) = k⁻¹ * ((ι z)⁻¹ * δ * theta Δ (ι z)) * theta Δ k := by
      rw [map_mul, _root_.mul_inv_rev]
      simp only [mul_assoc]
    rw [e, hcomm z]
    exact mul_mem (mul_mem (inv_mem hk) hδ) hθk
  · intro z hz
    apply (UpperTheory.V.Z.Sym.Loc.stabU O K Δ τ hL c d m hD δ ι P hM 1).1
    show (MulAut.conj (1 : U3 Δ)⁻¹).toMonoidHom (ι z) ∈ KU O Δ
    simpa using hz
  · intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    show ι z ∈ KU O Δ
    apply kuOf
    intro v hv i
    have hx := (mem_iff_tor_mem_of_isFix_of_isIntegral_quo hL hu hD h1fix z hz1 hz2 (P.symm v)).1 ((hmem1 _).2 (by simpa using hv))
    rw [hmem1, hM.tor] at hx
    simpa using hx i
end

