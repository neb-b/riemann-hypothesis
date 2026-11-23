module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Formalism.SharpRestriction.Bundle0001
public import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.HostTorsionOrderLe
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumIntegralIndicatorCosetsSubspacesContaining
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumIntegralIndicatorCosetsKernelSubspaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdentityCosetEntryProportionalColumnDatum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0062

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ClassicalThetaOfDatumSmulMove
section
open NumberField IsDedekindDomain

namespace GlobalTheory.Corev.ThCLin

open Formalism.L2.Ker Formalism.L2.Th1.H

theorem hatS_mul_left {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (vol : ℝ) (SA : Finset V)
    (Φ : V → ℂ) (p : ℂ) (y : V) :
    hatS H vol SA (fun s => p * Φ s) y = p * hatS H vol SA Φ y := by
  simp only [hatS, mul_assoc, ← Finset.mul_sum]
  ring

theorem thC_smul_move : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ} (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (AA : Submodule (𝓞 E) E) (SS : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (c : ℕ) (p : ℂ) (Ξ : Formalism.L2.Col.HomE E a b → ℂ) (θ : Formalism.L2.Ker.VV ι a b → ℂ), Formalism.L2.Ker.thC emb δ d sc AA SS N N' c (fun x => p * Ξ x) θ = Formalism.L2.Ker.thC emb δ d sc AA SS N N' c Ξ (fun z => p * θ z) := by
  intro E _ _ _ ι _ a b emb δ d sc AA SS N N' c p Ξ θ
  have hon : onV emb δ (fun x => p * Ξ x) = fun v => p * onV emb δ Ξ v := by
    funext v
    unfold onV
    split_ifs <;> simp
  funext z
  simp only [thC, xiV, xiL, xiS, hon, hatS_mul_left, sumU, opU]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  ring

end GlobalTheory.Corev.ThCLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CloudAddNodeLeTenBaseSize
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX

namespace GlobalTheory

theorem cloud_add_node_le_ten_b : ∀ (C : Formalism.MainNotions.Inhab.FC) (cD ch : ℝ) (D : D7) (L : SizeData₂ D), Val C cD ch L →
    SizesAt L → L.sc.x ≤ L.sc.X' → ∀ τ : D.what₂.Tau,
    (∀ i j, (((D.hc τ).v i : ℚ) : ℝ) + (((D.hc τ).b j : ℚ) : ℝ) ≤ 10 * L.sc.b) ∧
      ∀ j j', (((D.hc τ).b j' : ℚ) : ℝ) - (((D.hc τ).b j : ℚ) : ℝ) ≤ 10 * L.sc.b := by
  intro C cD ch D L hV hS hxX τ
  obtain ⟨-, -, -, -, -, -, -, -, hLa, hRho, hBot, -, -, -, -, -, hDel, -, hBm, -⟩ := hS
  obtain ⟨hv, -, ⟨b1, hbj, htop, hthick, hthin⟩, -⟩ := hV.hc
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hL : 0 < L.sc.L := Real.rpow_pos_of_pos hx0 _
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp hL.le
  have hX'pos : 0 < L.sc.X' := Real.exp_pos _
  have hb'0 : 0 ≤ L.sc.b' := by
    unfold Scale.b' Scale.a; positivity
  have hb'b : L.sc.b' ≤ L.sc.b := by
    unfold Scale.b' Scale.a
    rw [div_le_iff₀ hX'pos]
    nlinarith
  have hwb : L.sc.w'' D.R.n ≤ L.sc.b := by
    unfold Scale.w''
    rcases Nat.eq_zero_or_pos D.R.n with hn | hn
    · simp [hn]; linarith
    · have h1 : (1:ℝ) ≤ D.R.n := by exact_mod_cast hn
      have : (1:ℝ) ≤ L.sc.x * D.R.n := by nlinarith
      exact (div_le_self hb'0 this).trans hb'b

  have hw : ((NumberField.Units.torsionOrder D.host.E : ℕ) : ℝ) ≤ L.sc.b := by
    have h1 := UpperTheory.Mu.host_torsionOrder_le D.host
    have hfk : D.R.f ≤ D.R.k := D.R.f_le_k
    have hkN : D.R.k ≤ D.R.N D.R.m := Nat.le_add_right _ _
    have hm2 := D.R.two_le_m
    have hm10 : 8 ≤ D.R.m ^ 10 := le_trans (by norm_num) (Nat.pow_le_pow_left hm2 10)
    have h2 : NumberField.Units.torsionOrder D.host.E ≤ D.R.k * (D.R.N D.R.m * D.R.m ^ 10) := by
      calc _ ≤ 8 * D.R.f ^ 2 := h1
        _ = D.R.f * (D.R.f * 8) := by ring
        _ ≤ _ := Nat.mul_le_mul hfk (Nat.mul_le_mul (hfk.trans hkN) hm10)
    have h3 : ((NumberField.Units.torsionOrder D.host.E : ℕ) : ℝ) ≤
        (D.R.k : ℝ) * ((D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10) := by exact_mod_cast h2
    have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    have h4 := mul_le_mul_of_nonneg_left hDel.1 hk0
    have hD := hDel.2.2.2.2.1
    have hth : (1 : ℝ) ≤ L.sc.x ^ szTh L :=
      Real.one_le_rpow hx.le (by unfold szTh; linarith [L.sc.eps_pos])
    have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
    have h5 : (1 : ℝ) ≤ L.sc.x ^ szTh L * D.R.m := by nlinarith
    have hkD0 : (0 : ℝ) ≤ (D.R.k : ℝ) * (D.s.Del : ℝ) := le_trans (by positivity) h4
    have h6 := le_mul_of_one_le_left hkD0 h5
    have e : (L.sc.x ^ szTh L * D.R.m) * ((D.R.k : ℝ) * (D.s.Del : ℝ)) =
        L.sc.x ^ szTh L * D.R.m * D.R.k * (D.s.Del : ℝ) := by ring
    linarith

  have hbase : ((b1 τ : ℤ) : ℝ) ≤ 3 * L.sc.b := by
    by_cases htp : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 htp
      have h1 := htop τ ⟨t, ht⟩ hte.symm
      have h2 := hBot ⟨t, ht⟩
      have hLa0 : 0 ≤ L.LaG := le_trans (Real.rpow_pos_of_pos hx0 _).le hLa.1
      have hsec : 0 ≤ L.sc.x ^ szTh L * Real.log L.sc.x * L.LaG / D.R.k := by
        have := Real.log_nonneg hx.le
        have := Real.rpow_pos_of_pos hx0 (szTh L)
        positivity
      have hx2 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by norm_num)
      have hq : szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / 4 := by
        have : 4 * szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
            4 * (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
        unfold SizeRho at hRho
        linarith
      have hq' : szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k ≤ L.sc.b' / 4 := by
        have : szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
            (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
        rw [this]; nlinarith
      have hfl : ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) ≤ L.sc.b' :=
        (Int.floor_le _).trans (div_le_self hb'0 hx.le)
      have : ((b1 τ : ℤ) : ℝ) = (L.bT ⟨t, ht⟩ : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) := by
        rw [h1]; push_cast; ring
      linarith
    · by_cases hth : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
      · have hc := Int.ceil_lt_add_one L.sc.b
        have h := (hthick τ hth).2
        have hR : ((b1 τ : ℤ) : ℝ) < ((⌈L.sc.b⌉ : ℤ) : ℝ) + ((NumberField.Units.torsionOrder D.host.E : ℕ) : ℝ) := by
          exact_mod_cast h
        linarith
      · have h := hthin τ ⟨(D.eTau τ).2, htp, hth⟩
        have hc := Int.ceil_lt_add_one (L.sc.w'' D.R.n)
        rw [h]; linarith

  have hbR : ∀ j : Fin D.R.m, (((D.hc τ).b j : ℚ) : ℝ) = (b1 τ : ℝ) + (j.1 : ℝ) * (h0v L.sc ch : ℝ) := by
    intro j; rw [(hbj τ j).1]; push_cast; ring
  have hh0 : (0 : ℝ) ≤ (h0v L.sc ch : ℝ) := Nat.cast_nonneg _
  have hspan : ∀ j : Fin D.R.m, (j.1 : ℝ) * (h0v L.sc ch : ℝ) ≤ (b1 τ : ℝ) := by
    intro j
    have hm : 0 < D.R.m := j.pos
    have hB := hBm τ hm
    rw [hbR, hbR] at hB
    have hj : (j.1 : ℝ) ≤ ((D.R.m - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : j.1 ≤ D.R.m - 1)
    have := mul_le_mul_of_nonneg_right hj hh0
    simp only [Nat.cast_zero, zero_mul, add_zero] at hB
    linarith
  refine ⟨fun i j => ?_, fun j j' => ?_⟩
  · have hm : 0 < D.R.m := j.pos
    rw [hv τ i, hbR j]
    have hD := hDel.2.2.2.2.1
    rw [hV.Del_eq] at hD
    simp only [Rat.cast_natCast] at hD
    have hth : (1 : ℝ) ≤ L.sc.x ^ szTh L :=
      Real.one_le_rpow hx.le (by unfold szTh; linarith [L.sc.eps_pos])
    have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast hm
    have hDl0 : (0 : ℝ) ≤ (Delv L.sc cD : ℝ) := Nat.cast_nonneg _
    have hkD0 : (0 : ℝ) ≤ (D.R.k : ℝ) * (Delv L.sc cD : ℝ) := by positivity
    have hkD : (D.R.k : ℝ) * (Delv L.sc cD : ℝ) ≤ L.sc.b := by
      have h1 : (1 : ℝ) ≤ L.sc.x ^ szTh L * D.R.m := by nlinarith
      have : (D.R.k : ℝ) * (Delv L.sc cD : ℝ) ≤ (L.sc.x ^ szTh L * D.R.m) * ((D.R.k : ℝ) * (Delv L.sc cD : ℝ)) := by
        nlinarith
      have e : (L.sc.x ^ szTh L * D.R.m) * ((D.R.k : ℝ) * (Delv L.sc cD : ℝ)) =
          L.sc.x ^ szTh L * D.R.m * D.R.k * (Delv L.sc cD : ℝ) := by ring
      linarith
    have hki : ((D.R.k - 2 - i.1 : ℕ) : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast (by omega : D.R.k - 2 - i.1 ≤ D.R.k)
    simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
    have := mul_le_mul_of_nonneg_right hki (by positivity : (0:ℝ) ≤ 4 * (Delv L.sc cD : ℝ))
    have := hspan j
    nlinarith
  · rw [hbR j, hbR j']
    have h1 := hspan j'
    have h2 : 0 ≤ (j.1 : ℝ) * (h0v L.sc ch : ℝ) := by positivity
    linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeIdentityIntegral
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

theorem GlobalTheory.ParHecke.heckeIdentity_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D D' : Type) [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ t : ℕ, Fintype.card D' = Fintype.card D + t → ∀ (s : Finset D') RK, IsRepsK (torusElt k D' ϖ (indic s)) RK → ∀ (sn : ℕ → Finset D) (Rn : ℕ → Finset (GL D k)), (∀ n ≤ Fintype.card D, (sn n).card = n ∧ IsRepsK (torusElt k D ϖ (-indic (sn n))) (Rn n)) → ∀ y : Matrix D' D k, ∑ g ∈ RK, intInd ((g⁻¹).1 * y) = ∑ n ∈ Finset.range (Fintype.card D + 1), (if n ≤ s.card then ((resCard k ^ (n * (t - (s.card - n))) * Formalism.L2.Col.gaussBin (resCard k) t (s.card - n) : ℕ) : ℂ) else 0) * ∑ g ∈ Rn n, intInd (y * g.1) := by
  intro k _ _ _ _ D D' _ _ _ _ ϖ hϖ t ht s RK hRK sn Rn hRn y
  have hL := _root_.GlobalTheory.ParHecke.CosetSubL.sum_intInd_cosets_up k D D' ϖ hϖ s RK hRK y
  by_cases hy : ∀ i j, y i j ∈ 𝒪[k]
  · let y₀ : Matrix D' D 𝒪[k] := fun i j => ⟨y i j, hy i j⟩
    have hy₀ : y = y₀.map (algebraMap 𝒪[k] k) := by
      ext i j; rfl
    rw [hL.2 y₀ hy₀]
    have hR : ∀ n ∈ Finset.range (Fintype.card D + 1), ∑ g ∈ Rn n, intInd (y * g.1) =
        (Nat.card {U : Submodule 𝓀[k] (D → 𝓀[k]) // U ≤ LinearMap.ker (y₀.map (IsLocalRing.residue 𝒪[k])).mulVecLin ∧ Module.finrank 𝓀[k] U = n} : ℂ) := by
      intro n hn
      have hn' : n ≤ Fintype.card D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      obtain ⟨hc, hr⟩ := hRn n hn'
      rw [(_root_.GlobalTheory.ParHecke.CosetSub.sum_intInd_cosets k D D' ϖ hϖ (sn n) (Rn n) hr y).2 y₀ hy₀, hc]
    rw [Finset.sum_congr rfl (fun n hn => by rw [hR n hn])]
    have hC := _root_.GlobalTheory.RangeKerCount.card_above_range_eq_sum 𝓀[k] (D → 𝓀[k]) (D' → 𝓀[k]) (y₀.map (IsLocalRing.residue 𝒪[k])).mulVecLin t s.card
      (by simp only [Module.finrank_fintype_fun_eq_card]; exact ht)
      (by simp only [Module.finrank_fintype_fun_eq_card]; exact Finset.card_le_univ s)
    simp only [Module.finrank_fintype_fun_eq_card] at hC
    rw [hC]
    push_cast
    refine Finset.sum_congr rfl (fun n _ => ?_)
    split_ifs <;> simp [resCard]
  · rw [hL.1 hy]
    symm
    apply Finset.sum_eq_zero
    intro n hn
    have hn' : n ≤ Fintype.card D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    rw [(_root_.GlobalTheory.ParHecke.CosetSub.sum_intInd_cosets k D D' ϖ hϖ (sn n) (Rn n) (hRn n hn').2 y).1 hy, mul_zero]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatchAtType
section
namespace GlobalTheory.SymBridge

theorem matchAtType : MatchAtType := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s S _ _ ν hν h
  exact ⟨_root_.GlobalTheory.EntryBridge.entry_agree X Pr R Ch sel S₀ mu cst σ₀ P k ι s S ν hν h,
    _root_.GlobalTheory.SymBridge.psiAgree_of_atType X Pr R Ch sel S₀ mu cst σ₀ P k ι s S ν hν h,
    _root_.GlobalTheory.SymBridge.LastStepProof.topAgree X Pr R Ch sel S₀ mu cst σ₀ P k ι s S ν hν h⟩

end GlobalTheory.SymBridge
end

