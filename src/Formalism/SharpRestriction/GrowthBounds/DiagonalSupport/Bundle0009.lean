module

public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.SumMulSumProd
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle0005
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle0008

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.DecIdentity
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

section At

variable (p : ℕ) {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)
  {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J) (dNo : TL J Dt.nL r → ℕ)
  (ka : ZMod J → ℕ → Fin K → ℤ)
  (No : MvPolynomial (TL J Dt.nL r × Fin K) O) (Go : MvPolynomial (ML J Dt.nL r × Fin r) O)

theorem plane_dec (hA : ATL) (hS : ValSlice) (hC : ValComp) (hVB : ValBd p O Fr deg Y N₁ G' cP Dt ka No Go)
    (hSp : SuppOK p O Fr Dt dNo No Go) (δ : ZMod J × ℤ → ℕ) :
    ∃ (N : ℕ) (A' : Fin N → ZMod J → MvPolynomial (ℤ × Fin r) O),
      (∀ i j, PlOK p O Fr deg Y N₁ G' cP Dt ka δ j (A' i j)) ∧
      homComp δ (xiPl Fr O Dt.nL Go) = ∑ i, ∏ j, rename (fun v : ℤ × Fin r => ((j, v.1), v.2)) (A' i j) := by
  obtain ⟨hV1, hV2, -⟩ := hVB
  obtain ⟨hSp1, -⟩ := hSp
  let Cv : ZMod J → Set ((ℤ → Prop) × ℤ) := fun j =>
    {q | ∃ u < Dt.nL j + r, q = ((fun y => y < pU p O Fr Dt j u), ⌈tauU p O Fr deg Y N₁ G' cP Dt ka j u⌉)} ∪
    {q | ∃ u < Dt.nL j, q = ((fun y => y ≤ pU p O Fr Dt j u), ⌈tauU p O Fr deg Y N₁ G' cP Dt ka j (u + 1)⌉)}
  have hCv : ∀ j, ∀ q ∈ Cv j, ((q.2 : ℤ) : WithTop ℤ) ≤
      valS (LSeg J) {i | i.1 = j ∧ q.1 i.2} (homComp δ (xiPl Fr O Dt.nL Go)) := by
    intro j q hq
    rcases hq with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · exact le_trans (ceil_le_of_geZ (hV1 j u hu))
        (hC O (ZMod J × ℤ) r (LSeg J) (SLt j (pU p O Fr Dt j u)) (xiPl Fr O Dt.nL Go) δ).1
    · exact le_trans (ceil_le_of_geZ (hV2 j u hu))
        (hC O (ZMod J × ℤ) r (LSeg J) (SLe j (pU p O Fr Dt j u)) (xiPl Fr O Dt.nL Go) δ).1
  obtain ⟨N, A', hA', hF⟩ := seg_dec hA hS (homComp δ (xiPl Fr O Dt.nL Go)) Cv (fun _ => ∅) hCv
    (fun j q hq => by simp at hq)
  refine ⟨N, A', fun i j => ?_, hF⟩
  obtain ⟨hsup, hv, -⟩ := hA' i j
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [MvPolynomial.mem_supported]
    intro v hv'
    obtain ⟨mo, hmo, hvmo⟩ := (MvPolynomial.mem_vars_iff_mem_support v).mp (Finset.mem_coe.mp hv')
    obtain ⟨mo', hmo', he⟩ := hsup mo hmo
    have hF' := (support_homComp δ _ mo' hmo').1
    have hne : mo' ((j, v.1), v.2) ≠ 0 := by
      rw [← he]
      exact Finsupp.mem_support_iff.mp hvmo
    exact hSp1 mo' hF' ((j, v.1), v.2) (Finsupp.mem_support_iff.mpr hne)
  · intro mo hmo x
    obtain ⟨mo', hmo', he⟩ := hsup mo hmo
    rw [← (support_homComp δ _ mo' hmo').2 (j, x)]
    simp only [multideg, he]
  · intro u hu
    exact hv ((fun y => y < pU p O Fr Dt j u), ⌈tauU p O Fr deg Y N₁ G' cP Dt ka j u⌉)
      (Or.inl ⟨u, hu, rfl⟩)
  · intro u hu
    exact hv ((fun y => y ≤ pU p O Fr Dt j u), ⌈tauU p O Fr deg Y N₁ G' cP Dt ka j (u + 1)⌉)
      (Or.inr ⟨u, hu, rfl⟩)

theorem normal_dec (hA : ATL) (hS : ValSlice) (hVB : ValBd p O Fr deg Y N₁ G' cP Dt ka No Go)
    (hSp : SuppOK p O Fr Dt dNo No Go) :
    ∃ (N : ℕ) (B' : Fin N → ZMod J → MvPolynomial (ℤ × Fin K) O),
      (∀ i j, NoOK p O Fr cP Dt dNo ka j (B' i j)) ∧
      xiNo Fr O K Dt.nL No = ∑ i, ∏ j, rename (fun v : ℤ × Fin K => ((j, v.1), v.2)) (B' i j) := by
  obtain ⟨-, -, hV3⟩ := hVB
  obtain ⟨-, hSp2⟩ := hSp
  let Cl : ZMod J → Set ((ℤ → Prop) × ℤ) := fun j =>
    {q | ∃ u < Dt.nL j + r, q = ((fun y => y < pU p O Fr Dt j u), ka j u 0 + 4 * (cP : ℤ))} ∪
    {q | ∃ u < Dt.nL j + r, q = ((fun y => y ≤ pU p O Fr Dt j u), ka j (u + 1) 0 + 4 * (cP : ℤ))}
  have hCl : ∀ j, ∀ q ∈ Cl j,
      lam1S (LSeg J) {i | i.1 = j ∧ q.1 i.2} (xiNo Fr O K Dt.nL No) ≤ ((q.2 : ℤ) : WithBot ℤ) := by
    intro j q hq
    rcases hq with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · exact (hV3 j u hu).1
    · exact (hV3 j u hu).2
  obtain ⟨N, B', hB', hF⟩ := seg_dec hA hS (xiNo Fr O K Dt.nL No) (fun _ => ∅) Cl
    (fun j q hq => by simp at hq) hCl
  refine ⟨N, B', fun i j => ?_, hF⟩
  obtain ⟨hsup, -, hl⟩ := hB' i j
  refine ⟨?_, ?_, fun u hu => ⟨?_, ?_⟩⟩
  · rw [MvPolynomial.mem_supported]
    intro v hv'
    obtain ⟨mo, hmo, hvmo⟩ := (MvPolynomial.mem_vars_iff_mem_support v).mp (Finset.mem_coe.mp hv')
    obtain ⟨mo', hmo', he⟩ := hsup mo hmo
    have hne : mo' ((j, v.1), v.2) ≠ 0 := by
      rw [← he]
      exact Finsupp.mem_support_iff.mp hvmo
    exact (hSp2 mo' hmo').1 ((j, v.1), v.2) (Finsupp.mem_support_iff.mpr hne)
  · intro mo hmo x
    obtain ⟨mo', hmo', he⟩ := hsup mo hmo
    rw [← (hSp2 mo' hmo').2 (j, x)]
    simp only [multideg, he]
  · exact hl ((fun y => y < pU p O Fr Dt j u), ka j u 0 + 4 * (cP : ℤ)) (Or.inl ⟨u, hu, rfl⟩)
  · exact hl ((fun y => y ≤ pU p O Fr Dt j u), ka j (u + 1) 0 + 4 * (cP : ℤ)) (Or.inr ⟨u, hu, rfl⟩)

theorem dec_identity {N1 N2 : ℕ} (A' : Fin N1 → ZMod J → MvPolynomial (ℤ × Fin r) O)
    (B' : Fin N2 → ZMod J → MvPolynomial (ℤ × Fin K) O) :
    ∑ q : Fin (N1 * N2), ∏ t ∈ Finset.range J, phSeg O K p Fr (t : ℤ)
        (plEmb O r K (A' (finProdFinEquiv.symm q).1 (((t : ℤ)) : ZMod J)) *
          nmEmb O r K (B' (finProdFinEquiv.symm q).2 (((t : ℤ)) : ZMod J))) =
      PhiPl Fr p O K J (∑ i, ∏ j, rename (fun v : ℤ × Fin r => ((j, v.1), v.2)) (A' i j)) *
        PhiNo Fr p O K J (∑ i, ∏ j, rename (fun v : ℤ × Fin K => ((j, v.1), v.2)) (B' i j)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_prod, PhiPl_seg, PhiNo_seg]
  rw [sum_mul_sum_prod]
  refine Finset.sum_congr rfl fun q _ => ?_
  refine (prod_range_zmod (fun t : ℤ => phSeg O K p Fr t
    (plEmb O r K (A' (finProdFinEquiv.symm q).1 (t : ZMod J)) *
      nmEmb O r K (B' (finProdFinEquiv.symm q).2 (t : ZMod J))))).trans ?_
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [cast_segZ, map_mul]

end At

theorem restDecG_of (hA : ATL) (hS : ValSlice) (hC : ValComp) (hVB : RestValBdG) (hXX : RestXXG) (hDd : RestDdG) :
    RestDecG := by
  intro p _ n' r K _ _ _ O _ _ _ S Fr TT L₁ L₂ N₁ G' deg d Y cP hM J _ Dt dPl dNo ka rho No Go hMH δ hocc
  obtain ⟨hvb, hsp⟩ := hVB p O S Fr TT L₁ L₂ N₁ G' deg d Y cP hM J Dt dPl dNo ka rho No Go hMH
  have hxx := hXX p O S Fr TT L₁ L₂ N₁ G' deg d Y cP hM J Dt dPl dNo ka hMH.1
  have hdd := hDd p O S Fr TT L₁ L₂ N₁ G' deg d Y cP hM J Dt dPl dNo ka rho No Go hMH δ hocc
  have hJ : J = Fr.J := hMH.1.1.1
  obtain ⟨N1, A', hA1, hA2⟩ := plane_dec p O Fr deg Y N₁ G' cP Dt dNo ka No Go hA hS hC hvb hsp δ
  obtain ⟨N2, B', hB1, hB2⟩ := normal_dec p O Fr deg Y N₁ G' cP Dt dNo ka No Go hA hS hvb hsp
  refine ⟨N1 * N2, fun jz x => ((δ ((jz : ZMod J), x) + dNoOf p O Fr Dt dNo ((jz : ZMod J), x) : ℕ) : ℝ),
    fun q jz => plEmb O r K (A' (finProdFinEquiv.symm q).1 (jz : ZMod J)) *
      nmEmb O r K (B' (finProdFinEquiv.symm q).2 (jz : ZMod J)),
    fun jz x => δ ((jz : ZMod J), x) + dNoOf p O Fr Dt dNo ((jz : ZMod J), x), ?_, ?_, ?_⟩
  · intro q j hj
    have h := hxx δ (((j : ℤ)) : ZMod J) _ _ (hA1 (finProdFinEquiv.symm q).1 _) (hB1 (finProdFinEquiv.symm q).2 _)
    rw [segZ_cast j (by rw [hJ]; exact hj)] at h
    exact h
  · intro j hj x hx hWL
    have hs := segZ_cast (J := J) j (by rw [hJ]; exact hj)
    have h := hdd (((j : ℤ)) : ZMod J) x (by rw [hs]; exact hx) (by rw [hs]; exact hWL)
    rw [hs] at h
    exact h
  · rw [hA2, hB2, ← hJ]
    exact dec_identity p O Fr A' B'

end Formalism.MainNotions.Proposition5Numerics
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembAlgF
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section K

variable {O : Type} [CommRing O] [IsDomain O] {n' m r K : ℕ} (hk : m + 1 = r + K)

theorem toKK_mul (P Q : RRing O n' (r + K)) : toKK hk (P * Q) = toKK hk P * toKK hk Q := by
  unfold toKK
  rw [map_mul, map_mul]

theorem toKK_add (P Q : RRing O n' (r + K)) : toKK hk (P + Q) = toKK hk P + toKK hk Q := by
  unfold toKK
  rw [map_add (f := _), map_add (f := _)]

theorem toKK_C (a : O) : toKK hk (C a : RRing O n' (r + K)) = C (algebraMap O (KK O) a) := by
  simp [toKK]

theorem toKK_X_pow (v : Fin n' × Fin (r + K)) (n : ℕ) :
    toKK hk ((X v : RRing O n' (r + K)) ^ n) = (X (v.1, Fin.cast hk.symm v.2)) ^ n := by
  simp only [toKK, map_pow, rename_X, map_X]
  rfl

end K

section Shift

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ} {J : ℕ} [NeZero J]

theorem seg_shift' (hV : Fr.Valid L₁ N₁) (hJ : J = Fr.J) (j : ZMod J) :
    ∃ s : ℤ, (s = 0 ∨ s = n') ∧
      ∀ i, Fr.fr (segZ j + 1) i = Fr.fr (segZ (j + 1)) i + s ∧ Fr.fr (segZ j) i = Fr.fr (segZ (j + 1) - 1) i + s := by
  have hv : (j + 1).val = (j.val + 1) % J := by
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
  have hlt := ZMod.val_lt j
  rcases Nat.lt_or_ge (j.val + 1) J with h | h
  · refine ⟨0, Or.inl rfl, fun i => ?_⟩
    have e : segZ (j + 1) = segZ j + 1 := by
      unfold segZ
      rw [hv, Nat.mod_eq_of_lt h]
      push_cast; ring
    rw [e]
    simp
  · have hJe : j.val + 1 = J := by omega
    refine ⟨n', Or.inr rfl, fun i => ?_⟩
    have e : segZ (j + 1) = 0 := by
      unfold segZ
      rw [hv, hJe, Nat.mod_self]
      rfl
    have e2 : segZ j + 1 = 0 + (Fr.J : ℤ) := by
      unfold segZ
      rw [← hJ]
      omega
    have e3 : segZ j = -1 + (Fr.J : ℤ) := by omega
    rw [e, e2, e3]
    exact ⟨hV.2.1 0 i, by simpa using hV.2.1 (-1) i⟩

theorem wc_geom (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J) (j : ZMod J) (i : ℕ) (hi : i < r) :
    posOf n' (Fr.fr (segZ (j + 1) - 1) i) = posOf n' (Fr.fr (segZ j) i) ∧
    Fr.dist (segZ (j + 1)) (Fr.fr (segZ (j + 1) - 1) i) =
      Fr.dist (segZ j) (Fr.fr (segZ j) i) + (Fr.fr (segZ j + 1) (r - 1) - Fr.fr (segZ j) (r - 1)).toNat := by
  obtain ⟨s, hs, h⟩ := seg_shift' hV hJ j
  have h1 := (h i).2
  have h2 := (h (r - 1)).1
  have h3 := ph_z_mono Fr hV hr (j := segZ j) (j' := segZ j + 1) (by omega)
  have h4 := frame_entry_le_last Fr L₁ N₁ hV (segZ j) i hi
  refine ⟨?_, ?_⟩
  · rw [h1]
    rcases hs with rfl | rfl
    · rw [add_zero]
    · exact (bf_posOf_add _).symm
  · unfold Frames.dist
    omega

end Shift

section Hom

variable (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) {L₁ N₁ : ℕ} {J : ℕ} [NeZero J]
  (Dt : SignedChainData p O r J)

theorem plane_X (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J)
    (hgP : ∀ j (mm : Fin r), Dt.gP j mm = (Fr.fr (segZ j + 1) (r - 1) - Fr.fr (segZ j) (r - 1)).toNat)
    (v : ML J Dt.nL r × Fin r) :
    toKK hk (PhiPl Fr p O K J (xiPl Fr O Dt.nL (X v))) = upPl Fr p O hk Dt.nL (Dt.ph (X v)) := by
  obtain ⟨x, a⟩ := v
  unfold xiPl PhiPl
  rw [rename_X, aeval_X, toKK_X_pow]
  unfold SignedChainData.ph upPl
  rw [aeval_X]
  cases x with
  | ll j l => simp only [aeval_X]; rfl
  | lab j mm => simp only [aeval_X]; rfl
  | tp j mm h => simp only [aeval_X]; rfl
  | wc j mm =>
    simp only [map_pow, aeval_X]
    obtain ⟨g1, g2⟩ := wc_geom (Fr := Fr) hV hr hJ j (r - 1 - mm.val) (by omega)
    rw [← pow_mul]
    have e1 : (mlPos Fr Dt.nL (ML.wc j mm)) = (j + 1, Fr.fr (segZ (j + 1) - 1) (r - 1 - mm.val)) := rfl
    simp only [e1]
    rw [g1, g2, pow_add]
    unfold SignedChainData.P
    rw [hgP]
    rfl

theorem plane_hom (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J)
    (hgP : ∀ j (mm : Fin r), Dt.gP j mm = (Fr.fr (segZ j + 1) (r - 1) - Fr.fr (segZ j) (r - 1)).toNat)
    (Go : MvPolynomial (ML J Dt.nL r × Fin r) O) :
    toKK hk (PhiPl Fr p O K J (xiPl Fr O Dt.nL Go)) =
      upPl Fr p O hk Dt.nL (Dt.ph (MvPolynomial.map (algebraMap O (KK O)) Go)) := by
  induction Go using MvPolynomial.induction_on with
  | C a =>
    unfold xiPl
    rw [rename_C, map_C]
    have h1 : PhiPl Fr p O K J (C a) = C a := by unfold PhiPl; rw [aeval_C]; rfl
    have h2 : Dt.ph (C (algebraMap O (KK O) a)) = C (algebraMap O (KK O) a) := by
      unfold SignedChainData.ph; rw [aeval_C]; rfl
    have h3 : upPl Fr p O hk Dt.nL (C (algebraMap O (KK O) a)) = C (algebraMap O (KK O) a) := by
      unfold upPl; rw [aeval_C]; rfl
    rw [h1, h2, h3, toKK_C]
  | add P Q hP hQ =>
    have e : xiPl Fr O Dt.nL (P + Q) = xiPl Fr O Dt.nL P + xiPl Fr O Dt.nL Q := by unfold xiPl; rw [map_add (f := _)]
    rw [e, map_add (f := _), toKK_add, hP, hQ, map_add (f := _), map_add (f := _), map_add (f := _)]
  | mul_X P v hP =>
    have e : xiPl Fr O Dt.nL (P * X v) = xiPl Fr O Dt.nL P * xiPl Fr O Dt.nL (X v) := by unfold xiPl; rw [map_mul]
    rw [e, map_mul, toKK_mul, hP, plane_X p O hk Fr Dt hV hr hJ hgP v, map_mul, map_mul, map_mul, map_X]

theorem normal_hom (nL : ZMod J → ℕ) (No : MvPolynomial (TL J nL r × Fin K) O) :
    toKK hk (PhiNo Fr p O K J (xiNo Fr O K nL No)) =
      upNo Fr p O hk nL (MvPolynomial.map (algebraMap O (KK O)) No) := by
  induction No using MvPolynomial.induction_on with
  | C a =>
    unfold xiNo
    rw [rename_C, map_C]
    have h1 : PhiNo Fr p O K J (C a) = C a := by unfold PhiNo; rw [aeval_C]; rfl
    have h3 : upNo Fr p O hk nL (C (algebraMap O (KK O) a)) = C (algebraMap O (KK O) a) := by
      unfold upNo; rw [aeval_C]; rfl
    rw [h1, h3, toKK_C]
  | add P Q hP hQ =>
    have e : xiNo Fr O K nL (P + Q) = xiNo Fr O K nL P + xiNo Fr O K nL Q := by unfold xiNo; rw [map_add (f := _)]
    rw [e, map_add (f := _), toKK_add, hP, hQ, map_add (f := _), map_add (f := _)]
  | mul_X P v hP =>
    have e : xiNo Fr O K nL (P * X v) = xiNo Fr O K nL P * xiNo Fr O K nL (X v) := by unfold xiNo; rw [map_mul]
    have hX : toKK hk (PhiNo Fr p O K J (xiNo Fr O K nL (X v))) = upNo Fr p O hk nL (X v) := by
      unfold xiNo PhiNo upNo
      rw [rename_X, aeval_X, toKK_X_pow, aeval_X]
      rfl
    rw [e, map_mul, toKK_mul, hP, hX, map_mul, map_mul, map_X]

theorem label_hom (nL : ZMod J → ℕ) (rho : TL J nL r × Fin (r + K) → ℕ) :
    toKK hk (monomial (labO Fr K nL rho) (1 : O)) = monomial (labMon Fr hk nL rho) 1 := by
  have h : Finsupp.mapDomain (castVK (n' := n') hk) (labO Fr K nL rho) = labMon Fr hk nL rho := by
    rw [labMon_eq, Fintype.sum_prod_type]
    unfold labO
    rw [Finsupp.mapDomain_finsetSum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finsupp.mapDomain_finsetSum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finsupp.mapDomain_single]
    rfl
  unfold toKK
  rw [rename_monomial, map_monomial, map_one, h]

theorem alg_identity (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J)
    (hgP : ∀ j (mm : Fin r), Dt.gP j mm = (Fr.fr (segZ j + 1) (r - 1) - Fr.fr (segZ j) (r - 1)).toNat)
    (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (No : MvPolynomial (TL J Dt.nL r × Fin K) O)
    (Go : MvPolynomial (ML J Dt.nL r × Fin r) O) : AlgAt p O hk Fr Dt rho No Go := by
  unfold AlgAt asm
  rw [toKK_mul, toKK_mul, label_hom, plane_hom p O hk Fr Dt hV hr hJ hgP, normal_hom, mul_assoc]

end Hom

theorem restAlgG : RestAlgG := by
  intro p _ n' r K m _ _ _ O _ _ _ _ hk Fr TT L₁ L₂ N₁ G' deg d Y cP hM J _ Dt dPl dNo ka rho No Go hMH
  exact alg_identity p O hk Fr Dt hM.frames.2.1 (le_trans (by norm_num) hM.two_le_r) hMH.1.1.1 hMH.1.1.2.2.2.2.1 rho No Go

end Formalism.MainNotions.Proposition5Numerics
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PosULeIff
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section Ord2

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ}

theorem posU_lt_iff' (hV : Fr.Valid L₁ N₁) (j : ℤ) (N : ℕ) (hN : N = (Fr.LLset j).card) (a b : ℕ) (ha : a < N + r)
    (hb : b < N + r) : posU Fr N j a < posU Fr N j b ↔ a < b := by
  subst hN; exact posU_lt_iff hV j a b ha hb

theorem posU_le_iff' (hV : Fr.Valid L₁ N₁) (j : ℤ) (N : ℕ) (hN : N = (Fr.LLset j).card) (a b : ℕ) (ha : a < N + r)
    (hb : b < N + r) : posU Fr N j a ≤ posU Fr N j b ↔ a ≤ b := by
  subst hN; exact posU_le_iff hV j a b ha hb

theorem posU_ll' (j : ℤ) (N : ℕ) (l : ℕ) (hl : l < N) : posU Fr N j l = llPos Fr j l := by
  unfold posU
  rw [if_pos hl]

theorem posU_fr' (j : ℤ) (N : ℕ) (i : ℕ) : posU Fr N j (N + i) = Fr.fr j i := by
  unfold posU
  rw [if_neg (by omega), Nat.add_sub_cancel_left]

theorem w_lt_posU' (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (N : ℕ) (hN : N = (Fr.LLset j).card) (i u : ℕ) (hi : i < r)
    (hu : u < N + r) : Fr.fr (j - 1) i < posU Fr N j u := by
  subst hN; exact w_lt_posU hV hr j i u hi hu

end Ord2

section Pre

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ} {J : ℕ} {nL : ZMod J → ℕ}

theorem ml_ll_lt (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) (j' : ZMod J) (l : Fin (nL j')) :
    mlPos Fr nL (ML.ll j' l) ∈ SLt j (posU Fr (nL j) (segZ j) u) ↔ j' = j ∧ l.val < u := by
  show (j' = j ∧ llPos Fr (segZ j') l.val < _) ↔ _
  constructor
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_ll' (Fr := Fr) (segZ j') (nL j') l.val l.isLt] at h
    exact (posU_lt_iff' hV (segZ j') (nL j') (hnL j') l.val u (by omega) hu).mp h
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_ll' (Fr := Fr) (segZ j') (nL j') l.val l.isLt]
    exact (posU_lt_iff' hV (segZ j') (nL j') (hnL j') l.val u (by omega) hu).mpr h

theorem ml_ll_le (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) (j' : ZMod J) (l : Fin (nL j')) :
    mlPos Fr nL (ML.ll j' l) ∈ SLe j (posU Fr (nL j) (segZ j) u) ↔ j' = j ∧ l.val ≤ u := by
  show (j' = j ∧ llPos Fr (segZ j') l.val ≤ _) ↔ _
  constructor
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_ll' (Fr := Fr) (segZ j') (nL j') l.val l.isLt] at h
    exact (posU_le_iff' hV (segZ j') (nL j') (hnL j') l.val u (by omega) hu).mp h
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_ll' (Fr := Fr) (segZ j') (nL j') l.val l.isLt]
    exact (posU_le_iff' hV (segZ j') (nL j') (hnL j') l.val u (by omega) hu).mpr h

theorem fr_lt (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) (j' : ZMod J) (m : Fin r) :
    (j' = j ∧ Fr.fr (segZ j') (r - 1 - m.val) < posU Fr (nL j) (segZ j) u) ↔ j' = j ∧ nL j + (r - 1 - m.val) < u := by
  have hm := m.isLt
  constructor
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_fr' (Fr := Fr) (segZ j') (nL j')] at h
    exact (posU_lt_iff' hV _ _ (hnL j') _ u (by omega) hu).mp h
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_fr' (Fr := Fr) (segZ j') (nL j')]
    exact (posU_lt_iff' hV _ _ (hnL j') _ u (by omega) hu).mpr h

theorem fr_le (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) (j' : ZMod J) (m : Fin r) :
    (j' = j ∧ Fr.fr (segZ j') (r - 1 - m.val) ≤ posU Fr (nL j) (segZ j) u) ↔ j' = j ∧ nL j + (r - 1 - m.val) ≤ u := by
  have hm := m.isLt
  constructor
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_fr' (Fr := Fr) (segZ j') (nL j')] at h
    exact (posU_le_iff' hV _ _ (hnL j') _ u (by omega) hu).mp h
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_fr' (Fr := Fr) (segZ j') (nL j')]
    exact (posU_le_iff' hV _ _ (hnL j') _ u (by omega) hu).mpr h

theorem tl_pre_lt (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) : tlPos Fr nL ⁻¹' SLt j (posU Fr (nL j) (segZ j) u) = NSet nL j u := by
  ext ⟨j', x⟩
  rcases x with l | m
  · rw [Set.mem_preimage]
    refine (ml_ll_lt hV hnL j u hu j' l).trans ?_
    constructor
    · rintro ⟨rfl, h⟩
      exact Or.inl ⟨l, rfl, h⟩
    · rintro (⟨l', he, h⟩ | ⟨m', he, _⟩)
      · obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.mp he
        cases he2
        exact ⟨rfl, h⟩
      · obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.mp he
        cases he2
  · rw [Set.mem_preimage]
    refine (fr_lt hV hnL j u hu j' m).trans ?_
    constructor
    · rintro ⟨rfl, h⟩
      exact Or.inr ⟨m, rfl, h⟩
    · rintro (⟨l', he, _⟩ | ⟨m', he, h⟩)
      · obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.mp he
        cases he2
      · obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.mp he
        cases he2
        exact ⟨rfl, h⟩

theorem tl_pre_le (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) : tlPos Fr nL ⁻¹' SLe j (posU Fr (nL j) (segZ j) u) = NSet nL j (u + 1) := by
  ext ⟨j', x⟩
  rcases x with l | m
  · rw [Set.mem_preimage]
    refine (ml_ll_le hV hnL j u hu j' l).trans ?_
    constructor
    · rintro ⟨rfl, h⟩
      exact Or.inl ⟨l, rfl, by omega⟩
    · rintro (⟨l', he, h⟩ | ⟨m', he, _⟩)
      · obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.mp he
        cases he2
        exact ⟨rfl, by omega⟩
      · obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.mp he
        cases he2
  · rw [Set.mem_preimage]
    refine (fr_le hV hnL j u hu j' m).trans ?_
    constructor
    · rintro ⟨rfl, h⟩
      exact Or.inr ⟨m, rfl, by omega⟩
    · rintro (⟨l', he, _⟩ | ⟨m', he, h⟩)
      · obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.mp he
        cases he2
      · obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.mp he
        cases he2
        exact ⟨rfl, by omega⟩

end Pre

end Formalism.MainNotions.Proposition5Numerics
end
end

