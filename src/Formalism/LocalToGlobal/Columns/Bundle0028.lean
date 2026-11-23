module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Columns.ChainInst
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Formalism.LocalToGlobal.Columns.Bundle0027
public import Formalism.LocalToGlobal.Columns.RecLevelLocF
public import Formalism.LocalToGlobal.Columns.MtHeckeLoc
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.ChainInstS
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

theorem LocE.symmetric_level_bound_le (k₀ rS s : ℕ) : LocE.bd5 k₀ rS s ≤ s := by
  unfold LocE.bd5
  split_ifs <;> omega

section Loc

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

def symPhiCond (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (k₀ rS r t j c n : ℕ) (M : ℕ → ℕ → E) : Prop :=
  (∀ p p', p < n + c → p' < r + (j - 1) * t → IntAt P (M p p')) ∧
    (∀ p p', r + (j - 1) * t ≤ p → p < n + c → p' < r + (j - 1) * t → IntAt P (M p p' / (q : E))) ∧
    (∀ p', p' < r → redP P (M p' p') = 1 ∧ ∀ p, p < r + (j - 1) * t → p ≠ p' →
      (r ≤ p ∨ symIdx k₀ rS p' < symIdx k₀ rS p ∨ (p' = k₀ + rS ∧ p < k₀)) → redP P (M p p') = 0) ∧
    (∀ p p', r ≤ p' → p' < r + (j - 1) * t → p < r + (j - 1) * t → (p' - r) / t < (p - r) / t → redP P (M p p') = 0)

open Classical in
theorem phiGS_eq (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    (k₀ rS r t j c' n' c n : ℕ) (x : HomE E (n' + c') (n + c)) :
    LocE.PhiGS (P := P) q ψ₀ χ k₀ rS r t j c' n' c n x =
      if symPhiCond P q k₀ rS r t j c n (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x) then
        LocE.lamGvS ψ₀ χ k₀ r t (j - 1) (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x) *
          (LocE.unitV (χ (j - 1)) (Matrix.det (Matrix.of fun s s' : Fin (r + (j - 1) * t) =>
            LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x s.1 s'.1)))⁻¹
      else 0 := rfl

theorem symFPos_fIdx {k₀ c n p : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) : LocE.fPos k₀ c n (LocE.fIdx k₀ c n p) = p := by
  unfold LocE.fPos LocE.fIdx
  split_ifs <;> omega

theorem symFIdx_lt {k₀ c n p : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) : LocE.fIdx k₀ c n p < n + c := by
  unfold LocE.fIdx
  split_ifs <;> omega

theorem JGsym_entry (hq0 : (q : E) ≠ 0) {k₀ rS r t n c : ℕ} (hk : k₀ ≤ n) (hr : k₀ + rS ≤ r)
    {κ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hκ : κ ∈ LocE.JGsym P q k₀ rS r t n c) {p p' : ℕ} (hp : p < n + c) (hp' : p' < r) (hpn : p' < n + c)
    (hb : symIdx k₀ rS p' ≤ symIdx k₀ rS p ∨ (p' = k₀ + rS ∧ p < k₀)) :
    IntAt P ((LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) κ.toLinearMap p p' - if p = p' then 1 else 0) / (q : E)) := by
  have hm := (hκ.2.2 (symIdx k₀ rS p') (symIdx_lt hr hp')).2
  unfold LocE.bvecS LocE.flagS at hm
  rw [symIdxInv_symIdx, ciMem_sclLat] at hm
  have h3 := hm ⟨LocE.fIdx k₀ c n p, symFIdx_lt hk hp⟩
  have hbd : LocE.bd5 k₀ rS (symIdx k₀ rS p') ≤ symIdx k₀ rS p := by
    rcases hb with hb | ⟨h1, h2⟩
    · exact le_trans (LocE.symmetric_level_bound_le _ _ _) hb
    · subst h1
      unfold LocE.bd5 symIdx
      split_ifs <;> omega
  simp only [symFPos_fIdx hk hp, if_pos hbd] at h3
  unfold LocE.bvecG at h3
  rw [map_smul, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul] at h3
  have hat : Loc.atN (κ.toLinearMap (Loc.eN E (n + c) (LocE.fIdx k₀ c n p'))) (LocE.fIdx k₀ c n p) =
      κ (Loc.eN E (n + c) (LocE.fIdx k₀ c n p')) ⟨LocE.fIdx k₀ c n p, symFIdx_lt hk hp⟩ := by
    unfold Loc.atN
    rw [dite_eq_left (symFIdx_lt hk hp)]
    rfl
  unfold LocE.entB
  rw [hat]
  generalize κ (Loc.eN E (n + c) (LocE.fIdx k₀ c n p')) ⟨LocE.fIdx k₀ c n p, symFIdx_lt hk hp⟩ = Xv at h3 ⊢
  have he : Loc.eN E (n + c) (LocE.fIdx k₀ c n p') ⟨LocE.fIdx k₀ c n p, symFIdx_lt hk hp⟩ = if p = p' then 1 else 0 := by
    unfold Loc.eN
    by_cases hpp : p = p'
    · subst hpp
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg hpp, if_neg]
      intro h
      apply hpp
      have h' : LocE.fIdx k₀ c n p = LocE.fIdx k₀ c n p' := h
      have h1 := symFPos_fIdx (c := c) hk hp
      have h2 := symFPos_fIdx (c := c) hk hpn
      rw [h'] at h1
      omega
  rw [he] at h3
  have e : ((q : E) ^ (LocE.scE n (fun i => i + 1) (LocE.fIdx k₀ c n p) + 1))⁻¹ *
      ((q : E) ^ LocE.scE n (fun i => i + 1) (LocE.fIdx k₀ c n p') * Xv -
        (q : E) ^ LocE.scE n (fun i => i + 1) (LocE.fIdx k₀ c n p') * (if p = p' then 1 else 0)) =
      (Xv * (q : E) ^ (LocE.scE n (fun i => i + 1) (LocE.fIdx k₀ c n p') - LocE.scE n (fun i => i + 1) (LocE.fIdx k₀ c n p)) -
        if p = p' then 1 else 0) / (q : E) := by
    by_cases hpp : p = p'
    · subst hpp
      rw [if_pos rfl, sub_self, zpow_zero, zpow_add₀ hq0, zpow_one]
      have hA := zpow_ne_zero (LocE.scE n (fun i => i + 1) (LocE.fIdx k₀ c n p)) hq0
      field_simp
    · rw [if_neg hpp, zpow_sub₀ hq0, zpow_add₀ hq0, zpow_one]
      have hA := zpow_ne_zero (LocE.scE n (fun i => i + 1) (LocE.fIdx k₀ c n p)) hq0
      field_simp
      ring
  rw [← e]
  exact h3

theorem JGsym_red (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) {k₀ rS r t n c : ℕ} (hk : k₀ ≤ n) (hr : k₀ + rS ≤ r)
    {κ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hκ : κ ∈ LocE.JGsym P q k₀ rS r t n c) {p p' : ℕ} (hp : p < n + c) (hp' : p' < r) (hpn : p' < n + c)
    (hne : p ≠ p') (hb : symIdx k₀ rS p' < symIdx k₀ rS p ∨ (p' = k₀ + rS ∧ p < k₀)) :
    redP P (LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) κ.toLinearMap p p') = 0 := by
  have h := JGsym_entry hq0 hk hr hκ hp hp' hpn (hb.imp le_of_lt id)
  rw [if_neg hne, sub_zero] at h
  exact (ciRed_of_div hq hq0 h).2

theorem phiGS_col (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {k₀ rS r t j c' n' c n : ℕ} (hkr : k₀ < r) (x : HomE E (n' + c') (n + c)) (h : LocE.PhiGS (P := P) q ψ₀ χ k₀ rS r t j c' n' c n x ≠ 0)
    {p : ℕ} (hp : p < n + c) :
    IntAt P (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p k₀) ∧
      redP P (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p k₀) = if p = k₀ then 1 else 0 := by
  classical
  rw [phiGS_eq] at h
  have hC := (ite_ne_right_iff.1 h).1
  have hka : k₀ < r + (j - 1) * t := Nat.lt_of_lt_of_le hkr (Nat.le_add_right _ _)
  refine ⟨hC.1 p k₀ hp hka, ?_⟩
  by_cases hpk : p = k₀
  · rw [if_pos hpk, hpk]
    exact (hC.2.2.1 k₀ hkr).1
  · rw [if_neg hpk]
    by_cases hpa : p < r + (j - 1) * t
    · refine (hC.2.2.1 k₀ hkr).2 p hpa hpk (Or.inr ?_)
      unfold symIdx
      by_cases h0 : rS = 0
      · subst h0
        by_cases hlt : p < k₀
        · exact Or.inr ⟨rfl, hlt⟩
        · left
          split_ifs <;> omega
      · left
        split_ifs <;> omega
    · exact (ciRed_of_div hq hq0 (hC.2.1 p k₀ (Nat.le_of_not_lt hpa) hp hka)).2

theorem symEntB_join_col (q : ℕ) {k₀ n' c' n c : ℕ} (hc' : c' = 1) (hc : c = 0)
    (x₀ : HomE E n' n) (y' : Sp E n) {p : ℕ} (hp : p < n) :
    LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) (joinCol (c' := c') (c := c) x₀ y') p k₀ = (q : E) * y' ⟨p, hp⟩ := by
  subst hc' hc
  have f1 : LocE.fIdx k₀ 1 n' k₀ = n' := by
    unfold LocE.fIdx
    rw [if_neg (lt_irrefl _), if_pos (by omega)]
    omega
  have f2 : LocE.fIdx k₀ 0 n p = p := ciFIdx (Or.inl rfl) (by omega)
  unfold LocE.entB joinCol atNL
  rw [f1, f2, ciScE_lt _ hp, dite_eq_left (show n' < n' + 1 by omega)]
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
  rw [ciAtN_inX hp]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e1 : (LinearMap.funLeft E E (Fin.castAdd 1)) (Loc.eN E (n' + 1) n') = (0 : Fin n' → E) := by
    funext i
    show Loc.eN E (n' + 1) n' (Fin.castAdd 1 i) = 0
    unfold Loc.eN
    simp only [Fin.val_castAdd]
    rw [if_neg (by have := i.2; omega)]
  have e2 : Loc.eN E (n' + 1) n' ⟨n', by omega⟩ = 1 := by
    unfold Loc.eN
    rw [if_pos rfl]
  have e3 : LocE.scE n' (fun i => i + 1) n' = 1 := by simp [LocE.scE]
  rw [e1, e2, e3, map_zero, Pi.zero_apply, zero_add, one_mul, sub_zero, zpow_one, mul_comm]

end Loc

section Glob

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem psiAt_sym {m2 : ℕ} (hc' : cOf R m2 = 1) (hc : cOf R (m2 + 1) = 0) (hs : cst.sharp = true) (P : rowSG Pr sel mu)
    (hP : P.1 ∈ Pr.vGs) (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1)))
    (h : PsiAt Ch sel mu cst m2 P 1 x₀ y' ≠ 0) (i : Fin (R.N (m2 + 1))) :
    IntAt P.1 ((qOf P.1 : X.E) * y' i) ∧ redP P.1 ((qOf P.1 : X.E) * y' i) = if i.1 = R.k then 1 else 0 := by
  classical
  unfold PsiAt omPhi at h
  rw [ciOm_one] at h
  have h' := right_ne_zero_of_mul h
  unfold PhiAt at h'
  rw [if_pos hP, if_pos hs] at h'
  have hkr : R.k < R.r := by
    have := R.two_le_m
    unfold Ranks.r
    omega
  have hi : i.1 < R.N (m2 + 1) + cOf R (m2 + 1) := Nat.lt_of_lt_of_le i.2 (Nat.le_add_right _ _)
  have hq0 : ((qOf P.1 : ℕ) : X.E) ≠ 0 := Nat.cast_ne_zero.2 (qOf_pos P.1).ne'
  have a := phiGS_col (xqQ_mem P.1) hq0 _ _ hkr _ h' hi
  rw [symEntB_join_col _ hc' hc x₀ y' i.2] at a
  exact a

end Glob

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.LevPackFrLat
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E} (v : HeightOneSpectrum (𝓞 F))

theorem th_fLoc_pi (h : BasePi ST π) (a : Formalism.BasicNotions.intV E v)
    (ha : (a : E ⊗[F] v.adicCompletion F) = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E π)) (m : fMod hc n ST v) :
    a • m = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ m
  show a • fLoc hc n ST v x = 0
  rw [← map_smul, rll_fLoc_eq_zero, rll_baseKer_eq n h, rll_mem_loc_dLat n v _ (div_ne_zero h.star_ne_zero h.coe_ne_zero)]
  have hx : x.1 ∈ Formalism.L2.Herm.locL v (rll_dLat n (star (algebraMap (𝓞 E) E π))) := by
    rw [← rll_dualV_eq hc n v h]; exact x.2
  rw [rll_mem_loc_dLat n v _ h.star_ne_zero] at hx
  refine ⟨fun i hi => mul_mem a.2 (hx.1 i hi), ?_⟩
  show inclE (F := F) (v.adicCompletion F) (star (algebraMap (𝓞 E) E π) / algebraMap (𝓞 E) E π) *
    ((a : E ⊗[F] v.adicCompletion F) * x.1 (lastIdx n)) ∈ Formalism.BasicNotions.intV E v
  rw [ha, rll_cp_mul v h]
  exact hx.2

end Loc

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)
  (c₀ : DiaG (E := X.E) (ST := Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := Pr.vGs))
  (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c) (hK : LocalLevelIsKOneAtT hc u Λ)

end Gen

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.MtHeckeSum
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG Formalism.UG.P
open Formalism.L2.DIV (Pl kP St redAt)

section Sum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {v : HeightOneSpectrum (𝓞 F)} {Pb : Pl E} (U : MhlUnif Pb) (k : ℕ)

theorem mhs_cosets_finite (ST SG : Finset (Pl E)) (hov : IsOver v Pb) (hST : ∀ Q ∈ ST, ¬ IsOver v Q)
    (hSG : ∀ Q ∈ SG, ¬ IsOver v Q) (hsp : conjPrime₂ Pb ≠ Pb) (hk : k ≤ n) : (mhlCosets hc (n := n) v U k).Finite := by
  have hB := mhl_split_bij' hc U k ST SG hov hST hSG hsp hk 1
  refine Set.Finite.of_finite_image ?_ hB.injOn
  rw [hB.image_eq]
  exact DecoSet.heckeSet_finite (conjPrime₂ Pb).ne_bot (conjIdeal_ne_bot (conjPrime₂ Pb).ne_bot) k _

theorem mhs_exists_reps (ST SG : Finset (Pl E)) (hov : IsOver v Pb) (hST : ∀ Q ∈ ST, ¬ IsOver v Q)
    (hSG : ∀ Q ∈ SG, ¬ IsOver v Q) (hsp : conjPrime₂ Pb ≠ Pb) (hk : k ≤ n) :
    ∃ R : Finset (UAd hc n), Set.BijOn (fun η : UAd hc n => (QuotientGroup.mk η : UAd hc n ⧸ mhlKv hc n v)) R
      (mhlCosets hc v U k) := by
  classical
  have hfin := mhs_cosets_finite hc U k ST SG hov hST hSG hsp hk
  refine ⟨hfin.toFinset.image Quotient.out, ?_, ?_, ?_⟩
  · intro η hη
    simp only [Finset.coe_image, Set.mem_image, Set.Finite.coe_toFinset] at hη
    obtain ⟨c, hc', rfl⟩ := hη
    show (QuotientGroup.mk c.out : UAd hc n ⧸ mhlKv hc n v) ∈ mhlCosets hc v U k
    rw [QuotientGroup.out_eq']
    exact hc'
  · intro η hη η' hη' h
    simp only [Finset.coe_image, Set.mem_image, Set.Finite.coe_toFinset] at hη hη'
    obtain ⟨c, -, rfl⟩ := hη
    obtain ⟨c', -, rfl⟩ := hη'
    have h' : c = c' := (QuotientGroup.out_eq' c).symm.trans (h.trans (QuotientGroup.out_eq' c'))
    rw [h']
  · intro c hc'
    refine ⟨c.out, ?_, QuotientGroup.out_eq' c⟩
    simp only [Finset.coe_image, Set.mem_image, Set.Finite.coe_toFinset]
    exact ⟨c, hc', rfl⟩

theorem mhs_decoOf_out (ST SG : Finset (Pl E)) (hST : ∀ Q ∈ ST, ¬ IsOver v Q) (hSG : ∀ Q ∈ SG, ¬ IsOver v Q)
    (x η : UAd hc n) :
    decoOf ST SG ((x * (QuotientGroup.mk η : UAd hc n ⧸ mhlKv hc n v).out : UAd hc n) :
      GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = decoOf ST SG ((x * η : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
  obtain ⟨h, e⟩ := QuotientGroup.mk_out_eq_mul (mhlKv hc n v) η
  rw [e, ← mul_assoc, Subgroup.coe_mul]
  exact decoOf_mul_mhlKv ST SG hST hSG _ h.2

end Sum

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.QdfFrameRatio
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG Formalism.HermitianLatticesTheory

section QFr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG Q : Finset (Pl E)}

theorem qdf_frame_ratio (p p' : DecoF E n ST SG Q) (γ : Sp E n ≃ₗ[E] Sp E n)
    (hN : p'.deco.1.N = gmap γ p.deco.1.N) (P : Q) :
    ∀ y, (p'.fr P).symm (γ (p.fr P y)) ∈ stdAt E n P.1 ↔ y ∈ stdAt E n P.1 := by
  intro y
  have h1 := p'.2 P ((p'.fr P).symm (γ (p.fr P y)))
  have e1 : p'.1.2 P ((p'.fr P).symm (γ (p.fr P y))) = γ (p.fr P y) := LinearEquiv.apply_symm_apply _ _
  rw [e1] at h1
  rw [← h1]
  show γ (p.fr P y) ∈ localization₂ P.1.asIdeal p'.1.1.1.N ↔ _
  have hN' : p'.1.1.1.N = gmap γ p.1.1.1.N := hN
  rw [hN', mem_localization_gmap, LinearEquiv.symm_apply_apply]
  exact p.2 P y

def qdRatio (p p' : DecoF E n ST SG Q) (γ : Sp E n ≃ₗ[E] Sp E n) (hN : p'.deco.1.N = gmap γ p.deco.1.N) (P : Q) :
    GLint E n P.1 :=
  ⟨(p.fr P).trans (γ.trans (p'.fr P).symm), fun y => qdf_frame_ratio p p' γ hN P y⟩

end QFr

section QEmpty

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) {K : Type} [Field K]

end QEmpty

end Formalism.L2.Col
end
end

