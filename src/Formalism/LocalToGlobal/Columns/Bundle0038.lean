module

public import Formalism.LocalToGlobal.Columns.ChainTw
public import Formalism.LocalToGlobal.Columns.Bundle0037
public import Formalism.LocalToGlobal.Columns.Bundle0033

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.ChainTwL
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwL

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

open Classical

theorem tw_mem_vGs_of_not {P : rowSG Pr sel mu} (hP : P.1 ∉ twQOff (Pr := Pr) sel mu) : P.1 ∈ Pr.vGs := by
  rcases Finset.mem_union.1 P.2 with h | h
  · exact h
  · by_contra hn
    exact hP (Finset.mem_sdiff.2 ⟨h, hn⟩)

theorem tw_mem_QOff {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) : P.1 ∈ twQOff (Pr := Pr) sel mu :=
  Finset.mem_sdiff.2 ⟨(Finset.mem_union.1 P.2).resolve_left hP, hP⟩

theorem twCFin_sub {i : ℕ} {st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i} {P : twQOff (Pr := Pr) sel mu}
    {D : Quotient (twSetoid (Pr := Pr) (R := R) cst.sharp (i + 1) P.1)} (hD : D ∈ twCFin Ch sel mu cst st P) :
    D ∈ twCSet Ch sel mu cst st P := by
  unfold twCFin at hD
  split_ifs at hD with hf
  · exact (Set.Finite.mem_toFinset hf).1 hD
  · exact absurd hD (Finset.notMem_empty _)

theorem twCFin_mem {i : ℕ} {st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i} {P : twQOff (Pr := Pr) sel mu}
    (hf : (twCSet Ch sel mu cst st P).Finite) {D : Quotient (twSetoid (Pr := Pr) (R := R) cst.sharp (i + 1) P.1)}
    (hD : D ∈ twCSet Ch sel mu cst st P) : D ∈ twCFin Ch sel mu cst st P := by
  unfold twCFin
  rw [dite_eq_left hf]
  exact (Set.Finite.mem_toFinset hf).2 hD

def TwNormAt {i : ℕ} (st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i) : Prop :=
  ∀ (P : twQOff (Pr := Pr) sel mu) D, D ∈ twCSet Ch sel mu cst st P →
    ∃ h, Quotient.mk _ h = D ∧ TwCand Ch sel mu cst st P h ∧ TwNF (Pr := Pr) (i + 1) P.1 h ∧ prCat (Pr := Pr) cst.sharp (i + 1) P.1 h ≤ GLint X.E (R.N (i + 1)) P.1

theorem twRep_spec {i : ℕ} {st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i} {P : twQOff (Pr := Pr) sel mu}
    {D : Quotient (twSetoid (Pr := Pr) (R := R) cst.sharp (i + 1) P.1)}
    (hD : ∃ h, Quotient.mk _ h = D ∧ TwCand Ch sel mu cst st P h ∧ TwNF (Pr := Pr) (i + 1) P.1 h ∧ prCat (Pr := Pr) cst.sharp (i + 1) P.1 h ≤ GLint X.E (R.N (i + 1)) P.1) :
    Quotient.mk _ (twRep Ch sel mu cst st P D) = D ∧ TwCand Ch sel mu cst st P (twRep Ch sel mu cst st P D) ∧
      TwNF (Pr := Pr) (i + 1) P.1 (twRep Ch sel mu cst st P D) ∧ prCat (Pr := Pr) cst.sharp (i + 1) P.1 (twRep Ch sel mu cst st P D) ≤ GLint X.E (R.N (i + 1)) P.1 :=
  Classical.epsilon_spec hD

theorem twNext_h_g {i : ℕ} (st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i) (b : (twNext Ch sel mu cst st).β)
    (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) : (twNext Ch sel mu cst st).h b P = 1 := by
  dsimp only [twNext]
  rw [dite_eq_right (fun h => (Finset.mem_sdiff.1 h).2 hP)]

theorem twNext_h_Q {i : ℕ} (st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i) (b : (twNext Ch sel mu cst st).β)
    (P : twQOff (Pr := Pr) sel mu) :
    (twNext Ch sel mu cst st).h b (twRow P) = twRep Ch sel mu cst st P (b.1 P).1 := by
  dsimp only [twNext]
  rw [dite_eq_left (show (twRow P).1 ∈ twQOff (Pr := Pr) sel mu from P.2)]
  rfl

theorem twNext_spec {i : ℕ} {st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i} (hN : TwNormAt (Ch := Ch) (cst := cst) st)
    (b : (twNext Ch sel mu cst st).β) (P : twQOff (Pr := Pr) sel mu) :
    Quotient.mk _ ((twNext Ch sel mu cst st).h b (twRow P)) = (b.1 P).1 ∧
      TwCand Ch sel mu cst st P ((twNext Ch sel mu cst st).h b (twRow P)) ∧
      TwNF (Pr := Pr) (i + 1) P.1 ((twNext Ch sel mu cst st).h b (twRow P)) ∧ prCat (Pr := Pr) cst.sharp (i + 1) P.1 ((twNext Ch sel mu cst st).h b (twRow P)) ≤ GLint X.E (R.N (i + 1)) P.1 := by
  rw [twNext_h_Q]
  exact twRep_spec (hN P _ (twCFin_sub (b.1 P).2))

theorem twNext_nonvan {i : ℕ} {st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i} (hN : TwNormAt (Ch := Ch) (cst := cst) st)
    (b : (twNext Ch sel mu cst st).β) (P : rowSG Pr sel mu) :
    ∃ al : st.β, FiniteSumNonzeroLargeDepth Ch sel mu cst i P (st.h al P) ((twNext Ch sel mu cst st).h b P) := by
  by_cases hP : P.1 ∈ twQOff (Pr := Pr) sel mu
  · obtain ⟨-, ⟨-, al, hal⟩, -, -⟩ := twNext_spec hN b ⟨P.1, hP⟩
    exact ⟨al, hal⟩
  · have hG := tw_mem_vGs_of_not hP
    obtain ⟨al, hal⟩ := b.2 P hG
    exact ⟨al, by rw [twNext_h_g st b P hG]; exact hal⟩

theorem twNext_inj {i : ℕ} {st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i} (hN : TwNormAt (Ch := Ch) (cst := cst) st)
    (b b' : (twNext Ch sel mu cst st).β)
    (H : ∀ P : rowSG Pr sel mu, SameDC (Pr := Pr) cst.sharp (i + 1) P.1 ((twNext Ch sel mu cst st).h b P) ((twNext Ch sel mu cst st).h b' P)) :
    b = b' := by
  apply Subtype.ext
  funext P
  apply Subtype.ext
  have h1 := (twNext_spec hN b P).1
  have h2 := (twNext_spec hN b' P).1
  rw [← h1, ← h2]
  exact Quotient.sound (H (twRow P))

theorem twNext_surj {i : ℕ} {st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i} (hN : TwNormAt (Ch := Ch) (cst := cst) st)
    (hfin : ∀ P, (twCSet Ch sel mu cst st P).Finite) (hg1 : ∀ al (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → st.h al P = 1)
    (hSG : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → ∀ h ∈ stabL X.E _ (lamYat (Pr := Pr) (i + 1) P.1),
      FiniteSumNonzeroLargeDepth Ch sel mu cst i P 1 h → SameDC (Pr := Pr) cst.sharp (i + 1) P.1 1 h)
    (hNV : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → FiniteSumNonzeroLargeDepth Ch sel mu cst i P 1 1)
    (hh : rowSG Pr sel mu → AutY X R (i + 1)) (hs : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → hh P ∈ stabL X.E _ (lamYat (Pr := Pr) (i + 1) P.1))
    (hb : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwBdd (Pr := Pr) (i + 1) P.1 (hh P))
    (H : ∀ P, ∃ al : st.β, FiniteSumNonzeroLargeDepth Ch sel mu cst i P (st.h al P) (hh P)) :
    ∃ b : (twNext Ch sel mu cst st).β, ∀ P, SameDC (Pr := Pr) cst.sharp (i + 1) P.1 ((twNext Ch sel mu cst st).h b P) (hh P) := by
  have hmem : ∀ P : twQOff (Pr := Pr) sel mu,
      Quotient.mk (twSetoid (Pr := Pr) (R := R) cst.sharp (i + 1) P.1) (hh (twRow P)) ∈ twCFin Ch sel mu cst st P := fun P => by
    apply twCFin_mem (hfin P)
    have hc : TwCand Ch sel mu cst st P (hh (twRow P)) := ⟨hb (twRow P) (Finset.mem_sdiff.1 P.2).2, H (twRow P)⟩
    exact ⟨hh (twRow P), rfl, hc⟩
  have hne : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → ∃ al : st.β, FiniteSumNonzeroLargeDepth Ch sel mu cst i P (st.h al P) 1 := fun P hP => by
    obtain ⟨al, -⟩ := H P
    exact ⟨al, by rw [hg1 al P hP]; exact hNV P hP⟩
  let b : (twNext Ch sel mu cst st).β := ⟨fun P => ⟨_, hmem P⟩, hne⟩
  refine ⟨b, fun P => ?_⟩
  by_cases hP : P.1 ∈ twQOff (Pr := Pr) sel mu
  · have h1 := (twNext_spec hN b ⟨P.1, hP⟩).1
    exact Quotient.exact h1
  · have hG := tw_mem_vGs_of_not hP
    rw [twNext_h_g st b P hG]
    obtain ⟨al, hal⟩ := H P
    rw [hg1 al P hG] at hal
    exact hSG P hG (hh P) (hs P hG) hal

variable (Ch sel mu cst)

theorem twSt_succ_le {m2 i : ℕ} (h : i + 1 ≤ m2) : twSt Ch sel mu cst m2 (i + 1) = twNext Ch sel mu cst (twSt Ch sel mu cst m2 i) := by
  rw [twSt, if_pos h]

theorem twSt_last (m2 : ℕ) : twSt Ch sel mu cst m2 (m2 + 1) = twUnitSt _ (m2 + 1) := by
  rw [twSt, if_neg (by omega), if_pos rfl]

theorem twSt_le (m2 : ℕ) : ∀ (j : ℕ) (_b : (twSt Ch sel mu cst m2 j).β), j ≤ m2 + 1
  | 0, _ => Nat.zero_le _
  | i + 1, b => by
      revert b
      by_cases h1 : i + 1 ≤ m2
      · intro _; omega
      · by_cases h2 : i + 1 = m2 + 1
        · intro _; omega
        · rw [show twSt Ch sel mu cst m2 (i + 1) = twEmptySt _ (i + 1) by rw [twSt, if_neg h1, if_neg h2]]
          intro b; exact b.elim

theorem twSt_h_g (m2 : ℕ) : ∀ (j : ℕ) (b : (twSt Ch sel mu cst m2 j).β) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
    (twSt Ch sel mu cst m2 j).h b P = 1
  | 0, _, _, _ => rfl
  | i + 1, b, P, hP => by
      revert b
      by_cases h1 : i + 1 ≤ m2
      · rw [twSt_succ_le Ch sel mu cst h1]
        intro b; exact twNext_h_g _ b P hP
      · by_cases h2 : i + 1 = m2 + 1
        · rw [show twSt Ch sel mu cst m2 (i + 1) = twUnitSt _ (i + 1) by rw [twSt, if_neg h1, if_pos h2]]
          intro _; rfl
        · rw [show twSt Ch sel mu cst m2 (i + 1) = twEmptySt _ (i + 1) by rw [twSt, if_neg h1, if_neg h2]]
          intro b; exact b.elim

end TwL

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.FixEColLevSym
section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section FE

variable {X : Fields} {Pr : Primes X} {R : Ranks}

private theorem mulVec_eN_eq_of_mem_HPar {κ : Type} [CommRing κ] {n r k rS t s : ℕ} (hr : r ≤ n) (ht : 0 < t)
    (hn : n = r + s * t) (hkr : k < r) (hkrS : k + rS ≤ r) (M : GL (Fin n) κ)
    (hM : M ∈ HPar n κ hr (List.replicate s t) (HPsymF κ r k rS)) :
    (M : Matrix (Fin n) (Fin n) κ) *ᵥ Loc.eN κ n k = Loc.eN κ n k := by
  rw [mem_HPar_iff hr ht hn] at hM
  obtain ⟨hB, hS⟩ := hM
  rw [mem_HPsymF_iff hkrS] at hS
  obtain ⟨s1, s2, s3⟩ := hS
  have hv := upper_block_val_submatrix hr (blockTri_blkOf_le r t hB)
  rw [mem_blockTri] at hB
  have hkn : k < n := by omega
  have he : Loc.eN κ n k = Pi.single (⟨k, hkn⟩ : Fin n) 1 := by
    funext l
    simp only [Loc.eN, Pi.single_apply, Fin.ext_iff]
  rw [he, Matrix.mulVec_single_one]
  funext i
  simp only [Matrix.col_apply, Pi.single_apply]
  by_cases hir : (i : ℕ) < r
  · have key : ∀ a b : Fin r, ((upperLeftBlock hr M : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) a b =
        (M : Matrix (Fin n) (Fin n) κ) (Fin.castLE hr a) (Fin.castLE hr b) := by
      intro a b
      rw [hv]
      rfl
    have hk' : (⟨k, hkn⟩ : Fin n) = Fin.castLE hr ⟨k, hkr⟩ := Fin.ext rfl
    rw [hk']
    by_cases hik : (i : ℕ) = k
    · have hi2 : i = Fin.castLE hr ⟨k, hkr⟩ := Fin.ext hik
      rw [if_pos hi2, hi2, ← key]
      exact s2 _
    · have hi' : i = Fin.castLE hr ⟨i, hir⟩ := Fin.ext rfl
      rw [if_neg (fun h => hik (by rw [h]; rfl)), hi', ← key]
      by_cases hrS : rS = 0
      · rcases Nat.lt_or_gt_of_ne hik with h | h
        · exact s3 _ _ h (by simp [hrS])
        · exact s1 _ _ (by simp only [symIdx, Fin.val_mk, hrS]; split_ifs <;> omega)
      · exact s1 _ _ (by simp only [symIdx, Fin.val_mk]; split_ifs <;> omega)
  · rw [if_neg (fun h => hir (by rw [h]; exact hkr))]
    exact hB _ _ (by
      simp only [blkOf, Fin.val_mk, if_pos hkr, if_neg hir]
      exact Nat.succ_pos _)

theorem fixE_colLevSym (Ch : Chars X Pr R.m) {m2 : ℕ} (hm : R.m = m2 + 2) : FixE (R := R) (colLevSym Ch) m2 := by
  intro h hh w
  have hw : h w ∈ (colLevSym Ch (m2 + 1) w).H := (Subgroup.mem_pi _).mp hh w (Set.mem_univ _)
  have e0 : ¬ (m2 + 1 = 0) := by omega
  have e1 : ¬ (m2 + 1 + 1 < R.m) := by omega
  have e2 : m2 + 1 + 1 = R.m := by omega
  unfold colLevSym at hw
  rw [if_neg e0, dite_eq_right e1, dite_eq_left e2] at hw
  exact mulVec_eN_eq_of_mem_HPar _ (by have := R.rank_add_five_le; omega)
    (by
      show R.k + (m2 + 1) * (R.t + 1) = R.k + R.m - 1 + (m2 + 1) * R.t
      rw [hm, Nat.mul_succ]
      omega)
    (by
      show R.k < R.k + R.m - 1
      have := R.two_le_m
      omega)
    (by
      show R.k + (R.m / 2 - 1) ≤ R.k + R.m - 1
      omega) _ hw

end FE

end Formalism.L2.Col
end
end

