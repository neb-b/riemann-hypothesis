module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0045
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PlusHatsPassGenerators
section
namespace GlobalTheory.HatNF.GenPlus

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open Formalism.FourierDecayAlt.P.MAx3.H

noncomputable section

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem star_inv_eq {x xi y yi : A} (h : star x = y) (hx : x * xi = 1) (hy : y * yi = 1) : star xi = yi := by
  have h1 : star xi * y = 1 := by rw [← h, ← star_mul, hx, star_one]
  calc star xi = star xi * (y * yi) := by rw [hy, mul_one]
    _ = yi := by rw [← mul_assoc, h1, one_mul]

theorem star_list_prod (l : List A) : star l.prod = (l.map star).reverse.prod := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.prod_cons, star_mul, ih, List.map_cons, List.reverse_cons, List.prod_append,
      List.prod_singleton]

variable {P : M.Par} {d : Q.NFData P A}

theorem mem_span {b h : A} (hb : b ∈ bmon d) (hh : h ∈ hats d.L) : b * h ∈ nfSpan d (hats d.L) 0 0 1 :=
  Submodule.subset_span ⟨b, hb, [h], rfl, by simpa using hh, by simp⟩

theorem ahat_mem (y : ℂ) : d.L.Ahat y ∈ hats d.L := Or.inl (Or.inl (Or.inl ⟨y, rfl⟩))
theorem plusHatR_mem_hatLettersAllPoints (y : ℂ) : d.L.R0 y ∈ hats d.L := Or.inl (Or.inl (Or.inr ⟨y, rfl⟩))

theorem kappa_comm (h : HatHyp d) (f : M.Ty P → ℂ) (y : ℂ) :
    Commute (d.κ f) (d.L.Ahat y) ∧ Commute (d.κ f) (d.L.R0 y) := by
  obtain ⟨-, -, hR, -, -, -, hs⟩ := h
  have hf : ∀ g ∈ d.L.fns, Commute (d.κ f) g := fun g hg => hR.2.1 f g (Or.inl hg)
  have hn : Commute (d.κ f) d.L.nab := hR.2.1 f _ (Or.inr (by simp))
  have hp : ∀ l, Commute (d.κ f) (d.L.p l) := fun l => hs f _ (by simp [TL.siteOps])
  have hT := d.L.inv_comm_Tprod hp (fun l => hf _ (d.L.inv_mem_c l)) (fun l => hf _ (d.L.inv_mem_ci l)) y
  have hDr : Commute (d.κ f) d.L.Dr := LevelData.inv_comm_ofFn fun l => hf _ (d.L.inv_mem_c l)
  have hDrb : Commute (d.κ f) d.L.Drb := LevelData.inv_comm_ofFn fun l => hf _ (d.L.inv_mem_cb l)
  have hl0 : Commute (d.κ f) (d.L.l0 y) :=
    hn.neg_right.sub_right ((Algebra.commute_algebraMap_right _ _).mul_right
      ((hf _ d.L.inv_mem_ζb).mul_right (hf _ d.L.inv_mem_GGi)))
  exact ⟨hDr.mul_right (hT 0 0),
    (hDrb.mul_right (hf _ d.L.inv_mem_GG)).mul_right ((hl0.mul_right (hT 0 0)).add_right (hT 1 0))⟩

theorem ssn_rule (h : HatHyp d) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (y : ℂ) :
    d.L.Ahat y * ssn d l = ssn d l * d.L.Ahat (y - 1) ∧ d.L.R0 y * ssn d l = ssn d l * d.L.R0 (y - 1) := by
  obtain ⟨-, -, hR, -, -, -, -⟩ := h
  obtain ⟨h1, h2⟩ := hR.2.2.2.2.1 l hl
  have hc := hR.2.2.1 l
  have := Formalism.FourierDecayAlt.P.intertwinerConjugation _ P.r d.L (d.SS l) 0 (fun x hx => (hc x (Or.inl (Or.inl hx))).symm.eq)
    (fun m => (hc _ (Or.inl (Or.inr ⟨m, rfl⟩))).symm.eq) (fun m => (hc _ (Or.inr ⟨m, rfl⟩)).symm.eq) h1 h2
    (fun x _ => by simp) (fun l => by simp) (fun l => by simp) (by simp) (by simp) y
  exact ⟨this.1, this.2.1⟩

variable [StarModule ℂ A]

theorem star_GG (h : HatHyp d) : star d.L.GG = d.L.GG := by
  obtain ⟨-, ⟨hz, -, hT⟩, -⟩ := h
  have hzb : star d.L.ζb = d.L.ζ := by rw [← hz, star_star]
  rw [d.L.GG_def, star_sub, star_mul, hz, hzb, Algebra.algebraMap_eq_smul_one, star_smul, hT, star_one]

theorem star_GGi (h : HatHyp d) : star d.L.GGi = d.L.GGi := star_inv_eq (star_GG h) d.L.GG_GGi d.L.GG_GGi

theorem star_fns (h : HatHyp d) : ∀ x ∈ d.L.fns, star x ∈ d.L.fns := by
  have hG := star_GG h
  have hGi := star_GGi h
  obtain ⟨-, ⟨hz, -, -⟩, -, -, hc, hci, -⟩ := h
  have hzi : star d.L.ζi = d.L.ζbi := star_inv_eq hz d.L.ζ_ζi d.L.ζb_ζbi
  intro x hx
  simp only [LevelData.fns, Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | (rfl | rfl | rfl | rfl | rfl | rfl))
  · rw [hc]; exact d.L.inv_mem_cb l
  · rw [hci]; exact d.L.inv_mem_cbi l
  · rw [← hc, star_star]; exact d.L.inv_mem_c l
  · rw [← hci, star_star]; exact d.L.inv_mem_ci l
  · rw [hz]; exact d.L.inv_mem_ζb
  · rw [hzi]; exact d.L.inv_mem_ζbi
  · rw [← hz, star_star]; exact d.L.inv_mem_ζ
  · rw [← hzi, star_star]; exact d.L.inv_mem_ζi
  · rw [hG]; exact d.L.inv_mem_GG
  · rw [hGi]; exact d.L.inv_mem_GGi

omit [StarModule ℂ A] in
theorem star_ssn (h : HatHyp d) (l : ℕ) : star (ssn d l) = star (d.SS l) * (d.L.Dr * d.L.Drbi) := by
  obtain ⟨-, -, -, -, hc, hci, -⟩ := h
  have h1 : star d.L.Drb = d.L.Dr := by
    unfold LevelData.Drb LevelData.Dr
    rw [star_list_prod, List.map_ofFn]
    have : (star ∘ d.L.cb) = d.L.c := funext fun m => by rw [Function.comp, ← hc, star_star]
    rw [this, rev_prod d.L]
    intro x hx; obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx; exact memF d.L (d.L.inv_mem_c m)
  have h2 : star d.L.Dri = d.L.Drbi := by
    unfold LevelData.Dri LevelData.Drbi
    rw [star_list_prod, List.map_ofFn]
    have : (star ∘ d.L.ci) = d.L.cbi := funext hci
    rw [this, rev_prod d.L]
    intro x hx; obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx; exact memF d.L (d.L.inv_mem_cbi m)
  unfold ssn
  rw [star_mul, star_mul, h1, h2, cl_comm d.L (memDrbi d.L) (memDr d.L)]

theorem star_ssn_rule (h : HatHyp d) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (y : ℂ) :
    d.L.Ahat y * star (ssn d l) = star (ssn d l) * d.L.Ahat (y + 1) ∧
      d.L.R0 y * star (ssn d l) = star (ssn d l) * d.L.R0 (y + 1) := by
  have hGi := star_GGi h
  have hF := star_fns h
  rw [star_ssn h]
  obtain ⟨-, ⟨hz, hn, -⟩, hR, hp, -, -, -⟩ := h
  obtain ⟨h1, h2⟩ := hR.2.2.2.2.1 l hl
  have hc := hR.2.2.1 l
  have hzb : star d.L.ζb = d.L.ζ := by rw [← hz, star_star]
  have hns : star d.L.nabs = d.L.nab := by rw [← hn, star_star]
  have key : ∀ x, Commute (d.SS l) (star x) → x * star (d.SS l) = star (d.SS l) * x := fun x hx => by
    have := congrArg star hx.eq
    simpa [star_mul] using this
  have hf : ∀ x ∈ d.L.fns, x * star (d.SS l) = star (d.SS l) * x :=
    fun x hx => key x (hc _ (Or.inl (Or.inl (hF x hx))))
  have hp1 : ∀ m, d.L.p m * star (d.SS l) = star (d.SS l) * d.L.p m := fun m =>
    key _ (by rw [hp]; exact (hc _ (Or.inr ⟨m, rfl⟩)).neg_right)
  have hp2 : ∀ m, d.L.pb m * star (d.SS l) = star (d.SS l) * d.L.pb m := fun m =>
    key _ (by
      have : star (d.L.pb m) = -d.L.p m := by
        have := congrArg star (hp m)
        rw [star_star, star_neg] at this
        rw [this, neg_neg]
      rw [this]; exact (hc _ (Or.inl (Or.inr ⟨m, rfl⟩))).neg_right)
  have c1 : star (d.SS l) * (d.L.GGi * d.L.ζb) = d.L.ζb * d.L.GGi * star (d.SS l) := by
    rw [← mul_assoc, ← hf _ d.L.inv_mem_GGi, mul_assoc, ← hf _ d.L.inv_mem_ζb, ← mul_assoc,
      (d.L.inv_fcomm d.L.inv_mem_GGi d.L.inv_mem_ζb).eq]
  have c2 : star (d.SS l) * (d.L.GGi * d.L.ζ) = d.L.ζ * d.L.GGi * star (d.SS l) := by
    rw [← mul_assoc, ← hf _ d.L.inv_mem_GGi, mul_assoc, ← hf _ d.L.inv_mem_ζ, ← mul_assoc,
      (d.L.inv_fcomm d.L.inv_mem_GGi d.L.inv_mem_ζ).eq]
  have e1 : d.L.nab * star (d.SS l) = star (d.SS l) * d.L.nab + d.L.ζb * d.L.GGi * star (d.SS l) := by
    have := congrArg star h2
    rw [star_mul, star_sub, star_mul, star_mul, star_mul, hns, hz, hGi] at this
    rw [← c1, this]; abel
  have e2 : d.L.nabs * star (d.SS l) = star (d.SS l) * d.L.nabs + d.L.ζ * d.L.GGi * star (d.SS l) := by
    have := congrArg star h1
    rw [star_mul, star_sub, star_mul, star_mul, star_mul, hn, hzb, hGi] at this
    rw [← c2, this]; abel
  have := Formalism.FourierDecayAlt.P.intertwinerConjugation _ P.r d.L 0 (star (d.SS l)) (fun x _ => by simp) (fun l => by simp)
    (fun l => by simp) (by simp) (by simp) hf hp1 hp2 e1 e2 y
  exact ⟨this.2.2.2.2.1, this.2.2.2.2.2.1⟩

end

theorem plus_hats_pass_generators : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (d : Q.NFData P A), HatHyp d → ∀ b ∈ bset d, ∀ y : ℂ,
      d.L.Ahat y * b ∈ nfSpan d (hats d.L) 0 0 1 ∧ d.L.R0 y * b ∈ nfSpan d (hats d.L) 0 0 1 := by
  intro P A _ _ _ _ d h b hb y
  have gen : ∀ {x}, x ∈ bset d → x ∈ bmon d := fun h => Submonoid.subset_closure h
  have mDD : d.L.D * d.L.Dbi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mDbD : d.L.Db * d.L.Di ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mζi : d.L.ζi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mζbi : d.L.ζbi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have hdrb : d.L.Drb * d.L.Di ∈ bmon d := by
    rw [drb_eq]; exact Submonoid.mul_mem _ mDbD mζbi
  have hbm := gen hb
  rcases hb with (((hb | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · refine ⟨by rw [(hat_ζi d.L y).1]; exact mem_span hbm (ahat_mem _), ?_⟩
      rw [gen_ζi_R]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      exact Submodule.add_mem _ (mem_span hbm (plusHatR_mem_hatLettersAllPoints _)) (Submodule.add_mem _
        (Submodule.smul_mem _ _ (mem_span mDbD (ahat_mem _)))
        (Submodule.smul_mem _ _ (mem_span (Submonoid.mul_mem _ (Submonoid.mul_mem _ mζi mζbi) mDbD) (ahat_mem _))))
    · exact ⟨by rw [← (hat_ζbi d.L y).1]; exact mem_span hbm (ahat_mem _),
        by rw [← (hat_ζbi d.L y).2]; exact mem_span hbm (plusHatR_mem_hatLettersAllPoints _)⟩
    · refine ⟨by rw [gen_DD_A]; exact mem_span hbm (ahat_mem _), ?_⟩
      rw [gen_DD_R]
      exact Submodule.add_mem _ (mem_span hbm (plusHatR_mem_hatLettersAllPoints _))
        (Submodule.smul_mem _ _ (mem_span (Submonoid.mul_mem _ mDD hdrb) (ahat_mem _)))
    · refine ⟨by rw [gen_DbD_A]; exact mem_span hbm (ahat_mem _), ?_⟩
      rw [gen_DbD_R]
      exact Submodule.add_mem _ (mem_span hbm (plusHatR_mem_hatLettersAllPoints _))
        (Submodule.smul_mem _ _ (mem_span (Submonoid.mul_mem _ mDbD hdrb) (ahat_mem _)))
  · exact ⟨by rw [← (kappa_comm h f y).1.eq]; exact mem_span hbm (ahat_mem _),
      by rw [← (kappa_comm h f y).2.eq]; exact mem_span hbm (plusHatR_mem_hatLettersAllPoints _)⟩
  · have hi' := Finset.mem_Icc.2 (Set.mem_Icc.1 hi)
    exact ⟨by rw [(ssn_rule h hi' y).1]; exact mem_span hbm (ahat_mem _),
      by rw [(ssn_rule h hi' y).2]; exact mem_span hbm (plusHatR_mem_hatLettersAllPoints _)⟩
  · have hi' := Finset.mem_Icc.2 (Set.mem_Icc.1 hi)
    exact ⟨by beta_reduce; rw [(star_ssn_rule h hi' y).1]; exact mem_span hbm (ahat_mem _),
      by beta_reduce; rw [(star_ssn_rule h hi' y).2]; exact mem_span hbm (plusHatR_mem_hatLettersAllPoints _)⟩

end GlobalTheory.HatNF.GenPlus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProjRaisingProjEqSmul
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.RaiseFormula

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem up_unique {j : ℕ} {a b c : M.Ty P} (h : M.Up P j a b) (h' : M.Up P j a c) : b = c := by
  funext i
  exact Fin.ext ((h i).trans (h' i).symm)

theorem up_index {l j : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) {a b : M.Ty P} (h : M.Up P l a b)
    (h' : M.Up P j a b) : j = l := by
  rw [Finset.mem_Icc] at hl
  have h1 := h ⟨l - 1, by omega⟩
  have h2 := h' ⟨l - 1, by omega⟩
  have e : l - 1 + 1 = l := by omega
  simp only [e, if_true] at h1 h2
  by_contra hne
  rw [if_neg (fun x => hne x.symm)] at h2
  omega

theorem up_ne {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) {a b : M.Ty P} (h : M.Up P l a b) : b ≠ a := by
  rw [Finset.mem_Icc] at hl
  rintro rfl
  have h1 := h ⟨l - 1, by omega⟩
  have e : l - 1 + 1 = l := by omega
  simp only [e, if_true] at h1
  omega

omit [StarRing A] in
theorem sum_proj (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) : ∑ ρ, NF.proj κ ρ = 1 := by
  unfold NF.proj
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, ← map_one κ]
  congr 1
  funext x
  simp [Finset.sum_apply]

omit [StarRing A] in
theorem kap_mul_proj (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (f : M.Ty P → ℂ) (ρ : M.Ty P) :
    κ f * NF.proj κ ρ = f ρ • NF.proj κ ρ := by
  unfold NF.proj
  rw [← map_mul, ← map_smul]
  congr 1
  funext x
  by_cases h : x = ρ <;> simp [h]

omit [StarRing A] in
theorem proj_mul_proj (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) {ρ ρ' : M.Ty P} (h : ρ' ≠ ρ) :
    NF.proj κ ρ' * NF.proj κ ρ = 0 := by
  have := kap_mul_proj κ (fun x => if x = ρ' then 1 else 0) ρ
  rw [if_neg (Ne.symm h), zero_smul] at this
  exact this

theorem proj_SS_proj (d : Q.NFData P A) (hd : d.Rel) {j : ℕ} {ρ ρ' : M.Ty P} (h : ¬ M.Up P j ρ ρ') :
    NF.proj d.κ ρ' * d.SS j * NF.proj d.κ ρ = 0 := by
  have h1 := hd.2.2.2.1 j (fun a => if M.Up P j a ρ' then 1 else 0) (fun x => if x = ρ' then 1 else 0) (by
    intro a b hab
    by_cases hb : b = ρ'
    · subst hb; simp [hab]
    · have : ¬ M.Up P j a ρ' := fun h' => hb (up_unique hab h')
      simp [hb, this])
  have h2 : NF.proj d.κ ρ' * d.SS j = _ := h1
  rw [h2, mul_assoc, kap_mul_proj, if_neg h, zero_smul, mul_zero]

theorem proj_raising_proj_eq_smul (d : Q.NFData P A) (hd : d.Rel) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (Y : ℂ)
    {ρ ρ' : M.Ty P} (h : M.Up P l ρ ρ') :
    NF.proj d.κ ρ' * d.QQ Y 1 0 * NF.proj d.κ ρ =
      M.xEx P {l} ρ Y • (NF.proj d.κ ρ' * d.SS l * NF.proj d.κ ρ) := by
  have hq : d.QQ Y 1 0 = d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y := rfl
  have hc : ∀ g ∈ d.L.fns ∪ {d.L.nab, d.L.nabs}, Commute (NF.proj d.κ ρ') g := fun g hg => hd.2.1 _ g hg
  have c1 : Commute (NF.proj d.κ ρ') d.L.GG := hc _ (by simp [LevelData.fns])
  have c2 : Commute (NF.proj d.κ ρ') d.L.GGi := hc _ (by simp [LevelData.fns])
  have c3 : Commute (NF.proj d.κ ρ') d.L.ζb := hc _ (by simp [LevelData.fns])
  have c4 : Commute (NF.proj d.κ ρ') d.L.nab := hc _ (by simp)
  have c5 : Commute (NF.proj d.κ ρ') (d.x Y) := by
    unfold NF.proj Q.NFData.x
    exact (Commute.all _ _).map d.κ
  have c6 : Commute (NF.proj d.κ ρ') (d.L.l0 Y) := by
    unfold LevelData.l0
    exact c4.neg_right.sub_right ((Algebra.commute_algebraMap_right _ _).mul_right (c3.mul_right c2))
  have c7 := (c1.mul_right c5).mul_right c6
  rw [hq, mul_add, add_mul, c7.eq, mul_assoc _ (NF.proj d.κ ρ'), proj_mul_proj _ (up_ne hl h), mul_zero, zero_add]
  unfold Q.NFData.weightedSumBis
  have key : ∀ j, NF.proj d.κ ρ' * (d.SS j * d.κ fun ρ => M.xEx P {j} ρ Y) * NF.proj d.κ ρ =
      M.xEx P {j} ρ Y • (NF.proj d.κ ρ' * d.SS j * NF.proj d.κ ρ) := by
    intro j
    rw [← mul_assoc, mul_assoc _ (d.κ _), kap_mul_proj, mul_smul_comm]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single l]
  · exact key l
  · intro j _ hj
    rw [key, proj_SS_proj d hd (fun h' => hj (up_index hl h h')), smul_zero]
  · intro h'; exact absurd hl h'

theorem xEx_ne_zero (ex : Finset ℕ) (ρ : M.Ty P) (Y : ℂ) (h : M.xC P ρ Y ≠ 0) : M.xEx P ex ρ Y ≠ 0 := by
  unfold M.xC at h
  unfold M.xEx
  rw [Finset.prod_ne_zero_iff] at h ⊢
  exact fun i hi => h i (Finset.mem_sdiff.1 hi).1

theorem ss_formula : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ Y : ℂ, (∀ ρ : M.Ty P, M.xC P ρ Y ≠ 0) → ∃ co : M.Ty P → M.Ty P → ℂ, d.SS l = ∑ ρ, ∑ ρ', co ρ ρ' • (NF.proj d.κ ρ' * d.QQ Y 1 0 * NF.proj d.κ ρ) := by
  intro P A _ _ _ _ d hd l hl Y hY
  have hr : d.Rel := hd.2.2.1
  refine ⟨fun ρ ρ' => if M.Up P l ρ ρ' then (M.xEx P {l} ρ Y)⁻¹ else 0, ?_⟩
  have h0 : d.SS l = ∑ ρ, ∑ ρ', NF.proj d.κ ρ' * d.SS l * NF.proj d.κ ρ := by
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [sum_proj, one_mul, mul_one]
  refine h0.trans (Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun ρ' _ => ?_)
  by_cases h : M.Up P l ρ ρ'
  · simp only [if_pos h]
    rw [proj_raising_proj_eq_smul d hr hl Y h, smul_smul, inv_mul_cancel₀ (xEx_ne_zero _ _ _ (hY ρ)), one_smul]
  · simp only [if_neg h]
    rw [zero_smul, proj_SS_proj d hr h]

end GlobalTheory.HatNF.RaiseFormula
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProjectorEntryValueUnderLinearFunctional
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory
private theorem qminor_cast {M : Type} [AddCommGroup M] [Module ℂ M] {n a b : ℕ} (E : Fin n → Fin n → Module.End ℂ M)
    (h : a = b) (f g : Fin b → Fin n) (u : ℂ) :
    Formalism.REAL.qminor E (fun i : Fin a => f (Fin.cast h i)) (fun i : Fin a => g (Fin.cast h i)) u
      = Formalism.REAL.qminor E f g u := by
  subst h
  rfl
end GlobalTheory

namespace GlobalTheory

theorem capelli_projector_entry_value : ∀ (M Wp : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (τ : ℝ), 1 ≤ k → Formalism.REAL.GlRel E → (∀ a b : Fin (2 * r + k + 1), a < b → ¬ (r ≤ a.val ∧ b.val ≤ r + k) → (∀ v, l (E a b v) = p a b • l v) ∧ ‖p a b‖ = (if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ) else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then τ else 0)) → ∀ (mu : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (Pop : Fin k → Fin k → Wp → Wp), Function.Injective mu → (∀ (Y : ℂ) (w : M), Formalism.REAL.qdet E (Y + ((((2 * r + k + 1) : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w) → (∀ i j v, l (E ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) j) v) = Pop i j (l v)) → (∀ (w : ℂ) (x : Wp), Formalism.FourierDecayAlt.Q.qmF Pop id id w x = (∏ i ∈ Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + (u i : ℂ))) • x) → ∀ s, ∃ c : ℂ, ‖c‖ = (if r = 0 then 1 else τ ^ 2) * ((∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i|) / ∏ t ∈ univ.erase s, |mu s - mu t|) ∧ ∀ (v : M) (y : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → M), (∀ t, splitCas E (y t) = ((-mu t + (1 - (((2 * r + k + 1) : ℕ) : ℝ)) / 2 : ℝ) : ℂ) • y t) → ∑ t, y t = Pi.single (Fin.last (2 * r + k)) v → l (y s (if r = 0 then Fin.last (2 * r + k) else 0)) = c • l v := by
  intro M Wp _ _ _ _ k r E l p τ hk hE hp mu u Pop hmu hq hP hW s
  set D : ℂ := ∏ t ∈ univ.erase s, ((mu t : ℂ) - mu s) with hD
  set N : ℂ := ∏ i ∈ Icc 1 k, (-(mu s : ℂ) + 1 / 2 + (u i : ℂ)) with hN
  have hDn : ‖D‖ = ∏ t ∈ univ.erase s, |mu s - mu t| := by
    rw [hD, norm_prod]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  have hNn : ‖N‖ = ∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i| := by
    rw [hN, norm_prod]
    refine Finset.prod_congr rfl fun t _ => ?_
    have : (-(mu s : ℂ) + 1 / 2 + (u t : ℂ)) = ((-(mu s - 1 / 2 - u t) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_neg]
  have hD0 : D ≠ 0 := by
    rw [hD, Finset.prod_ne_zero_iff]
    intro t ht h
    have h1 : mu t = mu s := by exact_mod_cast sub_eq_zero.mp h
    exact (Finset.mem_erase.mp ht).1 (hmu h1)
  have hinj : Function.Injective (fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) := by
    intro a b h
    have := congrArg Fin.val h
    simp only at this
    exact Fin.ext (by omega)
  have hblock : ∀ v, l (Formalism.REAL.qminor E (fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1)))
      (fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) (-(mu s : ℂ) + (k : ℂ) / 2) v) = N • l v := by
    intro v
    rw [_root_.GlobalTheory.qminor_block_intertwine M Wp _ k E l _ Pop hinj hP, hW, hN]
    congr 1
    refine Finset.prod_congr rfl fun t _ => ?_
    ring
  have hcof : ∀ (v : M) (y : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → M), (∀ t, splitCas E (y t) = ((-mu t + (1 - (((2 * r + k + 1) : ℕ) : ℝ)) / 2 : ℝ) : ℂ) • y t) → ∑ t, y t = Pi.single (Fin.last (2 * r + k)) v → ∀ i : Fin (2 * r + k + 1),
      D • l (y s i) = ((-1 : ℂ) ^ (i.val + (2 * r + k))) • l (Formalism.REAL.qminor E (Fin.succAbove (Fin.last (2 * r + k))) (Fin.succAbove i) (-(mu s : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) v) := by
    intro v y hy hs i
    have h := _root_.GlobalTheory.comatrix_picks_eigencomponent M (2 * r + k) E mu y hE hq hy s i
    have hj : ∀ j, ∑ t, y t j = (Pi.single (Fin.last (2 * r + k)) v : Fin (2 * r + k + 1) → M) j := by
      intro j
      rw [← hs, Finset.sum_apply]
    rw [Finset.sum_eq_single (Fin.last (2 * r + k))] at h
    · rw [hj, Pi.single_eq_same] at h
      rw [← map_smul, ← map_smul, hD, ← h]
      rfl
    · intro j _ hne
      rw [hj, Pi.single_eq_of_ne hne]
      simp
    · simp
  by_cases hr : r = 0
  · refine ⟨D⁻¹ * N, ?_, ?_⟩
    · rw [norm_mul, norm_inv, hDn, hNn, if_pos hr]; ring
    · intro v y hy hs
      rw [if_pos hr]
      have h := hcof v y hy hs (Fin.last _)
      subst hr
      have hm : Formalism.REAL.qminor E (Fin.succAbove (Fin.last (2 * 0 + k))) (Fin.succAbove (Fin.last (2 * 0 + k))) (-(mu s : ℂ) + ((2 * 0 + k : ℕ) : ℂ) / 2) = Formalism.REAL.qminor E (fun i : Fin k => (⟨0 + i.val, by omega⟩ : Fin (2 * 0 + k + 1)))
          (fun i : Fin k => (⟨0 + i.val, by omega⟩ : Fin (2 * 0 + k + 1))) (-(mu s : ℂ) + (k : ℂ) / 2) := by
        have := qminor_cast E (show k = 2 * 0 + k by omega) (Fin.succAbove (Fin.last (2 * 0 + k))) (Fin.succAbove (Fin.last (2 * 0 + k))) (-(mu s : ℂ) + (k : ℂ) / 2)
        have e : (fun i : Fin k => (⟨0 + i.val, by omega⟩ : Fin (2 * 0 + k + 1))) = fun i => Fin.succAbove (Fin.last (2 * 0 + k)) (Fin.cast (show k = 2 * 0 + k by omega) i) := by
          funext i
          apply Fin.ext
          simp
        rw [e, this]
        simp
      rw [hm, hblock] at h
      have hs1 : ((-1 : ℂ) ^ ((Fin.last (2 * 0 + k)).val + (2 * 0 + k))) = 1 := by
        rw [Fin.val_last, ← two_mul, pow_mul]; simp
      rw [hs1, one_smul] at h
      rw [mul_smul, ← h, smul_smul, inv_mul_cancel₀ hD0, one_smul]
  · have hr1 : 1 ≤ r := by omega
    obtain ⟨c1, hc1, h1⟩ := _root_.GlobalTheory.RowChain.chain_rows M Wp k r E l p τ hk hE hp hr1
    obtain ⟨c2, hc2, h2⟩ := _root_.GlobalTheory.qminor_column_chain M Wp k r E l p τ hk hE hp hr1
    refine ⟨D⁻¹ * ((-1 : ℂ) ^ (2 * r + k) * (c1 * (c2 * N))), ?_, ?_⟩
    · rw [norm_mul, norm_inv, norm_mul, norm_mul, norm_mul, hDn, hNn, if_neg hr, hc1, hc2, norm_pow]
      simp only [norm_neg, norm_one, one_pow]
      ring
    · intro v y hy hs
      rw [if_neg hr]
      have h := hcof v y hy hs 0
      have e : (-(mu s : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) - (r : ℂ) = -(mu s : ℂ) + (k : ℂ) / 2 := by
        push_cast; ring
      rw [h1, h2, e, hblock, Fin.val_zero, zero_add] at h
      rw [mul_smul, mul_smul, mul_smul, mul_smul, ← h, smul_smul, inv_mul_cancel₀ hD0, one_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirStdEigenvalue
section
open Formalism.REAL

namespace GlobalTheory

theorem splitCasimirStd_eigenvalue : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (m : Fin (n + 1) → ℂ), GlRel E → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ w v, qdet E w v = (∏ j, (w + m j)) • v) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → ∀ (lam : ℂ) (x : (PiLp 2 (fun _ : Fin (n + 1) => V))), x ≠ 0 → Om x = lam • x → ∃ j, lam = m j + 0 := by
  intro V _ _ _ n E Et Om m hE hadj hq hEt hOm lam x hx hlam
  obtain ⟨K, hK, -⟩ := GlobalTheory.T.capelli_comatrix_last_row_inverts_casimir V n E Om m hE hq hOm
  obtain ⟨-, -, -, hc⟩ := tensorStd_rel_adjoint_splitCasimir V n E Et Om hE hadj hEt hOm
  by_contra hne
  have hprod : (∏ j, (-lam + m j)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun j _ h => hne ⟨j, ?_⟩
    linear_combination -h
  have hlast : ∀ y, Om y = lam • y → y (Fin.last n) = 0 := by
    intro y hy
    have h := hK (-lam) y
    rw [hy, sub_zero, neg_smul, neg_add_cancel, map_zero] at h
    exact (smul_eq_zero.1 h.symm).resolve_left hprod
  apply hx
  refine PiLp.ext fun c => ?_
  have h1 : Om (Et (Fin.last n) c x) = lam • Et (Fin.last n) c x := by
    have h := LinearMap.congr_fun (hc (Fin.last n) c) x
    simp only [Module.End.mul_apply] at h
    rw [h, hlam, map_smul]
  have h2 := hlast _ h1
  rw [hEt, hlast x hlam] at h2
  simpa using h2

end GlobalTheory
end

