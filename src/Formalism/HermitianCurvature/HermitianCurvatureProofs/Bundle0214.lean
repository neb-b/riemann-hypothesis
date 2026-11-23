module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0093
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0201
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0203

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RootVectorActionCutoff
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN.MC

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2

section alg

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)}

def cI (p : Fin (2 * r + k + 1)) : Fin (mdim k r 0) := ⟨p.val, by have := p.isLt; simp [mdim]; omega⟩

theorem posL_cI (p : Fin (2 * r + k + 1)) : posL k r 0 (cI p) = p := Fin.ext (by simp [posL, cI])

theorem cI_inj : Function.Injective (cI (k := k) (r := r)) := fun p q h => Fin.ext (by
  have := congrArg Fin.val h; simpa [cI] using this)


variable (E) in
abbrev SA (hD : IsOpen D) : Subalgebra ℂ (Module.End ℂ (VS k r 0 D E)) :=
  Algebra.adjoin ℂ (Set.range fun p : Fin (mdim k r 0) × Fin (mdim k r 0) => Eh (E := E) (i := 0) hD p.1 p.2)

def EA (hD : IsOpen D) (p q : Fin (2 * r + k + 1)) : SA E hD :=
  ⟨Eh hD (cI p) (cI q), Algebra.subset_adjoin ⟨(cI p, cI q), rfl⟩⟩

theorem EA_val (hD : IsOpen D) (p q : Fin (2 * r + k + 1)) : (EA (E := E) hD p q : Module.End ℂ (VS k r 0 D E)) =
    Eh hD (cI p) (cI q) := rfl

theorem EA_gl (hD : IsOpen D) : GlRel (EA (E := E) hD) := by
  intro a b c d
  apply Subtype.ext
  have h := Eh_gl (E := E) (i := 0) hD (cI a) (cI b) (cI c) (cI d)
  simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, EA_val]
  rw [h]
  congr 1
  · by_cases hbc : b = c
    · rw [if_pos (congrArg cI hbc), if_pos hbc]; rfl
    · rw [if_neg (fun e => hbc (cI_inj e)), if_neg hbc]; rfl
  · by_cases hda : d = a
    · rw [if_pos (congrArg cI hda), if_pos hda]; rfl
    · rw [if_neg (fun e => hda (cI_inj e)), if_neg hda]; rfl

def La (hD : IsOpen D) (v : VS k r 0 D E) (g : Mx k r) : SA E hD →ₗ[ℂ] E where
  toFun x := ((x : Module.End ℂ (VS k r 0 D E)) v : Mx k r → E) g
  map_add' x y := by simp
  map_smul' c x := by simp

theorem La_apply (hD : IsOpen D) (v : VS k r 0 D E) (g : Mx k r) (x : SA E hD) :
    La hD v g x = ((x : Module.End ℂ (VS k r 0 D E)) v : Mx k r → E) g := rfl

theorem leftEq_SA (hD : IsOpen D) (z : Fin (2 * r + k + 1) → ℂ)
    (hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D) (x : SA E hD) :
    ∀ v : VS k r 0 D E, LeftEq k r z 0 D (v : Mx k r → E) →
      LeftEq k r z 0 D ((x : Module.End ℂ (VS k r 0 D E)) v : Mx k r → E) := by
  obtain ⟨x, hx⟩ := x
  show ∀ v : VS k r 0 D E, LeftEq k r z 0 D (v : Mx k r → E) → LeftEq k r z 0 D (x v : Mx k r → E)
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨p, rfl⟩ := hy
    intro v hv g hg n hn
    have hng : n * g ∈ Glev k r 0 ∩ D := ⟨Formalism.FourierDecayAlt.P.Qx3.glev_mul hn.2 hg.1, hN g hg n hn⟩
    rw [ev_E hD p.1 p.2 v hng, ev_E hD p.1 p.2 v hg]
    exact ((generator_action_preserved E k r z 0 D p.1 p.2 (v : Mx k r → E) (v : Mx k r → E) 1 hD v.2.1 v.2.1).2.1 hN hv) g hg n hn
  | algebraMap c =>
    intro v hv g hg n hn
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hv g hg n hn, smul_comm]
  | add y₁ y₂ _ _ h₁ h₂ =>
    intro v hv g hg n hn
    simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
    rw [h₁ v hv g hg n hn, h₂ v hv g hg n hn, smul_add]
  | mul y₁ y₂ _ _ h₁ h₂ =>
    intro v hv
    exact h₁ _ (h₂ v hv)

abbrev Tor (hD : IsOpen D) (j : ℕ) : Subalgebra ℂ (SA E hD) :=
  Algebra.adjoin ℂ {x | ∃ l : Fin r, j ≤ l.val ∧ x = EA hD (eI k r l) (eI k r l)}

theorem comm_Tor (hD : IsOpen D) (j : ℕ) (p q : Fin (2 * r + k + 1))
    (hp : ∀ l : Fin r, j ≤ l.val → p ≠ eI k r l) (hq : ∀ l : Fin r, j ≤ l.val → q ≠ eI k r l) (P : SA E hD)
    (hP : P ∈ Tor hD j) : Commute (EA hD p q) P := by
  induction hP using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    have h := EA_gl (E := E) hD p q (eI k r l) (eI k r l)
    rw [if_neg (hq l hl), if_neg (fun e => hp l hl e.symm), sub_zero] at h
    exact sub_eq_zero.1 h
  | algebraMap c => exact Algebra.commute_algebraMap_right c _
  | add y₁ y₂ _ _ h₁ h₂ => exact h₁.add_right h₂
  | mul y₁ y₂ _ _ h₁ h₂ => exact h₁.mul_right h₂

theorem Tor_mono (hD : IsOpen D) {j j' : ℕ} (h : j ≤ j') : Tor (E := E) hD j' ≤ Tor hD j :=
  Algebra.adjoin_mono fun _ ⟨l, hl, e⟩ => ⟨l, h.trans hl, e⟩

theorem EA_mem_Tor (hD : IsOpen D) (l : Fin r) {j : ℕ} (h : j ≤ l.val) :
    EA (E := E) hD (eI k r l) (eI k r l) ∈ Tor hD j :=
  Algebra.subset_adjoin ⟨l, h, rfl⟩

end alg

section qm

theorem map_qminor {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B) {n t : ℕ}
    (E : Fin n → Fin n → A) (a b : Fin t → Fin n) (u : ℂ) :
    φ (qminor E a b u) = qminor (fun p q => φ (E p q)) a b u := by
  unfold qminor
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 2
  congr 1
  congr 1
  funext k
  simp only [Function.comp_apply, Tm, map_add]
  split_ifs <;> simp

theorem qminor_reindex {A : Type} [Ring A] [Algebra ℂ A] {n n' t : ℕ} (E : Fin n' → Fin n' → A) (ι : Fin n → Fin n')
    (hι : Function.Injective ι) (a b : Fin t → Fin n) (u : ℂ) :
    qminor (fun p q => E (ι p) (ι q)) a b u = qminor E (ι ∘ a) (ι ∘ b) u := by
  unfold qminor
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 2
  congr 1
  congr 1
  funext l
  simp only [Tm, Function.comp_apply]
  by_cases h : a (σ l) = b l
  · rw [if_pos h, if_pos (congrArg ι h)]
  · rw [if_neg h, if_neg (fun e => h (hι e))]

end qm

section main

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} (hD : IsOpen D)

theorem gauge_last (c : Fin r → ℂ) :
    (∏ a : Fin r, (if a.val < (Fin.last r).val then ‖c a‖ ^ (Mdim k r a - 1) else 1)) =
      ∏ a : Fin r, ‖c a‖ ^ (Mdim k r a - 1) :=
  Finset.prod_congr rfl fun a _ => if_pos a.isLt

theorem resG_last (J : Mx k r → E) (c : Fin r → ℂ) (g : Mx k r) :
    Q.resG k r (Fin.last r) J c g = ((∏ a : Fin r, ‖c a‖ ^ (Mdim k r a - 1) : ℝ) : ℂ) • J (wCell k r (Fin.last r) c * g) := by
  unfold Q.resG
  rw [gauge_last]

theorem root_vector_action_cutoff (z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') (hRR : RightRuleE) {f : Mx k r → E}
    (hf : SmoothLev k r 0 D f) (hRf : RightEq k r z' 0 D f) (a b : Fin r) (hab : a.val < b.val) :
    ((EA hD (eI k r a) (eI k r b) : SA E hD) : Module.End ℂ (VS k r 0 D E)) ⟨cut k r 0 D f, cut_mem hD hf⟩ =
      (if b.val = a.val + 1 then (1 : ℂ) else 0) • ⟨cut k r 0 D f, cut_mem hD hf⟩ := by
  apply Subtype.ext
  funext g
  by_cases hg : g ∈ Glev k r 0 ∩ D
  · rw [EA_val, ev_E hD _ _ _ hg]
    have hloc := (good_eh (E := E) hD (cI (eI k r a)) (cI (eI k r b))).loc (cut k r 0 D f) f
      (fun x hx => cut_of_mem f hx) g hg
    simp only [posL_cI] at hloc
    rw [posL_cI, posL_cI]
    show EH k r (eI k r a) (eI k r b) (cut k r 0 D f) g = (if b.val = a.val + 1 then (1 : ℂ) else 0) • cut k r 0 D f g
    rw [hloc, hRR E k r z' D f hz' hD hf hRf g hg a b hab, cut_of_mem f hg]
  · show ((Eh hD (cI (eI k r a)) (cI (eI k r b)) ⟨cut k r 0 D f, cut_mem hD hf⟩ : VS k r 0 D E) : Mx k r → E) g =
      (if b.val = a.val + 1 then (1 : ℂ) else 0) • cut k r 0 D f g
    rw [(Eh hD (cI (eI k r a)) (cI (eI k r b)) ⟨cut k r 0 D f, cut_mem hD hf⟩).2.2 g hg,
      show cut k r 0 D f g = 0 from Set.indicator_of_notMem hg f, smul_zero]

end main

end Formalism.FourierDecayAlt.P.PBN.MC
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ToStdAppendBlk
section
namespace Formalism.FourierDecayAlt.P.LiftDegreeLemmas

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField Formalism.FourierDecayAlt.P.PBL
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem toStd_append_blk (r : ℕ) (g : ℝ) (s : ℕ) (c : ℂ) : ∀ (h : C.LPt) (b : ℕ),
    D.toStd r g b (h ++ [(s, c)]) = D.toStd r g b h ++
      [(s, (((g / (2 * Real.pi)) ^ S6.nuBlock r ((b + D.ptSize h : ℕ) : ℤ) (s : ℤ) : ℝ) : ℂ) *
        Complex.I ^ (s - 1) * c)] := by
  intro h b
  induction h generalizing b with
  | nil => simp [D.toStd, D.ptSize]
  | cons blk rest ih =>
    obtain ⟨s', t⟩ := blk
    simp only [List.cons_append, D.toStd, ih (b + s'), D.ptSize, List.map_cons,
      List.sum_cons, add_assoc]

theorem slv_congr {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (T : D.LevTower k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (i : ℕ) (hi : i ≤ r)
    (w : List C.Letter) {P P' : C.LPt} (e : P = P') (hP : D.ptSize P = i) (hP' : D.ptSize P' = i) :
    KB.slv T F i hi w P hP = KB.slv T F i hi w P' hP' := by
  subst e; rfl

theorem psd_shift {Y : Finset C.LPt} {k : C.LPt → C.LPt → ℂ} (blk : ℕ × ℂ)
    (hk : TB.PSDOn (Y.image fun h => h ++ [blk]) k) : TB.PSDOn Y fun p q => k (p ++ [blk]) (q ++ [blk]) := by
  have hinj : Set.InjOn (fun h : C.LPt => h ++ [blk]) Y := fun x _ y _ hxy => List.append_cancel_right hxy
  rw [PBA.psd_iff_qf] at hk ⊢
  obtain ⟨hh, hq⟩ := hk
  refine ⟨fun x hx y hy => hh _ (Finset.mem_image_of_mem _ hx) _ (Finset.mem_image_of_mem _ hy), fun c => ?_⟩
  have e : PBA.qf Y (fun p q => k (p ++ [blk]) (q ++ [blk])) c =
      PBA.qf (Y.image fun h => h ++ [blk]) k (fun z => c z.dropLast) := by
    unfold PBA.qf
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp
  rw [e]; exact hq _

section lam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def lamB (S : C.HidaSetting E Wp Wq) (b s : ℕ) : ℂ :=
  ((((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r (b : ℤ) (s : ℤ) : ℝ) : ℂ) * Complex.I ^ (s - 1)

theorem stdS_blk (S : C.HidaSetting E Wp Wq) (b s : ℕ) (hb : 1 ≤ b) (H : C.LPt) (hH : D.ptSize H = b - 1) (t : ℂ) :
    stdS S (H ++ [(s, t)]) = stdS S H ++ [(s, lamB S b s * t)] := by
  unfold stdS lamB
  rw [toStd_append_blk, hH, show 1 + (b - 1) = b by omega]

theorem norm_lamB (S : C.HidaSetting E Wp Wq) (hg : (0 : ℝ) < S.g) (b s : ℕ) :
    ‖lamB S b s‖ = ((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r (b : ℤ) (s : ℤ) := by
  unfold lamB
  rw [norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, Complex.norm_real, Real.norm_of_nonneg]
  exact zpow_nonneg (by positivity) _

theorem lamB_ne (S : C.HidaSetting E Wp Wq) (hg : (0 : ℝ) < S.g) (b s : ℕ) : lamB S b s ≠ 0 := by
  intro h
  have := norm_lamB S hg b s
  rw [h, norm_zero] at this
  exact (zpow_pos (by positivity : (0 : ℝ) < (S.g : ℝ) / (2 * Real.pi)) _).ne this

end lam

section deg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem uB_blk (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (b s : ℕ) (hb : 1 ≤ b) (H : C.LPt) (hH : D.ptSize H = b - 1) (t : ℂ)
    (hP : D.IsLocPt (H ++ [(s, t)]) j) :
    ∃ hX : D.IsLocPt (stdS S H ++ [(s, lamB S b s * t)]) j,
      uB S p F v ε j hj w (H ++ [(s, t)]) = (((√(nnS S (H ++ [(s, t)])) / bS S (H ++ [(s, t)]) : ℝ) : ℂ)) •
        KB.slv (p v).T (F v ε) j hj w (stdS S H ++ [(s, lamB S b s * t)]) hX.2 := by
  have hgpos := g_pos_of_built hB
  have e := stdS_blk S b s hb H hH t
  have hX : D.IsLocPt (stdS S H ++ [(s, lamB S b s * t)]) j := by
    rw [← e]; exact (PBD.isLocPt_toStd_iff _ _ hgpos _ 1 j).2 hP
  refine ⟨hX, ?_⟩
  rw [uB_pos S p F v ε j hj w _ hP]
  congr 1
  exact slv_congr _ _ _ _ _ e _ _

theorem deg_uB_lift (hDL : KB.DegLift) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (b s : ℕ) (hb : 1 ≤ b) (a : List C.Letter) (K : ℕ)
    (grid : Fin K → Fin (2 * (j - s) + s + 1) → ℝ) (hinj : ∀ c, Function.Injective (grid c))
    (H H' : C.LPt) (hH : D.ptSize H = b - 1) (hH' : D.ptSize H' = b - 1) (t t' : ℂ) :
    ((-1) ^ (s - 1) * ((lamB S b s * t)⁻¹ - (lamB S b s * t')⁻¹)) ^ K *
        (p v).form j hj a (uB S p F v ε j hj a (H ++ [(s, t)])) (uB S p F v ε j hj a (H' ++ [(s, t')])) =
      ∑ n : Fin K → Fin (2 * (j - s) + s + 1), ((∏ c, F7.lagCo (grid c) (n c) : ℝ) : ℂ) *
        KB.pairJ ((p v).form j hj a) (List.ofFn fun c => grid c (n c))
          (uB S p F v ε j hj (KB.plusW (List.ofFn fun c => grid c (n c)) a) (H ++ [(s, t)]))
          (uB S p F v ε j hj (KB.minusW (List.ofFn fun c => grid c (n c)) a) (H' ++ [(s, t')])) := by
  by_cases hloc : D.IsLocPt (H ++ [(s, t)]) j ∧ D.IsLocPt (H' ++ [(s, t')]) j
  · obtain ⟨hP, hP'⟩ := hloc
    obtain ⟨hX, eX⟩ := uB_blk hB F v ε j hj a b s hb H hH t hP
    obtain ⟨hX', eX'⟩ := uB_blk hB F v ε j hj a b s hb H' hH' t' hP'
    have hdeg := hDL (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (F v ε) j s hj a (stdS S H) (stdS S H')
      (lamB S b s * t) (lamB S b s * t') hX hX' K grid (hF v ε hε) hinj
    rw [rr_eq_form (p v) (F v ε) j hj a _ _ hX hX'] at hdeg
    set Dh : ℂ := (((√(nnS S (H ++ [(s, t)])) / bS S (H ++ [(s, t)]) : ℝ) : ℂ)) with hDh
    set Dh' : ℂ := (((√(nnS S (H' ++ [(s, t')])) / bS S (H' ++ [(s, t')]) : ℝ) : ℂ)) with hDh'
    obtain ⟨ε2, hε2, hs, hs'⟩ := nv_pair (slv_nv (p v) (hF v ε hε) j hj a _ hX)
      (slv_nv (p v) (hF v ε hε) j hj a _ hX')
    rw [eX, eX', form_smul_l (p v) j hj a _ _ _ hs (nv_smul _ hs'), form_smul_r (p v) j hj a _ _ _ hs hs']
    have hL : ((-1) ^ (s - 1) * ((lamB S b s * t)⁻¹ - (lamB S b s * t')⁻¹)) ^ K *
        (Dh * (conj Dh' * (p v).form j hj a (KB.slv (p v).T (F v ε) j hj a _ hX.2)
          (KB.slv (p v).T (F v ε) j hj a _ hX'.2))) =
        Dh * conj Dh' * (((-1) ^ (s - 1) * ((lamB S b s * t)⁻¹ - (lamB S b s * t')⁻¹)) ^ K *
          (p v).form j hj a (KB.slv (p v).T (F v ε) j hj a _ hX.2) (KB.slv (p v).T (F v ε) j hj a _ hX'.2)) := by
      ring
    rw [hL, hdeg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    set ys := List.ofFn fun c => grid c (n c) with hys
    obtain ⟨hXp, eXp⟩ := uB_blk hB F v ε j hj (KB.plusW ys a) b s hb H hH t hP
    obtain ⟨hXm, eXm⟩ := uB_blk hB F v ε j hj (KB.minusW ys a) b s hb H' hH' t' hP'
    obtain ⟨ε3, hε3, hp, hm⟩ := nv_pair (slv_nv (p v) (hF v ε hε) j hj (KB.plusW ys a) _ hX)
      (slv_nv (p v) (hF v ε hε) j hj (KB.minusW ys a) _ hX')
    rw [eXp, eXm, pj_smul (p v) j hj a ys _ _ _ _ hp hm]
    ring
  · have h0 : ∀ w : List C.Letter, uB S p F v ε j hj w (H ++ [(s, t)]) = 0 ∨
        uB S p F v ε j hj w (H' ++ [(s, t')]) = 0 := by
      intro w
      by_cases hh : D.IsLocPt (H ++ [(s, t)]) j
      · exact Or.inr (uB_neg S p F v ε j hj w _ fun hh' => hloc ⟨hh, hh'⟩)
      · exact Or.inl (uB_neg S p F v ε j hj w _ hh)
    obtain ⟨ε1, hε1, hx, hx'⟩ := nv_pair (uB_nv hB F hF v ε hε j hj a (H ++ [(s, t)]))
      (uB_nv hB F hF v ε hε j hj a (H' ++ [(s, t')]))
    have lhs0 : (p v).form j hj a (uB S p F v ε j hj a (H ++ [(s, t)])) (uB S p F v ε j hj a (H' ++ [(s, t')])) = 0 := by
      rcases h0 a with h0 | h0
      · rw [h0, form_zero_l (p v) j hj a _ hx']
      · rw [h0, form_zero_r (p v) j hj a _ hx]
    rw [lhs0, mul_zero]
    symm
    refine Finset.sum_eq_zero fun n _ => ?_
    set ys := List.ofFn fun c => grid c (n c) with hys
    obtain ⟨ε3, hε3, hp, hm⟩ := nv_pair (uB_nv hB F hF v ε hε j hj (KB.plusW ys a) (H ++ [(s, t)]))
      (uB_nv hB F hF v ε hε j hj (KB.minusW ys a) (H' ++ [(s, t')]))
    by_cases hh : D.IsLocPt (H ++ [(s, t)]) j
    · rw [uB_neg S p F v ε j hj (KB.minusW ys a) _ fun hh' => hloc ⟨hh, hh'⟩, pj_zero_r (p v) j hj a ys _ hp, mul_zero]
    · rw [uB_neg S p F v ε j hj (KB.plusW ys a) _ hh, pj_zero_l (p v) j hj a ys _ hm, mul_zero]

end deg

end

end Formalism.FourierDecayAlt.P.LiftDegreeLemmas
end

