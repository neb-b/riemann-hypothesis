module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BasePointMemDomain
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0232
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0185
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0106
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0233
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0194
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0200
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0031
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0227
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0215
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0197
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0216
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0165

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ActOneVariableSmul
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem act_one_variable_smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Type} [Fintype S] [DecidableEq S]
    (M : Wd.SlopeTestRemainingChoices S (Pr (V1 E))) (s : ℂ) (x : Wd.Ix S → V1 E) :
    act1 M (fun b => s • x b) = fun e => s • act1 M x e := by
  funext e
  simp only [act1, map_smul, Finset.smul_sum]

theorem kapM_eq (P : M.Par) (j : ℕ) : kapM (P.r - j) P.k = kapJ P j := by
  unfold kapM kapJ
  push_cast
  ring

theorem headPic_of (hJ : HeadJ) : HeadPic := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh X μ L st Φ hD hF hw hΦ t ht e y hy
  have ht0 : t ≠ 0 := (ht.1 (1, t) (List.mem_append_right _ (List.mem_singleton_self _))).2
  have hn : 1 + (P.r - (j + 1)) = P.r - j := by omega
  have hc : y.1 ∈ OmX (P.r - (j + 1)) := hy.1
  have hdom := fun τ (hτ : τ ≠ 0) => base_point_mem_domain hn (PBH.levTower_bs_z_eq_castV_liftVec p.T j hj) (PBH.levTower_bs_z'_eq_castV_liftVec p.T j hj) hy hτ
  have hL : IsActualLevel X L := hD.2.2.1

  set gg : ℝ := ∏ a : Fin (P.r - (j + 1)),
    (if a.val < (Fin.last (P.r - (j + 1))).val then ‖y.1 a‖ ^ (Mdim P.k (P.r - (j + 1)) a - 1) else 1) with hgg
  have hgg0 : gg ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => by
    split_ifs
    · exact pow_ne_zero _ (norm_ne_zero_iff.2 (hc a))
    · exact one_ne_zero
  set γ := wCell P.k (P.r - (j + 1)) (Fin.last _) y.1 * y.2 with hγdef
  have hγ : γ ∈ B.GV P.k (P.r - (j + 1)) := Formalism.FourierDecayAlt.P.PBF.wCell_mul_GV hc hy.2.1
  have hΩ : γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' :=
    Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus (p.T.bs (j + 1)).z_mem (p.T.bs (j + 1)).z'_mem hy.1 hy.2.1 hy.2.2

  let Rd := rdL (k := P.k) (π := (p.T.bs j).π) (π' := (p.T.bs j).π') hn y hdom
  let φ : Wd.Ix (Fin w.length) → V1 (Wq →L[ℂ] Wp) := fun b => (((gg⁻¹ : ℝ)) : ℂ) • Rd (Φ b)
  have hφ : ∀ b τ, τ ≠ 0 → (φ b).1 τ =
      B.JF (p.T.bs j) (KB.slv p.T F j (by omega) w h hh.2 b) (mLev P j hj τ γ) := by
    intro b τ hτ
    have hr := pic_read (k := P.k) hn (PBH.levTower_bs_z_eq_castV_liftVec p.T j hj) (PBH.levTower_bs_z'_eq_castV_liftVec p.T j hj)
      (Subtype.val (Φ b)) (B.JF (p.T.bs j) (KB.slv p.T F j (by omega) w h hh.2 b)) (hΦ b) hτ y hy
    have hraw := raw_eq hn y hdom (Φ b) hτ
    change (((gg⁻¹ : ℝ)) : ℂ) • (Rd (Φ b)).1 τ = _
    have hpos : ‖τ‖ ^ (2 * (P.r - j) + P.k) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hτ)
    have hR : (Rd (Φ b)).1 τ = Q.resG P.k (P.r - (j + 1)) (Fin.last _)
        (fun γ' => B.JF (p.T.bs j) (KB.slv p.T F j (by omega) w h hh.2 b)
          (D.castM hn (U.mMap P.k 1 (P.r - (j + 1)) (Matrix.of fun _ _ => τ) γ'))) y.1 y.2 := by
      have h2 := hraw.symm.trans hr
      have h3 := congrArg (fun v => (((‖τ‖ ^ (2 * (P.r - j) + P.k))⁻¹ : ℝ) : ℂ) • v) h2
      simp only [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hpos, Complex.ofReal_one, one_smul] at h3
      exact h3
    rw [hR]
    unfold resG
    rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hgg0, Complex.ofReal_one, one_smul]
    rfl
  have hRφ : (fun b => Rd (Φ b)) = fun b => ((gg : ℝ) : ℂ) • φ b := by
    funext b
    simp only [φ, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hgg0, Complex.ofReal_one, one_smul]
  have hJe := hJ Wp Wq P p F j hj w h hh γ hF hw hγ hΩ φ hφ t ht e

  have hraw := raw_eq hn y hdom (P5.act (P5.bTl L ⟨0, by change 0 < P.r - j; omega⟩ (D.positionted w)) Φ e) ht0
  have hact := rd_act hn y hc hdom X hL (D.positionted w) Φ e
  refine hraw.trans ?_
  change ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) • (Rd (P5.act _ Φ e)).1 t = _
  rw [hact, hRφ]
  unfold oneBT
  rw [act_one_variable_smul, kapM_eq]
  change ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) • (((gg : ℝ) : ℂ) • (oneBT (kapJ P j) (D.positionted w) φ e).1 t) = _
  rw [← hJe]
  congr 1

end Formalism.FourierDecayAlt.P.PBP

namespace Formalism.FourierDecayAlt.P

theorem pb_radHead_of_headJ (hJ : LevelPointCoordinates.HeadJ) : KB.RadHead := pb_radHead_of_headPic (PBP.headPic_of hJ)

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockKWaveC
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section C2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem blockK_waveC (hA : P5.ThmPActualCpt) (hPSC : StandardPairingDecay.PStdC) (hDW : KB.DegWave) (hSS : KB.SizeStdCpt)
    (hVI : KB.VIsoCpt) (hFP : FormPosCpt) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (a : List C.Letter) (ha : D.AdmAt S v a) (haN : a.length ≤ S.Ntop)
    (hwa : KB.CutWord (D.parOf S v) (S.l + 1) a) (K : ℕ) (grid : Fin K → Fin (2 * j + 1) → ℝ)
    (hinj : ∀ b, Function.Injective (grid b))
    (hnodes : ∀ n : Fin K → Fin (2 * j + 1),
        D.AdmAt S v (KB.plusW (List.ofFn fun b => grid b (n b)) a) ∧
        D.AdmAt S v (KB.minusW (List.ofFn fun b => grid b (n b)) a) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW (List.ofFn fun b => grid b (n b)) a) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.minusW (List.ofFn fun b => grid b (n b)) a) ∧
        (List.ofFn fun b => grid b (n b)).Pairwise (fun y y' => 2 < |y - y'|) ∧
        ∀ y ∈ (List.ofFn fun b => grid b (n b)), NodeOK S v a (decide (j = 0)) y)
    (Xc : ℝ) (hXc0 : 0 ≤ Xc)
    (hXc : (∏ b, ∑ i, |F7.lagCo (grid b) i|) * (((S.g : ℝ) * lamS S j) / (2 * Real.pi)) ^ K *
      (Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l (decide (j = 0)) (S.pl v)) ^ K ≤ Xc ^ K)
    (l : ℂ) (Y : Finset C.LPt) (hY : ∀ h ∈ Y, D.ptSize h = j) :
    KB.BlockPSD Y Y
      (fun p' q' => ((Xc ^ K : ℝ) : ℂ) * ∑ n : Fin K → Fin (2 * j + 1), (F7.thGrid grid n : ℂ) *
        KB.gN (setC S p F) v ε j (KB.plusW (List.ofFn fun b => grid b (n b)) a) p' q')
      (fun p' q' => Complex.I ^ K * l ^ K * KB.hatB (setC S p F) v ε (j + 1) 1 a l p' q')
      (fun p' q' => ((Xc ^ K : ℝ) : ℂ) * ∑ n : Fin K → Fin (2 * j + 1), (F7.thGrid grid n : ℂ) *
        KB.gN (setC S p F) v ε j (KB.minusW (List.ofFn fun b => grid b (n b)) a) p' q') := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGo, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -, -, -, -⟩ := hv v
  have hgpos := g_pos_of_built hB
  have hlam := lamS_pos S hgpos j
  have hΓ := gam_pos hB j
  have hsa := sizeAt_pos S hGo v a ha
  set T : ℝ := ((S.g : ℝ) * lamS S j) / (2 * Real.pi) with hT
  have hT0 : 0 < T := by positivity
  set t : ℝ := 2 * Real.pi / ((S.g : ℝ) * lamS S j) with ht
  have htT : t * T = 1 := by rw [ht, hT]; field_simp
  set s := sW S j l with hs
  set c0 : ℝ := 1 / (ΓS S j * S.sizeAt v a) with hc0
  set ys : (Fin K → Fin (2 * j + 1)) → List ℝ := fun n => List.ofFn fun b => grid b (n b) with hys
  set Λ : ℝ := ∏ b, ∑ i, |F7.lagCo (grid b) i| with hΛ
  set θ : (Fin K → Fin (2 * j + 1)) → ℝ := fun n => F7.thGrid grid n with hθ
  set lag : (Fin K → Fin (2 * j + 1)) → ℝ := fun n => ∏ b, F7.lagCo (grid b) (n b) with hlag
  set S' := setC S p F with hS'

  set Pn : (Fin K → Fin (2 * j + 1)) → C.LPt → C.LPt → ℂ := fun n p' q' =>
    (((lag n / θ n) * T ^ K * c0 : ℝ) : ℂ) * KB.pairJ ((p v).form j hj a) (ys n)
      (KB.waveG ((p v).T.bs j) s _ (uY S p F v ε j hj (KB.plusW (ys n) a) Y p'))
      (uY S p F v ε j hj (KB.minusW (ys n) a) Y q') with hPn
  have hCS : ∀ n (c d : C.LPt → ℂ), ‖∑ p' ∈ Y, ∑ q' ∈ Y, c p' * conj (d q') * Pn n p' q'‖ ^ 2 ≤
      (Xc ^ K) ^ 2 * ((∑ p' ∈ Y, ∑ p'' ∈ Y, c p' * conj (c p'') * KB.gN S' v ε j (KB.plusW (ys n) a) p' p'').re *
        (∑ q' ∈ Y, ∑ q'' ∈ Y, d q' * conj (d q'') * KB.gN S' v ε j (KB.minusW (ys n) a) q' q'').re) := by
    intro n c d
    obtain ⟨hAp, hAm, hCp, hCm, hpw, hnd⟩ := hnodes n
    have hCp' : KB.CutWord (D.parOf S v) (p v).l0 (KB.plusW (ys n) a) := by rw [hl0]; exact hCp
    have hCm' : KB.CutWord (D.parOf S v) (p v).l0 (KB.minusW (ys n) a) := by rw [hl0]; exact hCm
    obtain ⟨hqpos, hcs⟩ := hSS hA (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) j hj a (ys n) hCp' hCm' hpw
    set qv : ℝ → ℝ := fun y => (Wd.qw (M.qC (D.parOf S v)) (D.positionted a) (y : ℂ)).re with hqv
    set Q : ℝ := ((ys n).map qv).prod with hQd
    have hQ : 0 < Q := List.prod_pos fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact hqpos y hy
    have hsp := sizeAt_pos S hGo v _ hAp
    have hsm := sizeAt_pos S hGo v _ hAm
    set cp : ℝ := 1 / (ΓS S j * S.sizeAt v (KB.plusW (ys n) a)) with hcp
    set cm : ℝ := 1 / (ΓS S j * S.sizeAt v (KB.minusW (ys n) a)) with hcm
    have hcp0 : 0 < cp := by positivity
    have hcm0 : 0 < cm := by positivity
    set κ : ℂ := (((lag n / θ n) * T ^ K * c0 : ℝ) : ℂ) with hκ
    have hc := cs_choice (CV ((p v).T.bs j) (S := Fin (KB.plusW (ys n) a).length))
      (CV ((p v).T.bs j) (S := Fin (KB.minusW (ys n) a).length))
      ((p v).form j hj (KB.plusW (ys n) a)) ((p v).form j hj (KB.minusW (ys n) a))
      (KB.pairJ ((p v).form j hj a) (ys n))
      cv_zero (fun x y hx hy => cv_add hx hy) (fun c x hx => cv_smul c hx)
      cv_zero (fun x y hx hy => cv_add hx hy) (fun c x hx => cv_smul c hx)
      (fun x₁ x₂ y c h₁ h₂ hy => form_slC (p v) j hj _ x₁ x₂ y c h₁ h₂ hy)
      (fun x y₁ y₂ c hx h₁ h₂ => form_srC (p v) j hj _ x y₁ y₂ c hx h₁ h₂)
      (fun x₁ x₂ y c h₁ h₂ hy => form_slC (p v) j hj _ x₁ x₂ y c h₁ h₂ hy)
      (fun x y₁ y₂ c hx h₁ h₂ => form_srC (p v) j hj _ x y₁ y₂ c hx h₁ h₂)
      (fun x₁ x₂ y c h₁ h₂ hy => pj_slC (p v) j hj a (ys n) x₁ x₂ y c h₁ h₂ hy)
      (fun x y₁ y₂ c hx h₁ h₂ => pj_srC (p v) j hj a (ys n) x y₁ y₂ c hx h₁ h₂)
      (KB.waveG ((p v).T.bs j) s (KB.plusW (ys n) a))
      (fun x hx => (hVI hA _ _ (D.parOf S v) (p v) j hj _ hCp' s x x hx hx).1)
      (fun x y c _ _ => PBG.waveG_add_smul _ s _ x y c)
      (fun x y hx hy => (hVI hA _ _ (D.parOf S v) (p v) j hj _ hCp' s x y hx hy).2)
      Q hQ (fun x y hx hy => hcs x y hx hy) Y (uY S p F v ε j hj (KB.plusW (ys n) a) Y)
      (uY S p F v ε j hj (KB.minusW (ys n) a) Y) (fun h => uY_cv hB F hF v ε hε j hj _ Y h)
      (fun h => uY_cv hB F hF v ε hε j hj _ Y h) κ cp cm hcp0 hcm0 c d

    have eA : ∑ p' ∈ Y, ∑ p'' ∈ Y, c p' * conj (c p'') * KB.gN S' v ε j (KB.plusW (ys n) a) p' p'' =
        ∑ p' ∈ Y, ∑ p'' ∈ Y, c p' * conj (c p'') * ((cp : ℂ) * (p v).form j hj (KB.plusW (ys n) a)
          (uY S p F v ε j hj (KB.plusW (ys n) a) Y p') (uY S p F v ε j hj (KB.plusW (ys n) a) Y p'')) := by
      refine Finset.sum_congr rfl fun p' hp' => Finset.sum_congr rfl fun p'' hp'' => ?_
      rw [uY_mem S p F v ε j hj _ Y p' hp', uY_mem S p F v ε j hj _ Y p'' hp'', gN_uB hB F hF v ε hε j hj _ p' p'']
    have eB : ∑ q' ∈ Y, ∑ q'' ∈ Y, d q' * conj (d q'') * KB.gN S' v ε j (KB.minusW (ys n) a) q' q'' =
        ∑ q' ∈ Y, ∑ q'' ∈ Y, d q' * conj (d q'') * ((cm : ℂ) * (p v).form j hj (KB.minusW (ys n) a)
          (uY S p F v ε j hj (KB.minusW (ys n) a) Y q') (uY S p F v ε j hj (KB.minusW (ys n) a) Y q'')) := by
      refine Finset.sum_congr rfl fun p' hp' => Finset.sum_congr rfl fun p'' hp'' => ?_
      rw [uY_mem S p F v ε j hj _ Y p' hp', uY_mem S p F v ε j hj _ Y p'' hp'', gN_uB hB F hF v ε hε j hj _ p' p'']
    have hnnA := quad_nonneg (gN_psdC hA hFP hB F hF v ε hε j hj _ hCp Y) c
    have hnnB := quad_nonneg (gN_psdC hA hFP hB F hF v ε hε j hj _ hCm Y) d
    rw [eA] at hnnA ⊢
    rw [eB] at hnnB ⊢
    refine hc.trans (mul_le_mul_of_nonneg_right ?_ (mul_nonneg hnnA hnnB))

    have hg1 := hB.1
    have hg2 := hB.2.1
    have hGg : 0 < S.G.g := by unfold Sz.Glob.g; exact_mod_cast Nat.mul_pos hg1 hg2
    have hGk : 0 < S.G.ka := by
      unfold Sz.Glob.ka; rw [S.hv]; have := PBD.rd_pos' E; positivity
    have hsA := supA_nonneg S hGg hGk v (decide (j = 0))
    have hmem : ∀ b, grid b (n b) ∈ ys n := fun b => List.mem_ofFn.2 ⟨b, rfl⟩
    have hPne : ∀ b, S.P v (grid b (n b)) ≠ 0 ∧ S.P v (grid b (n b) + 1) ≠ 0 := by
      intro b
      have hgr : (∃ a', grid b (n b) ∈ S.grid v a') ∨ grid b (n b) ∈ S.grid1 v := by
        rcases hnd _ (hmem b) with ⟨-, a', -, -, h⟩ | ⟨-, h, -⟩
        · exact Or.inl ⟨a', h⟩
        · exact Or.inr h
      obtain ⟨-, -, h1, h2⟩ := (hGo v).2.2.2.2.2 _ hgr
      exact ⟨h1, h2⟩
    have hnorm : ‖κ‖ = Λ * T ^ K * (1 / (ΓS S j * S.sizeAt v a)) := by
      rw [hκ, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_of_pos (lam_div_theta grid hinj n).1,
        (lam_div_theta grid hinj n).2, abs_of_nonneg (pow_nonneg hT0.le K), abs_of_nonneg (by positivity : (0:ℝ) ≤ c0)]
    rw [hnorm, hQd, hcp, hcm, sizeAt_plusW, sizeAt_minusW, prod_ofFn_map, prod_ofFn_map, prod_ofFn_map]
    exact ratio_bound (fun b => grid b (n b)) (S.P v) qv Λ T (ΓS S j) (S.sizeAt v a)
      (Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l (decide (j = 0)) (S.pl v)) Xc hΓ hsa
      (fun b => hqpos _ (hmem b)) (fun b => (hPne b).1) (fun b => (hPne b).2)
      (fun b => (node_bound hB v a ha haN _ _ (hnd _ (hmem b))).2)
      (Finset.prod_nonneg fun b _ => Finset.sum_nonneg fun i _ => abs_nonneg _) hT0.le
      (mul_nonneg (Real.exp_pos 1).le hsA) hXc
  have hblock := block_of_choices Y (fun n => KB.gN S' v ε j (KB.plusW (ys n) a))
    (fun n => KB.gN S' v ε j (KB.minusW (ys n) a)) Pn θ (Xc ^ K) (Xc ^ K)
    (fun n => (lam_div_theta grid hinj n).1.le)
    (fun n => gN_psdC hA hFP hB F hF v ε hε j hj _ (hnodes n).2.2.1 Y)
    (fun n => gN_psdC hA hFP hB F hF v ε hε j hj _ (hnodes n).2.2.2.1 Y)
    (pow_nonneg hXc0 K) le_rfl hCS
  refine blockPSD_congr (fun _ _ _ _ => rfl) (fun p' hp' q' hq' => ?_) (fun _ _ _ _ => rfl) hblock

  show ∑ n, (θ n : ℂ) * Pn n p' q' = Complex.I ^ K * l ^ K * KB.hatB S' v ε (j + 1) 1 a l p' q'
  rw [hatB_uB_C hPSC hB F hF v ε hε j hj a hwa l p' q' (hY p' hp') (hY q' hq')]
  have hdeg := deg_uB hDW hB F hF v ε hε j hj a K grid hinj s p' q'
  have hIl : Complex.I ^ K * l ^ K = ((T ^ K : ℝ) : ℂ) * s ^ K := by
    rw [hs, sW_eq, mul_pow, mul_pow, ← mul_assoc, ← mul_assoc]
    have : ((T ^ K : ℝ) : ℂ) * (t : ℂ) ^ K = 1 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← mul_pow, mul_comm T t, htT, one_pow, Complex.ofReal_one]
    linear_combination (Complex.I ^ K * l ^ K) * this.symm
  have e1 : Complex.I ^ K * l ^ K * ((c0 : ℂ) * (p v).form j hj a
      (KB.waveG ((p v).T.bs j) s a (uB S p F v ε j hj a p')) (uB S p F v ε j hj a q')) =
      ((T ^ K * c0 : ℝ) : ℂ) * (s ^ K * (p v).form j hj a
      (KB.waveG ((p v).T.bs j) s a (uB S p F v ε j hj a p')) (uB S p F v ε j hj a q')) := by
    rw [hIl]; push_cast; ring
  rw [show (((1 / (ΓS S j * S.sizeAt v a)) : ℝ) : ℂ) = (c0 : ℂ) from rfl, e1, hdeg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hth := (lam_div_theta grid hinj n).1
  have hθ0 : ((F7.thGrid grid n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hth.ne'
  simp only [hPn, uY_mem S p F v ε j hj _ Y p' hp', uY_mem S p F v ε j hj _ Y q' hq', hlag, hθ]
  push_cast
  field_simp
  ring

end C2

end

end Formalism.FourierDecayAlt.P.PBL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CastMIotaSelf
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.FinRangeListSplitting

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH

section split

variable {k ρ : ℕ} {z z' : Fin (2 * (1 + ρ) + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)} {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem finRange_split (ρ : ℕ) :
    (List.finRange (1 + ρ)).reverse = (List.finRange ρ).reverse.map shS ++ [⟨0, by omega⟩] := by
  refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
  by_cases hi : i < ρ
  · rw [List.getElem_append_left (by simpa using hi)]
    simp only [List.getElem_reverse, List.getElem_map, List.getElem_finRange, List.length_finRange]
    ext
    simp [shS]
    omega
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.getElem_reverse, List.getElem_finRange, List.length_finRange, List.length_map,
      List.length_reverse, List.getElem_singleton]
    ext
    simp
    omega

theorem bTall_split (L : R.LevelData (Pr (RadSp k (1 + ρ) z z' π π')) (1 + ρ)) (w : List (Wd.Letter ℂ S)) :
    P5.bTall L w = ((List.finRange ρ).reverse.map fun l => P5.bTl L (shS l) w).prod * P5.bTl L ⟨0, by omega⟩ w := by
  unfold P5.bTall
  rw [finRange_split, List.map_append, List.map_map, List.prod_append]
  simp [Function.comp_def]

end split

section rel

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {T : V →ₗ[ℂ] V'}
  {S : Type} [Fintype S] [DecidableEq S]

theorem arel_listProd {ι : Type} (f : ι → Wd.SlopeTestRemainingChoices S (Pr V)) (f' : ι → Wd.SlopeTestRemainingChoices S (Pr V'))
    (h : ∀ i, ARel T (f i) (f' i)) : ∀ l : List ι, ARel T (l.map f).prod (l.map f').prod
  | [] => by simp only [List.map_nil, List.prod_nil]; exact arel_one
  | a :: l => by
    simp only [List.map_cons, List.prod_cons]
    exact arel_mul (h a) (arel_listProd f f' h l)

end rel

section tr

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * ρ + k + 1) → ℂ} {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)} {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)}

theorem bTall_tr {t : ℂ} (ht : t ≠ 0)
    {X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'}
    {Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))}
    {L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ)}
    {Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ}
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) {S : Type} [Fintype S] [DecidableEq S]
    (w : List (Wd.Letter ℂ S)) (x : Wd.Ix S → RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')
    (e : Wd.Ix S) :
    trL ht z z' π π' (P5.act (P5.bTall L w) x e) =
      P5.act (P5.bTall Ls w) (fun a => trL ht z z' π π' (P5.act (P5.bTl L ⟨0, by omega⟩ w) x a)) e := by
  have hop := fun (l : Fin ρ) (i : Fin 6) Φ => op_tr ht X Xs l i Φ
  have hsite : ∀ l : Fin ρ, ARel (trL ht z z' π π') (P5.bTl L (shS l) w) (P5.bTl Ls l w) := by
    intro l
    refine Formalism.FourierDecayAlt.P.PBP.arel_bT ?_ ?_ ?_ w
    · show Rel _ (L.p (shS l)) (Ls.p l)
      rw [hL.1, hLs.1]
      exact rel_mk (fun v => hop l 0 v) (fun v => by simp only [LinearMap.neg_apply, hop l 3, map_neg])
    · show Rel _ (L.c (shS l)) (Ls.c l)
      rw [hL.2.2.1, hLs.2.2.1]
      exact rel_mk (fun v => hop l 1 v) (fun v => hop l 4 v)
    · show Rel _ (L.ci (shS l)) (Ls.ci l)
      rw [hL.2.2.2.1, hLs.2.2.2.1]
      exact rel_mk (fun v => hop l 2 v) (fun v => hop l 5 v)
  have hall : ARel (trL ht z z' π π') ((List.finRange ρ).reverse.map fun l => P5.bTl L (shS l) w).prod
      (P5.bTall Ls w) := arel_listProd _ _ hsite _
  rw [bTall_split, Formalism.FourierDecayAlt.P5.act_mul]
  exact act_tr hall _ e

end tr

section cast

variable {k n ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem bTall_cast (hn : 1 + ρ = n) {z z' : Fin (2 * n + k + 1) → ℂ} {zs zs' : Fin (2 * ρ + k + 1) → ℂ}
    (hz : z = D.castV hn (liftVec k 1 ρ zs)) (hz' : z' = D.castV hn (liftVec k 1 ρ zs'))
    {π : Mx k n → (Wp →L[ℂ] Wp)} {π' : Mx k n → (Wq →L[ℂ] Wq)}
    {πs : Mx k ρ → (Wp →L[ℂ] Wp)} {πs' : Mx k ρ → (Wq →L[ℂ] Wq)}
    (hπ : ∀ y, πs y = π (D.castM hn (ιLev k 1 ρ y))) (hπ' : ∀ y, πs' y = π' (D.castM hn (ιLev k 1 ρ y)))
    (X : ActualOps k n z z' π π') (Xs : ActualOps k ρ zs zs' πs πs')
    (L : R.LevelData (Pr (RadSp k n z z' π π')) n) (Ls : R.LevelData (Pr (RadSp k ρ zs zs' πs πs')) ρ)
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) {t : ℂ} (ht : t ≠ 0) :
    ∃ T : RadSp k n z z' π π' →ₗ[ℂ] RadSp k ρ zs zs' πs πs',
      (∀ Φ c g, (T Φ : Fn k ρ (Wq →L[ℂ] Wp)) c g =
        (Φ : Fn k n (Wq →L[ℂ] Wp)) (fun l => consC t c (Fin.cast hn.symm l)) (D.castM hn (ιLev k 1 ρ g))) ∧
      ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Wd.Letter ℂ S)) (x : Wd.Ix S → RadSp k n z z' π π')
        (e : Wd.Ix S),
        T (P5.act (P5.bTall L w) x e) =
          P5.act (P5.bTall Ls w) (fun a => T (P5.act (P5.bTl L ⟨0, by omega⟩ w) x a)) e := by
  subst hn
  rw [Formalism.FourierDecayAlt.P.JCTx5.castV_rfl] at hz hz'
  subst hz hz'
  obtain rfl : πs = fun y => π (ιLev k 1 ρ y) := funext fun y => by rw [hπ, Formalism.FourierDecayAlt.P.JCTx5.castM_rfl]
  obtain rfl : πs' = fun y => π' (ιLev k 1 ρ y) := funext fun y => by rw [hπ', Formalism.FourierDecayAlt.P.JCTx5.castM_rfl]
  refine ⟨trL ht zs zs' π π', fun Φ c g => ?_, fun S _ _ w x e => bTall_tr ht hL hLs w x e⟩
  rw [Formalism.FourierDecayAlt.P.JCTx5.castM_rfl]
  rfl

end cast

section misc

theorem exists_cons {n ρ : ℕ} (hn : 1 + ρ = n) (c : Fin n → ℂ) :
    ∃ (t : ℂ) (c' : Fin ρ → ℂ), c = fun l => consC t c' (Fin.cast hn.symm l) := by
  refine ⟨c ⟨0, by omega⟩, fun i => c ⟨i.val + 1, by omega⟩, funext fun l => ?_⟩
  unfold consC
  by_cases h : l.val = 0
  · rw [dite_eq_left (by simpa using h)]
    exact congrArg c (Fin.ext h)
  · rw [dite_eq_right (by simpa using h)]
    exact congrArg c (Fin.ext (by simp; omega))

theorem omX_cons {n ρ : ℕ} (hn : 1 + ρ = n) {t : ℂ} {c : Fin ρ → ℂ}
    (h : (fun l => consC t c (Fin.cast hn.symm l)) ∈ OmX n) : t ≠ 0 ∧ c ∈ OmX ρ := by
  refine ⟨?_, fun i => ?_⟩
  · have := h ⟨0, by omega⟩
    simpa [consC] using this
  · have := h ⟨i.val + 1, by omega⟩
    simpa [consC] using this

theorem hcell_cons {n ρ : ℕ} (hn : 1 + ρ = n) (t : ℂ) (c : Fin ρ → ℂ) :
    PBI.hcell (fun l : Fin n => consC t c (Fin.cast hn.symm l)) = (1, t) :: PBI.hcell c := by
  subst hn
  refine List.ext_getElem (by simp [PBI.hcell]; omega) fun i h1 h2 => ?_
  simp only [PBI.hcell, List.getElem_ofFn]
  rcases i with _ | i
  · simp [consC]
  · simp [consC]

theorem hcell_nil {n : ℕ} (hn : n = 0) (c : Fin n → ℂ) : PBI.hcell c = [] := by
  subst hn; rfl

theorem prod_cons {n ρ : ℕ} (hn : 1 + ρ = n) (k : ℕ) (t : ℂ) (c : Fin ρ → ℂ) :
    (∏ i : Fin n, ‖consC t c (Fin.cast hn.symm i)‖ ^ (2 * (n - (i : ℕ)) + k)) =
      ‖t‖ ^ (2 * n + k) * ∏ i : Fin ρ, ‖c i‖ ^ (2 * (ρ - (i : ℕ)) + k) := by
  subst hn
  rw [← (finCongr (Nat.add_comm ρ 1)).prod_comp, Fin.prod_univ_succ]
  congr 1
  simp only [consC, finCongr_apply, Fin.val_cast, Fin.val_succ]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 2
  omega

theorem iota_split {k n ρ m : ℕ} (hn : 1 + ρ = n) (hm : m = 0) (e1 : n + m = n) (e2 : ρ + m = ρ)
    (g : B.Mat k m) :
    D.castM e1 (ιLev k n m g) = D.castM hn (ιLev k 1 ρ (D.castM e2 (ιLev k ρ m g))) := by
  subst hn hm
  rw [Formalism.FourierDecayAlt.P.JCTx5.castM_rfl, Formalism.FourierDecayAlt.P.JCTx5.castM_rfl, Formalism.FourierDecayAlt.P.JCTx5.castM_rfl]
  exact (ιLev_comp g).symm

theorem castM_iota_self {k a : ℕ} (ha : a = 0) (e : a + a = a) (g : B.Mat k a) : D.castM e (ιLev k a a g) = g := by
  subst ha
  exact Formalism.FourierDecayAlt.P.Dx2.Tower.castMat_levelEmbed_zero e g

theorem resG_empty {k a : ℕ} (ha : a = 0) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (J : Mx k a → E)
    (c : Fin a → ℂ) (g : Mx k a) : resG k a (Fin.last a) J c g = J g := by
  subst ha
  simp [resG, wCell]

theorem ptSize_append (h h' : C.LPt) : D.ptSize (h ++ h') = D.ptSize h + D.ptSize h' := by
  simp [D.ptSize]

end misc

end Formalism.FourierDecayAlt.P.FinRangeListSplitting
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAAdjDone
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem local_adjoint_transfer_holds : JALocAdj := jALocAdj_of_adjComm FFS.adjoint_commutation_holds

theorem local_class_transfer_holds : JALocCC := jALocCC_of_op local_operator_transfer_holds local_adjoint_transfer_holds

theorem group_action_commutation_holds : GA.GAJComm := GA.gAJComm_of_adjComm FFS.adjoint_commutation_holds

theorem group_adjoint_transfer_holds : JAGroupAdj := jAGroupAdj_of_jComm group_action_commutation_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
end

