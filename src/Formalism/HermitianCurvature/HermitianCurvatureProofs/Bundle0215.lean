module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0140
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0204
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaFiniteOfHaar
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableCsmul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0203
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0164
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NegMulCCancel
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBZero
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKap
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0161
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0191
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0162
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0207
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0206
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0199

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CharacterStabilizerEqOne
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section tools

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem stabilizer_mem_unipotent {z' : Fin (2 * r + k + 1) → ℂ} {n0 : B.Mat k r} (hn0 : n0 ∈ C3.N0set k r z') :
    n0 ∈ Formalism.QuantumDeterminants.Nset k r := by
  refine ⟨hn0.1, fun a i _ => ?_, fun i j h1 h2 h3 => hn0.2.2.2.1 i j h1 h2 h3⟩
  have h := congrFun (hn0.2.1 a) i
  rw [show (n0 *ᵥ bvec (eI k r a)) i = n0 i (eI k r a) by simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]] at h
  rw [h]
  simp [bvec, Pi.single_apply]

theorem character_stabilizer_eq_one {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') (c : ℂ) {n0 : B.Mat k r}
    (hn0 : n0 ∈ C3.N0set k r z') : psi k r z' c n0 = 1 := by
  have hcol : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), n0 i (eI k r a) = if i = eI k r a then 1 else 0 := by
    intro a i
    have h := congrFun (hn0.2.1 a) i
    rw [show (n0 *ᵥ bvec (eI k r a)) i = n0 i (eI k r a) by simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]] at h
    rw [h]
    simp [bvec, Pi.single_apply]
  have hell : ell k r z' n0 = 0 := by
    unfold ell
    refine Finset.sum_eq_zero fun a _ => ?_
    split_ifs with h
    · rw [hcol]
      rw [if_neg]
      intro he
      have := congrArg Fin.val he
      simp [eI] at this
    · rw [hn0.2.2.1]
      exact hz' _ (Or.inl (by simp [eI]))
  unfold psi
  rw [hell, mul_zero]
  simp

theorem smoothOnH_of_ckOn {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E}
    (hf : B.CkOn ⊤ (B.GV k r) f) : SmoothOnH (Hpk k r) f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hf g₀ hg₀
  exact ⟨U, f', hU, hgU, hf', fun g hg hgG => hfe g hg hgG⟩

theorem smoothLev_of_loc {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E}
    (hf : ∀ x ∈ B.GV k r, Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc ⊤ f x) : Q.SmoothLev k r 0 Set.univ f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hf g₀ ((Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g₀).1 hg₀.1)
  exact ⟨U, f', hU, hgU, hf', fun g hg hgl => hfe g hg ((Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g).1 hgl)⟩

theorem kr_left (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (σ x : B.Mat k r) :
    PBG.Kr Bs (fun g => F (σ * g)) x = PBG.Kr Bs F (σ * x) := by
  unfold PBG.Kr
  congr 1
  funext p
  have e : σ * (x * Matrix.of p.2 * Matrix.of p.1) = σ * x * Matrix.of p.2 * Matrix.of p.1 := by
    simp only [Matrix.mul_assoc]
  show star (psi k r Bs.z' cStd (Matrix.of p.2)) • (F (σ * (x * Matrix.of p.2 * Matrix.of p.1))).comp
    (Bs.π' (Matrix.of p.1)⁻¹) = _
  rw [e]

theorem kr_congr (Bs : B.RealPlaceData k r Wp Wq) {F₁ F₂ : B.Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ B.GV k r, F₁ g = F₂ g) {x : B.Mat k r} (hx : x ∈ B.GV k r) : PBG.Kr Bs F₁ x = PBG.Kr Bs F₂ x := by
  unfold PBG.Kr
  refine integral_congr_ae ?_
  filter_upwards [PBG.ae_inR Bs] with ξ hξ
  rw [h _ (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hx hξ.2.1) hξ.1.1)]

theorem kr_dmin [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (H : B.Mat k r → (Wq →L[ℂ] Wp)) (l : Fin (r + 2)) (x : B.Mat k r) :
    PBG.Kr Bs (fun g => (Dmin k r Bs.z Bs.z' g l)⁻¹ • H g) x = (Dmin k r Bs.z Bs.z' x l)⁻¹ • PBG.Kr Bs H x := by
  unfold PBG.Kr
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [PBG.ae_inR Bs] with ξ hξ
  show star (psi k r Bs.z' cStd (Matrix.of ξ.2)) • ((Dmin k r Bs.z Bs.z' (x * Matrix.of ξ.2 * Matrix.of ξ.1) l)⁻¹ •
      H (x * Matrix.of ξ.2 * Matrix.of ξ.1)).comp (Bs.π' (Matrix.of ξ.1)⁻¹) =
    (Dmin k r Bs.z Bs.z' x l)⁻¹ • (star (psi k r Bs.z' cStd (Matrix.of ξ.2)) •
      (H (x * Matrix.of ξ.2 * Matrix.of ξ.1)).comp (Bs.π' (Matrix.of ξ.1)⁻¹))
  rw [PBG.dmin_pR Bs hξ x l, ContinuousLinearMap.smul_comp, smul_comm]

def pL (x : Mt k r × Mt k r) : B.SS k r := (x, (Matrix.of.symm 1, Matrix.of.symm 1))

theorem inSS_pL (Bs : B.RealPlaceData k r Wp Wq) {x : Mt k r × Mt k r}
    (hx : (Matrix.of x.1 : B.Mat k r) ∈ UWset k r Bs.z ∧ (Matrix.of x.2 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r) :
    Bs.inSS (pL x) := by
  refine ⟨hx.1, hx.2, ?_, ?_⟩
  · change Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ UWset k r Bs.z'
    rw [Equiv.apply_symm_apply]
    exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw (k := k) (r := r) Bs.z'
  · change Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ Formalism.QuantumDeterminants.Nset k r
    rw [Equiv.apply_symm_apply]
    exact Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_one

theorem sgs_pL (x : Mt k r × Mt k r) (g : B.Mat k r) :
    B.sgs (pL x) g = (Matrix.of x.1 : B.Mat k r)⁻¹ * (Matrix.of x.2 : B.Mat k r)⁻¹ * g := by
  simp only [B.sgs, pL, Prod.fst, Prod.snd, Equiv.apply_symm_apply, Matrix.mul_one]

theorem contDiff_lmul (σ : B.Mat k r) : ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat k r => σ * g) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun l _ => contDiff_const.mul ((contDiff_apply ℝ (fun _ => ℂ) j).comp (contDiff_apply ℝ _ l))

theorem cpt_left (Bs : B.RealPlaceData k r Wp Wq) {G : B.Mat k r → (Wq →L[ℂ] Wp)} (hG : KB.CptCoef Bs G)
    {x : Mt k r × Mt k r}
    (hx : (Matrix.of x.1 : B.Mat k r) ∈ UWset k r Bs.z ∧ (Matrix.of x.2 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r) :
    KB.CptCoef Bs (fun g => G ((Matrix.of x.1 : B.Mat k r)⁻¹ * (Matrix.of x.2 : B.Mat k r)⁻¹ * g)) := by
  set σ : B.Mat k r := (Matrix.of x.1 : B.Mat k r)⁻¹ * (Matrix.of x.2 : B.Mat k r)⁻¹ with hσ
  have hp := inSS_pL Bs hx
  have hmem : ∀ g ∈ B.GV k r, σ * g ∈ B.GV k r := fun g hg => by
    have := Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hg
    rwa [sgs_pL] at this
  have hgf : ∀ g, Gf k r Bs.z Bs.z' (σ * g) = Gf k r Bs.z Bs.z' g := fun g => by
    have := Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp g
    rwa [sgs_pL] at this
  obtain ⟨hs, ⟨R, hR⟩, ⟨ε, hε, hGf⟩⟩ := hG
  refine ⟨fun g₀ hg₀ => ?_, ⟨B.gN (Matrix.of x.2 : B.Mat k r) * B.gN (Matrix.of x.1 : B.Mat k r) * max R 0,
    fun g hg hne => ?_⟩, ⟨ε, hε, fun g hg hne => ?_⟩⟩
  · obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hs (σ * g₀) (hmem g₀ hg₀)
    have hc : Continuous (fun g : B.Mat k r => σ * g) := (contDiff_lmul σ).continuous
    refine ⟨(fun g => σ * g) ⁻¹' U, fun g => f' (σ * g), hU.preimage hc, hgU, ?_, fun g hg hgG => hfe _ hg (hmem g hgG)⟩
    exact hf'.comp (contDiff_lmul σ).contDiffOn (fun g hg => hg)
  · have h1 := hR _ (hmem g hg) hne
    have hu1 : IsUnit (Matrix.of x.1 : B.Mat k r).det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hx.1.1
    have hu2 : IsUnit (Matrix.of x.2 : B.Mat k r).det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hx.2.1
    have e : g = (Matrix.of x.2 : B.Mat k r) * (Matrix.of x.1 : B.Mat k r) * (σ * g) := by
      rw [hσ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc (Matrix.of x.2 : B.Mat k r),
        Matrix.mul_nonsing_inv _ hu1, Matrix.mul_one, Matrix.mul_nonsing_inv _ hu2, Matrix.one_mul]
    calc B.gN g = B.gN ((Matrix.of x.2 : B.Mat k r) * (Matrix.of x.1 : B.Mat k r) * (σ * g)) := by rw [← e]
      _ ≤ B.gN ((Matrix.of x.2 : B.Mat k r) * (Matrix.of x.1 : B.Mat k r)) * B.gN (σ * g) :=
          Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _
      _ ≤ (B.gN (Matrix.of x.2 : B.Mat k r) * B.gN (Matrix.of x.1 : B.Mat k r)) * max R 0 :=
          mul_le_mul (Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _) (h1.trans (le_max_left _ _)) (Formalism.FourierDecayAlt.P.B6.gN_nonneg _)
            (mul_nonneg (Formalism.FourierDecayAlt.P.B6.gN_nonneg _) (Formalism.FourierDecayAlt.P.B6.gN_nonneg _))
  · have := hGf _ (hmem g hg) hne
    rwa [hgf] at this

theorem loc_kr [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F) :
    ∀ x0 ∈ B.GV k r, Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc ⊤ (PBG.Kr Bs F) x0 := by
  obtain ⟨hs, ⟨R, hR⟩, -⟩ := hF
  refine PBG.kr_loc_cpt Bs hs (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k r R) fun g hg hgC => ?_
  by_contra hne
  exact hgC (hR g hg hne)

end tools

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerMatrixBlockThreeMul
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBQ

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section what₂

variable {k p ρ : ℕ}

theorem block_three_mul_apply_last (A11 : Matrix (Fin p) (Fin p) ℂ) (A12 : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ)
    (A13 : Matrix (Fin p) (Fin p) ℂ) (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) (A22 : B.Mat k ρ)
    (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) (g : B.Mat k (p + ρ)) (a : Fin p) (c : Fin (2 * (p + ρ) + k + 1)) :
    (U.blk3 A11 A12 A13 A21 A22 A23 0 0 1 * g) (U.eB k p ρ (Sum.inr a)) c = g (U.eB k p ρ (Sum.inr a)) c := by
  rw [Matrix.mul_apply, ← (U.eB k p ρ).sum_comp]
  rw [Finset.sum_eq_single (Sum.inr a)]
  · rw [Ux3.block3_apply]; simp
  · intro q _ hq
    rw [Ux3.block3_apply]
    rcases q with (q | q) | q
    · simp
    · simp
    · have : q ≠ a := fun h => hq (by rw [h])
      simp [Matrix.one_apply, this.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem zh_row (a : Fin p) : (⟨2 * (p + ρ) + k - a.val, by omega⟩ : Fin (2 * (p + ρ) + k + 1)) =
    U.eB k p ρ (Sum.inr ⟨p - 1 - a.val, by omega⟩) := by
  ext; rw [Ux3.block_index_last_val]; simp; omega

theorem corner_matrix_block_three_mul (A11 : Matrix (Fin p) (Fin p) ℂ) (A12 : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ)
    (A13 : Matrix (Fin p) (Fin p) ℂ) (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) (A22 : B.Mat k ρ)
    (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) (g : B.Mat k (p + ρ)) :
    U.Zh k p ρ (U.blk3 A11 A12 A13 A21 A22 A23 0 0 1 * g) = U.Zh k p ρ g := by
  ext a b
  simp only [U.Zh]
  rw [zh_row, block_three_mul_apply_last]

theorem zh_rn_mul (x : U.RC k p ρ) (g : B.Mat k (p + ρ)) : U.Zh k p ρ (U.Rn k p ρ x * g) = U.Zh k p ρ g := by
  rw [Ux3.rn_eq]; exact corner_matrix_block_three_mul _ _ _ _ _ _ g

theorem zh_embG_mul (y : B.Mat k ρ) (g : B.Mat k (p + ρ)) : U.Zh k p ρ (U.embG k p ρ y * g) = U.Zh k p ρ g := by
  unfold U.embG; exact corner_matrix_block_three_mul _ _ _ _ _ _ g

end what₂

section zh

variable {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem zh_sP_mul (Bj : B.RealPlaceData k ρ Wp Wq) (x : XP k p ρ) (g : B.Mat k (p + ρ)) :
    U.Zh k p ρ (sP Bj x * g) = U.Zh k p ρ g := by
  unfold sP
  split_ifs
  · rw [Matrix.mul_assoc, zh_rn_mul, zh_embG_mul]
  · rw [Matrix.one_mul]

theorem zh_mul_UW (z : Fin (2 * (p + ρ) + k + 1) → ℂ) (g h : B.Mat k (p + ρ)) (hh : h ∈ UWset k (p + ρ) z) :
    U.Zh k p ρ (g * h) = U.Zh k p ρ g := by
  ext a b
  simp only [U.Zh, Matrix.mul_apply]
  have hcol : ∀ c : Fin (2 * (p + ρ) + k + 1), h c ⟨b.val, by omega⟩ = if c.val = b.val then 1 else 0 := by
    intro c
    have h1 := congrFun (hh.2.1 ⟨b.val, by omega⟩).1 c
    have e : eI k (p + ρ) ⟨b.val, by omega⟩ = ⟨b.val, by omega⟩ := rfl
    rw [e] at h1
    rw [← Formalism.FourierDecayAlt.P.PBM.mulVec_bvec_apply h ⟨b.val, by omega⟩ c, h1]
    unfold bvec
    by_cases hcb : c.val = b.val
    · rw [if_pos hcb, Pi.single_apply, if_pos (Fin.ext hcb)]
    · rw [if_neg hcb, Pi.single_apply, if_neg (fun h' => hcb (congrArg Fin.val h'))]
  rw [Finset.sum_eq_single ⟨b.val, by omega⟩]
  · rw [hcol, if_pos rfl, mul_one]
  · intro c _ hc
    rw [hcol, if_neg (fun h' => hc (Fin.ext h')), mul_zero]
  · intro h'; exact absurd (Finset.mem_univ _) h'

theorem nblk_upper (nn : B.Mat k (p + ρ)) (hn : nn ∈ Nset k (p + ρ)) :
    Matrix.of (fun c b : Fin p => nn ⟨c.val, by omega⟩ ⟨b.val, by omega⟩) =
      G.upper (fun q : G.UT p => nn ⟨q.1.1.val, by omega⟩ ⟨q.1.2.val, by omega⟩) := by
  ext c b
  simp only [Matrix.of_apply, G.upper, G.strictUpper, Matrix.add_apply, Matrix.one_apply]
  rcases lt_trichotomy c b with hcb | rfl | hcb
  · rw [if_neg (ne_of_lt hcb), dite_eq_left hcb, zero_add]
  · rw [LeftFubiniLemmas.n_col nn hn c _ le_rfl, if_pos rfl, if_pos rfl, dite_eq_right (lt_irrefl _), add_zero]
  · rw [LeftFubiniLemmas.n_col nn hn b _ (le_of_lt hcb), if_neg (by simp only; omega), if_neg (ne_of_gt hcb),
      dite_eq_right (not_lt.mpr (le_of_lt hcb)), add_zero]

end zh

section support

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem pb_head_support (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (H : B.Mat k n → (Wq →L[ℂ] Wp)) (Cs : Set (B.Mat k n)) (hCs : IsCompact Cs)
    (hH : ∀ g ∈ B.GV k n, g ∉ Cs → H g = 0) :
    ∃ R : ℝ, ∀ v : U.LW σ → ℂ, R < ‖v‖ → ∀ g ∈ B.GV k n,
      U.Zh k p ρ (D.castM e.symm g) = LeftFubiniLemmas.lhOf σ v * U.hMat σ d → pbF Bj B0 e H g = 0 := by
  subst e
  obtain ⟨C2, hC2⟩ := Formalism.FourierDecayAlt.P.aux_statement_17 p 0 σ d hd
  have hcont : Continuous (fun c : B.Mat k (p + ρ) => U.mx (U.Zh k p ρ c)) := by
    have e1 : (fun c : B.Mat k (p + ρ) => U.mx (U.Zh k p ρ c)) =
        fun c => ‖(fun a b => c ⟨2 * (p + ρ) + k - a.val, by omega⟩ ⟨b.val, by omega⟩ : Fin p → Fin p → ℂ)‖ := rfl
    rw [e1]
    refine continuous_norm.comp ?_
    refine continuous_pi fun a => continuous_pi fun b => ?_
    exact (continuous_apply (⟨b.val, by omega⟩ : Fin (2 * (p + ρ) + k + 1))).comp
      (continuous_apply (⟨2 * (p + ρ) + k - a.val, by omega⟩ : Fin (2 * (p + ρ) + k + 1)))
  obtain ⟨M, hM⟩ := hCs.exists_bound_of_continuousOn hcont.continuousOn
  set M0 : ℝ := max M 0 with hM0
  set C0 : ℝ := max C2 0 with hC0
  refine ⟨C0 * M0 ^ p, fun v hv g hg hZ => ?_⟩
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl] at hZ
  unfold pbF
  rw [← integral_zero (XP k p ρ) (Wq →L[ℂ] Wp)]
  refine integral_congr_ae ?_
  filter_upwards [ae_goodP Bj] with x hx
  show pbI Bj B0 rfl H g x = 0
  unfold pbI
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  have hK : PBG.Kr B0 H (sP Bj x * g) = 0 := by
    unfold PBG.Kr
    rw [← integral_zero (Mt k (p + ρ) × Mt k (p + ρ)) (Wq →L[ℂ] Wp)]
    refine integral_congr_ae ?_
    filter_upwards [PBG.ae_inR B0] with ξ hξ
    show _ = 0
    have hc : sP Bj x * g * Matrix.of ξ.2 * Matrix.of ξ.1 ∉ Cs := by
      intro hcC
      have hZc : U.Zh k p ρ (sP Bj x * g * Matrix.of ξ.2 * Matrix.of ξ.1) =
          U.headH σ d v (fun q : G.UT p => (Matrix.of ξ.2 : B.Mat k (p + ρ)) ⟨q.1.1.val, by omega⟩ ⟨q.1.2.val, by omega⟩) := by
        rw [zh_mul_UW _ _ _ hξ.1, LeftFubiniLemmas.zh_mul_N _ _ hξ.2, zh_sP_mul, hZ, nblk_upper _ hξ.2,
          (LeftFubiniLemmas.head_hermitian_eq p σ d v _).1]
      set η : U.XiH p 0 σ := ((fun i => i.elim0, fun _ i => i.elim0),
        (v, fun q : G.UT p => (Matrix.of ξ.2 : B.Mat k (p + ρ)) ⟨q.1.1.val, by omega⟩ ⟨q.1.2.val, by omega⟩)) with hη
      have hZj : U.ZjH σ d η (fun i => i.elim0) = U.Zh k p ρ (sP Bj x * g * Matrix.of ξ.2 * Matrix.of ξ.1) := by
        rw [hZc, LeftFubiniLemmas.lower_corner_hermitian_zero]
      have hb := (hC2 η (fun i => i.elim0)).2.2.1
      rw [hZj] at hb
      have hm := hM _ hcC
      rw [Real.norm_eq_abs, abs_le] at hm
      have hmx0 : 0 ≤ U.mx (U.Zh k p ρ (sP Bj x * g * Matrix.of ξ.2 * Matrix.of ξ.1)) := norm_nonneg _
      have h1 : U.mx (U.Zh k p ρ (sP Bj x * g * Matrix.of ξ.2 * Matrix.of ξ.1)) ≤ M0 := hm.2.trans (le_max_left _ _)
      have h2 : ‖v‖ ≤ C0 * M0 ^ p := by
        refine hb.trans ?_
        exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ hmx0 h1 p) (pow_nonneg hmx0 _) (le_max_right _ _)
      exact absurd hv (not_lt.mpr h2)
    have hGV : sP Bj x * g * Matrix.of ξ.2 * Matrix.of ξ.1 ∈ B.GV k (p + ρ) := by
      have hs : sP Bj x ∈ B.GV k (p + ρ) := by
        unfold sP
        rw [if_pos hx]
        refine Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (LeftFubiniLemmas.rn_nset _).1 ?_
        rw [← Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]
        exact Formalism.FourierDecayAlt.P.Dx2.Tower.lev_GV p ρ _
          (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hx.1.1) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hx.2.1))
      exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hs hg) hξ.2.1) hξ.1.1
    rw [hH _ hGV hc, ContinuousLinearMap.zero_comp, smul_zero]
  rw [hK, ContinuousLinearMap.comp_zero, smul_zero]

end support

end Formalism.FourierDecayAlt.P.PBQ
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapAsm
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jABddKapQQ_of_kapRealiser (hR : KapRealiser) : JABddKapQQ := by
  obtain ⟨K, hK, hR⟩ := hR
  refine ⟨K, hK, ?_⟩
  intro Cc Cb hCc hCb E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL b hb
  obtain ⟨κ, rfl⟩ := hb
  obtain ⟨c, ca, hadj, hc, hca, he, hea, hbc, hbca, hbig⟩ :=
    hR Cc Cb hCc hCb E Wp Wq S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ κ
  refine ⟨SSn.orderZeroDifferentialOperator S v c ca hadj, SSn.order_zero_operator_order, ⟨?_, ?_⟩, ?_, fun J hJ => ⟨?_, ?_, ?_⟩⟩
  · intro Tm hTm
    simp only [SSn.orderZeroDifferentialOperator, List.mem_singleton] at hTm
    subst hTm
    exact ⟨hc, hca⟩
  · intro p hp f' _ g hg
    rw [SSn.order_zero_operator_apply, SSn.order_zero_operator_apply]
    exact he p hp g hg.1 _
  · intro Tm hTm ε hε m
    simp only [SSn.orderZeroDifferentialOperator, List.mem_singleton] at hTm
    subst hTm
    obtain ⟨C1, h1⟩ := hbc ε hε m
    obtain ⟨C2, h2⟩ := hbca ε hε m
    refine ⟨max C1 C2, fun u w hu hw hl g hg hG => ⟨?_, ?_⟩⟩
    · have hpow : 0 ≤ B.gN g ^ (Cb * ((S.G.r : ℝ) + 1) * m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      rw [zero_add]
      exact (h1 u w hu hw hl g hg hG).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)
    · have hpow : 0 ≤ B.gN g ^ (Cb * ((S.G.r : ℝ) + 1) * m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      rw [zero_add]
      exact (h2 u w hu hw hl g hg hG).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpow)
  · rw [SSn.order_zero_operator_apply]; exact SSn.equivariant_coefficient_preserves_forms hc he hJ
  · rw [SSn.order_zero_operator_adjoint]; exact SSn.equivariant_coefficient_preserves_forms hca hea hJ
  · rw [SSn.order_zero_operator_apply]
    exact trJ_kap_of_bigCell S T v e κ c hbig J

theorem jABddKapQQ_of_typeProj (hB : DatumBd) (hG : SSn.SSnGeom) (hP : TypeProj) : JABddKapQQ :=
  jABddKapQQ_of_kapRealiser (kapRealiser_of_typeProj hB hG hP)

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnAsm
section
open Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn

open NumberField Formalism.FourierDecayAlt.P.CutMP

theorem sSnAssemble_of (hC : JA.DatumCompose) : SSnAssemble := by
  intro hG hR
  obtain ⟨K1, hK1, hG⟩ := hG
  obtain ⟨K2, hK2, hR⟩ := hR
  refine ⟨max K1 K2, le_max_of_le_left hK1, ?_⟩
  intro Cc Cb hCc hCb E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ l hl
  obtain ⟨a, a', ι, hD⟩ := hG Cc Cb (le_trans (le_max_left _ _) hCc) (le_trans (le_max_left _ _) hCb)
    E Wp Wq S T f χ ν' m₀ top A₀ hB v
  obtain ⟨Φ, Φa, hΦ⟩ := hR Cc (le_trans (le_max_right _ _) hCc) E Wp Wq S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ l hl
  have hCb0 : 0 ≤ Cb := le_trans (le_max_of_le_left hK1) hCb
  have hBg : 0 ≤ Cb * ((S.G.r : ℝ) + 1) := mul_nonneg hCb0 (by positivity)
  obtain ⟨c, ca, hadj, hc, hca, he, hea, hb, hba, hcv⟩ :=
    hC E Wp Wq S T v _ a a' ι Φ Φa hBg hD ⟨hΦ.1, hΦ.2.1, hΦ.2.2.1, hΦ.2.2.2.1⟩
  refine ⟨c, ca, hadj, hc, hca, he, hea, hb, hba, ?_⟩
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Formalism.QuantumDeterminants.Tz S.G.k S.G.r (T v).base.z * Formalism.QuantumDeterminants.Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  intro q hq ρ π
  have hqD : q ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hq.1, hTT ▸ hq.2⟩
  have hG' := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hqD
  have hpos : B.gq (T v).base q ∈ B.GPos (T v).base := ⟨hG'.1, hG'.2.2⟩
  obtain ⟨h1, h2, h3⟩ := hD.2.2.2.2.2.2.2 q hq
  rw [hcv _ hpos, h1, h2, h3]
  exact hΦ.2.2.2.2 q hq ρ π

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocOpAdjProof
section
noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem local_operator_transfer_holds : JALocOp :=
  jALocOp_of_tools LT.operator_in_class_holds LT.agreement_on_domain_holds LT.theta_transfer_apply_holds

theorem jALocAdj_of_adjComm (h : FFS.AdjComm) : JALocAdj :=
  jALocAdj_of_tools LT.operator_in_class_holds LT.agreement_on_domain_holds (LT.thetaJ_of_adjComm h)

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLSAExh
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

theorem average_one_cutoff_on_orbits : Formalism.FourierDecayAlt.P.JFxI.AvgCutoff := avgCutoff_of_smooth averaging_smoothness_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

