module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformizerSectionAtPrimeSet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1929
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1884
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1862
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1879
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveHomogeneousOperatorLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1926
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1934
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1928
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1933
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftDatumConjugateHalfFiniteFourierSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.LiftFour

theorem dil_add {D : D7} (i : Fin D.R.m) (a : D.host.E) (x y : WO (Vc D i) (Wc D i)) :
    dil i a (x + y) = dil i a x + dil i a y := by
  exact Matrix.ext fun p q => by simp only [dil, Matrix.map_apply, Matrix.add_apply, mul_add]

theorem isHalf_add {D : D7} {m n : ℕ} {e : AE D} {x y : Mx D m n} (hx : IsHalf e x) (hy : IsHalf e y) :
    IsHalf e (x + y) := fun p q => by simp only [Matrix.add_apply, mul_add, hx p q, hy p q]

theorem isHalf_of_add {D : D7} {m n : ℕ} {e : AE D} {x y : Mx D m n} (hxy : IsHalf e (x + y)) (hy : IsHalf e y) :
    IsHalf e x := fun p q => by
  have h1 := hxy p q
  simp only [Matrix.add_apply, mul_add, hy p q] at h1
  exact add_right_cancel h1

theorem isHalf_dil {D : D7} (i : Fin D.R.m) {e : AE D} {a : D.host.E} (ha : a ≠ 0) (x : WO (Vc D i) (Wc D i)) :
    IsHalf e (dil i a x) ↔ IsHalf e x := by
  have hu : incA D a⁻¹ * incA D a = 1 := by rw [← RingHom.map_mul, inv_mul_cancel₀ ha, map_one]
  constructor
  · intro h p q
    have h1 : e * (incA D a * x p q) = incA D a * x p q := h p q
    linear_combination (incA D a⁻¹) * h1 - (e * x p q - x p q) * hu
  · intro h p q
    show e * (incA D a * x p q) = incA D a * x p q
    rw [mul_left_comm, h p q]

theorem redM_frMapO_add {D : D7} {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (PP : Pl D.host.E) (a b : WO S T) (ha : IsIntM (frMapO S T βS βT a)) (hb : IsIntM (frMapO S T βS βT b)) :
    redM PP (frMapO S T βS βT (a + b)) = redM PP (frMapO S T βS βT a) + redM PP (frMapO S T βS βT b) := by
  have e : frMapO S T βS βT (a + b) = frMapO S T βS βT a + frMapO S T βS βT b := by
    ext p q
    have := GlobalTheory.PlaceDatum.frMapO_add βS βT a b 1 p q
    simpa using this
  ext p q
  simp only [redM, e, Matrix.add_apply, Matrix.of_apply]
  rw [dite_eq_left (add_mem (ha p q) (hb p q)), dite_eq_left (ha p q), dite_eq_left (hb p q), ← map_add (f := _)]
  rfl

theorem datum_conj_half_fourier : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)),
    (∃ t, Q ⊆ R.Q t) → (∀ PP ∈ Q, ξR PP ≠ 1) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) →
    ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) →
    ∃ (Y : Finset (WO (Vc D i) (Wc D i))) (a : WO (Vc D i) (Wc D i) → ℂ) (Gc : ℂ), UnitOff N Gc ∧ (∀ y ∈ Y, IsHalf eQ y) ∧
      (∀ t, (if IsHalf (cA D eQ) t ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) t) then
        omegaQ Q (Wc D i).rank ξR (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) t)) else 0) =
        halfInd (cA D eQ) (lattice₂ R i) t * ∑ y ∈ Y, a y * R.ψ (symplO (Vc D i) (Wc D i) t y)) ∧
      ∀ t, ∑ y ∈ Y, a y * halfInd eQ (lattice₂ R i) (t + y) = Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) t) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i hV ξR Q hQ hξ N hN hNQ eQ heQ ϖ hϖ hϖQ
  classical
  letI : ∀ PP : Pl D.host.E, Fintype (kP PP) := fun PP => Fintype.ofFinite _
  have hϖ' : (ϖ : D.host.E) ≠ 0 := by
    intro h; exact hϖ (by exact_mod_cast h)
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hrn : (Wc D i).rank ≤ (Vc D i).rank := by rw [rV, rW]; omega
  obtain ⟨ψP, hψP, hchar⟩ := _root_.GlobalTheory.QResChar.char_eq_prod D G Pl0 T0 A Ks R F hC hG i hV Q hQ eQ heQ ϖ hϖ hϖQ
  obtain ⟨c, hinv, hc⟩ := _root_.GlobalTheory.ResidueFourier.omegaQ_fourier D Q (Vc D i).rank (Wc D i).rank hrn ψP ξR hψP hξ
  choose yx hyh hyl hyr using _root_.GlobalTheory.HalfLiftRed.exists_half_dil_redM_eq D G Pl0 T0 A Ks R F hC hG i hV Q hQ eQ heQ ϖ hϖ hϖQ
  have hker := _root_.GlobalTheory.DilKer.mem_localLattice_iff_redM D G Pl0 T0 A Ks R F hC hG i hV Q hQ eQ heQ ϖ hϖ hϖQ
  have h4a := _root_.GlobalTheory.QHalfLat.isIntM_adj_iff_mem_latP D G Pl0 T0 A Ks R F hC hG i hV Q hQ eQ heQ
  have h4b := _root_.GlobalTheory.HalfLatInt.isIntM_iff_mem_latP D G Pl0 T0 A Ks R F hC hG i hV Q hQ eQ heQ
  have hdm := _root_.GlobalTheory.BaseCmp.dil_mem_latP D G Pl0 T0 A Ks R i ϖ
  have key : ∀ g : WO (Vc D i) (Wc D i) → ℂ,
      ∑ y ∈ Finset.univ.image yx, (∑ x ∈ Finset.univ.filter (fun x => yx x = y), c x) * g y = ∑ x, c x * g (yx x) := by
    intro g
    simp_rw [Finset.sum_mul]
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image yx) (g := yx)
      (fun x _ => Finset.mem_image_of_mem yx (Finset.mem_univ x))]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x hx => ?_
    rw [(Finset.mem_filter.1 hx).2]
  refine ⟨Finset.univ.image yx, fun y => ∑ x ∈ Finset.univ.filter (fun x => yx x = y), c x, _,
    _root_.GlobalTheory.GaussUnit.unitOff_prod_gaussSum D Q (Vc D i).rank (Wc D i).rank hrn ψP ξR hψP hξ N hN hNQ, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hy
    exact hyh x
  · intro t
    rw [key (fun y => R.ψ (symplO (Vc D i) (Wc D i) t y))]
    by_cases ht : IsHalf (cA D eQ) t
    · by_cases hl : t ∈ lattice₂ R i
      · have hint := (h4a t ht).2 hl
        rw [if_pos ⟨ht, hint⟩, halfInd, if_pos ⟨hl, ht⟩, one_mul, hinv]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hchar t (yx x) ht hl (hyh x) (hyl x), ← Finset.prod_attach Q]
        refine congrArg _ (Finset.prod_congr rfl fun PP _ => ?_)
        rw [hyr x PP]
      · rw [if_neg (fun h => hl ((h4a t ht).1 h.2)), halfInd, if_neg (fun h => hl h.1), zero_mul]
    · rw [if_neg (fun h => ht h.1), halfInd, if_neg (fun h => ht h.2), zero_mul]
  · intro t
    rw [key (fun y => halfInd eQ (lattice₂ R i) (t + y)), flatDat]
    by_cases ht : IsHalf eQ t
    · have hdt : IsHalf eQ (dil i (ϖ : D.host.E) t) := (isHalf_dil i hϖ' t).2 ht
      by_cases hl : dil i (ϖ : D.host.E) t ∈ lattice₂ R i
      · have hint := (h4b _ hdt).2 hl
        rw [if_pos ⟨hdt, hint⟩]
        set ρt : ∀ PP : ↥Q, Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (kP PP.1) :=
          fun PP => redM PP.1 (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) t)) with hρt
        have hterm : ∀ x, halfInd eQ (lattice₂ R i) (t + yx x) = if x = -ρt then 1 else 0 := by
          intro x
          have hh : IsHalf eQ (t + yx x) := isHalf_add ht (hyh x)
          have hdl : dil i (ϖ : D.host.E) (t + yx x) ∈ lattice₂ R i := by
            rw [dil_add]; exact add_mem hl (hyl x)
          have hintx := (h4b _ ((isHalf_dil i hϖ' _).2 (hyh x))).2 (hyl x)
          rw [halfInd]
          by_cases hx : x = -ρt
          · have hm : t + yx x ∈ lattice₂ R i := by
              refine (hker _ hh hdl).2 fun PP hPP => ?_
              rw [dil_add, redM_frMapO_add _ _ _ _ _ hint hintx, hyr x ⟨PP, hPP⟩, hx]
              simp [hρt]
            rw [if_pos hx, if_pos ⟨hm, hh⟩]
          · rw [if_neg hx, if_neg]
            rintro ⟨hm, -⟩
            apply hx
            funext PP
            have h0 := (hker _ hh hdl).1 hm PP.1 PP.2
            rw [dil_add, redM_frMapO_add _ _ _ _ _ hint hintx, hyr x PP] at h0
            rw [Pi.neg_apply, hρt]
            exact eq_neg_of_add_eq_zero_right h0
        simp_rw [hterm, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq' Finset.univ (-ρt) c, if_pos (Finset.mem_univ _)]
        exact hc ρt _ fun PP => rfl
      · rw [if_neg (fun h => hl ((h4b _ hdt).1 h.2))]
        rw [mul_zero]
        refine Finset.sum_eq_zero fun x _ => ?_
        rw [halfInd, if_neg, mul_zero]
        rintro ⟨hm, -⟩
        apply hl
        have := hdm _ hm
        rw [dil_add] at this
        simpa using sub_mem this (hyl x)
    · rw [if_neg (fun h => ht ((isHalf_dil i hϖ' t).1 h.1))]
      rw [mul_zero]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [halfInd, if_neg, mul_zero]
      rintro ⟨-, hh⟩
      exact ht (isHalf_of_add hh (hyh x))

end GlobalTheory.LiftFour
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarLocalThetaFactor
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.OppLinOp

theorem local_op_eq_smul : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι → ∀ g ∈ UAt σ G.V' (evFin F v), ∀ h ∈ UAt σ G.W (evFin F v),
    ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
    Acts (evFin F v) (om' (g, h)) φ φ₁ →
    ∃ (c : ℂ) (P : GL (Fin a') (Fv F v)) (Q : GL (Fin (a + a')) (Fv F v)), ∀ Y, ι φ₁ Y = c * ι φ (P.1 * Y * Q.1) := by
  intro hPr F E _ _ _ _ _ σ B a a' G X om om' hT v t ι hι g hg h hh φ hφ φ₁ hφ₁ hacts
  classical
  set co : Matrix (Fin a') (Fin (a + a')) (AE F E) → Matrix (Fin a') (Fin (a + a')) (Fv F v) :=
    fun u => -((1 : GL (Fin a') (Fv F v)).1ᵀ * G.V'.J.map t * u.map (piW (t.comp σ)) * (G.W.J.map t)ᵀ *
      (1 : GL (Fin (a + a')) (Fv F v)).1) with hco
  have hL : G.M'.IsLin B.ψ (piW (t.comp σ)) (piW t) co ι := hι
  have hP' := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).2
  obtain ⟨hex1, hex2, -⟩ := GlobalTheory.T.theta_action_exists hPr F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hP' v

  have hex1' : ∀ ξ : (Fin a' × Fin (a + a') → Fv F v) → ℂ, ∃ η, ξ ∈ SB (Fin a' × Fin (a + a') → Fv F v) →
      η ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧ Acts (evFin F v) (om' (g, h)) ξ η := by
    intro ξ
    by_cases hξ : ξ ∈ SB (Fin a' × Fin (a + a') → Fv F v)
    · obtain ⟨η, hη, -⟩ := hex1 g hg h hh ξ hξ
      exact ⟨η, fun _ => hη⟩
    · exact ⟨0, fun h' => absurd h' hξ⟩
  choose T hTspec using hex1'

  set ιi := Function.invFunOn ι (SB (Fin a' × Fin (a + a') → Fv F v) : Set ((Fin a' × Fin (a + a') → Fv F v) → ℂ))
    with hιi
  have hinv := hL.bij.invOn_invFunOn
  have hi1 : ∀ Ξ ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)),
      ιi Ξ ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧ ι (ιi Ξ) = Ξ :=
    fun Ξ hΞ => ⟨hL.bij.surjOn.mapsTo_invFunOn hΞ, hinv.2 hΞ⟩
  have hi2 : ∀ ξ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ιi (ι ξ) = ξ := fun ξ hξ => hinv.1 hξ

  set gt := (mat g).map (piW t) with hgt
  set gi := (mat g⁻¹).map (piW t) with hgi
  set ht' := (mat h).map (piW t) with hht
  set hi := (mat h⁻¹).map (piW t) with hhi
  have hg1 : gt * gi = 1 := by
    rw [hgt, hgi, ← Matrix.map_mul]
    have : mat g * mat g⁻¹ = 1 := by simp [mat]
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  have hg2 : gi * gt = 1 := by
    rw [hgt, hgi, ← Matrix.map_mul]
    have : mat g⁻¹ * mat g = 1 := by simp [mat]
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  have hh1 : ht' * hi = 1 := by
    rw [hht, hhi, ← Matrix.map_mul]
    have : mat h * mat h⁻¹ = 1 := by simp [mat]
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  have hh2 : hi * ht' = 1 := by
    rw [hht, hhi, ← Matrix.map_mul]
    have : mat h⁻¹ * mat h = 1 := by simp [mat]
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  have hPP : giᵀ * gtᵀ = 1 := by rw [← Matrix.transpose_mul, hg1, Matrix.transpose_one]
  have hPP' : gtᵀ * giᵀ = 1 := by rw [← Matrix.transpose_mul, hg2, Matrix.transpose_one]

  have at_conj : ∀ u : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) u →
      At (evFin F v) (mat g * u * (mat h)ᵀ) := by
    intro u hu c hc
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hu c hc, Matrix.mul_zero, Matrix.zero_mul]
  have hmap : ∀ (f : AE F E →+* Fv F v) (u : Matrix (Fin a') (Fin (a + a')) (AE F E)),
      (mat g * u * (mat h)ᵀ).map f = (mat g).map f * u.map f * ((mat h).map f)ᵀ := by
    intro f u
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have hco_act : ∀ u : Matrix (Fin a') (Fin (a + a')) (AE F E), co (mat g * u * (mat h)ᵀ) = giᵀ * co u * hi := by
    intro u
    have hca : gtᵀ * co (mat g * u * (mat h)ᵀ) * ht' = co u := GlobalTheory.T.local_moment_matrix_transform F E σ a' (a + a') G.V' G.W v t g h u
    calc co (mat g * u * (mat h)ᵀ) = (giᵀ * gtᵀ) * co (mat g * u * (mat h)ᵀ) * (ht' * hi) := by
          rw [hPP, hh1, Matrix.one_mul, Matrix.mul_one]
      _ = giᵀ * (gtᵀ * co (mat g * u * (mat h)ᵀ) * ht') * hi := by simp only [Matrix.mul_assoc]
      _ = giᵀ * co u * hi := by rw [hca]

  set A : (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ) → Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ :=
    fun Ξ Y => ι (T (ιi Ξ)) (giᵀ * Y * hi) with hA
  have hlin : ∀ (c0 : ℂ), ∀ Ξ ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)),
      ∀ Ξ' ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)), A (c0 • Ξ + Ξ') = c0 • A Ξ + A Ξ' := by
    intro c0 Ξ hΞ Ξ' hΞ'
    obtain ⟨hξ, hιξ⟩ := hi1 Ξ hΞ
    obtain ⟨hξ', hιξ'⟩ := hi1 Ξ' hΞ'
    have hs : c0 • ιi Ξ + ιi Ξ' ∈ SB (Fin a' × Fin (a + a') → Fv F v) := add_mem (Submodule.smul_mem _ c0 hξ) hξ'
    have e1 : ιi (c0 • Ξ + Ξ') = c0 • ιi Ξ + ιi Ξ' := by
      have : ι (c0 • ιi Ξ + ιi Ξ') = c0 • Ξ + Ξ' := by rw [map_add (f := _), map_smul, hιξ, hιξ']
      rw [← this]; exact hi2 _ hs
    obtain ⟨-, hTa1⟩ := hTspec _ hξ
    obtain ⟨-, hTa2⟩ := hTspec _ hξ'
    obtain ⟨-, hTa3⟩ := hTspec _ hs
    have e2 := GlobalTheory.T.local_action_linear_in_vector F (Fin a' × Fin (a + a')) v (om' (g, h)) c0 (ιi Ξ) (ιi Ξ') _ _ _ hξ hξ' hTa1 hTa2 hTa3
    funext Y
    show ι (T (ιi (c0 • Ξ + Ξ'))) (giᵀ * Y * hi) = c0 * ι (T (ιi Ξ)) (giᵀ * Y * hi) + ι (T (ιi Ξ')) (giᵀ * Y * hi)
    rw [e1, e2, map_add (f := _), map_smul]
    rfl
  have hA0 : A 0 = 0 := by
    have h0 := hlin 1 0 (zero_mem _) 0 (zero_mem _)
    simp only [one_smul, add_zero] at h0
    have h2 : A 0 + A 0 = A 0 + 0 := by rw [add_zero]; exact h0.symm
    exact add_left_cancel h2
  have hadd : ∀ f ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)), ∀ f' ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)),
      A (f + f') = A f + A f' := fun f hf f' hf' => by simpa using hlin 1 f hf f' hf'
  have hsmul : ∀ (c : ℂ), ∀ f ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)), A (c • f) = c • A f :=
    fun c f hf => by simpa [hA0] using hlin c f hf 0 (zero_mem _)

  have hut_map : ∀ u : Matrix (Fin a') (Fin (a + a')) (AE F E), ∀ f : AE F E →+* Fv F v, u.map f = 0 →
      (mat g * u * (mat h)ᵀ).map f = 0 := by
    intro u f hu
    rw [hmap, hu, Matrix.mul_zero, Matrix.zero_mul]
  have hsurj := fun Y => GlobalTheory.T.local_matrix_moment_surjective F E σ B hT.base a' (a + a') _ _ _ _ G.V' G.W hT.geo.hV' hT.geo.hW v t Y
  have htr : ∀ Z : Matrix (Fin a') (Fin (a + a')) (Fv F v), ∀ Ξ ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)),
      A (fun Y => Ξ (Y + Z)) = fun Y => A Ξ (Y + Z) := by
    intro Z Ξ hΞ
    obtain ⟨hξ, hιξ⟩ := hi1 Ξ hΞ
    obtain ⟨u, hu, hut, hcu⟩ := hsurj Z
    have hcu' : co u = Z := hcu
    obtain ⟨ξ₁, ⟨hξ₁, hact₁⟩, -⟩ := hex2 u hu (ιi Ξ) hξ
    have e1 : ι ξ₁ = fun Y => Ξ (Y + Z) := by
      funext Y
      rw [hL.trans u hu hut (ιi Ξ) hξ ξ₁ hξ₁ hact₁ Y, hιξ, hcu']
    have e2 : ιi (fun Y => Ξ (Y + Z)) = ξ₁ := by rw [← e1]; exact hi2 ξ₁ hξ₁
    obtain ⟨hTξ, hTa⟩ := hTspec (ιi Ξ) hξ
    obtain ⟨ξ₄, ⟨hξ₄, hact₄⟩, -⟩ := hex2 _ (at_conj u hu) (T (ιi Ξ)) hTξ
    obtain ⟨-, hTa₁⟩ := hTspec ξ₁ hξ₁
    have e3 : ξ₄ = T ξ₁ := GlobalTheory.T.theta_pair_local_schwartz_action F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hP' v (g, h) u (ιi Ξ) ξ₁
      (T (ιi Ξ)) (T ξ₁) ξ₄ hξ hξ₁ hTξ hact₁ hTa hTa₁ hact₄
    funext Y
    show ι (T (ιi (fun Y => Ξ (Y + Z)))) (giᵀ * Y * hi) = ι (T (ιi Ξ)) (giᵀ * (Y + Z) * hi)
    rw [e2, ← e3, hL.trans _ (at_conj u hu) (hut_map u _ hut) (T (ιi Ξ)) hTξ ξ₄ hξ₄ hact₄, hco_act, hcu',
      Matrix.mul_add, Matrix.add_mul]

  have hmul : ∀ Z : Matrix (Fin a') (Fin (a + a')) (Fv F v), ∀ Ξ ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)),
      A (fun Y => GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, Y i j * Z i j) * Ξ Y) =
        fun Y => GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, Y i j * Z i j) * A Ξ Y := by
    intro Z Ξ hΞ
    obtain ⟨hξ, hιξ⟩ := hi1 Ξ hΞ
    obtain ⟨u, hu, hut, hchar⟩ := GlobalTheory.T.local_matrix_moment_surjective_conj F E σ B hT.base a' (a + a') _ _ _ _ G.V' G.W hT.geo.hV' hT.geo.hW v t Z
    have hchar' : ∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) x → x.map (piW t) = 0 →
        B.ψ (symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) x u) =
          GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, co x i j * Z i j) := hchar
    obtain ⟨ξ₁, ⟨hξ₁, hact₁⟩, -⟩ := hex2 u hu (ιi Ξ) hξ
    have e1 : ι ξ₁ = fun Y => GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, Y i j * Z i j) * Ξ Y := by
      funext Y
      obtain ⟨x, hx, hxt, hcx⟩ := hsurj Y
      have hcx' : co x = Y := hcx
      rw [← hcx', hL.mult u hu hut (ιi Ξ) hξ ξ₁ hξ₁ hact₁ x hx hxt, hιξ, hchar' x hx hxt]
    have e2 : ιi (fun Y => GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, Y i j * Z i j) * Ξ Y) = ξ₁ := by
      rw [← e1]; exact hi2 ξ₁ hξ₁
    obtain ⟨hTξ, hTa⟩ := hTspec (ιi Ξ) hξ
    obtain ⟨ξ₄, ⟨hξ₄, hact₄⟩, -⟩ := hex2 _ (at_conj u hu) (T (ιi Ξ)) hTξ
    obtain ⟨-, hTa₁⟩ := hTspec ξ₁ hξ₁
    have e3 : ξ₄ = T ξ₁ := GlobalTheory.T.theta_pair_local_schwartz_action F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hP' v (g, h) u (ιi Ξ) ξ₁
      (T (ιi Ξ)) (T ξ₁) ξ₄ hξ hξ₁ hTξ hact₁ hTa hTa₁ hact₄
    funext Y
    obtain ⟨x, hx, hxt, hcx⟩ := hsurj Y
    have hcx' : co x = Y := hcx
    have e4 : co (mat g * x * (mat h)ᵀ) = giᵀ * Y * hi := by rw [hco_act, hcx']
    have hs : symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) (mat g * x * (mat h)ᵀ) (mat g * u * (mat h)ᵀ) =
        symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) x u := GlobalTheory.T.symplectic_form_unitary_invariant F E σ a' (a + a') G.V' G.W g h x u
    show ι (T (ιi (fun Y => GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, Y i j * Z i j) * Ξ Y))) (giᵀ * Y * hi) =
      GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, Y i j * Z i j) * ι (T (ιi Ξ)) (giᵀ * Y * hi)
    rw [e2, ← e3, ← e4, hL.mult _ (at_conj u hu) (hut_map u _ hut) (T (ιi Ξ)) hTξ ξ₄ hξ₄ hact₄ _ (at_conj x hx)
      (hut_map x _ hxt), hs, hchar' x hx hxt, hcx']
  obtain ⟨cc, hcc⟩ := _root_.GlobalTheory.SchurLin.schur_linear_model (Fv F v) (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.SchrSB.continuous_psiAt B.ψ hT.base.std.1 v)
    (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hT.base.std v) a' (a + a') A hadd hsmul htr hmul
  have hιφ : ι φ ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) := hL.bij.mapsTo hφ
  have eT : φ₁ = T φ := (hex1 g hg h hh φ hφ).unique ⟨hφ₁, hacts⟩ (hTspec φ hφ)
  refine ⟨cc, ⟨gtᵀ, giᵀ, hPP', hPP⟩, ⟨ht', hi, hh1, hh2⟩, fun Y => ?_⟩
  have key := congrFun (hcc (ι φ) hιφ) (gtᵀ * Y * ht')
  change ι (T (ιi (ι φ))) (giᵀ * (gtᵀ * Y * ht') * hi) = cc * ι φ (gtᵀ * Y * ht') at key
  have ee : giᵀ * (gtᵀ * Y * ht') * hi = Y := by
    simp only [← Matrix.mul_assoc, hPP, Matrix.one_mul]
    rw [Matrix.mul_assoc, hh1, Matrix.mul_one]
  rw [hi2 φ hφ, ← eT, ee] at key
  exact key

end GlobalTheory.OppLinOp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFinitePresentationOfNilpotentThickening
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

open scoped TensorProduct

namespace GlobalTheory

open Algebra in
theorem finiteType_of_finiteType_quotient_map_nilpotent {P A : Type} [CommRing P] [CommRing A]
    [Algebra P A] (I : Ideal P) (hI : IsNilpotent I)
    [h : Algebra.FiniteType P (A ⧸ I.map (algebraMap P A))] : Algebra.FiniteType P A := by
  set J := I.map (algebraMap P A)
  obtain ⟨s, hs⟩ := h.out
  classical
  let t : Finset A := s.image (fun x => Quotient.out x)
  have hmk : (Ideal.Quotient.mkₐ P J) '' (t : Set A) = (s : Set (A ⧸ J)) := by
    ext x; simp [t]
  let C := Algebra.adjoin P (t : Set A)
  have key : ∀ b : A, ∃ c ∈ C, b - c ∈ J := by
    intro b
    have hb : Ideal.Quotient.mkₐ P J b ∈ (C.map (Ideal.Quotient.mkₐ P J)) := by
      rw [AlgHom.map_adjoin, hmk, hs]; trivial
    obtain ⟨c, hc, hcb⟩ := hb
    exact ⟨c, hc, Ideal.Quotient.eq.mp (by simpa using hcb.symm)⟩
  have base : (⊤ : Submodule P A) ≤ Subalgebra.toSubmodule C ⊔ I • ⊤ := by
    intro b _
    obtain ⟨c, hc, hbc⟩ := key b
    have : b - c ∈ I • (⊤ : Submodule P A) := by
      rw [Ideal.smul_top_eq_map]; exact hbc
    have := Submodule.add_mem_sup (show c ∈ Subalgebra.toSubmodule C from hc) this
    simpa using this
  have step : ∀ n : ℕ, (⊤ : Submodule P A) ≤ Subalgebra.toSubmodule C ⊔ (I ^ n) • ⊤ := by
    intro n
    induction n with
    | zero =>
      intro b _
      exact Submodule.mem_sup_right (by rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; trivial)
    | succ n ih =>
      refine ih.trans (sup_le le_sup_left ?_)
      calc (I ^ n) • (⊤ : Submodule P A) ≤ (I ^ n) • (Subalgebra.toSubmodule C ⊔ I • ⊤) :=
            Submodule.smul_mono le_rfl base
        _ = (I ^ n) • Subalgebra.toSubmodule C ⊔ (I ^ n) • (I • ⊤) := Submodule.smul_sup _ _ _
        _ ≤ Subalgebra.toSubmodule C ⊔ (I ^ (n + 1)) • ⊤ := by
            rw [pow_succ, Submodule.mul_smul]
            exact sup_le_sup_right Submodule.smul_le_right _
  obtain ⟨N, hN⟩ := hI
  have hC : Subalgebra.toSubmodule C = ⊤ := by
    have := step N
    rw [hN, Submodule.zero_eq_bot, Submodule.bot_smul, sup_bot_eq] at this
    exact top_le_iff.mp this
  exact ⟨⟨t, Algebra.toSubmodule_eq_top.mp hC⟩⟩

theorem finiteType_of_finiteType_tensor_nilpotent {P A R : Type} [CommRing P] [CommRing A]
    [CommRing R] [Algebra P A] [Algebra P R] (hs : Function.Surjective (algebraMap P R))
    (hn : IsNilpotent (RingHom.ker (algebraMap P R)))
    (h : (Algebra.TensorProduct.includeRight : R →ₐ[P] A ⊗[P] R).toRingHom.FiniteType) :
    Algebra.FiniteType P A := by
  have h1 : Algebra.FiniteType P (A ⊗[P] R) := by
    rw [← RingHom.finiteType_algebraMap,
      ← (Algebra.TensorProduct.includeRight : R →ₐ[P] A ⊗[P] R).comp_algebraMap]
    exact h.comp (RingHom.FiniteType.of_surjective _ hs)
  let f : P →ₐ[P] R := Algebra.ofId P R
  have hf : Function.Surjective f := hs
  let I : Ideal P := RingHom.ker f
  let e1 : (A ⧸ I.map (algebraMap P A)) ≃ₐ[P] A ⊗[P] (P ⧸ I) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).restrictScalars P
  let e2 : A ⊗[P] (P ⧸ I) ≃ₐ[P] A ⊗[P] R :=
    Algebra.TensorProduct.congr AlgEquiv.refl (Ideal.quotientKerAlgEquivOfSurjective hf)
  have h2 : Algebra.FiniteType P (A ⧸ I.map (algebraMap P A)) := h1.equiv (e1.trans e2).symm
  exact finiteType_of_finiteType_quotient_map_nilpotent I hn

theorem locallyOfFinitePresentation_specMap_of_isPullback_nilpotent {P R₁ A : CommRingCat.{0}}
    (f₁ : P ⟶ R₁) (hs : Function.Surjective f₁) (hn : IsNilpotent (RingHom.ker f₁.hom))
    [IsNoetherianRing P] (φ : P ⟶ A) {W : Scheme.{0}} (fst : W ⟶ Spec A) (snd : W ⟶ Spec R₁)
    (hsq : IsPullback fst snd (Spec.map φ) (Spec.map f₁)) (hsnd : LocallyOfFinitePresentation snd) :
    LocallyOfFinitePresentation (Spec.map φ) := by
  have h1 : LocallyOfFinitePresentation (pullback.snd (Spec.map φ) (Spec.map f₁)) := by
    have e : pullback.snd (Spec.map φ) (Spec.map f₁) = hsq.isoPullback.inv ≫ snd := by
      rw [Iso.eq_inv_comp, hsq.isoPullback_hom_snd]
    rw [e]
    exact MorphismProperty.comp_mem _ _ _ (locallyOfFinitePresentation_of_isOpenImmersion _) hsnd
  letI := φ.hom.toAlgebra
  letI := f₁.hom.toAlgebra
  have hT : LocallyOfFinitePresentation ((pullbackSpecIso P A R₁).inv ≫ pullback.snd _ _) :=
    MorphismProperty.comp_mem _ _ _ (locallyOfFinitePresentation_of_isOpenImmersion _) h1
  rw [pullbackSpecIso_inv_snd, LocallyOfFinitePresentation.SpecMap_iff] at hT
  rw [LocallyOfFinitePresentation.SpecMap_iff, ← RingHom.FinitePresentation.of_finiteType]
  exact finiteType_of_finiteType_tensor_nilpotent (A := A) hs hn (RingHom.FiniteType.of_finitePresentation hT)

theorem locallyOfFinitePresentation_of_nilpotent_thickening :
    ∀ (P R₁ : CommRingCat.{0}) (f₁ : P ⟶ R₁), Function.Surjective f₁ → IsNilpotent (RingHom.ker f₁.hom) → IsNoetherianRing P → ∀ (Y : Over (Spec P)) (Y₁ : Over (Spec R₁)) (j₁ : Y₁.left ⟶ Y.left), IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) → LocallyOfFinitePresentation Y₁.hom → LocallyOfFinitePresentation Y.hom := by
  intro P R₁ f₁ hs hn hP Y Y₁ j₁ hpb hY₁
  haveI : IsZariskiLocalAtSource @LocallyOfFinitePresentation.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFinitePresentation.{0})
    Y.left.affineOpenCover.openCover]
  intro i
  haveI : IsOpenImmersion (Y.left.affineOpenCover.f i) :=
    inferInstanceAs (IsOpenImmersion (Y.left.affineOpenCover.openCover.f i))
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Y.left.affineOpenCover.f i ≫ Y.hom)
  have hsq : IsPullback (pullback.fst (Y.left.affineOpenCover.f i) j₁)
      (pullback.snd (Y.left.affineOpenCover.f i) j₁ ≫ Y₁.hom) (Spec.map φ) (Spec.map f₁) := by
    rw [hφ]; exact (IsPullback.of_hasPullback (Y.left.affineOpenCover.f i) j₁).paste_vert hpb
  have hfin := GlobalTheory.locallyOfFinitePresentation_specMap_of_isPullback_nilpotent f₁ hs hn φ _ _ hsq
    (MorphismProperty.comp_mem _ _ _ (locallyOfFinitePresentation_of_isOpenImmersion _) hY₁)
  rw [hφ] at hfin
  exact hfin

end GlobalTheory
end

