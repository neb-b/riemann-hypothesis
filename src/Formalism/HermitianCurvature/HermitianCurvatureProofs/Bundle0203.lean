module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0193
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0010
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0195
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0043

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RaisingCompactSupport
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.GaugeNormPower

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section closed

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem aa_closed (P : (Mat k r → E) → Prop)
    (hRd : ∀ (X : Mat k r) (f : Mat k r → E), inLie k r X → P f → P (RdV X f))
    (hadd : ∀ f₁ f₂ : Mat k r → E, P f₁ → P f₂ → P (fun x => f₁ x + f₂ x))
    (hmul : ∀ (φ : Mat k r → ℂ), ContDiff ℝ (⊤ : ℕ∞) φ → ∀ f : Mat k r → E, P f → P (fun x => φ x • f x))
    (hzero : P (fun _ => 0)) (m : ℕ) (hm : m ≤ r) (u : ℂ) (f : Mat k r → E) (hf : P f) :
    P (C3.AAop k r m hm u f) :=
  _root_.UpperTheory.Reformulated.B.Qj20.aa_closed P hRd hadd hmul hzero m hm u f hf

theorem loc_add' {m : ℕ∞} {f₁ f₂ : Mat k r → E} {g : Mat k r} (h₁ : Loc m f₁ g) (h₂ : Loc m f₂ g) :
    Loc m (fun x => f₁ x + f₂ x) g := by
  obtain ⟨U₁, f₁', hU₁, hg₁, hf₁, he₁⟩ := h₁
  obtain ⟨U₂, f₂', hU₂, hg₂, hf₂, he₂⟩ := h₂
  exact ⟨U₁ ∩ U₂, fun x => f₁' x + f₂' x, hU₁.inter hU₂, ⟨hg₁, hg₂⟩,
    (hf₁.mono Set.inter_subset_left).add (hf₂.mono Set.inter_subset_right),
    fun x hx hxG => by show f₁ x + f₂ x = f₁' x + f₂' x; rw [he₁ x hx.1 hxG, he₂ x hx.2 hxG]⟩

theorem loc_smulFun {m : ℕ∞} (φ : Mat k r → ℂ) {V : Set (Mat k r)} (hV : IsOpen V)
    (hφ : ContDiffOn ℝ (m : WithTop ℕ∞) φ V) {f : Mat k r → E} {g : Mat k r} (hgV : g ∈ V) (h : Loc m f g) :
    Loc m (fun x => φ x • f x) g := by
  obtain ⟨U, f', hU, hgU, hf, he⟩ := h
  exact ⟨U ∩ V, fun x => φ x • f' x, hU.inter hV, ⟨hgU, hgV⟩,
    (hφ.mono Set.inter_subset_right).smul (hf.mono Set.inter_subset_left),
    fun x hx hxG => by show φ x • f x = φ x • f' x; rw [he x hx.1 hxG]⟩

theorem loc_zero' {m : ℕ∞} {g : Mat k r} : Loc m (fun _ => (0 : E)) g :=
  ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

theorem loc_AAop {f : Mat k r → E} {g : Mat k r} (h : Loc ⊤ f g) (m : ℕ) (hm : m ≤ r) (u : ℂ) :
    Loc ⊤ (C3.AAop k r m hm u f) g := by
  refine aa_closed (fun f => Loc ⊤ f g) (fun X f hX hf => ?_) (fun _ _ h₁ h₂ => loc_add' h₁ h₂)
    (fun φ hφ f hf => loc_smulFun φ isOpen_univ hφ.contDiffOn (Set.mem_univ g) hf) loc_zero' m hm u f h
  have hf' : Loc ((⊤ : ℕ∞) + 1) f g := by rw [top_add]; exact hf
  exact loc_RdV hX hf'

theorem zero_AAop {f : Mat k r → E} {U : Set (Mat k r)} (hU : IsOpen U) (h : ∀ x ∈ U, x ∈ GV k r → f x = 0)
    (m : ℕ) (hm : m ≤ r) (u : ℂ) : ∀ x ∈ U, x ∈ GV k r → C3.AAop k r m hm u f x = 0 := by
  refine aa_closed (fun f => ∀ x ∈ U, x ∈ GV k r → f x = 0) (fun X f hX hf => ?_)
    (fun f₁ f₂ h₁ h₂ x hx hxG => by simp [h₁ x hx hxG, h₂ x hx hxG])
    (fun φ _ f hf x hx hxG => by simp [hf x hx hxG]) (fun _ _ _ => rfl) m hm u f h
  intro x hx hxG
  rw [rdV_congr (f₂ := fun _ => (0 : E)) hU hx hxG hX (fun y hy hyG => hf y hy hyG)]
  simp [RdV]

end closed

end Formalism.FourierDecayAlt.P.GaugeNormPower

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.GaugeNormPower

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem raising_compact_support : PBN.AACpt := by
  intro k r Wp Wq _ _ _ _ Bs F y hF
  obtain ⟨hs, ⟨R, hR⟩, ⟨ε, hε, hG⟩⟩ := hF
  have hGc : Continuous fun g : Mat k r => Gf k r Bs.z Bs.z' g :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').continuous
  have hvan : ∀ U : Set (Mat k r), IsOpen U → (∀ x ∈ U, x ∈ GV k r → F x = 0) →
      ∀ x ∈ U, x ∈ GV k r → PBN.aaTop Bs y F x = 0 := by
    intro U hU hF0 x hx hxG
    have := zero_AAop hU hF0 r le_rfl ((y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) x hx hxG
    simp only [PBN.aaTop, this, smul_zero]
  have hUε : IsOpen {x : Mat k r | Gf k r Bs.z Bs.z' x < ε} := isOpen_lt hGc continuous_const
  have hFε : ∀ x ∈ {x : Mat k r | Gf k r Bs.z Bs.z' x < ε}, x ∈ GV k r → F x = 0 := by
    intro x hx hxG
    by_contra h
    exact absurd (hG x hxG h) (not_le.mpr hx)
  refine ⟨?_, ⟨R, ?_⟩, ⟨ε, hε, ?_⟩⟩
  · intro g₀ hg₀
    by_cases hlt : Gf k r Bs.z Bs.z' g₀ < ε
    · exact ⟨_, fun _ => 0, hUε, hlt, contDiffOn_const, fun x hx hxG => hvan _ hUε hFε x hx hxG⟩
    · push Not at hlt
      have hD : Dmin k r Bs.z Bs.z' g₀ (Fin.last (r + 1)) ≠ 0 := by
        intro h0
        have h1 : 0 ≤ Tz k r Bs.z * Tz k r Bs.z' * Complex.normSq (Dmin k r Bs.z Bs.z' g₀ ⟨r, by omega⟩) :=
          mul_nonneg (mul_pos Bs.T_pos Bs.T'_pos).le (Complex.normSq_nonneg _)
        simp only [Gf, h0, map_zero] at hlt
        linarith
      have hDc : ContDiff ℝ (⊤ : ℕ∞) fun x : Mat k r => Dmin k r Bs.z Bs.z' x (Fin.last (r + 1)) :=
        Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin Bs.z Bs.z' _
      have hV : IsOpen {x : Mat k r | Dmin k r Bs.z Bs.z' x (Fin.last (r + 1)) ≠ 0} :=
        isOpen_ne_fun hDc.continuous continuous_const
      have hloc : Loc ⊤ (C3.AAop k r r le_rfl ((y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) F) g₀ :=
        loc_AAop (hs g₀ hg₀) r le_rfl _
      exact loc_smulFun (fun x => (Dmin k r Bs.z Bs.z' x (Fin.last (r + 1)))⁻¹) hV
        (hDc.contDiffOn.inv fun x hx => hx) hD hloc
  · intro g hg hne
    by_contra hgt
    push Not at hgt
    have hU : IsOpen {x : Mat k r | R < gN x} := isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous
    refine hne (hvan _ hU (fun x hx hxG => ?_) g hgt hg)
    by_contra h
    exact absurd (hR x hxG h) (not_le.mpr hx)
  · intro g hg hne
    by_contra hlt
    push Not at hlt
    exact hne (hvan _ hUε hFε g hlt hg)

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RatioBound
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section pj

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
  (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (ys : List ℝ) {ε : ℝ}

theorem pj_sl (x₁ x₂ : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (y : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (h₁ : NV (p.T.bs j) ε x₁) (h₂ : NV (p.T.bs j) ε x₂) (hy : NV (p.T.bs j) ε y) :
    KB.pairJ (p.form j hj w) ys (x₁ + c • x₂) y =
      KB.pairJ (p.form j hj w) ys x₁ y + c * KB.pairJ (p.form j hj w) ys x₂ y :=
  PBG.pairJ_sesq_left P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w ys x₁ x₂ y c (PBG.decV_of_nice h₁)
    (PBG.decV_of_nice h₂) (PBG.decV_of_nice hy)

theorem pj_sr (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (y₁ y₂ : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : NV (p.T.bs j) ε x) (h₁ : NV (p.T.bs j) ε y₁) (h₂ : NV (p.T.bs j) ε y₂) :
    KB.pairJ (p.form j hj w) ys x (y₁ + c • y₂) =
      KB.pairJ (p.form j hj w) ys x y₁ + conj c * KB.pairJ (p.form j hj w) ys x y₂ :=
  PBG.pairJ_sesq_right P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w ys x y₁ y₂ c (PBG.decV_of_nice hx)
    (PBG.decV_of_nice h₁) (PBG.decV_of_nice h₂)

theorem pj_zero_l (y : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hy : NV (p.T.bs j) ε y) : KB.pairJ (p.form j hj w) ys 0 y = 0 := by
  have h := pj_sl p j hj w ys 0 0 y 1 nv_zero nv_zero hy
  simp only [one_smul, add_zero, one_mul] at h
  linear_combination -h

theorem pj_zero_r (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hx : NV (p.T.bs j) ε x) : KB.pairJ (p.form j hj w) ys x 0 = 0 := by
  have h := pj_sr p j hj w ys x 0 0 1 hx nv_zero nv_zero
  simp only [one_smul, add_zero, map_one, one_mul] at h
  linear_combination -h

theorem pj_smul (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (y : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c d : ℂ)
    (hx : NV (p.T.bs j) ε x) (hy : NV (p.T.bs j) ε y) :
    KB.pairJ (p.form j hj w) ys (c • x) (d • y) = c * conj d * KB.pairJ (p.form j hj w) ys x y := by
  have h1 := pj_sl p j hj w ys 0 x (d • y) c nv_zero hx (nv_smul d hy)
  have h2 := pj_sr p j hj w ys x 0 y d hx nv_zero hy
  rw [zero_add, pj_zero_l p j hj w ys _ (nv_smul d hy), zero_add] at h1
  rw [zero_add, pj_zero_r p j hj w ys x hx, zero_add] at h2
  rw [h1, h2]; ring

end pj

section deg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem uB_pos (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j) :
    uB S p F v ε j hj w h = (((√(nnS S h) / bS S h : ℝ) : ℂ)) •
      KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2) := by
  unfold uB; rw [dite_eq_left hh]

theorem uB_neg (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (h : C.LPt) (hh : ¬ D.IsLocPt h j) : uB S p F v ε j hj w h = 0 := by
  unfold uB; rw [dite_eq_right hh]

theorem waveG_smul' {k ρ : ℕ} {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp']
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (Bs : B.RealPlaceData k ρ Wp' Wq') (s : ℂ) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq' →L[ℂ] Wp')) (c : ℂ) :
    KB.waveG Bs s w (c • x) = c • KB.waveG Bs s w x := by
  have := PBG.waveG_add_smul Bs s w 0 x c
  rwa [zero_add, PBG.waveG_zero, zero_add] at this

theorem deg_uB (hDW : KB.DegWave) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (a : List C.Letter) (K : ℕ) (grid : Fin K → Fin (2 * j + 1) → ℝ)
    (hinj : ∀ b, Function.Injective (grid b)) (s : ℂ) (h h' : C.LPt) :
    s ^ K * (p v).form j hj a (KB.waveG ((p v).T.bs j) s a (uB S p F v ε j hj a h)) (uB S p F v ε j hj a h') =
      ∑ n : Fin K → Fin (2 * j + 1), ((∏ b, F7.lagCo (grid b) (n b) : ℝ) : ℂ) *
        KB.pairJ ((p v).form j hj a) (List.ofFn fun b => grid b (n b))
          (KB.waveG ((p v).T.bs j) s _ (uB S p F v ε j hj (KB.plusW (List.ofFn fun b => grid b (n b)) a) h))
          (uB S p F v ε j hj (KB.minusW (List.ofFn fun b => grid b (n b)) a) h') := by
  have hgpos := g_pos_of_built hB
  by_cases hloc : D.IsLocPt h j ∧ D.IsLocPt h' j
  · obtain ⟨hh, hh'⟩ := hloc
    have hH : D.IsLocPt (stdS S h) j := (PBD.isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
    have hH' : D.IsLocPt (stdS S h') j := (PBD.isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hh'
    have hdeg := hDW (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (F v ε) j hj a (stdS S h) (stdS S h') hH hH' K
      grid s LinearMap.id (fun ε x hx => hx) (hF v ε hε) hinj
    simp only [LinearMap.id_apply, onOld_id] at hdeg
    set Dh : ℂ := (((√(nnS S h) / bS S h : ℝ) : ℂ)) with hDh
    set Dh' : ℂ := (((√(nnS S h') / bS S h' : ℝ) : ℂ)) with hDh'
    rw [uB_pos S p F v ε j hj a h hh, uB_pos S p F v ε j hj a h' hh', waveG_smul']
    obtain ⟨ε2, hε2, hs, hs'⟩ := nv_pair (slv_nv (p v) (hF v ε hε) j hj a (stdS S h) hH)
      (slv_nv (p v) (hF v ε hε) j hj a (stdS S h') hH')
    have hws := PBFV.waveG_nice ((p v).T.bs j) ε2 s a _ hs
    rw [form_smul_l (p v) j hj a _ _ _ hws (nv_smul _ hs'), form_smul_r (p v) j hj a _ _ _ hws hs']
    have hL : s ^ K * (Dh * (conj Dh' * (p v).form j hj a (KB.waveG ((p v).T.bs j) s a
        (KB.slv (p v).T (F v ε) j hj a (stdS S h) ((stdS_size S h).trans hh.2)))
        (KB.slv (p v).T (F v ε) j hj a (stdS S h') ((stdS_size S h').trans hh'.2)))) =
        Dh * conj Dh' * (s ^ K * (p v).form j hj a (KB.waveG ((p v).T.bs j) s a
        (KB.slv (p v).T (F v ε) j hj a (stdS S h) hH.2)) (KB.slv (p v).T (F v ε) j hj a (stdS S h') hH'.2)) := by
      ring
    rw [hL, hdeg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    set ys := List.ofFn fun b => grid b (n b) with hys
    obtain ⟨ε3, hε3, hp, hm⟩ := nv_pair (slv_nv (p v) (hF v ε hε) j hj (KB.plusW ys a) (stdS S h) hH)
      (slv_nv (p v) (hF v ε hε) j hj (KB.minusW ys a) (stdS S h') hH')
    have hwp := PBFV.waveG_nice ((p v).T.bs j) ε3 s _ _ hp
    rw [uB_pos S p F v ε j hj (KB.plusW ys a) h hh, uB_pos S p F v ε j hj (KB.minusW ys a) h' hh', waveG_smul',
      pj_smul (p v) j hj a ys _ _ _ _ hwp hm]
    ring
  · have h0 : uB S p F v ε j hj a h = 0 ∨ uB S p F v ε j hj a h' = 0 := by
      by_cases hh : D.IsLocPt h j
      · exact Or.inr (uB_neg S p F v ε j hj a h' fun hh' => hloc ⟨hh, hh'⟩)
      · exact Or.inl (uB_neg S p F v ε j hj a h hh)
    obtain ⟨ε1, hε1, hx, hx'⟩ := nv_pair (uB_nv hB F hF v ε hε j hj a h) (uB_nv hB F hF v ε hε j hj a h')
    have hwx := PBFV.waveG_nice ((p v).T.bs j) ε1 s a _ hx
    have lhs0 : (p v).form j hj a (KB.waveG ((p v).T.bs j) s a (uB S p F v ε j hj a h)) (uB S p F v ε j hj a h') = 0 := by
      rcases h0 with h0 | h0
      · rw [h0, PBG.waveG_zero, form_zero_l (p v) j hj a _ hx']
      · rw [h0, form_zero_r (p v) j hj a _ hwx]
    rw [lhs0, mul_zero]
    symm
    refine Finset.sum_eq_zero fun n _ => ?_
    set ys := List.ofFn fun b => grid b (n b) with hys
    obtain ⟨ε3, hε3, hp, hm⟩ := nv_pair (uB_nv hB F hF v ε hε j hj (KB.plusW ys a) h)
      (uB_nv hB F hF v ε hε j hj (KB.minusW ys a) h')
    have hwp := PBFV.waveG_nice ((p v).T.bs j) ε3 s _ _ hp
    by_cases hh : D.IsLocPt h j
    · rw [uB_neg S p F v ε j hj (KB.minusW ys a) h' fun hh' => hloc ⟨hh, hh'⟩, pj_zero_r (p v) j hj a ys _ hwp, mul_zero]
    · rw [uB_neg S p F v ε j hj (KB.plusW ys a) h hh, PBG.waveG_zero, pj_zero_l (p v) j hj a ys _ hm, mul_zero]

end deg

section kern

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem gam_pos (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (j : ℕ) : 0 < ΓS S j := by
  have hgpos := g_pos_of_built hB
  have hrd := PBD.rd_pos' E
  unfold ΓS
  exact PBD.gamLev_pos _ _ _ _ (by unfold D.kapG; positivity) (by unfold D.deG; positivity) _

def uY (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (Y : Finset C.LPt) (h : C.LPt) :
    Wd.Ix (Fin w.length) → B.Mat S.G.k (S.G.r - j) → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :=
  if h ∈ Y then uB S p F v ε j hj w h else 0

theorem uY_mem (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (Y : Finset C.LPt) (h : C.LPt) (hh : h ∈ Y) :
    uY S p F v ε j hj w Y h = uB S p F v ε j hj w h := by
  unfold uY; rw [if_pos hh]

theorem blockPSD_congr {α : Type} {Y : Finset α} {a a' b b' w w' : α → α → ℂ}
    (ha : ∀ x ∈ Y, ∀ y ∈ Y, a x y = a' x y) (hw : ∀ x ∈ Y, ∀ y ∈ Y, w x y = w' x y)
    (hb : ∀ x ∈ Y, ∀ y ∈ Y, b x y = b' x y) (h : KB.BlockPSD Y Y a w b) : KB.BlockPSD Y Y a' w' b' := by
  rw [PBA.blockPSD_iff] at h ⊢
  refine psd_congr (fun x hx y hy => ?_) h
  cases x with
  | inl x =>
    cases y with
    | inl y => exact ha x (Finset.inl_mem_disjSum.1 hx) y (Finset.inl_mem_disjSum.1 hy)
    | inr y => exact hw x (Finset.inl_mem_disjSum.1 hx) y (Finset.inr_mem_disjSum.1 hy)
  | inr x =>
    cases y with
    | inl y =>
      show conj (w y x) = conj (w' y x)
      rw [hw y (Finset.inl_mem_disjSum.1 hy) x (Finset.inr_mem_disjSum.1 hx)]
    | inr y => exact hb x (Finset.inr_mem_disjSum.1 hx) y (Finset.inr_mem_disjSum.1 hy)

end kern

theorem lam_div_theta {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (hinj : ∀ b, Function.Injective (grid b))
    (n : Fin K → Fin (d + 1)) :
    0 < F7.thGrid grid n ∧
      |∏ b, F7.lagCo (grid b) (n b)| / F7.thGrid grid n = ∏ b, ∑ i, |F7.lagCo (grid b) i| := by
  have hs : ∀ b, 0 < ∑ i, |F7.lagCo (grid b) i| := fun b =>
    lt_of_lt_of_le (abs_pos.2 (PBD.lagCo_ne_zero _ (hinj b) (n b)))
      (Finset.single_le_sum (f := fun i => |F7.lagCo (grid b) i|) (fun i _ => abs_nonneg _) (Finset.mem_univ _))
  have hl : ∀ b, 0 < |F7.lagCo (grid b) (n b)| := fun b => abs_pos.2 (PBD.lagCo_ne_zero _ (hinj b) (n b))
  have hth : 0 < F7.thGrid grid n := Finset.prod_pos fun b _ => div_pos (hl b) (hs b)
  refine ⟨hth, ?_⟩
  unfold F7.thGrid
  rw [Finset.abs_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  field_simp [(hl b).ne', (hs b).ne']

theorem ratio_bound {K : ℕ} (ys : Fin K → ℝ) (Pv qv : ℝ → ℝ) (Λ T Γ sa B Xc : ℝ) (hΓ : 0 < Γ) (hsa : 0 < sa)
    (hq : ∀ b, 0 < qv (ys b)) (hP : ∀ b, Pv (ys b) ≠ 0) (hP' : ∀ b, Pv (ys b + 1) ≠ 0)
    (hnode : ∀ b, |Pv (ys b) * Pv (ys b + 1)| / qv (ys b) ≤ B ^ 2) (hΛ : 0 ≤ Λ) (hT : 0 ≤ T) (hB0 : 0 ≤ B)
    (hX : Λ * T ^ K * B ^ K ≤ Xc ^ K) :
    (Λ * T ^ K * (1 / (Γ * sa))) ^ 2 / ((∏ b, qv (ys b)) * (1 / (Γ * ((∏ b, |Pv (ys b)|) * sa))) *
      (1 / (Γ * ((∏ b, |Pv (ys b + 1)|) * sa)))) ≤ (Xc ^ K) ^ 2 := by
  have hQ : 0 < ∏ b, qv (ys b) := Finset.prod_pos fun b _ => hq b
  have hPp : 0 < ∏ b, |Pv (ys b)| := Finset.prod_pos fun b _ => abs_pos.2 (hP b)
  have hPm : 0 < ∏ b, |Pv (ys b + 1)| := Finset.prod_pos fun b _ => abs_pos.2 (hP' b)
  have e : (Λ * T ^ K * (1 / (Γ * sa))) ^ 2 / ((∏ b, qv (ys b)) * (1 / (Γ * ((∏ b, |Pv (ys b)|) * sa))) *
      (1 / (Γ * ((∏ b, |Pv (ys b + 1)|) * sa)))) =
      (Λ * T ^ K) ^ 2 * ∏ b, (|Pv (ys b) * Pv (ys b + 1)| / qv (ys b)) := by
    rw [Finset.prod_div_distrib]
    simp only [abs_mul, Finset.prod_mul_distrib]
    field_simp
  rw [e]
  have hprod : ∏ b, (|Pv (ys b) * Pv (ys b + 1)| / qv (ys b)) ≤ (B ^ 2) ^ K := by
    calc ∏ b, (|Pv (ys b) * Pv (ys b + 1)| / qv (ys b)) ≤ ∏ _b : Fin K, B ^ 2 :=
          Finset.prod_le_prod₀ (fun b _ => div_nonneg (abs_nonneg _) (hq b).le) fun b _ => hnode b
      _ = (B ^ 2) ^ K := by simp
  have h0 : 0 ≤ Λ * T ^ K * B ^ K := by positivity
  calc (Λ * T ^ K) ^ 2 * ∏ b, (|Pv (ys b) * Pv (ys b + 1)| / qv (ys b)) ≤ (Λ * T ^ K) ^ 2 * (B ^ 2) ^ K :=
        mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
    _ = (Λ * T ^ K * B ^ K) ^ 2 := by ring
    _ ≤ (Xc ^ K) ^ 2 := pow_le_pow_left₀ h0 hX 2

end

end Formalism.FourierDecayAlt.P.PBL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeActionHolds
section
open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace RightTypeActionHermitianCurvature

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)} {i : Fin (r + 1)} {mm : ℕ∞}

theorem mem_right (hD : IsDom k r z z' i D) {g h : Mx k r} (hg : g ∈ Glev k r i ∩ D)
    (hh : h ∈ UWset k r z') : g * h ∈ Glev k r i ∩ D := by
  have := Qx8.dom_mem hD hg (Qx8.uw_one z) (Qx8.nlev_one _) hh (Qx8.nlev_one _)
  simpa using this

theorem J_right (hπ' : IsCRepOn (UWset k r z') π') (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D) {g h : Mx k r}
    (hg : g ∈ Glev k r i ∩ D) (hh : h ∈ UWset k r z') : J (g * h) = (J g).comp (π' h) := by
  have e1 := hJ.2.2.2 g hg 1 (Qx8.uw_one z) 1 (Qx8.uw_one z')
  have e2 := hJ.2.2.2 g hg 1 (Qx8.uw_one z) h hh
  rw [Matrix.one_mul, Matrix.mul_one, hπ'.1] at e1
  rw [Matrix.one_mul] at e2
  have e3 : (J g).comp (1 : Wq →L[ℂ] Wq) = J g := ContinuousLinearMap.comp_id _
  rw [e3] at e1
  rw [e2, ← ContinuousLinearMap.comp_assoc, ← e1]

theorem rd_right (hD : IsDom k r z z' i D) (hπ' : IsCRepOn (UWset k r z') π')
    (hc : ContinuousOn π' (UWset k r z')) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wq →L[ℂ] Wq}
    (hF : ∀ g ∈ Glev k r i ∩ D, F g = (J g).comp B) {X : Mx k r} (hX : QrD.InLieW k r z' X)
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) : RdV X F g = (J g).comp ((QrD.dOp π' X).comp B) := by
  have h := QrD.dOp_hasDeriv hπ' hc hX
  let L : (Wq →L[ℂ] Wq) →L[ℂ] (Wq →L[ℂ] Wp) :=
    (ContinuousLinearMap.compL ℂ Wq Wq Wp (J g)).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wq).flip B)
  have h2 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have h3 : (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) =
      (L.restrictScalars ℝ) ∘ fun t : ℝ => π' (NormedSpace.exp ((t : ℂ) • X)) := by
    funext t
    rw [hF _ (mem_right hD hg (QrD.exp_uw hX t)), J_right hπ' hJ hg (QrD.exp_uw hX t)]
    rfl
  unfold RdV
  rw [h3]
  exact h2.deriv

theorem rz_right (hD : IsDom k r z z' i D) (hπ' : IsCRepOn (UWset k r z') π')
    (hc : ContinuousOn π' (UWset k r z')) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wq →L[ℂ] Wq}
    (hF : ∀ g ∈ Glev k r i ∩ D, F g = (J g).comp B) {Z : Mx k r}
    (h1 : QrD.InLieW k r z' (hpart1 (Hpk k r) Z)) (h2 : QrD.InLieW k r z' (hpart2 (Hpk k r) Z))
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    RZ (Hpk k r) Z F g = (J g).comp ((QrD.ecOp π' Z).comp B) := by
  unfold RZ QrD.ecOp
  rw [rd_right hD hπ' hc hJ hF h1 hg, rd_right hD hπ' hc hJ hF h2 hg]
  ext v
  simp

theorem fold_right (hD : IsDom k r z z' i D) (hπ' : IsCRepOn (UWset k r z') π')
    (hc : ContinuousOn π' (UWset k r z')) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    (L : List (ℂ × Mx k r))
    (hL : ∀ p ∈ L, QrD.InLieW k r z' (hpart1 (Hpk k r) p.2) ∧ QrD.InLieW k r z' (hpart2 (Hpk k r) p.2)) :
    ∃ B : Wq →L[ℂ] Wq,
      (∀ g ∈ Glev k r i ∩ D,
        (L.map fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + RZ (Hpk k r) p.2 y).foldr (fun T h => T h) J g =
          (J g).comp B) ∧
      ∀ v, B v = (L.map fun p => fun y : Wq => p.1 • y + EcRep (Hpk k r) π' p.2 y).foldr (fun T h => T h) v := by
  induction L with
  | nil => exact ⟨1, fun g _ => (ContinuousLinearMap.comp_id _).symm, fun v => rfl⟩
  | cons p L ih =>
    obtain ⟨B, hB1, hB2⟩ := ih fun q hq => hL q (by simp [hq])
    have hp := hL p (by simp)
    refine ⟨p.1 • B + (QrD.ecOp π' p.2).comp B, fun g hg => ?_, fun v => ?_⟩
    · simp only [List.map_cons, List.foldr_cons, Pi.add_apply, Pi.smul_apply]
      rw [rz_right hD hπ' hc hJ hB1 hp.1 hp.2 hg, hB1 g hg]
      ext v
      simp
    · simp only [List.map_cons, List.foldr_cons]
      rw [← hB2 v, QrD.ecRep_eq hπ' hc hp.1 hp.2]
      rfl

end RightTypeActionHermitianCurvature

theorem right_type_action_holds : RightTypeAction0 := by
  intro Wp Wq _ _ _ _ _ k r m z z' π π' D mm _ _ hD hπ' hc J hJ g hg Bs hB w v
  unfold capR capRep qmF
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, Pi.smul_apply, _root_.sum_apply, _root_.smul_apply,
    map_sum, map_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  obtain ⟨B, hB1, hB2⟩ := RightTypeActionHermitianCurvature.fold_right hD hπ' hc hJ
    (List.ofFn fun j : Fin m => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0 : ℂ), unitB (Hpk k r) Bs (σ j) j))
    (by
      intro p hp
      rw [List.mem_ofFn] at hp
      obtain ⟨j, rfl⟩ := hp
      exact QrD.frame_lie hB (σ j) j)
  have e1 := hB1 g hg
  have e2 := hB2 v
  simp only [List.map_ofFn, Function.comp_def, ite_smul, zero_smul] at e1 e2
  simp only [id]
  rw [e1, ← e2]
  rfl

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end
end

