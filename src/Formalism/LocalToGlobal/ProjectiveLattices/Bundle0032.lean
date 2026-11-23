module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
public import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0030
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.DepRun
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

theorem satDir_of (hS : ChartSaturated Xo c) {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (C : IntChart T io y) :
    SatDir T (letI := io.toAlgebra; C.ch.uvec) := by
  intro τ
  obtain ⟨⟨w, emb, hw, hbasis⟩, -⟩ := hS T io y C τ
  have huv := C.gen.1.2.2.2.2.2.2
  choose A hA using fun m : Fin (chD C.ch) => (hbasis (Pi.single m 1)).exists
  have hAw : (Matrix.of A) * (Matrix.of w) = 1 := by
    ext m j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    rw [hA m j, Pi.single_apply]
    by_cases hjm : j = m
    · subst hjm; simp
    · simp [hjm, Ne.symm hjm]
  have hwA : (Matrix.of w) * (Matrix.of A) = 1 := by
    first
      | exact mul_eq_one_comm.mp hAw
      | exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hAw
  refine ⟨fun i j => A j (emb i), fun i i' => ?_⟩
  letI := io.toAlgebra
  have e1 : ∀ j, C.ch.uvec ⟨τ, i'⟩ j * algebraMap T.V T.Fr (A j (emb i)) =
      algebraMap T.V T.Fr (w (emb i') j * A j (emb i)) := by
    intro j
    rw [huv, map_mul, hw]
  refine (Finset.sum_congr rfl (fun j _ => e1 j)).trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum]
  have h3 := congrFun (congrFun hwA (emb i')) (emb i)
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply] at h3
  rw [h3]
  by_cases hii : i' = i
  · subst hii; simp
  · rw [if_neg (fun h' => hii (emb.injective h')), if_neg hii, map_zero]

theorem nuW_le_crude (hE : IntChartEx Xo c) (hS : ChartSaturated Xo c) (la : HeightOneSpectrum (𝓞 c.F)) (k : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ha : DomW Dw a) (hn : Fintype.card (Lt1 Dw) ≤ n) :
    nuW Xo c la k a n ≤ max 0 (crudeBd la (DF Dw a) : EReal) := by
  unfold nuW
  refine max_le_max le_rfl ?_
  unfold nuSup
  refine iSup_le fun T => iSup_le fun io => iSup_le fun e => iSup_le fun ho =>
    iSup_le fun y => iSup_le fun hy => ?_
  obtain ⟨C⟩ := hE T io y hy
  unfold nuLoc
  refine (iInf_le _ C).trans ?_
  letI := io.toAlgebra
  exact (crude_inf C.ch.B C.ch.h C.ch.gauge H.w0 k C.ch.uvec (satDir_of hS C) a n ha hn ho).1

omit [StarRing (𝓞 E)] in
theorem card_Lt1_le_finrank_mul : Fintype.card (Lt1 Dw) ≤ Module.finrank ℚ E * (Dw.p + Dw.q) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc ∑ τ : E →+* ℂ, Dw.mult τ ≤ ∑ _τ : E →+* ℂ, (Dw.p + Dw.q) := by
        apply Finset.sum_le_sum
        intro τ _
        unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult
        split_ifs <;> omega
    _ = Module.finrank ℚ E * (Dw.p + Dw.q) := by
        rw [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, smul_eq_mul]

end

variable {D : D7}

theorem nuFinAt_of (T : Core D) (hp : T.Q.Pins) (Dd : DepData D.host.E) [StarRing (𝓞 D.host.E)]
    (hw : ∀ j, InR D j → (∀ τ, Antitone fun i => Dd.aL j (τ, i)) ∧ 2 * D.R.f * D.R.r ≤ Dd.nW j)
    (hE : ∀ j, InR D j → IntChartEx (T.Q.Xo j) T.Q.c) (hS : ∀ j, InR D j → ChartSaturated (T.Q.Xo j) T.Q.c) :
    NuFinAt T Dd := by
  intro j hj la
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    rw [(hp.2.2.2 j hj).1, (hp.2.2.2 j hj).2.1]
    have := hj.1; have := hj.2
    simp only [Ranks.sigW, Ranks.r]; omega
  have hn : Fintype.card (Lt1 (T.Q.Dw j)) ≤ Dd.nW j := by
    refine card_Lt1_le_finrank_mul.trans ?_
    rw [hfr, hr]; exact (hw j hj).2
  refine ne_top_of_le_ne_top ?_ (nuW_le_crude (hE j hj) (hS j hj) la _ _ _ (fun τ i i' h => (hw j hj).1 τ h) hn)
  rcases le_total (0 : EReal) (crudeBd la (DF (T.Q.Dw j) (Dd.aL j)) : EReal) with h | h
  · rw [max_eq_right h]; exact EReal.coe_ne_top _
  · rw [max_eq_left h]; exact EReal.zero_ne_top

def depRun (T : Core D) (EX : ErrX D) (Tn : ℕ+) (vd : ℕ → ℝ) (wL wF ka : ∀ j, WeightFamilies.Wt D j) : DepData D.host.E :=
  depDataOf T EX Tn vd (fun j => wtA (wL j)) (fun j => wtA (wF j)) (fun j => (wL j).n)
    (fun j => ∑ τ, ∑ i, (ka j).aP τ i) fun j => ∑ τ, ∑ i, (ka j).aM τ i

theorem lawsPi_depRun [StarRing (𝓞 D.host.E)] {T : Core D} (h : LawsM T) (EX : ErrX D) (Tn : ℕ+) (vd : ℕ → ℝ) (wL wF ka : ∀ j, WeightFamilies.Wt D j)
    (hn : ∀ j, InR D j → 2 * D.R.f * D.R.r ≤ (wL j).n) : LawsPi T (depRun T EX Tn vd wL wF ka) := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, rfl, ?_, ?_, ?_⟩
  · exact tPos_depDataOf ..
  · exact fun j hj => ⟨(dom_wtA (wL j)).1, hn j hj⟩
  · exact piSplit_depDataOf ..
  · exact piHalf_depDataOf _ _ _ _ _ _ _ _ _ h

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.MuValFix
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem MuVal.eq_one_of_fixed {D : D7} {V : HSp D} {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ}
    (h : MuVal V χ mu) (y : (AE D)ˣ)
    (hy : sigR (AF D.host.F) D.sp.cm.sig (y : AE D) = y) : χ y = 1 := by
  obtain ⟨x, hx⟩ := h.1 1
  have hxy : IsDetRoot V 1 (x * y) := by
    unfold IsDetRoot at hx ⊢
    rw [Units.val_mul, map_mul, hy, ← mul_assoc, ← hx]
  have e2 := h.2 1 (x * y) hxy
  rw [h.2 1 x hx, map_mul] at e2
  have e3 : χ x * 1 = χ x * χ y := by
    apply Subtype.ext
    simpa [Circle.coe_mul] using e2
  exact (mul_left_cancel e3).symm

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.OneCusp
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open scoped ComplexConjugate

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem not_isIso_of_p0_zero (X : Data E r) (h0 : X.p0 = 0) (ξ : Fin r → E) : ¬ X.IsIso ξ := by
  rintro ⟨-, hh, hne⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ X.Ψ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h : ComplexEmbedding.conjugate τ ∈ X.Ψ
    · exact ⟨_, h⟩
    · exact ⟨τ, (X.cmType τ).2 h⟩
  obtain ⟨P, hP, hG⟩ := X.signature ⟨τ, hτ⟩
  set v : Fin r → ℂ := fun a => τ (ξ a) with hv
  set w : Fin r → ℂ := P⁻¹.mulVec v with hw
  have hPw : P.mulVec w = v := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hP), Matrix.one_mulVec]
  have h1 : hermC τ X.Gm v v = 0 := by
    have := congrArg τ hh
    rw [map_zero] at this
    rw [← this]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hermC, herm, map_sum, map_mul, hv, cc, IsCMField.complexEmbedding_complexConj]
  have h2 : hermC τ X.Gm v v = ∑ a, ∑ b, w a * gram τ X.Gm P a b * conj (w b) := by
    have sw : ∀ f : Fin r → Fin r → Fin r → Fin r → ℂ,
        ∑ x, ∑ y, ∑ a, ∑ b, f x y a b = ∑ a, ∑ b, ∑ x, ∑ y, f x y a b := fun f =>
      calc ∑ x, ∑ y, ∑ a, ∑ b, f x y a b = ∑ x, ∑ a, ∑ y, ∑ b, f x y a b :=
            Finset.sum_congr rfl fun x _ => Finset.sum_comm
        _ = ∑ a, ∑ x, ∑ y, ∑ b, f x y a b := Finset.sum_comm
        _ = ∑ a, ∑ x, ∑ b, ∑ y, f x y a b :=
            Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
        _ = ∑ a, ∑ b, ∑ x, ∑ y, f x y a b := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    have L : ∀ x y, P.mulVec w x * τ (X.Gm x y) * conj (P.mulVec w y) =
        ∑ a, ∑ b, w a * (P x a * τ (X.Gm x y) * conj (P y b)) * conj (w b) := by
      intro x y
      simp only [Matrix.mulVec, dotProduct]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul]; ring
    rw [← hPw]
    simp only [hermC, L, gram, col, Matrix.of_apply]
    rw [sw]
    simp only [Finset.mul_sum, Finset.sum_mul]
  have h3 : ∑ a, Complex.normSq (w a) = 0 := by
    rw [h2, hG] at h1
    have : ∑ a, (Complex.normSq (w a) : ℂ) = 0 := by
      rw [← neg_eq_zero, ← Finset.sum_neg_distrib, ← h1]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_eq_single a (fun b _ hb => by simp [Matrix.diagonal_apply_ne _ hb.symm]) (by simp)]
      simp [sgn, h0, Complex.mul_conj]
    exact_mod_cast this
  have h4 : w = 0 := funext fun a => Complex.normSq_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg fun a _ => Complex.normSq_nonneg _).mp h3 a (Finset.mem_univ a))
  apply hne
  funext a
  have : v a = 0 := by rw [← hPw, h4, Matrix.mulVec_zero]; rfl
  exact (map_eq_zero τ).mp this

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

theorem dom_zero : Dom (0 : (E →+* ℂ) × ℕ → ℕ) 0 := ⟨fun _ _ _ _ => le_rfl, Even.zero⟩

end

variable {D : D7} {T : Core D}

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ReadQuot
section
noncomputable section

namespace Formalism.L2.Pj

open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct Pointwise

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem volPair_of_tie (hT : VolTieG D) (V : HSp D) (hs : V.SigOK) : ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2 := by
  have h := hT V hs
  clear hT
  obtain ⟨⟨μ, hμ⟩, hb⟩ := h
  obtain ⟨⟨𝓕, h𝓕⟩, -⟩ := hb μ hμ
  refine ⟨(μ, 𝓕), ?_⟩
  exact ⟨hμ, h𝓕⟩

theorem quotSupp_of (V : HSp D) (hV : FinVol V) (hP : ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2) :
    QuotSupp V := by
  intro φ hφc hφinv hae g0
  by_contra hg0
  haveI : Countable (GQ V) := by
    unfold GQ
    exact Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  have hvp : IsVolPair D V (volPair V).1 (volPair V).2 := by
    have e : volPair V = hP.choose := by
      unfold volPair
      rw [dite_eq_left hP]
    rw [e]
    exact hP.choose_spec
  haveI : (volPair V).1.IsHaarMeasure := hvp.1.1
  haveI : BorelSpace (GA D V) := by
    first
    | exact Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA
    | exact Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA _ _
  haveI : MeasurableMul (GA D V) := by
    first
    | exact Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA
    | exact Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA _ _
  haveI : MeasurableConstSMul (GQ V) (GA D V) := ⟨fun c => measurable_const_mul (c : GA D V)⟩
  haveI : SMulInvariantMeasure (GQ V) (GA D V) (volPair V).1 :=
    ⟨fun c s _ => measure_preimage_mul (volPair V).1 (c : GA D V) s⟩
  let O : Set (GA D V) := {g | φ g ≠ 0}
  have hO : IsOpen O := isOpen_ne_fun hφc continuous_const
  have hOinv : ∀ γ : GQ V, γ • O = O := by
    intro γ
    ext g
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨x, hx, rfl⟩
      show φ ((γ : GA D V) * x) ≠ 0
      rw [hφinv _ γ.2]
      exact hx
    · intro hg
      refine ⟨((γ⁻¹ : GQ V) : GA D V) * g, ?_, ?_⟩
      · show φ (((γ⁻¹ : GQ V) : GA D V) * g) ≠ 0
        rw [hφinv _ (γ⁻¹).2]
        exact hg
      · show (γ : GA D V) * (((γ⁻¹ : GQ V) : GA D V) * g) = g
        rw [← mul_assoc, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, one_mul]
  have hpos : 0 < (volPair V).1 O := hO.measure_pos _ ⟨g0, hg0⟩
  have hOF : (volPair V).1 (O ∩ (volPair V).2) ≠ 0 := fun h =>
    hpos.ne' (hvp.2.measure_zero_of_invariant O hOinv h)
  let S : Set (AutQ V) := {q | ¬ onQ V φ q = (0 : AutQ V → ℂ) q}
  have h0 : muQ1 V S = 0 := ae_iff.mp hae
  have hS : muQ V S = 0 := by
    unfold muQ1 at h0
    rw [if_pos (show muQ V Set.univ ≠ 0 ∧ muQ V Set.univ ≠ ⊤ from hV), Measure.smul_apply,
      smul_eq_mul] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (ENNReal.inv_eq_zero.mp h) hV.2
    · exact h
  have hmeas : AEMeasurable (autMk V) ((volPair V).1.restrict (volPair V).2) := by
    have hm : Measurable (autMk V) := by
      first
      | exact measurable_quotient_mk'
      | exact fun _ hs => hs
    exact hm.aemeasurable
  have hpre : autMk V ⁻¹' S = O := by
    ext g
    have hrel := Quotient.mk_out (s := QuotientGroup.rightRel (GQ V)) g
    rw [QuotientGroup.rightRel_apply] at hrel
    have hv : φ (autMk V g).out = φ g := by
      have e : g = (g * (autMk V g).out⁻¹) * (autMk V g).out := by group
      conv_rhs => rw [e]
      rw [hφinv _ hrel]
    show ¬ φ (autMk V g).out = 0 ↔ φ g ≠ 0
    rw [hv]
  have hle := Measure.le_map_apply hmeas S
  rw [hpre, Measure.restrict_apply hO.measurableSet] at hle
  have e2 : muQ V S = Measure.map (autMk V) ((volPair V).1.restrict (volPair V).2) S := rfl
  rw [← e2, hS] at hle
  exact hOF (le_antisymm hle (zero_le))

section Dom

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem aeDom_of {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {σ : c.F →+* ℂ} {V : HSp D}
    {dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r} {mu : GA D V → ℂ} {Kf : Subgroup (GA D V)}
    {th : ∀ k, ((U σ).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hA : AdelAut V dict mu) (hV : FinVol V) (hP : ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2)
    (hmu : MuUnit V dict mu) (hd : DictIsUnif V dict Kf th hr) : AeDom U σ V dict mu := by
  intro la P hPm hae k x hx
  have key : ∀ Q ∈ holSub (U σ).X la,
      ((∀ γ ∈ GQ V, ∀ g, adel V dict mu Q (γ * g) = adel V dict mu Q g) ∧
        Continuous (adel V dict mu Q)) ∧
      ∀ k, (∀ x ∈ ((U σ).X k).dom, ∀ b ∈ Bor ((U σ).X k).Ψ r, Q k (rmul x b) = bchar (la k) b * Q k x) ∧
        ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, Q k (lact γ x) = ((U σ).X k).χ (la k) γ * Q k x := by
    intro Q hQ
    unfold holSub at hQ
    induction hQ using Submodule.span_induction with
    | mem Q hQ =>
      refine ⟨hA la Q hQ, fun k => ?_⟩
      have hs := (hQ k).1.1
      exact ⟨hs.2.1, hs.2.2⟩
    | zero =>
      refine ⟨⟨fun γ _ g => by simp, by rw [map_zero]; exact continuous_zero⟩,
        fun k => ⟨fun x _ b _ => by simp, fun γ _ x _ => by simp⟩⟩
    | add Q₁ Q₂ _ _ h1 h2 =>
      refine ⟨⟨fun γ hγ g => ?_, ?_⟩, fun k => ⟨fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩⟩
      · rw [map_add (f := _), Pi.add_apply, Pi.add_apply, h1.1.1 γ hγ g, h2.1.1 γ hγ g]
      · rw [map_add (f := _)]
        exact h1.1.2.add h2.1.2
      · simp only [Pi.add_apply]
        rw [(h1.2 k).1 x hx b hb, (h2.2 k).1 x hx b hb, mul_add]
      · simp only [Pi.add_apply]
        rw [(h1.2 k).2 γ hγ x hx, (h2.2 k).2 γ hγ x hx, mul_add]
    | smul a Q _ h =>
      refine ⟨⟨fun γ hγ g => ?_, ?_⟩, fun k => ⟨fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩⟩
      · rw [map_smul, Pi.smul_apply, Pi.smul_apply, h.1.1 γ hγ g]
      · rw [map_smul]
        exact h.1.2.const_smul a
      · simp only [Pi.smul_apply, smul_eq_mul]
        rw [(h.2 k).1 x hx b hb]
        ring
      · simp only [Pi.smul_apply, smul_eq_mul]
        rw [(h.2 k).2 γ hγ x hx]
        ring
  obtain ⟨⟨hinv, hcont⟩, hlaw⟩ := key P hPm
  have hz := quotSupp_of V hV hP (adel V dict mu P) hcont hinv hae
  obtain ⟨-, -, -, hd4, hd5, -⟩ := hd
  obtain ⟨g, γ, hγ, b, hb, hg⟩ := hd5 k x hx
  have h0 : P (dict g).1 (dict g).2 = 0 := by
    have e : mu g * P (dict g).1 (dict g).2 = 0 := hz g
    have hmu0 : mu g ≠ 0 := by
      intro h
      have h1 := hmu.2.1 g
      rw [h, norm_zero] at h1
      exact zero_ne_one h1
    exact (mul_eq_zero.mp e).resolve_left hmu0
  have hdom := hd4 g
  rw [hg] at h0 hdom
  exact eq_zero_of_orbit _ (la k) (P k) (hlaw k).1 (hlaw k).2 hx hγ hb hdom h0

end Dom

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.RecCond
section
namespace Formalism.L2.Pj

open Formalism.BasicNotions

def OKPsi (D : D7) : Prop := ∀ Q : Par D, Q.Pins → ∀ j, InR D j → KPsiIn (Dw := Q.Dw j) Q.c

end Formalism.L2.Pj
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.RecConj
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}
  (c : Coeff l)

private theorem rt0_conj_ne_lemma : (starRingEnd ℂ) H.rt0 ≠ H.rt0 := by
  intro h2
  have hre := Complex.conj_eq_iff_re.mp h2
  have hsq := H.sqrt_neg_disc_sq
  rw [← hre] at hsq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h3 : ((H.rt0.re ^ 2 : ℝ) : ℂ) = ((-(H.d : ℝ) : ℝ) : ℂ) := by push_cast; exact hsq
  have h4 := Complex.ofReal_injective h3
  nlinarith [sq_nonneg H.rt0.re]

theorem not_good_conj {σ : c.F →+* ℂ} (h : GoodEmb c σ) : ¬ GoodEmb c ((starRingEnd ℂ).comp σ) := by
  intro h'
  unfold GoodEmb at h h'
  simp only [RingHom.comp_apply] at h h'
  rw [h] at h'
  exact rt0_conj_ne_lemma h'

private theorem imaginary_root_conj_lemma_2 : (starRingEnd ℂ) H.rt0 = -H.rt0 := by
  have h1 : ((starRingEnd ℂ) H.rt0) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, H.sqrt_neg_disc_sq, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
  · exact absurd h rt0_conj_ne_lemma
  · exact h

theorem goodOf_conj (σ : c.F →+* ℂ) : goodOf c ((starRingEnd ℂ).comp σ) = goodOf c σ := by
  have key : ∀ τ : c.F →+* ℂ, GoodEmb c τ ∨ GoodEmb c ((starRingEnd ℂ).comp τ) := by
    intro τ
    unfold GoodEmb
    simp only [RingHom.comp_apply]
    generalize hxd : (IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ = x
    have hx : (x : ℂ) = H.rt0 := by rw [← hxd]; rfl
    have hx2 : x ^ 2 = -((H.d : ℕ) : c.F) := by
      apply Subtype.ext
      have h0 : (x : ℂ) ^ 2 = -((H.d : ℕ) : ℂ) := by rw [hx, H.sqrt_neg_disc_sq]
      exact_mod_cast h0
    have hsq : (τ x) ^ 2 = H.rt0 ^ 2 := by
      rw [← map_pow, hx2, map_neg, map_natCast, H.sqrt_neg_disc_sq]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact Or.inl h
    · right
      rw [h, map_neg, imaginary_root_conj_lemma_2, neg_neg]
  unfold goodOf
  by_cases h1 : GoodEmb c σ
  · have h2 := not_good_conj c h1
    rw [if_neg h2, if_pos h1]
    ext x
    simp
  · rcases key σ with h | h
    · exact absurd h h1
    · rw [if_pos h, if_neg h1]

end

variable {D : D7} {T : Core D} (h : LawsCore T)

theorem recB_supN_conj (j : ℕ) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) (F : (recB h).Cusp j w) :
    (recB h).supN j w ((starRingEnd ℂ).comp σ) F = (recB h).supN j w σ F := by
  simp [recB, mkB, cutN, Core.Ns, goodOf_conj]

end Formalism.L2.Pj
end
end

