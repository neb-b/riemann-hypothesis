module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1355
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0406
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0604
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0225

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodFunctionLineDerivative
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem continuous_lineDer_of_growth (h : IsCMExt F E σ) {φ : GAd σ J → ℂ} (hs : GlobalTheory.UAut.IsSm σ J φ) (hc : Continuous φ)
    {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) {A : ℕ} {B : ℝ}
    (hB : ∀ g, ‖lineDer γ (lineDer γ φ) g‖ ≤ B * (height σ J g : ℝ) ^ A) : Continuous (lineDer γ φ) := by
  have hpos : ∀ g, 0 < (height σ J g : ℝ) := fun g =>
    zero_lt_one.trans_le (by exact_mod_cast GlobalTheory.AdelicU.one_le_height σ J g)
  have hB0 : 0 ≤ B := (mul_nonneg_iff_of_pos_right (pow_pos (hpos 1) A)).1 ((norm_nonneg _).trans (hB 1))
  have hγc : Continuous γ := by
    obtain ⟨w, τ, Z, _, hy⟩ := hγ
    choose y hγ' hy using hy
    have hc : Continuous y := by
      rw [(GlobalTheory.Orb.isEmbedding_archMat J h τ).continuous_iff]
      have e : (GlobalTheory.Orb.matCoord (GlobalTheory.Orb.archMat σ J τ) ∘ y) = fun t i j => NormedSpace.exp (t • Z) i j := by
        funext t i j; simp only [Function.comp_apply, GlobalTheory.Orb.matCoord, hy t]
      rw [e]
      have hexp : Continuous fun t : ℝ => NormedSpace.exp (t • Z) := by
        letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
        letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
        letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
        exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
      exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp ((continuous_apply i).comp hexp)
    have : γ = fun t => embArch σ J w (y t) := funext hγ'
    rw [this]
    exact (continuous_embArch σ J w).comp hc
  have hht : Continuous fun g : GAd σ J => (height σ J g : ℝ) :=
    NNReal.continuous_coe.comp (GlobalTheory.AdelicU.continuous_height_GAd σ J)
  obtain ⟨c, hc'⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).image (hht.comp hγc)).bddAbove
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ g, ‖lineDer γ φ g - t⁻¹ • (φ (g * γ t) - φ g)‖ ≤
      B * ((height σ J g : ℝ) * c) ^ A * t := fun t t0 t1 g => by
    set q := t⁻¹ • (φ (g * γ t) - φ g) with hq
    have d1 := GlobalTheory.UAut.ConstAut.hasDerivAt_foldr h hs (l := []) (by simp) hγ g
    have d2 := GlobalTheory.UAut.ConstAut.hasDerivAt_foldr h hs (l := [γ]) (by simpa using hγ) hγ g
    simp only [List.foldr_cons, List.foldr_nil] at d1 d2
    have := GlobalTheory.CuspDecay.mul_norm_deriv_le (f := fun s => φ (g * γ s) - φ g - s • q)
      (f₁ := fun s => lineDer γ φ (g * γ s) - q) (f₂ := fun s => lineDer γ (lineDer γ φ) (g * γ s))
      (fun s => by simpa using ((d1 s).sub_const (φ g)).fun_sub ((hasDerivAt_id s).smul_const q))
      (fun s => (d2 s).sub_const q) t0.le (B := B * ((height σ J g : ℝ) * c) ^ A) fun s hs' => (hB _).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hpos _).le
          ((NNReal.coe_le_coe.2 (GlobalTheory.AdelicU.height_mul_le σ J _ _)).trans (by
            rw [NNReal.coe_mul]
            exact mul_le_mul_of_nonneg_left (hc' ⟨s, ⟨hs'.1, hs'.2.trans t1⟩, rfl⟩) (hpos g).le)) A) hB0)
    rw [GlobalTheory.UAut.ConstAut.realLine_zero h hγ, mul_one, hq, smul_inv_smul₀ t0.ne', sub_self, sub_self, zero_smul, sub_self,
      norm_zero, zero_add, zero_add, mul_comm _ t] at this
    exact le_of_mul_le_mul_left this t0
  refine continuous_of_locally_uniform_approx_of_continuousAt fun x u hu => ?_
  obtain ⟨ε, hε, hu⟩ := Metric.mem_uniformity_dist.1 hu
  have hb : Continuous fun g : GAd σ J => B * ((height σ J g : ℝ) * c) ^ A :=
    continuous_const.mul ((hht.mul continuous_const).pow A)
  obtain ⟨t, t0, t1, t2⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ B * ((height σ J x : ℝ) * c) ^ A * t < ε := by
    have : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t ≤ 1 ∧ B * ((height σ J x : ℝ) * c) ^ A * t < ε :=
      eventually_mem_nhdsWithin.and (Filter.Eventually.filter_mono nhdsWithin_le_nhds
        ((eventually_le_nhds zero_lt_one).and
          ((continuous_const.mul continuous_id).continuousAt.eventually_lt continuousAt_const (by simpa using hε))))
    exact this.exists
  refine ⟨_, (isOpen_lt (hb.mul (continuous_const (y := t))) (continuous_const (y := ε))).mem_nhds t2,
    fun g => t⁻¹ • (φ (g * γ t) - φ g),
    (((hc.comp (continuous_mul_const _)).sub hc).const_smul t⁻¹).continuousAt, fun y hy => hu ?_⟩
  rw [dist_eq_norm]
  exact (key t t0 t1 y).trans_lt hy

theorem lineDer_mul_fin {φ : GAd σ J → ℂ} {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) {k : GAd σ J} (hk : k ∈ finPts σ J)
    (e : ∀ g, φ (g * k) = φ g) (g : GAd σ J) : lineDer γ φ (g * k) = lineDer γ φ g := by
  have : (fun t => φ (g * k * γ t)) = fun t => φ (g * γ t) := funext fun t => by
    have hmem : γ t ∈ infPts σ J := by
      obtain ⟨w, τ, Z, -, ht⟩ := hγ
      obtain ⟨y, hy, -⟩ := ht t
      rw [hy]
      exact mem_infPts.2 (projFin_embArch σ J w y)
    have hc := GlobalTheory.CompanionTheory.SiegelAssemble.commute_of_mem hmem hk
    calc
      φ (g * k * γ t) = φ ((g * γ t) * k) := by rw [mul_assoc, ← hc.eq, ← mul_assoc]
      _ = φ (g * γ t) := e _
  simp only [lineDer, this]

theorem isCuspidal_lineDer (h : IsCMExt F E σ) (hJ : IsHermND σ J) {φ : GAd σ J → ℂ} (hl : GlobalTheory.AutomorphicL2Unitary.LeftInv (ratPts σ J) φ)
    (hc : Continuous φ) (hs : GlobalTheory.UAut.IsSm σ J φ) (hcu : IsCuspidal σ J φ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ)
    (hc' : Continuous (lineDer γ φ)) : IsCuspidal σ J (lineDer γ φ) := by
  intro r C hC μ 𝓕 hμ h𝓕 x
  have hI : GlobalTheory.UAut.IsIsoCols σ J C := hC.2
  haveI := GlobalTheory.UAut.locallyCompact_unipRad h hJ hI
  have hco := GlobalTheory.UAut.cocompact_unipRad h hJ hI
  have hl' : GlobalTheory.AutomorphicL2Unitary.LeftInv (ratPts σ J) (lineDer γ φ) := GlobalTheory.UAut.ConstAut.leftInv_foldr hl [γ]
  have h0 : ∀ y, GlobalTheory.Cusp.constTermOn (ratPts σ J) (unipRad σ J C) φ y = 0 := fun y =>
    (hco.constTermOn_eq_zero_iff h𝓕 hl y).2 (hcu r C hC μ 𝓕 hμ h𝓕 y)
  have hd := GlobalTheory.CuspLie.hasDerivAt_constTermOn hco hl hc hl' hc'
    (by
      obtain ⟨w, τ, Z, _, hy⟩ := hγ
      choose y hγ' hy using hy
      have hc : Continuous y := by
        rw [(GlobalTheory.Orb.isEmbedding_archMat J h τ).continuous_iff]
        have e : (GlobalTheory.Orb.matCoord (GlobalTheory.Orb.archMat σ J τ) ∘ y) = fun t i j => NormedSpace.exp (t • Z) i j := by
          funext t i j; simp only [Function.comp_apply, GlobalTheory.Orb.matCoord, hy t]
        rw [e]
        have hexp : Continuous fun t : ℝ => NormedSpace.exp (t • Z) := by
          letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
          letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
          letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
          exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
        exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp ((continuous_apply i).comp hexp)
      have : γ = fun t => embArch σ J w (y t) := funext hγ'
      rw [this]
      exact (continuous_embArch σ J w).comp hc)
    (GlobalTheory.UAut.ConstAut.hasDerivAt_foldr h hs (l := []) (by simp) hγ) x
  simp only [h0] at hd
  rw [GlobalTheory.UAut.ConstAut.realLine_zero h hγ, mul_one] at hd
  exact (hco.constTermOn_eq_zero_iff h𝓕 hl' x).1 (hd.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ)))

theorem good_lineDer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (U : Subgroup (GAd σ J)) (A : ℕ) (φ : GAd σ J → ℂ) (γ : ℝ → GAd σ J), Good σ J U A φ → IsRealLine σ J γ → Good σ J U A (lineDer γ φ) := by
  intro F E _ _ _ _ _ σ h n J hJ U A φ γ hφ hγ
  obtain ⟨B, hB⟩ := hφ.growth [γ, γ] (by simpa using hγ)
  have hcont : Continuous (lineDer γ φ) :=
    continuous_lineDer_of_growth h hφ.smooth hφ.cont hγ (A := A) (B := B) (by simpa using hB)
  refine ⟨GlobalTheory.UAut.ConstAut.leftInv_foldr hφ.left [γ], fun k hk hf => lineDer_mul_fin hγ hf (hφ.level k hk hf), hcont,
    GlobalTheory.UAut.isSm_lineDer hφ.smooth hγ, fun l hl => ?_,
    isCuspidal_lineDer h hJ hφ.left hφ.cont hφ.smooth hφ.cusp hγ hcont⟩
  have := hφ.growth (l ++ [γ]) (by
    intro δ hδ
    rcases List.mem_append.1 hδ with e | e
    · exact hl δ e
    · rw [List.mem_singleton.1 e]; exact hγ)
  simpa only [List.foldr_append, List.foldr_cons, List.foldr_nil] using this

end GlobalTheory.CompanionTheory.RapidDecay

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedRestrictPullBijective
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison

namespace GlobalTheory.CompanionTheory.OmLoc

open Pb

theorem mor_mk_congr {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R'} {σ : R →+* R'} (G : C' ⥤ C)
    (τ τ' : (T : C') → F.obj (G.obj T) →ₛₗ[σ] F'.obj T) (n n') (h : τ = τ') :
    (⟨G, τ, n⟩ : CH.Mor F F' σ) = ⟨G, τ', n'⟩ := by
  subst h; rfl

theorem sq_incl_eq {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r r' : ℤ) :
    (incl h).sq (incl_fil h r) (incl_fil h r') =
      (CH.Mor.restrict (sq (sFil Q r) (sFil Q r')) (ObjectProperty.ιOfLE h) :) := by
  refine mor_mk_congr _ _ _ _ _ ?_
  funext T
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem chain {b : Base} {L : b.Fun} (r r' : ℤ) (Q1 Q2 Q3 : ObjectProperty (Thick L)) (h12 : Q2 ≤ Q1) (h23 : Q3 ≤ Q2) (n : ℕ)
    (b1 : Function.Bijective ((CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q1.ι).pull n))
    (b2 : Function.Bijective (((incl h12).sq (incl_fil h12 r) (incl_fil h12 r')).pull n))
    (b3 : Function.Bijective (((incl h23).sq (incl_fil h23 r) (incl_fil h23 r')).pull n)) :
    Function.Bijective ((CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q3.ι).pull n) := by
  have e : CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q3.ι =
      (CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q1.ι).comp
        (F' := sq (sFil Q1 r) (sFil Q1 r')) (σ' := RingHom.id _) (σ'' := RingHom.id _)
        (((incl h12).sq (incl_fil h12 r) (incl_fil h12 r')).comp (σ'' := RingHom.id _) ((incl h23).sq (incl_fil h23 r) (incl_fil h23 r'))) := by
    rw [sq_incl_eq, sq_incl_eq]
    rfl
  have f : ⇑((CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q3.ι).pull n) =
      ⇑(((incl h23).sq (incl_fil h23 r) (incl_fil h23 r')).pull n) ∘
        ⇑(((incl h12).sq (incl_fil h12 r) (incl_fil h12 r')).pull n) ∘
          ⇑((CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q1.ι).pull n) := by
    funext x
    rw [e]
    exact (P.pull_comp _ _ n x).1.trans ((P.pull_comp _ _ n _).1)
  rw [f]
  exact b3.comp (b2.comp b1)

theorem grT_restrict_bijective : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (𝒱 : Set X.Opens), sSup 𝒱 = ⊤ →
    ∀ (a s : ℕ), a < s → ∀ n : ℕ, Function.Bijective ((CH.Mor.restrict (HT.grT (smFun X q) a) (Pb.KS q s 𝒱).ι).pull n) := by
  intro K _ X q 𝒱 h𝒱 a s has n
  have hI : ∀ T : Thick (nlFun (dividedPowersBot K) 0 X q (Ideal.Quotient.mk ⊥)), InU ⊤ T := fun T => le_of_eq rfl
  have h12 : St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) {⊤} ≤ St ⊤ {⊤} :=
    fun T hT => ⟨trivial, hT.2⟩
  have h23 : St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) 𝒱 ≤ St (TF 1 s) {⊤} :=
    fun T hT => ⟨hT.1, ⊤, rfl, hI T⟩
  exact chain (L := nlFun (dividedPowersBot K) 0 X q (Ideal.Quotient.mk ⊥)) (a : ℤ) ((a : ℤ) + 1) _ _ _ h12 h23 n
    (GlobalTheory.CompanionTheory.OmRes.restrict_pull_bijective_of_forall _ _ (fun T => ⟨trivial, ⊤, rfl, hI T⟩) n)
    (Pb.refl ⊤ 1 s (Or.inl ⟨rfl, rfl⟩) {⊤} h12 (a : ℤ) ((a : ℤ) + 1) (by omega) n)
    ((Pb.zar (TF 1 s) (Or.inl ⟨rfl, 1, s, rfl⟩) 𝒱 {⊤} h23 (by rintro W rfl; exact h𝒱.ge) n).1 (a : ℤ) ((a : ℤ) + 1))

end GlobalTheory.CompanionTheory.OmLoc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasInfCharGLRankZero
section
noncomputable section

open scoped Classical
open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.TreeInfSum

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

inductive ListInf (τ : E →+* ℂ) : List (Σ M : ℕ, Submodule ℂ (Sm E M)) → Multiset ℂ → Prop
  | nil : ListInf τ [] 0
  | cons {x : Σ M : ℕ, Submodule ℂ (Sm E M)} {l : List (Σ M : ℕ, Submodule ℂ (Sm E M))} {m₀ m' : Multiset ℂ} :
      HasInfCharGL x.2 τ m₀ → ListInf τ l m' → ListInf τ (x :: l) (m₀ + m')

theorem ListInf.split (τ : E →+* ℂ) (l₁ l₂ : List (Σ M : ℕ, Submodule ℂ (Sm E M))) (m : Multiset ℂ)
    (h : ListInf τ (l₁ ++ l₂) m) : ∃ m₁ m₂, ListInf τ l₁ m₁ ∧ ListInf τ l₂ m₂ ∧ m = m₁ + m₂ := by
  induction l₁ generalizing m with
  | nil => exact ⟨0, m, .nil, h, by simp⟩
  | cons x l ih =>
    have h' : ListInf τ (x :: (l ++ l₂)) m := h
    cases h' with
    | cons h₀ h' =>
      obtain ⟨m₁, m₂, h₁, h₂, rfl⟩ := ih _ h'
      exact ⟨_, m₂, .cons h₀ h₁, h₂, by rw [add_assoc]⟩

theorem listInf_ofFn (τ : E →+* ℂ) {c : ℕ} (N : Fin c → ℕ) (V : ∀ i, Submodule ℂ (Sm E (N i)))
    (m : Fin c → Multiset ℂ) (h : ∀ i, HasInfCharGL (V i) τ (m i)) :
    ListInf τ (List.ofFn fun i => (⟨N i, V i⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))) (∑ i, m i) := by
  induction c with
  | zero => simpa using ListInf.nil
  | succ c ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    exact .cons (h 0) (ih (fun i => N i.succ) (fun i => V i.succ) (fun i => m i.succ) (fun i => h i.succ))

theorem hasInfCharGL_rank_zero (V : Submodule ℂ (Sm E 0)) (τ : E →+* ℂ) : HasInfCharGL V τ 0 := by
  refine ⟨rfl, fun u φ _ => ?_⟩
  simp [cap, Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm]

theorem infOf_of_listInf (τ : E →+* ℂ) {N : ℕ} (t : Tr E N) (hg : t.Good) (hu : t.Untw) (m : Multiset ℂ)
    (h : ListInf τ (t.leafList.filter fun x => 0 < x.1) m) : t.InfOf τ m := by
  induction t generalizing m with
  | @leaf M V z =>
    rcases hg with ⟨rfl, rfl, rfl⟩ | ⟨hM, -, -⟩
    · have h' : ListInf τ [] m := by simpa [Tr.leafList] using h
      cases h'
      exact ⟨0, hasInfCharGL_rank_zero _ τ, by simp⟩
    · have hz : z = 0 := hu z (by simp [Tr.twists])
      subst hz
      have h' : ListInf τ [(⟨M, V⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))] m := by
        simpa [Tr.leafList, hM] using h
      cases h' with
      | cons h₀ h₁ =>
        cases h₁
        exact ⟨_, h₀, by simp⟩
  | node t₁ t₂ ih₁ ih₂ =>
    have hu₁ : t₁.Untw := fun z hz => hu z (by simp [Tr.twists, hz])
    have hu₂ : t₂.Untw := fun z hz => hu z (by simp [Tr.twists, hz])
    have h' := h
    simp only [Tr.leafList, List.filter_append] at h'
    obtain ⟨m₁, m₂, h₁, h₂, rfl⟩ := ListInf.split τ _ _ m h'
    exact ⟨m₁, m₂, ih₁ hg.1 hu₁ m₁ h₁, ih₂ hg.2 hu₂ m₂ h₂, rfl⟩

theorem treeInf : PositivityTheory.Rg.BcB.F.RS.TreeInf := by
  intro hT E _ _ _ N t P τ m hg hu hp h0 hm
  have h1 := listInf_ofFn τ P.N P.V (fun i => P.m i τ) (fun i => P.inf i τ)
  have hp' : (List.ofFn fun i => (⟨P.N i, P.V i⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))) =
      t.leafList.filter fun x => 0 < x.1 := hp
  rw [hp'] at h1
  exact GlobalTheory.BcSpehProof.hasInfCharGL_unique h0 (hT E N t τ _ (infOf_of_listInf τ t hg hu _ h1)) hm

end GlobalTheory.CompanionTheory.TreeInfSum

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeSum
section
open UpperHalfPlane CongruenceSubgroup Ad3

namespace GlobalTheory.CompanionTheory.HeckeSum

theorem sum_root (p : ℕ) (hp : p.Prime) (n : ℕ) :
    ∑ b ∈ Finset.range p, Complex.exp (-(2 * Real.pi * Complex.I * n * b / p)) =
      if p ∣ n then (p : ℂ) else 0 := by
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / p)) p :=
    Complex.isPrimitiveRoot_exp p hp.ne_zero
  set ζ : ℂ := (Complex.exp (2 * Real.pi * Complex.I / p))⁻¹ ^ n with hζ
  have hterm : ∀ b ∈ Finset.range p,
      Complex.exp (-(2 * Real.pi * Complex.I * n * b / p)) = ζ ^ b := by
    intro b _
    rw [hζ, ← Complex.exp_neg, ← pow_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm]
  have hζp : ζ ^ p = 1 := by
    rw [hζ, ← pow_mul, mul_comm n p, pow_mul, hprim.inv.pow_eq_one, one_pow]
  split_ifs with h
  · have h1 : ζ = 1 := by
      rw [hζ]
      exact (hprim.inv.pow_eq_one_iff_dvd n).mpr h
    simp [h1]
  · have h1 : ζ ≠ 1 := by
      rw [hζ]
      intro h1
      exact h ((hprim.inv.pow_eq_one_iff_dvd n).mp h1)
    rw [geom_sum_eq h1, hζp, sub_self, zero_div]

theorem hecke_sum (k N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (f : CuspForm (Gamma1 N) (k : ℤ)) (a : ℕ → ℂ) (hf : IsForm k N χ f a)
    (he : IsEig k N χ a) (p : ℕ) (hp : p.Prime) (z : ℍ) (w : ℕ → ℍ)
    (hw : ∀ b : ℕ, (w b : ℂ) = ((z : ℂ) - b) / p) (w' : ℍ) (hw' : (w' : ℂ) = p * z) :
    ∑ b ∈ Finset.range p, (f : ℍ → ℂ) (w b) =
      p * (a p * f z - χ p * (p : ℂ) ^ (k - 1) * f w') := by
  have hterm : ∀ n : ℕ, ∑ b ∈ Finset.range p,
      a n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((w b : ℍ) : ℂ)) =
      if p ∣ n then (p : ℂ) * (a n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ) / p))
      else 0 := by
    intro n
    have hsplit : ∀ b : ℕ,
        a n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((w b : ℍ) : ℂ)) =
        a n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ) / p) *
          Complex.exp (-(2 * Real.pi * Complex.I * n * b / p)) := by
      intro b
      rw [hw b, mul_assoc (a n), ← Complex.exp_add]
      congr 2
      ring
    rw [Finset.sum_congr rfl fun b _ => hsplit b, ← Finset.mul_sum, sum_root p hp n]
    split_ifs <;> ring
  have hL : HasSum (fun n : ℕ => if p ∣ n then
      (p : ℂ) * (a n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ) / p)) else 0)
      (∑ b ∈ Finset.range p, (f : ℍ → ℂ) (w b)) := by
    have h := hasSum_sum fun b (_ : b ∈ Finset.range p) => hf.exp (w b)
    convert h using 1
    funext n
    exact (hterm n).symm
  have hinj : Function.Injective (fun m : ℕ => p * m) := fun x y h =>
    Nat.eq_of_mul_eq_mul_left hp.pos h
  have hLm : HasSum (fun m : ℕ => (p : ℂ) *
      (a (p * m) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ))))
      (∑ b ∈ Finset.range p, (f : ℍ → ℂ) (w b)) := by
    have h1 := (hinj.hasSum_iff (f := fun n : ℕ => if p ∣ n then
      (p : ℂ) * (a n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ) / p)) else 0)
      (a := ∑ b ∈ Finset.range p, (f : ℍ → ℂ) (w b)) ?_).mpr hL
    · convert h1 using 1
      funext m
      simp only [Function.comp_apply]
      rw [if_pos (dvd_mul_right p m)]
      congr 3
      rw [eq_div_iff (Nat.cast_ne_zero.mpr hp.ne_zero)]
      push_cast
      ring
    · intro x hx
      rw [if_neg]
      rintro ⟨m, rfl⟩
      exact hx ⟨m, rfl⟩
  have h2 : HasSum ((fun m : ℕ => if p ∣ m then
      a (m / p) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ)) else 0) ∘
      (fun n : ℕ => p * n)) ((f : ℍ → ℂ) w') := by
    convert hf.exp w' using 1
    funext n
    simp only [Function.comp_apply]
    rw [if_pos (dvd_mul_right p n), Nat.mul_div_cancel_left n hp.pos, hw']
    congr 2
    push_cast
    ring
  have hw's : HasSum (fun m : ℕ => if p ∣ m then
      a (m / p) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ)) else 0)
      ((f : ℍ → ℂ) w') := by
    refine (hinj.hasSum_iff ?_).mp h2
    intro x hx
    rw [if_neg]
    rintro ⟨m, rfl⟩
    exact hx ⟨m, rfl⟩
  have hR := ((hf.exp z).mul_left (a p)).sub (hw's.mul_left (χ p * (p : ℂ) ^ (k - 1)))
  have key : ∀ m : ℕ, a p * (a m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ))) - χ p * (p : ℂ) ^ (k - 1) *
      (if p ∣ m then a (m / p) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ)) else 0) = a (p * m) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ)) := by
    intro m
    have h := he.2.2 p m hp
    by_cases hm : p ∣ m
    · rw [if_pos hm] at h ⊢
      linear_combination (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ))) * h
    · rw [if_neg hm] at h ⊢
      linear_combination (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ))) * h
  simp only [key] at hR
  exact hLm.unique (hR.mul_left (p : ℂ))

end GlobalTheory.CompanionTheory.HeckeSum
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisFurther
section
open scoped Classical

open NumberField GlobalTheory.CuspRep Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.SpectralAccumulation

noncomputable section

namespace GlobalTheory.CompanionTheory.WeightJoin

theorem main : PositivityTheory.Rg.BcB.F.RS.WeightJoin := by
  intro E _ _ _ hU n a b μ e π lam n₁ n₂ hn hμ hπ hw h₁ h₂ hinf τ lam' hτ
  obtain ⟨-, he, hc⟩ := GlobalTheory.BCT.MuProps.main E hU μ e hμ
  let U : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  rw [GlobalTheory.BCT.TwistDisc.expo_pow, GlobalTheory.BCT.TwistDisc.expo_pow]
  rcases NumberField.InfinitePlace.embedding_mk_eq τ with h | h
  · have hv := hw (InfinitePlace.mk τ)
    have hinfv := hinf (InfinitePlace.mk τ)
    have hev := he (InfinitePlace.mk τ)
    rw [h] at hv hinfv hev
    rw [GlobalTheory.DefU.hasWeightAt_unique U τ hτ hv, hev, ← hinfv]
    congr 1 <;> exact Multiset.map_congr rfl fun x _ => by ring
  · have hv := GlobalTheory.DefiniteBC.hasWeightAt_conjugate hn (hw (InfinitePlace.mk τ))
    have hinfv := hinf (InfinitePlace.mk τ)
    have hev := hc (InfinitePlace.mk τ)
    have hs₁ := (h₁ (InfinitePlace.mk τ).embedding).2
    have hs₂ := (h₂ (InfinitePlace.mk τ).embedding).2
    have hcc : ComplexEmbedding.conjugate (InfinitePlace.mk τ).embedding = τ := by
      rw [h]; exact star_star τ
    have hcc' : (starRingEnd ℂ).comp (InfinitePlace.mk τ).embedding = τ := hcc
    rw [hcc'] at hs₁ hs₂
    rw [hcc] at hv hev
    rw [GlobalTheory.DefU.hasWeightAt_unique U τ hτ hv, GlobalTheory.DefiniteBC.infOfWeight_dual, ← hinfv, hev, hs₁, hs₂,
      Multiset.map_add, Multiset.map_map, Multiset.map_map, Multiset.map_map, Multiset.map_map]
    congr 1 <;> exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp_apply]; ring

end GlobalTheory.CompanionTheory.WeightJoin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleCpowDetInverseTwist
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RSZeta

end GlobalTheory.CompanionTheory.RSZeta
end
end

