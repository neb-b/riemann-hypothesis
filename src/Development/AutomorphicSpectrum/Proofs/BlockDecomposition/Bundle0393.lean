module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ConeWeightsNotSecondType
public import Formalism.RealPlaceAnalysis.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0384
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0382
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0376
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0335
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0356
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0377
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0347
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0282
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0378
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0380
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightMemCone
section
open Finset
open PositivityTheory.RgBcC.RealD (inCone)

namespace GlobalTheory.CompanionTheory.HighestCone

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {K : Fin n → Fin n → Module.End ℂ V}

theorem letter_comm (hg : Formalism.REAL.GlRel K) (a b c d : Fin n) (v : V) :
    K a b (K c d v) = K c d (K a b v) + (if b = c then K a d v else 0)
      - (if d = a then K c b v else 0) := by
  have h := congrArg (fun f : Module.End ℂ V => f v) (hg a b c d)
  simp only [LinearMap.sub_apply, mul_apply_eq_comp] at h
  have h3 : (if b = c then K a d else 0 : Module.End ℂ V) v = if b = c then K a d v else 0 := by
    split_ifs <;> simp
  have h4 : (if d = a then K c b else 0 : Module.End ℂ V) v = if d = a then K c b v else 0 := by
    split_ifs <;> simp
  rw [h3, h4] at h
  rw [add_sub_assoc, ← h]
  abel

theorem levi_step (hg : Formalism.REAL.GlRel K) (lev : Fin n → ℕ) (C : Fin n → Fin n → Prop)
    (Y Z : Submodule ℂ V)
    (hmin : ∀ S : Submodule ℂ V, Y ≤ S →
      (∀ a b, lev a = lev b → ∀ v ∈ S, K a b v ∈ S) → Z ≤ S)
    (hZ : ∀ a b, lev a = lev b → ∀ v ∈ Z, K a b v ∈ Z) (hYZ : Y ≤ Z)
    (hC : ∀ a b c d, C a b → lev c = lev d → (b = c → C a d) ∧ (d = a → C c b))
    (hY : ∀ a b, C a b → ∀ y ∈ Y, K a b y ∈ Z) :
    ∀ a b, C a b → ∀ z ∈ Z, K a b z ∈ Z := by
  let S : Submodule ℂ V :=
    { carrier := {z | z ∈ Z ∧ ∀ a b, C a b → K a b z ∈ Z}
      add_mem' := fun {u w} hu hw => ⟨Z.add_mem hu.1 hw.1, fun a b h => by
        rw [map_add (f := _)]; exact Z.add_mem (hu.2 a b h) (hw.2 a b h)⟩
      zero_mem' := ⟨Z.zero_mem, fun a b _ => by rw [map_zero]; exact Z.zero_mem⟩
      smul_mem' := fun r u hu => ⟨Z.smul_mem r hu.1, fun a b h => by
        rw [map_smul]; exact Z.smul_mem r (hu.2 a b h)⟩ }
  have hle : Z ≤ S := by
    refine hmin S (fun y hy => ⟨hYZ hy, fun a b h => hY a b h y hy⟩) ?_
    intro c d hcd v hv
    refine ⟨hZ c d hcd v hv.1, fun a b hab => ?_⟩
    rw [letter_comm hg a b c d v]
    refine Z.sub_mem (Z.add_mem (hZ c d hcd _ (hv.2 a b hab)) ?_) ?_
    · split_ifs with h
      · exact hv.2 a d ((hC a b c d hab hcd).1 h)
      · exact Z.zero_mem
    · split_ifs with h
      · exact hv.2 c b ((hC a b c d hab hcd).2 h)
      · exact Z.zero_mem
  intro a b hab z hz
  exact (hle hz).2 a b hab

def shift (c : Fin n → Fin n → ℕ) (t : Fin n) : ℝ :=
  ∑ a, ∑ b, (c a b : ℝ) * ((if t = a then 1 else 0) - (if t = b then 1 else 0))

theorem shift_add (c : Fin n → Fin n → ℕ) (a b t : Fin n) :
    shift (fun p q => c p q + if p = a ∧ q = b then 1 else 0) t =
      shift c t + ((if t = a then 1 else 0) - (if t = b then 1 else 0)) := by
  unfold shift
  have : ∀ p q : Fin n, (((c p q + if p = a ∧ q = b then 1 else 0 : ℕ) : ℝ)) *
      ((if t = p then 1 else 0) - (if t = q then 1 else 0)) =
      (c p q : ℝ) * ((if t = p then 1 else 0) - (if t = q then 1 else 0)) +
      (if p = a then (if q = b then ((if t = p then (1:ℝ) else 0) - (if t = q then 1 else 0)) else 0) else 0) := by
    intro p q
    by_cases hp : p = a <;> by_cases hq : q = b <;> simp [hp, hq]
    ring
  simp only [this, Finset.sum_add_distrib]
  simp

theorem weight_letter (hg : Formalism.REAL.GlRel K) (a b t : Fin n) (τ : ℂ) (y : V)
    (ht : K t t y = τ • y) :
    K t t (K a b y) = (τ + (((if t = a then 1 else 0) - (if t = b then 1 else 0) : ℝ) : ℂ)) • K a b y := by
  rw [letter_comm hg t t a b y, ht, map_smul]
  by_cases h1 : t = a <;> by_cases h2 : t = b
  · subst h1; subst h2; simp
  · subst h1
    have h2' : ¬ b = t := fun h => h2 h.symm
    simp [h2', h2, add_smul]
  · subst h2
    simp [h1, add_smul, sub_eq_add_neg]
  · have h2' : ¬ b = t := fun h => h2 h.symm
    simp [h1, h2, h2']

def coneSpan (K : Fin n → Fin n → Module.End ℂ V) (lev : Fin n → ℕ) (ν : Fin n → ℝ) :
    Submodule ℂ V :=
  Submodule.span ℂ {y | ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → lev b < lev a) ∧
    ∀ t, K t t y = (((ν t + shift c t : ℝ)) : ℂ) • y}

theorem coneSpan_letter (hg : Formalism.REAL.GlRel K) (lev : Fin n → ℕ) (ν : Fin n → ℝ) (a b : Fin n)
    (hab : lev b < lev a) (v : V) (hv : v ∈ coneSpan K lev ν) : K a b v ∈ coneSpan K lev ν := by
  unfold coneSpan at hv ⊢
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, hy⟩ := hy
    refine Submodule.subset_span ⟨fun p q => c p q + if p = a ∧ q = b then 1 else 0, ?_, ?_⟩
    · intro p q hpq
      by_cases h : p = a ∧ q = b
      · rw [h.1, h.2]; exact hab
      · apply hc p q
        simpa [h] using hpq
    · intro t
      rw [weight_letter hg a b t _ y (hy t), shift_add]
      congr 1
      push_cast
      ring
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u w _ _ hu hw => rw [map_add (f := _)]; exact Submodule.add_mem _ hu hw
  | smul r u _ hu => rw [map_smul]; exact Submodule.smul_mem _ r hu

theorem inCone_of_ne (lev : Fin n → ℕ) (ev : V →ₗ[ℂ] ℂ) (μ ν : Fin n → ℝ)
    (hev : ∀ a v, ev (K a a v) = (μ a : ℂ) * ev v) (c : Fin n → Fin n → ℕ)
    (hc : ∀ a b, c a b ≠ 0 → lev b < lev a) (y : V)
    (hy : ∀ t, K t t y = (((ν t + shift c t : ℝ)) : ℂ) • y) (hne : ev y ≠ 0) :
    inCone lev (ν - μ) := by
  have hμ : ∀ t, μ t = ν t + shift c t := by
    intro t
    have h := hev t y
    rw [hy t, map_smul, smul_eq_mul] at h
    have := mul_right_cancel₀ hne h
    exact_mod_cast this.symm
  refine ⟨fun a b => c b a, fun a b h => hc b a h, fun x => ?_⟩
  rw [Pi.sub_apply, hμ x]
  have hs : shift c x = ∑ a, ∑ b, (c b a : ℝ) * ((if x = b then 1 else 0) - (if x = a then 1 else 0)) := by
    unfold shift
    rw [Finset.sum_comm]
  rw [hs, sub_add_cancel_left, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem inCone_of_highest : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (K : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel K → ∀ lev : Fin n → ℕ, Monotone lev → ∀ (ev : V →ₗ[ℂ] ℂ) (μ ν : Fin n → ℝ) (x : V), Formalism.REAL.KHighest (fun _ => true) K ν x → (∀ a b v, lev a = lev b → a ≠ b → ev (K a b v) = 0) → (∀ a v, ev (K a a v) = (μ a : ℂ) * ev v) → (∃ T ∈ Algebra.adjoin ℂ {T : Module.End ℂ V | ∃ a b, T = K a b}, ev (T x) ≠ 0) → inCone lev (ν - μ) := by
  intro n V _ _ K hg lev hlev ev μ ν x hx hoff hdiag ⟨T, hT, hTx⟩

  let Y : Submodule ℂ V := sInf {S | x ∈ S ∧ ∀ a b, lev b < lev a → ∀ v ∈ S, K a b v ∈ S}
  let Z : Submodule ℂ V := sInf {S | Y ≤ S ∧ ∀ a b, lev a = lev b → ∀ v ∈ S, K a b v ∈ S}
  have hxY : x ∈ Y := by
    refine (Submodule.mem_sInf).2 fun S hS => hS.1
  have hYl : ∀ a b, lev b < lev a → ∀ v ∈ Y, K a b v ∈ Y := by
    intro a b hab v hv
    refine (Submodule.mem_sInf).2 fun S hS => hS.2 a b hab v ((Submodule.mem_sInf).1 hv S hS)
  have hYmin : ∀ S : Submodule ℂ V, x ∈ S →
      (∀ a b, lev b < lev a → ∀ v ∈ S, K a b v ∈ S) → Y ≤ S :=
    fun S h1 h2 => sInf_le ⟨h1, h2⟩
  have hYZ : Y ≤ Z := le_sInf fun S hS => hS.1
  have hZl : ∀ a b, lev a = lev b → ∀ v ∈ Z, K a b v ∈ Z := by
    intro a b hab v hv
    refine (Submodule.mem_sInf).2 fun S hS => hS.2 a b hab v ((Submodule.mem_sInf).1 hv S hS)
  have hZmin : ∀ S : Submodule ℂ V, Y ≤ S →
      (∀ a b, lev a = lev b → ∀ v ∈ S, K a b v ∈ S) → Z ≤ S :=
    fun S h1 h2 => sInf_le ⟨h1, h2⟩

  have step1 : ∀ a b, lev b < lev a → ∀ z ∈ Z, K a b z ∈ Z := by
    refine levi_step hg lev (fun a b => lev b < lev a) Y Z hZmin hZl hYZ ?_ ?_
    · intro a b c d hab hcd
      constructor
      · rintro rfl; show lev d < lev a; omega
      · rintro rfl; show lev b < lev c; omega
    · intro a b hab y hy
      exact hYZ (hYl a b hab y hy)

  have step2 : ∀ a b, ∀ y ∈ Y, K a b y ∈ Z := by
    let S : Submodule ℂ V :=
      { carrier := {y | y ∈ Y ∧ ∀ a b, K a b y ∈ Z}
        add_mem' := fun {u w} hu hw => ⟨Y.add_mem hu.1 hw.1, fun a b => by
          rw [map_add (f := _)]; exact Z.add_mem (hu.2 a b) (hw.2 a b)⟩
        zero_mem' := ⟨Y.zero_mem, fun a b => by rw [map_zero]; exact Z.zero_mem⟩
        smul_mem' := fun r u hu => ⟨Y.smul_mem r hu.1, fun a b => by
          rw [map_smul]; exact Z.smul_mem r (hu.2 a b)⟩ }
    have hle : Y ≤ S := by
      refine hYmin S ⟨hxY, fun a b => ?_⟩ ?_
      · rcases lt_trichotomy (lev a) (lev b) with h | h | h
        · have hab : a < b := by
            by_contra hn
            have := hlev (not_lt.1 hn)
            omega
          rw [hx.2 a b hab rfl]
          exact Z.zero_mem
        · exact hZl a b h x (hYZ hxY)
        · exact hYZ (hYl a b h x hxY)
      · intro c d hcd v hv
        refine ⟨hYl c d hcd v hv.1, fun a b => ?_⟩
        rw [letter_comm hg a b c d v]
        refine Z.sub_mem (Z.add_mem (step1 c d hcd _ (hv.2 a b)) ?_) ?_
        · split_ifs
          · exact hv.2 a d
          · exact Z.zero_mem
        · split_ifs
          · exact hv.2 c b
          · exact Z.zero_mem
    intro a b y hy
    exact (hle hy).2 a b

  have step3 : ∀ a b, ∀ z ∈ Z, K a b z ∈ Z := by
    intro a b
    exact levi_step hg lev (fun _ _ => True) Y Z hZmin hZl hYZ
      (fun _ _ _ _ _ _ => ⟨fun _ => trivial, fun _ => trivial⟩)
      (fun a b _ y hy => step2 a b y hy) a b trivial

  have hadj : ∀ T ∈ Algebra.adjoin ℂ {T : Module.End ℂ V | ∃ a b, T = K a b}, ∀ z ∈ Z, T z ∈ Z := by
    intro T hT
    induction hT using Algebra.adjoin_induction with
    | mem A hA =>
      obtain ⟨a, b, rfl⟩ := hA
      exact step3 a b
    | algebraMap r =>
      intro z hz
      simpa [Module.algebraMap_end_apply] using Z.smul_mem r hz
    | add A B _ _ hA hB =>
      intro z hz
      exact Z.add_mem (hA z hz) (hB z hz)
    | mul A B _ _ hA hB =>
      intro z hz
      exact hA _ (hB z hz)
  by_contra hcone

  have hY0 : Y ≤ LinearMap.ker ev := by
    have h1 : Y ≤ coneSpan K lev ν := by
      refine hYmin _ (Submodule.subset_span ⟨fun _ _ => 0, by simp, fun t => ?_⟩)
        (fun a b hab v hv => coneSpan_letter hg lev ν a b hab v hv)
      simpa [shift] using hx.1 t
    refine h1.trans ?_
    refine Submodule.span_le.2 ?_
    rintro y ⟨c, hc, hy⟩
    by_contra hne
    exact hcone (inCone_of_ne lev ev μ ν hdiag c hc y hy hne)
  have hZ0 : Z ≤ LinearMap.ker ev := by
    refine hZmin _ hY0 ?_
    intro a b _ v hv
    rw [LinearMap.mem_ker] at hv ⊢
    by_cases hab : a = b
    · subst hab
      rw [hdiag, hv, mul_zero]
    · exact hoff a b v ‹_› hab
  exact hTx (hZ0 (hadj T hT x (hYZ hxY)))

end GlobalTheory.CompanionTheory.HighestCone
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightOfUnitaryDerivative
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG GlobalTheory.CompanionTheory.RealCount.InjHw

namespace GlobalTheory.CompanionTheory.RealCountG.WtInt

variable {n : ℕ}

theorem expU_add (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s t : ℝ) :
    expU X hX (s + t) = expU X hX s * expU X hX t := by
  apply Subtype.ext
  show NormedSpace.exp (((s + t : ℝ) : ℂ) • X) = NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X)
  rw [Complex.ofReal_add, add_smul, Matrix.exp_add_of_commute]
  exact ((Commute.refl X).smul_left _).smul_right _

theorem expU_two_pi (a : Fin n) (hX : (Matrix.single a a Complex.I)ᴴ = -(Matrix.single a a Complex.I)) :
    expU (Matrix.single a a Complex.I) hX (2 * Real.pi) = 1 := by
  apply Subtype.ext
  show NormedSpace.exp (((2 * Real.pi : ℝ) : ℂ) • (Matrix.single a a Complex.I : Matrix (Fin n) (Fin n) ℂ)) = 1
  have e : (((2 * Real.pi : ℝ) : ℂ)) • (Matrix.single a a Complex.I : Matrix (Fin n) (Fin n) ℂ) =
      diagonal (fun c => if c = a then ((2 * Real.pi : ℝ) : ℂ) * Complex.I else 0) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hc : i = a
      · subst hc
        simp
      · simp [Matrix.single_apply, hc, Ne.symm hc]
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply, Matrix.single_apply,
        if_neg (fun hh => hij (hh.1.symm.trans hh.2)), smul_zero]
  rw [e, Matrix.exp_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext c
  have hh : NormedSpace.exp (fun c => if c = a then ((2 * Real.pi : ℝ) : ℂ) * Complex.I else 0) c =
      if c = a then Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) else 1 := by
    split_ifs with hc <;> simp [hc, Complex.exp_eq_exp_ℂ]
  rw [hh]
  have h2 : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
    push_cast
    exact Complex.exp_two_pi_mul_I
  rw [h2]
  simp

theorem eigen_int (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H)) (G : Fin n → Fin n → Module.End ℂ H)
    (hd : ∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X →
      (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H,
      HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0)
    (a : Fin n) (r : ℝ) {v : H} (hv : v ≠ 0) (hr : G a a v = (r : ℂ) • v) : ∃ m : ℤ, r = m := by
  have hX : (Matrix.single a a Complex.I)ᴴ = -(Matrix.single a a Complex.I) := by
    rw [single_conjT, Complex.star_def, Complex.conj_I, single_negI]
  set X : Matrix (Fin n) (Fin n) ℂ := Matrix.single a a Complex.I with hXdef
  set φ : ℝ → H := fun s => ρ (expU X hX s) v with hφ
  have hd0 : HasDerivAt φ ((Complex.I * r) • v) 0 := by
    have := hd X (expU X hX) hX (fun _ => rfl) v
    have e := sum_single (Kf := G) v a a Complex.I
    rw [← hXdef] at e
    rw [e, hr, smul_smul] at this
    exact this
  have hstep : ∀ s, HasDerivAt φ ((Complex.I * r) • φ s) s := by
    intro s
    let L : H →L[ℝ] H := (ρ (expU X hX s)).restrictScalars ℝ
    have hL : ∀ y, L y = ρ (expU X hX s) y := fun _ => rfl
    have h1 : HasDerivAt (fun t => L (φ t)) (L ((Complex.I * r) • v)) 0 :=
      L.hasFDerivAt.comp_hasDerivAt 0 hd0
    have h2 : HasDerivAt (fun t => L (φ t)) (L ((Complex.I * r) • v)) (s - s) := by
      rwa [sub_self]
    have h3 := h2.comp_sub_const s s
    have e : (fun t => L (φ (t - s))) = φ := by
      funext t
      have : expU X hX t = expU X hX s * expU X hX (t - s) := by
        rw [← expU_add]
        congr 1
        ring
      simp only [hL, hφ, this, map_mul, ContinuousLinearMap.mul_apply]
    rw [e] at h3
    have e2 : L ((Complex.I * r) • v) = (Complex.I * r) • φ s := by
      rw [hL, map_smul]
    rwa [e2] at h3
  set ψ : ℝ → H := fun s => Complex.exp ((s : ℂ) * (-(Complex.I * r))) • φ s with hψ
  have hψd : ∀ s, HasDerivAt ψ 0 s := by
    intro s
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * (-(Complex.I * r))) (-(Complex.I * r)) s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const (-(Complex.I * (r : ℂ)))
    have h2 := h1.cexp
    have h3 := h2.smul (hstep s)
    have : Complex.exp ((s : ℂ) * (-(Complex.I * r))) • (Complex.I * r) • φ s +
        (Complex.exp ((s : ℂ) * (-(Complex.I * r))) * -(Complex.I * r)) • φ s = 0 := by
      rw [smul_smul, ← add_smul]
      simp
    rw [this] at h3
    exact h3
  have hconst : ψ (2 * Real.pi) = ψ 0 :=
    is_const_of_deriv_eq_zero (fun s => (hψd s).differentiableAt) (fun s => (hψd s).deriv) _ _
  have h0 : φ 0 = v := by
    have : expU X hX 0 = 1 := by
      apply Subtype.ext
      show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1
      simp
    simp [hφ, this]
  have h2π : φ (2 * Real.pi) = v := by
    show ρ (expU X hX (2 * Real.pi)) v = v
    rw [show expU X hX (2 * Real.pi) = 1 from expU_two_pi a hX, map_one]
    rfl
  have hE : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) • v = v := by
    have b : ψ 0 = v := by simp [hψ, h0]
    have a' : ψ (2 * Real.pi) = Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) • v := by
      show Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) • φ (2 * Real.pi) = _
      rw [h2π]
    rw [← a', hconst, b]
  have hE1 : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) = 1 := by
    have : (Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) - 1) • v = 0 := by
      rw [sub_smul, hE, one_smul, sub_self]
    rcases smul_eq_zero.1 this with h' | h'
    · exact sub_eq_zero.1 h'
    · exact absurd h' hv
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hE1
  refine ⟨-m, ?_⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h5 : (r : ℂ) = ((-m : ℤ) : ℂ) := by
    push_cast at hm ⊢
    have h6 : (2 * (Real.pi : ℂ) * Complex.I) * ((r : ℂ) + m) = 0 := by
      linear_combination -hm
    have h7 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [hpi, Complex.I_ne_zero]
    have := (mul_eq_zero.1 h6).resolve_left h7
    linear_combination this
  exact_mod_cast h5

theorem weight_integral : ∀ {n : ℕ} (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H)) (G : Fin n → Fin n → Module.End ℂ H), (∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X → (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H, HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) → ∀ (μ : Fin n → ℝ) (v : H), v ≠ 0 → Formalism.REAL.IsWeight G μ v → ∃ ν : Fin n → ℤ, μ = wtR ν := by
  intro n H _ _ _ ρ G hd μ v hv hw
  choose ν hν using fun a => eigen_int H ρ G hd a (μ a) hv (hw a)
  exact ⟨ν, funext hν⟩

end GlobalTheory.CompanionTheory.RealCountG.WtInt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientsEquivOfNotLeStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_subquotients_equiv_of_not_le : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (E K L : Subrepresentation ρ), (subQuot E K).IsIrreducible → (subQuot E L).IsIrreducible → ¬ E ≤ E ⊓ K ⊔ E ⊓ L → Nonempty ((subQuot E K).Equiv (subQuot E L)) := by
  first | exact @GlobalTheory.CompanionTheory.GenCore.nonempty_equiv_subQuot | exact GlobalTheory.CompanionTheory.GenCore.nonempty_equiv_subQuot | (intros; apply GlobalTheory.CompanionTheory.GenCore.nonempty_equiv_subQuot <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityDropZeroBlocksStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_drop_zero_blocks : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r r' N : ℕ} (y : Fin r → IrrGL (k := k)) (hd : ∑ a, (y a).1 = N) (o : Fin r' → Fin r), StrictMono o → (∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) → ∀ (hd' : ∑ a, (y (o a)).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), jm y hd π = jm (fun a => y (o a)) hd' π := by
  first | exact @GlobalTheory.CompanionTheory.FineProd.JmDrop.jm_drop | exact GlobalTheory.CompanionTheory.FineProd.JmDrop.jm_drop | (intros; apply GlobalTheory.CompanionTheory.FineProd.JmDrop.jm_drop <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityOrderEmbeddingStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M GlobalTheory.CompanionTheory.WordProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_order_embedding : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n p N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ (zz : Fin n → IrrGL (k := k)) (σ : Fin p ↪o Fin n) (c : Fin n → ℕ), (∀ a, c (σ a) = (zz (σ a)).1) → (∀ j, j ∉ Set.range σ → c j = 0) → ∀ (hz : ∑ a, (zz (σ a)).1 = N) (f : (Σ j, Fin (c j)) ≃ Fin N), jm (fun a => zz (σ a)) hz π ≠ 0 → jhMult (piTensor fun j => (clOf (zz j) (c j)).rep.ρ) (jac f π) ≠ 0 := by
  exact @GlobalTheory.CompanionTheory.WordProd.RowCell.jhMult_row
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelEigenfunctionBoundStatement
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_eigenfunction_bound : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (α : GA E N → ℂ) (δ : ℝ) (F : Set (GA E N)), Continuous α → HasCompactSupport α → 0 < δ →
  IsFundamentalDomain (latticeGL E N) F μ → ∃ C₀ : ℝ, ∀ ψ : GA E N → ℂ, Continuous ψ → (∀ γ ∈ latticeGL E N, ∀ g, ψ (γ * g) = ψ g) →
  (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) → (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1 →
  ∀ (x : GA E N) (k : ℕ), {γ : GA E N | γ ∈ latticeGL E N ∧ ∃ a ∈ tsupport α, ∃ b ∈ tsupport α, γ = x * a * b⁻¹ * x⁻¹}.encard ≤ k →
    ‖ψ x‖ ^ 2 ≤ C₀ * k := by
  intro E _ _ _ N _ _ μ _ α δ F hα hc hδ hF
  haveI : Countable (latticeGL E N) := GlobalTheory.DiscreteUnit.countable_latticeGL
  exact GlobalTheory.CompanionTheory.Conc.BesselPt.pointwise μ (latticeGL E N) hα hc hδ hF
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCharacterFiniteExtensionStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_character_finite_extension : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (μ : G E Ω →* (Qbar l)ˣ), Continuous μ →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
    ∃ (LL' : FinExt l) (ψ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ), Bw.LL.1 ≤ LL'.1 ∧
      IsModel Bw ((rk1 μ).comp (Dec (F := E) A).subtype) LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ) ∧
      (∀ g, ((ψ g : ↥LL'.1) : Qbar l) = ((μ (g : G E Ω) : (Qbar l)ˣ) : Qbar l)) ∧
      Continuous (fun g => ((ψ g : ↥LL'.1) : Qbar l)) ∧ ∀ g, ‖((ψ g : ↥LL'.1) : Qbar l)‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.HeckeChar.exists_unit_model | exact GlobalTheory.CompanionTheory.HeckeChar.exists_unit_model | (intros; apply GlobalTheory.CompanionTheory.HeckeChar.exists_unit_model <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectionToTwistedEigenfunctionSupportStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projection_to_twisted_eigenfunction_support : ∀ {G : Type} {W : Type} [AddCommGroup W] [Module ℂ W] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (P : Subgroup G) (τ : Representation ℂ P W) (L : Subgroup G), IsCompact (L : Set G) → ∀ θ : L →* ℂˣ, IsOpen (θ.ker : Set L) → ∀ f : smoothPart (ind P τ), ∃ f' : smoothPart (ind P τ), f - f' ∈ twKer (smInd P τ) L θ ∧ (∀ g, f'.1.1 g ≠ 0 → ∃ l ∈ L, f.1.1 (g * l) ≠ 0) ∧ ∀ (l : L) (g : G), f'.1.1 (g * l) = (θ l : ℂ) • f'.1.1 g := by
  first | exact @GlobalTheory.CompanionTheory.TwAvgInd.exists_twisted_average_smInd | exact GlobalTheory.CompanionTheory.TwAvgInd.exists_twisted_average_smInd | (intros; apply GlobalTheory.CompanionTheory.TwAvgInd.exists_twisted_average_smInd <;> assumption)
end

