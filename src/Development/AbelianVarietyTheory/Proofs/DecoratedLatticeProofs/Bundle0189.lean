module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixClosedDerivLinearAdd
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

namespace GlobalTheory.SchwartzDeriv

section General

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [T2Space X]

theorem addHom_eq_zero (F : Type) [DivisionRing F] [CharZero F] [Module F X] (h : ℝ →+ X) (hc : Continuous h) {b : ℝ}
    (hb : b ≠ 0) (h0 : h b = 0) (t : ℝ) : h t = 0 := by

  have hq : ∀ q : ℚ, h ((q : ℝ) * b) = 0 := by
    intro q
    have hn : (q.den : F) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
    have hnum : (q.den : ℝ) * ((q : ℝ) * b) = (q.num : ℝ) * b := by
      rw [← mul_assoc]
      congr 1
      have : ((q.den : ℚ) * q : ℚ) = q.num := by rw [mul_comm]; exact Rat.mul_den_eq_num q
      exact_mod_cast this
    have h1 : q.den • h ((q : ℝ) * b) = 0 := by
      rw [← map_nsmul, nsmul_eq_mul, hnum, ← zsmul_eq_mul, map_zsmul, h0, smul_zero]
    have h2 : h ((q : ℝ) * b) = (q.den : F)⁻¹ • ((q.den : F) • h ((q : ℝ) * b)) := by
      rw [smul_smul, inv_mul_cancel₀ hn, one_smul]
    rw [h2, Nat.cast_smul_eq_nsmul, h1, smul_zero]
  have hsurj : Function.Surjective fun y : ℝ => y * b := fun y => ⟨y / b, div_mul_cancel₀ y hb⟩
  have hdense : DenseRange fun q : ℚ => (q : ℝ) * b :=
    hsurj.denseRange.comp Rat.denseRange_cast (continuous_mul_const b)
  exact hdense.induction_on t (isClosed_eq hc continuous_const) hq

theorem hasDerivAt_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : SchwartzMap E ℂ) (c s : E) :
    HasDerivAt (fun t : ℝ => G (s + t • c)) ((LineDeriv.lineDerivOp c G : SchwartzMap E ℂ) s) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => s + t • c) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const c).const_add s
  have h2 : HasFDerivAt (G : E → ℂ) (fderiv ℝ (G : E → ℂ) (s + (0 : ℝ) • c)) (s + (0 : ℝ) • c) :=
    G.differentiableAt.hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
  simp only [zero_smul, add_zero] at h3
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  exact h3

theorem exists_schwartz_deriv (F : Type) [DivisionRing F] [CharZero F] [Module F X] (P : X → Prop)
    (hP : ∀ a b, P a → P b → P (a + b)) (φ : X → ℂ)
    (hφ : ∀ (k : ℕ) (L : (Fin k → ℝ) →+ X), (Continuous L ∧ ∀ t, P (L t)) → Function.Injective L →
      ∀ x, ∃ g : SchwartzMap (Fin k → ℝ) ℂ, ∀ t, g t = φ (x + L t))
    (M : ℝ →+ X) (hM : Continuous M) (hMP : ∀ t, P (M t)) {k : ℕ} (L : (Fin k → ℝ) →+ X)
    (hL : Continuous L ∧ ∀ t, P (L t)) (hi : Function.Injective L) (x : X) :
    ∃ g : SchwartzMap (Fin k → ℝ) ℂ, ∀ s, HasDerivAt (fun t : ℝ => φ (x + L s + M t)) (g s) 0 := by
  obtain ⟨hLc, hLP⟩ := hL

  let A : (Fin (k + 1) → ℝ) →+ (Fin k → ℝ) :=
    (LinearMap.funLeft ℝ ℝ (Fin.castSucc : Fin k → Fin (k + 1))).toAddMonoidHom
  let B : (Fin (k + 1) → ℝ) →+ ℝ := Pi.evalAddMonoidHom (fun _ => ℝ) (Fin.last k)
  let L' : (Fin (k + 1) → ℝ) →+ X := L.comp A + M.comp B
  have hA : Continuous A := continuous_pi fun i => continuous_apply _
  have hB : Continuous B := continuous_apply _
  have hL'c : Continuous L' := (hLc.comp hA).add (hM.comp hB)
  have hL'P : ∀ u, P (L' u) := fun u => hP _ _ (hLP _) (hMP _)
  have hL'apply : ∀ u, L' u = L (fun i => u (Fin.castSucc i)) + M (u (Fin.last k)) := fun u => rfl
  by_cases hinj : Function.Injective L'
  ·
    obtain ⟨H, hH⟩ := hφ (k + 1) L' ⟨hL'c, hL'P⟩ hinj x
    let e : Fin (k + 1) → ℝ := Pi.single (Fin.last k) 1
    let j : (Fin k → ℝ) →L[ℝ] (Fin (k + 1) → ℝ) :=
      ContinuousLinearMap.pi (Fin.lastCases (motive := fun _ => (Fin k → ℝ) →L[ℝ] ℝ) 0
        fun i => ContinuousLinearMap.proj i)
    have hj_cs : ∀ s i, j s (Fin.castSucc i) = s i := by intro s i; simp [j]
    have hj_last : ∀ s, j s (Fin.last k) = 0 := by intro s; simp [j]
    have hup : ∃ (n : ℕ) (C : ℝ), ∀ s, ‖s‖ ≤ C * (1 + ‖j s‖) ^ n := by
      refine ⟨1, 1, fun s => ?_⟩
      rw [one_mul, pow_one]
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      calc ‖s i‖ = ‖j s (Fin.castSucc i)‖ := by rw [hj_cs]
        _ ≤ ‖j s‖ := norm_le_pi_norm _ _
        _ ≤ 1 + ‖j s‖ := by linarith
    refine ⟨SchwartzMap.compCLM ℝ j.hasTemperateGrowth hup (LineDeriv.lineDerivOp e H), fun s => ?_⟩
    have hd := hasDerivAt_line H e (j s)
    have heq : (fun t : ℝ => H (j s + t • e)) = fun t => φ (x + L s + M t) := by
      funext t
      have e1 : (fun i => (j s + t • e) (Fin.castSucc i)) = s := by
        funext i
        simp [e, hj_cs, Fin.castSucc_ne_last]
      have e2 : (j s + t • e) (Fin.last k) = t := by simp [e, hj_last]
      rw [hH, hL'apply, e1, e2, add_assoc]
    rw [heq] at hd
    exact hd
  ·
    obtain ⟨u, hu, hu0⟩ : ∃ u, L' u = 0 ∧ u ≠ 0 := by
      rw [injective_iff_map_eq_zero] at hinj
      push Not at hinj
      exact hinj
    rw [hL'apply] at hu
    have ht0 : u (Fin.last k) ≠ 0 := by
      intro h
      rw [h, map_zero, add_zero] at hu
      have hs : (fun i => u (Fin.castSucc i)) = 0 := hi (by rw [hu, map_zero])
      apply hu0
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · exact h
      · exact congrFun hs i
    let v : Fin k → ℝ := -((u (Fin.last k))⁻¹ • fun i => u (Fin.castSucc i))
    let Lv : ℝ →+ (Fin k → ℝ) := AddMonoidHom.mk' (fun t => t • v) fun a b => add_smul a b v
    have hMv : ∀ t, M t = L (t • v) := by
      intro t
      have h1 := addHom_eq_zero F (M - L.comp Lv)
        (hM.sub (hLc.comp (continuous_id.smul continuous_const))) ht0 ?_ t
      · simpa [sub_eq_zero, Lv] using h1
      · simp only [AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, AddMonoidHom.mk'_apply, Lv, v, smul_neg,
          smul_smul, mul_inv_cancel₀ ht0, one_smul, map_neg, sub_neg_eq_add]
        rw [add_comm]
        exact hu
    obtain ⟨G, hG⟩ := hφ k L ⟨hLc, hLP⟩ hi x
    refine ⟨LineDeriv.lineDerivOp v G, fun s => ?_⟩
    have hd := hasDerivAt_line G v s
    have heq : (fun t : ℝ => G (s + t • v)) = fun t => φ (x + L s + M t) := by
      funext t
      rw [hG, hMv, map_add (f := _), add_assoc]
    rw [heq] at hd
    exact hd

end General

open GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies

variable {D : D7} {m n : ℕ}

theorem isSchwartzBruhat_add {φ φ' : Mx D m n → ℂ} (h : IsSchwartzBruhat φ) (h' : IsSchwartzBruhat φ') :
    IsSchwartzBruhat (φ + φ') := by
  refine { level := ?_, supp := ?_, schwartz := ?_ }
  · obtain ⟨U, hU, hφU⟩ := h.level
    obtain ⟨U', hU', hφU'⟩ := h'.level
    refine ⟨U ⊓ U', ?_, fun u hu hu0 x => ?_⟩
    · change IsOpen ((U : Set (Mx D m n)) ∩ (U' : Set (Mx D m n)))
      exact hU.inter hU'
    · have hu' := AddSubgroup.mem_inf.mp hu
      simp [hφU u hu'.1 hu0 x, hφU' u hu'.2 hu0 x]
  · obtain ⟨K, hK, hφK⟩ := h.supp
    obtain ⟨K', hK', hφK'⟩ := h'.supp
    refine ⟨K ∪ K', hK.union hK', fun x hx => ?_⟩
    by_cases h1 : φ x = 0
    · have h2 : φ' x ≠ 0 := by simpa [h1] using hx
      exact Or.inr (hφK' x h2)
    · exact Or.inl (hφK x h1)
  · intro k L hL hi x
    obtain ⟨g, hg⟩ := h.schwartz k L hL hi x
    obtain ⟨g', hg'⟩ := h'.schwartz k L hL hi x
    exact ⟨g + g', fun t => by simp [hg, hg']⟩

theorem isSchwartzBruhat_linear_mul {φ : Mx D m n → ℂ} (h : IsSchwartzBruhat φ) (ℓ : Mx D m n →+ ℂ) (hc : Continuous ℓ)
    (h0 : ∀ u : Mx D m n, u.map (infPart D) = 0 → ℓ u = 0) : IsSchwartzBruhat fun x => ℓ x * φ x := by
  refine { level := ?_, supp := ?_, schwartz := ?_ }
  · obtain ⟨U, hU, hφU⟩ := h.level
    refine ⟨U, hU, fun u hu hu0 x => ?_⟩
    show ℓ (x + u) * φ (x + u) = ℓ x * φ x
    rw [map_add (f := _), h0 u hu0, add_zero, hφU u hu hu0 x]
  · obtain ⟨K, hK, hφK⟩ := h.supp
    exact ⟨K, hK, fun x hx => hφK x (right_ne_zero_of_mul hx)⟩
  · intro k L hL hi x
    obtain ⟨g, hg⟩ := h.schwartz k L hL hi x

    let A : (Fin k → ℝ) →L[ℝ] ℂ := (ℓ.comp L).toRealLinearMap (hc.comp hL.1)
    have ht : (fun t => ℓ x + A t).HasTemperateGrowth := by fun_prop
    refine ⟨SchwartzMap.smulLeftCLM ℂ (fun t => ℓ x + A t) g, fun t => ?_⟩
    rw [SchwartzMap.smulLeftCLM_apply_apply ht, hg]
    simp [A, smul_eq_mul]

theorem exists_isSchwartzBruhat_deriv {φ : Mx D m n → ℂ} (h : IsSchwartzBruhat φ) (M : ℝ →+ Mx D m n) (hM : Continuous M)
    (hM0 : ∀ t, (M t).map (finPart D) = 0) :
    ∃ φ', IsSchwartzBruhat φ' ∧ ∀ x, HasDerivAt (fun t : ℝ => φ (x + M t)) (φ' x) 0 := by
  have : T2Space (Mx D m n) := (lattice_Mx D m n).2.2.2.1
  have hP : ∀ a b : Mx D m n, a.map (finPart D) = 0 → b.map (finPart D) = 0 → (a + b).map (finPart D) = 0 := by
    intro a b ha hb
    rw [Matrix.map_add _ (map_add _), ha, hb, add_zero]

  have hdiff : ∀ y, HasDerivAt (fun t : ℝ => φ (y + M t)) (deriv (fun t : ℝ => φ (y + M t)) 0) 0 := by
    intro y
    obtain ⟨g, hg⟩ := exists_schwartz_deriv D.host.F (fun u : Mx D m n => u.map (finPart D) = 0) hP φ h.schwartz
      M hM hM0 (k := 0) 0 ⟨continuous_const, fun t => by simp⟩ (fun a b _ => Subsingleton.elim a b) y
    have hg0 := hg 0
    simp only [AddMonoidHom.zero_apply, add_zero] at hg0
    exact hg0.differentiableAt.hasDerivAt
  refine ⟨fun x => deriv (fun t : ℝ => φ (x + M t)) 0, ⟨?_, ?_, ?_⟩, hdiff⟩
  · obtain ⟨U, hU, hφU⟩ := h.level
    refine ⟨U, hU, fun u hu hu0 x => ?_⟩
    simp only [add_right_comm x u, hφU u hu hu0]
  · obtain ⟨K, hK, hφK⟩ := h.supp
    refine ⟨K, hK, fun x hx => ?_⟩
    by_contra hxK
    apply hx
    have hz : (fun t : ℝ => φ (x + M t)) = fun _ => 0 := by
      funext t
      by_contra ht
      apply hxK
      have := hφK _ ht
      rwa [Matrix.map_add _ (map_add _), hM0, add_zero] at this
    simp only [hz, deriv_const]
  · intro k L hL hi x
    obtain ⟨g, hg⟩ := exists_schwartz_deriv D.host.F (fun u : Mx D m n => u.map (finPart D) = 0) hP φ h.schwartz
      M hM hM0 L hL hi x
    exact ⟨g, fun s => (hg s).deriv.symm⟩

theorem isSchwartzBruhat_closed : ∀ (D : D7) (m n : ℕ) (φ : Mx D m n → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → (∀ M : ℝ →+ Mx D m n, Continuous M → (∀ t, (M t).map (finPart D) = 0) → ∃ φ', GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ' ∧ ∀ x, HasDerivAt (fun t : ℝ => φ (x + M t)) (φ' x) 0) ∧ (∀ ℓ : Mx D m n →+ ℂ, Continuous ℓ → (∀ u : Mx D m n, u.map (infPart D) = 0 → ℓ u = 0) → GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat fun x => ℓ x * φ x) ∧ ∀ φ', GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ' → GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat (φ + φ') := fun _ _ _ _ hφ =>
  ⟨fun M hM hM0 => exists_isSchwartzBruhat_deriv hφ M hM hM0, fun ℓ hc h0 => isSchwartzBruhat_linear_mul hφ ℓ hc h0,
    fun _ h' => isSchwartzBruhat_add hφ h'⟩

end GlobalTheory.SchwartzDeriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionIsotropicStabilizerArchimedean
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

namespace GlobalTheory.Core.Rk.IwIso

open GlobalTheory.AdelicU Formalism.UG

theorem local_decomp {A : Type} [CommRing A] {n r : ℕ} (σ : A →+* A) (f : A →+* ℂ) (hf : Function.Bijective f)
    (hσ : ∀ x, f (σ x) = star (f x)) {J : Matrix (Fin n) (Fin n) A} (b : GL (Fin n) A) (ε : Fin n → Bool)
    (hb : Formalism.UG.cT σ b.1 * J * b.1 = Matrix.diagonal fun i => if ε i then 1 else -1)
    (X : Matrix (Fin n) (Fin r) A) (hX : Formalism.UG.cT σ X * J * X = 0) (g : GL (Fin n) A) (hg : g ∈ UJ σ J) :
    ∃ k ∈ UJ σ J, b⁻¹ * k * b ∈ UJ σ (1 : Matrix (Fin n) (Fin n) A) ∧
      ∃ β : Matrix (Fin r) (Fin r) A, (g * k⁻¹).1 * X = X * β :=
  _root_.GlobalTheory.Core.Rk.IwArch.iw_iso_cols σ f hf hσ b ε hb X hX g hg

theorem iso_arch {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (w : InfinitePlace D.host.F) :
    (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion D.sp.cm.sig) (Matrix.map d.jX (compInf D.host.F D.host.E w)) *
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion T.gram : Matrix (Fin r) (Fin T.rank) _) *
      Matrix.map d.jX (compInf D.host.F D.host.E w) = 0 :=
  _root_.GlobalTheory.IsoColReal.isotropic_at_real d w

theorem mem_stab_of_arch {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : GA D T) (hfin : q ∈ GinfC T)
    (harch : ∀ w : InfinitePlace D.host.F, ∃ β : Matrix (Fin r) (Fin r) (TensorProduct D.host.F w.Completion D.host.E),
      (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w q)).1 * Matrix.map d.jX (compInf D.host.F D.host.E w) =
        Matrix.map d.jX (compInf D.host.F D.host.E w) * β) :
    q ∈ stab d :=
  _root_.GlobalTheory.Core.Rk.IwGlob.mem_stab_of_keeps d q hfin harch

theorem glue {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (k : ∀ w : InfinitePlace F, GArch σ J w) :
    ∃ g : GAd σ J, (∀ w, projArch σ J w g = k w) ∧ projFin σ J g = 1 := by
  classical
  have key : ∀ s : Finset (InfinitePlace F), ∃ g : GAd σ J, (∀ w ∈ s, projArch σ J w g = k w) ∧
      (∀ w ∉ s, projArch σ J w g = 1) ∧ projFin σ J g = 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by simp, fun _ _ => map_one _, map_one _⟩
    | insert a s ha ih =>
      obtain ⟨g, h1, h2, h3⟩ := ih
      refine ⟨g * embArch σ J a (k a), fun w hw => ?_, fun w hw => ?_, ?_⟩
      · rw [map_mul]
        rcases Finset.mem_insert.1 hw with rfl | hw
        · rw [h2 w ha, projArch_embArch_self, one_mul]
        · have hne : w ≠ a := fun e => ha (e ▸ hw)
          rw [h1 w hw, projArch_embArch_ne σ J hne, mul_one]
      · have hne : w ≠ a := fun e => hw (e ▸ Finset.mem_insert_self a s)
        rw [map_mul, h2 w (fun h => hw (Finset.mem_insert_of_mem h)), projArch_embArch_ne σ J hne, mul_one]
      · rw [map_mul, h3, projFin_embArch, mul_one]
  obtain ⟨g, h1, -, h3⟩ := key Finset.univ
  exact ⟨g, fun w => h1 w (Finset.mem_univ w), h3⟩

theorem local_at_arch {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hc : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (w : InfinitePlace F)
    (b : GL (Fin n) (TensorProduct F w.Completion E)) (ε : Fin n → Bool)
    (hb : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) b.1 * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion J * b.1 =
      Matrix.diagonal fun i => if ε i then 1 else -1)
    (X : Matrix (Fin n) (Fin r) (TensorProduct F w.Completion E))
    (hX : (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) X * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion J :
      Matrix (Fin r) (Fin n) _) * X = 0)
    (g : GL (Fin n) (TensorProduct F w.Completion E))
    (hg : g ∈ UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion J)) :
    ∃ k ∈ UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion J),
      b⁻¹ * k * b ∈ UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) (1 : Matrix (Fin n) (Fin n) _) ∧
      ∃ β : Matrix (Fin r) (Fin r) (TensorProduct F w.Completion E), (g * k⁻¹).1 * X = X * β := by
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  exact local_decomp _ (infEmb τ) (infEmb_bijective hc τ) (fun x => (infEmb_sigR hc τ x).symm) b ε hb X hX g hg

theorem mem_stabArch_of {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (w : InfinitePlace F)
    (b : GL (Fin n) (TensorProduct F w.Completion E)) (g : GArch σ J w)
    (h : b⁻¹ * matHom _ σ J g * b ∈ UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) 1) : g ∈ stabArch σ J w b := by
  show (MulAut.conj b⁻¹) (matHom _ σ J g) ∈ UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) (1 : Matrix (Fin n) (Fin n) _)
  rwa [MulAut.conj_apply, inv_inv]


set_option maxHeartbeats 2000000 in
theorem iwasawa_stab_arch : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (b : GL (Fin T.rank) (AE D)), IsMaj T b → ∀ y ∈ GinfC T, ∃ q ∈ stab d, ∃ k ∈ Kmax T b, q ∈ GinfC T ∧ y = q * k := by
  intro D T T₀ r d b hb y hy
  have hloc := fun w : InfinitePlace D.host.F => local_at_arch (isCMExt_host D) T.gram w _ (hb w).choose
    (hb w).choose_spec _ (iso_arch d w) (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w y))
    (projArch D.sp.cm.sig T.gram w y).2
  choose kk hk hk1 hβ using hloc
  obtain ⟨k, hkw, hkf⟩ := glue D.sp.cm.sig T.gram (fun w => ⟨kk w, hk w⟩)
  have hfk : finHom T k = 1 := by
    have e : finHom T k = GlobalTheory.AdelicU.matHom (Af D.host.F) D.sp.cm.sig T.gram (projFin D.sp.cm.sig T.gram k) := rfl
    rw [e, hkf, map_one]
  refine ⟨y * k⁻¹, ?_, k, ?_, ?_, by group⟩
  · refine mem_stab_of_arch d _ ?_ fun w => ?_
    · show finHom T (y * k⁻¹) = 1
      rw [map_mul, map_inv, hfk, inv_one, mul_one]
      exact hy
    · obtain ⟨β, h⟩ := hβ w
      refine ⟨β, ?_⟩
      rw [MonoidHom.map_mul (projArch D.sp.cm.sig T.gram w), MonoidHom.map_inv (projArch D.sp.cm.sig T.gram w), hkw w,
        MonoidHom.map_mul]
      exact h
  · rw [Kmax, levelAll, Subgroup.mem_inf, mem_levelOpen, Subgroup.mem_iInf]
    refine ⟨fun v => ?_, fun w => ?_⟩
    · rw [← projFinLoc_projFin, hkf, map_one]
      exact one_mem _
    · refine Subgroup.mem_comap.2 ?_
      have h3 := mem_stabArch_of D.sp.cm.sig T.gram w _ ⟨kk w, hk w⟩ (hk1 w)
      rw [← hkw w] at h3
      exact h3
  · show finHom T (y * k⁻¹) = 1
    rw [map_mul, map_inv, hfk, inv_one, mul_one]
    exact hy

end GlobalTheory.Core.Rk.IwIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KeepsDiagOfMulStkRowsOne
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

open GlobalTheory.MixModel Matrix

noncomputable section

namespace GlobalTheory.Core.Rk.SW

theorem keepsDiag_of_mul_stkRows_one {R : Type} [CommRing R] {n : ℕ} {M : Matrix (Fin (n + n)) (Fin (n + n)) R}
    {β : Matrix (Fin n) (Fin n) R} (h : M * stkRows 1 1 = stkRows β β) : KeepsDiag finSumFinEquiv M := by
  rw [keepsDiag_iff]
  have key : ∀ s : Fin n ⊕ Fin n, ∀ j, M (finSumFinEquiv s) (finSumFinEquiv (Sum.inl j)) +
      M (finSumFinEquiv s) (finSumFinEquiv (Sum.inr j)) = β (s.elim id id) j := by
    intro s j
    have h1 : ∑ k, M (finSumFinEquiv s) k * stkRows (1 : Matrix (Fin n) (Fin n) R) 1 k j =
        stkRows β β (finSumFinEquiv s) j := congrFun (congrFun h _) j
    rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type] at h1
    simp only [stkRows, Matrix.submatrix_apply, id, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h1
    rw [h1]
    rcases s with s | s <;> rfl
  intro i j
  rw [key (Sum.inr i), key (Sum.inl i)]
  rfl

variable {D : D7}

section Core

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

end Core

end GlobalTheory.Core.Rk.SW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalGroupActionInertSupportedPointsFrames
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.InertFrameAct

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem compW_eq_toCompl (h : w.under (𝓞 D.host.F) = v) (a : AE D) :
    GlobalTheory.InertHomIdx.compW D w a = toCompl h (GlobalTheory.AdelicU.compFin D.host.F D.host.E v a) := by
  show finAdEquiv D.host.F D.host.E (finPart D a) w = _
  rw [finAdEquiv_apply h, ← GlobalTheory.EmbChart.map_evalV_map_sndA]
  rfl

theorem secW_mul (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (z : w.adicCompletion D.host.E) (a : AE D) :
    secW hw h z * a = secW hw h (z * GlobalTheory.InertHomIdx.compW D w a) := by
  show GlobalTheory.EmbChart.tensAt D.host.E v ((InertChart.complEquiv hw h).symm z) * a =
    GlobalTheory.EmbChart.tensAt D.host.E v ((InertChart.complEquiv hw h).symm (z * GlobalTheory.InertHomIdx.compW D w a))
  rw [GlobalTheory.EmbChart.tensAt_mul_right]
  congr 1
  apply (InertChart.complEquiv hw h).injective
  rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, compW_eq_toCompl h]
  rfl

theorem mul_secW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (z : w.adicCompletion D.host.E) (a : AE D) :
    a * secW hw h z = secW hw h (GlobalTheory.InertHomIdx.compW D w a * z) := by
  rw [mul_comm, secW_mul, mul_comm]

theorem mul_map_secW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) (AE D)) (M : Matrix (Fin n) (Fin p) (w.adicCompletion D.host.E)) :
    A * M.map (secW hw h) = (A.map (GlobalTheory.InertHomIdx.compW D w) * M).map (secW hw h) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, mul_secW]

theorem map_secW_mul (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) {m n p : ℕ}
    (M : Matrix (Fin m) (Fin n) (w.adicCompletion D.host.E)) (B : Matrix (Fin n) (Fin p) (AE D)) :
    M.map (secW hw h) * B = (M * B.map (GlobalTheory.InertHomIdx.compW D w)).map (secW hw h) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, secW_mul]

end GlobalTheory.InertFrameAct


open GlobalTheory.InertFrameAct in
theorem GlobalTheory.InertFrameAct.actO_uPt : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)) (gS : Gv S v) (gT : Gv T v) (x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)), actO S T (embV S v gS) (embV T v gT) (uPt hw h k aS aT x) = uPt hw h k aS aT ((aT⁻¹ * locMat D.sp.cm.sig T.gram h gT * aT).1 * x * (aS⁻¹ * locMat D.sp.cm.sig S.gram h gS⁻¹ * aS).1) := by
  intro D v w hw h S T k aS aT gS gT x
  have hT : (mt T (embV T v gT)).map (GlobalTheory.InertHomIdx.compW D w) = (locMat D.sp.cm.sig T.gram h gT).1 := by
    have e := finMat_map_compAt D.sp.cm.sig T.gram h (embV T v gT)
    rw [proj_emb_self] at e
    exact e
  have hS : (mt S (embV S v gS⁻¹)).map (GlobalTheory.InertHomIdx.compW D w) = (locMat D.sp.cm.sig S.gram h gS⁻¹).1 := by
    have e := finMat_map_compAt D.sp.cm.sig S.gram h (embV S v gS⁻¹)
    rw [proj_emb_self] at e
    exact e
  have hinv : (embV S v gS)⁻¹ = embV S v gS⁻¹ := (map_inv _ _).symm
  rw [actO, uPt, uPt, hinv, mul_map_secW, map_secW_mul, hT, hS]
  congr 1
  have h1 : aT.1 * (aT⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : aS.1 * (aS⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Units.val_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [h2, Matrix.mul_one]
  rw [← Matrix.mul_assoc aT.1 (aT⁻¹).1, h1, Matrix.one_mul]
end
end

