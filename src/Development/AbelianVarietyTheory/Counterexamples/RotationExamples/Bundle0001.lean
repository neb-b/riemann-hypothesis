module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LevelVectorSizeBounds
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
namespace GlobalTheory.Survey.LevelVectorSizeBounds
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}

theorem hookProd_pos (μ : YoungDiagram) : 0 < Formalism.LatticeIndexTer.hookProd μ := by
  unfold Formalism.LatticeIndexTer.hookProd
  refine Finset.prod_pos fun x hx => ?_
  have hx' : (x.1, x.2) ∈ μ := hx
  have a := YoungDiagram.mem_iff_lt_rowLen.1 hx'
  have b := YoungDiagram.mem_iff_lt_colLen.1 hx'
  omega

theorem locK_eq_one {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {P : HeightOneSpectrum (𝓞 E)}
    (h : χ.UnrAt P) (a : 𝓞 E) (k : Eˣ) (hk : (k : E) = a) (ha : a ∉ P.asIdeal) : χ.locK P k = 1 := by
  refine h _ ?_
  show Valued.v (((k : E)) : P.adicCompletion E) = 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hk]
  have := (P.valuation_eq_one_iff_notMem (K := E) (r := a)).2 ha
  exact this

theorem not_both {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : q ≠ p) (h1 : (p : 𝓞 E) ∈ P.asIdeal) (h2 : (q : 𝓞 E) ∈ P.asIdeal) : False := by
  have hc : IsCoprime (q : 𝓞 E) (p : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hq hp).2 hne)
  obtain ⟨x, y, hxy⟩ := hc
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hxy ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ h2) (P.asIdeal.mul_mem_left _ h1)))

theorem q_mem {P : Pl D.host.E} {q : ℕ} (h : Nat.card (kP P) = q) : (q : 𝓞 D.host.E) ∈ P.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← h]
  have := card_nsmul_eq_zero' (G := kP P) (x := 1)
  rwa [nsmul_one] at this

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)


theorem isLocal_triv : IsLocalLevel (D := D) R.triv := by
  refine ⟨fun _ => ⊥, fun _ => 1, ?_⟩
  have key : ∀ (H : Subgroup (G0 R.Pg D.R.r)) (c : H →* ℂˣ), H = ⊥ → R.triv = ⟨H, c⟩ := by
    rintro H c rfl
    have : c = 1 := by ext x; rw [Subsingleton.elim x 1]; simp
    subst this; rfl
  exact key _ _ (Subgroup.pi_bot)

theorem grp_triv (i : Fin D.R.m) (t : T) (m) :
    grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) R.triv m) = (levEnv _ (R.βV i) (R.datVt i t)).J := rfl

theorem eq_one_of_full_upper_block_eq_one {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (e : n = r) (g : GL (Fin n) κ) (h : upperLeftBlock hr g = 1) : g = 1 := by
  subst e
  have hg : g ∈ blockTri (κ := κ) (n := n) (blk2 n) := by
    intro a b hab
    simp [blk2] at hab
  unfold upperLeftBlock at h
  rw [extendOne_of_mem _ hg] at h
  have h2 := congrArg (fun x : GL (Fin n) κ => (x : Matrix (Fin n) (Fin n) κ)) h
  ext a b
  exact congrFun (congrFun h2 a) b

theorem omegaG_triv (i : Fin D.R.m) (m) (y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) :
    Datum.omegaG (R.datWp i R.triv) m y = Datum.omegaK R.Pg y := by
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have key : ∀ g : ∀ PP : ↥R.Pg, GL (Fin (Wc D i).rank) (kP PP.1),
      (fun PP => upperLeftBlock (r_le_rank_Wc i) (g PP)) ∈ (⊥ : Subgroup (G0 R.Pg D.R.r)) → ∀ PP, g PP = 1 := fun g hg PP =>
    eq_one_of_full_upper_block_eq_one _ hrk _ (congrFun (Subgroup.mem_bot.1 hg) PP)
  unfold Datum.omegaG Datum.omegaK
  split_ifs with h1 h2 h2
  · have hg := key _ h1.2.choose_spec.2.2
    have e1 : (R.datWp i R.triv).s = 0 := rfl
    have e2 : ∀ x, (R.datWp i R.triv).P.chi x = 1 := fun _ => rfl
    rw [e2]
    simp only [e1, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, Units.val_one, one_mul]
    refine Finset.prod_eq_one fun PP _ => ?_
    rw [hg PP]; simp
  · exfalso
    refine h2 fun PP hP => ⟨h1.1 PP hP, ?_⟩
    obtain ⟨g, g1, -, g3⟩ := h1.2
    exact (g1 ⟨PP, hP⟩).symm.trans (congrArg Units.val (key g g3 ⟨PP, hP⟩))
  · exfalso
    refine h1 ⟨fun PP hP => (h2 PP hP).1, fun _ => 1, fun PP => (h2 PP.1 PP.2).2.symm, fun _ => Subgroup.one_mem _, ?_⟩
    have : (fun PP : ↥R.Pg => upperLeftBlock (r_le_rank_Wc i) (1 : GL (Fin (Wc D i).rank) (kP PP.1))) = 1 := by
      funext PP; exact blockDiagonalExtendByOnePrimeField_one _ _
    exact this ▸ Subgroup.one_mem _
  · rfl


theorem levFn_congr {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (r : ℕ) (hr : r ≤ n) (t s : ℕ) (Pg Q : Finset (Pl D.host.E))
    (P : LevelP Pg r ℂ) (cg cg' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (xq xq' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (h1 : ∀ c, ∀ PP ∈ Pg, cg c PP = cg' c PP) (h2 : ∀ PP ∈ Q, xq PP = xq' PP) (x) :
    levFn β ⟨r, hr, t, s, Pg, Q, P, cg, xq⟩ x = levFn β ⟨r, hr, t, s, Pg, Q, P, cg', xq'⟩ x := by
  unfold levFn
  congr 1
  · congr 1
    exact Finset.prod_congr rfl fun PP hP => Finset.prod_congr rfl fun c _ => by dsimp only; rw [h1 _ PP hP]
  · exact Finset.prod_congr rfl fun PP hP => by dsimp only; rw [h2 PP hP]


include R in
theorem delta_base (i : Fin D.R.m) : deltaAtEmb D i (sg0 D A) = RealDat.Delta i := by
  have hl : ∀ ρ, lab (sg0 D A) ρ = ρ := fun ρ => by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0]; exact GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm.lab_base ρ
  unfold deltaAtEmb RealDat.Delta
  congr 1 <;> funext ρ
  · unfold aPlAt; rw [hl]
  · unfold aMiAt; rw [hl]

end GlobalTheory.Survey.LevelVectorSizeBounds

end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.RotationExamples.OneLeAPlLast
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.ThetaFiresProbe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem labE_fixed (τ : D.what₂.Tau) : labE D.what₂.embLL τ = tauE D τ := by
  ext x
  exact DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf (D.eTau τ).1 x)

theorem lab_fixed (ρ : D.what₂.Tau) : lab D.what₂.embLL ρ = ρ := by
  have h : ∃ τ, labE D.what₂.embLL τ = tauE D ρ ∨ labE D.what₂.embLL τ = (starRingEnd ℂ).comp (tauE D ρ) :=
    ⟨ρ, Or.inl (labE_fixed ρ)⟩
  unfold lab
  rw [dite_eq_left h]
  have hs := h.choose_spec
  generalize h.choose = τ at hs
  rw [labE_fixed] at hs
  rcases hs with hs | hs
  · have h1 : D.host.sigmaOf (D.eTau τ).1 = D.host.sigmaOf (D.eTau ρ).1 := by
      exact AlgEquiv.ext fun x => D.host.φ₀.injective (DFunLike.congr_fun hs x)
    apply D.eTau.injective
    apply Subtype.ext
    exact (by unfold Host.sigmaOf at h1; exact (EquivLike.injective _) h1)
  · exfalso
    have a := xi_zero_im_pos D τ
    have b := xi_zero_im_pos D ρ
    rw [hs] at a
    simp at a
    linarith

theorem parAt_fixed (W : HSp D) (ρ : D.what₂.Tau) :
    parAt W D.what₂.embLL ρ = Formalism.L2.NTheta.holPar _ _ (Formalism.L2.NTheta.wtOf D W ρ) := by
  unfold parAt kapAt
  rw [lab_fixed, if_pos (labE_fixed ρ)]
  rfl

end GlobalTheory.ThetaFiresProbe
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.RotationExamples.SobolevContinuityLowGeneration
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links

namespace GlobalTheory.Survey.SobolevContinuityLowGeneration

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sobCont_zero {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Lie : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Sobolev₂ Lie σ 0 :=
  ⟨[], 0, by simp, by simp⟩

theorem sobCont_smul {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ℓ : H →ₗ[ℂ] ℂ} (c : ℂ)
    (h : Sobolev₂ Lie σ ℓ) : Sobolev₂ Lie σ (c • ℓ) := by
  obtain ⟨S, C, h1, h2⟩ := h
  refine ⟨S, ‖c‖ * C, h1, fun w hw => ?_⟩
  rw [LinearMap.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h2 w hw) (norm_nonneg c)

theorem sobCont_add {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ℓ ℓ' : H →ₗ[ℂ] ℂ}
    (h : Sobolev₂ Lie σ ℓ) (h' : Sobolev₂ Lie σ ℓ') : Sobolev₂ Lie σ (ℓ + ℓ') := by
  obtain ⟨S, C, h1, h2⟩ := h
  obtain ⟨S', C', h1', h2'⟩ := h'
  refine ⟨S ++ S', max C C', fun l hl => (List.mem_append.1 hl).elim (h1 l) (h1' l), fun w hw => ?_⟩
  have p : ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), 0 ≤ (S.map fun l => ‖l.foldr (dRep σ) w‖).sum := by
    intro S
    refine List.sum_nonneg fun x hx => ?_
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg _
  rw [LinearMap.add_apply, List.map_append, List.sum_append, mul_add]
  refine (norm_add_le _ _).trans (add_le_add ((h2 w hw).trans ?_) ((h2' w hw).trans ?_))
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (p S)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (p S')

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def LowGenerates (M : DSModel V S) (τ : D.what₂.Tau) : Prop :=
  ∀ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ →
    (∀ u ∈ lowT M τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w : M.sm τ, (w : M.H τ) = M.rep τ g u → ℓ w = 0) →
    ∀ w : M.sm τ, ℓ w = 0

open Classical in
theorem mult_equiv_cont {θ} {M : DSModel V S} {J χ} {U : MMap M} (hU : U ∈ Mult θ M J χ) :
    (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ),
      (w : M.H τ) = M.rep τ g (v τ) → U (Function.update v τ w) = rTr V (atTau θ V τ g) (U v)) ∧
    ∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
      ∀ w : M.sm τ, ℓ w = U (Function.update v τ w) x := by
  induction hU using Submodule.span_induction with
  | mem T hT => exact ⟨hT.equiv, hT.cont⟩
  | zero => exact ⟨fun _ _ _ _ _ _ => rfl, fun τ v x => ⟨0, sobCont_zero _ _, fun _ => rfl⟩⟩
  | add T T' _ _ h h' =>
    refine ⟨fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
    · rw [MultilinearMap.add_apply, h.1 τ g hg v w hw, h'.1 τ g hg v w hw]; rfl
    · obtain ⟨ℓ, a, b⟩ := h.2 τ v x
      obtain ⟨ℓ', a', b'⟩ := h'.2 τ v x
      exact ⟨ℓ + ℓ', sobCont_add a a', fun w => by rw [LinearMap.add_apply, b, b']; rfl⟩
  | smul c T _ h =>
    refine ⟨fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
    · rw [MultilinearMap.smul_apply, h.1 τ g hg v w hw]; rfl
    · obtain ⟨ℓ, a, b⟩ := h.2 τ v x
      exact ⟨c • ℓ, sobCont_smul c a, fun w => by rw [LinearMap.smul_apply, b]; rfl⟩

theorem eq_zero_of_lowGenerates {θ} {M : DSModel V S} (hM : ∀ τ, LowGenerates M τ) {J χ} {U : MMap M}
    (hU : U ∈ Mult θ M J χ) (h0 : ∀ v : ∀ ρ, lowT M ρ, U (fun ρ => (v ρ : M.sm ρ)) = 0) : U = 0 := by
  classical
  obtain ⟨he, hc⟩ := mult_equiv_cont hU
  have key : ∀ s : Finset D.what₂.Tau, ∀ v : M.Vec, (∀ ρ, ρ ∉ s → v ρ ∈ lowT M ρ) → U v = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro v hv; exact h0 fun ρ => ⟨v ρ, hv ρ (by simp)⟩
    | insert τ s _ ih =>
      intro v hv
      funext x
      obtain ⟨ℓ, hℓ, e⟩ := hc τ v x
      have := hM τ ℓ hℓ (fun u hu g hg w hw => ?_) (v τ)
      · rw [e] at this
        simpa using this
      · have h1 := he τ g hg (Function.update v τ u) w (by simpa using hw)
        have h2 : U (Function.update v τ u) = 0 := by
          refine ih _ fun ρ hρ => ?_
          by_cases hh : ρ = τ
          · subst hh; simpa using hu
          · rw [Function.update_of_ne hh]; exact hv ρ (by simp [hh, hρ])
        rw [e]
        simp only [Function.update_idem] at h1
        have h3 := congrFun h1 x
        simp only [rTr] at h3
        rw [h3, h2]; rfl
  exact MultilinearMap.ext fun v => key Finset.univ v (by simp)

end GlobalTheory.Survey.SobolevContinuityLowGeneration

end
end

