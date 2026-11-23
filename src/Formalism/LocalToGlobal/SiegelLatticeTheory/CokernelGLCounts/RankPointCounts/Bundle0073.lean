module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0070
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0071

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LiftOrbOf
section
noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

set_option maxHeartbeats 1600000

theorem liftOrb_of (hSR : SRLift) : LiftOrb := by
  intro F _ _ _ E _ _ _ _ M hOK m Z Z' ⟨φ⟩ hκ
  classical
  set e : Fin (m + 1) → M.R := Pi.single (Fin.last m) 1 with he
  have hmkZ : ∀ x : Fin (m + 1) → M.R, (Submodule.Quotient.mk (Z.Z.mulVec x) : M.Cok Z) = 0 :=
    fun x => (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
  have hmkZ' : ∀ x : Fin (m + 1) → M.R, (Submodule.Quotient.mk (Z'.Z.mulVec x) : M.Cok Z') = 0 :=
    fun x => (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩

  have hcol : ∀ j : Fin (m + 1), ∃ w : Fin (m + 1) → M.R,
      (Submodule.Quotient.mk w : M.Cok Z') = φ.1 (Submodule.Quotient.mk (Pi.single j 1)) ∧
      mu M Z' w = mu M Z (Pi.single j 1) ∧ (j = Fin.last m → w = e) := by
    intro j
    by_cases hj : j = Fin.last m
    · subst hj
      refine ⟨e, φ.2.1.symm, ?_, fun _ => rfl⟩
      rw [he, mu_e, mu_e, hκ]
    · obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (φ.1 (Submodule.Quotient.mk (Pi.single j 1)))
      have hl := φ.2.2 (Submodule.Quotient.mk (Pi.single j 1))
      rw [← hv, lam_mk, lam_mk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hl
      obtain ⟨t, ht⟩ := hl
      refine ⟨v - Z'.Z.mulVec (t • e), ?_, ?_, fun h => absurd h hj⟩
      · rw [Submodule.Quotient.mk_sub, hmkZ', sub_zero, hv]
      · have ht' : ((t : M.R) : E) = mu M Z' v - mu M Z (Pi.single j 1) := ht
        rw [sub_eq_add_neg, ← Matrix.mulVec_neg, mu_add, mu_Z]
        simp only [Pi.neg_apply, Pi.smul_apply, he, Pi.single_eq_same, smul_eq_mul, mul_one, NegMemClass.coe_neg]
        rw [ht']
        ring
  choose w hw1 hw2 hw3 using hcol
  set l₁ : Matrix (Fin (m + 1)) (Fin (m + 1)) M.R := Matrix.of fun i j => w j i with hl₁
  have hl₁v : ∀ x, l₁.mulVec x = ∑ j, x j • w j := by
    intro x; funext i
    simp [hl₁, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hx : ∀ x : Fin (m + 1) → M.R, ∑ j, x j • (Pi.single j 1 : Fin (m + 1) → M.R) = x := by
    intro x; funext i; simp [Finset.sum_apply, Pi.single_apply]
  have hP1 : ∀ x, (Submodule.Quotient.mk (l₁.mulVec x) : M.Cok Z') = φ.1 (Submodule.Quotient.mk x) := by
    intro x
    conv_rhs => rw [← hx x]
    rw [hl₁v]
    have e1 : (Submodule.Quotient.mk (∑ j, x j • w j) : M.Cok Z') =
        ∑ j, x j • (Submodule.Quotient.mk (w j) : M.Cok Z') := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Submodule.mkQ_apply, map_sum]; simp
    have e2 : (Submodule.Quotient.mk (∑ j, x j • (Pi.single j 1 : Fin (m + 1) → M.R)) : M.Cok Z) =
        ∑ j, x j • (Submodule.Quotient.mk (Pi.single j 1) : M.Cok Z) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Submodule.mkQ_apply, map_sum]; simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, e2, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hw1 j]
  have hP2 : ∀ x, mu M Z' (l₁.mulVec x) = mu M Z x := by
    intro x
    conv_rhs => rw [← hx x]
    rw [hl₁v, mu_sum, mu_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mu_smul, mu_smul, hw2 j]
  have hl₁e : ∀ i, l₁ i (Fin.last m) = if i = Fin.last m then 1 else 0 := by
    intro i
    simp only [hl₁, Matrix.of_apply, hw3 _ rfl, he, Pi.single_apply]

  have hK1 : ∀ y ∈ headK M Z', (Submodule.Quotient.mk y : M.Cok Z') = 0 := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := (mem_headK M Z').1 hy
    exact hmkZ' x
  have hK2 : ∀ y ∈ headK M Z', mu M Z' y = 0 := by
    intro y hy
    obtain ⟨x, hx0, rfl⟩ := (mem_headK M Z').1 hy
    rw [mu_Z, hx0]; simp

  have hb : ∃ y₀, Z'.Z.mulVec y₀ = l₁.mulVec (Z.Z.mulVec e) ∧ y₀ (Fin.last m) = 1 := by
    have h0 : (Submodule.Quotient.mk (l₁.mulVec (Z.Z.mulVec e)) : M.Cok Z') = 0 := by
      rw [hP1, hmkZ, map_zero]
    obtain ⟨y₀, hy₀⟩ := (Submodule.Quotient.mk_eq_zero _).1 h0
    have hy₀' : Z'.Z.mulVec y₀ = l₁.mulVec (Z.Z.mulVec e) := hy₀
    refine ⟨y₀, hy₀', ?_⟩
    have := hP2 (Z.Z.mulVec e)
    rw [← hy₀', mu_Z, mu_Z, he, Pi.single_eq_same] at this
    exact Subtype.ext (by simpa using this)
  obtain ⟨y₀, hy₀, hy₀l⟩ := hb
  have hspan : ∀ v : Fin (m + 1) → M.R, ∃ x, v - l₁.mulVec x ∈ headK M Z' := by
    intro v
    obtain ⟨x₀, hx₀⟩ := Submodule.Quotient.mk_surjective _ (φ.1.symm (Submodule.Quotient.mk v))
    have h1 : (Submodule.Quotient.mk (v - l₁.mulVec x₀) : M.Cok Z') = 0 := by
      rw [Submodule.Quotient.mk_sub, hP1, hx₀, LinearEquiv.apply_symm_apply, sub_self]
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).1 h1
    simp only [Matrix.mulVecLin_apply] at hy
    refine ⟨x₀ + y (Fin.last m) • Z.Z.mulVec e, (mem_headK M Z').2 ⟨y - y (Fin.last m) • y₀, ?_, ?_⟩⟩
    · simp [hy₀l]
    · rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hy₀, hy, Matrix.mulVec_add, Matrix.mulVec_smul]
      abel
  obtain ⟨H, hHK, hHl, hdet⟩ := hSR M hOK m l₁ (headK M Z') hl₁e hspan
  set l := l₁ + H with hl
  have hHx : ∀ x, H.mulVec x ∈ headK M Z' := by
    intro x
    have : H.mulVec x = ∑ j, x j • (fun i => H i j) := by
      funext i; simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hHK j)
  have hQ1 : ∀ x, (Submodule.Quotient.mk (l.mulVec x) : M.Cok Z') = φ.1 (Submodule.Quotient.mk x) := by
    intro x
    rw [hl, Matrix.add_mulVec, Submodule.Quotient.mk_add, hK1 _ (hHx x), add_zero, hP1]
  have hQ2 : ∀ x, mu M Z' (l.mulVec x) = mu M Z x := by
    intro x
    rw [hl, Matrix.add_mulVec, mu_add, hK2 _ (hHx x), add_zero, hP2]
  have hle : ∀ i, l i (Fin.last m) = if i = Fin.last m then 1 else 0 := by
    intro i; rw [hl, Matrix.add_apply, hl₁e, hHl, add_zero]

  have hcolρ : ∀ j, ∃ x, Z'.Z.mulVec x = l.mulVec (Z.Z.mulVec (Pi.single j 1)) := by
    intro j
    have h0 : (Submodule.Quotient.mk (l.mulVec (Z.Z.mulVec (Pi.single j 1))) : M.Cok Z') = 0 := by
      rw [hQ1, hmkZ, map_zero]
    exact (Submodule.Quotient.mk_eq_zero _).1 h0
  choose xs hxs using hcolρ
  set ρ₀ : Matrix (Fin (m + 1)) (Fin (m + 1)) M.R := Matrix.of fun i j => xs j i with hρ₀
  have hZρ : Z'.Z * ρ₀ = l * Z.Z := by
    ext i j
    have h1 : (Z'.Z * ρ₀) i j = (Z'.Z.mulVec (xs j)) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hρ₀]
    have h2 : (l * Z.Z) i j = (l.mulVec (Z.Z.mulVec (Pi.single j 1))) i := by
      rw [Matrix.mulVec_mulVec]; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [h1, h2, hxs j]
  have hρl : ∀ j, ρ₀ (Fin.last m) j = if j = Fin.last m then 1 else 0 := by
    intro j
    have := hQ2 (Z.Z.mulVec (Pi.single j 1))
    rw [← hxs j, mu_Z, mu_Z] at this
    apply Subtype.ext
    simp only [hρ₀, Matrix.of_apply]
    rw [this]
    by_cases h : j = Fin.last m
    · subst h; simp
    · simp [Pi.single_apply, h, Ne.symm h]

  have hlu : IsUnit (l.det) := hdet
  have honto : ∀ x, ∃ y, ρ₀.mulVec y = x := by
    intro x
    set u := l⁻¹.mulVec (Z'.Z.mulVec x) with hu
    have hlu' : l.mulVec u = Z'.Z.mulVec x := by
      rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hlu, Matrix.one_mulVec]
    have hmu : (Submodule.Quotient.mk u : M.Cok Z) = 0 := by
      have h1 := hQ1 u
      rw [hlu', hmkZ'] at h1
      exact (φ.1.map_eq_zero_iff).1 h1.symm
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).1 hmu
    simp only [Matrix.mulVecLin_apply] at hy
    refine ⟨y, mulVec_inj M Z' ?_⟩
    rw [Matrix.mulVec_mulVec, hZρ, ← Matrix.mulVec_mulVec, hy, hlu']
  choose ys hys using fun i : Fin (m + 1) => honto (Pi.single i 1)
  have hright : ρ₀ * (Matrix.of fun i j => ys j i) = 1 := by
    ext i j
    have := congrFun (hys j) i
    simp only [Matrix.mulVec, dotProduct] at this
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [this, Matrix.one_apply, Pi.single_apply]
  have hρu : IsUnit ρ₀.det := by
    have := congrArg Matrix.det hright
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact isUnit_iff_exists_inv.2 ⟨_, this⟩
  refine ⟨l, ρ₀⁻¹, hlu, (Matrix.isUnit_nonsing_inv_det_iff).2 hρu, hle, fun j => ?_, ?_⟩
  · have h1 : Matrix.vecMul e ρ₀ = e := by
      funext j
      simp only [Matrix.vecMul, dotProduct, he, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      rw [hρl]
    have h2 : Matrix.vecMul e ρ₀⁻¹ = e := by
      conv_lhs => rw [← h1]
      rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hρu, Matrix.vecMul_one]
    have := congrFun h2 j
    simp only [Matrix.vecMul, dotProduct, he, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at this
    rw [this]
  · calc Z'.Z = Z'.Z * ρ₀ * ρ₀⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hρu, Matrix.mul_one]
      _ = l * Z.Z * ρ₀⁻¹ := by rw [hZρ]

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqLoc
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut
  Formalism.L2.SG.Pf.MainEqAna

namespace Formalism.L2.SG.Pf.MainEqLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LocalInputLeG {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) {E : Type} [Field E] {r : ℕ}
    {Cl Nu : Type} (N : PN.NGData τ E r Cl Nu) (C1 C0 : ℕ) (AAre : ℝ) : Prop :=
  ∀ γ, PN.IsPt X N γ → ∀ S : Finset (Cl × Nu), ∃ L : PN.LocalNG Cl Nu, L.Basic ∧ ZAt L C1 r ∧
    L.MassRatioAt C0 r ∧ L.Unfold ∧ (∀ x ∈ S, N.a2 x.1 γ x.2 = weightedGenericAmplitudeSq L x.1 x.2) ∧ N.Hh γ = L.Htot ∧
    0 < L.ngenTot ∧ L.ngenTot ≤ AAre * 2 * N.Hh γ ^ PN.eN r * N.n γ

theorem localInputG_of_le {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) {E : Type} [Field E] {r : ℕ}
    {Cl Nu : Type} (N : PN.NGData τ E r Cl Nu) (C1 C0 : ℕ) (AAre : ℝ) (h : LocalInputLeG X N C1 C0 AAre)
    (hng : ∀ γ, N.ngen γ = AAre * 2 * N.Hh γ ^ PN.eN r * N.n γ) : LocalInputG X N C1 C0 := by
  intro γ hγ S
  obtain ⟨L, hB, hZ, hM, hU, ha, hH, hpos, hle⟩ := h γ hγ S
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = AAre * 2 * N.Hh γ ^ PN.eN r * N.n γ / L.ngenTot := ⟨_, rfl⟩
  have hc1 : 1 ≤ c := by
    rw [hc, le_div_iff₀ hpos, one_mul]
    exact hle
  have hV0 : 0 ≤ L.V0 := hB.2.2.2.2.2.1
  refine ⟨{ L with V0 := L.V0 * c }, ?_, hZ, hM, ?_, ?_, hH, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hB
    unfold Formalism.FourierDecayAlt.PN.LocalNG.Basic
    exact ⟨h1, h2, h3, h4, h5, mul_nonneg h6 (by linarith), h7⟩
  · intro d S' hS'
    have h0 := hU d S' hS'
    have hw : 0 ≤ L.V0 * ∏ p, L.wt p (d p) :=
      mul_nonneg hV0 (Finset.prod_nonneg fun p _ => hB.1 p (d p))
    calc ∑ x ∈ S', L.rw x.1 ≤ L.V0 * ∏ p, L.wt p (d p) := h0
      _ ≤ L.V0 * c * ∏ p, L.wt p (d p) := by nlinarith
  · intro x hx
    rw [ha x hx]
    first
      | rfl
      | (unfold Formalism.L2.SG.Pf.MainEqCut.weightedGenericAmplitudeSq Formalism.L2.SG.Pf.MainEqCut.ampGen; rfl)
      | (cases hd : L.dat x.1 x.2 <;> simp [Formalism.L2.SG.Pf.MainEqCut.weightedGenericAmplitudeSq, Formalism.L2.SG.Pf.MainEqCut.ampGen, hd])
  · show N.ngen γ = L.V0 * c * ∏ p, L.ngen p
    rw [hng γ]
    have e : L.ngenTot = L.V0 * ∏ p, L.ngen p := rfl
    have hne : L.ngenTot ≠ 0 := hpos.ne'
    rw [show L.V0 * c * ∏ p, L.ngen p = L.ngenTot * c by rw [e]; ring, hc, mul_div_assoc',
      mul_div_cancel_left₀ _ hne]

def StepLocPinnedG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 C0n : ℕ, ∃ CSt : ℝ, 0 ≤ CSt ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u ν →
      ∃ s : X.B.I.Ginf → NNReal,
        (∀ γ, Formalism.L2.SG.RealObj.RegX X u u γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧
        (∀ γ, (s γ : ℝ) ^ 2 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) ∧
        LocalInputLeG (genT (Y.tO u u)) (NOfG Y u (sc s ν) ν (fun _ => 0)) C1 C0n
          (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA)

end Formalism.L2.SG.Pf.MainEqLoc

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.MainEqLoc

theorem stepLocGenPinnedG_of_loc (h : StepLocPinnedG) : StepLocGenPinnedG := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C1, C0n, CSt, hCSt, C'₀, Cl₀, H⟩ := h Cg cb Cw cT CT C0
  refine ⟨C1, C0n, CSt, hCSt, C'₀, Cl₀, ?_⟩
  intro C' Cl hC' hCl D large₂ X Y u hctx hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hok ν hpin
  obtain ⟨s, hs1, hs2, hs3, hloc⟩ :=
    H C' Cl hC' hCl D large₂ X Y u hctx hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hok ν hpin
  let AAre : ℝ := PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA
  let N0 := NOfG Y u (sc s ν) ν (fun _ => 0)
  let ng : PN.Pts D.host.E D.R.rS → ℝ := fun γ => AAre * 2 * N0.Hh γ ^ PN.eN D.R.rS * N0.n γ
  refine ⟨s, ng, 2, hs1, hs2, hs3, by norm_num, le_refl _, ?_, ?_⟩
  · exact localInputG_of_le _ _ C1 C0n AAre hloc (fun γ => rfl)
  · intro γ _
    refine ⟨?_, le_refl _⟩
    change 0 ≤ Formalism.L2.SG.RowsConc.nPt _ _ _ γ
    unfold Formalism.L2.SG.RowsConc.nPt
    apply Finset.prod_nonneg
    intro w _
    apply mul_nonneg
    · exact pow_nonneg (mul_nonneg (inv_nonneg.2 (Even.pow_nonneg (Even.mul_right (even_two_mul _) _) _))
        (w.1.nonneg _)) _
    · apply Finset.prod_nonneg
      intro a _
      exact Even.pow_nonneg (Even.mul_right (even_two_mul _) _) _

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemDdPowMulQd
section
noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem ddS_ne : ddS D ≠ 0 := by
  intro h
  apply shapeNZ.1 1
  unfold ddPow; rw [h]; simp

theorem ddPow_mul (i j : ℕ) : ddPow D i * ddPow D j = ddPow D (i + j) := by
  unfold ddPow
  rw [← zpow_add₀ ddS_ne]
  congr 1; push_cast; ring

theorem mem_ddPow_mul {i j : ℕ} {x y : D.host.E} (hx : x ∈ ddPow D i) (hy : y ∈ ddPow D j) :
    x * y ∈ ddPow D (i + j) := by
  rw [← ddPow_mul]; exact FractionalIdeal.mul_mem_mul hx hy

theorem mem_qdPow_mul {i j : ℕ} {x y : D.host.E} (hx : x ∈ qdPow D i) (hy : y ∈ ddPow D j) :
    x * y ∈ qdPow D (i + j) := by
  have := FractionalIdeal.mul_mem_mul hx hy
  unfold qdPow at this ⊢
  rwa [mul_assoc, ddPow_mul] at this

theorem mem_ddPow_mul_qd {i j : ℕ} {x y : D.host.E} (hx : x ∈ ddPow D i) (hy : y ∈ qdPow D j) :
    x * y ∈ qdPow D (i + j) := by
  rw [mul_comm, add_comm]; exact mem_qdPow_mul hy hx

theorem one_mem_ddPow0 : (1 : D.host.E) ∈ ddPow D 0 := by
  unfold ddPow; simp only [CharP.cast_eq_zero, neg_zero, zpow_zero]
  exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩

theorem qd_le_dd (h : ℕ) {x : D.host.E} (hx : x ∈ qdPow D h) : x ∈ ddPow D h := by
  rw [qdPow_mem_iff] at hx
  have h2 : ((gS D : ℕ) : D.host.E) ∈ ddPow D 0 := by
    unfold ddPow; simp only [CharP.cast_eq_zero, neg_zero, zpow_zero]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨(gS D : ℕ), map_natCast _ _⟩
  have := mem_ddPow_mul h2 hx
  rwa [zero_add, mul_div_cancel₀ _ gS_ne] at this

def GrD (M : MatR D) : Prop := ∀ a c : Fin (D.R.rS + 1), a ≤ c → M a c ∈ ddPow D (c.val - a.val)

theorem grD_inv {X : MatR D} (hX : UpU X) (hG : GrD X) : GrD X⁻¹ := by
  have hXi := upU_inv hX
  have hd : IsUnit X.det := by rw [upU_det hX]; exact isUnit_one
  have key : ∀ n : ℕ, ∀ a c : Fin (D.R.rS + 1), a ≤ c → c.val - a.val = n → X⁻¹ a c ∈ ddPow D n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a c hac hn
      rcases eq_or_lt_of_le hac with h | h
      · subst h; rw [(hXi a a).2 rfl]; simp only [Nat.sub_self] at hn; subst hn; exact one_mem_ddPow0
      ·
        have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv X hd) a) c
        rw [Matrix.mul_apply, Matrix.one_apply_ne (ne_of_lt h), ← Finset.add_sum_erase _ _ (Finset.mem_univ a),
          (hX a a).2 rfl, one_mul] at h1
        have h2 : X⁻¹ a c = -∑ i ∈ Finset.univ.erase a, X a i * X⁻¹ i c := by
          rw [eq_neg_iff_add_eq_zero]; exact h1
        rw [h2]
        refine (ddPow D n : Submodule (𝓞 D.host.E) D.host.E).neg_mem (Submodule.sum_mem _ fun i hi => ?_)
        have hia : i ≠ a := Finset.ne_of_mem_erase hi
        by_cases hai : a < i
        · by_cases hic : i ≤ c
          · have hlt : c.val - i.val < n := by have : a.val < i.val := hai; omega
            have e : n = (i.val - a.val) + (c.val - i.val) := by have : a.val < i.val := hai; omega
            rw [e]
            exact mem_ddPow_mul (hG a i (le_of_lt hai)) (ih _ hlt i c hic rfl)
          · rw [(hXi i c).1 (lt_of_not_ge hic), mul_zero]; exact FractionalIdeal.zero_mem _
        · rw [(hX a i).1 (lt_of_le_of_ne (not_lt.1 hai) hia), zero_mul]; exact FractionalIdeal.zero_mem _
  intro a c hac
  exact key _ a c hac rfl

theorem inv_diff {X X' : MatR D} (hX : UpU X) (hX' : UpU X') {a c : Fin (D.R.rS + 1)} (hac : a < c)
    (hag : ∀ i j : Fin (D.R.rS + 1), i < j → j.val - i.val < c.val - a.val → X i j = X' i j) :
    X⁻¹ a c - X'⁻¹ a c = X' a c - X a c := by
  have hd : IsUnit X.det := by rw [upU_det hX]; exact isUnit_one
  have hd' : IsUnit X'.det := by rw [upU_det hX']; exact isUnit_one
  have hXi := upU_inv hX
  have hXi' := upU_inv hX'
  have hm : X⁻¹ - X'⁻¹ = X⁻¹ * (X' - X) * X'⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hd', Matrix.mul_one]
  have e := congrFun (congrFun hm a) c
  rw [Matrix.sub_apply] at e
  rw [e, Matrix.mul_apply, Finset.sum_eq_single c]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [(hXi a a).2 rfl, (hXi' c c).2 rfl, one_mul, mul_one, Matrix.sub_apply]
    · intro i _ hia
      by_cases hai : a < i
      · rw [Matrix.sub_apply]
        by_cases hic : i < c
        · rw [hag i c hic (by have : a.val < i.val := hai; have : i.val < c.val := hic; omega), sub_self, mul_zero]
        · rcases eq_or_lt_of_le (not_lt.1 hic) with h | h
          · rw [h, (hX' i i).2 rfl, (hX i i).2 rfl, sub_self, mul_zero]
          · rw [(hX' i c).1 h, (hX i c).1 h, sub_self, mul_zero]
      · rw [(hXi a i).1 (lt_of_le_of_ne (not_lt.1 hai) hia), zero_mul]
    · simp
  · intro j _ hjc
    by_cases hjc' : j < c
    · rw [Matrix.mul_apply]
      refine mul_eq_zero_of_left (Finset.sum_eq_zero fun i _ => ?_) _
      by_cases hai : a ≤ i
      · rw [Matrix.sub_apply]
        by_cases hij : i < j
        · rw [hag i j hij (by have : a.val ≤ i.val := hai; have : j.val < c.val := hjc'; omega), sub_self, mul_zero]
        · rcases eq_or_lt_of_le (not_lt.1 hij) with h | h
          · rw [h, (hX' i i).2 rfl, (hX i i).2 rfl, sub_self, mul_zero]
          · rw [(hX' i j).1 h, (hX i j).1 h, sub_self, mul_zero]
      · rw [(hXi a i).1 (lt_of_not_ge hai), zero_mul]
    · rw [(hXi' j c).1 (lt_of_le_of_ne (not_lt.1 hjc') (Ne.symm hjc)), mul_zero]
  · simp

variable (w : Point D.host.E (D.R.rS + 1))

theorem Xmat_upU (y : FreeE w → D.host.E) : UpU (Xmat w y) := by
  intro a c
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [Xmat, ne_of_gt h, if_false]
    rw [dite_eq_right (fun h' => absurd h'.1 (not_lt.2 (le_of_lt h)))]
  · simp [Xmat, h]

theorem Xmat_blk (y : FreeE w → D.host.E) : IsBlockDiagonalMatrix w (Xmat w y) := by
  intro a c hne
  have hac : a ≠ c := fun e => hne (by rw [e])
  simp only [Xmat, hac, if_false]
  rw [dite_eq_right (fun h' => hne h'.2)]

theorem Xmat_q (y : FreeE w → D.host.E) (q : FreeE w) : Xmat w y q.1.1 q.1.2 = y q := by
  have hne : q.1.1 ≠ q.1.2 := ne_of_lt q.2.1
  simp only [Xmat, hne, if_false]
  rw [dite_eq_left q.2]
  rfl

theorem Xmat_grD (y : FreeE w → D.host.E) (hy : ∀ q, y q ∈ ddPow D (hgt w q)) : GrD (Xmat w y) := by
  intro a c hac
  rcases eq_or_lt_of_le hac with h | h
  · subst h; simp only [Xmat, if_true, Nat.sub_self]; exact one_mem_ddPow0
  · by_cases hb : blkOf w.1 a.val = blkOf w.1 c.val
    · have := Xmat_q w y ⟨(a, c), h, hb⟩
      simp only at this; rw [this]; exact hy ⟨(a, c), h, hb⟩
    · rw [Xmat_blk w y a c hb]; exact FractionalIdeal.zero_mem _

end Formalism.L2.SG.Pf.StabIntLat
end
end

