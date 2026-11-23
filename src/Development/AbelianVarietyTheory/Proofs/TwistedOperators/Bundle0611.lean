module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnfSupportOfNeOne
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0607
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0809
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelAlgebraicExpansion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0333
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DeterminantIdeleAtIdempotentIdempotentPartCompon
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
noncomputable section

namespace GlobalTheory.TopLevelInv

variable {D : D7}

theorem infPart_of_isIdemSum {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) : infPart D e = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have hs := map_sum (infPart D).toAddMonoidHom es P
  change (infPart D).toAddMonoidHom _ = 0
  rw [hs]
  exact Finset.sum_eq_zero fun PP hPP =>
    (GlobalTheory.IdemSupport.delta_of_isIdemAt (GlobalTheory.StdFrames.comp_toAd D) (hes PP hPP)).1


open Classical in
theorem cpt_of_isIdemSum {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) (Q : Pl D.host.E) :
    GlobalTheory.StdFrames.cpt Q (toEAf D e) = if Q ∈ P then 1 else 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have hs := map_sum ((GlobalTheory.StdFrames.cpt Q).comp (toEAf D)).toAddMonoidHom es P
  change ((GlobalTheory.StdFrames.cpt Q).comp (toEAf D)).toAddMonoidHom _ = _
  rw [hs]
  have h : ∀ PP ∈ P, GlobalTheory.StdFrames.cpt Q (toEAf D (es PP)) = if PP = Q then 1 else 0 := fun PP hPP => by
    by_cases hQ : PP = Q
    · subst hQ; rw [if_pos rfl]; exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes PP hPP)).1
    · rw [if_neg hQ]; exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes PP hPP)).2 Q (Ne.symm hQ)
  calc _ = ∑ PP ∈ P, (if PP = Q then (1 : Q.adicCompletion D.host.E) else 0) := Finset.sum_congr rfl h
    _ = _ := by rw [Finset.sum_ite_eq']

theorem cpt_one_of_isIdemSum {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {Q : Pl D.host.E} (hQ : Q ∈ P) :
    GlobalTheory.StdFrames.cpt Q (toEAf D e) = 1 := by
  classical
  rw [cpt_of_isIdemSum he, if_pos hQ]

theorem cpt_zero_of_isIdemSum {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {Q : Pl D.host.E} (hQ : Q ∉ P) :
    GlobalTheory.StdFrames.cpt Q (toEAf D e) = 0 := by
  classical
  rw [cpt_of_isIdemSum he, if_neg hQ]

theorem map_unitMix_of_zero {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (e x : R) (h : φ e = 0) :
    φ (e * x + (1 - e)) = 1 := by
  rw [map_add (f := _), map_mul, map_sub, map_one, h]; ring

set_option maxHeartbeats 1000000 in
theorem detAt_cutPart_parts {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) (V : HSp D) (g : GA D V) :
    infPart D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem V (cutPart (e + cA D e) V g) : AE D) = 1 ∧
    (∀ Q ∈ P, GlobalTheory.StdFrames.cpt Q (toEAf D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem V
      (cutPart (e + cA D e) V g) : AE D)) = ((Formalism.L2.Theta.mt V g).map fun z => GlobalTheory.StdFrames.cpt Q (toEAf D z)).det) ∧
    ∀ Q ∉ P, GlobalTheory.StdFrames.cpt Q (toEAf D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem V
      (cutPart (e + cA D e) V g) : AE D)) = 1 := by
  have hee : e * e = e := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem
  have hc : e * cA D e = 0 := he.2
  have hf := idem_conj_sum hee hc
  have hval : (GlobalTheory.VecInv.detAt e hee V (cutPart (e + cA D e) V g) : AE D) =
      e * (Formalism.L2.Theta.mt V (cutPart (e + cA D e) V g)).det + (1 - e) := rfl
  rw [hval]
  have hinf := infPart_of_isIdemSum he
  refine ⟨?_, fun Q hQ => ?_, fun Q hQ => ?_⟩
  · rw [RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hinf, zero_mul, zero_add, sub_zero]
  · let φ : AE D →+* Q.adicCompletion D.host.E := (GlobalTheory.StdFrames.cpt Q).comp (toEAf D)
    have h1 : φ e = 1 := cpt_one_of_isIdemSum he hQ
    have h2 : φ (cA D e) = 0 := by
      have := congrArg φ hc
      rwa [RingHom.map_mul, RingHom.map_zero, h1, one_mul] at this
    have h3 : φ (e + cA D e) = 1 := by rw [RingHom.map_add (f := _), h1, h2, add_zero]
    change φ _ = ((Formalism.L2.Theta.mt V g).map φ).det
    rw [RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub, RingHom.map_one, h1, one_mul, sub_self, add_zero,
      RingHom.map_det, mt_cutPart hf.1 hf.2]
    congr 1
    refine Matrix.ext fun i j => ?_
    change φ ((e + cA D e) * Formalism.L2.Theta.mt V g i j + (1 - (e + cA D e)) * (1 : Matrix _ _ (AE D)) i j) = φ (Formalism.L2.Theta.mt V g i j)
    rw [RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, h3, one_mul, sub_self,
      zero_mul, add_zero]
  · let φ : AE D →+* Q.adicCompletion D.host.E := (GlobalTheory.StdFrames.cpt Q).comp (toEAf D)
    have h1 : φ e = 0 := cpt_zero_of_isIdemSum he hQ
    change φ _ = 1
    exact map_unitMix_of_zero φ e _ h1

end GlobalTheory.TopLevelInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DownwardVertexMapLastVertexMulOfFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport

noncomputable section

namespace GlobalTheory.TopLevelInv

theorem frame_symm_of_zero {a c b : ℕ} (h : a + c = b) (hc : c = 0) (p : Fin b) :
    (frame h).symm p = Sum.inl ⟨p.val, by omega⟩ := by
  subst hc
  rw [Equiv.symm_apply_eq]
  ext
  simp only [frame, Equiv.trans_apply, finCongr_apply, Fin.val_cast]
  rfl

theorem downMap_last_mul_of_toFrame_eq : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (hs : 1 ≤ Γ.s) (j : ℕ) (hj : j + 1 < Γ.m) (hB : j + 2 = Γ.m)
    (g : GL (Fin (Γ.rank (Γ.m, j + 1))) k) (κ : GL (Fin (topRank Γ (j + 1))) k),
    toFrame hs hj g = embX (Γ.m - 1 - (j + 1)) κ → ∀ (x x' : ColArgs Γ) (e e' : Vars Γ), x' (j + 1) = x (j + 1) * κ.val →
    downMap hs x' e' (j + 1) = downMap hs x e (j + 1) * g.val := by
  intro k _ _ _ _ _ _ Γ hs j hj hB g κ hg x x' e e' hx
  have hr : Γ.rank (Γ.m, j + 1) = topRank Γ (j + 1) := by have := topRank_add hs (j + 1); omega
  have hval : ∀ p q, g.val p q = κ.val (Fin.cast hr p) (Fin.cast hr q) := by
    intro p q
    have h1 : g = (toFrame hs hj).symm (embX _ κ) := by rw [← hg, MulEquiv.symm_apply_apply]
    rw [h1]
    unfold toFrame
    rw [frameGL_symm_val, submatrix_apply, frame_symm_of_zero _ (by omega), frame_symm_of_zero _ (by omega)]
    rfl
  unfold downMap
  rw [dite_eq_right (by omega), dite_eq_left (by omega), dite_eq_right (by omega), dite_eq_left (by omega), hx]
  ext r q
  simp only [submatrix_apply, Matrix.mul_apply, hval]
  exact (Fintype.sum_equiv (finCongr hr) _ _ (fun p => rfl)).symm

end GlobalTheory.TopLevelInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicInvariantFormVacuumSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.SplitAlgForm

open GlobalTheory.SplitScalar GlobalTheory.LevelSeries.IdemSumForm GlobalTheory.AlgWave

theorem psi_ne_zero {G : Type} [AddGroup G] (ψ : AddChar G ℂ) (x : G) : ψ x ≠ 0 := by
  intro h
  have := ψ.map_add_eq_mul x (-x)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem fin_smul {D : D7} {m n : ℕ} (a : AE D) {x : Mx D m n} (hx : x.map (infPart D) = 0) :
    (a • x).map (infPart D) = 0 := by
  ext i j
  have : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
  show infPart D (a * x i j) = 0
  rw [RingHom.map_mul, this, mul_zero]

theorem fin_add {D : D7} {m n : ℕ} {x y : Mx D m n} (hx : x.map (infPart D) = 0) (hy : y.map (infPart D) = 0) :
    (x + y).map (infPart D) = 0 := by
  rw [Matrix.map_add _ (map_add (infPart D)), hx, hy, add_zero]


set_option maxHeartbeats 1000000 in
theorem exists_alg_form : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ e : Formalism.L2.Theta.AE D, IsSplitIdem D e → ∀ (n : ℕ) (w : Fin n → WO S T), (∀ p, (w p).map (infPart D) = 0) →
    ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧
      ℓ v = 1 ∧ ∀ p, IsAlgebraic ℚ (ℓ (heisO ψ S T (w p) v)) := by
  intro D ψ θ S T sS sT ΛS ΛT v hv hS hT e he n w hw
  classical
  have hψ : IsStdChar D ψ (-1) := hv.1
  obtain ⟨hd, -, hsg⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  set Λ : AddSubgroup (WO S T) := latO S T (ΛS : Set (Fin S.rank → D.host.E))
    (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛdef
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ Λ, a • u ∈ Λ := fun a ha =>
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha]))
  have hΛfin : ∀ u ∈ Λ, u.map (infPart D) = 0 := fun u hu => latO_fin hu
  have hth : ∀ w f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w f) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have hvth : IsThetaFunO ψ S T v := hv.2.theta
  have hlat : IsLatVac (heisO ψ S T) Λ v := hv.2.lat
  have hsign : ∀ u ∈ Λ, ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ heisO ψ S T u v = ε • v := fun u hu => by
    obtain ⟨ε, hε, h⟩ := hsg v hlat u hu
    exact ⟨ε, hε, h v hlat⟩
  have hεQ : ∀ ε : ℂ, (ε = 1 ∨ ε = -1) → ε ∈ Qb ∧ ε ≠ 0 := by
    rintro ε (rfl | rfl)
    · exact ⟨one_mem _, one_ne_zero⟩
    · exact ⟨neg_mem (one_mem _), neg_ne_zero.2 one_ne_zero⟩
  have hpsi : ∀ x y : WO S T, x.map (infPart D) = 0 → y.map (infPart D) = 0 → ψ (symplO S T x y) ∈ Qb :=
    fun x y hx hy => GlobalTheory.BotFourier.psi_mem hψ hS hT hx hy
  have hpsiH : ∀ x y : WO S T, x.map (infPart D) = 0 → y.map (infPart D) = 0 → ψ (symplOH S T x y) ∈ Qb :=
    fun x y hx hy => GlobalTheory.BotFourier.psiH_mem hψ hS hT hx hy

  have hcS : IsSplitIdem D (cA D e) := isSplitIdem_conj he
  have he1 : e * e = e := he.1
  have hec : e * (cA D e) = 0 := he.2.1
  have hce : (cA D e) * e = 0 := by rw [mul_comm]; exact hec
  have hc1 : (cA D e) * (cA D e) = (cA D e) := by rw [← RingHom.map_mul, he1]
  have hcc : cA D (cA D e) = e := GlobalTheory.DualPairCheck.cA_cA e
  have hq1 : (1 - (e + (cA D e))) * (1 - (e + (cA D e))) = 1 - (e + (cA D e)) := by linear_combination he1 + hc1 + 2 * hec
  have hcq : cA D (1 - (e + (cA D e))) = 1 - (e + (cA D e)) := by
    rw [map_sub, map_one, map_add (f := _), hcc, add_comm (cA D e) e]
  have hcq0 : (cA D e) * (1 - (e + (cA D e))) = 0 := by linear_combination -hc1 - hce
  have hqc0 : cA D (1 - (e + (cA D e))) * (cA D e) = 0 := by rw [hcq, mul_comm]; exact hcq0
  have hdec : ∀ x : WO S T, (cA D e) • x + (e • x + (1 - (e + (cA D e))) • x) = x := fun x => by
    rw [← add_smul, ← add_smul, ← add_assoc, add_comm (cA D e) e, add_sub_cancel, one_smul]

  have caseB : ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, IsHalf (cA D e) u → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) →
      ℓ v = 1 → ∀ x : WO S T, x.map (infPart D) = 0 → (1 - (e + (cA D e))) • x ∈ Λ → ℓ (heisO ψ S T x v) ∈ Qb := by
    intro ℓ hinv h1 x hx hx'
    obtain ⟨ε, hε, hεv⟩ := hsign _ hx'
    have hxe : IsHalf e (e • x) := (isHalf_iff _ _).2 (by rw [smul_smul, he1])
    have hxc : IsHalf (cA D e) ((cA D e) • x) := (isHalf_iff _ _).2 (by rw [smul_smul, hc1])
    have hxq : IsHalf (1 - (e + (cA D e))) ((1 - (e + (cA D e))) • x) := (isHalf_iff _ _).2 (by rw [smul_smul, hq1])
    have horth : symplO S T (e • x) ((1 - (e + (cA D e))) • x) = 0 := symplO_eq_zero S T hcq0 hxe hxq
    have e1 : heisO ψ S T (e • x + (1 - (e + (cA D e))) • x) v = ε • heisO ψ S T (e • x) v := by
      rw [heisO_add_of_orth ψ S T horth, hεv, heisO_smul]
    have e2 : heisO ψ S T ((cA D e) • x) (heisO ψ S T (e • x + (1 - (e + (cA D e))) • x) v) =
        ψ (symplOH S T ((cA D e) • x) (e • x + (1 - (e + (cA D e))) • x)) • heisO ψ S T x v := by
      rw [heisO_heisO, hdec x]
    have e3 : ℓ (heisO ψ S T ((cA D e) • x) (heisO ψ S T (e • x + (1 - (e + (cA D e))) • x) v)) =
        ε * ℓ (heisO ψ S T (e • x) v) := by
      rw [hinv _ hxc _ (hth _ _ hvth), e1, map_smul, smul_eq_mul]
    rw [e2, map_smul, smul_eq_mul] at e3
    have hx0 := psi_ne_zero ψ (symplOH S T ((cA D e) • x) (e • x + (1 - (e + (cA D e))) • x))
    have hpq : ψ (symplOH S T ((cA D e) • x) (e • x + (1 - (e + (cA D e))) • x)) ∈ Qb :=
      hpsiH _ _ (fin_smul _ hx) (fin_add (fin_smul _ hx) (fin_smul _ hx))
    have e4 : ℓ (heisO ψ S T x v) = (ψ (symplOH S T ((cA D e) • x) (e • x + (1 - (e + (cA D e))) • x)))⁻¹ *
        (ε * ℓ (heisO ψ S T (e • x) v)) := by
      rw [← e3, inv_mul_cancel_left₀ hx0]
    rw [e4]
    refine mul_mem (inv_mem hpq) (mul_mem (hεQ ε hε).1 ?_)
    by_cases hxΛ : e • x ∈ Λ
    · rw [hlat.2 e he _ hxΛ hxe, h1]; exact one_mem _
    · obtain ⟨l, hl, hlc, hne⟩ := dual_half he1 (fun u hu => half_fin he hu) hd (fun u hu => hΛ (cA D e) hc1 u hu) hxe hxΛ
      have h0 : ℓ (heisO ψ S T (e • x) v) = 0 := by
        have k1 := hinv l hlc _ (hth (e • x) v hvth)
        rw [heisO_comm, hlat.2 (cA D e) hcS l hl hlc, map_smul, smul_eq_mul] at k1
        have : (ψ (symplO S T l (e • x)) - 1) * ℓ (heisO ψ S T (e • x) v) = 0 := by
          rw [sub_mul, k1, one_mul, sub_self]
        exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
      rw [h0]; exact zero_mem _

  have step : ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, IsHalf (cA D e) u → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) →
      ℓ v = 1 → ∀ x : WO S T, x.map (infPart D) = 0 → ∃ ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ,
        (∀ u : WO S T, IsHalf (cA D e) u → ∀ f, IsThetaFunO ψ S T f → ℓ' (heisO ψ S T u f) = ℓ' f) ∧ ℓ' v = 1 ∧
        ℓ' (heisO ψ S T x v) ∈ Qb ∧ ∀ y : WO S T, y.map (infPart D) = 0 →
          ∃ a ∈ Qb, ℓ' (heisO ψ S T y v) = a * ℓ (heisO ψ S T y v) := by
    intro ℓ hinv h1 x hx
    by_cases hB : (1 - (e + (cA D e))) • x ∈ Λ
    · exact ⟨ℓ, hinv, h1, caseB ℓ hinv h1 x hx hB, fun y _ => ⟨1, one_mem _, (one_mul _).symm⟩⟩
    have hex : ¬ ∀ u ∈ Λ, ψ (symplO S T ((1 - (e + (cA D e))) • x) u) = 1 := fun h => hB ((hd _ (fin_smul _ hx)).2 h)
    push_neg at hex
    obtain ⟨u', hu', hne'⟩ := hex
    have huΛ : (1 - (e + (cA D e))) • u' ∈ Λ := hΛ _ hq1 u' hu'
    have huq : IsHalf (1 - (e + (cA D e))) ((1 - (e + (cA D e))) • u') := (isHalf_iff _ _).2 (by rw [smul_smul, hq1])
    rw [symplO_smul, hcq] at hne'
    have hne := psi_skew_ne hne'
    obtain ⟨ε, hε, hεv⟩ := hsign _ huΛ
    obtain ⟨hεQ', hε0⟩ := hεQ ε hε
    have hzQ : ψ (symplO S T ((1 - (e + (cA D e))) • u') x) ∈ Qb := hpsi _ _ (hΛfin _ huΛ) hx
    have hk : ε - ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x) ≠ 0 := by
      rw [← mul_one_sub]
      exact mul_ne_zero hε0 (sub_ne_zero.2 (Ne.symm hne))
    have hcomm : ∀ w₁ : WO S T, heisO ψ S T ((1 - (e + (cA D e))) • u') (heisO ψ S T w₁ v) =
        (ψ (symplO S T ((1 - (e + (cA D e))) • u') w₁) * ε) • heisO ψ S T w₁ v := fun w₁ => by
      rw [heisO_comm, hεv, heisO_smul, smul_smul]
    refine ⟨(ε - ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x))⁻¹ •
      (ℓ ∘ₗ (heisL ψ S T ((1 - (e + (cA D e))) • u') - (ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x)) • LinearMap.id)),
      fun y hy f hf => ?_, ?_, ?_, fun y hy => ?_⟩
    all_goals simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.sub_apply, heisL_apply,
      LinearMap.id_apply, map_sub, map_smul, smul_eq_mul]
    · have hc' : heisO ψ S T ((1 - (e + (cA D e))) • u') (heisO ψ S T y f) =
          heisO ψ S T y (heisO ψ S T ((1 - (e + (cA D e))) • u') f) := by
        rw [heisO_comm, symplO_eq_zero S T hqc0 huq hy, AddChar.map_zero_eq_one, one_smul]
      rw [hc', hinv y hy _ (hth _ _ hf), hinv y hy f hf]
    · rw [hεv, map_smul, smul_eq_mul, h1, mul_one, mul_one, inv_mul_cancel₀ hk]
    · rw [hcomm, map_smul, smul_eq_mul]
      have : ψ (symplO S T ((1 - (e + (cA D e))) • u') x) * ε * ℓ (heisO ψ S T x v) -
          ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x) * ℓ (heisO ψ S T x v) = 0 := by ring
      rw [this, mul_zero]
      exact zero_mem _
    · refine ⟨(ε - ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x))⁻¹ *
        (ψ (symplO S T ((1 - (e + (cA D e))) • u') y) * ε - ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x)),
        mul_mem (inv_mem (sub_mem hεQ' (mul_mem hεQ' hzQ)))
          (sub_mem (mul_mem (hpsi _ _ (hΛfin _ huΛ) hy) hεQ') (mul_mem hεQ' hzQ)), ?_⟩
      rw [hcomm, map_smul, smul_eq_mul]
      ring

  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨p, hp⟩ := hv.2.norm.1
    have := hv.2.norm.2 p hp
    simp [nrm2] at this
  obtain ⟨ℓ₀, hℓ₀, hinv₀⟩ := invariant_form (e := (cA D e)) (Λ := Λ) hc1 (by rw [hcc]; exact hec)
    (fun u hu => half_fin hcS hu) hd (fun u hu => by rw [hcc]; exact hΛ e he1 u hu) hv0
    (fun l hl hh => hlat.2 (cA D e) hcS l hl hh) (fun l hl hh => hlat.2 e he l hl (by rwa [hcc] at hh))
  have main : ∀ (n : ℕ) (w : Fin n → WO S T), (∀ p, (w p).map (infPart D) = 0) → ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, IsHalf (cA D e) u → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧ ℓ v = 1 ∧
      ∀ p, ℓ (heisO ψ S T (w p) v) ∈ Qb := by
    intro n
    induction n with
    | zero =>
      intro w _
      refine ⟨(ℓ₀ v)⁻¹ • ℓ₀, fun u hu f hf => ?_, ?_, fun p => p.elim0⟩
      · rw [LinearMap.smul_apply, LinearMap.smul_apply, hinv₀ u hu f hf]
      · rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hℓ₀]
    | succ n ih =>
      intro w hw
      obtain ⟨ℓ, hinv, h1, halg⟩ := ih (fun p => w p.castSucc) fun p => hw _
      obtain ⟨ℓ', hinv', h1', hlast, hfac⟩ := step ℓ hinv h1 (w (Fin.last n)) (hw _)
      refine ⟨ℓ', hinv', h1', fun p => ?_⟩
      induction p using Fin.lastCases with
      | last => exact hlast
      | cast q =>
        obtain ⟨a, ha, h⟩ := hfac _ (hw q.castSucc)
        rw [h]
        exact mul_mem ha (halg q)
  obtain ⟨ℓ, hinv, h1, halg⟩ := main n w hw
  exact ⟨ℓ, fun u hu f hf => hinv u hu f hf, h1, fun p => mem_algebraicClosure_iff.1 (halg p)⟩

end GlobalTheory.SplitAlgForm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanCharacterTheta
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

open scoped ComplexOrder Kronecker Matrix

namespace GlobalTheory.BottomRealChar

open GlobalTheory.Grid (neg sgn ofSgn)

theorem detPlus_neg_one_one {m n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) (b : Matrix (Fin m) (Fin m) ℂ) :
    GlobalTheory.WeilParts.detPlus (-1) 1 a b = 1 := by
  unfold GlobalTheory.WeilParts.detPlus
  have e : (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (-1 : Matrix (Fin n) (Fin n) ℂ)ᵀ = -1 := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> simp_all
  have e2 : (1 / 2 : ℂ) • ((1 + -1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) * (b ⊗ₖ aᵀ)) +
      (1 / 2 : ℂ) • (1 - -1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) = 1 := by
    rw [add_neg_cancel, Matrix.zero_mul, smul_zero, zero_add, sub_neg_eq_add, ← two_smul ℂ, smul_smul]
    norm_num
  rw [e, e2, Matrix.det_one]

theorem commGroup_div_eq_div_mul_ratio {G : Type*} [CommGroup G] (a x y e c : G) :
    c * e / (a * x * e) = c * e / (a * y * e) * (y * x⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]
  abel

def detChar {D : D7} (θ : InfFam D) (V : HSp D) (e : D.what₂.Tau → ℤ) : GinfC V →* ℂ where
  toFun g := ∏ τ, (compAt θ τ (Formalism.L2.Theta.mt V g.1)).det ^ e τ
  map_one' := by
    simp only [OneMemClass.coe_one, GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.det_one, one_zpow, Finset.prod_const_one]
  map_mul' g h := by
    simp only [Subgroup.coe_mul, GlobalTheory.StdUnn.CartanMove.compAt_mt_mul, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]

theorem detChar_apply {D : D7} (θ : InfFam D) (V : HSp D) (e : D.what₂.Tau → ℤ) (g : GinfC V) :
    detChar θ V e g = ∏ τ, (compAt θ τ (Formalism.L2.Theta.mt V g.1)).det ^ e τ := rfl

theorem continuous_detChar {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (e : D.what₂.Tau → ℤ) :
    Continuous (detChar θ V e) := by
  refine continuous_finsetProd _ fun τ _ => Continuous.zpow₀ ?_ _ fun g => Or.inl fun h0 => ?_
  · exact (((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp
      ((GlobalTheory.RealWeil.continuous_mt V).1.comp continuous_subtype_val))).matrix_det
  · have := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ g.1)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this

theorem isAlgebraic_detChar {D : D7} (θ : InfFam D) (V : HSp D) (e : D.what₂.Tau → ℤ) (g : GinfC V)
    (hg : ∀ τ a b, IsAlgebraic ℚ (compAt θ τ (Formalism.L2.Theta.mt V g.1) a b)) : IsAlgebraic ℚ (detChar θ V e g) := by
  let K := algebraicClosure ℚ ℂ
  have hK : ∀ z : ℂ, z ∈ K ↔ IsAlgebraic ℚ z := fun z => mem_algebraicClosure_iff
  rw [← hK, detChar_apply]
  refine prod_mem fun τ _ => zpow_mem ?_ _
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun a _ => (hK _).2 (hg τ _ _))

end GlobalTheory.BottomRealChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepLin
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section
namespace GlobalTheory.StepLeft

variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}


open Classical in
def stepLin (n' : Type) [Fintype n'] (g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) :
    Matrix (StepVar n c n') (StepVar n c n') k :=
  Matrix.of fun a b => if a.1.2 = b.1.2 then g a.1.1 b.1.1 else 0

end GlobalTheory.StepLeft
end
end

